-- Prove2me | solution 1 for OAI.TuringRigidity.OrdinalArithmetic.omega_certificates_at_levels
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:25:16.812496+00:00
-- url     : https://prove2.me/submissions/c2e0dedf-006d-4e36-982a-458c1105e5f4

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_OrdinalArithmetic_relative_omega_power_internal
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_definablePower_mem
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_ground_relativeModel_ordinal_iff
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_ground_relative_context
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_hierarchyGraph_sigmaDefinable
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_uniform_hierarchy_certificate

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ElementaryLanguage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory
universe u

namespace SentenceForm

theorem finite_support (p : SentenceForm) (D : Set ZFSet.{u})
    (e f : ℕ → ZFSet.{u}) (h : ∀ i, i < p.bound → e i = f i) :
    p.Sat D e ↔ p.Sat D f := by
  induction p generalizing e f with
  | equal i j =>
    have hi := h i (by simp only [bound]; omega)
    have hj := h j (by simp only [bound]; omega)
    simp only [Sat,hi,hj]
  | member i j =>
    have hi := h i (by simp only [bound]; omega)
    have hj := h j (by simp only [bound]; omega)
    simp only [Sat,hi,hj]
  | conj p q ihp ihq =>
    exact and_congr (ihp e f (fun i hi => h i (by simp only [bound]; omega)))
      (ihq e f (fun i hi => h i (by simp only [bound]; omega)))
  | neg p ih => exact not_congr (ih e f h)
  | ex p ih =>
    apply exists_congr; intro x
    apply and_congr_right; intro _
    apply ih
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact h i (by simp only [bound] at h ⊢; omega)

theorem sat_rename (p : SentenceForm) (v : ℕ → ℕ)
    (D : Set ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (p.rename v).Sat D e ↔ p.Sat D (fun i => e (v i)) := by
  induction p generalizing v e with
  | equal => rfl
  | member => rfl
  | conj p q ihp ihq => exact and_congr (ihp v e) (ihq v e)
  | neg p ih => exact not_congr (ih v e)
  | ex p ih =>
    apply exists_congr; intro x
    apply and_congr_right; intro _
    have he : (fun i => cons x e (match i with | 0 => 0 | j+1 => v j+1)) =
        cons x (fun i => e (v i)) := by funext i; cases i <;> rfl
    exact (ih _ _).trans (he ▸ Iff.rfl)
end SentenceForm

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_DefinablePower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem mem_definedSubset (A x : ZFSet.{u}) (p : SentenceForm)
    {n : ℕ} (v : Fin n → ZFSet.{u}) :
    x ∈ definedSubset A p v ↔ x ∈ A ∧ p.Sat (A : Set ZFSet) (cons x (tupleEnv v)) :=
  ZFSet.mem_sep

theorem definableOver_subset {A S : ZFSet.{u}} (h : DefinableOver A S) : S ⊆ A := by
  obtain ⟨n,p,v,_,_,rfl⟩ := h
  exact fun _ hx => (mem_definedSubset A _ p v).mp hx |>.1

theorem mem_definablePower (A S : ZFSet.{u}) :
    S ∈ definablePower A ↔ DefinableOver A S := by
  rw [definablePower,ZFSet.mem_sep]
  exact ⟨And.right,fun h => ⟨ZFSet.mem_powerset.mpr (definableOver_subset h),h⟩⟩

theorem subset_of_mem_definablePower {A S : ZFSet.{u}}
    (h : S ∈ definablePower A) : S ⊆ A :=
  definableOver_subset ((mem_definablePower A S).mp h)

theorem separation_mem_definablePower (A : ZFSet.{u}) (p : SentenceForm)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, i < p.bound → e i ∈ A) :
    A.sep (fun x => p.Sat (A : Set ZFSet) (cons x e)) ∈ definablePower A := by
  apply (mem_definablePower A _).mpr
  let v : Fin p.bound → ZFSet.{u} := fun i => e i
  refine ⟨p.bound,p,v,by omega,fun i => he i i.isLt,?_⟩
  apply ZFSet.ext; intro x
  rw [ZFSet.mem_sep,mem_definedSubset]
  apply and_congr_right; intro _
  apply p.finite_support
  intro i hi
  cases i with
  | zero => rfl
  | succ i =>
    change e i = tupleEnv v i
    simp [tupleEnv,v,show i < p.bound by omega]

theorem self_mem_definablePower (A : ZFSet.{u}) : A ∈ definablePower A := by
  apply (mem_definablePower A A).mpr
  refine ⟨0,.equal 0 0,Fin.elim0,by decide,fun i => Fin.elim0 i,?_⟩
  apply ZFSet.ext; intro x
  simp [mem_definedSubset,SentenceForm.Sat]

theorem subset_definablePower {A : ZFSet.{u}} (hA : Transitive A) : A ⊆ definablePower A := by
  intro S hS
  apply (mem_definablePower A S).mpr
  refine ⟨1,.member 0 1,fun _ => S,by decide,fun _ => hS,?_⟩
  apply ZFSet.ext; intro x
  simp only [mem_definedSubset,SentenceForm.Sat,cons_zero,cons_succ]
  simp only [tupleEnv,show 0 < 1 by decide,dite_eq_left]
  exact ⟨fun hx => ⟨hA S hS x hx,hx⟩,And.right⟩

theorem definablePower_transitive {A : ZFSet.{u}} (hA : Transitive A) :
    Transitive (definablePower A) := by
  intro S hS x hx
  exact subset_definablePower hA (subset_of_mem_definablePower hS hx)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel
universe u

theorem mem_seed (R x : ZFSet.{u}) :
    x ∈ seed R ↔ ∃ n : ℕ, x ∈ iterUnion n ({R} : ZFSet) := by
  rw [seed,ZFSet.mem_sUnion]
  constructor
  · rintro ⟨a,ha,hx⟩
    obtain ⟨n,rfl⟩ := ZFSet.mem_range.mp ha
    exact ⟨n,hx⟩
  · rintro ⟨n,hx⟩
    exact ⟨_,ZFSet.mem_range_self (f := fun index : ℕ => iterUnion index ({R} : ZFSet.{u})) n,hx⟩

theorem parameter_mem_seed (R : ZFSet.{u}) : R ∈ seed R :=
  (mem_seed R R).mpr ⟨0,ZFSet.mem_singleton.mpr rfl⟩

theorem seed_transitive (R : ZFSet.{u}) : Transitive (seed R) := by
  intro x hx y hy
  obtain ⟨n,hn⟩ := (mem_seed R x).mp hx
  exact (mem_seed R y).mpr ⟨n+1,ZFSet.mem_sUnion.mpr ⟨x,hn,hy⟩⟩

theorem parameter_subset_seed (R : ZFSet.{u}) : R ⊆ seed R :=
  fun x hx => seed_transitive R R (parameter_mem_seed R) x hx

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleStages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel
universe u

theorem mem_stage (R o x : ZFSet.{u}) :
    x ∈ stage R o ↔ x ∈ seed R ∨ ∃ i ∈ o, x ∈ definablePower (stage R i) := by
  rw [stage,ZFSet.mem_union,ZFSet.mem_sUnion]
  apply or_congr_right
  constructor
  · rintro ⟨a,ha,hx⟩
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp ha
    exact ⟨_,((equivShrink o).symm i).property,hx⟩
  · rintro ⟨i,hi,hx⟩
    refine ⟨_,ZFSet.mem_range.mpr ⟨equivShrink o ⟨i,hi⟩,rfl⟩,?_⟩
    simpa using hx

theorem seed_subset_stage (R o : ZFSet.{u}) : seed R ⊆ stage R o :=
  fun x hx => (mem_stage R o x).mpr (Or.inl hx)

theorem stage_transitive (R o : ZFSet.{u}) : Transitive (stage R o) := by
  induction o using ZFSet.inductionOn with
  | h o ih =>
    intro x hx y hy
    rcases (mem_stage R o x).mp hx with hx|⟨i,hi,hx⟩
    · exact seed_subset_stage R o (seed_transitive R x hx y hy)
    · exact (mem_stage R o y).mpr (Or.inr ⟨i,hi,definablePower_transitive (ih i hi) x hx y hy⟩)

theorem stage_mono (R : ZFSet.{u}) {i j : ZFSet.{u}} (hij : i ⊆ j) : stage R i ⊆ stage R j := by
  intro x hx
  rcases (mem_stage R i x).mp hx with hx|⟨k,hk,hx⟩
  · exact seed_subset_stage R j hx
  · exact (mem_stage R j x).mpr (Or.inr ⟨k,hij hk,hx⟩)

theorem definablePower_subset_stage (R : ZFSet.{u}) {i j : ZFSet.{u}} (hi : i ∈ j) :
    definablePower (stage R i) ⊆ stage R j :=
  fun x hx => (mem_stage R j x).mpr (Or.inr ⟨i,hi,hx⟩)

theorem stage_mem_stage (R : ZFSet.{u}) {i j : ZFSet.{u}} (hi : i ∈ j) :
    stage R i ∈ stage R j :=
  definablePower_subset_stage R hi (self_mem_definablePower _)

theorem stage_succ (R o : ZFSet.{u}) :
    stage R (insert o o) = definablePower (stage R o) := by
  apply ZFSet.ext; intro x
  constructor
  · intro hx
    rcases (mem_stage R (insert o o) x).mp hx with hseed|⟨i,hi,hdef⟩
    · exact subset_definablePower (stage_transitive R o) (seed_subset_stage R o hseed)
    · rcases ZFSet.mem_insert_iff.mp hi with he|hi
      · simpa only [he] using hdef
      · exact subset_definablePower (stage_transitive R o) (definablePower_subset_stage R hi hdef)
  · intro hx; exact definablePower_subset_stage R (ZFSet.mem_insert o o) hx

theorem level_succ (R : ZFSet.{u}) (o : Ordinal.{u}) :
    level R (o+1) = definablePower (level R o) := by
  simp only [level,Ordinal.toZFSet_add_one,stage_succ]

theorem level_mono (R : ZFSet.{u}) {i j : Ordinal.{u}} (hij : i ≤ j) : level R i ⊆ level R j :=
  stage_mono R (Ordinal.toZFSet_monotone hij)

theorem level_mem_level (R : ZFSet.{u}) {i j : Ordinal.{u}} (hij : i < j) : level R i ∈ level R j :=
  stage_mem_stage R (Ordinal.toZFSet_mem_toZFSet_iff.mpr hij)

theorem level_transitive (R : ZFSet.{u}) (o : Ordinal.{u}) : Transitive (level R o) :=
  stage_transitive R o.toZFSet

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ElementarySatisfaction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse
universe u

theorem bounded_sat (p : Formula) (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (fromBounded p).Sat (M : Set ZFSet) e ↔ p.Realize M e := by
  induction p generalizing e with
  | equal => rfl
  | member => rfl
  | conj p q ihp ihq => exact and_congr (ihp e) (ihq e)
  | neg p ih => exact not_congr (ih e)
  | existsMem i p ih =>
    simp only [fromBounded,SentenceForm.Sat,Formula.Realize,cons_zero,cons_succ]
    apply exists_congr; intro x
    exact and_congr_right (fun _ => and_congr_right (fun _ => ih (cons x e)))

theorem sigma_sat (p : SigmaFormula) (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (fromSigma p).Sat (M : Set ZFSet) e ↔ p.Realize M e := by
  induction p generalizing e with
  | bounded p => exact bounded_sat p M e
  | existsSet p ih =>
    apply exists_congr; intro x
    exact and_congr_right (fun _ => ih (cons x e))

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel SentenceForm BoundedSetTheory TransitiveNameModel
universe u

theorem shifted_parameters (p : SentenceForm) (D : Set ZFSet.{u})
    (x a : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (p.rename parameterShift).Sat D (cons x (cons a e)) ↔ p.Sat D (cons x e) := by
  rw [sat_rename]
  have he : (fun i => cons x (cons a e) (parameterShift i)) = cons x e := by
    funext i; cases i <;> rfl
  rw [he]

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleGroundReals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel
universe u

theorem mem_groundReals (M x : ZFSet.{u}) :
    x ∈ groundReals M ↔ x ∈ M ∧ x ⊆ ZFSet.omega := by
  rw [groundReals,ZFSet.mem_sep,ZFSet.mem_powerset,and_comm]

theorem groundReals_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    groundReals M ∈ M := by
  obtain ⟨R,hR,hdef⟩ := internal_power M hM hT.powerSet (sourceT_omega_mem M hM hT)
  have heq : R = groundReals M := by
    apply ZFSet.ext; intro x
    exact (hdef x).trans (mem_groundReals M x).symm
  exact heq ▸ hR

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelAddition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
universe u
noncomputable section

theorem setSucc_omega : ∀ x ∈ ZFSet.omega.{u}, setSucc x ∈ ZFSet.omega := by
  intro x hx
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  exact (mem_omega _).mpr ⟨n+1,rfl⟩

end
end TuringRigidity.SetModelArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelFunctionGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelFunctions
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration SetModelArithmetic
universe u
noncomputable section

variable {M : ZFSet.{u}} (C : Context M)
include C

theorem Context.omega_mem : ZFSet.omega.{u} ∈ M :=
  BoundedSetTheory.omega_mem M C.transitive C.separation C.infinity

theorem Context.nat_mem (n : ℕ) : natSet.{u} n ∈ M :=
  C.transitive _ C.omega_mem _ ((mem_omega _).mpr ⟨n,rfl⟩)

end
end TuringRigidity.SetModelFunctions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BoundedDefinability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedDefinability
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions
universe u
noncomputable section

theorem parity_ext {α : Sort*} {f g : ℕ → α} (he : ∀ n, f (2*n) = g (2*n))
    (ho : ∀ n, f (2*n+1) = g (2*n+1)) : f = g := by
  funext n
  have hm : n%2 < 2 := Nat.mod_lt n (by decide)
  by_cases h : n%2=0
  · have hn : n=2*(n/2) := by omega
    rw [hn]
    exact he _
  · have hn : n=2*(n/2)+1 := by omega
    rw [hn]
    exact ho _

@[simp] theorem mix_slotMap (e d : ℕ → ZFSet.{u}) (r s : ℕ → ℕ) :
    mix e d ∘ slotMap r s = mix (e ∘ r) (d ∘ s) := by
  apply parity_ext <;> intro n <;> simp

variable {M : ZFSet.{u}} {P Q : (ℕ → ZFSet.{u}) → Prop}

theorem Definable.congr (h : Definable M P) (he : ∀ e, P e ↔ Q e) : Definable M Q := by
  obtain ⟨p,d,hd,hp⟩ := h
  exact ⟨p,d,hd,fun e => (hp e).trans (he e)⟩

theorem Definable.neg (h : Definable M P) : Definable M (fun e => ¬ P e) := by
  obtain ⟨p,d,hd,hp⟩ := h
  exact ⟨.neg p,d,hd,fun e => not_congr (hp e)⟩

theorem Definable.and (hP : Definable M P) (hQ : Definable M Q) :
    Definable M (fun e => P e ∧ Q e) := by
  obtain ⟨p,d,hd,hp⟩ := hP
  obtain ⟨q,c,hc,hq⟩ := hQ
  refine ⟨.conj (p.rename (slotMap id (fun i => 2*i)))
    (q.rename (slotMap id (fun i => 2*i+1))),mix d c,?_,?_⟩
  · intro i
    unfold mix
    split <;> first | exact hd _ | exact hc _
  · intro e
    simp only [Formula.Eval,Formula.eval_rename_comp,mix_slotMap,Function.comp_id]
    have hd' : mix d c ∘ (fun i => 2*i) = d := by funext i; simp
    have hc' : mix d c ∘ (fun i => 2*i+1) = c := by funext i; simp
    rw [hd',hc',hp,hq]

theorem bind_mix (x : ZFSet.{u}) (e d : ℕ → ZFSet.{u}) :
    cons x (mix e d) ∘ bindSlots = mix (cons x e) d := by
  apply parity_ext
  · intro n
    cases n with
    | zero => rfl
    | succ n => simp
  · intro n
    simp [show 2*n+2 = (2*n+1)+1 from by omega]

theorem Definable.existsMem (h : Definable M P) (i : ℕ) :
    Definable M (fun e => ∃ x ∈ e i, P (cons x e)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  refine ⟨.existsMem (2*i) (p.rename bindSlots),d,hd,?_⟩
  intro e
  simp only [Formula.Eval,mix_even,Formula.eval_rename_comp,bind_mix,hp]

theorem member_definable (C : Context M) (i j : ℕ) : Definable M (fun e => e i ∈ e j) :=
  ⟨.member (2*i) (2*j),fun _ => ZFSet.omega,fun _ => C.omega_mem,fun e => by simp [Formula.Eval]⟩

theorem equal_param {a : ZFSet.{u}} (ha : a ∈ M) (i : ℕ) :
    Definable M (fun e => e i = a) :=
  ⟨.equal (2*i) 1,fun _ => a,fun _ => ha,fun e => by simp [Formula.Eval,mix]⟩

theorem Definable.sep_mem (C : Context M) (h : Definable M P) (e : ℕ → ZFSet.{u})
    (he : ∀ i, e i ∈ M) {a : ZFSet.{u}} (ha : a ∈ M) :
    ZFSet.sep (fun x => P (cons x e)) a ∈ M := by
  obtain ⟨p,d,hd,hp⟩ := h
  let q := p.rename bindSlots
  have hm : ∀ i, mix e d i ∈ M := by
    intro i
    unfold mix
    split <;> first | exact he _ | exact hd _
  have hs := BoundedSetTheory.sep_mem M C.transitive C.separation q (mix e d) hm ha
  have hh : ZFSet.sep (fun x => q.Eval (cons x (mix e d))) a =
      ZFSet.sep (fun x => P (cons x e)) a := by
    apply ZFSet.ext
    intro x
    simp only [ZFSet.mem_sep,q,Formula.eval_rename_comp,bind_mix,hp]
  exact hh ▸ hs

end
end TuringRigidity.BoundedDefinability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SentenceCodeDefinability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.SentenceCoding
open BoundedSetTheory TransitiveNameModel BoundedDefinability SetModelFunctions SetModelSyntax
universe u

variable {M : ZFSet.{u}}

theorem defOr {P Q : (ℕ → ZFSet.{u}) → Prop}
    (hP : Definable M P) (hQ : Definable M Q) : Definable M (fun e => P e ∨ Q e) :=
  (hP.neg.and hQ.neg).neg.congr (fun _ => by tauto)

theorem defImp {P Q : (ℕ → ZFSet.{u}) → Prop}
    (hP : Definable M P) (hQ : Definable M Q) : Definable M (fun e => P e → Q e) :=
  (hP.and hQ.neg).neg.congr (fun _ => by tauto)

theorem defAllMem {P : (ℕ → ZFSet.{u}) → Prop}
    (h : Definable M P) (i : ℕ) : Definable M (fun e => ∀ x ∈ e i, P (cons x e)) :=
  (h.neg.existsMem i).neg.congr (fun _ => by simp)

theorem defSubset (C : Context M) (i j : ℕ) : Definable M (fun e => e i ⊆ e j) :=
  defAllMem (member_definable C 0 (j+1)) i

end TuringRigidity.SentenceCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SetSatisfactionBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem setBounded_eval (p : SentenceForm) (a : ℕ) (v : ℕ → ℕ)
    (e : ℕ → ZFSet.{u}) :
    (setBounded p a v).Eval e ↔ p.Sat (e a : Set ZFSet) (fun i => e (v i)) := by
  induction p generalizing a v e with
  | equal => rfl
  | member => rfl
  | conj p q ihp ihq => exact and_congr (ihp a v e) (ihq a v e)
  | neg p ih => exact not_congr (ih a v e)
  | ex p ih =>
    simp only [setBounded,Formula.Eval,SentenceForm.Sat]
    apply exists_congr; intro x
    apply and_congr_right; intro _
    have he : (fun i => cons x e (match i with | 0 => 0 | j+1 => v j+1)) =
        cons x (fun i => e (v i)) := by funext i; cases i <;> rfl
    exact (ih (a+1) _ (cons x e)).trans (he ▸ Iff.rfl)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SentenceSupportFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.SentenceCoding
open ElementaryModel RelativeConstructible BoundedSetTheory TransitiveNameModel
open BoundedDefinability SetModelFunctions SetModelReals
universe u

variable {M : ZFSet.{u}}

theorem defPairMem (C : Context M) (i j g : ℕ) :
    Definable M (fun e => ZFSet.pair (e i) (e j) ∈ e g) :=
  ⟨.pairMem (2*i) (2*j) (2*g),fun _ => ZFSet.omega,fun _ => C.omega_mem,
    fun e => by simp only [Formula.eval_pairMem,mix_even]⟩

end TuringRigidity.SentenceCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SigmaParameterized
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedDefinability
open BoundedSetTheory TransitiveNameModel SetModelFunctions
universe u

variable {M : ZFSet.{u}} {P Q : (ℕ → ZFSet.{u}) → Prop}

theorem Definable.toSigma (hM : Transitive M) (h : Definable M P) : SigmaDefinable M P := by
  obtain ⟨p,d,hd,hp⟩ := h
  refine ⟨.bounded p,d,hd,?_⟩
  intro e he
  exact (p.absolute M hM (mix e d) (by
    intro i; unfold mix; split <;> first | exact he _ | exact hd _)).trans (hp e)

theorem SigmaDefinable.existsSet (h : SigmaDefinable M P) :
    SigmaDefinable M (fun e => ∃ x ∈ M, P (cons x e)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  refine ⟨.existsSet (p.rename bindSlots),d,hd,?_⟩
  intro e he
  simp only [SigmaFormula.Realize,SigmaFormula.realize_rename]
  apply exists_congr; intro x
  apply and_congr_right; intro hx
  have hh := bind_mix x e d
  change (p.Realize M (cons x (mix e d) ∘ bindSlots)) ↔ _
  rw [hh]
  exact hp (cons x e) (by intro i; cases i; exact hx; exact he _)

theorem SigmaDefinable.congr (h : SigmaDefinable M P)
    (hPQ : ∀ e, (∀ i, e i ∈ M) → (P e ↔ Q e)) : SigmaDefinable M Q := by
  obtain ⟨p,d,hd,hp⟩ := h
  exact ⟨p,d,hd,fun e he => (hp e he).trans (hPQ e he)⟩

end TuringRigidity.BoundedDefinability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_HierarchyGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem HierarchyGraph.correct {M R d r f : ZFSet.{u}}
    (h : HierarchyGraph M (seed R) d r f) (x : ZFSet.{u}) (hx : x ∈ d)
    (v : ZFSet.{u}) (hv : v ∈ r) (hfv : ZFSet.pair x v ∈ f) :
    v = definablePower (stage R x) := by
  induction x using ZFSet.inductionOn generalizing v with
  | h x ih =>
    obtain ⟨A,_,hs,rfl⟩ := h.2.2 x hx v hv hfv
    congr 1
    apply ZFSet.ext; intro z
    rw [mem_stage]
    constructor
    · intro hz
      rcases hs.2.1 z hz with hz|⟨y,hy,w,hw,hfw,hz⟩
      · exact Or.inl hz
      · rw [ih y hy (h.1 x hx y hy) w hw hfw] at hz
        exact Or.inr ⟨y,hy,hz⟩
    · rintro (hz|⟨y,hy,hz⟩)
      · exact hs.1 hz
      · obtain ⟨w,hw,hfw,_⟩ := h.2.1.2 y (h.1 x hx y hy)
        rw [← ih y hy (h.1 x hx y hy) w hw hfw] at hz
        exact hs.2.2 y hy w hw hfw hz

theorem HierarchyGraph.mem_iff {M R d r f : ZFSet.{u}}
    (h : HierarchyGraph M (seed R) d r f) (z : ZFSet.{u}) :
    z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (definablePower (stage R x)) := by
  constructor
  · intro hz
    obtain ⟨x,hx,v,hv,rfl⟩ := h.2.1.1 z hz
    exact ⟨x,hx,by rw [h.correct x hx v hv hz]⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨v,hv,hfv,_⟩ := h.2.1.2 x hx
    rw [← h.correct x hx v hv hfv]
    exact hfv

theorem HierarchyGraph.unique {M N R d r t f g : ZFSet.{u}}
    (hf : HierarchyGraph M (seed R) d r f) (hg : HierarchyGraph N (seed R) d t g) : f = g := by
  apply ZFSet.ext; intro z
  exact (hf.mem_iff z).trans (hg.mem_iff z).symm

theorem mem_stageImage (s x f z : ZFSet.{u}) :
    z ∈ stageImage s x f ↔ z ∈ s ∨ ∃ y ∈ x, ∃ w, ZFSet.pair y w ∈ f ∧ z ∈ w := by
  rw [stageImage,ZFSet.mem_union,ZFSet.mem_sep]
  apply or_congr_right
  constructor
  · rintro ⟨_,y,hy,w,_,hf,hz⟩; exact ⟨y,hy,w,hf,hz⟩
  · rintro ⟨y,hy,w,hf,hz⟩
    have hw := second_mem_doubleUnion hf
    exact ⟨ZFSet.mem_sUnion.mpr ⟨w,hw,hz⟩,y,hy,w,hw,hf,hz⟩

theorem stageImage_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {s x f : ZFSet.{u}} (hs : s ∈ M) (hx : x ∈ M) (hf : f ∈ M) : stageImage s x f ∈ M := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have hr := iterUnion_mem M hM hT.union hf 2
  have hd := (((defPairMem C 1 0 4).and (member_definable C 2 0)).existsMem 4).existsMem 1
  let e := cons x (cons f (fun _ => iterUnion 2 f))
  have he : ∀ i, e i ∈ M := by intro i; rcases i with _|_|i; exact hx; exact hf; exact hr
  exact binary_union_mem M hM hT.pairing hT.union hs
    (hd.sep_mem C e he (union_mem M hM hT.union hr))

theorem hierarchyGraph_of_mem_iff (M R d f : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hs : seed R ∈ M) (hdM : d ∈ M) (hfM : f ∈ M) (hd : Transitive d)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (definablePower (stage R x))) :
    HierarchyGraph M (seed R) d (iterUnion 2 f) f := by
  have hpair (x v : ZFSet.{u}) : ZFSet.pair x v ∈ f ↔ x ∈ d ∧ v = definablePower (stage R x) := by
    rw [hf]
    constructor
    · rintro ⟨y,hy,he⟩
      obtain ⟨rfl,hv⟩ := ZFSet.pair_inj.mp he
      exact ⟨hy,hv⟩
    · rintro ⟨hx,rfl⟩; exact ⟨x,hx,rfl⟩
  refine ⟨hd,⟨?_,?_⟩,?_⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := (hf z).mp hz
    exact ⟨x,hx,_,second_mem_doubleUnion hz,rfl⟩
  · intro x hx
    have hp := (hpair x _).mpr ⟨hx,rfl⟩
    exact ⟨_,second_mem_doubleUnion hp,hp,fun v _ hv => (hpair x v).mp hv |>.2⟩
  · intro x hx v _ hv
    have he := (hpair x v).mp hv |>.2
    subst v
    have hA : stageImage (seed R) x f = stage R x := by
      apply ZFSet.ext; intro z
      rw [mem_stageImage,mem_stage]
      apply or_congr_right
      constructor
      · rintro ⟨y,hy,w,hw,hz⟩
        rw [(hpair y w).mp hw |>.2] at hz
        exact ⟨y,hy,hz⟩
      · rintro ⟨y,hy,hz⟩
        exact ⟨y,hy,_,(hpair y _).mpr ⟨hd x hx y hy,rfl⟩,hz⟩
    refine ⟨stage R x,hA ▸ stageImage_mem M hM hT hs (hM d hdM x hx) hfM,?_,rfl⟩
    refine ⟨seed_subset_stage R x,?_,?_⟩
    · intro z hz
      rcases (mem_stage R x z).mp hz with hz|⟨y,hy,hz⟩
      · exact Or.inl hz
      · have hp := (hpair y _).mpr ⟨hd x hx y hy,rfl⟩
        exact Or.inr ⟨y,hy,_,second_mem_doubleUnion hp,hp,hz⟩
    · intro y hy w _ hw
      rw [(hpair y w).mp hw |>.2]
      exact definablePower_subset_stage R hy

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ContextHierarchyGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem stageImage_mem_context (M : ZFSet.{u}) (C : Context M)
    {s x f : ZFSet.{u}} (hs : s ∈ M) (hx : x ∈ M) (hf : f ∈ M) : stageImage s x f ∈ M := by
  have hr := iterUnion_mem M C.transitive C.union hf 2
  have hd := (((defPairMem C 1 0 4).and (member_definable C 2 0)).existsMem 4).existsMem 1
  let e := cons x (cons f (fun _ => iterUnion 2 f))
  have he : ∀ i, e i ∈ M := by intro i; rcases i with _|_|i; exact hx; exact hf; exact hr
  exact binary_union_mem M C.transitive C.pairing C.union hs
    (hd.sep_mem C e he (union_mem M C.transitive C.union hr))

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SigmaParameterizedClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedDefinability
open BoundedSetTheory TransitiveNameModel SetModelFunctions
universe u
variable {M : ZFSet.{u}} {P Q : (ℕ → ZFSet.{u}) → Prop}

theorem SigmaDefinable.subst (h : SigmaDefinable M P) (r : ℕ → ℕ) :
    SigmaDefinable M (fun e => P (e ∘ r)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  refine ⟨p.rename (slotMap r id),d,hd,?_⟩
  intro e he
  rw [SigmaFormula.realize_rename]
  change p.Realize M (mix e d ∘ slotMap r id) ↔ _
  simpa only [mix_slotMap,Function.comp_id] using hp (e ∘ r) (fun i => he (r i))

theorem SigmaDefinable.and (hP : SigmaDefinable M P) (hQ : SigmaDefinable M Q) :
    SigmaDefinable M (fun e => P e ∧ Q e) := by
  obtain ⟨p,d,hd,hp⟩ := hP
  obtain ⟨q,c,hc,hq⟩ := hQ
  refine ⟨.conj (p.rename (slotMap id (fun i => 2*i)))
    (q.rename (slotMap id (fun i => 2*i+1))),mix d c,?_,?_⟩
  · intro i; unfold mix; split <;> first | exact hd _ | exact hc _
  · intro e he
    rw [SigmaFormula.realize_conj,SigmaFormula.realize_rename,SigmaFormula.realize_rename]
    have hd' : mix d c ∘ (fun i => 2*i) = d := by funext i; simp
    have hc' : mix d c ∘ (fun i => 2*i+1) = c := by funext i; simp
    change p.Realize M (mix e (mix d c) ∘ slotMap id (fun i => 2*i)) ∧
      q.Realize M (mix e (mix d c) ∘ slotMap id (fun i => 2*i+1)) ↔ _
    rw [mix_slotMap,mix_slotMap,Function.comp_id,hd',hc',hp e he,hq e he]

theorem SigmaDefinable.or (h0 : (∅ : ZFSet.{u}) ∈ M)
    (hP : SigmaDefinable M P) (hQ : SigmaDefinable M Q) :
    SigmaDefinable M (fun e => P e ∨ Q e) := by
  obtain ⟨p,d,hd,hp⟩ := hP
  obtain ⟨q,c,hc,hq⟩ := hQ
  refine ⟨.disj (p.rename (slotMap id (fun i => 2*i)))
    (q.rename (slotMap id (fun i => 2*i+1))),mix d c,?_,?_⟩
  · intro i; unfold mix; split <;> first | exact hd _ | exact hc _
  · intro e he
    rw [SigmaFormula.realize_disj M h0,SigmaFormula.realize_rename,SigmaFormula.realize_rename]
    have hd' : mix d c ∘ (fun i => 2*i) = d := by funext i; simp
    have hc' : mix d c ∘ (fun i => 2*i+1) = c := by funext i; simp
    change p.Realize M (mix e (mix d c) ∘ slotMap id (fun i => 2*i)) ∨
      q.Realize M (mix e (mix d c) ∘ slotMap id (fun i => 2*i+1)) ↔ _
    rw [mix_slotMap,mix_slotMap,Function.comp_id,hd',hc',hp e he,hq e he]

theorem SigmaDefinable.impBounded (C : Context M)
    (hP : Definable M P) (hQ : SigmaDefinable M Q) :
    SigmaDefinable M (fun e => P e → Q e) := by
  apply ((hP.neg.toSigma C.transitive).or (C.nat_mem 0) hQ).congr
  intro e _
  classical
  tauto

end TuringRigidity.BoundedDefinability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_HierarchySyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u
variable {M : ZFSet.{u}}

theorem stageStep_definable (C : Context M) (s f r x A : ℕ) :
    Definable M (fun e => StageStep (e s) (e f) (e r) (e x) (e A)) := by
  have hn := defAllMem (defOr (member_definable C 0 (s+1))
    ((((defPairMem C 1 0 (f+3)).and (member_definable C 2 0)).existsMem (r+2)).existsMem (x+1))) A
  have hc := defAllMem (defAllMem (defImp (defPairMem C 1 0 (f+2))
    (defSubset C 0 (A+2))) (r+1)) x
  exact (defSubset C s A).and (hn.and hc)

theorem functionGraph_definable (C : Context M) (d r f : ℕ) :
    Definable M (fun e => FunctionGraph (e d) (e r) (e f)) := by
  refine ⟨.functionGraph (2*f) (2*d) (2*r),fun _ => ZFSet.omega,
    fun _ => C.omega_mem,?_⟩
  intro e
  simp only [Formula.eval_functionGraph,mix_even,FunctionGraph]

theorem sigma_binary_relation (P : ZFSet.{u} → ZFSet.{u} → Prop)
    (h : SigmaDefinable M (fun e => P (e 1) (e 0))) :
    ∃ p : SigmaFormula, ∃ a : ℕ → ZFSet.{u}, (∀ i, a i ∈ M) ∧
      ∀ x ∈ M, ∀ y ∈ M, p.Realize M (cons y (cons x a)) ↔ P x y := by
  obtain ⟨p,a,ha,hp⟩ := h
  let r : ℕ → ℕ := fun i => if i % 2 = 0 then (if i / 2 = 0 then 0 else 1) else i/2+2
  refine ⟨p.rename r,a,ha,?_⟩
  intro x hx y hy
  rw [SigmaFormula.realize_rename]
  have he : cons y (cons x a) ∘ r = mix (cons y (fun _ => x)) a := by
    apply parity_ext
    · intro n
      cases n with
      | zero => rfl
      | succ n => simp [r,show ¬ 2 * (n+1) ≤ 1 by omega]
    · intro n; simp [r,Nat.add_div]
  change p.Realize M (cons y (cons x a) ∘ r) ↔ _
  rw [he]
  exact hp (cons y (fun _ => x)) (by intro i; cases i; exact hy; exact hx)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_InternalHierarchyRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem internal_hierarchyGraph (M R d q : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hs : seed R ∈ M) (hdM : d ∈ M) (hqM : q ∈ M) (hd : Transitive d)
    (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d) (x : ZFSet.{u}) (hx : x ∈ d) :
    ∃ f ∈ M, HierarchyGraph M (seed R) (_root_.OAI.TuringRigidity.BoundedSetTheory.hull d q x) (iterUnion 2 f) f := by
  let hP := hT.pairing
  let hU := hT.union
  let hS := hT.separation.finitePrefix.bounded
  let hR := hT.replacement.finitePrefix
  obtain ⟨p,e,he,hp⟩ := uniform_hierarchy_certificate M R d q hM hT hs hdM hqM hd hq
  induction x using ZFSet.inductionOn with
  | h x ih =>
    have hxM := hM d hdM x hx
    have cert (y f : ZFSet.{u}) (hy : y ∈ x) (hf : f ∈ M) :
        p.Realize M (cons f (cons y e)) ↔
          ∃ r ∈ M, HierarchyGraph M (seed R) (_root_.OAI.TuringRigidity.BoundedSetTheory.hull d q y) r f :=
      hp y (hd x hx y hy) f hf
    obtain ⟨b,hb,hbdef⟩ := hR p e he x hxM (by
      intro y hy
      obtain ⟨f,hf,hfg⟩ := ih y hy (hd x hx y hy)
      refine ⟨f,hf,(cert y f hy hf).mpr
        ⟨_,iterUnion_mem M hM hU hf 2,hfg⟩,?_⟩
      intro g hg hcg
      obtain ⟨r,_,hgg⟩ := (cert y g hy hg).mp hcg
      exact hgg.unique hfg)
    have hbg (f : ZFSet.{u}) : f ∈ b ↔
        ∃ y ∈ x, ∃ r ∈ M, HierarchyGraph M (seed R) (_root_.OAI.TuringRigidity.BoundedSetTheory.hull d q y) r f := by
      constructor
      · intro hf
        have hfM := hM b hb f hf
        obtain ⟨y,hy,hc⟩ := (hbdef f hfM).mp hf
        exact ⟨y,hy,(cert y f hy hfM).mp hc⟩
      · rintro ⟨y,hy,r,hr,hg⟩
        obtain ⟨f',hf',hg'⟩ := ih y hy (hd x hx y hy)
        have heq := hg.unique hg'
        have hfM : f ∈ M := heq ▸ hf'
        exact (hbdef f hfM).mpr ⟨y,hy,(cert y f hy hfM).mpr ⟨r,hr,hg⟩⟩
    let g := ZFSet.sUnion b
    have hgM : g ∈ M := union_mem M hM hU hb
    have hg (z : ZFSet.{u}) : z ∈ g ↔
        ∃ y ∈ x, ∃ w ∈ _root_.OAI.TuringRigidity.BoundedSetTheory.hull d q y, z = ZFSet.pair w (definablePower (stage R w)) := by
      constructor
      · intro hz
        obtain ⟨f,hf,hzf⟩ := ZFSet.mem_sUnion.mp hz
        obtain ⟨y,hy,r,_,hfg⟩ := (hbg f).mp hf
        exact ⟨y,hy,(hfg.mem_iff z).mp hzf⟩
      · rintro ⟨y,hy,w,hw,hz⟩
        obtain ⟨f,hf,hfg⟩ := ih y hy (hd x hx y hy)
        exact ZFSet.mem_sUnion.mpr ⟨f,(hbg f).mpr
          ⟨y,hy,_,iterUnion_mem M hM hU hf 2,hfg⟩,(hfg.mem_iff z).mpr ⟨w,hw,hz⟩⟩
    have hvalue : stageImage (seed R) x g = stage R x := by
      apply ZFSet.ext; intro z
      rw [mem_stageImage,mem_stage]
      apply or_congr_right
      constructor
      · rintro ⟨y,hy,w,hw,hz⟩
        obtain ⟨a,_,v,_,hp⟩ := (hg _).mp hw
        obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
        exact ⟨y,hy,hz⟩
      · rintro ⟨y,hy,hz⟩
        exact ⟨y,hy,_,(hg _).mpr
          ⟨y,hy,y,self_mem_hull d q (hd x hx y hy),rfl⟩,hz⟩
    have hvM : definablePower (stage R x) ∈ M := definablePower_mem M _ hM hT
      (hvalue ▸ stageImage_mem M hM hT hs hxM hgM)
    let f := g ∪ ({ZFSet.pair x (definablePower (stage R x))} : ZFSet.{u})
    have hfM : f ∈ M := binary_union_mem M hM hP hU hgM
      (singleton_mem M hM hP (orderedPair_mem M hM hP hxM hvM))
    refine ⟨f,hfM,hierarchyGraph_of_mem_iff M R _ f hM hT hs
      (hull_mem M d q hM hS hdM hqM hxM) hfM (hull_transitive d q x hd) ?_⟩
    intro z
    change z ∈ g ∪ ({ZFSet.pair x (definablePower (stage R x))} : ZFSet.{u}) ↔ _
    rw [ZFSet.mem_union,ZFSet.mem_singleton,hg]
    constructor
    · rintro (⟨y,hy,w,hw,hz⟩|hz)
      · exact ⟨w,(hull_unfold M d q hM hP hU hS hR hdM hqM hd hq hx w).mpr
          (Or.inr ⟨y,hy,hw⟩),hz⟩
      · exact ⟨x,self_mem_hull d q hx,hz⟩
    · rintro ⟨w,hw,hz⟩
      rcases (hull_unfold M d q hM hP hU hS hR hdM hqM hd hq hx w).mp hw with rfl|⟨y,hy,hw⟩
      · exact Or.inr hz
      · exact Or.inl ⟨y,hy,w,hw,hz⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_InternalConstructibleHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem seed_mem (M R : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) (hR : R ∈ M) :
    seed R ∈ M := by
  obtain ⟨b,hb,hdef⟩ := collect_unionIterates M hM hT.pairing hT.union
    hT.replacement.finitePrefix (sourceT_omega_mem M hM hT)
    (singleton_mem M hM hT.pairing hR)
  have he : ZFSet.sUnion b = seed R := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sUnion,mem_seed]
    constructor
    · rintro ⟨a,ha,hz⟩
      obtain ⟨n,rfl⟩ := (hdef a).mp ha
      exact ⟨n,hz⟩
    · rintro ⟨n,hz⟩
      exact ⟨_,(hdef _).mpr ⟨n,rfl⟩,hz⟩
  exact he ▸ union_mem M hM hT.union hb

theorem internal_hierarchy_cover (M R o : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hR : R ∈ M) (ho : o ∈ M) :
    ∃ d ∈ M, ∃ f ∈ M, o ∈ d ∧
      HierarchyGraph M (seed R) d (iterUnion 2 f) f := by
  obtain ⟨c,hc,hct,hoc⟩ := internal_transitive_container M hM hT.pairing hT.union
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity ho
  obtain ⟨q,hq,hqdef⟩ := internal_power M hM hT.powerSet hc
  obtain ⟨f,hf,hfg⟩ := internal_hierarchyGraph M R c q hM hT (seed_mem M R hM hT hR)
    hc hq hct hqdef o hoc
  exact ⟨hull c q o,hull_mem M c q hM hT.separation.finitePrefix.bounded hc hq ho,
    f,hf,self_mem_hull c q hoc,hfg⟩

theorem stage_mem (M R o : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hR : R ∈ M) (ho : o ∈ M) : stage R o ∈ M := by
  obtain ⟨d,_,f,hf,hod,hfg⟩ := internal_hierarchy_cover M R o hM hT hR ho
  obtain ⟨v,hv,hfv,_⟩ := hfg.2.1.2 o hod
  have hvM : v ∈ M := hM _ (iterUnion_mem M hM hT.union hf 2) v hv
  rw [hfg.correct o hod v hv hfv] at hvM
  exact hM _ hvM _ (self_mem_definablePower (stage R o))

theorem level_mem (M R : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hR : R ∈ M) (o : Ordinal.{u}) (ho : o.toZFSet ∈ M) : level R o ∈ M :=
  stage_mem M R o.toZFSet hM hT hR ho

theorem level_subset_model (M R : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hR : R ∈ M) (o : Ordinal.{u}) (ho : o.toZFSet ∈ M) : level R o ⊆ M :=
  fun x hx => hM _ (level_mem M R hM hT hR o ho) x hx

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel
universe u

theorem relativeModel_subset (M R : ZFSet.{u}) : relativeModel M R ⊆ M :=
  fun _ hx => (ZFSet.mem_sep.mp hx).1

theorem InRelativeModel.mem_ground {M R x : ZFSet.{u}}
    (hM : Transitive M) (hT : SourceT M) (hR : R ∈ M)
    (hx : InRelativeModel M R x) : x ∈ M := by
  obtain ⟨o,ho,hx⟩ := hx
  exact level_subset_model M R hM hT hR o ho hx

theorem mem_relativeModel (M R x : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) :
    x ∈ relativeModel M R ↔ InRelativeModel M R x := by
  rw [relativeModel,ZFSet.mem_sep]
  exact ⟨And.right,fun hx => ⟨hx.mem_ground hM hT hR,hx⟩⟩

theorem InRelativeModel.transitive {M R x y : ZFSet.{u}}
    (hx : InRelativeModel M R x) (hy : y ∈ x) : InRelativeModel M R y := by
  obtain ⟨o,ho,hx⟩ := hx
  exact ⟨o,ho,level_transitive R o x hx y hy⟩

theorem relativeModel_transitive (M R : ZFSet.{u}) (hM : Transitive M) :
    Transitive (relativeModel M R) := by
  intro x hx y hy
  obtain ⟨hxM,hx⟩ := ZFSet.mem_sep.mp hx
  exact ZFSet.mem_sep.mpr ⟨hM x hxM y hy,hx.transitive hy⟩

theorem internal_ordinal_zero (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    (0 : Ordinal.{u}).toZFSet ∈ M := by
  rw [Ordinal.toZFSet_zero]
  exact hM _ (sourceT_omega_mem M hM hT) _ ZFSet.omega_zero

theorem internal_ordinal_succ (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (o : Ordinal.{u}) (ho : o.toZFSet ∈ M) : (o+1).toZFSet ∈ M := by
  rw [Ordinal.toZFSet_add_one]
  have eq : insert o.toZFSet o.toZFSet = ({o.toZFSet} : ZFSet.{u}) ∪ o.toZFSet := by
    apply ZFSet.ext; intro z
    simp only [ZFSet.mem_insert_iff,ZFSet.mem_union,ZFSet.mem_singleton]
  rw [eq]
  exact binary_union_mem M hM hT.pairing hT.union
    (singleton_mem M hM hT.pairing ho) ho

theorem internal_ordinal_max (M : ZFSet.{u}) {i j : Ordinal.{u}}
    (hi : i.toZFSet ∈ M) (hj : j.toZFSet ∈ M) : (max i j).toZFSet ∈ M := by
  rcases le_total i j with h|h
  · simpa only [max_eq_right h] using hj
  · simpa only [max_eq_left h] using hi

theorem level_in_relativeModel (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (o : Ordinal.{u}) (ho : o.toZFSet ∈ M) :
    InRelativeModel M R (level R o) :=
  ⟨o+1,internal_ordinal_succ M hM hT o ho,
    level_mem_level R (lt_add_one o)⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformHierarchyStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem HierarchyGraph.stageStep_iff {M R d r f : ZFSet.{u}}
    (h : HierarchyGraph M (seed R) d r f) (x : ZFSet.{u}) (hx : x ∈ d) (A : ZFSet.{u}) :
    StageStep (seed R) f r x A ↔ A = stage R x := by
  constructor
  · intro hs
    apply ZFSet.ext; intro z
    rw [mem_stage]
    constructor
    · intro hz
      rcases hs.2.1 z hz with hz|⟨y,hy,w,hw,hfw,hz⟩
      · exact Or.inl hz
      · rw [h.correct y (h.1 x hx y hy) w hw hfw] at hz
        exact Or.inr ⟨y,hy,hz⟩
    · rintro (hz|⟨y,hy,hz⟩)
      · exact hs.1 hz
      · obtain ⟨w,hw,hfw,_⟩ := h.2.1.2 y (h.1 x hx y hy)
        rw [← h.correct y (h.1 x hx y hy) w hw hfw] at hz
        exact hs.2.2 y hy w hw hfw hz
  · rintro rfl
    refine ⟨seed_subset_stage R x,?_,?_⟩
    · intro z hz
      rcases (mem_stage R x z).mp hz with hz|⟨y,hy,hz⟩
      · exact Or.inl hz
      · obtain ⟨w,hw,hfw,_⟩ := h.2.1.2 y (h.1 x hx y hy)
        rw [← h.correct y (h.1 x hx y hy) w hw hfw] at hz
        exact Or.inr ⟨y,hy,w,hw,hfw,hz⟩
    · intro y hy w hw hfw
      rw [h.correct y (h.1 x hx y hy) w hw hfw]
      exact definablePower_subset_stage R hy

theorem stage_sigmaDefinable (M R : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hR : R ∈ M) : SigmaDefinable M (fun e => e 0 = stage R (e 1)) := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have hg : SigmaDefinable M (fun e => HierarchyGraph M (seed R) (e 2) (e 0) (e 1)) := by
    have h := hierarchyGraph_sigmaDefinable hM hT 0 3 1 2
    have eq := (equal_param (seed_mem M R hM hT hR) 0).toSigma hM
    exact (eq.and h).existsSet.congr (fun e _ => by simp [seed_mem M R hM hT hR])
  have hs : SigmaDefinable M (fun e => StageStep (seed R) (e 1) (e 0) (e 4) (e 3)) := by
    have h := (stageStep_definable C 0 2 1 5 4).toSigma hM
    have eq := (equal_param (seed_mem M R hM hT hR) 0).toSigma hM
    exact (eq.and h).existsSet.congr (fun e _ => by simp [seed_mem M R hM hT hR])
  have hc := ((member_definable C 4 2).toSigma hM).and (hg.and hs)
  apply hc.existsSet.existsSet.existsSet.congr
  intro e he
  change (∃ d ∈ M, ∃ f ∈ M, ∃ r ∈ M, e 1 ∈ d ∧
    HierarchyGraph M (seed R) d r f ∧ StageStep (seed R) f r (e 1) (e 0)) ↔ _
  constructor
  · rintro ⟨d,_,f,_,r,_,hx,hg,hs⟩
    exact (hg.stageStep_iff (e 1) hx (e 0)).mp hs
  · intro hv
    obtain ⟨d,hd,f,hf,hx,hg⟩ := internal_hierarchy_cover M R (e 1) hM hT hR (he 1)
    exact ⟨d,hd,f,hf,_,iterUnion_mem M hM hT.union hf 2,hx,hg,
      (hg.stageStep_iff (e 1) hx (e 0)).mpr hv⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeModelSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel BoundedDefinability SetModelFunctions
universe u

theorem eval_ordinalFormula (i : ℕ) (e : ℕ → ZFSet.{u}) :
    (ordinalFormula i).Eval e ↔ (e i).IsOrdinal := by
  rw [ZFSet.isOrdinal_iff_forall_mem_isTransitive]
  simp only [ordinalFormula,Formula.Eval,Formula.eval_transitive,
    Formula.eval_allMem,cons_zero]
  rfl

theorem ordinal_definable {M : ZFSet.{u}} (C : Context M) (i : ℕ) :
    Definable M (fun e => (e i).IsOrdinal) :=
  ⟨ordinalFormula (2*i),fun _ => ZFSet.omega,fun _ => C.omega_mem,
    fun e => by rw [eval_ordinalFormula,mix_even]⟩

theorem relativeLevel_sigmaDefinable (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) :
    SigmaDefinable M (fun e => (e 0).IsOrdinal ∧ e 1 ∈ stage R (e 0)) := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,
    hT.separation.finitePrefix.bounded,hT.infinity⟩
  have h := (stage_sigmaDefinable M R hM hT hR).and
    (((ordinal_definable C 1).toSigma hM).and ((member_definable C 2 0).toSigma hM))
  apply h.existsSet.congr
  intro e he
  change (∃ A ∈ M, A = stage R (e 0) ∧ (e 0).IsOrdinal ∧ e 1 ∈ A) ↔ _
  constructor
  · rintro ⟨A,_,rfl,ho,hx⟩; exact ⟨ho,hx⟩
  · rintro ⟨ho,hx⟩
    exact ⟨_,stage_mem M R (e 0) hM hT hR (he 0),rfl,ho,hx⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeModelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel BoundedDefinability SetModelFunctions InternalRank
universe u

theorem relative_level_bound (M R a : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) (ha : a ∈ M)
    (h : ∀ x ∈ a, InRelativeModel M R x) :
    ∃ o : Ordinal.{u}, o.toZFSet ∈ M ∧ a ⊆ level R o := by
  obtain ⟨p,e,he,hp⟩ := sigma_binary_relation
    (fun x o : ZFSet.{u} => o.IsOrdinal ∧ x ∈ stage R o)
    (relativeLevel_sigmaDefinable M R hM hT hR)
  obtain ⟨W,hW,hbound⟩ := sigma_collection M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hT.choice
    p e he a ha (by
      intro x hx
      obtain ⟨o,ho,hxo⟩ := h x hx
      exact ⟨o.toZFSet,ho,(hp x (hM a ha x hx) o.toZFSet ho).mpr
        ⟨ZFSet.isOrdinal_toZFSet o,hxo⟩⟩)
  have hr : W.rank.toZFSet ∈ M := by
    rw [← rankSet_eq_ordinal]
    exact rankSet_mem_ground M hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hW
  refine ⟨W.rank,hr,?_⟩
  intro x hx
  obtain ⟨o,ho,hxo⟩ := hbound x hx
  obtain ⟨hord,hxo⟩ := (hp x (hM a ha x hx) o (hM W hW o ho)).mp hxo
  have hxl : x ∈ level R o.rank := by
    change x ∈ stage R o.rank.toZFSet
    rwa [hord.toZFSet_rank_eq]
  exact level_mono R (ZFSet.rank_lt_of_mem ho).le hxl

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeModelClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel ElementaryModel SentenceForm
universe u

theorem finite_parameters_in_relative_level (M R : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (e : ℕ → ZFSet.{u}) (n : ℕ)
    (he : ∀ i, i < n → InRelativeModel M R (e i)) :
    ∃ o : Ordinal.{u}, o.toZFSet ∈ M ∧ ∀ i, i < n → e i ∈ level R o := by
  induction n with
  | zero => exact ⟨0,internal_ordinal_zero M hM hT,fun _ hi => (Nat.not_lt_zero _ hi).elim⟩
  | succ n ih =>
    obtain ⟨o,ho,hoe⟩ := ih (fun i hi => he i (Nat.lt_succ_of_lt hi))
    obtain ⟨p,hp,hpe⟩ := he n (Nat.lt_succ_self n)
    refine ⟨max o p,internal_ordinal_max M ho hp,fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi|rfl
    · exact level_mono R (le_max_left o p) (hoe i hi)
    · exact level_mono R (le_max_right o p) hpe

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeSigmaWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel BoundedDefinability SetModelFunctions
open ElementaryModel SentenceForm
universe u

theorem relative_level_subset (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) {o : Ordinal.{u}} (ho : o.toZFSet ∈ M) :
    level R o ⊆ relativeModel M R :=
  fun x hx => (mem_relativeModel M R x hM hT hR).mpr ⟨o,ho,hx⟩

theorem relative_sigma_level_witness (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) (i : Ordinal.{u}) (hi : i.toZFSet ∈ M)
    (φ : SigmaFormula) (e : ℕ → ZFSet.{u}) (he : ∀ n, e n ∈ level R i)
    (hφ : φ.Realize (relativeModel M R) e) :
    ∃ o : Ordinal.{u}, o.toZFSet ∈ M ∧ level R i ⊆ level R o ∧
      φ.Realize (level R o) e := by
  obtain ⟨xs,hlen,hxs,hmat⟩ := (φ.realize_iff_prefix _ e).mp hφ
  have hsM := FiniteTuple.elements_mem M hM hT.pairing hT.union
    (by simpa only [Ordinal.toZFSet_zero] using internal_ordinal_zero M hM hT) xs
    (fun x hx => relativeModel_subset M R (hxs x hx))
  obtain ⟨j,hj,hjs⟩ := relative_level_bound M R (FiniteTuple.elements xs) hM hT hR hsM
    (fun x hx => (mem_relativeModel M R x hM hT hR).mp
      (hxs x ((FiniteTuple.mem_elements x xs).mp hx)))
  have hlist : ∀ x ∈ xs, x ∈ level R (max i j) := fun x hx =>
    level_mono R (le_max_right i j) (hjs ((FiniteTuple.mem_elements x xs).mpr hx))
  have heL : ∀ n, e n ∈ level R (max i j) := fun n => level_mono R (le_max_left i j) (he n)
  have heN := fun n => relative_level_subset M R hM hT hR hi (he n)
  refine ⟨max i j,internal_ordinal_max M hi hj,level_mono R (le_max_left i j),
    (φ.realize_iff_prefix _ e).mpr ⟨xs,hlen,hlist,?_⟩⟩
  exact (φ.matrix.absolute _ (level_transitive R _) _ (SigmaFormula.feed_mem xs e _ hlist heL)).mpr
    ((φ.matrix.absolute _ (relativeModel_transitive M R hM) _
      (SigmaFormula.feed_mem xs e _ hxs heN)).mp hmat)

theorem sigmaDefinable_request_bound {M : ZFSet.{u}}
    {P : (ℕ → ZFSet.{u}) → Prop} (h : SigmaDefinable M P)
    (hM : Transitive M) (hT : SourceT M) (e : ℕ → ZFSet.{u})
    (he : ∀ i, e i ∈ M) {a : ZFSet.{u}} (ha : a ∈ M) :
    ∃ W ∈ M, ∀ x ∈ a, (∃ y ∈ M, P (cons y (cons x e))) →
      ∃ y ∈ W, P (cons y (cons x e)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  let q := (p.rename bindSlots).rename (liftMap bindSlots)
  have hm : ∀ i, mix e d i ∈ M := by
    intro i; unfold mix; split <;> first | exact he _ | exact hd _
  have hq (x y : ZFSet.{u}) (hx : x ∈ M) (hy : y ∈ M) :
      q.Realize M (cons y (cons x (mix e d))) ↔ P (cons y (cons x e)) := by
    dsimp only [q]
    rw [SigmaFormula.realize_rename]
    have eq : (fun n => cons y (cons x (mix e d)) (liftMap bindSlots n)) =
        cons y (mix (cons x e) d) := by
      funext n; cases n with
      | zero => rfl
      | succ n => exact congrFun (bind_mix x e d) n
    rw [eq,SigmaFormula.realize_rename]
    change p.Realize M (cons y (mix (cons x e) d) ∘ bindSlots) ↔ _
    rw [bind_mix]
    exact hp _ (by
      intro i
      rcases i with _|i; exact hy
      rcases i with _|i; exact hx
      exact he i)
  obtain ⟨W,hW,hw⟩ := internal_sigma_request_bound M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hT.choice q (mix e d) hm ha
  refine ⟨W,hW,?_⟩
  intro x hx hxy
  have hxM := hM a ha x hx
  obtain ⟨y,hy,hqxy⟩ := hw x hx (by
    obtain ⟨y,hy,hxy⟩ := hxy
    exact ⟨y,hy,(hq x y hxM hy).mpr hxy⟩)
  exact ⟨y,hy,(hq x y hxM (hM W hW y hy)).mp hqxy⟩

theorem relative_sigma_request_definable (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) (φ : SigmaFormula) :
    SigmaDefinable M (fun e => (e 0).IsOrdinal ∧ e 2 ⊆ stage R (e 0) ∧
      φ.Realize (stage R (e 0)) (cons (e 1) (fun i => e (i+3)))) := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,
    hT.separation.finitePrefix.bounded,hT.infinity⟩
  let v : ℕ → ℕ := fun n => match n with | 0 => 4 | k+1 => 2*(k+4)
  have hs : Definable M (fun e => φ.Realize (e 0) (cons (e 2) (fun i => e (i+4)))) := by
    refine ⟨setBounded (fromSigma φ) 0 v,fun _ => ZFSet.omega,fun _ => C.omega_mem,?_⟩
    intro e
    rw [setBounded_eval,show mix e (fun _ => ZFSet.omega) 0 = e 0 from rfl,sigma_sat]
    have eq : (fun i => mix e (fun _ => ZFSet.omega) (v i)) =
        cons (e 2) (fun i => e (i+4)) := by
      funext i; cases i with
      | zero => exact mix_even e (fun _ => ZFSet.omega) 2
      | succ i => simp [v]
    rw [eq]
  have h := (stage_sigmaDefinable M R hM hT hR).and
    (((ordinal_definable C 1).toSigma hM).and
      (((SentenceCoding.defSubset C 3 0).toSigma hM).and (hs.toSigma hM)))
  apply h.existsSet.congr
  intro e he
  change (∃ A ∈ M, A = stage R (e 0) ∧ (e 0).IsOrdinal ∧ e 2 ⊆ A ∧
    φ.Realize A (cons (e 1) (fun i => e (i+3)))) ↔ _
  constructor
  · rintro ⟨A,_,rfl,ho,ht,hφ⟩; exact ⟨ho,ht,hφ⟩
  · rintro ⟨ho,ht,hφ⟩
    exact ⟨_,stage_mem M R (e 0) hM hT hR (he 0),rfl,ho,ht,hφ⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeSigmaReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel InternalRank
universe u

theorem relative_sigma_reflection (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) (i : Ordinal.{u}) (hi : i.toZFSet ∈ M)
    (φ : SigmaFormula) (e : ℕ → ZFSet.{u}) (he : ∀ n, e n ∈ level R i)
    (a : ZFSet.{u}) (ha : a ∈ level R i) :
    ∃ o : Ordinal.{u}, o.toZFSet ∈ M ∧ level R i ⊆ level R o ∧
      ∀ x ∈ a, φ.Realize (relativeModel M R) (cons x e) ↔
        φ.Realize (level R o) (cons x e) := by
  have ht := level_mem M R hM hT hR i hi
  have haM := hM _ ht a ha
  have heM : ∀ n, cons (level R i) e n ∈ M := by
    intro n; cases n; exact ht; exact hM _ ht _ (he _)
  obtain ⟨W,hW,hw⟩ := sigmaDefinable_request_bound
    (relative_sigma_request_definable M R hM hT hR φ) hM hT (cons (level R i) e) heM haM
  have hr : W.rank.toZFSet ∈ M := by
    rw [← rankSet_eq_ordinal]
    exact rankSet_mem_ground M hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hW
  let o := max i W.rank
  have ho : o.toZFSet ∈ M := internal_ordinal_max M hi hr
  have hio : level R i ⊆ level R o := level_mono R (le_max_left i W.rank)
  refine ⟨o,ho,hio,?_⟩
  intro x hx
  have heI : ∀ n, cons x e n ∈ level R i := by
    intro n; cases n; exact level_transitive R i a ha x hx; exact he _
  constructor
  · intro hφ
    obtain ⟨j,hj,hij,hφj⟩ := relative_sigma_level_witness M R hM hT hR i hi φ (cons x e) heI hφ
    obtain ⟨z,hz,hord,htz,hφz⟩ := hw x hx ⟨j.toZFSet,hj,ZFSet.isOrdinal_toZFSet j,hij,hφj⟩
    change z.IsOrdinal at hord
    change level R i ⊆ stage R z at htz
    change φ.Realize (stage R z) (cons x e) at hφz
    have heq : stage R z = level R z.rank := by
      change stage R z = stage R z.rank.toZFSet
      rw [hord.toZFSet_rank_eq]
    rw [heq] at htz hφz
    exact φ.transitive_upward (level_transitive R _) (level_transitive R _)
      (level_mono R ((ZFSet.rank_lt_of_mem hz).le.trans (le_max_right i W.rank)))
      (cons x e) (fun n => htz (heI n)) hφz
  · intro hφ
    exact φ.transitive_upward (level_transitive R o) (relativeModel_transitive M R hM)
      (relative_level_subset M R hM hT hR ho) (cons x e) (fun n => hio (heI n)) hφ

theorem relative_sigma_parameter_bound (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (φ : SigmaFormula) (e : ℕ → ZFSet.{u})
    (he : ∀ n, InRelativeModel M R (e n)) (a : ZFSet.{u})
    (ha : InRelativeModel M R a) :
    ∃ i : Ordinal.{u}, i.toZFSet ∈ M ∧ a ∈ level R i ∧
      ∃ e' : ℕ → ZFSet.{u}, (∀ n, e' n ∈ level R i) ∧ (∀ n, n < φ.scope → e' n = e n) ∧
        ∀ N x : ZFSet.{u}, φ.Realize N (cons x e') ↔ φ.Realize N (cons x e) := by
  obtain ⟨i,hi,hia⟩ := ha
  obtain ⟨j,hj,hje⟩ := finite_parameters_in_relative_level M R hM hT e φ.scope (fun n _ => he n)
  let e' := fun n => if n < φ.scope then e n else a
  have haL : a ∈ level R (max i j) := level_mono R (le_max_left i j) hia
  refine ⟨max i j,internal_ordinal_max M hi hj,haL,e',?_,?_,?_⟩
  · intro n
    dsimp [e']; split
    next hn => exact level_mono R (le_max_right i j) (hje n hn)
    next => exact haL
  · intro n hn; exact ite_eq_left hn
  · intro N x
    apply φ.realize_congr; intro n hn
    cases n with
    | zero => rfl
    | succ n => exact ite_eq_left (show n < φ.scope by omega)

theorem relativeModel_sigma_collection (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) : SigmaCollection (relativeModel M R) := by
  intro φ e he a ha htotal
  obtain ⟨i,hi,hia,e',he',heq,hcongr⟩ := relative_sigma_parameter_bound M R hM hT
    (.existsSet φ) e (fun n => (mem_relativeModel M R _ hM hT hR).mp (he n)) a
    ((mem_relativeModel M R _ hM hT hR).mp ha)
  obtain ⟨o,ho,hio,hφ⟩ := relative_sigma_reflection M R hM hT hR i hi (.existsSet φ) e' he' a hia
  have hlevel := relative_level_subset M R hM hT hR ho
  refine ⟨level R o,(mem_relativeModel M R _ hM hT hR).mpr
    (level_in_relativeModel M R hM hT o ho),?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := (hφ x hx).mp ((hcongr _ x).mpr (htotal x hx))
  have hup : φ.Realize (relativeModel M R) (cons y (cons x e')) :=
    φ.transitive_upward (level_transitive R o) (relativeModel_transitive M R hM)
      hlevel (cons y (cons x e')) (by
        intro n; rcases n with _|n; exact hy
        rcases n with _|n; exact hio (level_transitive R i a hia x hx)
        exact hio (he' n)) hxy
  refine ⟨y,hy,?_⟩
  apply (φ.realize_congr (relativeModel M R) (cons y (cons x e')) (cons y (cons x e)) ?_).mp hup
  intro n hn
  rcases n with _|n; rfl
  rcases n with _|n; rfl
  exact heq n (by change n < φ.scope-1; omega)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeSigmaSchemas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel ElementaryModel SentenceForm
universe u

theorem relativeModel_sigma_separation (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) : SigmaSeparation (relativeModel M R) := by
  intro φ e he a ha
  let N := relativeModel M R
  obtain ⟨i,hi,hia,e',he',_,hcongr⟩ := relative_sigma_parameter_bound M R hM hT φ e
    (fun n => (mem_relativeModel M R _ hM hT hR).mp (he n)) a
    ((mem_relativeModel M R _ hM hT hR).mp ha)
  obtain ⟨o,ho,hio,hφ⟩ := relative_sigma_reflection M R hM hT hR i hi φ e' he' a hia
  let A := level R o
  let ψ := SentenceForm.conj (.member 0 1) ((fromSigma φ).rename parameterShift)
  have haA : a ∈ A := hio hia
  have hψ := separation_mem_definablePower A ψ (cons a e') (by
    intro n _; cases n; exact haA; exact hio (he' _))
  let b := a.sep (fun x => φ.Realize N (cons x e))
  have eq : A.sep (fun x => ψ.Sat (A : Set ZFSet) (cons x (cons a e'))) = b := by
    apply ZFSet.ext; intro x
    simp only [b,ZFSet.mem_sep,ψ,Sat,cons_zero,cons_succ,shifted_parameters,sigma_sat]
    constructor
    · rintro ⟨_,hxa,hψ⟩
      exact ⟨hxa,(hcongr N x).mp ((hφ x hxa).mpr hψ)⟩
    · rintro ⟨hxa,hψ⟩
      exact ⟨level_transitive R o a haA x hxa,hxa,(hφ x hxa).mp ((hcongr N x).mpr hψ)⟩
  have hb : b ∈ N := by
    apply (mem_relativeModel M R b hM hT hR).mpr
    refine ⟨o+1,internal_ordinal_succ M hM hT o ho,?_⟩
    rw [level_succ,← eq]
    exact hψ
  exact ⟨b,hb,fun _ _ => ZFSet.mem_sep⟩

theorem replacementImageFormula_spec (φ : SigmaFormula) (N a y : ZFSet.{u})
    (hN : Transitive N) (ha : a ∈ N) (e : ℕ → ZFSet.{u}) :
    (replacementImageFormula φ).Realize N (cons y (cons a e)) ↔
      ∃ x ∈ a, φ.Realize N (cons y (cons x e)) := by
  simp only [replacementImageFormula,SigmaFormula.Realize,SigmaFormula.realize_andBounded,
    Formula.Realize,cons_zero,cons_succ,SigmaFormula.realize_rename]
  have eq (x : ZFSet.{u}) : (fun i => cons x (cons y (cons a e)) (replacementImageVars i)) =
      cons y (cons x e) := by
    funext i; rcases i with _|i; rfl
    rcases i with _|i <;> rfl
  simp only [eq]
  exact ⟨fun ⟨x,_,hx,hφ⟩ => ⟨x,hx,hφ⟩,
    fun ⟨x,hx,hφ⟩ => ⟨x,hN a ha x hx,hx,hφ⟩⟩

theorem relativeModel_sigma_replacement (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) : SigmaReplacement (relativeModel M R) := by
  intro φ e he a ha htotal
  let N := relativeModel M R
  have hN := relativeModel_transitive M R hM
  obtain ⟨W,hW,hw⟩ := relativeModel_sigma_collection M R hM hT hR φ e he a ha
    (fun x hx => by obtain ⟨y,hy,hφ,_⟩ := htotal x hx; exact ⟨y,hy,hφ⟩)
  obtain ⟨b,hb,hbdef⟩ := relativeModel_sigma_separation M R hM hT hR
    (replacementImageFormula φ) (cons a e) (by intro n; cases n; exact ha; exact he _) W hW
  refine ⟨b,hb,?_⟩
  intro y hy
  rw [hbdef y hy,replacementImageFormula_spec φ N a y hN ha e]
  constructor
  · exact And.right
  · rintro ⟨x,hx,hφ⟩
    obtain ⟨z,hz,hφz⟩ := hw x hx
    obtain ⟨w,hw,_,hu⟩ := htotal x hx
    have hyz : y = z := (hu y hy hφ).trans (hu z (hN W hW z hz) hφz).symm
    exact ⟨hyz ▸ hz,x,hx,hφ⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_CanonicalOmegaSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem inductiveSetFormula_spec (w : ℕ) (e : ℕ → ZFSet.{u}) :
    (inductiveSetFormula w).Eval e ↔
      (∅ : ZFSet) ∈ e w ∧ ∀ x ∈ e w, insert x x ∈ e w := by
  simp only [inductiveSetFormula,Formula.Eval,Formula.eval_empty,
    Formula.eval_allMem,Formula.eval_successor,cons_zero,cons_succ]
  simp only [exists_eq_right]

theorem omega_subset_inductive {W : ZFSet.{u}}
    (h : (∅ : ZFSet) ∈ W ∧ ∀ x ∈ W, insert x x ∈ W) : ZFSet.omega ⊆ W := by
  intro x hx
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  clear hx
  induction n with
  | zero => exact h.1
  | succ n ih => exact h.2 _ ih

theorem canonicalOmega_spec (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (w : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (canonicalOmega w).Sat (M : Set ZFSet) e ↔ e w = ZFSet.omega := by
  have habs (p : Formula) (x : ZFSet.{u}) (hx : x ∈ M) :
      (fromBounded p).Sat (M : Set ZFSet) (cons x e) ↔ p.Eval (cons x e) := by
    rw [bounded_sat,Formula.absolute p M hM _
      (by intro i; cases i; exact hx; exact he _)]
  have hw : (∅ : ZFSet.{u}) ∈ ZFSet.omega ∧
      ∀ x ∈ ZFSet.omega.{u}, insert x x ∈ ZFSet.omega :=
    ⟨(mem_omega _).mpr ⟨0,rfl⟩,SetModelArithmetic.setSucc_omega⟩
  change ((fromBounded (inductiveSetFormula w)).Sat (M : Set ZFSet) e ∧
    (SentenceForm.all (SentenceForm.imp (fromBounded (inductiveSetFormula 0))
      (fromBounded (.subset (w+1) 0)))).Sat (M : Set ZFSet) e) ↔ _
  simp only [SentenceForm.sat_all,SentenceForm.sat_imp]
  rw [bounded_sat,Formula.absolute _ M hM e he,inductiveSetFormula_spec]
  have hmin : (∀ x ∈ (M : Set ZFSet),
      (fromBounded (inductiveSetFormula 0)).Sat (M : Set ZFSet) (cons x e) →
      (fromBounded (.subset (w+1) 0)).Sat (M : Set ZFSet) (cons x e)) ↔
      ∀ x ∈ M, ((∅ : ZFSet) ∈ x ∧ ∀ y ∈ x, insert y y ∈ x) → e w ⊆ x := by
    apply forall_congr'; intro x
    apply forall_congr'; intro hx
    rw [habs _ x hx,habs _ x hx,inductiveSetFormula_spec,Formula.eval_subset]
    rfl
  rw [hmin]
  constructor
  · rintro ⟨hi,hminimal⟩
    exact ZFSet.ext fun x => ⟨fun hx => hminimal _ hω hw hx,fun hx => omega_subset_inductive hi hx⟩
  · intro h
    rw [h]
    exact ⟨hw,fun _ _ hi => omega_subset_inductive hi⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalOrderType
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

theorem value_isOrdinal {d r : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (ht : TransitiveOn d r) (x : ZFSet.{u}) (hx : x ∈ d) :
    (value d r wf x).IsOrdinal := by
  induction x using wf.induction with
  | h x ih =>
    apply ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr
    constructor
    · intro y hy z hz
      obtain ⟨b,hb,hbx,rfl⟩ := (mem_value d r wf x y).mp hy
      obtain ⟨a,ha,hab,rfl⟩ := (mem_value d r wf b z).mp hz
      exact (mem_value d r wf x _).mpr ⟨a,ha,ht a ha b hb x hx hab hbx,rfl⟩
    · intro y hy
      obtain ⟨a,ha,hax,rfl⟩ := (mem_value d r wf x y).mp hy
      exact ih a ⟨ha,hax⟩ ha

theorem mem_ordinalRange (d r : ZFSet.{u}) (wf : WellFounded (Rel d r)) (z : ZFSet.{u}) :
    z ∈ ordinalRange d r wf ↔ ∃ x ∈ d, z = value d r wf x := by
  rw [ordinalRange,ZFSet.mem_range]
  constructor
  · rintro ⟨s,hs⟩; exact ⟨label d s,label_mem d s,hs.symm⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨s,rfl⟩ := label_surjective d hx
    exact ⟨s,rfl⟩

theorem ordinalRange_isOrdinal {d r : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (ht : TransitiveOn d r) : (ordinalRange d r wf).IsOrdinal := by
  apply ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr
  constructor
  · intro x hx y hy
    obtain ⟨a,_,rfl⟩ := (mem_ordinalRange d r wf x).mp hx
    obtain ⟨b,hb,_,rfl⟩ := (mem_value d r wf a y).mp hy
    exact (mem_ordinalRange d r wf _).mpr ⟨b,hb,rfl⟩
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := (mem_ordinalRange d r wf x).mp hx
    exact value_isOrdinal wf ht a ha

theorem orderType_toZFSet {d r : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (ht : TransitiveOn d r) : (orderType d r wf).toZFSet = ordinalRange d r wf :=
  (ordinalRange_isOrdinal wf ht).toZFSet_rank_eq

theorem orderType_internal (M d r : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hd : d ∈ M) (hr : r ∈ M) (wf : WellFounded (Rel d r))
    (ht : TransitiveOn d r) :
    (orderType d r wf).toZFSet ∈ M ∧
      ∃ f ∈ M, Graph d r d (orderType d r wf).toZFSet f ∧
        ∀ z ∈ (orderType d r wf).toZFSet, ∃ x ∈ d, ZFSet.pair x z ∈ f := by
  obtain ⟨f,hf,hg⟩ := internal_graph M d r hM hP hU hPow hS hR hd hr wf
  have heq : graphRange d f = ordinalRange d r wf := by
    apply ZFSet.ext; intro z
    exact (hg.range_iff wf z).trans (mem_ordinalRange d r wf z).symm
  have hm : ordinalRange d r wf ∈ M := heq ▸ graphRange_mem M hM hU hS hd hf
  rw [orderType_toZFSet wf ht]
  refine ⟨hm,f,hf,?_,?_⟩
  · refine ⟨(fun _ hx => hx),(fun _ _ _ hy _ => hy),?_,?_,?_⟩
    · intro z hz
      obtain ⟨x,hx,rfl⟩ := (hg.mem_iff wf z).mp hz
      exact ⟨x,hx,_,(mem_ordinalRange d r wf _).mpr ⟨x,hx,rfl⟩,rfl⟩
    · intro x hx
      refine ⟨value d r wf x,(mem_ordinalRange d r wf _).mpr ⟨x,hx,rfl⟩,
        (hg.mem_iff wf _).mpr ⟨x,hx,rfl⟩,?_⟩
      intro z _ hxz
      obtain ⟨y,_,he⟩ := (hg.mem_iff wf _).mp hxz
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
      rfl
    · intro x hx z _ hxz
      obtain ⟨y,hy,he⟩ := (hg.mem_iff wf _).mp hxz
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
      constructor
      · intro z hz
        obtain ⟨y,hy,hyx,rfl⟩ := (mem_value d r wf x z).mp hz
        exact ⟨y,hy,hyx,(hg.mem_iff wf _).mpr ⟨y,hy,rfl⟩⟩
      · intro y hy hyx z _ hyz
        obtain ⟨w,_,he⟩ := (hg.mem_iff wf _).mp hyz
        obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
        exact (mem_value d r wf x _).mpr ⟨y,hy,hyx,rfl⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := (mem_ordinalRange d r wf z).mp hz
    exact ⟨x,hx,(hg.mem_iff wf _).mpr ⟨x,hx,rfl⟩⟩

end TuringRigidity.RelationCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalOrderTypeSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory ElementaryModel RelativeConstructible
universe u

theorem OrderTypeCertificate.exact {d r a f : ZFSet.{u}}
    (wf : WellFounded (Rel d r)) (ht : TransitiveOn d r)
    (hc : OrderTypeCertificate d r a f) : a = (orderType d r wf).toZFSet := by
  rw [orderType_toZFSet wf ht]
  apply ZFSet.ext; intro z
  rw [mem_ordinalRange]
  constructor
  · intro hz
    obtain ⟨x,hx,hxz⟩ := hc.2.2 z hz
    exact ⟨x,hx,hc.2.1.correct wf x hx z hz hxz⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨z,hz,hxz,_⟩ := hc.2.1.2.2.2.1 x hx
    exact hc.2.1.correct wf x hx z hz hxz ▸ hz

theorem orderTypeMatrix_eval (a d r f : ℕ) (e : ℕ → ZFSet.{u}) :
    (orderTypeMatrix a d r f).Eval e ↔ OrderTypeCertificate (e d) (e r) (e a) (e f) := by
  simp only [orderTypeMatrix,OrderTypeCertificate,Formula.Eval,eval_ordinalFormula,
    Code.eval_graph,Formula.eval_allMem,Formula.eval_pairMem,cons_zero,cons_succ]

end TuringRigidity.RelationCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalOrderPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

theorem value_of_ordinal_presentation (d r : ZFSet.{u}) (o : Ordinal.{u})
    (wf : WellFounded (Rel d r)) (j : ZFSet.{u} → ZFSet.{u})
    (hj : ∀ x ∈ d, j x ∈ o.toZFSet)
    (hs : ∀ z ∈ o.toZFSet, ∃ x ∈ d, j x = z)
    (he : ∀ x ∈ d, ∀ y ∈ d, ZFSet.pair x y ∈ r ↔ j x ∈ j y)
    (x : ZFSet.{u}) (hx : x ∈ d) : value d r wf x = j x := by
  induction x using wf.induction with
  | h x ih =>
    apply ZFSet.ext; intro z
    rw [mem_value]
    constructor
    · rintro ⟨y,hy,hyx,rfl⟩
      rw [ih y ⟨hy,hyx⟩ hy]
      exact (he y hy x hx).mp hyx
    · intro hz
      have hzo := (ZFSet.isOrdinal_toZFSet o).subset_of_mem (hj x hx) hz
      obtain ⟨y,hy,hyz⟩ := hs z hzo
      have hyx : ZFSet.pair y x ∈ r := (he y hy x hx).mpr (hyz ▸ hz)
      exact ⟨y,hy,hyx,hyz.symm.trans (ih y ⟨hy,hyx⟩ hy).symm⟩

theorem orderType_of_ordinal_presentation (d r : ZFSet.{u}) (o : Ordinal.{u})
    (wf : WellFounded (Rel d r)) (j : ZFSet.{u} → ZFSet.{u})
    (hj : ∀ x ∈ d, j x ∈ o.toZFSet)
    (hs : ∀ z ∈ o.toZFSet, ∃ x ∈ d, j x = z)
    (he : ∀ x ∈ d, ∀ y ∈ d, ZFSet.pair x y ∈ r ↔ j x ∈ j y) :
    orderType d r wf = o := by
  have hr : ordinalRange d r wf = o.toZFSet := by
    apply ZFSet.ext; intro z
    rw [mem_ordinalRange]
    constructor
    · rintro ⟨x,hx,rfl⟩
      rw [value_of_ordinal_presentation d r o wf j hj hs he x hx]
      exact hj x hx
    · intro hz
      obtain ⟨x,hx,heq⟩ := hs z hz
      exact ⟨x,hx,heq.symm.trans (value_of_ordinal_presentation d r o wf j hj hs he x hx).symm⟩
  unfold orderType
  rw [hr,Ordinal.rank_toZFSet]

end TuringRigidity.RelationCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalProductSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse
universe u

theorem productLessFormula_eval (a b x y : ℕ) (e : ℕ → ZFSet.{u}) :
    (productLessFormula a b x y).Eval e ↔ ProductLess (e a) (e b) (e x) (e y) := by
  simp [productLessFormula,Formula.Eval,ProductLess]

theorem productRelationFormula_eval (a b p : ZFSet.{u}) :
    productRelationFormula.Eval (cons p (cons (ZFSet.prod b a) (cons a (fun _ => b)))) ↔
      ∃ x ∈ ZFSet.prod b a, ∃ y ∈ ZFSet.prod b a,
        p = ZFSet.pair x y ∧ ProductLess a b x y := by
  simp [productRelationFormula,Formula.Eval,productLessFormula_eval]

theorem productRelation_mem (M a b : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (ha : a ∈ M) (hb : b ∈ M) : productRelation a b ∈ M := by
  have hd := product_mem M hM hP hU hPow hS hb ha
  let e := cons (ZFSet.prod b a) (cons a (fun _ => b))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    · exact hd
    · exact ha
    · exact hb
  have hs := sep_mem M hM hS productRelationFormula e he
    (product_mem M hM hP hU hPow hS hd hd)
  have eq : ZFSet.sep (fun p => productRelationFormula.Eval (cons p e))
      (ZFSet.prod (ZFSet.prod b a) (ZFSet.prod b a)) = productRelation a b := by
    apply ZFSet.ext; intro p
    simp only [productRelation,ZFSet.mem_sep,e,productRelationFormula_eval]
  exact eq ▸ hs

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalProductPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse
universe u

theorem productValue_mem (a b : Ordinal.{u}) (x : ZFSet.{u})
    (hx : x ∈ ZFSet.prod b.toZFSet a.toZFSet) : productValue a x ∈ (a*b).toZFSet := by
  obtain ⟨s,hs,t,ht,rfl⟩ := ZFSet.mem_prod.mp hx
  obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hs
  obtain ⟨d,hd,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
  rw [productValue_pair,Ordinal.rank_toZFSet,Ordinal.rank_toZFSet,Ordinal.toZFSet_mem_toZFSet_iff]
  exact Ordinal.lt_mul_iff.mpr ⟨c,hc,d,hd,rfl⟩

theorem productValue_surjective (a b : Ordinal.{u}) (z : ZFSet.{u})
    (hz : z ∈ (a*b).toZFSet) :
    ∃ x ∈ ZFSet.prod b.toZFSet a.toZFSet, productValue a x = z := by
  obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
  obtain ⟨q,hq,r,hr,rfl⟩ := Ordinal.lt_mul_iff.mp hc
  refine ⟨ZFSet.pair q.toZFSet r.toZFSet,ZFSet.mem_prod.mpr
    ⟨_,Ordinal.toZFSet_mem_toZFSet_iff.mpr hq,_,Ordinal.toZFSet_mem_toZFSet_iff.mpr hr,rfl⟩,?_⟩
  rw [productValue_pair,Ordinal.rank_toZFSet,Ordinal.rank_toZFSet]

theorem productRelation_transitive (a b : Ordinal.{u}) :
    TransitiveOn (ZFSet.prod b.toZFSet a.toZFSet) (productRelation a.toZFSet b.toZFSet) := by
  intro x hx y hy z hz hxy hyz
  apply (productValue_relation a b x hx z hz).mpr
  exact ((ZFSet.isOrdinal_toZFSet (a*b)).mem (productValue_mem a b z hz)).subset_of_mem
    ((productValue_relation a b y hy z hz).mp hyz) ((productValue_relation a b x hx y hy).mp hxy)

theorem product_orderType (a b : Ordinal.{u}) :
    orderType (ZFSet.prod b.toZFSet a.toZFSet) (productRelation a.toZFSet b.toZFSet)
      (productRelation_wellFounded a b) = a*b :=
  orderType_of_ordinal_presentation _ _ _ _ (productValue a)
    (productValue_mem a b) (productValue_surjective a b) (productValue_relation a b)

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalProductSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel
universe u

theorem productDomainMatrix_eval (d a b : ℕ) (e : ℕ → ZFSet.{u}) :
    (productDomainMatrix d a b).Eval e ↔ e d = ZFSet.prod (e b) (e a) := by
  simp only [productDomainMatrix,Formula.Eval,Formula.eval_allMem,
    Formula.eval_orderedPair,Formula.eval_pairMem,cons_zero,cons_succ]
  constructor
  · rintro ⟨hsub,hsup⟩
    apply ZFSet.ext; intro x
    constructor
    · intro hx; exact ZFSet.mem_prod.mpr (hsub x hx)
    · intro hx
      obtain ⟨s,hs,t,ht,rfl⟩ := ZFSet.mem_prod.mp hx
      exact hsup s hs t ht
  · intro heq
    rw [heq]
    exact ⟨fun x hx => ZFSet.mem_prod.mp hx,
      fun s hs t ht => ZFSet.mem_prod.mpr ⟨s,hs,t,ht,rfl⟩⟩

theorem productRelationMatrix_eval (r d a b : ℕ) (e : ℕ → ZFSet.{u})
    (hd : e d = ZFSet.prod (e b) (e a)) :
    (productRelationMatrix r d a b).Eval e ↔ e r = productRelation (e a) (e b) := by
  simp only [productRelationMatrix,Formula.Eval,Formula.eval_allMem,Formula.eval_orderedPair,
    Formula.eval_imp,Formula.eval_pairMem,cons_zero,cons_succ]
  have h3 (x y p : ZFSet.{u}) := productLessFormula_eval (a+3) (b+3) 1 0
    (cons y (cons x (cons p e)))
  have h2 (x y : ZFSet.{u}) := productLessFormula_eval (a+2) (b+2) 1 0
    (cons y (cons x e))
  simp only [h3,h2,cons_zero,cons_succ,hd]
  constructor
  · rintro ⟨hr,hall⟩
    apply ZFSet.ext; intro p
    constructor
    · intro hp
      obtain ⟨x,hx,y,hy,rfl,hxy⟩ := hr p hp
      exact (pair_mem_productRelation _ _ _ _).mpr ⟨hx,hy,hxy⟩
    · intro hp
      obtain ⟨_,x,hx,y,hy,rfl,hxy⟩ := ZFSet.mem_sep.mp hp
      exact hall x hx y hy hxy
  · intro heq
    rw [heq]
    exact ⟨fun p hp => (ZFSet.mem_sep.mp hp).2,
      fun x hx y hy hxy => (pair_mem_productRelation _ _ _ _).mpr ⟨hx,hy,hxy⟩⟩

theorem productMatrix_eval (c a b d r f : ℕ) (e : ℕ → ZFSet.{u}) :
    (productMatrix c a b d r f).Eval e ↔
      e d = ZFSet.prod (e b) (e a) ∧ e r = productRelation (e a) (e b) ∧
      OrderTypeCertificate (e d) (e r) (e c) (e f) := by
  simp only [productMatrix,Formula.Eval,productDomainMatrix_eval]
  apply and_congr_right; intro hd
  rw [productRelationMatrix_eval r d a b e hd,orderTypeMatrix_eval]

theorem productSentence_semantics (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) :
    productSentence.Sat (A : Set ZFSet) e ↔
      ∃ d ∈ A, ∃ r ∈ A, ∃ f ∈ A,
        d = ZFSet.prod (e 2) (e 1) ∧ r = productRelation (e 1) (e 2) ∧
          OrderTypeCertificate d r (e 0) f := by
  change (∃ d ∈ A, ∃ r ∈ A, ∃ f ∈ A,
    (fromBounded _).Sat _ (cons f (cons r (cons d e)))) ↔ _
  apply exists_congr; intro d
  apply and_congr_right; intro hd
  apply exists_congr; intro r
  apply and_congr_right; intro hr
  apply exists_congr; intro f
  apply and_congr_right; intro hf
  rw [bounded_sat,Formula.absolute _ A hA _ (by
    intro i; rcases i with _|_|_|i <;> simp [cons,he,hd,hr,hf]),productMatrix_eval]
  rfl

theorem productSentence_sound (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) (a b : Ordinal.{u})
    (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet) :
    productSentence.Sat (A : Set ZFSet) e → e 0 = (a*b).toZFSet := by
  intro h
  obtain ⟨d,_,r,_,f,_,hd,hr,hc⟩ := (productSentence_semantics A hA e he).mp h
  rw [ha,hb] at hd hr
  rw [hd,hr] at hc
  exact (hc.exact (productRelation_wellFounded a b) (productRelation_transitive a b)).trans
    (congrArg Ordinal.toZFSet (product_orderType a b))

theorem productSentence_spec_of_certificate (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) (a b : Ordinal.{u})
    (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet)
    (hd : ZFSet.prod b.toZFSet a.toZFSet ∈ A)
    (hr : productRelation a.toZFSet b.toZFSet ∈ A)
    (hf : ∃ f ∈ A, OrderTypeCertificate (ZFSet.prod b.toZFSet a.toZFSet)
      (productRelation a.toZFSet b.toZFSet) (a*b).toZFSet f) :
    productSentence.Sat (A : Set ZFSet) e ↔ e 0 = (a*b).toZFSet := by
  refine ⟨productSentence_sound A hA e he a b ha hb,?_⟩
  intro hc
  obtain ⟨f,hf,hcert⟩ := hf
  apply (productSentence_semantics A hA e he).mpr
  exact ⟨_,hd,_,hr,f,hf,by rw [ha,hb],by rw [ha,hb],hc ▸ hcert⟩

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalProductClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel
universe u

theorem toZFSet_nat (n : ℕ) : (n : Ordinal.{u}).toZFSet = natSet n := by
  induction n with
  | zero => simp [natSet]
  | succ n ih => rw [Nat.cast_add_one,Ordinal.toZFSet_add_one,ih]; rfl

theorem toZFSet_omega : Ordinal.omega0.toZFSet = ZFSet.omega.{u} := by
  apply ZFSet.ext; intro x
  rw [Ordinal.mem_toZFSet_iff,mem_omega]
  constructor
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨n,rfl⟩ := Ordinal.lt_omega0.mp ha
    exact ⟨n,toZFSet_nat n⟩
  · rintro ⟨n,rfl⟩
    exact ⟨n,Ordinal.natCast_lt_omega0 n,toZFSet_nat n⟩

theorem ordinal_mul_internal_schemas (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (a b : Ordinal.{u}) (ha : a.toZFSet ∈ M) (hb : b.toZFSet ∈ M) :
    (a*b).toZFSet ∈ M ∧ ∃ f ∈ M,
      OrderTypeCertificate (ZFSet.prod b.toZFSet a.toZFSet)
        (productRelation a.toZFSet b.toZFSet) (a*b).toZFSet f := by
  obtain ⟨hc,f,hf,hg,ho⟩ := orderType_internal M _ _ hM hP hU hPow hS hR
    (product_mem M hM hP hU hPow hS hb ha)
    (productRelation_mem M _ _ hM hP hU hPow hS ha hb)
    (productRelation_wellFounded a b) (productRelation_transitive a b)
  rw [product_orderType] at hc hg ho
  exact ⟨hc,f,hf,ZFSet.isOrdinal_toZFSet _,hg,ho⟩

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalProductReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel
universe u

theorem productSigma_sentence : fromSigma productSigma = productSentence := rfl

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OmegaPowerStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions
universe u

theorem omegaPower_members (a : Ordinal.{u}) (z : ZFSet.{u}) :
    z ∈ (Ordinal.omega0 ^ a).toZFSet ↔ z ∈ (1 : Ordinal.{u}).toZFSet ∨
      ∃ x ∈ a.toZFSet, z ∈ omegaNext x := by
  constructor
  · intro hz
    by_cases ha : a = 0
    · left; simpa [ha] using hz
    · obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
      obtain ⟨b,hb,n,hn⟩ := (Ordinal.lt_omega0_opow ha).mp hc
      refine Or.inr ⟨b.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hb,?_⟩
      rw [omegaNext,Ordinal.rank_toZFSet,Ordinal.toZFSet_mem_toZFSet_iff]
      exact hn.trans (Ordinal.opow_mul_lt_opow (Ordinal.natCast_lt_omega0 n) (lt_add_one b))
  · rintro (hz|⟨x,hx,hz⟩)
    · exact Ordinal.toZFSet_monotone (Order.one_le_iff_ne_zero.mpr (Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero)) hz
    · obtain ⟨b,hb,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
      change z ∈ (Ordinal.omega0 ^ (b.toZFSet.rank+1)).toZFSet at hz
      rw [Ordinal.rank_toZFSet] at hz
      exact Ordinal.toZFSet_monotone
        (Ordinal.opow_le_opow_right Ordinal.omega0_pos (Order.succ_le_of_lt hb)) hz

theorem OmegaGraph.correct {M d r f : ZFSet.{u}} (h : OmegaGraph M d r f)
    (x : ZFSet.{u}) (hx : x ∈ d) (v : ZFSet.{u}) (hv : v ∈ r)
    (hfv : ZFSet.pair x v ∈ f) : v = omegaNext x := by
  induction x using ZFSet.inductionOn generalizing v with
  | h x ih =>
    obtain ⟨A,_,hs,_,rfl⟩ := h.2.2 x hx v hv hfv
    have hxo := h.1.mem hx
    have he : A = (Ordinal.omega0 ^ x.rank).toZFSet := by
      apply ZFSet.ext; intro z
      rw [omegaPower_members,hxo.toZFSet_rank_eq]
      constructor
      · intro hz
        rcases hs.2.1 z hz with hz|⟨y,hy,w,hw,hfw,hz⟩
        · exact Or.inl hz
        · exact Or.inr ⟨y,hy,(ih y hy (h.1.subset_of_mem hx hy) w hw hfw) ▸ hz⟩
      · rintro (hz|⟨y,hy,hz⟩)
        · exact hs.1 hz
        · obtain ⟨w,hw,hfw,_⟩ := h.2.1.2 y (h.1.subset_of_mem hx hy)
          rw [← ih y hy (h.1.subset_of_mem hx hy) w hw hfw] at hz
          exact hs.2.2 y hy w hw hfw hz
    rw [he,Ordinal.rank_toZFSet,omegaNext,Ordinal.opow_add_one]

theorem OmegaGraph.mem_iff {M d r f : ZFSet.{u}} (h : OmegaGraph M d r f) (z : ZFSet.{u}) :
    z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (omegaNext x) := by
  constructor
  · intro hz
    obtain ⟨x,hx,v,hv,rfl⟩ := h.2.1.1 z hz
    exact ⟨x,hx,by rw [h.correct x hx v hv hz]⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨v,hv,hfv,_⟩ := h.2.1.2 x hx
    rw [← h.correct x hx v hv hfv]
    exact hfv

theorem OmegaGraph.unique {M N d r t f g : ZFSet.{u}}
    (hf : OmegaGraph M d r f) (hg : OmegaGraph N d t g) : f = g := by
  apply ZFSet.ext; intro z
  exact (hf.mem_iff z).trans (hg.mem_iff z).symm

theorem omegaStageImage (d f x : ZFSet.{u}) (hd : d.IsOrdinal) (hx : x ∈ d)
    (hf : ∀ z, z ∈ f ↔ ∃ y ∈ d, z = ZFSet.pair y (omegaNext y)) :
    stageImage (1 : Ordinal.{u}).toZFSet x f = (Ordinal.omega0 ^ x.rank).toZFSet := by
  apply ZFSet.ext; intro z
  rw [mem_stageImage,omegaPower_members,(hd.mem hx).toZFSet_rank_eq]
  apply or_congr_right
  constructor
  · rintro ⟨y,hy,w,hfw,hz⟩
    obtain ⟨v,_,hp⟩ := (hf _).mp hfw
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
    exact ⟨y,hy,hz⟩
  · rintro ⟨y,hy,hz⟩
    exact ⟨y,hy,_,(hf _).mpr ⟨y,hd.subset_of_mem hx hy,rfl⟩,hz⟩

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OmegaPowerGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions SentenceCoding
universe u

theorem insert_self_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (hU : BoundedSetTheory.Union M) {x : ZFSet.{u}} (hx : x ∈ M) : insert x x ∈ M := by
  have he : insert x x = ({x} : ZFSet.{u}) ∪ x := by
    apply ZFSet.ext; intro z
    simp only [ZFSet.mem_insert_iff,ZFSet.mem_union,ZFSet.mem_singleton]
  rw [he]
  exact binary_union_mem M hM hP hU (singleton_mem M hM hP hx) hx

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OmegaPowerDefinability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions SentenceCoding
universe u

theorem omegaStageStep_exact {M d r f x A : ZFSet.{u}} (hg : OmegaGraph M d r f)
    (hx : x ∈ d) (hs : StageStep (1 : Ordinal.{u}).toZFSet f r x A) :
    A = (Ordinal.omega0 ^ x.rank).toZFSet := by
  apply ZFSet.ext; intro z
  rw [omegaPower_members,(hg.1.mem hx).toZFSet_rank_eq]
  constructor
  · intro hz
    rcases hs.2.1 z hz with hz|⟨y,hy,w,hw,hfw,hz⟩
    · exact Or.inl hz
    · exact Or.inr ⟨y,hy,(hg.correct y (hg.1.subset_of_mem hx hy) w hw hfw) ▸ hz⟩
  · rintro (hz|⟨y,hy,hz⟩)
    · exact hs.1 hz
    · obtain ⟨w,hw,hfw,_⟩ := hg.2.1.2 y (hg.1.subset_of_mem hx hy)
      rw [← hg.correct y (hg.1.subset_of_mem hx hy) w hw hfw] at hz
      exact hs.2.2 y hy w hw hfw hz

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OmegaGraphRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

theorem omegaStageStep_domain (M x r f : ZFSet.{u}) (hg : OmegaGraph M x r f) :
    StageStep (1 : Ordinal.{u}).toZFSet f r x (Ordinal.omega0 ^ x.rank).toZFSet := by
  refine ⟨?_,?_,?_⟩
  · intro z hz; exact (omegaPower_members x.rank z).mpr (Or.inl hz)
  · intro z hz
    rcases (omegaPower_members x.rank z).mp hz with hz|⟨t,ht,hz⟩
    · exact Or.inl hz
    · rw [hg.1.toZFSet_rank_eq] at ht
      obtain ⟨v,hv,hfv,_⟩ := hg.2.1.2 t ht
      rw [← hg.correct t ht v hv hfv] at hz
      exact Or.inr ⟨t,ht,v,hv,hfv,hz⟩
  · intro t ht v hv hfv z hz
    rw [hg.correct t ht v hv hfv] at hz
    exact (omegaPower_members x.rank z).mpr
      (Or.inr ⟨t,hg.1.toZFSet_rank_eq.symm ▸ ht,hz⟩)

theorem omegaStageStep_domain_exact {M x r f A : ZFSet.{u}} (hg : OmegaGraph M x r f)
    (hs : StageStep (1 : Ordinal.{u}).toZFSet f r x A) :
    A = (Ordinal.omega0 ^ x.rank).toZFSet := by
  have ht := omegaStageStep_domain M x r f hg
  apply ZFSet.ext; intro z
  constructor
  · intro hz
    rcases hs.2.1 z hz with hz|⟨t,ht',v,hv,hfv,hz⟩
    · exact ht.1 hz
    · exact ht.2.2 t ht' v hv hfv hz
  · intro hz
    rcases ht.2.1 z hz with hz|⟨t,ht',v,hv,hfv,hz⟩
    · exact hs.1 hz
    · exact hs.2.2 t ht' v hv hfv hz

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OmegaStageSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

theorem omegaStageMatrix_eval (s f r x A : ℕ) (e : ℕ → ZFSet.{u}) :
    (omegaStageMatrix s f r x A).Eval e ↔ StageStep (e s) (e f) (e r) (e x) (e A) := by
  simp only [omegaStageMatrix,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_disj,Formula.eval_pairMem,Formula.eval_imp,cons_zero,cons_succ,StageStep]

theorem ordinalAllMem_sat (M : ZFSet.{u}) (hM : Transitive M)
    (i : ℕ) (p : SentenceForm) (e : ℕ → ZFSet.{u}) (hi : e i ∈ M) :
    (ordinalAllMem i p).Sat (M : Set ZFSet) e ↔
      ∀ x ∈ e i, p.Sat (M : Set ZFSet) (cons x e) := by
  simp only [ordinalAllMem,SentenceForm.sat_all,SentenceForm.sat_imp,
    SentenceForm.Sat,cons_zero,cons_succ]
  exact ⟨fun h x hx => h x (hM _ hi x hx) hx,fun h x _ hx => h x hx⟩

theorem ordinalProductAt_sound (M : ZFSet.{u}) (hM : Transitive M)
    (v a b : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (ha : (e a).IsOrdinal) (hb : (e b).IsOrdinal) :
    (ordinalProductAt v a b).Sat (M : Set ZFSet) e →
      e v = ((e a).rank * (e b).rank).toZFSet := by
  rw [ordinalProductAt,SentenceForm.sat_rename]
  exact productSentence_sound M hM _ (fun i => he _) _ _
    ha.toZFSet_rank_eq.symm hb.toZFSet_rank_eq.symm

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OmegaGraphSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

theorem omegaGraphSentence_semantics (M : ZFSet.{u}) (hM : Transitive M)
    (s w d r f : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (omegaGraphSentence s w d r f).Sat (M : Set ZFSet) e ↔
      (e d).IsOrdinal ∧ FunctionGraph (e d) (e r) (e f) ∧
      ∀ x ∈ e d, ∀ v ∈ e r, ZFSet.pair x v ∈ e f →
        ∃ A ∈ M, StageStep (e s) (e f) (e r) x A ∧ A.IsOrdinal ∧
          (ordinalProductAt 1 0 (w+3)).Sat (M : Set ZFSet) (cons A (cons v (cons x e))) := by
  have hb (p : Formula) : (fromBounded p).Sat (M : Set ZFSet) e ↔ p.Eval e := by
    rw [bounded_sat,Formula.absolute _ M hM e he]
  change ((fromBounded _).Sat _ e ∧ (fromBounded _).Sat _ e ∧
    (ordinalAllMem d _).Sat _ e) ↔ _
  rw [hb,hb,eval_ordinalFormula,Formula.eval_functionGraph,
    ordinalAllMem_sat M hM d _ e (he d)]
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply forall_congr'; intro x
  apply forall_congr'; intro hx
  have hxM := hM _ (he d) x hx
  rw [ordinalAllMem_sat M hM (r+1) _ (cons x e) (he r)]
  apply forall_congr'; intro v
  apply forall_congr'; intro hv
  have hvM := hM _ (he r) v hv
  rw [SentenceForm.sat_imp,bounded_sat,Formula.absolute _ M hM _ (by
    intro i; rcases i with _|_|i; exact hvM; exact hxM; exact he i),Formula.eval_pairMem]
  apply forall_congr'; intro _
  change (∃ A ∈ M, (fromBounded _).Sat _ _ ∧ (fromBounded _).Sat _ _ ∧ _) ↔ _
  apply exists_congr; intro A
  apply and_congr_right; intro hA
  have heA : ∀ i, cons A (cons v (cons x e)) i ∈ M := by
    intro i; rcases i with _|_|_|i; exact hA; exact hvM; exact hxM; exact he i
  rw [bounded_sat,Formula.absolute _ M hM _ heA,omegaStageMatrix_eval,
    bounded_sat,Formula.absolute _ M hM _ heA,eval_ordinalFormula]
  rfl

theorem omegaGraphSentence_sound (M : ZFSet.{u}) (hM : Transitive M)
    (s w d r f : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (hs : e s = (1 : Ordinal.{u}).toZFSet) (hw : e w = ZFSet.omega) :
    (omegaGraphSentence s w d r f).Sat (M : Set ZFSet) e →
      OmegaGraph M (e d) (e r) (e f) := by
  rw [omegaGraphSentence_semantics M hM s w d r f e he]
  rintro ⟨hd,hf,hstep⟩
  refine ⟨hd,hf,?_⟩
  intro x hx v hv hfv
  obtain ⟨A,hA,hst,ho,hp⟩ := hstep x hx v hv hfv
  have hwOrd : ZFSet.omega.{u}.IsOrdinal := toZFSet_omega ▸ ZFSet.isOrdinal_toZFSet Ordinal.omega0
  have hm := ordinalProductAt_sound M hM 1 0 (w+3) _ (by
    intro i; rcases i with _|_|_|i; exact hA; exact hM _ (he r) v hv;
    exact hM _ (he d) x hx; exact he i) ho (by simpa [hw] using hwOrd) hp
  simp only [cons_zero,cons_succ,hw,← toZFSet_omega,Ordinal.rank_toZFSet] at hm
  exact ⟨A,hA,hs ▸ hst,ho,hm⟩

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OmegaPowerSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

theorem ordinalOneMatrix_eval (s : ℕ) (e : ℕ → ZFSet.{u}) :
    (ordinalOneMatrix s).Eval e ↔ e s = (1 : Ordinal.{u}).toZFSet := by
  have hone : (1 : Ordinal.{u}).toZFSet = ({∅} : ZFSet.{u}) := by
    rw [← Nat.cast_one,toZFSet_nat]; rfl
  rw [hone]
  simp only [ordinalOneMatrix,Formula.Eval,Formula.eval_allMem,Formula.eval_empty,cons_zero]
  constructor
  · rintro ⟨hall,x,hx,rfl⟩
    apply ZFSet.ext; intro z
    simp only [ZFSet.mem_singleton]
    exact ⟨hall z,fun h => h.symm ▸ hx⟩
  · intro he
    rw [he]
    exact ⟨fun z hz => ZFSet.mem_singleton.mp hz,∅,ZFSet.mem_singleton.mpr rfl,rfl⟩

theorem omegaPowerBody_semantics (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    omegaPowerBody.Sat (M : Set ZFSet) e ↔
      e 4 = ZFSet.omega ∧ e 3 = (1 : Ordinal.{u}).toZFSet ∧
      e 0 = e 6 ∧
      (omegaGraphSentence 3 4 0 1 2).Sat (M : Set ZFSet) e ∧
      StageStep (e 3) (e 2) (e 1) (e 6) (e 5) := by
  change ((canonicalOmega 4).Sat _ e ∧ (fromBounded _).Sat _ e ∧
    (omegaGraphSentence 3 4 0 1 2).Sat _ e ∧ (fromBounded _).Sat _ e) ↔ _
  rw [canonicalOmega_spec M hM hω 4 e he,bounded_sat,
    Formula.absolute _ M hM e he,Formula.Eval,ordinalOneMatrix_eval,
    Formula.Eval,bounded_sat,Formula.absolute _ M hM e he,omegaStageMatrix_eval]
  tauto

theorem omegaPowerSentence_semantics (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    omegaPowerSentence.Sat (M : Set ZFSet) e ↔
      ∃ w ∈ M, ∃ s ∈ M, ∃ f ∈ M, ∃ r ∈ M, ∃ d ∈ M,
        w = ZFSet.omega ∧ s = (1 : Ordinal.{u}).toZFSet ∧ d = e 1 ∧
        (omegaGraphSentence 3 4 0 1 2).Sat (M : Set ZFSet)
          (cons d (cons r (cons f (cons s (cons w e))))) ∧
        StageStep s f r (e 1) (e 0) := by
  change (∃ w ∈ M, ∃ s ∈ M, ∃ f ∈ M, ∃ r ∈ M, ∃ d ∈ M,
    omegaPowerBody.Sat _ _) ↔ _
  apply exists_congr; intro w
  apply and_congr_right; intro hw
  apply exists_congr; intro s
  apply and_congr_right; intro hs
  apply exists_congr; intro f
  apply and_congr_right; intro hf
  apply exists_congr; intro r
  apply and_congr_right; intro hr
  apply exists_congr; intro d
  apply and_congr_right; intro hd
  exact omegaPowerBody_semantics M hM hω _ (by
    intro i; rcases i with _|_|_|_|_|i
    exact hd; exact hr; exact hf; exact hs; exact hw; exact he i)

theorem omegaPowerSentence_sound (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    omegaPowerSentence.Sat (M : Set ZFSet) e →
      (e 1).IsOrdinal ∧ e 0 = (Ordinal.omega0 ^ (e 1).rank).toZFSet := by
  rw [omegaPowerSentence_semantics M hM hω e he]
  rintro ⟨w,hw,s,hs,f,hf,r,hr,d,hd,hew,hes,hed,hg,hst⟩
  have hgraph := omegaGraphSentence_sound M hM 3 4 0 1 2 _ (by
    intro i; rcases i with _|_|_|_|_|i
    exact hd; exact hr; exact hf; exact hs; exact hw; exact he i) hes hew hg
  change OmegaGraph M d r f at hgraph
  rw [hed] at hgraph
  exact ⟨hgraph.1,omegaStageStep_domain_exact hgraph (hes ▸ hst)⟩

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OmegaPowerCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

theorem ordinalProductAt_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (v a b : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (α β : Ordinal.{u}) (ha : e a = α.toZFSet) (hb : e b = β.toZFSet)
    (hc : ProductCertificates M α β) (hv : e v = (α*β).toZFSet) :
    (ordinalProductAt v a b).Sat (M : Set ZFSet) e := by
  rw [ordinalProductAt,SentenceForm.sat_rename]
  exact (productSentence_spec_of_certificate M hM
    (fun i => e (if i = 0 then v else if i = 1 then a else b)) (fun i => he _) α β ha hb
    hc.1 hc.2.1 hc.2.2).mpr hv

theorem omegaGraphSentence_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (hs : e 3 = (1 : Ordinal.{u}).toZFSet) (hw : e 4 = ZFSet.omega)
    (hg : OmegaGraph M (e 0) (e 1) (e 2))
    (hp : ∀ t ∈ e 0, ProductCertificates M (Ordinal.omega0 ^ t.rank) Ordinal.omega0) :
    (omegaGraphSentence 3 4 0 1 2).Sat (M : Set ZFSet) e := by
  apply (omegaGraphSentence_semantics M hM 3 4 0 1 2 e he).mpr
  refine ⟨hg.1,hg.2.1,?_⟩
  intro t ht v hv hfv
  obtain ⟨A,hA,hst,ho,hval⟩ := hg.2.2 t ht v hv hfv
  have hAe := omegaStageStep_exact hg ht hst
  refine ⟨A,hA,hs.symm ▸ hst,ho,?_⟩
  apply ordinalProductAt_of_certificates M hM 1 0 7 (cons A (cons v (cons t e)))
    (fun i => by
      rcases i with _|_|_|i
      exact hA; exact hM _ (he 1) v hv; exact hM _ (he 0) t ht; exact he i)
    (Ordinal.omega0 ^ t.rank) Ordinal.omega0 hAe (by simpa using hw.trans toZFSet_omega.symm) (hp t ht)
  simpa only [cons_zero,cons_succ,hAe,Ordinal.rank_toZFSet] using hval

theorem omegaPowerSentence_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (hc : OmegaPowerCertificates M (e 1))
    (hy : e 0 = (Ordinal.omega0 ^ (e 1).rank).toZFSet) :
    omegaPowerSentence.Sat (M : Set ZFSet) e := by
  obtain ⟨hd,f,hf,r,hr,hg,hp⟩ := hc
  have hs : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact hM _ hω _ ((mem_omega _).mpr ⟨1,rfl⟩)
  have hst := omegaStageStep_domain M (e 1) r f hg
  apply (omegaPowerSentence_semantics M hM hω e he).mpr
  refine ⟨_,hω,_,hs,f,hf,r,hr,_,hd,rfl,rfl,rfl,?_,hy.symm ▸ hst⟩
  exact omegaGraphSentence_of_certificates M hM _ (by
    intro i; rcases i with _|_|_|_|_|i
    exact hd; exact hr; exact hf; exact hs; exact hω; exact he i) rfl rfl hg hp

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SigmaCollectionClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedDefinability
open BoundedSetTheory TransitiveNameModel
open BoundedDefinability SetModelFunctions
universe u
theorem SigmaDefinable.allMem_collection {M : ZFSet.{u}} {P : (ℕ → ZFSet.{u}) → Prop}
    (C : Context M) (hRep : SigmaReplacement M) (hC : SigmaCollection M)
    (h : SigmaDefinable M P) (a : ℕ) :
    SigmaDefinable M (fun e => ∀ x ∈ e a, P (cons x e)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  refine ⟨.allMem (2*a) (p.rename bindSlots),d,hd,?_⟩
  intro e he
  rw [SigmaFormula.realize_allMem M C.transitive C.pairing C.union C.separation
    hRep C.infinity hC _ _ _ (by
      intro i; unfold mix; split <;> first | exact he _ | exact hd _),mix_even]
  apply forall_congr'; intro x
  apply forall_congr'; intro hx
  rw [SigmaFormula.realize_rename]
  change p.Realize M (cons x (mix e d) ∘ bindSlots) ↔ _
  rw [bind_mix]
  exact hp (cons x e) (by intro i; cases i; exact C.transitive _ (he a) x hx; exact he _)

end TuringRigidity.BoundedDefinability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OmegaRecursionSchemas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions SentenceCoding
universe u

theorem productSigma_context (M : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (a b : Ordinal.{u})
    (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet) :
    productSigma.Realize M e ↔ e 0 = (a*b).toZFSet := by
  rw [← sigma_sat,productSigma_sentence]
  have haM : a.toZFSet ∈ M := ha ▸ he 1
  have hbM : b.toZFSet ∈ M := hb ▸ he 2
  obtain ⟨_,f,hf,hc⟩ := ordinal_mul_internal_schemas M C.transitive C.pairing C.union
    C.power C.separation hRep a b haM hbM
  exact productSentence_spec_of_certificate M C.transitive e he a b ha hb
    (product_mem M C.transitive C.pairing C.union C.power C.separation hbM haM)
    (productRelation_mem M _ _ C.transitive C.pairing C.union C.power C.separation haM hbM)
    ⟨f,hf,hc⟩

theorem omegaGraph_of_mem_iff_context (M d f : ZFSet.{u}) (C : Context M)
    (hdM : d ∈ M) (hfM : f ∈ M) (hd : d.IsOrdinal)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (omegaNext x)) :
    OmegaGraph M d (iterUnion 2 f) f := by
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact C.transitive _ (omega_mem M C.transitive C.separation C.infinity) _ ((mem_omega _).mpr ⟨1,rfl⟩)
  have hpair (x v : ZFSet.{u}) : ZFSet.pair x v ∈ f ↔ x ∈ d ∧ v = omegaNext x := by
    rw [hf]
    constructor
    · rintro ⟨y,hy,he⟩
      obtain ⟨rfl,hv⟩ := ZFSet.pair_inj.mp he
      exact ⟨hy,hv⟩
    · rintro ⟨hx,rfl⟩; exact ⟨x,hx,rfl⟩
  refine ⟨hd,⟨?_,?_⟩,?_⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := (hf z).mp hz
    exact ⟨x,hx,_,second_mem_doubleUnion hz,rfl⟩
  · intro x hx
    have hp := (hpair x _).mpr ⟨hx,rfl⟩
    exact ⟨_,second_mem_doubleUnion hp,hp,fun v _ hv => (hpair x v).mp hv |>.2⟩
  · intro x hx v _ hv
    have he := (hpair x v).mp hv |>.2
    subst v
    have hA := omegaStageImage d f x hd hx hf
    refine ⟨(Ordinal.omega0 ^ x.rank).toZFSet,
      hA ▸ stageImage_mem_context M C h1 (C.transitive d hdM x hx) hfM,?_,ZFSet.isOrdinal_toZFSet _,?_⟩
    · refine ⟨?_,?_,?_⟩
      · intro z hz; exact (omegaPower_members x.rank z).mpr (Or.inl hz)
      · intro z hz
        rcases (omegaPower_members x.rank z).mp hz with hz|⟨y,hy,hz⟩
        · exact Or.inl hz
        · rw [(hd.mem hx).toZFSet_rank_eq] at hy
          have hp := (hpair y _).mpr ⟨hd.subset_of_mem hx hy,rfl⟩
          exact Or.inr ⟨y,hy,_,second_mem_doubleUnion hp,hp,hz⟩
      · intro y hy w _ hw z hz
        rw [(hpair y w).mp hw |>.2] at hz
        exact (omegaPower_members x.rank z).mpr
          (Or.inr ⟨y,(hd.mem hx).toZFSet_rank_eq.symm ▸ hy,hz⟩)
    · rw [omegaNext,Ordinal.opow_add_one,Ordinal.rank_toZFSet]

theorem mulOmega_sigmaDefinable_schemas (M : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement M) :
    SigmaDefinable M (fun e => (e 1).IsOrdinal ∧ e 0 = ((e 1).rank*Ordinal.omega0).toZFSet) := by
  have ho := omega_mem M C.transitive C.separation C.infinity
  let p := SigmaFormula.conj (.bounded (ordinalFormula 2))
    (productSigma.rename (fun i => if i = 0 then 0 else if i = 1 then 2 else 1))
  refine ⟨p,fun _ => ZFSet.omega,fun _ => ho,?_⟩
  intro e he
  rw [SigmaFormula.realize_conj]
  have hoSem : (SigmaFormula.bounded (ordinalFormula 2)).Realize M
      (mix e (fun _ => ZFSet.omega)) ↔ (e 1).IsOrdinal := by
    rw [SigmaFormula.Realize,Formula.absolute _ M C.transitive _ (by
      intro i; unfold mix; split; exact he _; exact ho),eval_ordinalFormula]
    rfl
  rw [hoSem]
  apply and_congr_right; intro heo
  rw [SigmaFormula.realize_rename]
  exact productSigma_context M C hRep _ (by
    intro i; change mix e (fun _ => ZFSet.omega)
      (if i = 0 then 0 else if i = 1 then 2 else 1) ∈ M
    split; exact he 0
    split; exact he 1
    exact ho) (e 1).rank Ordinal.omega0 heo.toZFSet_rank_eq.symm toZFSet_omega.symm

theorem omegaGraph_sigmaDefinable_schemas (M : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement M) (hColl : SigmaCollection M)
    (d r f : ℕ) : SigmaDefinable M (fun e => OmegaGraph M (e d) (e r) (e f)) := by
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact C.nat_mem 1
  have hs : SigmaDefinable M (fun e =>
      StageStep (1 : Ordinal.{u}).toZFSet (e (f+3)) (e (r+3)) (e 2) (e 0)) := by
    have hb := (stageStep_definable C 0 (f+4) (r+4) 3 1).toSigma C.transitive
    have hc := ((equal_param h1 0).toSigma C.transitive).and hb
    exact hc.existsSet.congr (fun e _ => by simp [h1])
  have hv : SigmaDefinable M (fun e => (e 0).IsOrdinal ∧
      e 1 = ((e 0).rank*Ordinal.omega0).toZFSet) :=
    (mulOmega_sigmaDefinable_schemas M C hRep).subst (fun i => if i = 0 then 1 else 0)
  have hi := SigmaDefinable.impBounded C (defPairMem C 1 0 (f+2)) (hs.and hv).existsSet
  exact ((ordinal_definable C d).toSigma C.transitive).and
    (((functionGraph_definable C d r f).toSigma C.transitive).and
      ((hi.allMem_collection C hRep hColl (r+1)).allMem_collection C hRep hColl d))

theorem uniform_omega_certificate_schemas (M : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement M) (hColl : SigmaCollection M) :
    ∃ p : SigmaFormula, ∃ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ M) ∧
      ∀ x ∈ M, ∀ f ∈ M, p.Realize M (cons f (cons x e)) ↔
        ∃ r ∈ M, OmegaGraph M (insert x x) r f := by
  have hd : Definable M (fun e => e 0 = insert (e 3) (e 3)) := by
    refine ⟨.successor 0 6,fun _ => ZFSet.omega,fun _ => C.omega_mem,?_⟩
    intro e; simp [Formula.eval_successor,mix]
  have hg := (hd.toSigma C.transitive).and (omegaGraph_sigmaDefinable_schemas M C hRep hColl 0 1 2)
  obtain ⟨p,e,he,hp⟩ := sigma_binary_relation (fun x f => ∃ r ∈ M,
    ∃ d ∈ M, d = insert x x ∧ OmegaGraph M d r f) hg.existsSet.existsSet
  refine ⟨p,e,he,?_⟩
  intro x hx f hf
  rw [hp x hx f hf]
  constructor
  · rintro ⟨r,hr,d,_,rfl,h⟩; exact ⟨r,hr,h⟩
  · rintro ⟨r,hr,h⟩
    exact ⟨r,hr,insert x x,insert_self_mem M C.transitive C.pairing C.union hx,rfl,h⟩

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RestrictedOmegaRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions SentenceCoding
universe u

theorem internal_omegaGraph_schemas (M : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement M) (hColl : SigmaCollection M)
    (x : ZFSet.{u}) (hxM : x ∈ M) (hxo : x.IsOrdinal) :
    ∃ f ∈ M, OmegaGraph M (insert x x) (iterUnion 2 f) f := by
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact C.transitive _ (omega_mem M C.transitive C.separation C.infinity) _ ((mem_omega _).mpr ⟨1,rfl⟩)
  obtain ⟨p,e,he,hp⟩ := uniform_omega_certificate_schemas M C hRep hColl
  induction x using ZFSet.inductionOn with
  | h x ih =>
    have cert (y f : ZFSet.{u}) (hy : y ∈ x) (hf : f ∈ M) := hp y (C.transitive x hxM y hy) f hf
    obtain ⟨b,hb,hbdef⟩ := hRep p e he x hxM (by
      intro y hy
      obtain ⟨f,hf,hfg⟩ := ih y hy (C.transitive x hxM y hy) (hxo.mem hy)
      refine ⟨f,hf,(cert y f hy hf).mpr
        ⟨_,iterUnion_mem M C.transitive C.union hf 2,hfg⟩,?_⟩
      intro g hg hcg
      obtain ⟨r,_,hgg⟩ := (cert y g hy hg).mp hcg
      exact hgg.unique hfg)
    have hbg (f : ZFSet.{u}) : f ∈ b ↔
        ∃ y ∈ x, ∃ r ∈ M, OmegaGraph M (insert y y) r f := by
      constructor
      · intro hf
        have hfM := C.transitive b hb f hf
        obtain ⟨y,hy,hc⟩ := (hbdef f hfM).mp hf
        exact ⟨y,hy,(cert y f hy hfM).mp hc⟩
      · rintro ⟨y,hy,r,hr,hg⟩
        obtain ⟨f',hf',hg'⟩ := ih y hy (C.transitive x hxM y hy) (hxo.mem hy)
        have heq := hg.unique hg'
        have hfM : f ∈ M := heq ▸ hf'
        exact (hbdef f hfM).mpr ⟨y,hy,(cert y f hy hfM).mpr ⟨r,hr,hg⟩⟩
    let g := ZFSet.sUnion b
    have hgM : g ∈ M := union_mem M C.transitive C.union hb
    have hg (z : ZFSet.{u}) : z ∈ g ↔ ∃ y ∈ x, z = ZFSet.pair y (omegaNext y) := by
      constructor
      · intro hz
        obtain ⟨f,hf,hzf⟩ := ZFSet.mem_sUnion.mp hz
        obtain ⟨y,hy,r,_,hfg⟩ := (hbg f).mp hf
        obtain ⟨w,hw,hz⟩ := (hfg.mem_iff z).mp hzf
        rcases ZFSet.mem_insert_iff.mp hw with rfl|hw
        · exact ⟨w,hy,hz⟩
        · exact ⟨w,hxo.subset_of_mem hy hw,hz⟩
      · rintro ⟨y,hy,hz⟩
        obtain ⟨f,hf,hfg⟩ := ih y hy (C.transitive x hxM y hy) (hxo.mem hy)
        exact ZFSet.mem_sUnion.mpr ⟨f,(hbg f).mpr
          ⟨y,hy,_,iterUnion_mem M C.transitive C.union hf 2,hfg⟩,
          (hfg.mem_iff z).mpr ⟨y,ZFSet.mem_insert_iff.mpr (Or.inl rfl),hz⟩⟩
    have hvalue : stageImage (1 : Ordinal.{u}).toZFSet x g =
        (Ordinal.omega0 ^ x.rank).toZFSet := by
      apply ZFSet.ext; intro z
      rw [mem_stageImage,omegaPower_members,hxo.toZFSet_rank_eq]
      apply or_congr_right
      constructor
      · rintro ⟨y,hy,w,hfw,hz⟩
        obtain ⟨v,_,hp⟩ := (hg _).mp hfw
        obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
        exact ⟨y,hy,hz⟩
      · rintro ⟨y,hy,hz⟩
        exact ⟨y,hy,_,(hg _).mpr ⟨y,hy,rfl⟩,hz⟩
    have hpow : (Ordinal.omega0 ^ x.rank).toZFSet ∈ M :=
      hvalue ▸ stageImage_mem_context M C h1 hxM hgM
    have hvM : omegaNext x ∈ M := by
      rw [omegaNext,Ordinal.opow_add_one]
      exact (ordinal_mul_internal_schemas M C.transitive C.pairing C.union C.power C.separation hRep _ Ordinal.omega0 hpow (toZFSet_omega.symm ▸ C.omega_mem)).1
    let f := g ∪ ({ZFSet.pair x (omegaNext x)} : ZFSet.{u})
    have hfM : f ∈ M := binary_union_mem M C.transitive C.pairing C.union hgM
      (singleton_mem M C.transitive C.pairing (orderedPair_mem M C.transitive C.pairing hxM hvM))
    have hsucc : (insert x x).IsOrdinal := by
      rw [← hxo.toZFSet_rank_eq,← Ordinal.toZFSet_add_one]
      exact ZFSet.isOrdinal_toZFSet _
    refine ⟨f,hfM,omegaGraph_of_mem_iff_context M _ f C
      (insert_self_mem M C.transitive C.pairing C.union hxM) hfM hsucc ?_⟩
    intro z
    change z ∈ g ∪ ({ZFSet.pair x (omegaNext x)} : ZFSet.{u}) ↔ _
    rw [ZFSet.mem_union,ZFSet.mem_singleton,hg]
    constructor
    · rintro (⟨y,hy,hz⟩|hz)
      · exact ⟨y,ZFSet.mem_insert_of_mem _ hy,hz⟩
      · exact ⟨x,ZFSet.mem_insert_iff.mpr (Or.inl rfl),hz⟩
    · rintro ⟨y,hy,hz⟩
      rcases ZFSet.mem_insert_iff.mp hy with rfl|hy
      · exact Or.inr hz
      · exact Or.inl ⟨y,hy,hz⟩

theorem ordinal_omega_opow_schemas (M : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement M) (hColl : SigmaCollection M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) : (Ordinal.omega0 ^ a).toZFSet ∈ M := by
  obtain ⟨f,hf,hg⟩ := internal_omegaGraph_schemas M C hRep hColl a.toZFSet ha (ZFSet.isOrdinal_toZFSet a)
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact C.transitive _ (omega_mem M C.transitive C.separation C.infinity) _ ((mem_omega _).mpr ⟨1,rfl⟩)
  have hv := omegaStageImage _ f a.toZFSet hg.1 (ZFSet.mem_insert_iff.mpr (Or.inl rfl)) hg.mem_iff
  rw [Ordinal.rank_toZFSet] at hv
  exact hv ▸ stageImage_mem_context M C h1 ha hf

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeOmegaCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions SentenceCoding
universe u

theorem internal_omegaGraph_below_schemas (M : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement M) (hColl : SigmaCollection M)
    (x : ZFSet.{u}) (hx : x ∈ M) (ho : x.IsOrdinal) :
    ∃ f ∈ M, OmegaGraph M x (iterUnion 2 f) f := by
  obtain ⟨f,hf,hg⟩ := internal_omegaGraph_schemas M C hRep hColl x hx ho
  let p : Formula := .existsMem 1 (.existsMem 3 (.orderedPair 2 1 0))
  let e : ℕ → ZFSet.{u} := cons x (fun _ => iterUnion 2 f)
  let g := ZFSet.sep (fun z => p.Eval (cons z e)) f
  have hgM : g ∈ M := sep_mem M C.transitive C.separation p e
    (by intro i; cases i; exact hx; exact iterUnion_mem M C.transitive C.union hf 2) hf
  have hm (z : ZFSet.{u}) : z ∈ g ↔ ∃ t ∈ x, z = ZFSet.pair t (omegaNext t) := by
    change z ∈ ZFSet.sep _ f ↔ _
    simp only [ZFSet.mem_sep,p,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ]
    change (z ∈ f ∧ ∃ t ∈ x, ∃ v ∈ iterUnion 2 f, z = ZFSet.pair t v) ↔ _
    constructor
    · rintro ⟨hz,t,ht,v,hv,rfl⟩
      exact ⟨t,ht,by rw [hg.correct t (ZFSet.mem_insert_of_mem x ht) v hv hz]⟩
    · rintro ⟨t,ht,rfl⟩
      have hp := (hg.mem_iff _).mpr ⟨t,ZFSet.mem_insert_of_mem x ht,rfl⟩
      exact ⟨hp,t,ht,_,second_mem_doubleUnion hp,rfl⟩
  exact ⟨g,hgM,omegaGraph_of_mem_iff_context M x g C hx hgM ho hm⟩

theorem ProductCertificates.context (M : ZFSet.{u}) (C : Context M)
    (hRep : SigmaReplacement M) (a b : Ordinal.{u})
    (ha : a.toZFSet ∈ M) (hb : b.toZFSet ∈ M) : ProductCertificates M a b := by
  obtain ⟨_,f,hf,hc⟩ := ordinal_mul_internal_schemas M C.transitive C.pairing C.union
    C.power C.separation hRep a b ha hb
  exact ⟨product_mem M C.transitive C.pairing C.union C.power C.separation hb ha,
    productRelation_mem M _ _ C.transitive C.pairing C.union C.power C.separation ha hb,
    f,hf,hc⟩

theorem OmegaPowerCertificates.schemas (M : ZFSet.{u}) (C : Context M)
    (hRep : SigmaReplacement M) (hColl : SigmaCollection M)
    (x : ZFSet.{u}) (hx : x ∈ M) (ho : x.IsOrdinal) : OmegaPowerCertificates M x := by
  obtain ⟨f,hf,hg⟩ := internal_omegaGraph_below_schemas M C hRep hColl x hx ho
  refine ⟨hx,f,hf,_,iterUnion_mem M C.transitive C.union hf 2,hg,?_⟩
  intro t ht
  have htM := C.transitive _ hx t ht
  exact ProductCertificates.context M C hRep _ _
    (ordinal_omega_opow_schemas M C hRep hColl t.rank
      ((hg.1.mem ht).toZFSet_rank_eq.symm ▸ htM)) (toZFSet_omega.symm ▸ C.omega_mem)

theorem relative_omega_power_certificates (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) :
    OmegaPowerCertificates (relativeModel M (groundReals M)) a.toZFSet :=
  OmegaPowerCertificates.schemas _ (ground_relative_context M hM hT)
    (relativeModel_sigma_replacement M _ hM hT (groundReals_mem M hM hT))
    (relativeModel_sigma_collection M _ hM hT (groundReals_mem M hM hT))
    a.toZFSet ((ground_relativeModel_ordinal_iff M hM hT a).mpr ha) (ZFSet.isOrdinal_toZFSet a)

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GroundSeedOrdinalHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem omega_mem_groundReals (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ZFSet.omega ∈ groundReals M :=
  (mem_groundReals M _).mpr ⟨sourceT_omega_mem M hM hT,fun _ h => h⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalDecoderDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

theorem ground_level_omega_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (δ : Ordinal.{u}) : ZFSet.omega ∈ level (groundReals M) δ :=
  seed_subset_stage _ _ (parameter_subset_seed _ (omega_mem_groundReals M hM hT))

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_ProductCertificateCollection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions SentenceCoding
universe u

theorem productBundleSigma_spec (M : ZFSet.{u}) (hM : Transitive M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (a b : Ordinal.{u})
    (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet) :
    productBundleSigma.Realize M e ↔
      ZFSet.prod b.toZFSet a.toZFSet ∈ e 0 ∧ productRelation a.toZFSet b.toZFSet ∈ e 0 ∧
        ∃ f ∈ e 0, OrderTypeCertificate (ZFSet.prod b.toZFSet a.toZFSet)
          (productRelation a.toZFSet b.toZFSet) (a*b).toZFSet f ∧ (a*b).toZFSet ∈ e 0 := by
  have sem (c d r f : ZFSet.{u}) (hc : c ∈ M) (hd : d ∈ M) (hr : r ∈ M) (hf : f ∈ M) :
      (Formula.conj (productMatrix 3 5 6 2 1 0)
        (.conj (.member 2 4) (.conj (.member 1 4) (.conj (.member 0 4) (.member 3 4))))).Realize M
          (cons f (cons r (cons d (cons c e)))) ↔
        (d = ZFSet.prod b.toZFSet a.toZFSet ∧ r = productRelation a.toZFSet b.toZFSet ∧
          OrderTypeCertificate d r c f) ∧ d ∈ e 0 ∧ r ∈ e 0 ∧ f ∈ e 0 ∧ c ∈ e 0 := by
    rw [Formula.absolute _ M hM _ (by
      intro i; rcases i with _|_|_|_|i
      exact hf; exact hr; exact hd; exact hc; exact he i)]
    simp only [Formula.Eval,productMatrix_eval,cons_zero,cons_succ,ha,hb]
  change (∃ c ∈ M, ∃ d ∈ M, ∃ r ∈ M, ∃ f ∈ M, _) ↔ _
  constructor
  · rintro ⟨c,hc,d,hd,r,hr,f,hf,h⟩
    obtain ⟨⟨rfl,rfl,hcert⟩,hd0,hr0,hf0,hc0⟩ := (sem c d r f hc hd hr hf).mp h
    have eq := hcert.exact (productRelation_wellFounded a b) (productRelation_transitive a b)
    rw [product_orderType] at eq
    subst c
    exact ⟨hd0,hr0,f,hf0,hcert,hc0⟩
  · rintro ⟨hd,hr,f,hf,hcert,hc⟩
    exact ⟨_,hM _ (he 0) _ hc,_,hM _ (he 0) _ hd,_,hM _ (he 0) _ hr,
      f,hM _ (he 0) _ hf,(sem _ _ _ f (hM _ (he 0) _ hc) (hM _ (he 0) _ hd)
        (hM _ (he 0) _ hr) (hM _ (he 0) _ hf)).mpr ⟨⟨rfl,rfl,hcert⟩,hd,hr,hf,hc⟩⟩

theorem product_certificate_collection (M : ZFSet.{u}) (C : Context M)
    (hRep : SigmaReplacement M) (hColl : SigmaCollection M)
    (a b : Ordinal.{u}) (ha : a.toZFSet ∈ M) (hb : b.toZFSet ∈ M) :
    ∃ U ∈ M, ∀ c < a,
      ZFSet.prod b.toZFSet c.toZFSet ∈ U ∧ productRelation c.toZFSet b.toZFSet ∈ U ∧
        ∃ f ∈ U, OrderTypeCertificate (ZFSet.prod b.toZFSet c.toZFSet)
          (productRelation c.toZFSet b.toZFSet) (c*b).toZFSet f ∧ (c*b).toZFSet ∈ U := by
  obtain ⟨W,hW,hcover⟩ := hColl productBundleSigma (fun _ => b.toZFSet) (fun _ => hb)
    a.toZFSet ha (by
      intro x hx
      obtain ⟨c,hca,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
      have hc := C.transitive _ ha _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr hca)
      obtain ⟨hprod,f,hf,hcert⟩ := ordinal_mul_internal_schemas M C.transitive C.pairing
        C.union C.power C.separation hRep c b hc hb
      have hd := product_mem M C.transitive C.pairing C.union C.power C.separation hb hc
      have hr := productRelation_mem M _ _ C.transitive C.pairing C.union C.power C.separation hc hb
      let B := FiniteTuple.elements [ZFSet.prod b.toZFSet c.toZFSet,
        productRelation c.toZFSet b.toZFSet,f,(c*b).toZFSet]
      have hB : B ∈ M := FiniteTuple.elements_mem M C.transitive C.pairing C.union
        (C.transitive _ C.omega_mem _ ZFSet.omega_zero) _ (by
          intro y hy
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
          rcases hy with rfl|rfl|rfl|rfl <;> assumption)
      refine ⟨B,hB,(productBundleSigma_spec M C.transitive _ (by
        intro i; rcases i with _|_|i; exact hB; exact hc; exact hb) c b rfl rfl).mpr ?_⟩
      have hm (y : ZFSet.{u}) : y ∈ B ↔ y ∈ [ZFSet.prod b.toZFSet c.toZFSet,
          productRelation c.toZFSet b.toZFSet,f,(c*b).toZFSet] := FiniteTuple.mem_elements _ _
      exact ⟨(hm _).mpr (by simp),(hm _).mpr (by simp),f,(hm _).mpr (by simp),hcert,
        (hm _).mpr (by simp)⟩)
  refine ⟨ZFSet.sUnion W,union_mem M C.transitive C.union hW,?_⟩
  intro c hc
  obtain ⟨B,hB,hcert⟩ := hcover c.toZFSet (Ordinal.toZFSet_mem_toZFSet_iff.mpr hc)
  obtain ⟨hd,hr,f,hf,hcert,hp⟩ := (productBundleSigma_spec M C.transitive _ (by
    intro i; rcases i with _|_|i
    exact C.transitive _ hW _ hB
    exact C.transitive _ ha _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr hc)
    exact hb) c b rfl rfl).mp hcert
  exact ⟨ZFSet.mem_sUnion.mpr ⟨B,hB,hd⟩,ZFSet.mem_sUnion.mpr ⟨B,hB,hr⟩,
    f,ZFSet.mem_sUnion.mpr ⟨B,hB,hf⟩,hcert,ZFSet.mem_sUnion.mpr ⟨B,hB,hp⟩⟩

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeOmegaLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions SentenceCoding
universe u

theorem OmegaGraph.relocate {M N d r f : ZFSet.{u}} (hg : OmegaGraph M d r f)
    (hval : ∀ t ∈ d, (Ordinal.omega0 ^ t.rank).toZFSet ∈ N) : OmegaGraph N d r f := by
  refine ⟨hg.1,hg.2.1,?_⟩
  intro t ht v hv hp
  obtain ⟨A,_,hs,ho,he⟩ := hg.2.2 t ht v hv hp
  exact ⟨A,(omegaStageStep_exact hg ht hs).symm ▸ hval t ht,hs,ho,he⟩

theorem omega_certificates_at_levels_oai (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧ ∀ δ : Ordinal.{u}, γ ≤ δ →
      a.toZFSet ∈ level (groundReals M) δ ∧
      (Ordinal.omega0 ^ a).toZFSet ∈ level (groundReals M) δ ∧
      OmegaPowerCertificates (level (groundReals M) δ) a.toZFSet ∧
      ∀ z ∈ level (groundReals M) δ,
        omegaPowerSentence.Sat (level (groundReals M) δ : Set ZFSet)
          (cons z (fun _ => a.toZFSet)) ↔ z = (Ordinal.omega0 ^ a).toZFSet := by
  let R := groundReals M
  let N := relativeModel M R
  have hR := groundReals_mem M hM hT
  have C := ground_relative_context M hM hT
  have hRep := relativeModel_sigma_replacement M R hM hT hR
  have hColl := relativeModel_sigma_collection M R hM hT hR
  have haN : a.toZFSet ∈ N := (ground_relativeModel_ordinal_iff M hM hT a).mpr ha
  have hyN := relative_omega_power_internal M hM hT a ha
  obtain ⟨_,f,hf,r,hr,hg,_⟩ := relative_omega_power_certificates M hM hT a ha
  obtain ⟨U,hU,hprod⟩ := product_certificate_collection N C hRep hColl
    (Ordinal.omega0 ^ a) Ordinal.omega0 hyN (toZFSet_omega.symm ▸ C.omega_mem)
  let e := cons a.toZFSet (cons (Ordinal.omega0 ^ a).toZFSet (cons f (cons r (fun _ => U))))
  have he (i : ℕ) : e i ∈ N := by
    rcases i with _|_|_|_|i
    exact haN; exact hyN; exact hf; exact hr; exact hU
  obtain ⟨γ,hγ,hγe⟩ := finite_parameters_in_relative_level M R hM hT e 5
    (fun i _ => (mem_relativeModel M R _ hM hT hR).mp (he i))
  refine ⟨γ,hγ,?_⟩
  intro δ hδ
  have hL (i : ℕ) (hi : i < 5) : e i ∈ level R δ := level_mono R hδ (hγe i hi)
  have hlt (t : ZFSet.{u}) (ht : t ∈ a.toZFSet) :
      Ordinal.omega0 ^ t.rank < Ordinal.omega0 ^ a := by
    obtain ⟨b,hb,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
    rw [Ordinal.rank_toZFSet]
    exact (Ordinal.opow_lt_opow_iff_right (by exact Ordinal.one_lt_omega0)).mpr hb
  have hc : OmegaPowerCertificates (level R δ) a.toZFSet := by
    refine ⟨hL 0 (by omega),f,hL 2 (by omega),r,hL 3 (by omega),
      hg.relocate (fun t ht => level_transitive R δ _ (hL 1 (by omega)) _
        (Ordinal.toZFSet_mem_toZFSet_iff.mpr (hlt t ht))),?_⟩
    intro t ht
    obtain ⟨hd,hr,f',hf',hcert,_⟩ := hprod _ (hlt t ht)
    have hsub : U ⊆ level R δ := level_transitive R δ U (hL 4 (by omega))
    exact ⟨hsub hd,hsub hr,f',hsub hf',hcert⟩
  refine ⟨hL 0 (by omega),hL 1 (by omega),hc,?_⟩
  intro z hz
  have henv : ∀ i, cons z (fun _ => a.toZFSet) i ∈ level R δ := by
    intro i; cases i; exact hz; exact hL 0 (by omega)
  have hω := OrdinalCoding.ground_level_omega_mem M hM hT δ
  constructor
  · intro h
    have hval := (omegaPowerSentence_sound _ (level_transitive R δ) hω _ henv h).2
    simpa only [cons_succ,cons_zero,Ordinal.rank_toZFSet] using hval
  · intro h
    apply omegaPowerSentence_of_certificates _ (level_transitive R δ) hω _ henv hc
    simpa only [cons_succ,cons_zero,Ordinal.rank_toZFSet] using h

end TuringRigidity.OrdinalArithmetic

end OAI
end

theorem solution.{u} : type_of% @OAI.TuringRigidity.OrdinalArithmetic.omega_certificates_at_levels_oai.{u} := @OAI.TuringRigidity.OrdinalArithmetic.omega_certificates_at_levels_oai.{u}
