-- Prove2me | solution 1 for OAI.TuringRigidity.RelativeConstructible.Construction.cofinal_one_real_definition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:30:14.078188+00:00
-- url     : https://prove2.me/submissions/163c315b-3321-4f35-a75b-449ac9757302

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_OrdinalCoding_cofinal_padded_code_certificates
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_Construction_largest_domain_definition

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

theorem seed_minimal (R M : ZFSet.{u}) (hM : Transitive M) (hR : R ∈ M) : seed R ⊆ M := by
  intro x hx
  obtain ⟨n,hn⟩ := (mem_seed R x).mp hx
  have sub : ∀ n : ℕ, iterUnion n ({R} : ZFSet) ⊆ M := by
    intro n
    induction n with
    | zero => intro y hy; obtain rfl := ZFSet.mem_singleton.mp hy; exact hR
    | succ n ih =>
      intro y hy
      obtain ⟨z,hz,hy⟩ := ZFSet.mem_sUnion.mp hy
      exact hM z (ih hz) y hy
  exact sub n hn

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

theorem stage_zero (R : ZFSet.{u}) : stage R ∅ = seed R := by
  apply ZFSet.ext; intro x
  simp [mem_stage]

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

theorem level_zero (R : ZFSet.{u}) : level R 0 = seed R := by
  rw [level,Ordinal.toZFSet_zero,stage_zero]

theorem level_succ (R : ZFSet.{u}) (o : Ordinal.{u}) :
    level R (o+1) = definablePower (level R o) := by
  simp only [level,Ordinal.toZFSet_add_one,stage_succ]

theorem level_mono (R : ZFSet.{u}) {i j : Ordinal.{u}} (hij : i ≤ j) : level R i ⊆ level R j :=
  stage_mono R (Ordinal.toZFSet_monotone hij)

theorem level_transitive (R : ZFSet.{u}) (o : Ordinal.{u}) : Transitive (level R o) :=
  stage_transitive R o.toZFSet

theorem mem_level_limit (R x : ZFSet.{u}) (o : Ordinal.{u}) (ho : Order.IsSuccLimit o) :
    x ∈ level R o ↔ ∃ i < o, x ∈ level R i := by
  constructor
  · intro hx
    rcases (mem_stage R o.toZFSet x).mp hx with hx|⟨a,ha,hx⟩
    · refine ⟨0,Ordinal.natCast_lt_of_isSuccLimit ho 0,?_⟩
      rwa [level_zero]
    · obtain ⟨i,hi,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ha
      refine ⟨i+1,ho.succ_lt hi,?_⟩
      rwa [level_succ]
  · rintro ⟨i,hi,hx⟩
    exact level_mono R hi.le hx

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalInfinity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem omega_transitive : Transitive ZFSet.omega.{u} := by
  intro x hx y hy
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  obtain ⟨i,_,rfl⟩ := (mem_natSet n y).mp hy
  exact (mem_omega _).mpr ⟨i,rfl⟩

end TuringRigidity.BoundedSetTheory

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_FiniteGraphSatisfaction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem prependValues_tail (w : ℕ → ZFSet.{u}) (n : ℕ) (e : ℕ → ZFSet.{u}) (i : ℕ) :
    prependValues w n e (n+i) = e i := by
  induction n generalizing e i with
  | zero => simp [prependValues]
  | succ n ih =>
    change prependValues w n (cons (w n) e) (n+1+i) = e i
    rw [show n+1+i = n+(i+1) by omega,ih]
    rfl

theorem prependValues_lt (w : ℕ → ZFSet.{u}) (n : ℕ) (e : ℕ → ZFSet.{u})
    (i : ℕ) (hi : i < n) : prependValues w n e i = w i := by
  induction n generalizing e with
  | zero => omega
  | succ n ih =>
    by_cases hin : i < n
    · exact ih _ hin
    · have he : i = n := by omega
      subst i
      exact prependValues_tail w n (cons (w n) e) 0

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

theorem SigmaDefinable.allMem (hM : Transitive M) (hT : SourceT M)
    (h : SigmaDefinable M P) (a : ℕ) :
    SigmaDefinable M (fun e => ∀ x ∈ e a, P (cons x e)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  have hC := sigma_collection M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hT.choice
  refine ⟨.allMem (2*a) (p.rename bindSlots),d,hd,?_⟩
  intro e he
  rw [SigmaFormula.realize_allMem M hM hT.pairing hT.union hT.separation.finitePrefix.bounded
    hT.replacement.finitePrefix hT.infinity hC _ _ _ (by
      intro i; unfold mix; split <;> first | exact he _ | exact hd _),mix_even]
  apply forall_congr'; intro x
  apply forall_congr'; intro hx
  rw [SigmaFormula.realize_rename]
  change p.Realize M (cons x (mix e d) ∘ bindSlots) ↔ _
  rw [bind_mix]
  exact hp (cons x e) (by intro i; cases i; exact hM _ (he a) x hx; exact he _)

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel
universe u

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

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory ElementaryModel
universe u

theorem ground_seed_shape (M : ZFSet.{u}) (hM : Transitive M) :
    seed (groundReals M) = insert (groundReals M) (groundReals M) := by
  let R := groundReals M
  have htrans : Transitive (insert R R) := by
    intro a ha b hb
    rcases ZFSet.mem_insert_iff.mp ha with rfl|ha
    · exact ZFSet.mem_insert_iff.mpr (Or.inr hb)
    · obtain ⟨haM,haω⟩ := (mem_groundReals M a).mp ha
      have hbω := haω hb
      have hbsub : b ⊆ ZFSet.omega := fun z hz => omega_transitive b hbω z hz
      exact ZFSet.mem_insert_iff.mpr (Or.inr ((mem_groundReals M b).mpr ⟨hM a haM b hb,hbsub⟩))
  apply ZFSet.ext; intro x
  constructor
  · exact fun hx => seed_minimal R _ htrans (ZFSet.mem_insert R R) hx
  · intro hx
    rcases ZFSet.mem_insert_iff.mp hx with rfl|hx
    · exact parameter_mem_seed R
    · exact parameter_subset_seed R hx

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SentenceInlining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem skipValue_env (x y : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (fun i => cons x (cons y e) (skipValue i)) = cons x e := by
  funext i; cases i <;> rfl

theorem bindComputed_spec (M : ZFSet.{u}) (n : ℕ)
    (f : ℕ → SentenceForm) (p : SentenceForm) (e w : ℕ → ZFSet.{u})
    (hw : ∀ i, i < n → w i ∈ M)
    (hf : ∀ i, i < n → ∀ x ∈ M,
      (f i).Sat (M : Set ZFSet) (cons x e) ↔ x = w i) :
    (bindComputed n f p).Sat (M : Set ZFSet) e ↔
      p.Sat (M : Set ZFSet) (prependValues w n e) := by
  induction n generalizing f e with
  | zero => rfl
  | succ n ih =>
    have hf' (y : ZFSet.{u}) : ∀ i, i < n → ∀ x ∈ M,
        ((f i).rename skipValue).Sat (M : Set ZFSet) (cons x (cons y e)) ↔ x = w i := by
      intro i hi x hx
      rw [SentenceForm.sat_rename,skipValue_env]
      exact hf i (by omega) x hx
    change (∃ x ∈ M, (f n).Sat (M : Set ZFSet) (cons x e) ∧
      (bindComputed n (fun i => (f i).rename skipValue) p).Sat
        (M : Set ZFSet) (cons x e)) ↔ _
    constructor
    · rintro ⟨x,hx,hfx,hp⟩
      obtain rfl := (hf n (by omega) x hx).mp hfx
      exact (ih _ _ (fun i hi => hw i (by omega)) (hf' (w n))).mp hp
    · intro hp
      exact ⟨w n,hw n (by omega),(hf n (by omega) _ (hw n (by omega))).mpr rfl,
        (ih _ _ (fun i hi => hw i (by omega)) (hf' (w n))).mpr hp⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructionInputData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem ConstructionInput.prefix_indexed (d : ConstructionInput.{u})
    (M : ZFSet.{u}) (i : ℕ) : (d.prefix i).Indexed M ↔ d.Indexed M := by
  cases d <;> rfl

theorem Construction.inputData_indexed (t : Construction.{u}) (M : ZFSet.{u})
    (hi : t.Indexed M) : ∀ k, (t.inputData k).Indexed M := by
  induction t with
  | reals => exact fun _ => trivial
  | parameter => exact fun _ => trivial
  | define o n p c ih =>
    intro k
    cases k with
    | zero => exact hi.1
    | succ k =>
      simp only [Construction.inputData]
      split
      next h =>
        rw [ConstructionInput.prefix_indexed]
        exact ih _ (hi.2 _) _
      next => trivial

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

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem mem_ordinalCut (A x : ZFSet.{u}) :
    x ∈ ordinalCut A ↔ x ∈ A ∧ x.IsOrdinal := ZFSet.mem_sep

theorem ordinalCut_isOrdinal (A : ZFSet.{u}) (hA : Transitive A) :
    (ordinalCut A).IsOrdinal := by
  apply ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr
  constructor
  · intro x hx y hy
    obtain ⟨hx,ho⟩ := (mem_ordinalCut A x).mp hx
    exact (mem_ordinalCut A y).mpr ⟨hA x hx y hy,ho.mem hy⟩
  · intro x hx; exact ((mem_ordinalCut A x).mp hx).2

theorem ordinalHeight_toZFSet (A : ZFSet.{u}) (hA : Transitive A) :
    (ordinalHeight A).toZFSet = ordinalCut A := (ordinalCut_isOrdinal A hA).toZFSet_rank_eq

theorem ordinal_mem_iff_height (A : ZFSet.{u}) (hA : Transitive A) (o : Ordinal.{u}) :
    o.toZFSet ∈ A ↔ o < ordinalHeight A := by
  rw [← Ordinal.toZFSet_mem_toZFSet_iff,ordinalHeight_toZFSet A hA,mem_ordinalCut]
  exact (and_iff_left (ZFSet.isOrdinal_toZFSet o)).symm

theorem ordinal_subset_iff_height (A : ZFSet.{u}) (hA : Transitive A) (o : Ordinal.{u}) :
    o.toZFSet ⊆ A ↔ o ≤ ordinalHeight A := by
  rw [← Ordinal.toZFSet_subset_toZFSet_iff,ordinalHeight_toZFSet A hA]
  constructor
  · intro h x hx
    exact (mem_ordinalCut A x).mpr ⟨h hx,(ZFSet.isOrdinal_toZFSet o).mem hx⟩
  · intro h x hx; exact ((mem_ordinalCut A x).mp (h hx)).1

theorem ordinalSentence_bound : ordinalSentence.bound = 1 := by rfl

theorem ordinalSentence_spec (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : e 0 ∈ A) :
    ordinalSentence.Sat (A : Set ZFSet) e ↔ (e 0).IsOrdinal := by
  have hs := ordinalSentence.finite_support (A : Set ZFSet) e (fun _ => e 0) (by
    intro i hi
    rw [ordinalSentence_bound] at hi
    have : i = 0 := by omega
    subst i; rfl)
  rw [hs]
  exact (bounded_sat _ _ _).trans
    (((ordinalFormula 0).absolute A hA _ (fun _ => he)).trans (eval_ordinalFormula 0 _))

theorem ordinalCut_mem_definablePower (A : ZFSet.{u}) (hA : Transitive A) :
    ordinalCut A ∈ definablePower A := by
  apply (mem_definablePower A _).mpr
  refine ⟨0,ordinalSentence,Fin.elim0,by rw [ordinalSentence_bound],fun i => Fin.elim0 i,?_⟩
  apply ZFSet.ext; intro x
  rw [mem_ordinalCut,mem_definedSubset]
  apply and_congr_right; intro hx
  exact (ordinalSentence_spec A hA (cons x (tupleEnv (Fin.elim0 : Fin 0 → ZFSet.{u}))) hx).symm

theorem ordinal_definablePower_iff (A : ZFSet.{u}) (hA : Transitive A) (o : Ordinal.{u}) :
    o.toZFSet ∈ definablePower A ↔ o ≤ ordinalHeight A := by
  constructor
  · intro ho
    exact (ordinal_subset_iff_height A hA o).mp (subset_of_mem_definablePower ho)
  · intro ho
    rcases lt_or_eq_of_le ho with ho|rfl
    · exact subset_definablePower hA ((ordinal_mem_iff_height A hA o).mpr ho)
    · rw [ordinalHeight_toZFSet A hA]
      exact ordinalCut_mem_definablePower A hA

theorem ordinalHeight_definablePower (A : ZFSet.{u}) (hA : Transitive A) :
    ordinalHeight (definablePower A) = ordinalHeight A + 1 := by
  apply le_antisymm
  · by_contra h
    have hm := (ordinal_mem_iff_height _ (definablePower_transitive hA) _).mpr (lt_of_not_ge h)
    have := (ordinal_definablePower_iff A hA _).mp hm
    exact (not_le_of_gt (lt_add_one (ordinalHeight A))) this
  · apply Order.add_one_le_iff.mpr
    exact (ordinal_mem_iff_height _ (definablePower_transitive hA) _).mp
      ((ordinal_definablePower_iff A hA _).mpr le_rfl)

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

theorem orderTypeCertificate_exists (M d r : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hd : d ∈ M) (hr : r ∈ M)
    (wf : WellFounded (Rel d r)) (ht : TransitiveOn d r) :
    (orderType d r wf).toZFSet ∈ M ∧
      ∃ f ∈ M, OrderTypeCertificate d r (orderType d r wf).toZFSet f := by
  obtain ⟨ha,f,hf,hg,ho⟩ := orderType_internal M d r hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hd hr wf ht
  exact ⟨ha,f,hf,ZFSet.isOrdinal_toZFSet _,hg,ho⟩

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

theorem ordinal_internal_of_presentation (M d r : ZFSet.{u}) (o : Ordinal.{u})
    (hM : Transitive M) (hT : SourceT M) (hd : d ∈ M) (hr : r ∈ M) (hon : On d r)
    (j : ZFSet.{u} → ZFSet.{u})
    (hj : ∀ x ∈ d, j x ∈ o.toZFSet)
    (hs : ∀ z ∈ o.toZFSet, ∃ x ∈ d, j x = z)
    (he : ∀ x ∈ d, ∀ y ∈ d, ZFSet.pair x y ∈ r ↔ j x ∈ j y) :
    o.toZFSet ∈ M ∧ ∃ f ∈ M, Presents d f j ∧ OrderTypeCertificate d r o.toZFSet f := by
  have wf : WellFounded (Rel d r) := by
    apply (InvImage.wf j ZFSet.mem_wf).mono
    intro x y hxy
    exact (he x hxy.1 y (right_mem hon hxy.2)).mp hxy.2
  have ht : TransitiveOn d r := by
    intro x hx y hy z hz hxy hyz
    apply (he x hx z hz).mpr
    exact ((ZFSet.isOrdinal_toZFSet o).mem (hj z hz)).subset_of_mem
      ((he y hy z hz).mp hyz) ((he x hx y hy).mp hxy)
  have hval := value_of_ordinal_presentation d r o wf j hj hs he
  have heq := orderType_of_ordinal_presentation d r o wf j hj hs he
  obtain ⟨ha,f,hf,hc⟩ := orderTypeCertificate_exists M d r hM hT hd hr wf ht
  rw [heq] at ha hc
  refine ⟨ha,f,hf,?_,hc⟩
  intro z
  rw [hc.2.1.mem_iff wf]
  apply exists_congr; intro x
  apply and_congr_right; intro hx
  rw [hval x hx]

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

theorem ordinal_mul_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a b : Ordinal.{u}) (ha : a.toZFSet ∈ M) (hb : b.toZFSet ∈ M) :
    (a*b).toZFSet ∈ M ∧ ∃ f ∈ M,
      Presents (ZFSet.prod b.toZFSet a.toZFSet) f (productValue a) ∧
      OrderTypeCertificate (ZFSet.prod b.toZFSet a.toZFSet)
        (productRelation a.toZFSet b.toZFSet) (a*b).toZFSet f :=
  ordinal_internal_of_presentation M _ _ _ hM hT
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hb ha)
    (productRelation_mem M _ _ hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded ha hb)
    (productRelation_on _ _) (productValue a) (productValue_mem a b)
    (productValue_surjective a b) (productValue_relation a b)

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

theorem productSentence_sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (a b : Ordinal.{u})
    (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet) :
    productSentence.Sat (M : Set ZFSet) e ↔ e 0 = (a*b).toZFSet := by
  have haM : a.toZFSet ∈ M := ha ▸ he 1
  have hbM : b.toZFSet ∈ M := hb ▸ he 2
  obtain ⟨_,f,hf,_,hc⟩ := ordinal_mul_internal M hM hT a b haM hbM
  exact productSentence_spec_of_certificate M hM e he a b ha hb
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hbM haM)
    (productRelation_mem M _ _ hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded haM hbM)
    ⟨f,hf,hc⟩

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

theorem ordinal_mul_omega_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) : (a*Ordinal.omega0).toZFSet ∈ M := by
  have ho : Ordinal.omega0.toZFSet ∈ M := by
    simpa only [toZFSet_omega] using
      omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity
  exact (ordinal_mul_internal M hM hT a Ordinal.omega0 ha ho).1

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

theorem productSigma_sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (a b : Ordinal.{u})
    (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet) :
    productSigma.Realize M e ↔ e 0 = (a*b).toZFSet := by
  rw [← sigma_sat,productSigma_sentence]
  exact productSentence_sourceT M hM hT e he a b ha hb

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

theorem omegaGraph_of_mem_iff (M d f : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hdM : d ∈ M) (hfM : f ∈ M) (hd : d.IsOrdinal)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (omegaNext x)) :
    OmegaGraph M d (iterUnion 2 f) f := by
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact hM _ (omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity) _ ((mem_omega _).mpr ⟨1,rfl⟩)
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
      hA ▸ stageImage_mem M hM hT h1 (hM d hdM x hx) hfM,?_,ZFSet.isOrdinal_toZFSet _,?_⟩
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

theorem mulOmega_sigmaDefinable (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    SigmaDefinable M (fun e => (e 1).IsOrdinal ∧ e 0 = ((e 1).rank*Ordinal.omega0).toZFSet) := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have ho := omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity
  let p := SigmaFormula.conj (.bounded (ordinalFormula 2))
    (productSigma.rename (fun i => if i = 0 then 0 else if i = 1 then 2 else 1))
  refine ⟨p,fun _ => ZFSet.omega,fun _ => ho,?_⟩
  intro e he
  rw [SigmaFormula.realize_conj]
  have hoSem : (SigmaFormula.bounded (ordinalFormula 2)).Realize M
      (mix e (fun _ => ZFSet.omega)) ↔ (e 1).IsOrdinal := by
    rw [SigmaFormula.Realize,Formula.absolute _ M hM _ (by
      intro i; unfold mix; split; exact he _; exact ho),eval_ordinalFormula]
    rfl
  rw [hoSem]
  apply and_congr_right; intro heo
  rw [SigmaFormula.realize_rename]
  exact productSigma_sourceT M hM hT _ (by
    intro i; change mix e (fun _ => ZFSet.omega)
      (if i = 0 then 0 else if i = 1 then 2 else 1) ∈ M
    split; exact he 0
    split; exact he 1
    exact ho) (e 1).rank Ordinal.omega0 heo.toZFSet_rank_eq.symm toZFSet_omega.symm

theorem omegaGraph_sigmaDefinable (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (d r f : ℕ) : SigmaDefinable M (fun e => OmegaGraph M (e d) (e r) (e f)) := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact C.nat_mem 1
  have hs : SigmaDefinable M (fun e =>
      StageStep (1 : Ordinal.{u}).toZFSet (e (f+3)) (e (r+3)) (e 2) (e 0)) := by
    have hb := (stageStep_definable C 0 (f+4) (r+4) 3 1).toSigma hM
    have hc := ((equal_param h1 0).toSigma hM).and hb
    exact hc.existsSet.congr (fun e _ => by simp [h1])
  have hv : SigmaDefinable M (fun e => (e 0).IsOrdinal ∧
      e 1 = ((e 0).rank*Ordinal.omega0).toZFSet) :=
    (mulOmega_sigmaDefinable M hM hT).subst (fun i => if i = 0 then 1 else 0)
  have hi := SigmaDefinable.impBounded C (defPairMem C 1 0 (f+2)) (hs.and hv).existsSet
  exact ((ordinal_definable C d).toSigma hM).and
    (((functionGraph_definable C d r f).toSigma hM).and
      ((hi.allMem hM hT (r+1)).allMem hM hT d))

theorem uniform_omega_certificate (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ∃ p : SigmaFormula, ∃ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ M) ∧
      ∀ x ∈ M, ∀ f ∈ M, p.Realize M (cons f (cons x e)) ↔
        ∃ r ∈ M, OmegaGraph M (insert x x) r f := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have hd : Definable M (fun e => e 0 = insert (e 3) (e 3)) := by
    refine ⟨.successor 0 6,fun _ => ZFSet.omega,fun _ => C.omega_mem,?_⟩
    intro e; simp [Formula.eval_successor,mix]
  have hg := (hd.toSigma hM).and (omegaGraph_sigmaDefinable M hM hT 0 1 2)
  obtain ⟨p,e,he,hp⟩ := sigma_binary_relation (fun x f => ∃ r ∈ M,
    ∃ d ∈ M, d = insert x x ∧ OmegaGraph M d r f) hg.existsSet.existsSet
  refine ⟨p,e,he,?_⟩
  intro x hx f hf
  rw [hp x hx f hf]
  constructor
  · rintro ⟨r,hr,d,_,rfl,h⟩; exact ⟨r,hr,h⟩
  · rintro ⟨r,hr,h⟩
    exact ⟨r,hr,insert x x,insert_self_mem M hM hT.pairing hT.union hx,rfl,h⟩

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_InternalOmegaPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions
universe u

theorem internal_omegaGraph (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (x : ZFSet.{u}) (hxM : x ∈ M) (hxo : x.IsOrdinal) :
    ∃ f ∈ M, OmegaGraph M (insert x x) (iterUnion 2 f) f := by
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact hM _ (omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity) _ ((mem_omega _).mpr ⟨1,rfl⟩)
  obtain ⟨p,e,he,hp⟩ := uniform_omega_certificate M hM hT
  induction x using ZFSet.inductionOn with
  | h x ih =>
    have cert (y f : ZFSet.{u}) (hy : y ∈ x) (hf : f ∈ M) := hp y (hM x hxM y hy) f hf
    obtain ⟨b,hb,hbdef⟩ := hT.replacement.finitePrefix p e he x hxM (by
      intro y hy
      obtain ⟨f,hf,hfg⟩ := ih y hy (hM x hxM y hy) (hxo.mem hy)
      refine ⟨f,hf,(cert y f hy hf).mpr
        ⟨_,iterUnion_mem M hM hT.union hf 2,hfg⟩,?_⟩
      intro g hg hcg
      obtain ⟨r,_,hgg⟩ := (cert y g hy hg).mp hcg
      exact hgg.unique hfg)
    have hbg (f : ZFSet.{u}) : f ∈ b ↔
        ∃ y ∈ x, ∃ r ∈ M, OmegaGraph M (insert y y) r f := by
      constructor
      · intro hf
        have hfM := hM b hb f hf
        obtain ⟨y,hy,hc⟩ := (hbdef f hfM).mp hf
        exact ⟨y,hy,(cert y f hy hfM).mp hc⟩
      · rintro ⟨y,hy,r,hr,hg⟩
        obtain ⟨f',hf',hg'⟩ := ih y hy (hM x hxM y hy) (hxo.mem hy)
        have heq := hg.unique hg'
        have hfM : f ∈ M := heq ▸ hf'
        exact (hbdef f hfM).mpr ⟨y,hy,(cert y f hy hfM).mpr ⟨r,hr,hg⟩⟩
    let g := ZFSet.sUnion b
    have hgM : g ∈ M := union_mem M hM hT.union hb
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
        obtain ⟨f,hf,hfg⟩ := ih y hy (hM x hxM y hy) (hxo.mem hy)
        exact ZFSet.mem_sUnion.mpr ⟨f,(hbg f).mpr
          ⟨y,hy,_,iterUnion_mem M hM hT.union hf 2,hfg⟩,
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
      hvalue ▸ stageImage_mem M hM hT h1 hxM hgM
    have hvM : omegaNext x ∈ M := by
      rw [omegaNext,Ordinal.opow_add_one]
      exact ordinal_mul_omega_internal M hM hT _ hpow
    let f := g ∪ ({ZFSet.pair x (omegaNext x)} : ZFSet.{u})
    have hfM : f ∈ M := binary_union_mem M hM hT.pairing hT.union hgM
      (singleton_mem M hM hT.pairing (orderedPair_mem M hM hT.pairing hxM hvM))
    have hsucc : (insert x x).IsOrdinal := by
      rw [← hxo.toZFSet_rank_eq,← Ordinal.toZFSet_add_one]
      exact ZFSet.isOrdinal_toZFSet _
    refine ⟨f,hfM,omegaGraph_of_mem_iff M _ f hM hT
      (insert_self_mem M hM hT.pairing hT.union hxM) hfM hsucc ?_⟩
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

theorem ordinal_omega_opow_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) : (Ordinal.omega0 ^ a).toZFSet ∈ M := by
  obtain ⟨f,hf,hg⟩ := internal_omegaGraph M hM hT a.toZFSet ha (ZFSet.isOrdinal_toZFSet a)
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact hM _ (omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity) _ ((mem_omega _).mpr ⟨1,rfl⟩)
  have hv := omegaStageImage _ f a.toZFSet hg.1 (ZFSet.mem_insert_iff.mpr (Or.inl rfl)) hg.mem_iff
  rw [Ordinal.rank_toZFSet] at hv
  exact hv ▸ stageImage_mem M hM hT h1 ha hf

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_LevelOrdinalHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem ordinalHeight_level (R : ZFSet.{u}) (o : Ordinal.{u}) :
    ordinalHeight (level R o) = ordinalHeight (seed R) + o := by
  induction o using Ordinal.limitRecOn with
  | zero => simp only [level_zero,add_zero]
  | add_one o ih =>
    rw [level_succ,ordinalHeight_definablePower _ (level_transitive R o),ih,add_assoc]
  | limit o ho ih =>
    apply le_antisymm
    · by_contra h
      have hx := (ordinal_mem_iff_height _ (level_transitive R o) _).mpr (lt_of_not_ge h)
      obtain ⟨i,hi,hx⟩ := (mem_level_limit R _ o ho).mp hx
      have hx' := (ordinal_mem_iff_height _ (level_transitive R i) _).mp hx
      rw [ih i hi] at hx'
      exact (not_lt_of_ge (add_le_add (le_refl (ordinalHeight (seed R))) hi.le)) hx'
    · by_contra h
      obtain ⟨i,hi,hi'⟩ := Ordinal.lt_add_iff_of_isSuccLimit ho |>.mp (lt_of_not_ge h)
      rw [← ih i hi] at hi'
      have hx := (ordinal_mem_iff_height _ (level_transitive R i) _).mpr hi'
      have hx' := level_mono R hi.le hx
      exact (lt_irrefl _) ((ordinal_mem_iff_height _ (level_transitive R o) _).mp hx')

theorem ordinal_mem_level_iff (R : ZFSet.{u}) (o a : Ordinal.{u}) :
    a.toZFSet ∈ level R o ↔ a < ordinalHeight (seed R) + o := by
  rw [ordinal_mem_iff_height _ (level_transitive R o),ordinalHeight_level]

theorem largest_ordinal_level_succ (R : ZFSet.{u}) (o : Ordinal.{u}) :
    (ordinalHeight (seed R) + o).toZFSet ∈ level R (o+1) ∧
      ∀ a : Ordinal.{u}, a.toZFSet ∈ level R (o+1) ↔ a ≤ ordinalHeight (seed R) + o := by
  have h (a : Ordinal.{u}) : a.toZFSet ∈ level R (o+1) ↔ a ≤ ordinalHeight (seed R) + o := by
    rw [ordinal_mem_level_iff,← add_assoc]
    exact Order.lt_add_one_iff
  exact ⟨(h _).mpr le_rfl,h⟩

theorem largest_ordinal_at_difference (R : ZFSet.{u}) (a : Ordinal.{u})
    (ha : ordinalHeight (seed R) ≤ a) :
    a.toZFSet ∈ level R (a - ordinalHeight (seed R) + 1) ∧
      ∀ b : Ordinal.{u}, b.toZFSet ∈ level R (a - ordinalHeight (seed R) + 1) ↔ b ≤ a := by
  simpa only [Ordinal.add_sub_cancel_of_le ha] using
    largest_ordinal_level_succ R (a - ordinalHeight (seed R))

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_LargestOrdinalSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem largestOrdinalSentence_bound : largestOrdinalSentence.bound = 1 := by rfl

theorem largestOrdinalSentence_spec (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : e 0 ∈ A) :
    largestOrdinalSentence.Sat (A : Set ZFSet) e ↔
      (e 0).IsOrdinal ∧ ∀ x ∈ A, x.IsOrdinal → x ∈ e 0 ∨ x = e 0 := by
  simp only [largestOrdinalSentence,SentenceForm.Sat,SentenceForm.sat_all,
    SentenceForm.sat_imp,SentenceForm.sat_disj,cons_zero,cons_succ]
  rw [ordinalSentence_spec A hA e he]
  apply and_congr_right; intro _
  apply forall_congr'; intro x
  apply forall_congr'; intro hx
  rw [ordinalSentence_spec A hA (cons x e) hx]
  rfl

theorem largestOrdinalSentence_unique (A : ZFSet.{u}) (hA : Transitive A)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ A)
    (hmax : ∀ b : Ordinal.{u}, b.toZFSet ∈ A → b ≤ a)
    (e : ℕ → ZFSet.{u}) (he : e 0 ∈ A) :
    largestOrdinalSentence.Sat (A : Set ZFSet) e ↔ e 0 = a.toZFSet := by
  rw [largestOrdinalSentence_spec A hA e he]
  constructor
  · rintro ⟨ho,hm⟩
    have heq := ho.toZFSet_rank_eq
    have hle := hmax (e 0).rank (by rwa [heq])
    have hge : a ≤ (e 0).rank := by
      rcases hm a.toZFSet ha (ZFSet.isOrdinal_toZFSet a) with h|h
      · rw [← heq,Ordinal.toZFSet_mem_toZFSet_iff] at h
        exact h.le
      · have := congrArg ZFSet.rank h
        simpa only [Ordinal.rank_toZFSet] using this.le
    exact heq.symm.trans (congrArg Ordinal.toZFSet (le_antisymm hle hge))
  · intro heq
    refine ⟨heq ▸ ZFSet.isOrdinal_toZFSet a,?_⟩
    intro x hx ho
    have hle : x.rank ≤ a := hmax x.rank (by rwa [ho.toZFSet_rank_eq])
    rcases lt_or_eq_of_le hle with h|h
    · left
      rw [heq,← ho.toZFSet_rank_eq]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr h
    · right
      rw [← ho.toZFSet_rank_eq,h,heq]

theorem largestOrdinalSentence_level (R : ZFSet.{u}) (o : Ordinal.{u})
    (e : ℕ → ZFSet.{u}) (he : e 0 ∈ level R (o+1)) :
    largestOrdinalSentence.Sat (level R (o+1) : Set ZFSet) e ↔
      e 0 = (ordinalHeight (seed R) + o).toZFSet := by
  have hm := largest_ordinal_level_succ R o
  exact largestOrdinalSentence_unique _ (level_transitive R _) _ hm.1
    (fun b hb => (hm.2 b).mp hb) e he

theorem bindLargestOrdinal_bound (p : SentenceForm) :
    (bindLargestOrdinal p).bound = p.bound - 1 := by
  change max largestOrdinalSentence.bound p.bound - 1 = p.bound - 1
  rw [largestOrdinalSentence_bound]
  omega

theorem bindLargestOrdinal_level (p : SentenceForm) (R : ZFSet.{u}) (o : Ordinal.{u})
    (e : ℕ → ZFSet.{u}) :
    (bindLargestOrdinal p).Sat (level R (o+1) : Set ZFSet) e ↔
      p.Sat (level R (o+1) : Set ZFSet) (cons (ordinalHeight (seed R) + o).toZFSet e) := by
  change (∃ a ∈ level R (o+1), largestOrdinalSentence.Sat _ (cons a e) ∧ p.Sat _ (cons a e)) ↔ _
  constructor
  · rintro ⟨a,ha,hm,hp⟩
    have heq := (largestOrdinalSentence_level R o (cons a e) ha).mp hm
    change a = _ at heq
    simpa only [heq] using hp
  · intro hp
    have hm := largest_ordinal_level_succ R o
    exact ⟨_,hm.1,(largestOrdinalSentence_level R o _ hm.1).mpr rfl,hp⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_FiniteDefinitionTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem definedSubset_of_membership (M V : ZFSet.{u}) (hM : Transitive M)
    (hV : V ∈ M) (p : SentenceForm) (e : ℕ → ZFSet.{u})
    (hp : ∀ z ∈ M, p.Sat (M : Set ZFSet) (cons z e) ↔ z ∈ V) :
    V = definedSubset M p (fun i : Fin p.bound => e i) := by
  apply ZFSet.ext; intro z
  rw [mem_definedSubset]
  have hs := p.finite_support (M : Set ZFSet) (cons z e)
    (cons z (tupleEnv (fun i : Fin p.bound => e i)))
    (by
      intro i hin
      cases i with
      | zero => rfl
      | succ i => simp only [cons_succ,tupleEnv,dite_eq_left (show i < p.bound by omega)])
  constructor
  · intro hz
    have hzM := hM V hV z hz
    exact ⟨hzM,hs.mp ((hp z hzM).mpr hz)⟩
  · rintro ⟨hzM,hz⟩
    exact (hp z hzM).mp (hs.mpr hz)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_FiniteStageDefinition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic
universe u

theorem Construction.ordinalData_mem (t : Construction.{u}) (M : ZFSet.{u})
    (hi : t.Indexed M) (k : ℕ) (o : Ordinal.{u}) (ho : t.ordinalData k = some o) :
    o.toZFSet ∈ M := by
  have hk := t.inputData_indexed M hi k
  unfold Construction.ordinalData at ho
  cases hd : t.inputData k with
  | reals => simp [hd] at ho
  | realPath path => simp [hd] at ho
  | stage a =>
    rw [hd] at hk
    simp only [hd] at ho
    have he : a = o := Option.some.inj ho
    exact he ▸ hk

end TuringRigidity.RelativeConstructible

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

theorem natSet_isOrdinal (n : ℕ) : (natSet.{u} n).IsOrdinal := by
  induction n with
  | zero => exact ZFSet.isOrdinal_empty
  | succ n ih => exact ZFSet.isOrdinal_succ ih

theorem omega_isOrdinal : ZFSet.omega.{u}.IsOrdinal := by
  apply ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr
  refine ⟨omega_transitive,?_⟩
  intro x hx
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  exact natSet_isOrdinal n

theorem omega_mem_groundReals (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ZFSet.omega ∈ groundReals M :=
  (mem_groundReals M _).mpr ⟨sourceT_omega_mem M hM hT,fun _ h => h⟩

theorem groundReals_not_isOrdinal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ¬ (groundReals M).IsOrdinal := by
  let s : ZFSet.{u} := {natSet 1}
  have h1ω : natSet.{u} 1 ∈ ZFSet.omega := (mem_omega _).mpr ⟨1,rfl⟩
  have hsM : s ∈ M := singleton_mem M hM hT.pairing
    (hM _ (sourceT_omega_mem M hM hT) _ h1ω)
  have hsR : s ∈ groundReals M := (mem_groundReals M s).mpr ⟨hsM,by
    intro x hx
    obtain rfl := ZFSet.mem_singleton.mp hx
    exact h1ω⟩
  intro h
  have hs := h.mem hsR
  have hz : natSet.{u} 0 ∈ s := hs.isTransitive.mem_trans ((natSet_mem_natSet 0 1).mpr (by decide))
    (ZFSet.mem_singleton.mpr rfl)
  have he : (0 : ℕ) = 1 := natSet_injective (ZFSet.mem_singleton.mp hz)
  exact Nat.zero_ne_one he

theorem ordinalCut_ground_seed (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ordinalCut (seed (groundReals M)) = insert ZFSet.omega ZFSet.omega := by
  apply ZFSet.ext; intro x
  rw [mem_ordinalCut,ground_seed_shape M hM]
  constructor
  · rintro ⟨hx,ho⟩
    rcases ZFSet.mem_insert_iff.mp hx with rfl|hx
    · exact False.elim (groundReals_not_isOrdinal M hM hT ho)
    · exact ZFSet.mem_insert_iff.mpr
        ((ho.subset_iff_eq_or_mem omega_isOrdinal).mp ((mem_groundReals M x).mp hx).2)
  · intro hx
    rcases ZFSet.mem_insert_iff.mp hx with rfl|hx
    · exact ⟨ZFSet.mem_insert_of_mem _ (omega_mem_groundReals M hM hT),omega_isOrdinal⟩
    · have hxR : x ∈ groundReals M := (mem_groundReals M x).mpr
        ⟨hM _ (sourceT_omega_mem M hM hT) _ hx,fun y hy => omega_transitive x hx y hy⟩
      exact ⟨ZFSet.mem_insert_of_mem _ hxR,omega_isOrdinal.mem hx⟩

theorem ordinalHeight_ground_seed (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ordinalHeight (seed (groundReals M)) = (insert ZFSet.omega ZFSet.omega : ZFSet.{u}).rank := by
  unfold ordinalHeight
  rw [ordinalCut_ground_seed M hM hT]

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformHeightDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u
attribute [local irreducible] Construction.ownRealsMembership SentenceForm.bound

theorem ground_seed_offset (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ordinalHeight (seed (groundReals M)) = realSeedOffset := ordinalHeight_ground_seed M hM hT

theorem largestOrdinal_ground_domain (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : realSeedOffset ≤ a) :
    a.toZFSet ∈ level (groundReals M) (heightDomainIndex a) ∧
      ∀ e : ℕ → ZFSet.{u}, e 0 ∈ level (groundReals M) (heightDomainIndex a) →
        (largestOrdinalSentence.Sat (level (groundReals M) (heightDomainIndex a) : Set ZFSet) e ↔
          e 0 = a.toZFSet) := by
  have hoff := ground_seed_offset M hM hT
  have hm := largest_ordinal_at_difference (groundReals M) a (hoff ▸ ha)
  rw [hoff] at hm
  refine ⟨hm.1,?_⟩
  intro e he
  exact largestOrdinalSentence_unique _ (level_transitive _ _) a hm.1
    (fun b hb => (hm.2 b).mp hb) e he

theorem bindLargestOrdinal_ground_domain (p : SentenceForm) (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (a : Ordinal.{u}) (ha : realSeedOffset ≤ a)
    (e : ℕ → ZFSet.{u}) :
    (bindLargestOrdinal p).Sat (level (groundReals M) (heightDomainIndex a) : Set ZFSet) e ↔
      p.Sat (level (groundReals M) (heightDomainIndex a) : Set ZFSet) (cons a.toZFSet e) := by
  have h := bindLargestOrdinal_level p (groundReals M) (a-realSeedOffset) e
  rw [ground_seed_offset M hM hT,Ordinal.add_sub_cancel_of_le ha] at h
  exact h

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalPairCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
universe u
open Ordinal

theorem cnf_monomial (x : Ordinal.{u}) :
    CNF omega0 (omega0 ^ x) = [(x,1)] := by
  simpa only [mul_one,add_zero,CNF.zero_right] using
    (CNF.opow_mul_add (b := omega0) (e := x) (x := 1) (y := 0)
      one_lt_omega0 one_ne_zero one_lt_omega0 (opow_pos x omega0_pos))

theorem pairCode_cnf_left (x y : Ordinal.{u}) (hy : y ≤ x) :
    CNF omega0 (pairCode x y) = [(x+1,1),(y,1)] := by
  rw [pairCode,ite_eq_left hy]
  have h := CNF.opow_mul_add (b := omega0) (e := x+1) (x := 1) (y := omega0 ^ y)
    one_lt_omega0 one_ne_zero one_lt_omega0
    ((opow_lt_opow_iff_right one_lt_omega0).mpr (hy.trans_lt (lt_add_one x)))
  simpa only [mul_one,cnf_monomial] using h

theorem pairCode_cnf_right (x y : Ordinal.{u}) (hy : ¬ y ≤ x) :
    CNF omega0 (pairCode x y) = [(y+1,2),(x,1)] := by
  rw [pairCode,ite_eq_right hy]
  have h := CNF.opow_mul_add (b := omega0) (e := y+1) (x := 2) (y := omega0 ^ x)
    one_lt_omega0 (by simp) (by exact_mod_cast natCast_lt_omega0 2)
    ((opow_lt_opow_iff_right one_lt_omega0).mpr
      ((lt_of_not_ge hy).trans (lt_add_one y)))
  simpa only [cnf_monomial] using h

theorem unpairCode_pairCode (x y : Ordinal.{u}) : unpairCode (pairCode x y) = (x,y) := by
  by_cases hy : y ≤ x
  · simp [unpairCode,pairCode_cnf_left x y hy,Ordinal.pred_add_one]
  · simp [unpairCode,pairCode_cnf_right x y hy,Ordinal.pred_add_one]

theorem pairCode_inj (x y x' y' : Ordinal.{u}) :
    pairCode x y = pairCode x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    have h' := congrArg unpairCode h
    simpa only [unpairCode_pairCode,Prod.mk.injEq] using h'
  · rintro ⟨rfl,rfl⟩; rfl

theorem max_lt_pairCode (x y : Ordinal.{u}) : max x y < pairCode x y := by
  by_cases hy : y ≤ x
  · rw [max_eq_left hy,pairCode,ite_eq_left hy]
    exact ((lt_add_one x).trans_le (right_le_opow (x+1) one_lt_omega0)).trans_le le_self_add
  · have hx : x ≤ y := (lt_of_not_ge hy).le
    rw [max_eq_right hx,pairCode,ite_eq_right hy]
    have hmul : omega0 ^ (y+1) ≤ omega0 ^ (y+1) * 2 :=
      Ordinal.le_mul_left _ (zero_lt_one.trans_le one_le_two)
    exact ((lt_add_one y).trans_le (right_le_opow (y+1) one_lt_omega0)).trans_le
      (hmul.trans le_self_add)

theorem left_lt_pairCode (x y : Ordinal.{u}) : x < pairCode x y :=
  (le_max_left x y).trans_lt (max_lt_pairCode x y)

theorem right_lt_pairCode (x y : Ordinal.{u}) : y < pairCode x y :=
  (le_max_right x y).trans_lt (max_lt_pairCode x y)

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_FiniteOrdinalCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
universe u

theorem vectorDecode_vectorCode {n : ℕ} (v : Fin n → Ordinal.{u}) :
    vectorDecode n (vectorCode v) = v := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [vectorCode,vectorDecode,unpairCode_pairCode,Fin.cases_zero]
    · simpa only [vectorCode,vectorDecode,unpairCode_pairCode,Fin.cases_succ] using
        congrFun (ih (fun k => v k.succ)) j

theorem entry_lt_vectorCode {n : ℕ} (v : Fin n → Ordinal.{u}) (i : Fin n) :
    v i < vectorCode v := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact left_lt_pairCode _ _
    · exact (ih (fun k => v k.succ) j).trans (right_lt_pairCode _ _)

theorem paddedDecode_paddedCode {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u}) :
    paddedDecode n (paddedCode v β) = v := by
  simp only [paddedDecode,paddedCode,unpairCode_pairCode,vectorDecode_vectorCode]

theorem padding_lt_paddedCode {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u}) :
    β < paddedCode v β := left_lt_pairCode _ _

theorem entry_lt_paddedCode {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u}) (i : Fin n) :
    v i < paddedCode v β := (entry_lt_vectorCode v i).trans (right_lt_pairCode _ _)

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalCodeDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory ElementaryModel RelativeConstructible
universe u

theorem paddedCode_entries_mem (A : ZFSet.{u}) (hA : Transitive A)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (ha : (paddedCode v β).toZFSet ∈ A) (i : Fin n) : (v i).toZFSet ∈ A :=
  hA _ ha _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr (entry_lt_paddedCode v β i))

theorem paddedCode_padding_mem (A : ZFSet.{u}) (hA : Transitive A)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (ha : (paddedCode v β).toZFSet ∈ A) : β.toZFSet ∈ A :=
  hA _ ha _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr (padding_lt_paddedCode v β))

theorem paddedCode_body_mem (A : ZFSet.{u}) (hA : Transitive A)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (ha : (paddedCode v β).toZFSet ∈ A) : (vectorCode v).toZFSet ∈ A :=
  hA _ ha _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr (right_lt_pairCode _ _))

theorem padded_height_domain (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hβ : realSeedOffset ≤ β) :
    let a := paddedCode v β
    a.toZFSet ∈ level (groundReals M) (heightDomainIndex a) ∧
      (∀ i, (v i).toZFSet ∈ level (groundReals M) (heightDomainIndex a)) ∧
      β.toZFSet ∈ level (groundReals M) (heightDomainIndex a) ∧
      (vectorCode v).toZFSet ∈ level (groundReals M) (heightDomainIndex a) ∧
      paddedDecode n a = v ∧
      (∀ e : ℕ → ZFSet.{u}, e 0 ∈ level (groundReals M) (heightDomainIndex a) →
        (largestOrdinalSentence.Sat (level (groundReals M) (heightDomainIndex a) : Set ZFSet) e ↔
          e 0 = a.toZFSet)) := by
  have hm := largestOrdinal_ground_domain M hM hT (paddedCode v β)
    (hβ.trans (padding_lt_paddedCode v β).le)
  exact ⟨hm.1,paddedCode_entries_mem _ (level_transitive _ _) v β hm.1,
    paddedCode_padding_mem _ (level_transitive _ _) v β hm.1,
    paddedCode_body_mem _ (level_transitive _ _) v β hm.1,paddedDecode_paddedCode v β,hm.2⟩

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalSumSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse
universe u

theorem taggedClause_eval (a b t v x y : ℕ) (cmp : Bool) (e : ℕ → ZFSet.{u}) :
    (taggedClause a b t v x y cmp).Eval e ↔
      ∃ s ∈ e a, ∃ q ∈ e b, e x = ZFSet.pair (e t) s ∧
        e y = ZFSet.pair (e v) q ∧ (if cmp then s ∈ q else True) := by
  cases cmp <;> simp [taggedClause, Formula.Eval]

theorem sumLessFormula_eval (a b z o x y : ℕ) (e : ℕ → ZFSet.{u})
    (hz : e z = ∅) (ho : e o = {∅}) :
    (sumLessFormula a b z o x y).Eval e ↔ SumLess (e a) (e b) (e x) (e y) := by
  simp [sumLessFormula, taggedClause_eval, hz, ho, SumLess, leftNode, rightNode]

theorem sumRelationFormula_eval (a b p : ZFSet.{u}) :
    sumRelationFormula.Eval
      (cons p (cons (sumDomain a b) (cons a (cons b (cons ∅ (fun _ => {∅})))))) ↔
      ∃ x ∈ sumDomain a b, ∃ y ∈ sumDomain a b,
        p = ZFSet.pair x y ∧ SumLess a b x y := by
  simp only [sumRelationFormula, Formula.Eval, Formula.eval_orderedPair,
    cons_zero, cons_succ]
  apply exists_congr; intro x
  apply and_congr_right; intro _
  apply exists_congr; intro y
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  exact sumLessFormula_eval _ _ _ _ _ _ _ rfl rfl

theorem sumDomain_mem (M a b : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (h0 : (∅ : ZFSet.{u}) ∈ M) (ha : a ∈ M) (hb : b ∈ M) :
    sumDomain a b ∈ M := by
  have h1 := singleton_mem M hM hP h0
  exact binary_union_mem M hM hP hU
    (product_mem M hM hP hU hPow hS h1 ha)
    (product_mem M hM hP hU hPow hS (singleton_mem M hM hP h1) hb)

theorem sumRelation_mem (M a b : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (h0 : (∅ : ZFSet.{u}) ∈ M) (ha : a ∈ M) (hb : b ∈ M) :
    sumRelation a b ∈ M := by
  have hd := sumDomain_mem M a b hM hP hU hPow hS h0 ha hb
  have h1 := singleton_mem M hM hP h0
  let e := cons (sumDomain a b) (cons a (cons b (cons ∅ (fun _ => {∅}))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|i; exact hd
    rcases i with _|i; exact ha
    rcases i with _|i; exact hb
    rcases i with _|i; exact h0
    exact h1
  have hs := sep_mem M hM hS sumRelationFormula e he
    (product_mem M hM hP hU hPow hS hd hd)
  have eq : ZFSet.sep (fun p => sumRelationFormula.Eval (cons p e))
      (ZFSet.prod (sumDomain a b) (sumDomain a b)) = sumRelation a b := by
    apply ZFSet.ext; intro p
    simp only [sumRelation, ZFSet.mem_sep, e, sumRelationFormula_eval]
  exact eq ▸ hs

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalSumPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse
universe u

attribute [local simp] leftNode_inj rightNode_inj leftNode_ne_rightNode rightNode_ne_leftNode

theorem sumValue_mem (a b : Ordinal.{u}) (x : ZFSet.{u})
    (hx : x ∈ sumDomain a.toZFSet b.toZFSet) : sumValue a x ∈ (a+b).toZFSet := by
  rcases (mem_sumDomain _ _ _).mp hx with ⟨s,hs,rfl⟩|⟨s,hs,rfl⟩
  · rw [sumValue_left]
    exact Ordinal.toZFSet_monotone le_self_add hs
  · obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hs
    rw [sumValue_right,Ordinal.rank_toZFSet,Ordinal.toZFSet_mem_toZFSet_iff]
    exact (add_lt_add_iff_left a).mpr hc

theorem sumValue_surjective (a b : Ordinal.{u}) (z : ZFSet.{u})
    (hz : z ∈ (a+b).toZFSet) :
    ∃ x ∈ sumDomain a.toZFSet b.toZFSet, sumValue a x = z := by
  obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
  by_cases h : c < a
  · exact ⟨leftNode c.toZFSet,(mem_sumDomain _ _ _).mpr
      (Or.inl ⟨c.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr h,rfl⟩),sumValue_left _ _⟩
  · have hle := le_of_not_gt h
    have hb : c-a < b := (Ordinal.sub_lt_of_le hle).mpr hc
    refine ⟨rightNode (c-a).toZFSet,(mem_sumDomain _ _ _).mpr
      (Or.inr ⟨(c-a).toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hb,rfl⟩),?_⟩
    rw [sumValue_right,Ordinal.rank_toZFSet,Ordinal.add_sub_cancel_of_le hle]

theorem sumRelation_transitive (a b : Ordinal.{u}) :
    TransitiveOn (sumDomain a.toZFSet b.toZFSet) (sumRelation a.toZFSet b.toZFSet) := by
  intro x hx y hy z hz hxy hyz
  apply (sumValue_relation a b x hx z hz).mpr
  exact ((ZFSet.isOrdinal_toZFSet (a+b)).mem (sumValue_mem a b z hz)).subset_of_mem
    ((sumValue_relation a b y hy z hz).mp hyz) ((sumValue_relation a b x hx y hy).mp hxy)

theorem sum_orderType (a b : Ordinal.{u}) :
    orderType (sumDomain a.toZFSet b.toZFSet) (sumRelation a.toZFSet b.toZFSet)
      (sumRelation_wellFounded a b) = a+b :=
  orderType_of_ordinal_presentation _ _ _ _ (sumValue a)
    (sumValue_mem a b) (sumValue_surjective a b) (sumValue_relation a b)

theorem ordinal_add_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a b : Ordinal.{u}) (ha : a.toZFSet ∈ M) (hb : b.toZFSet ∈ M) :
    (a+b).toZFSet ∈ M ∧ ∃ f ∈ M,
      Presents (sumDomain a.toZFSet b.toZFSet) f (sumValue a) ∧
      OrderTypeCertificate (sumDomain a.toZFSet b.toZFSet)
        (sumRelation a.toZFSet b.toZFSet) (a+b).toZFSet f := by
  have h0 := hM _ (omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity) _ ZFSet.omega_zero
  exact ordinal_internal_of_presentation M _ _ _ hM hT
    (sumDomain_mem M _ _ hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded h0 ha hb)
    (sumRelation_mem M _ _ hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded h0 ha hb)
    (sumRelation_on _ _) (sumValue a) (sumValue_mem a b)
    (sumValue_surjective a b) (sumValue_relation a b)

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalSumSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel
universe u

theorem nodeMember_eval (a t x : ℕ) (e : ℕ → ZFSet.{u}) :
    (nodeMember a t x).Eval e ↔ ∃ s ∈ e a, e x = ZFSet.pair (e t) s := by
  simp [nodeMember,Formula.Eval]

theorem sumDomainMatrix_eval (d a b z o : ℕ) (e : ℕ → ZFSet.{u})
    (hz : e z = ∅) (ho : e o = {∅}) :
    (sumDomainMatrix d a b z o).Eval e ↔ e d = sumDomain (e a) (e b) := by
  simp only [sumDomainMatrix,Formula.Eval,Formula.eval_allMem,Formula.eval_disj,
    nodeMember_eval,Formula.eval_orderedPair,cons_zero,cons_succ,hz,ho]
  change ((∀ x ∈ e d, (∃ s ∈ e a, x = leftNode s) ∨ (∃ s ∈ e b, x = rightNode s)) ∧
    (∀ s ∈ e a, ∃ x ∈ e d, x = leftNode s) ∧
    (∀ s ∈ e b, ∃ x ∈ e d, x = rightNode s)) ↔ _
  constructor
  · rintro ⟨hd,ha,hb⟩
    apply ZFSet.ext; intro x
    rw [mem_sumDomain]
    refine ⟨hd x,?_⟩
    rintro (⟨s,hs,rfl⟩|⟨s,hs,rfl⟩)
    · obtain ⟨x,hx,rfl⟩ := ha s hs; exact hx
    · obtain ⟨x,hx,rfl⟩ := hb s hs; exact hx
  · intro heq
    rw [heq]
    exact ⟨fun x hx => (mem_sumDomain _ _ _).mp hx,
      fun s hs => ⟨leftNode s,(mem_sumDomain _ _ _).mpr (Or.inl ⟨s,hs,rfl⟩),rfl⟩,
      fun s hs => ⟨rightNode s,(mem_sumDomain _ _ _).mpr (Or.inr ⟨s,hs,rfl⟩),rfl⟩⟩

theorem sumRelationMatrix_eval (r d a b z o : ℕ) (e : ℕ → ZFSet.{u})
    (hz : e z = ∅) (ho : e o = {∅}) (hd : e d = sumDomain (e a) (e b)) :
    (sumRelationMatrix r d a b z o).Eval e ↔ e r = sumRelation (e a) (e b) := by
  simp only [sumRelationMatrix,Formula.Eval,Formula.eval_allMem,Formula.eval_orderedPair,
    Formula.eval_imp,Formula.eval_pairMem,cons_zero,cons_succ]
  have h3 (x y p : ZFSet.{u}) := sumLessFormula_eval (a+3) (b+3) (z+3) (o+3) 1 0
    (cons y (cons x (cons p e))) (by simpa using hz) (by simpa using ho)
  have h2 (x y : ZFSet.{u}) := sumLessFormula_eval (a+2) (b+2) (z+2) (o+2) 1 0
    (cons y (cons x e)) (by simpa using hz) (by simpa using ho)
  simp only [h3,h2,cons_zero,cons_succ,hd]
  constructor
  · rintro ⟨hr,hall⟩
    apply ZFSet.ext; intro p
    constructor
    · intro hp
      obtain ⟨x,hx,y,hy,rfl,hxy⟩ := hr p hp
      exact (pair_mem_sumRelation _ _ _ _).mpr ⟨hx,hy,hxy⟩
    · intro hp
      obtain ⟨_,x,hx,y,hy,rfl,hxy⟩ := ZFSet.mem_sep.mp hp
      exact hall x hx y hy hxy
  · intro heq
    rw [heq]
    exact ⟨fun p hp => (ZFSet.mem_sep.mp hp).2,
      fun x hx y hy hxy => (pair_mem_sumRelation _ _ _ _).mpr ⟨hx,hy,hxy⟩⟩

theorem sumMatrix_eval (c a b d r f z o : ℕ) (e : ℕ → ZFSet.{u}) :
    (sumMatrix c a b d r f z o).Eval e ↔
      e z = ∅ ∧ e o = {∅} ∧ e d = sumDomain (e a) (e b) ∧
      e r = sumRelation (e a) (e b) ∧
      OrderTypeCertificate (e d) (e r) (e c) (e f) := by
  have hempty : (Formula.allMem z (.neg (.equal 0 0))).Eval e ↔ e z = ∅ := by
    simp only [Formula.eval_allMem,Formula.Eval,not_true_eq_false,imp_false]
    exact ⟨fun h => ZFSet.ext (fun x => by simp [h x]),fun h x => h ▸ ZFSet.notMem_empty x⟩
  simp only [sumMatrix,Formula.Eval,hempty,Formula.eval_singleton]
  apply and_congr_right; intro hz
  rw [hz]
  apply and_congr_right; intro ho
  rw [sumDomainMatrix_eval d a b z o e hz ho]
  apply and_congr_right; intro hd
  rw [sumRelationMatrix_eval r d a b z o e hz ho hd,orderTypeMatrix_eval]

theorem sumSentence_semantics (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) :
    sumSentence.Sat (A : Set ZFSet) e ↔
      ∃ d ∈ A, ∃ r ∈ A, ∃ f ∈ A, ∃ z ∈ A, ∃ o ∈ A,
        z = ∅ ∧ o = {∅} ∧ d = sumDomain (e 1) (e 2) ∧
        r = sumRelation (e 1) (e 2) ∧ OrderTypeCertificate d r (e 0) f := by
  change (∃ d ∈ A, ∃ r ∈ A, ∃ f ∈ A, ∃ z ∈ A, ∃ o ∈ A,
    (fromBounded _).Sat _ (cons o (cons z (cons f (cons r (cons d e)))))) ↔ _
  apply exists_congr; intro d
  apply and_congr_right; intro hd
  apply exists_congr; intro r
  apply and_congr_right; intro hr
  apply exists_congr; intro f
  apply and_congr_right; intro hf
  apply exists_congr; intro z
  apply and_congr_right; intro hz
  apply exists_congr; intro o
  apply and_congr_right; intro ho
  rw [bounded_sat,Formula.absolute _ A hA _ (by
    intro i; rcases i with _|_|_|_|_|i <;> simp [cons,he,hd,hr,hf,hz,ho]),sumMatrix_eval]
  rfl

theorem sumSentence_sound (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) (a b : Ordinal.{u})
    (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet) :
    sumSentence.Sat (A : Set ZFSet) e → e 0 = (a+b).toZFSet := by
  intro h
  obtain ⟨d,_,r,_,f,_,z,_,o,_,_,_,hd,hr,hc⟩ := (sumSentence_semantics A hA e he).mp h
  rw [ha,hb] at hd hr
  rw [hd,hr] at hc
  exact (hc.exact (sumRelation_wellFounded a b) (sumRelation_transitive a b)).trans
    (congrArg Ordinal.toZFSet (sum_orderType a b))

theorem sumSentence_spec_of_certificate (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) (a b : Ordinal.{u})
    (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet)
    (h0 : (∅ : ZFSet.{u}) ∈ A) (h1 : ({∅} : ZFSet.{u}) ∈ A)
    (hd : sumDomain a.toZFSet b.toZFSet ∈ A) (hr : sumRelation a.toZFSet b.toZFSet ∈ A)
    (hf : ∃ f ∈ A, OrderTypeCertificate (sumDomain a.toZFSet b.toZFSet)
      (sumRelation a.toZFSet b.toZFSet) (a+b).toZFSet f) :
    sumSentence.Sat (A : Set ZFSet) e ↔ e 0 = (a+b).toZFSet := by
  refine ⟨sumSentence_sound A hA e he a b ha hb,?_⟩
  intro hc
  obtain ⟨f,hf,hcert⟩ := hf
  apply (sumSentence_semantics A hA e he).mpr
  exact ⟨_,hd,_,hr,f,hf,∅,h0,{∅},h1,rfl,rfl,by rw [ha,hb],by rw [ha,hb],hc ▸ hcert⟩

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalSumClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel
universe u

theorem ordinal_mul_two_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) : (a*2).toZFSet ∈ M := by
  rw [Ordinal.mul_two]
  exact (ordinal_add_internal M hM hT a a ha ha).1

theorem doubleSentence_sound (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) (a : Ordinal.{u}) (ha : e 1 = a.toZFSet) :
    doubleSentence.Sat (A : Set ZFSet) e → e 0 = (a*2).toZFSet := by
  rw [doubleSentence,SentenceForm.sat_rename,Ordinal.mul_two]
  exact sumSentence_sound A hA _ (fun i => he _) a a ha ha

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalOrdinalCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory OrdinalArithmetic RelativeConstructible
universe u

theorem pairCode_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (x y : Ordinal.{u}) (hx : x.toZFSet ∈ M) (hy : y.toZFSet ∈ M) :
    (pairCode x y).toZFSet ∈ M := by
  unfold pairCode
  split
  · exact (ordinal_add_internal M hM hT _ _
      (ordinal_omega_opow_internal M hM hT _ (internal_ordinal_succ M hM hT x hx))
      (ordinal_omega_opow_internal M hM hT y hy)).1
  · exact (ordinal_add_internal M hM hT _ _
      (ordinal_mul_two_internal M hM hT _
        (ordinal_omega_opow_internal M hM hT _ (internal_ordinal_succ M hM hT y hy)))
      (ordinal_omega_opow_internal M hM hT x hx)).1

theorem vectorCode_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (hv : ∀ i, (v i).toZFSet ∈ M) :
    (vectorCode v).toZFSet ∈ M := by
  induction n with
  | zero =>
    simpa only [vectorCode,zero_add] using internal_ordinal_succ M hM hT 0 (internal_ordinal_zero M hM hT)
  | succ n ih =>
    exact pairCode_internal M hM hT _ _ (hv 0) (ih _ (fun i => hv i.succ))

theorem paddedCode_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hv : ∀ i, (v i).toZFSet ∈ M) (hβ : β.toZFSet ∈ M) :
    (paddedCode v β).toZFSet ∈ M :=
  pairCode_internal M hM hT _ _ hβ (vectorCode_internal M hM hT v hv)

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalCodeOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

theorem codePowerAt_sound (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (y x : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (codePowerAt y x).Sat (M : Set ZFSet) e →
      (e x).IsOrdinal ∧ e y = (Ordinal.omega0 ^ (e x).rank).toZFSet := by
  rw [codePowerAt,SentenceForm.sat_rename]
  exact omegaPowerSentence_sound M hM hω _ (fun i => he _)

theorem codeSumAt_sound (M : ZFSet.{u}) (hM : Transitive M)
    (c a b : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (α β : Ordinal.{u}) (ha : e a = α.toZFSet) (hb : e b = β.toZFSet) :
    (codeSumAt c a b).Sat (M : Set ZFSet) e → e c = (α+β).toZFSet := by
  rw [codeSumAt,SentenceForm.sat_rename]
  exact sumSentence_sound M hM _ (fun i => he _) α β ha hb

theorem codeScaleAt_sound (M : ZFSet.{u}) (hM : Transitive M)
    (twice : Bool) (y x : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (a : Ordinal.{u}) (ha : e x = a.toZFSet) :
    (codeScaleAt twice y x).Sat (M : Set ZFSet) e → e y = (codeScale twice a).toZFSet := by
  cases twice with
  | false => exact fun h => h.trans ha
  | true =>
    rw [codeScaleAt,ite_eq_left rfl,SentenceForm.sat_rename]
    exact doubleSentence_sound M hM _ (fun i => he _) a ha

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalCodeBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

theorem code_rename_bound (p : SentenceForm) (r : ℕ → ℕ) (n : ℕ)
    (h : ∀ i, i < p.bound → r i < n) : (p.rename r).bound ≤ n := by
  induction p generalizing r n with
  | equal i j =>
    have hi := h i (by simp [SentenceForm.bound])
    have hj := h j (by simp [SentenceForm.bound])
    simp only [SentenceForm.rename,SentenceForm.bound]; omega
  | member i j =>
    have hi := h i (by simp [SentenceForm.bound])
    have hj := h j (by simp [SentenceForm.bound])
    simp only [SentenceForm.rename,SentenceForm.bound]; omega
  | conj p q ihp ihq =>
    exact max_le (ihp r n (fun i hi => h i (by change i < max p.bound q.bound; omega)))
      (ihq r n (fun i hi => h i (by change i < max p.bound q.bound; omega)))
  | neg p ih => exact ih r n h
  | ex p ih =>
    have ht := ih (fun i => match i with | 0 => 0 | j+1 => r j+1) (n+1) (by
      intro i hi
      cases i with
      | zero => simp
      | succ i => have hh := h i (by change i < p.bound-1; omega); simp; omega)
    exact (Nat.sub_le_sub_right ht 1).trans (by omega)

theorem codeBranchBody_sound (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (twice : Bool) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (a b : Ordinal.{u}) (ha : e 5 = a.toZFSet) (hb : e 6 = b.toZFSet) :
    (codeBranchBody twice).Sat (M : Set ZFSet) e → e 4 = (codeBranchValue twice a b).toZFSet := by
  intro h
  obtain ⟨hk,hu,hv,ht,hc⟩ := h
  have hks : e 3 = (a+1).toZFSet := by
    rw [bounded_sat,Formula.absolute _ M hM e he,Formula.eval_successor,ha] at hk
    simpa only [Ordinal.toZFSet_add_one] using hk
  have hus := (codePowerAt_sound M hM hω 2 3 e he hu).2
  rw [hks,Ordinal.rank_toZFSet] at hus
  have hvs := (codePowerAt_sound M hM hω 1 6 e he hv).2
  rw [hb,Ordinal.rank_toZFSet] at hvs
  have hts := codeScaleAt_sound M hM twice 0 2 e he _ hus ht
  exact codeSumAt_sound M hM 4 0 1 e he _ _ hts hvs hc

theorem codeBranchSentence_sound (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (twice : Bool) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (a b : Ordinal.{u}) (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet) :
    (codeBranchSentence twice).Sat (M : Set ZFSet) e → e 0 = (codeBranchValue twice a b).toZFSet := by
  rintro ⟨k,hk,u,hu,v,hv,t,ht,h⟩
  exact codeBranchBody_sound M hM hω twice _ (by
    intro i; rcases i with _|_|_|_|i
    exact ht; exact hv; exact hu; exact hk; exact he i) a b ha hb h

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalPairSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

theorem pairCodeSentence_semantics (M : ZFSet.{u}) (hM : Transitive M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    pairCodeSentence.Sat (M : Set ZFSet) e ↔
      ((e 1).IsOrdinal ∧ (e 2).IsOrdinal) ∧
      ((e 2 ⊆ e 1 ∧ (codeBranchSentence false).Sat (M : Set ZFSet) e) ∨
        (¬ e 2 ⊆ e 1) ∧ (codeBranchSentence true).Sat (M : Set ZFSet)
          (fun i => e (if i = 0 then 0 else if i = 1 then 2 else 1))) := by
  change ((fromBounded _).Sat _ e ∧ (SentenceForm.disj _ _).Sat _ e) ↔ _
  rw [bounded_sat,Formula.absolute _ M hM e he,Formula.Eval,eval_ordinalFormula,eval_ordinalFormula,
    SentenceForm.sat_disj]
  simp only [SentenceForm.Sat,SentenceForm.sat_rename,bounded_sat,
    Formula.absolute _ M hM e he,Formula.eval_subset]

theorem pairCodeSentence_sound (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    pairCodeSentence.Sat (M : Set ZFSet) e →
      (e 1).IsOrdinal ∧ (e 2).IsOrdinal ∧ e 0 = (pairCode (e 1).rank (e 2).rank).toZFSet := by
  rw [pairCodeSentence_semantics M hM e he]
  rintro ⟨⟨ha,hb⟩,h⟩
  refine ⟨ha,hb,?_⟩
  have hsub : e 2 ⊆ e 1 ↔ (e 2).rank ≤ (e 1).rank := by
    rw [← ha.toZFSet_rank_eq,← hb.toZFSet_rank_eq,Ordinal.toZFSet_subset_toZFSet_iff]
    simp only [Ordinal.rank_toZFSet]
  rcases h with ⟨hle,hc⟩|⟨hnle,hc⟩
  · have hv := codeBranchSentence_sound M hM hω false e he _ _
      ha.toZFSet_rank_eq.symm hb.toZFSet_rank_eq.symm hc
    simpa only [pairCode,ite_eq_left (hsub.mp hle),codeBranchValue,codeScale,Bool.false_eq_true,↓reduceIte] using hv
  · have hv := codeBranchSentence_sound M hM hω true
      (fun i => e (if i = 0 then 0 else if i = 1 then 2 else 1)) (fun i => he _) _ _
      hb.toZFSet_rank_eq.symm ha.toZFSet_rank_eq.symm hc
    simpa only [pairCode,ite_eq_right (fun h => hnle (hsub.mpr h)),codeBranchValue,codeScale,↓reduceIte] using hv

theorem pairCodeSentence_recovers (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (a b : Ordinal.{u}) (hc : e 0 = (pairCode a b).toZFSet)
    (hp : pairCodeSentence.Sat (M : Set ZFSet) e) : e 1 = a.toZFSet ∧ e 2 = b.toZFSet := by
  obtain ⟨ha,hb,h⟩ := pairCodeSentence_sound M hM hω e he hp
  rw [hc] at h
  have h := congrArg ZFSet.rank h
  simp only [Ordinal.rank_toZFSet] at h
  obtain ⟨h1,h2⟩ := (pairCode_inj a b (e 1).rank (e 2).rank).mp h
  exact ⟨by rw [h1,ha.toZFSet_rank_eq],by rw [h2,hb.toZFSet_rank_eq]⟩

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalVectorSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

theorem vectorCodeSentence_bound (n : ℕ) : (vectorCodeSentence n).bound ≤ n+1 := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have hp := code_rename_bound pairCodeSentence
      (fun i => if i = 0 then 1 else if i = 1 then 2 else 0) 3 (by
        intro i _; split <;> (try split) <;> omega)
    have ht := code_rename_bound (vectorCodeSentence n) vectorTailSlots (n+3) (by
      intro i hi
      cases i with
      | zero => simp [vectorTailSlots]
      | succ i => change i+3 < n+3; omega)
    change max _ _ - 1 ≤ n+1+1
    omega

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalVectorRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

theorem vectorCodeSentence_recovers (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (n : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (v : Fin n → Ordinal.{u}) (hc : e 0 = (vectorCode v).toZFSet)
    (hp : (vectorCodeSentence n).Sat (M : Set ZFSet) e) :
    ∀ i, e (i.val+1) = (v i).toZFSet := by
  induction n generalizing e with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨t,ht,hpair,hrest⟩ := hp
    rw [SentenceForm.sat_rename] at hpair hrest
    have hrec := pairCodeSentence_recovers M hM hω
      (fun i => cons t e (if i = 0 then 1 else if i = 1 then 2 else 0)) (fun i => by
        split; exact he 0
        split; exact he 1
        exact ht) (v 0) (vectorCode (fun i => v i.succ)) hc hpair
    have hh : e 1 = (v 0).toZFSet := hrec.1
    have htcode : t = (vectorCode (fun i => v i.succ)).toZFSet := hrec.2
    have htail := ih (fun i => cons t e (vectorTailSlots i)) (fun i => by
      cases i; exact ht; exact he _) (fun i => v i.succ) htcode hrest
    intro i
    exact Fin.cases hh (fun j => htail j) i

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalPaddingSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

theorem paddedCodeSentence_bound (n : ℕ) : (paddedCodeSentence n).bound ≤ n+1 := by
  have hp := code_rename_bound pairCodeSentence
    (fun i => if i = 0 then 2 else if i = 1 then 1 else 0) 3 (by
      intro i _; split <;> (try split) <;> omega)
  have ht := code_rename_bound (vectorCodeSentence n) vectorTailSlots (n+3) (by
    intro i hi
    have hb := vectorCodeSentence_bound n
    cases i with
    | zero => simp [vectorTailSlots]
    | succ i => change i+3 < n+3; omega)
  change max _ _ - 1 - 1 ≤ n+1
  omega

theorem paddedCodeSentence_recovers (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (n : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (v : Fin n → Ordinal.{u}) (β : Ordinal.{u}) (hc : e 0 = (paddedCode v β).toZFSet)
    (hp : (paddedCodeSentence n).Sat (M : Set ZFSet) e) :
    ∀ i, e (i.val+1) = (v i).toZFSet := by
  obtain ⟨b,hb,t,ht,hpair,hvec⟩ := hp
  rw [SentenceForm.sat_rename] at hpair hvec
  have hrec := pairCodeSentence_recovers M hM hω
    (fun i => cons t (cons b e) (if i = 0 then 2 else if i = 1 then 1 else 0)) (fun i => by
      split; exact he 0
      split; exact hb
      exact ht) β (vectorCode v) hc hpair
  have htcode : t = (vectorCode v).toZFSet := hrec.2
  exact vectorCodeSentence_recovers M hM hω n
    (fun i => cons t (cons b e) (vectorTailSlots i))
    (fun i => by cases i; exact ht; exact he _) v htcode hvec

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalEntryBinding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

theorem code_prepend_congr (w v : ℕ → ZFSet.{u}) (n : ℕ) (e : ℕ → ZFSet.{u})
    (h : ∀ i, i < n → w i = v i) : prependValues w n e = prependValues v n e := by
  funext i
  by_cases hi : i < n
  · rw [prependValues_lt w n e i hi,prependValues_lt v n e i hi,h i hi]
  · have heq : i = n+(i-n) := by omega
    rw [heq,prependValues_tail,prependValues_tail]

theorem codeBindEntries_sat (M : ZFSet.{u}) (n : ℕ) (p : SentenceForm)
    (e : ℕ → ZFSet.{u}) :
    (codeBindEntries n p).Sat (M : Set ZFSet) e ↔
      ∃ w : ℕ → ZFSet.{u}, (∀ i, i < n → w i ∈ M) ∧
        p.Sat (M : Set ZFSet) (prependValues w n e) := by
  induction n generalizing e with
  | zero => exact ⟨fun h => ⟨e,by intro i hi; omega,h⟩,fun ⟨_,_,h⟩ => h⟩
  | succ n ih =>
    change (∃ x ∈ M, (codeBindEntries n p).Sat _ (cons x e)) ↔ _
    constructor
    · rintro ⟨x,hx,hp⟩
      obtain ⟨w,hw,hp⟩ := (ih (cons x e)).mp hp
      let v : ℕ → ZFSet.{u} := fun i => if i < n then w i else x
      have hn : v n = x := by simp [v]
      refine ⟨v,?_,?_⟩
      · intro i hi; dsimp [v]; split; exact hw i ‹i < n›; exact hx
      · change p.Sat _ (prependValues v n (cons (v n) e))
        rw [hn,code_prepend_congr v w n (cons x e) (by intro i hi; simp [v,hi])]
        exact hp
    · rintro ⟨w,hw,hp⟩
      exact ⟨w n,hw n (by omega),(ih _).mpr ⟨w,fun i hi => hw i (by omega),hp⟩⟩

theorem entryCodeSlots_env (n : ℕ) (e w : ℕ → ZFSet.{u}) :
    ∀ i, i < (paddedCodeSentence n).bound →
      prependValues w n e (entryCodeSlots n i) = cons (e 1) w i := by
  intro i hi
  have hb := paddedCodeSentence_bound n
  cases i with
  | zero => exact prependValues_tail w n e 1
  | succ i =>
    simp only [entryCodeSlots,ite_eq_left (show i < n by omega),cons_succ]
    exact prependValues_lt w n e i (by omega)

theorem paddedEntrySentence_semantics (M : ZFSet.{u}) (n : ℕ) (k : Fin n)
    (e : ℕ → ZFSet.{u}) :
    (paddedEntrySentence n k).Sat (M : Set ZFSet) e ↔
      ∃ w : ℕ → ZFSet.{u}, (∀ i, i < n → w i ∈ M) ∧ e 0 = w k.val ∧
        (paddedCodeSentence n).Sat (M : Set ZFSet) (cons (e 1) w) := by
  rw [paddedEntrySentence,codeBindEntries_sat]
  apply exists_congr; intro w
  apply and_congr_right; intro _
  change (prependValues w n e n = prependValues w n e k.val ∧ _) ↔ _
  rw [show prependValues w n e n = e 0 from prependValues_tail w n e 0,prependValues_lt w n e k.val k.isLt,
    SentenceForm.sat_rename]
  exact and_congr Iff.rfl ((paddedCodeSentence n).finite_support _ _ _ (entryCodeSlots_env n e w))

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalEntryDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

theorem paddedEntrySentence_sound (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (n : ℕ) (k : Fin n) (e : ℕ → ZFSet.{u})
    (he : ∀ i, e i ∈ M) (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hc : e 1 = (paddedCode v β).toZFSet)
    (hp : (paddedEntrySentence n k).Sat (M : Set ZFSet) e) : e 0 = (v k).toZFSet := by
  obtain ⟨w,hw,hy,hp⟩ := (paddedEntrySentence_semantics M n k e).mp hp
  let w' : ℕ → ZFSet.{u} := fun i => if i < n then w i else e 0
  have hw' (i : ℕ) : w' i ∈ M := by
    dsimp [w']; split; exact hw i ‹i < n›; exact he 0
  have hp' : (paddedCodeSentence n).Sat (M : Set ZFSet) (cons (e 1) w') := by
    apply ((paddedCodeSentence n).finite_support _ (cons (e 1) w) (cons (e 1) w') ?_).mp hp
    intro i hi
    have hb := paddedCodeSentence_bound n
    cases i with
    | zero => rfl
    | succ i => simp [w',show i < n by omega]
  have hv := paddedCodeSentence_recovers M hM hω n (cons (e 1) w')
    (fun i => by cases i; exact he 1; exact hw' _) v β hc hp'
  have hk := hv k
  simpa only [cons_succ,w',ite_eq_left k.isLt,← hy] using hk

end TuringRigidity.OrdinalCoding

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

theorem padded_entry_height_sound (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (n : ℕ) (k : Fin n) (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hβ : realSeedOffset ≤ β) (z : ZFSet.{u})
    (hz : z ∈ level (groundReals M) (heightDomainIndex (paddedCode v β))) :
    (paddedEntrySentence n k).Sat
      (level (groundReals M) (heightDomainIndex (paddedCode v β)) : Set ZFSet)
      (cons z (fun _ => (paddedCode v β).toZFSet)) → z = (v k).toZFSet := by
  have hc := (padded_height_domain M hM hT v β hβ).1
  exact paddedEntrySentence_sound _ (level_transitive _ _) (ground_level_omega_mem M hM hT _)
    n k _ (fun i => by cases i; exact hz; exact hc) v β rfl

theorem largestPaddedEntrySentence_bound (n : ℕ) (k : Fin n) :
    (largestPaddedEntrySentence n k).bound ≤ 1 := by
  have hb := code_rename_bound (paddedEntrySentence n k)
    (fun i => if i = 0 then 1 else 0) 2 (by intro i _; split <;> omega)
  rw [largestPaddedEntrySentence,bindLargestOrdinal_bound]
  omega

theorem largestPaddedEntrySentence_sound (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (n : ℕ) (k : Fin n) (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hβ : realSeedOffset ≤ β) (e : ℕ → ZFSet.{u})
    (he : e 0 ∈ level (groundReals M) (heightDomainIndex (paddedCode v β))) :
    (largestPaddedEntrySentence n k).Sat
      (level (groundReals M) (heightDomainIndex (paddedCode v β)) : Set ZFSet) e →
        e 0 = (v k).toZFSet := by
  rw [largestPaddedEntrySentence,bindLargestOrdinal_ground_domain _ M hM hT _
    (hβ.trans (padding_lt_paddedCode v β).le),SentenceForm.sat_rename]
  have heq : (fun i => cons (paddedCode v β).toZFSet e (if i = 0 then 1 else 0)) =
      cons (e 0) (fun _ => (paddedCode v β).toZFSet) := by
    funext i; cases i <;> rfl
  rw [heq]
  exact padded_entry_height_sound M hM hT n k v β hβ (e 0) he

end TuringRigidity.OrdinalCoding

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_SumCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions
universe u

theorem sumSentence_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (a b : Ordinal.{u}) (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet)
    (hc : SumCertificates M a b) (hy : e 0 = (a+b).toZFSet) :
    sumSentence.Sat (M : Set ZFSet) e := by
  have h1 : ({∅} : ZFSet.{u}) ∈ M := by
    have h := hM _ hω _ ((mem_omega _).mpr ⟨1,rfl⟩)
    simpa [natSet] using h
  exact (sumSentence_spec_of_certificate M hM e he a b ha hb
    (hM _ hω _ ZFSet.omega_zero) h1 hc.1 hc.2.1 hc.2.2).mpr hy

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_CodeOperationCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

theorem codePowerAt_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (y x : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (hc : OmegaPowerCertificates M (e x)) (hy : e y = (Ordinal.omega0 ^ (e x).rank).toZFSet) :
    (codePowerAt y x).Sat (M : Set ZFSet) e := by
  rw [codePowerAt,SentenceForm.sat_rename]
  exact omegaPowerSentence_of_certificates M hM hω _ (fun i => he _) hc hy

theorem codeSumAt_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (c a b : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (α β : Ordinal.{u}) (ha : e a = α.toZFSet) (hb : e b = β.toZFSet)
    (hc : SumCertificates M α β) (hy : e c = (α+β).toZFSet) :
    (codeSumAt c a b).Sat (M : Set ZFSet) e := by
  rw [codeSumAt,SentenceForm.sat_rename]
  exact sumSentence_of_certificates M hM hω _ (fun i => he _) α β ha hb hc hy


theorem codeScaleAt_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (twice : Bool) (y x : ℕ)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (a : Ordinal.{u}) (ha : e x = a.toZFSet)
    (hc : twice = true → SumCertificates M a a) (hy : e y = (codeScale twice a).toZFSet) :
    (codeScaleAt twice y x).Sat (M : Set ZFSet) e := by
  cases twice with
  | false => exact hy.trans ha.symm
  | true =>
    change (doubleSentence.rename (fun i => if i = 0 then y else x)).Sat (M : Set ZFSet) e
    rw [SentenceForm.sat_rename]
    rw [doubleSentence,SentenceForm.sat_rename]
    exact sumSentence_of_certificates M hM hω
      (fun i => e (if (if i = 0 then 0 else 1) = 0 then y else x))
      (fun i => he _) a a ha ha (hc rfl)
      (by simpa only [codeScale,↓reduceIte,Ordinal.mul_two] using hy)

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_CodeBranchCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

theorem codeBranchSentence_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (twice : Bool) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (a b : Ordinal.{u}) (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet)
    (hcert : CodeBranchCertificates M twice a b)
    (hc : e 0 = (codeBranchValue twice a b).toZFSet) :
    (codeBranchSentence twice).Sat (M : Set ZFSet) e := by
  obtain ⟨hk,hu,hv,ht,hp,hq,hd,hs⟩ := hcert
  let k := (a+1).toZFSet
  let u := (Ordinal.omega0 ^ (a+1)).toZFSet
  let v := (Ordinal.omega0 ^ b).toZFSet
  let t := (codeScale twice (Ordinal.omega0 ^ (a+1))).toZFSet
  let E := cons t (cons v (cons u (cons k e)))
  have hE : ∀ i, E i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    exact ht; exact hv; exact hu; exact hk; exact he i
  refine ⟨k,hk,u,hu,v,hv,t,ht,?_,?_,?_,?_,?_⟩
  · rw [bounded_sat,Formula.absolute _ M hM E hE,Formula.eval_successor]
    change k = insert (e 1) (e 1)
    rw [ha,← Ordinal.toZFSet_add_one]
  · apply codePowerAt_of_certificates M hM hω 2 3 E hE hp
    simp [E,u,k]
  · apply codePowerAt_of_certificates M hM hω 1 6 E hE
    · simpa only [E,cons_succ,hb] using hq
    · simp [E,v,hb]
  · exact codeScaleAt_of_certificates M hM hω twice 0 2 E hE _ rfl hd rfl
  · exact codeSumAt_of_certificates M hM hω 4 0 1 E hE _ _ rfl rfl hs hc

theorem pairCodeSentence_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (a b : Ordinal.{u}) (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet)
    (hcert : PairCodeCertificates M a b) (hc : e 0 = (pairCode a b).toZFSet) :
    pairCodeSentence.Sat (M : Set ZFSet) e := by
  apply (pairCodeSentence_semantics M hM e he).mpr
  refine ⟨⟨ha.symm ▸ ZFSet.isOrdinal_toZFSet _,hb.symm ▸ ZFSet.isOrdinal_toZFSet _⟩,?_⟩
  have hsub : e 2 ⊆ e 1 ↔ b ≤ a := by rw [ha,hb,Ordinal.toZFSet_subset_toZFSet_iff]
  by_cases hle : b ≤ a
  · left
    refine ⟨hsub.mpr hle,codeBranchSentence_of_certificates M hM hω false e he a b ha hb ?_ ?_⟩
    · simpa only [PairCodeCertificates,ite_eq_left hle] using hcert
    · simpa only [pairCode,ite_eq_left hle,codeBranchValue,codeScale,Bool.false_eq_true,↓reduceIte] using hc
  · right
    refine ⟨fun h => hle (hsub.mp h),codeBranchSentence_of_certificates M hM hω true
      (fun i => e (if i = 0 then 0 else if i = 1 then 2 else 1)) (fun i => he _) b a hb ha ?_ ?_⟩
    · simpa only [PairCodeCertificates,ite_eq_right hle] using hcert
    · simpa only [pairCode,ite_eq_right hle,codeBranchValue,codeScale,↓reduceIte] using hc

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_VectorCodeCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

theorem vectorCodeSentence_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (n : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (v : Fin n → Ordinal.{u}) (hv : ∀ i, e (i.val+1) = (v i).toZFSet)
    (hcert : VectorCodeCertificates M v) (hc : e 0 = (vectorCode v).toZFSet) :
    (vectorCodeSentence n).Sat (M : Set ZFSet) e := by
  induction n generalizing e with
  | zero =>
    rw [vectorCodeSentence,bounded_sat,Formula.absolute _ M hM e he,ordinalOneMatrix_eval]
    exact hc
  | succ n ih =>
    obtain ⟨ht,hp,hs⟩ := hcert
    let t := (vectorCode (fun i => v i.succ)).toZFSet
    refine ⟨t,ht,?_,?_⟩
    · rw [SentenceForm.sat_rename]
      apply pairCodeSentence_of_certificates M hM hω
        (fun i => cons t e (if i = 0 then 1 else if i = 1 then 2 else 0)) (fun i => by
        split; exact he 0
        split; exact he 1
        exact ht) (v 0) (vectorCode (fun i => v i.succ)) (hv 0) rfl hp
      exact hc
    · rw [SentenceForm.sat_rename]
      exact ih _ (fun i => by cases i; exact ht; exact he _) _ (fun i => hv i.succ) hs rfl

theorem paddedCodeSentence_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (n : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (v : Fin n → Ordinal.{u}) (β : Ordinal.{u}) (hv : ∀ i, e (i.val+1) = (v i).toZFSet)
    (hcert : PaddedCodeCertificates M v β) (hc : e 0 = (paddedCode v β).toZFSet) :
    (paddedCodeSentence n).Sat (M : Set ZFSet) e := by
  obtain ⟨hb,ht,hp,hs⟩ := hcert
  refine ⟨β.toZFSet,hb,(vectorCode v).toZFSet,ht,?_,?_⟩
  · rw [SentenceForm.sat_rename]
    exact pairCodeSentence_of_certificates M hM hω _ (fun i => by
      split; exact he 0
      split; exact hb
      exact ht) β (vectorCode v) rfl rfl hp hc
  · rw [SentenceForm.sat_rename]
    exact vectorCodeSentence_of_certificates M hM hω n _
      (fun i => by cases i; exact ht; exact he _) v hv hs rfl

theorem paddedEntrySentence_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (n : ℕ) (k : Fin n) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (v : Fin n → Ordinal.{u}) (β : Ordinal.{u}) (hc : e 1 = (paddedCode v β).toZFSet)
    (hcert : PaddedCodeCertificates M v β) (hy : e 0 = (v k).toZFSet) :
    (paddedEntrySentence n k).Sat (M : Set ZFSet) e := by
  let w : ℕ → ZFSet.{u} := fun i => if hi : i < n then (v ⟨i,hi⟩).toZFSet else e 0
  have hw (i : ℕ) : w i ∈ M := by
    dsimp [w]
    split
    · exact paddedCode_entries_mem M hM v β (hc ▸ he 1) _
    · exact he 0
  apply (paddedEntrySentence_semantics M n k e).mpr
  refine ⟨w,fun i _ => hw i,?_,?_⟩
  · simpa [w,k.isLt] using hy
  · exact paddedCodeSentence_of_certificates M hM hω n (cons (e 1) w)
      (fun i => by cases i; exact he 1; exact hw _) v β
      (fun i => by simp [w,i.isLt]) hcert hc

theorem largestPaddedEntrySentence_of_certificates (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (n : ℕ) (k : Fin n) (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hβ : realSeedOffset ≤ β) (e : ℕ → ZFSet.{u})
    (he : e 0 ∈ level (groundReals M) (heightDomainIndex (paddedCode v β)))
    (hcert : PaddedCodeCertificates (level (groundReals M) (heightDomainIndex (paddedCode v β))) v β) :
    (largestPaddedEntrySentence n k).Sat
      (level (groundReals M) (heightDomainIndex (paddedCode v β)) : Set ZFSet) e ↔
        e 0 = (v k).toZFSet := by
  refine ⟨largestPaddedEntrySentence_sound M hM hT n k v β hβ e he,?_⟩
  intro hy
  rw [largestPaddedEntrySentence,bindLargestOrdinal_ground_domain _ M hM hT _
    (hβ.trans (padding_lt_paddedCode v β).le),SentenceForm.sat_rename]
  have heq : (fun i => cons (paddedCode v β).toZFSet e (if i = 0 then 1 else 0)) =
      cons (e 0) (fun _ => (paddedCode v β).toZFSet) := by
    funext i; cases i <;> rfl
  rw [heq]
  exact paddedEntrySentence_of_certificates _ (level_transitive _ _) (ground_level_omega_mem M hM hT _)
    n k _ (fun i => by cases i; exact he; exact (padded_height_domain M hM hT v β hβ).1)
    v β rfl hcert hy

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_DecodedConstructionSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel OrdinalCoding
universe u
attribute [local irreducible] Construction.ownRealsMembership SentenceForm.bound

theorem Construction.ordinalVector_internal (t : Construction.{u}) (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (hi : t.Indexed M) :
    ∀ k, (t.ordinalVector k).toZFSet ∈ M := by
  intro k
  cases ho : t.ordinalData k with
  | none => simpa only [Construction.ordinalVector,ho,Option.getD_none] using internal_ordinal_zero M hM hT
  | some o => simpa only [Construction.ordinalVector,ho,Option.getD_some] using t.ordinalData_mem M hi k o ho

theorem bindComputed_bound (n m : ℕ) (f : ℕ → SentenceForm) (p : SentenceForm)
    (hp : p.bound ≤ n+m) (hf : ∀ i < n, (f i).bound ≤ m+1) :
    (bindComputed n f p).bound ≤ m := by
  induction n generalizing m f with
  | zero => simpa only [bindComputed,zero_add] using hp
  | succ n ih =>
    have hinner := ih (m+1) (fun i => (f i).rename skipValue) (by omega) (by
      intro i hi
      apply code_rename_bound (f i) skipValue (m+2)
      intro j hj
      cases j with
      | zero => change 0 < m+2; omega
      | succ j => change j+2 < m+2; have h := hf i (by omega); omega)
    have hn := hf n (by omega)
    simpa only [bindComputed,SentenceForm.bound] using
      (show max (f n).bound (bindComputed n (fun i => (f i).rename skipValue) p).bound - 1 ≤ m by omega)

theorem Construction.decodedOrdinalBody_bound (t : Construction.{u}) (q : SentenceForm) :
    (t.decodedOrdinalBody q).bound ≤ 2 := by
  apply bindComputed_bound
  · apply code_rename_bound
    intro i _
    rcases i with _|_|i
    · change t.ownRealsMembership.bound < t.ownRealsMembership.bound+2; omega
    · change t.ownRealsMembership.bound+1 < t.ownRealsMembership.bound+2; omega
    · dsimp only [ordinalBodySlots]; split <;> omega
  · intro i _
    by_cases hi : i < t.ownRealsMembership.bound
    · rw [Construction.decodedOrdinalInput,dite_eq_left hi]
      cases t.ordinalData i with
      | none => simp only [SentenceForm.bound]; omega
      | some o => exact (largestPaddedEntrySentence_bound _ _).trans (by omega)
    · rw [Construction.decodedOrdinalInput,dite_eq_right hi]
      simp only [SentenceForm.bound]; omega

theorem Construction.decodedOrdinalBody_spec (t : Construction.{u}) (q : SentenceForm)
    (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) (P : Oracle)
    (β : Ordinal.{u}) (hoff : realSeedOffset ≤ β)
    (hcert : PaddedCodeCertificates
      (level (groundReals M) (heightDomainIndex (paddedCode t.ordinalVector β))) t.ordinalVector β)
    (he : ∀ i, t.ordinalInputs P i ∈
      level (groundReals M) (heightDomainIndex (paddedCode t.ordinalVector β)))
    (z : ZFSet.{u}) :
    (t.decodedOrdinalBody q).Sat
      (level (groundReals M) (heightDomainIndex (paddedCode t.ordinalVector β)) : Set ZFSet)
      (cons z (fun _ => realCode P)) ↔
    q.Sat (level (groundReals M) (heightDomainIndex (paddedCode t.ordinalVector β)) : Set ZFSet)
      (cons z (t.ordinalInputs P)) := by
  let n := t.ownRealsMembership.bound
  let w := fun k => t.ordinalInputs P (k+1)
  let A := level (groundReals M) (heightDomainIndex (paddedCode t.ordinalVector β))
  have hf (k : ℕ) (hk : k < n) (x : ZFSet.{u}) (hx : x ∈ A) :
      (t.decodedOrdinalInput k).Sat (A : Set ZFSet) (cons x (cons z (fun _ => realCode P))) ↔ x = w k := by
    have hk' : k < t.ownRealsMembership.bound := hk
    rw [Construction.decodedOrdinalInput,dite_eq_left hk']
    cases ho : t.ordinalData k with
    | none => simp only [SentenceForm.Sat,w,Construction.ordinalInputs,cons_succ,cons_zero,ite_eq_left hk',ho]
    | some o =>
      have h := largestPaddedEntrySentence_of_certificates M hM hT n ⟨k,hk⟩ t.ordinalVector β hoff
        (cons x (cons z (fun _ => realCode P))) hx hcert
      simpa only [cons_zero,w,Construction.ordinalInputs,cons_succ,ite_eq_left hk',
        Construction.ordinalVector,ho,Option.getD_some] using h
  rw [Construction.decodedOrdinalBody,bindComputed_spec A n t.decodedOrdinalInput _
    (cons z (fun _ => realCode P)) w (fun i _ => he (i+1)) hf,SentenceForm.sat_rename]
  have henv : (fun i => prependValues w n (cons z (fun _ => realCode P)) (ordinalBodySlots n i)) =
      cons z (t.ordinalInputs P) := by
    funext i
    rcases i with _|_|k
    · exact prependValues_tail w n _ 0
    · exact prependValues_tail w n _ 1
    · by_cases hk : k < n
      · simpa only [ordinalBodySlots,ite_eq_left hk,cons_succ,w] using prependValues_lt w n _ k hk
      · have hk' : ¬ k < t.ownRealsMembership.bound := hk
        simp only [ordinalBodySlots,ite_eq_right hk,cons_succ,Construction.ordinalInputs,ite_eq_right hk']
        exact prependValues_tail w n _ 1
  rw [henv]

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_OneRealConstructionDefinition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel OrdinalCoding
universe u
attribute [local irreducible] Construction.ownRealsMembership SentenceForm.bound

theorem Construction.cofinal_one_real_definition_oai (t : Construction.{u}) :
    ∃ p : SentenceForm, p.bound ≤ 2 ∧
      ∀ M : ZFSet.{u}, Transitive M → SourceT M →
      ∀ P : Oracle, P ∈ modelReals M → t.Certified (groundReals M) P → t.Indexed M →
      ∀ θ : Ordinal.{u}, θ.toZFSet ∈ M →
      ∃ β : Ordinal.{u}, β.toZFSet ∈ M ∧ θ < β ∧ realSeedOffset < β ∧
        (heightDomainIndex (paddedCode t.ordinalVector β)).toZFSet ∈ M ∧
        (realCode P ∈ level (groundReals M) (heightDomainIndex (paddedCode t.ordinalVector β))) ∧
        t.value (groundReals M) P = definedSubset
          (level (groundReals M) (heightDomainIndex (paddedCode t.ordinalVector β))) p
          (fun _ : Fin p.bound => realCode P) := by
  obtain ⟨q,hq⟩ := t.largest_domain_definition
  refine ⟨t.decodedOrdinalBody q,t.decodedOrdinalBody_bound q,?_⟩
  intro M hM hT P hP ht hi θ hθ
  obtain ⟨γ,hγ,hbody⟩ := hq M hM hT P hP ht hi
  have hv := t.ordinalVector_internal M hM hT hi
  obtain ⟨β,hβ,hmaxβ,hoff,hidx,hcert⟩ := cofinal_padded_code_certificates M hM hT
    t.ordinalVector hv (max θ γ) (internal_ordinal_max M hθ hγ)
  have hθβ : θ < β := (le_max_left _ _).trans_lt hmaxβ
  have hγcode : γ ≤ paddedCode t.ordinalVector β :=
    ((le_max_right _ _).trans hmaxβ.le).trans (padding_lt_paddedCode t.ordinalVector β).le
  have hcode := paddedCode_internal M hM hT t.ordinalVector β hv hβ
  obtain ⟨_,hvalue,henv,_,hmem⟩ := hbody (paddedCode t.ordinalVector β) hcode hγcode
  rw [ground_seed_offset M hM hT] at hvalue henv hmem
  refine ⟨β,hβ,hθβ,hoff,hidx,henv 0,?_⟩
  apply definedSubset_of_membership _ _ (level_transitive _ _) hvalue (t.decodedOrdinalBody q)
    (fun _ => realCode P)
  intro z hz
  exact (t.decodedOrdinalBody_spec q M hM hT P β hoff.le hcert henv z).trans (hmem z hz)

end TuringRigidity.RelativeConstructible

end OAI
end

theorem solution.{u} : type_of% @OAI.TuringRigidity.RelativeConstructible.Construction.cofinal_one_real_definition_oai.{u} := @OAI.TuringRigidity.RelativeConstructible.Construction.cofinal_one_real_definition_oai.{u}
