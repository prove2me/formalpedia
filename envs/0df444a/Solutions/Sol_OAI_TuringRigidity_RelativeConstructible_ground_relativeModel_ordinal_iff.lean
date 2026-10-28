-- Prove2me | solution 1 for OAI.TuringRigidity.RelativeConstructible.ground_relativeModel_ordinal_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:11:54.405993+00:00
-- url     : https://prove2.me/submissions/5596ca2f-f677-4947-b54f-3bf4522c007b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_definablePower_mem
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

theorem level_zero (R : ZFSet.{u}) : level R 0 = seed R := by
  rw [level,Ordinal.toZFSet_zero,stage_zero]

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel SentenceForm BoundedSetTheory TransitiveNameModel
universe u

theorem pair_mem_definablePower (A a b : ZFSet.{u}) (ha : a ∈ A) (hb : b ∈ A) :
    ({a,b} : ZFSet.{u}) ∈ definablePower A := by
  apply (mem_definablePower A _).mpr
  let v : Fin 2 → ZFSet.{u} := Fin.cases a (fun _ => b)
  refine ⟨2,disj (.equal 0 1) (.equal 0 2),v,by decide,?_,?_⟩
  · intro i; exact Fin.cases ha (fun _ => hb) i
  · apply ZFSet.ext; intro x
    simp only [ZFSet.mem_pair,mem_definedSubset,sat_disj,Sat,cons_zero,cons_succ]
    have h0 : tupleEnv v 0 = a := by simp [tupleEnv,v]
    have h1 : tupleEnv v 1 = b := by simp [tupleEnv,v]; rfl
    rw [h0,h1]
    exact ⟨fun h => ⟨h.elim (fun h => h ▸ ha) (fun h => h ▸ hb),h⟩,And.right⟩

theorem union_mem_definablePower (A a : ZFSet.{u}) (hA : Transitive A) (ha : a ∈ A) :
    ZFSet.sUnion a ∈ definablePower A := by
  apply (mem_definablePower A _).mpr
  refine ⟨1,.ex (.conj (.member 0 2) (.member 1 0)),fun _ => a,
    by decide,fun _ => ha,?_⟩
  apply ZFSet.ext; intro x
  simp only [ZFSet.mem_sUnion,mem_definedSubset,Sat,cons_zero,cons_succ]
  have h0 : tupleEnv (fun _ : Fin 1 => a) 0 = a := by simp [tupleEnv]
  rw [h0]
  constructor
  · rintro ⟨y,hy,hx⟩
    have hyA := hA a ha y hy
    exact ⟨hA y hyA x hx,y,hyA,hy,hx⟩
  · rintro ⟨_,y,_,hy,hx⟩
    exact ⟨y,hy,hx⟩

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

theorem bounded_univ (p : Formula) (e : ℕ → ZFSet.{u}) :
    (fromBounded p).Sat Set.univ e ↔ p.Eval e := by
  induction p generalizing e with
  | equal => rfl
  | member => rfl
  | conj p q ihp ihq => exact and_congr (ihp e) (ihq e)
  | neg p ih => exact not_congr (ih e)
  | existsMem i p ih =>
    simp only [fromBounded,SentenceForm.Sat,Formula.Eval,cons_zero,cons_succ,Set.mem_univ,true_and]
    apply exists_congr; intro x
    exact and_congr_right (fun _ => ih (cons x e))

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

theorem bounded_separation_mem_definablePower (A a : ZFSet.{u}) (hA : Transitive A)
    (ha : a ∈ A) (φ : Formula) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) :
    a.sep (fun x => φ.Eval (cons x e)) ∈ definablePower A := by
  let ψ := SentenceForm.conj (.member 0 1) ((fromBounded φ).rename parameterShift)
  have hψ := separation_mem_definablePower A ψ (cons a e) (by
    intro i _; cases i; exact ha; exact he _)
  have heq : A.sep (fun x => ψ.Sat (A : Set ZFSet) (cons x (cons a e))) =
      a.sep (fun x => φ.Eval (cons x e)) := by
    apply ZFSet.ext; intro x
    simp only [ZFSet.mem_sep,ψ,Sat,cons_zero,cons_succ,shifted_parameters,bounded_sat]
    constructor
    · rintro ⟨hx,hxa,hφ⟩
      exact ⟨hxa,(φ.absolute A hA _ (by intro i; cases i; exact hx; exact he _)).mp hφ⟩
    · rintro ⟨hxa,hφ⟩
      have hx := hA a ha x hxa
      exact ⟨hx,hxa,(φ.absolute A hA _ (by intro i; cases i; exact hx; exact he _)).mpr hφ⟩
  rwa [heq] at hψ

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

theorem internally_indexed_ground_reals (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (x : ZFSet.{u}) (hx : x ⊆ ZFSet.omega) :
    (∃ o : Ordinal.{u}, o.toZFSet ∈ M ∧ x ∈ level (groundReals M) o) ↔ x ∈ M := by
  constructor
  · rintro ⟨o,ho,hxl⟩
    exact level_subset_model M (groundReals M) hM hT (groundReals_mem M hM hT) o ho hxl
  · intro hxM
    have hω := sourceT_omega_mem M hM hT
    refine ⟨0,?_,?_⟩
    · simpa only [Ordinal.toZFSet_zero] using hM _ hω _ ZFSet.omega_zero
    · rw [level_zero]
      exact parameter_subset_seed (groundReals M) ((mem_groundReals M x).mpr ⟨hxM,hx⟩)

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

theorem relativeModel_ground_reals (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (x : ZFSet.{u}) (hx : x ⊆ ZFSet.omega) :
    x ∈ relativeModel M (groundReals M) ↔ x ∈ M := by
  rw [mem_relativeModel M _ x hM hT (groundReals_mem M hM hT)]
  exact internally_indexed_ground_reals M hM hT x hx

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

theorem relativeModel_sigmaDefinable (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) :
    SigmaDefinable M (fun e => InRelativeModel M R (e 0)) := by
  apply (relativeLevel_sigmaDefinable M R hM hT hR).existsSet.congr
  intro e _
  change (∃ o ∈ M, o.IsOrdinal ∧ e 0 ∈ stage R o) ↔ _
  constructor
  · rintro ⟨o,ho,hord,hx⟩
    refine ⟨o.rank,?_,?_⟩
    · rwa [hord.toZFSet_rank_eq]
    · change e 0 ∈ stage R o.rank.toZFSet
      rwa [hord.toZFSet_rank_eq]
  · rintro ⟨o,ho,hx⟩
    exact ⟨o.toZFSet,ho,ZFSet.isOrdinal_toZFSet o,hx⟩

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

theorem SigmaDefinable.internal_separation {M : ZFSet.{u}}
    {P : (ℕ → ZFSet.{u}) → Prop} (h : SigmaDefinable M P)
    (hM : Transitive M) (hT : SourceT M) (e : ℕ → ZFSet.{u})
    (he : ∀ i, e i ∈ M) {a : ZFSet.{u}} (ha : a ∈ M) :
    a.sep (fun x => P (cons x e)) ∈ M := by
  obtain ⟨p,d,hd,hp⟩ := h
  have hm : ∀ i, mix e d i ∈ M := by
    intro i; unfold mix; split <;> first | exact he _ | exact hd _
  have hs := sigma_sep_mem M hM hT.separation.finitePrefix
    (p.rename bindSlots) (mix e d) hm ha
  have eq : a.sep (fun x => (p.rename bindSlots).Realize M (cons x (mix e d))) =
      a.sep (fun x => P (cons x e)) := by
    apply ZFSet.ext; intro x
    simp only [ZFSet.mem_sep]
    apply and_congr_right; intro hx
    rw [SigmaFormula.realize_rename]
    change p.Realize M (cons x (mix e d) ∘ bindSlots) ↔ _
    rw [bind_mix]
    exact hp _ (by intro i; cases i; exact hM a ha x hx; exact he _)
  exact eq ▸ hs

theorem relative_part_mem (M R a : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) (ha : a ∈ M) :
    a.sep (InRelativeModel M R) ∈ M := by
  exact SigmaDefinable.internal_separation (relativeModel_sigmaDefinable M R hM hT hR)
    hM hT (fun _ => R) (fun _ => hR) ha

theorem relative_part_bounded (M R a : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) (ha : a ∈ M) :
    ∃ o : Ordinal.{u}, o.toZFSet ∈ M ∧
      ∀ x ∈ a, InRelativeModel M R x ↔ x ∈ level R o := by
  obtain ⟨o,ho,hbound⟩ := relative_level_bound M R (a.sep (InRelativeModel M R))
    hM hT hR (relative_part_mem M R a hM hT hR ha)
    (fun _ hx => (ZFSet.mem_sep.mp hx).2)
  exact ⟨o,ho,fun x hx => ⟨fun h => hbound (ZFSet.mem_sep.mpr ⟨hx,h⟩),
    fun h => ⟨o,ho,h⟩⟩⟩

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

theorem pair_in_relativeModel (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) {a b : ZFSet.{u}}
    (ha : InRelativeModel M R a) (hb : InRelativeModel M R b) :
    InRelativeModel M R ({a,b} : ZFSet.{u}) := by
  obtain ⟨i,hi,hia⟩ := ha
  obtain ⟨j,hj,hjb⟩ := hb
  refine ⟨max i j+1,internal_ordinal_succ M hM hT _ (internal_ordinal_max M hi hj),?_⟩
  rw [level_succ]
  exact pair_mem_definablePower _ a b (level_mono R (le_max_left i j) hia)
    (level_mono R (le_max_right i j) hjb)

theorem union_in_relativeModel (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) {a : ZFSet.{u}} (ha : InRelativeModel M R a) :
    InRelativeModel M R (ZFSet.sUnion a) := by
  obtain ⟨i,hi,hia⟩ := ha
  refine ⟨i+1,internal_ordinal_succ M hM hT i hi,?_⟩
  rw [level_succ]
  exact union_mem_definablePower _ a (level_transitive R i) hia

theorem bounded_separation_in_relativeModel (M R a : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (ha : InRelativeModel M R a)
    (φ : Formula) (e : ℕ → ZFSet.{u})
    (he : ∀ i, i < (fromBounded φ).bound → InRelativeModel M R (e i)) :
    InRelativeModel M R (a.sep (fun x => φ.Eval (cons x e))) := by
  obtain ⟨i,hi,hia⟩ := ha
  obtain ⟨j,hj,hje⟩ := finite_parameters_in_relative_level M R hM hT e _ he
  let A := level R (max i j)
  have haA : a ∈ A := level_mono R (le_max_left i j) hia
  let e' : ℕ → ZFSet.{u} := fun n => if n < (fromBounded φ).bound then e n else a
  have heA : ∀ n, e' n ∈ A := by
    intro n
    dsimp [e']; split
    next hn => exact level_mono R (le_max_right i j) (hje n hn)
    next => exact haA
  have heval (x : ZFSet.{u}) : φ.Eval (cons x e') ↔ φ.Eval (cons x e) := by
    rw [← bounded_univ,← bounded_univ]
    apply (fromBounded φ).finite_support
    intro k hk
    cases k with
    | zero => rfl
    | succ k =>
      change e' k = e k
      simp [e',show k < (fromBounded φ).bound by omega]
  have heq : a.sep (fun x => φ.Eval (cons x e')) = a.sep (fun x => φ.Eval (cons x e)) := by
    apply ZFSet.ext; intro x
    simp only [ZFSet.mem_sep,heval]
  refine ⟨max i j+1,internal_ordinal_succ M hM hT _ (internal_ordinal_max M hi hj),?_⟩
  rw [level_succ,← heq]
  exact bounded_separation_mem_definablePower A a (level_transitive R _) haA φ e' heA

theorem relativeModel_pairing (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) : Pairing (relativeModel M R) := by
  intro a ha b hb
  have mem := mem_relativeModel M R
  refine ⟨{a,b},(mem _ hM hT hR).mpr (pair_in_relativeModel M R hM hT
    ((mem _ hM hT hR).mp ha) ((mem _ hM hT hR).mp hb)),?_⟩
  intro x _; exact ZFSet.mem_pair

theorem relativeModel_union (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) : BoundedSetTheory.Union (relativeModel M R) := by
  intro a ha
  refine ⟨ZFSet.sUnion a,(mem_relativeModel M R _ hM hT hR).mpr
    (union_in_relativeModel M R hM hT ((mem_relativeModel M R a hM hT hR).mp ha)),?_⟩
  intro x _
  rw [ZFSet.mem_sUnion]
  constructor
  · rintro ⟨y,hy,hx⟩
    exact ⟨y,relativeModel_transitive M R hM a ha y hy,hy,hx⟩
  · rintro ⟨y,_,hy,hx⟩; exact ⟨y,hy,hx⟩

theorem relativeModel_bounded_separation (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) : Separation (relativeModel M R) := by
  intro φ e he a ha
  have mem := mem_relativeModel M R
  refine ⟨a.sep (fun x => φ.Eval (cons x e)),(mem _ hM hT hR).mpr
    (bounded_separation_in_relativeModel M R a hM hT ((mem _ hM hT hR).mp ha)
      φ e (fun i _ => (mem _ hM hT hR).mp (he i))),?_⟩
  intro x hx
  rw [ZFSet.mem_sep,Formula.absolute φ _ (relativeModel_transitive M R hM) _ (by
    intro i; cases i; exact hx; exact he _)]

theorem ground_relativeModel_omega (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) : ZFSet.omega ∈ relativeModel M (groundReals M) := by
  exact (relativeModel_ground_reals M hM hT _ (fun _ hx => hx)).mpr
    (sourceT_omega_mem M hM hT)

theorem ground_relativeModel_infinity (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) : Infinity (relativeModel M (groundReals M)) := by
  have hω := ground_relativeModel_omega M hM hT
  have ht := relativeModel_transitive M (groundReals M) hM
  refine ⟨ZFSet.omega,hω,⟨∅,ht _ hω _ ZFSet.omega_zero,ZFSet.omega_zero,
    fun z _ => ZFSet.notMem_empty z⟩,?_⟩
  intro x _ hx
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  have hs := (mem_omega _).mpr ⟨n+1,rfl⟩
  exact ⟨natSet (n+1),ht _ hω _ hs,hs,fun _ _ => ZFSet.mem_insert_iff⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeModelPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel ElementaryModel SentenceForm
universe u

theorem subsets_mem_definablePower (A a : ZFSet.{u}) (hA : Transitive A) (ha : a ∈ A) :
    A.sep (fun x => x ⊆ a) ∈ definablePower A := by
  have hs := separation_mem_definablePower A (fromBounded (.subset 0 1))
    (fun _ => a) (fun _ _ => ha)
  have eq : A.sep (fun x => (fromBounded (.subset 0 1)).Sat (A : Set ZFSet)
      (cons x (fun _ => a))) = A.sep (fun x => x ⊆ a) := by
    apply ZFSet.ext; intro x
    simp only [ZFSet.mem_sep]
    apply and_congr_right; intro hx
    rw [bounded_sat,Formula.absolute _ A hA _ (by
      intro i; cases i; exact hx; exact ha)]
    exact Formula.eval_subset 0 1 _
  exact eq ▸ hs

theorem relativeModel_power_set (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) : PowerSet (relativeModel M R) := by
  intro a ha
  have haM := relativeModel_subset M R ha
  obtain ⟨q,hq,hqdef⟩ := internal_power M hM hT.powerSet haM
  obtain ⟨i,hi,hbound⟩ := relative_part_bounded M R q hM hT hR hq
  obtain ⟨j,hj,hja⟩ := (mem_relativeModel M R a hM hT hR).mp ha
  let o := max i j
  let A := level R o
  let b := A.sep (fun x => x ⊆ a)
  have haA : a ∈ A := level_mono R (le_max_right i j) hja
  have ho : o.toZFSet ∈ M := internal_ordinal_max M hi hj
  have hb : b ∈ relativeModel M R := by
    apply (mem_relativeModel M R b hM hT hR).mpr
    refine ⟨o+1,internal_ordinal_succ M hM hT o ho,?_⟩
    rw [level_succ]
    exact subsets_mem_definablePower A a (level_transitive R o) haA
  refine ⟨b,hb,?_⟩
  intro x hx
  have hsub : (∀ y ∈ relativeModel M R, y ∈ x → y ∈ a) ↔ x ⊆ a :=
    ⟨fun h y hy => h y (relativeModel_transitive M R hM x hx y hy) hy,
      fun h _ _ hy => h hy⟩
  rw [hsub]
  change x ∈ A.sep (fun x => x ⊆ a) ↔ x ⊆ a
  rw [ZFSet.mem_sep]
  constructor
  · exact And.right
  · intro hxa
    have hxq := (hqdef x).mpr ⟨relativeModel_subset M R hx,hxa⟩
    have hxi := (hbound x hxq).mp ((mem_relativeModel M R x hM hT hR).mp hx)
    exact ⟨level_mono R (le_max_left i j) hxi,hxa⟩

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeModelOrdinals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel InternalRank
universe u

theorem level_rank_lower_bound (R : ZFSet.{u}) (o : Ordinal.{u}) : o ≤ (level R o).rank := by
  induction o using Ordinal.lt_wf.induction with
  | h o ih =>
    by_contra h
    have hlt : (level R o).rank < o := lt_of_not_ge h
    have hmem := level_mem_level R hlt
    exact (not_le_of_gt (ZFSet.rank_lt_of_mem hmem)) (ih _ hlt)

theorem ground_relativeModel_ordinal_iff_oai (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (o : Ordinal.{u}) :
    o.toZFSet ∈ relativeModel M (groundReals M) ↔ o.toZFSet ∈ M := by
  constructor
  · intro ho; exact relativeModel_subset M (groundReals M) ho
  · intro ho
    let R := groundReals M
    let N := relativeModel M R
    have hR := groundReals_mem M hM hT
    have hN := relativeModel_transitive M R hM
    have hs := internal_ordinal_succ M hM hT o ho
    have hlevel : level R (o+1) ∈ N := (mem_relativeModel M R _ hM hT hR).mpr
      (level_in_relativeModel M R hM hT (o+1) hs)
    have hr := rankSet_mem_ground N hN (relativeModel_pairing M R hM hT hR)
      (relativeModel_union M R hM hT hR) (relativeModel_power_set M R hM hT hR)
      (relativeModel_bounded_separation M R hM hT hR)
      (relativeModel_sigma_replacement M R hM hT hR)
      (ground_relativeModel_infinity M hM hT) hlevel
    rw [rankSet_eq_ordinal] at hr
    exact hN _ hr _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr
      ((lt_add_one o).trans_le (level_rank_lower_bound R (o+1))))

end TuringRigidity.RelativeConstructible

end OAI
end

theorem solution.{u} : type_of% @OAI.TuringRigidity.RelativeConstructible.ground_relativeModel_ordinal_iff_oai.{u} := @OAI.TuringRigidity.RelativeConstructible.ground_relativeModel_ordinal_iff_oai.{u}
