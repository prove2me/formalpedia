-- Prove2me | solution 1 for OAI.TuringRigidity.RelativeConstructible.Construction.inlined_at_level
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:30:15.460215+00:00
-- url     : https://prove2.me/submissions/54565a57-e3d6-4ec1-b5a9-c6e1a1ff177d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelReals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelReals
open BoundedSetTheory TransitiveNameModel SetPresentationDecoding
universe u
noncomputable section

theorem omega_exists (P : ZFSet.{u} → Prop) :
    (∃ x ∈ ZFSet.omega, P x) ↔ ∃ n, P (natSet n) := by
  constructor
  · rintro ⟨x,hx,hP⟩
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    exact ⟨n,hP⟩
  · rintro ⟨n,hP⟩
    exact ⟨_,(mem_omega _).mpr ⟨n,rfl⟩,hP⟩

end
end TuringRigidity.SetModelReals

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelIteration
open BoundedSetTheory TransitiveNameModel SetModelReals
universe u
noncomputable section

theorem finiteGraph_zero (f : ℕ → ZFSet.{u}) : finiteGraph 0 f = ∅ := by
  apply ZFSet.ext
  intro z
  simp only [mem_finiteGraph,Nat.not_lt_zero,false_and,exists_false,ZFSet.notMem_empty]

theorem finiteGraph_succ (n : ℕ) (f : ℕ → ZFSet.{u}) :
    finiteGraph (n+1) f = insert (ZFSet.pair (natSet n) (f n)) (finiteGraph n f) := by
  apply ZFSet.ext
  intro z
  simp only [mem_finiteGraph,ZFSet.mem_insert_iff]
  constructor
  · rintro ⟨i,hi,he⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi|rfl
    · exact Or.inr ⟨i,hi,he⟩
    · exact Or.inl he
  · rintro (he|⟨i,hi,he⟩)
    · exact ⟨n,Nat.lt_succ_self n,he⟩
    · exact ⟨i,Nat.lt_succ_of_lt hi,he⟩

theorem finiteGraph_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hω : ZFSet.omega.{u} ∈ M)
    (n : ℕ) (f : ℕ → ZFSet.{u}) (hf : ∀ i < n, f i ∈ M) : finiteGraph n f ∈ M := by
  induction n with
  | zero =>
    rw [finiteGraph_zero]
    exact hM _ hω _ ZFSet.omega_zero
  | succ n ih =>
    rw [finiteGraph_succ]
    have hn := hM _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
    have hp := orderedPair_mem M hM hP hn (hf n (Nat.lt_succ_self n))
    have hs := singleton_mem M hM hP hp
    have hu := binary_union_mem M hM hP hU hs (ih (fun i hi => hf i (Nat.lt_succ_of_lt hi)))
    have he : ({ZFSet.pair (natSet n) (f n)} : ZFSet.{u}) ∪ finiteGraph n f =
        insert (ZFSet.pair (natSet n) (f n)) (finiteGraph n f) := by
      apply ZFSet.ext
      intro z
      simp only [ZFSet.mem_union,ZFSet.mem_singleton,ZFSet.mem_insert_iff]
    exact he ▸ hu

theorem eval_traceFormula (n x y p v g w z : ℕ) (e : ℕ → ZFSet.{u})
    (k : ℕ) (hn : e n = natSet k) (hw : e w = ZFSet.omega) (hz : e z = natSet 0) :
    (traceFormula n x y p v g w z).Eval e ↔ Trace (e v) (e g) k (e x) (e y) (e p) := by
  simp only [traceFormula,Formula.Eval,Formula.eval_pairMem,Formula.eval_allMem,
    Formula.eval_imp,Formula.eval_successor,cons_zero,cons_succ,hn,hw,hz,Trace]
  apply and_congr Iff.rfl
  apply and_congr _ Iff.rfl
  constructor
  · intro h i hi a ha hp
    obtain ⟨s,_,hs,b,hb,hpb,hgb⟩ := h (natSet i) ((natSet_mem_natSet i k).mpr hi) a ha hp
    exact ⟨b,hb,by simpa only [hs,natSet] using hpb,hgb⟩
  · intro h i hi a ha hp
    obtain ⟨j,hj,rfl⟩ := (mem_natSet k i).mp hi
    obtain ⟨b,hb,hpb,hgb⟩ := h j hj a ha hp
    exact ⟨natSet (j+1),(mem_omega _).mpr ⟨j+1,rfl⟩,rfl,b,hb,hpb,hgb⟩

theorem iterate_mem {v : ZFSet.{u}} (F : ZFSet.{u} → ZFSet.{u})
    (hF : ∀ x ∈ v, F x ∈ v) {x : ZFSet.{u}} (hx : x ∈ v) (n : ℕ) : F^[n] x ∈ v := by
  induction n with
  | zero => exact hx
  | succ n ih => simpa only [Function.iterate_succ_apply'] using hF _ ih

theorem trace_correct {v g : ZFSet.{u}} (F : ZFSet.{u} → ZFSet.{u})
    (hF : ∀ x ∈ v, F x ∈ v)
    (hg : ∀ x ∈ v, ∀ y ∈ v, ZFSet.pair x y ∈ g ↔ y = F x)
    {n : ℕ} {x y p : ZFSet.{u}} (hx : x ∈ v) (ht : Trace v g n x y p) : y = F^[n] x := by
  have hp (i : ℕ) (hi : i ≤ n) : ZFSet.pair (natSet i) (F^[i] x) ∈ p := by
    induction i with
    | zero => exact ht.1
    | succ i ih =>
      have hv := iterate_mem F hF hx i
      obtain ⟨b,hb,hpb,hgb⟩ := ht.2.1 i (by omega) _ hv (ih (by omega))
      have he := (hg _ hv b hb).mp hgb
      simpa only [he,Function.iterate_succ_apply'] using hpb
  exact (ht.2.2 _ (iterate_mem F hF hx n) (hp n le_rfl)).symm

theorem finiteGraph_trace {v g : ZFSet.{u}} (F : ZFSet.{u} → ZFSet.{u})
    (hF : ∀ x ∈ v, F x ∈ v)
    (hg : ∀ x ∈ v, ∀ y ∈ v, ZFSet.pair x y ∈ g ↔ y = F x)
    {x : ZFSet.{u}} (hx : x ∈ v) (n : ℕ) :
    Trace v g n x (F^[n] x) (finiteGraph (n+1) (fun i => F^[i] x)) := by
  refine ⟨(pair_mem_finiteGraph _ _ _ _).mpr ⟨by omega,rfl⟩,?_,?_⟩
  · intro i hi a ha hpa
    have he := ((pair_mem_finiteGraph _ _ _ _).mp hpa).2
    subst a
    refine ⟨F^[i+1] x,iterate_mem F hF hx (i+1),
      (pair_mem_finiteGraph _ _ _ _).mpr ⟨by omega,rfl⟩,?_⟩
    apply (hg _ (iterate_mem F hF hx i) _ (iterate_mem F hF hx (i+1))).mpr
    exact Function.iterate_succ_apply' F i x
  · intro b _ hpb
    exact ((pair_mem_finiteGraph _ _ _ _).mp hpb).2

end
end TuringRigidity.SetModelIteration

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelIteration
open BoundedSetTheory TransitiveNameModel SetModelReals
universe u
noncomputable section

theorem mem_iterationSet {v : ZFSet.{u}} (F : ZFSet.{u} → ZFSet.{u})
    (hF : ∀ x ∈ v, F x ∈ v) (z : ZFSet.{u}) :
    z ∈ iterationSet v F ↔ ∃ n : ℕ, ∃ x ∈ v,
      z = ZFSet.pair (ZFSet.pair (natSet n) x) (F^[n] x) := by
  rw [iterationSet,ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨n,x,hx,rfl⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨ZFSet.pair_mem_prod.mpr
      ⟨(mem_omega _).mpr ⟨n,rfl⟩,hx⟩,iterate_mem F hF hx n⟩,⟨n,x,hx,rfl⟩⟩

theorem eval_iterationFormula (z v g p d : ZFSet.{u}) :
    iterationFormula.Eval (cons z (cons ZFSet.omega (cons v (cons g
      (cons p (cons (natSet 0) (fun _ => d))))))) ↔
    ∃ n : ℕ, ∃ x ∈ v, ∃ y ∈ v, ∃ t ∈ d, ∃ s ∈ p,
      z = ZFSet.pair t y ∧ t = ZFSet.pair (natSet n) x ∧ Trace v g n x y s := by
  simp only [iterationFormula,Formula.Eval,cons_zero,cons_succ]
  rw [omega_exists]
  apply exists_congr
  intro n
  apply exists_congr
  intro x
  apply and_congr Iff.rfl
  apply exists_congr
  intro y
  apply and_congr Iff.rfl
  apply exists_congr
  intro t
  apply and_congr Iff.rfl
  apply exists_congr
  intro s
  apply and_congr Iff.rfl
  simp only [Formula.eval_orderedPair,cons_zero,cons_succ]
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  exact eval_traceFormula _ _ _ _ _ _ _ _ _ n rfl rfl rfl

theorem iterationSet_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M)
    {v g : ZFSet.{u}} (hv : v ∈ M) (hgM : g ∈ M)
    (F : ZFSet.{u} → ZFSet.{u}) (hF : ∀ x ∈ v, F x ∈ v)
    (hg : ∀ x ∈ v, ∀ y ∈ v, ZFSet.pair x y ∈ g ↔ y = F x) :
    iterationSet v F ∈ M := by
  have hω := omega_mem M hM hS hI
  have h0 : natSet.{u} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  let d := ZFSet.prod ZFSet.omega v
  have hd : d ∈ M := product_mem M hM hP hU hPow hS hω hv
  obtain ⟨p,hp,hpdef⟩ := internal_power M hM hPow hd
  have hprod := product_mem M hM hP hU hPow hS hd hv
  let e := cons ZFSet.omega (cons v (cons g (cons p (cons (natSet 0) (fun _ => d)))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|_|i <;> simp only [e,cons_zero,cons_succ]
    · exact hω
    · exact hv
    · exact hgM
    · exact hp
    · exact h0
    · exact hd
  have hs := sep_mem M hM hS iterationFormula e he hprod
  have eq : ZFSet.sep (fun z => iterationFormula.Eval (cons z e)) (ZFSet.prod d v) =
      iterationSet v F := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep,mem_iterationSet F hF,
      show iterationFormula.Eval (cons z e) ↔ _ from eval_iterationFormula z v g p d]
    constructor
    · rintro ⟨_,n,x,hx,y,hy,t,ht,s,hs,hz,htx,htrace⟩
      exact ⟨n,x,hx,by rw [hz,htx,trace_correct F hF hg hx htrace]⟩
    · rintro ⟨n,x,hx,rfl⟩
      let s := finiteGraph (n+1) (fun i => F^[i] x)
      have hsM : s ∈ M := finiteGraph_mem M hM hP hU hω _ _
        (fun i _ => hM v hv _ (iterate_mem F hF hx i))
      have hsD : s ⊆ d := by
        intro z hz
        obtain ⟨i,hi,rfl⟩ := (mem_finiteGraph _ _ _).mp hz
        exact ZFSet.pair_mem_prod.mpr ⟨(mem_omega _).mpr ⟨i,rfl⟩,iterate_mem F hF hx i⟩
      have hsP := (hpdef s).mpr ⟨hsM,hsD⟩
      have htD : ZFSet.pair (natSet n) x ∈ d :=
        ZFSet.pair_mem_prod.mpr ⟨(mem_omega _).mpr ⟨n,rfl⟩,hx⟩
      refine ⟨ZFSet.pair_mem_prod.mpr ⟨htD,iterate_mem F hF hx n⟩,
        n,x,hx,_,iterate_mem F hF hx n,_,htD,s,hsP,rfl,rfl,?_⟩
      exact finiteGraph_trace F hF hg hx n
  exact eq ▸ hs

end
end TuringRigidity.SetModelIteration

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

theorem pair_mem_successorSet {x y : ZFSet.{u}} (hx : x ∈ ZFSet.omega) (hy : y ∈ ZFSet.omega) :
    ZFSet.pair x y ∈ successorSet ↔ y = setSucc x := by
  simp only [successorSet,ZFSet.mem_sep,ZFSet.pair_mem_prod,hx,hy,true_and,ZFSet.pair_inj]
  constructor
  · rintro ⟨a,ha,he,hs⟩
    exact he ▸ hs
  · intro h
    exact ⟨x,hx,rfl,h⟩

theorem successorSet_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M) : successorSet.{u} ∈ M := by
  have hω := omega_mem M hM hS hI
  have hprod := product_mem M hM hP hU hPow hS hω hω
  have hs := sep_mem M hM hS successorFormula (fun _ => ZFSet.omega) (fun _ => hω) hprod
  have eq : ZFSet.sep (fun z => successorFormula.Eval (cons z (fun _ => ZFSet.omega)))
      (ZFSet.prod ZFSet.omega ZFSet.omega) = successorSet.{u} := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sep,successorFormula,Formula.Eval,Formula.eval_orderedPair,
      Formula.eval_successor,cons_zero,cons_succ,successorSet]
    apply and_congr Iff.rfl
    constructor
    · rintro ⟨x,hx,y,hy,hz,rfl⟩
      exact ⟨x,hx,hz⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x,hx,setSucc x,setSucc_omega x hx,rfl,rfl⟩
  exact eq ▸ hs

theorem iterate_setSucc (n m : ℕ) : setSucc^[n] (natSet.{u} m) = natSet (m+n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    change natSet (m+n+1) = natSet (m+(n+1))
    rw [Nat.add_assoc]

theorem addition_code (n m k : ℕ) :
    ZFSet.pair (ZFSet.pair (natSet.{u} n) (natSet m)) (natSet k) ∈ additionSet ↔ k = n+m := by
  rw [additionSet,mem_iterationSet setSucc setSucc_omega]
  constructor
  · rintro ⟨i,x,hx,he⟩
    obtain ⟨hinput,hout⟩ := ZFSet.pair_inj.mp he
    obtain ⟨hi,rfl⟩ := ZFSet.pair_inj.mp hinput
    have hin := natSet_injective hi
    rw [←hin,iterate_setSucc] at hout
    exact (natSet_injective hout).trans (Nat.add_comm m n)
  · intro hk
    refine ⟨n,natSet m,(mem_omega _).mpr ⟨m,rfl⟩,?_⟩
    rw [iterate_setSucc,hk,Nat.add_comm m n]

theorem additionSet_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M) : additionSet.{u} ∈ M :=
  iterationSet_mem M hM hP hU hPow hS hI (omega_mem M hM hS hI)
    (successorSet_mem M hM hP hU hPow hS hI) setSucc setSucc_omega
    (fun _ hx _ hy => pair_mem_successorSet hx hy)

end
end TuringRigidity.SetModelArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelMultiplicationStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
universe u
noncomputable section

theorem mem_pairNumbers (x : ZFSet.{u}) : x ∈ pairNumbers ↔ ∃ q, x = numberPair q := by
  constructor
  · intro hx
    obtain ⟨a,ha,b,hb,rfl⟩ := ZFSet.mem_prod.mp hx
    obtain ⟨n,rfl⟩ := (mem_omega a).mp ha
    obtain ⟨m,rfl⟩ := (mem_omega b).mp hb
    exact ⟨(n,m),rfl⟩
  · rintro ⟨q,rfl⟩
    exact ZFSet.pair_mem_prod.mpr ⟨(mem_omega _).mpr ⟨q.1,rfl⟩,(mem_omega _).mpr ⟨q.2,rfl⟩⟩

end
end TuringRigidity.SetModelArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration SetModelSequences
universe u
noncomputable section

@[simp] theorem natPair_mem (n m : ℕ) :
    ZFSet.pair (natSet.{u} n) (natSet m) ∈ pairNumbers :=
  (mem_pairNumbers _).mpr ⟨(n,m),rfl⟩

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

theorem setBounded_absolute (p : SentenceForm) (M : ZFSet.{u}) (hM : Transitive M)
    (a : ℕ) (v : ℕ → ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (setBounded p a v).Realize M e ↔ p.Sat (e a : Set ZFSet) (fun i => e (v i)) :=
  ((setBounded p a v).absolute M hM e he).trans (setBounded_eval p a v e)

end TuringRigidity.RelativeConstructible

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

theorem parameter_in_relativeModel (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) : InRelativeModel M R R :=
  ⟨0,internal_ordinal_zero M hM hT,level_zero R ▸ parameter_mem_seed R⟩

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory ElementaryModel
universe u

theorem Construction.value_in_relativeModel (t : Construction.{u}) (M R : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (P : Oracle)
    (ht : t.Certified R P) (hi : t.Indexed M) : InRelativeModel M R (t.value R P) := by
  cases t with
  | reals => exact parameter_in_relativeModel M R hM hT
  | parameter => exact (parameter_in_relativeModel M R hM hT).transitive ht
  | define o n p c =>
    refine ⟨o+1,internal_ordinal_succ M hM hT o hi.1,?_⟩
    rw [level_succ,mem_definablePower]
    exact ⟨n,p,_,ht.1,fun i => (ht.2 i).2,rfl⟩

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

theorem subsetBody_spec (M : ZFSet.{u}) (hM : Transitive M)
    (n out a : ℕ) (p : SentenceForm) (hp : p.bound ≤ n+1)
    (e w : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (hw : ∀ i, i < n → w i ∈ M) :
    (subsetBody n out a p).Sat (M : Set ZFSet) (prependValues w n e) ↔
      e out = definedSubset (e a) p (fun i : Fin n => w i) := by
  have hpre (i : ℕ) : prependValues w n e i ∈ M := by
    by_cases hi : i < n
    · rw [prependValues_lt _ _ _ _ hi]; exact hw i hi
    · have hi' : i = n+(i-n) := by omega
      rw [hi',prependValues_tail]; exact he _
  have htruth (x : ZFSet.{u}) (hx : x ∈ M) :
      (fromBounded (setBounded p (n+a+1) id)).Sat (M : Set ZFSet)
        (cons x (prependValues w n e)) ↔
      p.Sat (e a : Set ZFSet) (cons x (tupleEnv (fun i : Fin n => w i))) := by
    rw [bounded_sat,setBounded_absolute p M hM _ _ _
      (by intro i; cases i; exact hx; exact hpre _)]
    simp only [cons_succ,prependValues_tail,id_eq]
    apply p.finite_support
    intro i hi
    cases i with
    | zero => rfl
    | succ i =>
      change prependValues w n e i = tupleEnv (fun j : Fin n => w j) i
      rw [prependValues_lt _ _ _ _ (by omega)]
      simp [tupleEnv,show i < n by omega]
  simp only [subsetBody,SentenceForm.sat_all,SentenceForm.sat_iff,SentenceForm.Sat,
    cons_zero,cons_succ,prependValues_tail]
  constructor
  · intro h
    apply ZFSet.ext; intro x
    rw [mem_definedSubset]
    constructor
    · intro hx
      have hxM := hM _ (he out) x hx
      obtain ⟨ha,ht⟩ := (h x hxM).mp hx
      exact ⟨ha,(htruth x hxM).mp ht⟩
    · rintro ⟨ha,ht⟩
      have hxM := hM _ (he a) x ha
      exact (h x hxM).mpr ⟨ha,(htruth x hxM).mpr ht⟩
  · intro h x hx
    rw [h,mem_definedSubset]
    exact and_congr Iff.rfl (htruth x hx).symm

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelJoin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
universe u
noncomputable section

theorem natSet_successor_eq (n m : ℕ) :
    natSet.{u} n = insert (natSet m) (natSet m) ↔ n = m+1 := by
  change natSet n = natSet (m+1) ↔ n = m+1
  exact natSet_injective.eq_iff

end
end TuringRigidity.SetModelArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_RealProjectionSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic SetModelReals
universe u

theorem bitIndex_append (a b : List Bool) (n : ℕ) :
    bitIndex (a++b) n = bitIndex a (bitIndex b n) := by
  induction a with
  | nil => rfl
  | cons c a ih => simp only [List.cons_append,bitIndex,ih]

theorem realPart_bits (P : Oracle) (i n : ℕ) :
    realPart P i n = P (bitIndex (partBits i) n) := by
  induction i generalizing P with
  | zero => simp [realPart,partBits,bitIndex]
  | succ i ih => exact ih (fun k => P (2*k+1))

theorem bitStep_spec (b : Bool) (w a d x y : ℕ) (e : ℕ → ZFSet.{u})
    (hw : e w = ZFSet.omega) (ha : e a = additionSet) (hd : e d = pairNumbers)
    (n m : ℕ) (hx : e x = natSet n) (hy : e y = natSet m) :
    (bitStep b w a d x y).Eval e ↔ m = 2*n + if b then 1 else 0 := by
  cases b
  · simp [bitStep,eval_tripleFormula,hx,hy,ha,hd,addition_code,two_mul]
  · simp only [bitStep,ite_true,Formula.Eval,eval_tripleFormula,Formula.eval_successor,
      cons_zero,cons_succ,hw,hx,hy,ha,hd]
    rw [omega_exists]
    simp only [natPair_mem,true_and,addition_code,natSet_successor_eq]
    constructor
    · rintro ⟨k,hk,hm⟩; omega
    · intro hm; exact ⟨n+n,rfl,by omega⟩

theorem bitIndexFormula_spec (bs : List Bool) (w a d x y : ℕ) (e : ℕ → ZFSet.{u})
    (hw : e w = ZFSet.omega) (ha : e a = additionSet) (hd : e d = pairNumbers)
    (n m : ℕ) (hx : e x = natSet n) (hy : e y = natSet m) :
    (bitIndexFormula bs w a d x y).Eval e ↔ m = bitIndex bs n := by
  induction bs generalizing w a d x y e m with
  | nil => simp [bitIndexFormula,Formula.Eval,hx,hy,bitIndex,natSet_injective.eq_iff]
  | cons b bs ih =>
    simp only [bitIndexFormula,Formula.Eval,hw]
    rw [omega_exists]
    have hb (k : ℕ) := bitStep_spec b (w+1) (a+1) (d+1) 0 (y+1)
      (cons (natSet k) e) hw ha hd k m rfl hy
    have hi (k : ℕ) := ih (w+1) (a+1) (d+1) (x+1) 0 (cons (natSet k) e)
      hw ha hd k hx rfl
    simp only [hi,hb,exists_eq_left,bitIndex]

theorem projectionMember_spec (bs : List Bool) (w a d P x : ℕ)
    (e : ℕ → ZFSet.{u}) (hw : e w = ZFSet.omega) (ha : e a = additionSet)
    (hd : e d = pairNumbers) (Q : Oracle) (hP : e P = realCode Q) :
    (projectionMember bs w a d P x).Eval e ↔ e x ∈ realCode (fun n => Q (bitIndex bs n)) := by
  simp only [projectionMember,Formula.Eval,hw,cons_zero,cons_succ,hP]
  constructor
  · rintro ⟨hx,k,hk,hrel,hQ⟩
    obtain ⟨n,hn⟩ := (mem_omega (e x)).mp hx
    obtain ⟨m,rfl⟩ := (mem_omega k).mp hk
    have hm := (bitIndexFormula_spec bs (w+1) (a+1) (d+1) (x+1) 0
      (cons (natSet m) e) hw ha hd n m hn rfl).mp hrel
    rw [hn,natSet_mem_realCode]
    simpa [hm] using (natSet_mem_realCode Q m).mp hQ
  · intro hx
    obtain ⟨n,hn⟩ := (mem_omega (e x)).mp (realCode_subset _ hx)
    have hnQ : Q (bitIndex bs n) = true := (natSet_mem_realCode _ n).mp (hn ▸ hx)
    refine ⟨hn.symm ▸ (mem_omega _).mpr ⟨n,rfl⟩,natSet (bitIndex bs n),
      (mem_omega _).mpr ⟨_,rfl⟩,?_,(natSet_mem_realCode Q _).mpr hnQ⟩
    exact (bitIndexFormula_spec bs (w+1) (a+1) (d+1) (x+1) 0
      (cons (natSet (bitIndex bs n)) e) hw ha hd n _ hn rfl).mpr rfl

theorem projectionFormula_spec (M : ZFSet.{u}) (hM : Transitive M)
    (bs : List Bool) (out w a d P : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (hw : e w = ZFSet.omega) (ha : e a = additionSet) (hd : e d = pairNumbers)
    (Q : Oracle) (hP : e P = realCode Q) :
    (projectionFormula bs out w a d P).Sat (M : Set ZFSet) e ↔
      e out = realCode (fun n => Q (bitIndex bs n)) := by
  have hs (x : ZFSet.{u}) (hx : x ∈ M) :
      (fromBounded (projectionMember bs (w+1) (a+1) (d+1) (P+1) 0)).Sat
        (M : Set ZFSet) (cons x e) ↔ x ∈ realCode (fun n => Q (bitIndex bs n)) := by
    rw [bounded_sat,Formula.absolute _ M hM _
      (by intro i; cases i; exact hx; exact he _)]
    exact projectionMember_spec bs (w+1) (a+1) (d+1) (P+1) 0 (cons x e) hw ha hd Q hP
  simp only [projectionFormula,SentenceForm.sat_all,SentenceForm.sat_iff,
    SentenceForm.Sat,cons_zero,cons_succ]
  constructor
  · intro h
    apply ZFSet.ext; intro x
    constructor
    · intro hx
      have hxM := hM _ (he out) _ hx
      exact (hs x hxM).mp ((h x hxM).mp hx)
    · intro hx
      have hxM := hM _ (hw ▸ he w) _ (realCode_subset _ hx)
      exact (h x hxM).mpr ((hs x hxM).mpr hx)
  · intro h x hx; rw [h]; exact (hs x hx).symm

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_SingleRealConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic
universe u

theorem bitOracle_part (P : Oracle) (bs : List Bool) (i : ℕ) :
    realPart (bitOracle P bs) i = bitOracle P (bs ++ partBits i) := by
  funext n
  rw [realPart_bits]
  simp only [bitOracle,bitIndex_append]

theorem Construction.stageInputs_child (R : ZFSet.{u})
    (o : Ordinal.{u}) (n : ℕ) (p : SentenceForm) (c : Fin n → Construction.{u})
    (i : Fin n) (k : ℕ) :
    (Construction.define o n p c).stageInputs R (Nat.pair i k+1) = (c i).stageInputs R k := by
  simp only [Construction.stageInputs,Construction.inputData,Nat.unpair_pair]
  rw [dite_eq_left i.isLt]
  cases (c i).inputData k <;> rfl

theorem Construction.singleFormula_spec (t : Construction.{u}) (M R : ZFSet.{u})
    (hM : Transitive M) (P : Oracle) (bs : List Bool)
    (ht : t.Certified R (bitOracle P bs))
    (out rR rP w a d : ℕ) (r : ℕ → ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (hRR : e rR = R) (hPP : e rP = realCode P) (hw : e w = ZFSet.omega)
    (ha : e a = additionSet) (hd : e d = pairNumbers)
    (hr : ∀ k, e (r k) = t.stageInputs R k) :
    (t.singleFormula bs out rR rP w a d r).Sat (M : Set ZFSet) e ↔
      e out = t.value R (bitOracle P bs) := by
  induction t generalizing bs out rR rP w a d r e with
  | reals => exact Iff.of_eq (congrArg (e out = ·) hRR)
  | parameter => exact projectionFormula_spec M hM bs out w a d rP e he hw ha hd P hPP
  | define o n p c ih =>
    let v : ℕ → ZFSet.{u} := fun i => if h : i < n then
      (c ⟨i,h⟩).value R (realPart (bitOracle P bs) i) else R
    have hv (i : ℕ) (hin : i < n) : v i ∈ M := by
      dsimp [v]; rw [dite_eq_left hin]
      exact hM _ (show level R o ∈ M from (show e (r 0) = level R o from hr 0) ▸ he (r 0)) _ (ht.2 ⟨i,hin⟩).2
    have hf (i : ℕ) (hin : i < n) (x : ZFSet.{u}) (hx : x ∈ M) :
        (if h : i < n then
          (c ⟨i,h⟩).singleFormula (bs ++ partBits i) 0 (rR+1) (rP+1) (w+1) (a+1) (d+1)
            (fun k => r (Nat.pair i k+1)+1) else .equal 0 0).Sat
          (M : Set ZFSet) (cons x e) ↔ x = v i := by
      rw [dite_eq_left hin,show v i = (c ⟨i,hin⟩).value R (realPart (bitOracle P bs) i) from dite_eq_left hin,
        bitOracle_part]
      have hc : (c ⟨i,hin⟩).Certified R (bitOracle P (bs ++ partBits i)) := by
        rw [← bitOracle_part]; exact (ht.2 ⟨i,hin⟩).1
      apply ih ⟨i,hin⟩ _ hc 0 (rR+1) (rP+1) (w+1) (a+1) (d+1)
        (fun k => r (Nat.pair i k+1)+1) (cons x e)
        (by intro k; cases k; exact hx; exact he _) hRR hPP hw ha hd
      intro k
      change e (r (Nat.pair i k+1)) = _
      rw [hr,Construction.stageInputs_child R o n p c ⟨i,hin⟩ k]
    rw [Construction.singleFormula,bindComputed_spec M n _ _ e v hv hf,
      subsetBody_spec M hM n out (r 0) p ht.1 e v he hv]
    have hA : e (r 0) = level R o := hr 0
    rw [hA]
    have hvs : (fun i : Fin n => v i) =
        (fun i : Fin n => (c i).value R (realPart (bitOracle P bs) i)) := by
      funext i; exact dite_eq_left i.isLt
    rw [hvs]
    rfl

theorem Construction.singleMembership_of_inputs (t : Construction.{u}) (M R : ZFSet.{u})
    (hM : Transitive M) (P : Oracle) (ht : t.Certified R P)
    (hinputs : ∀ i, t.singleInputs R P i ∈ M) (hvalue : t.value R P ∈ M)
    (z : ZFSet.{u}) (hz : z ∈ M) :
    t.singleMembership.Sat (M : Set ZFSet) (cons z (t.singleInputs R P)) ↔
      z ∈ t.value R P := by
  have hs (x : ZFSet.{u}) (hx : x ∈ M) :
      (t.singleFormula [] 0 2 3 4 5 6 (fun k => k+7)).Sat (M : Set ZFSet)
        (cons x (cons z (t.singleInputs R P))) ↔ x = t.value R P := by
    apply t.singleFormula_spec M R hM P [] ht
    · intro i
      rcases i with _|_|i
      · exact hx
      · exact hz
      · exact hinputs i
    all_goals first | rfl | exact fun _ => rfl
  change (∃ x ∈ M, (t.singleFormula [] 0 2 3 4 5 6 (fun k => k+7)).Sat
    (M : Set ZFSet) (cons x (cons z (t.singleInputs R P))) ∧ z ∈ x) ↔ _
  constructor
  · rintro ⟨x,hx,hf,hzx⟩; exact (hs x hx).mp hf ▸ hzx
  · intro hzv
    have hv := hvalue
    exact ⟨_,hv,(hs _ hv).mpr rfl,hzv⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructionStageBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem internal_ordinal_finite_sup (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {α : Type*} (s : Finset α) (v : α → Ordinal.{u})
    (h : ∀ i ∈ s, (v i).toZFSet ∈ M) : (s.sup v).toZFSet ∈ M := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using internal_ordinal_zero M hM hT
  | @insert a s ha ih =>
    rw [Finset.sup_insert]
    exact internal_ordinal_max M (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem Construction.stageBound_mem (t : Construction.{u}) (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (hi : t.Indexed M) : t.stageBound.toZFSet ∈ M := by
  induction t with
  | reals => exact internal_ordinal_zero M hM hT
  | parameter => exact internal_ordinal_zero M hM hT
  | define o n p c ih =>
    exact internal_ordinal_succ M hM hT _ (internal_ordinal_max M hi.1
      (internal_ordinal_finite_sup M hM hT Finset.univ _ (fun i _ => ih i (hi.2 i))))

theorem Construction.stageInputs_bounded (t : Construction.{u}) (R : ZFSet.{u}) :
    ∀ k, t.stageInputs R k ∈ level R t.stageBound := by
  have hR (o : Ordinal.{u}) : R ∈ level R o := seed_subset_stage R o.toZFSet (parameter_mem_seed R)
  induction t with
  | reals => exact fun _ => hR 0
  | parameter => exact fun _ => hR 0
  | define o n p c ih =>
    intro k
    have hupper (i : Fin n) : (c i).stageBound ≤ (Construction.define o n p c).stageBound :=
      (Finset.le_sup (Finset.mem_univ i)).trans
        ((le_max_right o _).trans (le_of_lt (lt_add_one _)))
    cases k with
    | zero =>
      exact level_mem_level R ((le_max_left o _).trans_lt (lt_add_one _))
    | succ k =>
      unfold Construction.stageInputs
      simp only [Construction.inputData]
      by_cases h : (Nat.unpair k).1 < n
      · rw [dite_eq_left h]
        have hchild := level_mono R (hupper ⟨(Nat.unpair k).1,h⟩)
          (ih ⟨(Nat.unpair k).1,h⟩ (Nat.unpair k).2)
        unfold Construction.stageInputs at hchild
        cases hd : (c ⟨(Nat.unpair k).1,h⟩).inputData (Nat.unpair k).2 <;>
          simpa only [hd,ConstructionInput.prefix] using hchild
      · rw [dite_eq_right h]
        exact hR _

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_LevelInlinedDefinition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic
open SetDegreeDecoding PersistentRestrictions
universe u

theorem Construction.singleInputs_relative (t : Construction.{u}) (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (P : Oracle)
    (hP : P ∈ modelReals M) (hi : t.Indexed M) :
    ∀ i, t.singleInputs (groundReals M) P i ∈ relativeModel M (groundReals M) := by
  let R := groundReals M
  let N := relativeModel M R
  have hR := groundReals_mem M hM hT
  have hN := relativeModel_transitive M R hM
  have hp := relativeModel_pairing M R hM hT hR
  have hu := relativeModel_union M R hM hT hR
  have hpow := relativeModel_power_set M R hM hT hR
  have hs := relativeModel_bounded_separation M R hM hT hR
  have hinf := ground_relativeModel_infinity M hM hT
  have hw := ground_relativeModel_omega M hM hT
  intro i
  rcases i with _|_|_|_|_|i
  · exact (mem_relativeModel M R R hM hT hR).mpr (parameter_in_relativeModel M R hM hT)
  · exact (relativeModel_ground_reals M hM hT (realCode P) (realCode_subset P)).mpr hP
  · exact hw
  · exact additionSet_mem N hN hp hu hpow hs hinf
  · exact product_mem N hN hp hu hpow hs hw hw
  · have hid := t.inputData_indexed M hi i
    change t.stageInputs R i ∈ N
    unfold Construction.stageInputs
    cases hd : t.inputData i with
    | reals => exact (mem_relativeModel M R R hM hT hR).mpr (parameter_in_relativeModel M R hM hT)
    | realPath path => exact (mem_relativeModel M R R hM hT hR).mpr (parameter_in_relativeModel M R hM hT)
    | stage o =>
      rw [hd] at hid
      exact (mem_relativeModel M R _ hM hT hR).mpr (level_in_relativeModel M R hM hT o hid)

theorem Construction.inlined_at_level_oai (t : Construction.{u}) (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (P : Oracle)
    (hP : P ∈ modelReals M) (ht : t.Certified (groundReals M) P) (hi : t.Indexed M) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧
      t.value (groundReals M) P ∈ level (groundReals M) γ ∧
      (∀ i, t.singleInputs (groundReals M) P i ∈ level (groundReals M) γ) ∧
      ∀ z ∈ level (groundReals M) γ,
        t.singleMembership.Sat (level (groundReals M) γ : Set ZFSet)
          (cons z (t.singleInputs (groundReals M) P)) ↔ z ∈ t.value (groundReals M) P := by
  let R := groundReals M
  have hR := groundReals_mem M hM hT
  have hinputs := t.singleInputs_relative M hM hT P hP hi
  let e := cons (t.value R P) (t.singleInputs R P)
  have he (i : ℕ) (_hin : i < 6) : InRelativeModel M R (e i) := by
    cases i with
    | zero => exact t.value_in_relativeModel M R hM hT P ht hi
    | succ i => exact (mem_relativeModel M R _ hM hT hR).mp (hinputs i)
  obtain ⟨o,ho,hbound⟩ := finite_parameters_in_relative_level M R hM hT e 6 he
  let γ := max o t.stageBound
  have hγ : γ.toZFSet ∈ M := internal_ordinal_max M ho (t.stageBound_mem M hM hT hi)
  have hv : t.value R P ∈ level R γ := level_mono R (le_max_left _ _) (hbound 0 (by decide))
  have hin (i : ℕ) : t.singleInputs R P i ∈ level R γ := by
    by_cases hi5 : i < 5
    · exact level_mono R (le_max_left _ _) (hbound (i+1) (by omega))
    · obtain ⟨k,rfl⟩ : ∃ k, i = k+5 := ⟨i-5,by omega⟩
      change t.stageInputs R k ∈ level R γ
      exact level_mono R (le_max_right _ _) (t.stageInputs_bounded R k)
  refine ⟨γ,hγ,hv,hin,?_⟩
  intro z hz
  exact t.singleMembership_of_inputs (level R γ) R (level_transitive R γ) P ht hin hv z hz

end TuringRigidity.RelativeConstructible

end OAI
end

theorem solution.{u} : type_of% @OAI.TuringRigidity.RelativeConstructible.Construction.inlined_at_level_oai.{u} := @OAI.TuringRigidity.RelativeConstructible.Construction.inlined_at_level_oai.{u}
