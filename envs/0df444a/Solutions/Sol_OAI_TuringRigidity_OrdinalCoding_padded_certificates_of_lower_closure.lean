-- Prove2me | solution 1 for OAI.TuringRigidity.OrdinalCoding.padded_certificates_of_lower_closure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:07:50.422035+00:00
-- url     : https://prove2.me/submissions/85e4ec41-7b56-426c-b8ef-01838e77d977

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A008

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_FiniteStageSetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel
universe u

theorem pair_mem_level_succ (R : ZFSet.{u}) (a : Ordinal.{u})
    {x y : ZFSet.{u}} (hx : x ∈ level R a) (hy : y ∈ level R a) :
    ({x,y} : ZFSet.{u}) ∈ level R (a+1) := by
  rw [level_succ]
  exact pair_mem_definablePower _ _ _ hx hy

theorem orderedPair_mem_level_add_two (R : ZFSet.{u}) (a : Ordinal.{u})
    {x y : ZFSet.{u}} (hx : x ∈ level R a) (hy : y ∈ level R a) :
    ZFSet.pair x y ∈ level R (a+2) := by
  have hs : ({x} : ZFSet.{u}) ∈ level R (a+1) := by
    simpa using pair_mem_level_succ R a hx hx
  simpa only [ZFSet.pair,add_assoc,one_add_one_eq_two] using
    pair_mem_level_succ R (a+1) hs (pair_mem_level_succ R a hx hy)

theorem union_mem_level_succ (R : ZFSet.{u}) (a : Ordinal.{u})
    {x : ZFSet.{u}} (hx : x ∈ level R a) : ZFSet.sUnion x ∈ level R (a+1) := by
  rw [level_succ]
  exact union_mem_definablePower _ _ (level_transitive R a) hx

theorem iterUnion_mem_level_add (R : ZFSet.{u}) (a : Ordinal.{u})
    {x : ZFSet.{u}} (hx : x ∈ level R a) (n : ℕ) :
    iterUnion n x ∈ level R (a+n) := by
  induction n with
  | zero => simpa only [iterUnion,Nat.cast_zero,add_zero] using hx
  | succ n ih =>
    simpa only [iterUnion,Nat.cast_add,Nat.cast_one,add_assoc] using
      union_mem_level_succ R (a+n) ih

theorem orderedPair_mem_level_limit (R : ZFSet.{u}) (a : Ordinal.{u})
    (ha : Order.IsSuccLimit a) {x y : ZFSet.{u}}
    (hx : x ∈ level R a) (hy : y ∈ level R a) : ZFSet.pair x y ∈ level R a := by
  obtain ⟨i,hi,hx⟩ := (mem_level_limit R x a ha).mp hx
  obtain ⟨j,hj,hy⟩ := (mem_level_limit R y a ha).mp hy
  have h := orderedPair_mem_level_add_two R (max i j)
    (level_mono R (le_max_left i j) hx) (level_mono R (le_max_right i j) hy)
  have hlt := ha.succ_lt (ha.succ_lt (max_lt hi hj))
  apply level_mono R (show max i j + 2 ≤ a from ?_) h
  simpa only [Order.succ_eq_add_one,add_assoc,one_add_one_eq_two] using hlt.le

theorem insert_mem_level_succ (R : ZFSet.{u}) (a : Ordinal.{u})
    {x y : ZFSet.{u}} (hx : x ∈ level R a) (hy : y ∈ level R a) :
    insert x y ∈ level R (a+1) := by
  let A := level R a
  let p : ElementaryModel.SentenceForm := .disj (.equal 0 1) (.member 0 2)
  let e := BoundedSetTheory.cons x (fun _ => y)
  have h := separation_mem_definablePower A p e (fun i _ => by
    cases i; exact hx; exact hy)
  have heq : A.sep (fun z => p.Sat (A : Set ZFSet) (BoundedSetTheory.cons z e)) = insert x y := by
    apply ZFSet.ext; intro z
    simp only [ZFSet.mem_sep,ZFSet.mem_insert_iff,p,ElementaryModel.SentenceForm.sat_disj,
      ElementaryModel.SentenceForm.Sat,e,BoundedSetTheory.cons_zero,BoundedSetTheory.cons_succ]
    exact ⟨And.right,fun h => ⟨h.elim (fun h => h ▸ hx)
      (fun h => level_transitive R a y hy z h),h⟩⟩
  rw [heq] at h
  rwa [level_succ]

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

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_InternalHeightDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem internal_ordinal_downward (M : ZFSet.{u}) (hM : Transitive M)
    {a b : Ordinal.{u}} (hb : b.toZFSet ∈ M) (hab : a ≤ b) : a.toZFSet ∈ M := by
  rcases lt_or_eq_of_le hab with h|rfl
  · exact hM _ hb _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr h)
  · exact hb

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

theorem ProductCertificates.mono {M N : ZFSet.{u}} {a b : Ordinal.{u}}
    (h : ProductCertificates M a b) (hMN : M ⊆ N) : ProductCertificates N a b :=
  ⟨hMN h.1,hMN h.2.1,let ⟨f,hf,hc⟩ := h.2.2; ⟨f,hMN hf,hc⟩⟩

theorem ordinalProductAt_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (v a b : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (α β : Ordinal.{u}) (ha : e a = α.toZFSet) (hb : e b = β.toZFSet)
    (hc : ProductCertificates M α β) (hv : e v = (α*β).toZFSet) :
    (ordinalProductAt v a b).Sat (M : Set ZFSet) e := by
  rw [ordinalProductAt,SentenceForm.sat_rename]
  exact (productSentence_spec_of_certificate M hM
    (fun i => e (if i = 0 then v else if i = 1 then a else b)) (fun i => he _) α β ha hb
    hc.1 hc.2.1 hc.2.2).mpr hv

theorem OmegaPowerCertificates.mono {M N x : ZFSet.{u}}
    (h : OmegaPowerCertificates M x) (hMN : M ⊆ N) : OmegaPowerCertificates N x := by
  obtain ⟨hd,f,hf,r,hr,hg,hp⟩ := h
  refine ⟨hMN hd,f,hMN hf,r,hMN hr,⟨hg.1,hg.2.1,?_⟩,fun t ht => (hp t ht).mono hMN⟩
  intro t ht v hv hfv
  obtain ⟨A,hA,hs,ho,he⟩ := hg.2.2 t ht v hv hfv
  exact ⟨A,hMN hA,hs,ho,he⟩

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalPairCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
universe u
open Ordinal

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

theorem vectorCode_pos {n : ℕ} (v : Fin n → Ordinal.{u}) : 0 < vectorCode v := by
  cases n with
  | zero => exact zero_lt_one
  | succ n => exact (show 0 ≤ v 0 from zero_le).trans_lt (left_lt_pairCode _ _)

theorem padding_lt_paddedCode {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u}) :
    β < paddedCode v β := left_lt_pairCode _ _

theorem pairCode_isSuccLimit (x y : Ordinal.{u}) (hx : 0 < x) (hy : 0 < y) :
    Order.IsSuccLimit (pairCode x y) := by
  unfold pairCode
  split
  · exact Ordinal.isSuccLimit_add _ (Ordinal.isSuccLimit_opow_left
      Ordinal.isSuccLimit_omega0 (ne_of_gt hy))
  · exact Ordinal.isSuccLimit_add _ (Ordinal.isSuccLimit_opow_left
      Ordinal.isSuccLimit_omega0 (ne_of_gt hx))

theorem paddedCode_isSuccLimit {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hβ : 0 < β) : Order.IsSuccLimit (paddedCode v β) :=
  pairCode_isSuccLimit β (vectorCode v) hβ (vectorCode_pos v)

theorem finite_margin_lt_paddedCode {n : ℕ} (v : Fin n → Ordinal.{u}) (β c : Ordinal.{u})
    (hβ : 0 < β) (hc : c < paddedCode v β) (k : ℕ) :
    c + (k : Ordinal.{u}) < paddedCode v β := by
  induction k with
  | zero => simpa only [Nat.cast_zero,add_zero] using hc
  | succ k ih =>
    have h := (paddedCode_isSuccLimit v β hβ).succ_lt ih
    simpa only [Order.succ_eq_add_one,Nat.cast_add,Nat.cast_one,add_assoc] using h

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

end TuringRigidity.OrdinalCoding

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

theorem SumCertificates.mono {M N : ZFSet.{u}} {a b : Ordinal.{u}}
    (h : SumCertificates M a b) (hMN : M ⊆ N) : SumCertificates N a b :=
  ⟨hMN h.1,hMN h.2.1,let ⟨f,hf,hc⟩ := h.2.2; ⟨f,hMN hf,hc⟩⟩

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


end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_LimitOmegaGraphSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open OrdinalCoding
universe u


theorem omegaNextPairSentence_semantics (M : ZFSet.{u}) (hM : Transitive M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    omegaNextPairSentence.Sat (M : Set ZFSet) e ↔
      ∃ x ∈ M, ∃ y ∈ M, ∃ k ∈ M,
        (x.IsOrdinal ∧ k = insert x x ∧ e 0 = ZFSet.pair x y) ∧
        (codePowerAt 1 0).Sat (M : Set ZFSet) (cons k (cons y (cons x e))) := by
  change (∃ x ∈ M, ∃ y ∈ M, ∃ k ∈ M, _) ↔ _
  apply exists_congr; intro x
  apply and_congr_right; intro hx
  apply exists_congr; intro y
  apply and_congr_right; intro hy
  apply exists_congr; intro k
  apply and_congr_right; intro hk
  have hE : ∀ i, cons k (cons y (cons x e)) i ∈ M := by
    intro i; rcases i with _|_|_|i
    exact hk; exact hy; exact hx; exact he i
  rw [SentenceForm.Sat,bounded_sat,Formula.absolute _ M hM _ hE]
  simp only [Formula.Eval,eval_ordinalFormula,Formula.eval_successor,
    Formula.eval_orderedPair,cons_zero,cons_succ]

theorem omegaNextPairSentence_at_cut (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (a : Ordinal.{u}) (ha : Order.IsSuccLimit a)
    (hcut : ∀ c : Ordinal.{u}, c.toZFSet ∈ M ↔ c < a)
    (hpow : ∀ c < a, (Ordinal.omega0 ^ c).toZFSet ∈ M ∧ OmegaPowerCertificates M c.toZFSet)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    omegaNextPairSentence.Sat (M : Set ZFSet) e ↔
      ∃ c < a, e 0 = ZFSet.pair c.toZFSet (omegaNext c.toZFSet) := by
  rw [omegaNextPairSentence_semantics M hM e he]
  constructor
  · rintro ⟨x,hx,y,hy,k,hk,⟨ho,hkdef,hz⟩,hp⟩
    have hE : ∀ i, cons k (cons y (cons x e)) i ∈ M := by
      intro i; rcases i with _|_|_|i
      exact hk; exact hy; exact hx; exact he i
    have hv := (codePowerAt_sound M hM hω 1 0 _ hE hp).2
    change y = (Ordinal.omega0 ^ k.rank).toZFSet at hv
    have hsucc : k = (x.rank+1).toZFSet := by
      rw [Ordinal.toZFSet_add_one,ho.toZFSet_rank_eq,hkdef]
    rw [hsucc,Ordinal.rank_toZFSet] at hv
    refine ⟨x.rank,(hcut _).mp (ho.toZFSet_rank_eq.symm ▸ hx),?_⟩
    simpa only [ho.toZFSet_rank_eq,omegaNext] using hz.trans (congrArg (ZFSet.pair x) hv)
  · rintro ⟨c,hc,hz⟩
    have hs : c+1 < a := ha.succ_lt hc
    have hx := (hcut c).mpr hc
    have hk := (hcut (c+1)).mpr hs
    obtain ⟨hy,hcert⟩ := hpow (c+1) hs
    refine ⟨c.toZFSet,hx,(Ordinal.omega0 ^ (c+1)).toZFSet,hy,(c+1).toZFSet,hk,
      ⟨ZFSet.isOrdinal_toZFSet _,Ordinal.toZFSet_add_one c,?_⟩,?_⟩
    · simpa only [omegaNext,Ordinal.rank_toZFSet] using hz
    · apply codePowerAt_of_certificates M hM hω 1 0 _ (fun i => by
        rcases i with _|_|_|i
        exact hk; exact hy; exact hx; exact he i) hcert
      simp only [cons_zero,cons_succ,Ordinal.rank_toZFSet]

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ExactOmegaGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

theorem omegaGraph_of_exact_pairs (M d f : ZFSet.{u}) (hd : d.IsOrdinal)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (omegaNext x))
    (hval : ∀ x ∈ d, (Ordinal.omega0 ^ x.rank).toZFSet ∈ M) :
    OmegaGraph M d (iterUnion 2 f) f := by
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
    refine ⟨(Ordinal.omega0 ^ x.rank).toZFSet,
      hval x hx,?_,ZFSet.isOrdinal_toZFSet _,?_⟩
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

theorem OmegaGraph.union_value_mem {M d r f : ZFSet.{u}} (hg : OmegaGraph M d r f)
    {x : ZFSet.{u}} (hx : x ∈ d) : (Ordinal.omega0 ^ x.rank).toZFSet ∈ M := by
  obtain ⟨v,hv,hfv,_⟩ := hg.2.1.2 x hx
  obtain ⟨A,hA,hs,_,_⟩ := hg.2.2 x hx v hv hfv
  exact (omegaStageStep_exact hg hx hs) ▸ hA

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_LimitOmegaCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

theorem omega_graph_at_limit_successor (R : ZFSet.{u}) (a : Ordinal.{u})
    (ha : Order.IsSuccLimit a) (hheight : ordinalHeight (seed R) + a = a)
    (hω : ZFSet.omega.{u} ∈ level R a)
    (hpow : ∀ c < a, (Ordinal.omega0 ^ c).toZFSet ∈ level R a ∧
      OmegaPowerCertificates (level R a) c.toZFSet) :
    ∃ f ∈ level R (a+1), ∀ z, z ∈ f ↔
      ∃ x ∈ a.toZFSet, z = ZFSet.pair x (omegaNext x) := by
  let A := level R a
  have hcut (c : Ordinal.{u}) : c.toZFSet ∈ A ↔ c < a := by
    rw [ordinal_mem_level_iff,hheight]
  let f := A.sep (fun z => omegaNextPairSentence.Sat (A : Set ZFSet)
    (cons z (fun _ => ZFSet.omega)))
  have hf : f ∈ level R (a+1) := by
    rw [level_succ]
    exact separation_mem_definablePower A omegaNextPairSentence (fun _ => ZFSet.omega)
      (fun _ _ => hω)
  refine ⟨f,hf,?_⟩
  intro z
  change z ∈ A.sep _ ↔ _
  rw [ZFSet.mem_sep]
  constructor
  · rintro ⟨hz,hzspec⟩
    obtain ⟨c,hc,hz⟩ := (omegaNextPairSentence_at_cut A (level_transitive R a) hω a ha hcut hpow
      _ (fun i => by cases i; exact hz; exact hω)).mp hzspec
    exact ⟨c.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hc,hz⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
    have hy : omegaNext c.toZFSet ∈ A := by
      simpa only [omegaNext,Ordinal.rank_toZFSet] using (hpow (c+1) (ha.succ_lt hc)).1
    have hz := orderedPair_mem_level_limit R a ha ((hcut c).mpr hc) hy
    refine ⟨hz,(omegaNextPairSentence_at_cut A (level_transitive R a) hω a ha hcut hpow
      _ (fun i => by cases i; exact hz; exact hω)).mpr ⟨c,hc,rfl⟩⟩

theorem omega_certificates_at_limit_add_three (R : ZFSet.{u}) (a : Ordinal.{u})
    (ha : Order.IsSuccLimit a) (hheight : ordinalHeight (seed R) + a = a)
    (hω : ZFSet.omega.{u} ∈ level R a)
    (hpow : ∀ c < a, (Ordinal.omega0 ^ c).toZFSet ∈ level R a ∧
      OmegaPowerCertificates (level R a) c.toZFSet) :
    OmegaPowerCertificates (level R (a+3)) a.toZFSet := by
  obtain ⟨f,hf,hexact⟩ := omega_graph_at_limit_successor R a ha hheight hω hpow
  have h01 : a ≤ a+1 := le_self_add
  have h13 : a+1 ≤ a+3 := add_le_add le_rfl (by norm_num : (1 : Ordinal.{u}) ≤ 3)
  have h03 := h01.trans h13
  have hd : a.toZFSet ∈ level R (a+3) := by
    apply level_mono R h13
    apply (ordinal_mem_level_iff R (a+1) a).mpr
    rw [← add_assoc,hheight]
    exact lt_add_one a
  have hr : iterUnion 2 f ∈ level R (a+3) := by
    simpa only [Nat.cast_ofNat,add_assoc,show (1 : Ordinal.{u})+2=3 by norm_num] using
      iterUnion_mem_level_add R (a+1) hf 2
  refine ⟨hd,f,level_mono R h13 hf,_,hr,
    omegaGraph_of_exact_pairs _ _ f (ZFSet.isOrdinal_toZFSet a) hexact ?_,?_⟩
  · intro x hx
    obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
    rw [Ordinal.rank_toZFSet]
    exact level_mono R h03 (hpow c hc).1
  · intro x hx
    obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
    obtain ⟨_,g,hg,r,hr,hgraph,hprod⟩ := (hpow (c+1) (ha.succ_lt hc)).2
    exact (hprod c.toZFSet (Ordinal.toZFSet_mem_toZFSet_iff.mpr (lt_add_one c))).mono
      (level_mono R h03)

end TuringRigidity.OrdinalArithmetic

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_SuccessorOmegaCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

theorem omega_certificates_successor_add_five (R : ZFSet.{u}) (γ a : Ordinal.{u})
    (hc : OmegaPowerCertificates (level R γ) a.toZFSet)
    (ha : (Ordinal.omega0 ^ a).toZFSet ∈ level R γ)
    (hs : (Ordinal.omega0 ^ (a+1)).toZFSet ∈ level R γ)
    (hp : ProductCertificates (level R γ) (Ordinal.omega0 ^ a) Ordinal.omega0) :
    OmegaPowerCertificates (level R (γ+5)) (a+1).toZFSet := by
  obtain ⟨hd,f,hf,r,hr,hg,hprod⟩ := hc
  have h02 : γ ≤ γ+2 := le_self_add
  have h05 : γ ≤ γ+5 := le_self_add
  have h15 : γ+1 ≤ γ+5 := add_le_add le_rfl (by norm_num)
  have h35 : γ+3 ≤ γ+5 := add_le_add le_rfl (by exact_mod_cast (by decide : (3 : ℕ) ≤ 5))
  let g := insert (ZFSet.pair a.toZFSet (omegaNext a.toZFSet)) f
  have hy : omegaNext a.toZFSet ∈ level R γ := by
    simpa only [omegaNext,Ordinal.rank_toZFSet] using hs
  have hgM : g ∈ level R (γ+3) := by
    have h := insert_mem_level_succ R (γ+2)
      (orderedPair_mem_level_add_two R γ hd hy) (level_mono R h02 hf)
    simpa only [add_assoc,show (2 : Ordinal.{u})+1=3 by norm_num] using h
  have hexact (z : ZFSet.{u}) : z ∈ g ↔
      ∃ x ∈ (a+1).toZFSet, z = ZFSet.pair x (omegaNext x) := by
    rw [Ordinal.toZFSet_add_one]
    change z ∈ insert _ f ↔ _
    rw [ZFSet.mem_insert_iff,hg.mem_iff]
    constructor
    · rintro (hz|⟨x,hx,hz⟩)
      · exact ⟨a.toZFSet,ZFSet.mem_insert _ _,hz⟩
      · exact ⟨x,ZFSet.mem_insert_of_mem _ hx,hz⟩
    · rintro ⟨x,hx,hz⟩
      rcases ZFSet.mem_insert_iff.mp hx with rfl|hx
      · exact Or.inl hz
      · exact Or.inr ⟨x,hx,hz⟩
  have hdom : (a+1).toZFSet ∈ level R (γ+5) := by
    rw [Ordinal.toZFSet_add_one]
    exact level_mono R h15 (insert_mem_level_succ R γ hd hd)
  have hrange : iterUnion 2 g ∈ level R (γ+5) := by
    simpa only [Nat.cast_ofNat,add_assoc,show (3 : Ordinal.{u})+2=5 by norm_num] using
      iterUnion_mem_level_add R (γ+3) hgM 2
  refine ⟨hdom,g,level_mono R h35 hgM,_,hrange,
    omegaGraph_of_exact_pairs _ _ g (ZFSet.isOrdinal_toZFSet _) hexact ?_,?_⟩
  · intro x hx
    rw [Ordinal.toZFSet_add_one] at hx
    rcases ZFSet.mem_insert_iff.mp hx with rfl|hx
    · simpa only [Ordinal.rank_toZFSet] using level_mono R h05 ha
    · exact level_mono R h05 (hg.union_value_mem hx)
  · intro x hx
    rw [Ordinal.toZFSet_add_one] at hx
    rcases ZFSet.mem_insert_iff.mp hx with rfl|hx
    · simpa only [Ordinal.rank_toZFSet] using hp.mono (level_mono R h05)
    · exact (hprod x hx).mono (level_mono R h05)

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_PaddedOmegaBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

theorem offset_absorbed_above (s a b : Ordinal.{u}) (ha : s+a=a) (hab : a ≤ b) : s+b=b := by
  calc
    s+b = s+(a+(b-a)) := by rw [Ordinal.add_sub_cancel_of_le hab]
    _ = b := by rw [← add_assoc,ha,Ordinal.add_sub_cancel_of_le hab]

theorem heightDomainIndex_of_absorbed (a : Ordinal.{u}) (ha : realSeedOffset+a=a) :
    heightDomainIndex a = a+1 := by
  rw [heightDomainIndex,Ordinal.sub_eq_of_add_eq ha]

theorem padded_omega_boundary_certificates (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hβ : Order.IsSuccLimit β) (hoff : realSeedOffset+β=β) (hv : vectorCode v ≤ β)
    (hpow : ∀ c < β, (Ordinal.omega0 ^ c).toZFSet ∈ level (groundReals M) β ∧
      OmegaPowerCertificates (level (groundReals M) β) c.toZFSet)
    (hprod : ProductCertificates
      (level (groundReals M) (Ordinal.omega0 ^ (β+1)+1)) (Ordinal.omega0 ^ β) Ordinal.omega0) :
    OmegaPowerCertificates
      (level (groundReals M) (heightDomainIndex (paddedCode v β))) (β+1).toZFSet := by
  let R := groundReals M
  let b := Ordinal.omega0 ^ (β+1)
  have hβpos : 0 < β := Ordinal.natCast_lt_of_isSuccLimit hβ 0
  have hβb : β < b := (lt_add_one β).trans_le (Ordinal.right_le_opow (β+1) Ordinal.one_lt_omega0)
  have hbLimit : Order.IsSuccLimit b := Ordinal.isSuccLimit_opow_left
    Ordinal.isSuccLimit_omega0 (ne_of_gt (hβpos.trans (lt_add_one β)))
  have hβ3 : β+3 < b := by
    have h := hbLimit.succ_lt (hbLimit.succ_lt (hbLimit.succ_lt hβb))
    simpa only [Order.succ_eq_add_one,add_assoc,one_add_one_eq_two,
      show (2 : Ordinal.{u})+1=3 by norm_num] using h
  have hheight : ordinalHeight (seed R)+β=β := by
    rw [ground_seed_offset M hM hT]; exact hoff
  have hc := omega_certificates_at_limit_add_three R β hβ hheight
    (ground_level_omega_mem M hM hT β) hpow
  have hbabs := offset_absorbed_above realSeedOffset β b hoff hβb.le
  have hbM : b.toZFSet ∈ level R (b+1) := by
    apply (ordinal_mem_level_iff R (b+1) b).mpr
    rw [ground_seed_offset M hM hT,← add_assoc,hbabs]
    exact lt_add_one b
  have hpM : (Ordinal.omega0 ^ β).toZFSet ∈ level R (b+1) :=
    internal_ordinal_downward _ (level_transitive R (b+1)) hbM
      (Ordinal.opow_le_opow_right Ordinal.omega0_pos (le_of_lt (lt_add_one β)))
  have hs := omega_certificates_successor_add_five R (b+1) β
    (hc.mono (level_mono R (hβ3.le.trans le_self_add))) hpM hbM hprod
  have hbcode : b < paddedCode v β := by
    change b < pairCode β (vectorCode v)
    rw [pairCode,ite_eq_left hv]
    simpa only [add_zero] using (add_lt_add_iff_left b).mpr
      (Ordinal.opow_pos (vectorCode v) Ordinal.omega0_pos)
  have hcodeabs := offset_absorbed_above realSeedOffset β (paddedCode v β) hoff
    (padding_lt_paddedCode v β).le
  rw [heightDomainIndex_of_absorbed _ hcodeabs]
  apply hs.mono (level_mono R ?_)
  have hmargin := finite_margin_lt_paddedCode v β b hβpos hbcode 6
  have hsum : b+1+5 = b+6 := by
    rw [add_assoc]; congr 1; norm_num
  rw [hsum]
  exact hmargin.le.trans le_self_add

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_TrimmedOrderDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

theorem defined_set_at_successor (R : ZFSet.{u}) (γ : Ordinal.{u})
    (p : SentenceForm) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ level R γ)
    (s : ZFSet.{u}) (hsub : s ⊆ level R γ)
    (hs : ∀ z ∈ level R γ, p.Sat (level R γ : Set ZFSet) (cons z e) ↔ z ∈ s) :
    s ∈ level R (γ+1) := by
  have h := separation_mem_definablePower (level R γ) p e (fun i _ => he i)
  have eq : (level R γ).sep (fun z => p.Sat (level R γ : Set ZFSet) (cons z e)) = s := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep]
    exact ⟨fun ⟨hz,hp⟩ => (hs z hz).mp hp,fun hz => ⟨hsub hz,(hs z (hsub hz)).mpr hz⟩⟩
  rw [eq] at h
  rwa [level_succ]

theorem product_domain_subset_limit (R : ZFSet.{u}) (γ : Ordinal.{u})
    (hγ : Order.IsSuccLimit γ) {a b : ZFSet.{u}}
    (ha : a ∈ level R γ) (hb : b ∈ level R γ) : ZFSet.prod b a ⊆ level R γ := by
  intro z hz
  obtain ⟨s,hs,t,ht,rfl⟩ := ZFSet.mem_prod.mp hz
  exact orderedPair_mem_level_limit R γ hγ
    (level_transitive R γ _ hb _ hs) (level_transitive R γ _ ha _ ht)

theorem product_domain_at_limit_successor (R : ZFSet.{u}) (γ : Ordinal.{u})
    (hγ : Order.IsSuccLimit γ) {a b : ZFSet.{u}}
    (ha : a ∈ level R γ) (hb : b ∈ level R γ) : ZFSet.prod b a ∈ level R (γ+1) := by
  let e := cons a (fun _ => b)
  have he (i : ℕ) : e i ∈ level R γ := by cases i; exact ha; exact hb
  apply defined_set_at_successor R γ trimmedProductDomainSentence e he _
    (product_domain_subset_limit R γ hγ ha hb)
  intro z hz
  rw [trimmedProductDomainSentence,bounded_sat,Formula.absolute _ _ (level_transitive R γ) _
    (fun i => by cases i; exact hz; exact he _)]
  simp only [Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e,ZFSet.mem_prod]

theorem product_relation_at_limit_successor (R : ZFSet.{u}) (γ : Ordinal.{u})
    (hγ : Order.IsSuccLimit γ) {a b : ZFSet.{u}}
    (ha : a ∈ level R γ) (hb : b ∈ level R γ) : productRelation a b ∈ level R (γ+1) := by
  let A := level R γ
  let e := cons a (fun _ => b)
  have he (i : ℕ) : e i ∈ A := by cases i; exact ha; exact hb
  have hd := product_domain_subset_limit R γ hγ ha hb
  have hsub : productRelation a b ⊆ A := by
    intro z hz
    obtain ⟨x,hx,y,hy,rfl⟩ := ZFSet.mem_prod.mp (productRelation_on a b hz)
    exact orderedPair_mem_level_limit R γ hγ (hd hx) (hd hy)
  apply defined_set_at_successor R γ trimmedProductRelationSentence e he _ hsub
  intro z hz
  change (∃ x ∈ A, ∃ y ∈ A, (fromBounded _).Sat _ (cons y (cons x (cons z e)))) ↔ _
  have hspec (x y : ZFSet.{u}) (hx : x ∈ A) (hy : y ∈ A) :
      (fromBounded (.conj (.orderedPair 2 1 0) (productLessFormula 3 4 1 0))).Sat
        (A : Set ZFSet) (cons y (cons x (cons z e))) ↔
          z = ZFSet.pair x y ∧ ProductLess a b x y := by
    rw [bounded_sat,Formula.absolute _ A (level_transitive R γ) _ (fun i => by
      rcases i with _|_|_|i; exact hy; exact hx; exact hz; exact he i)]
    simp only [Formula.Eval,Formula.eval_orderedPair,productLessFormula_eval,cons_zero,cons_succ,e]
  constructor
  · rintro ⟨x,hx,y,hy,h⟩
    obtain ⟨rfl,hless⟩ := (hspec x y hx hy).mp h
    have hkeep := hless
    obtain ⟨s,hs,t,ht,v,hv,w,hw,hx',hy',_⟩ := hless
    exact (pair_mem_productRelation a b x y).mpr
      ⟨ZFSet.mem_prod.mpr ⟨s,hs,t,ht,hx'⟩,ZFSet.mem_prod.mpr ⟨v,hv,w,hw,hy'⟩,hkeep⟩
  · intro h
    obtain ⟨x,hx,y,hy,rfl⟩ := ZFSet.mem_prod.mp (productRelation_on a b h)
    exact ⟨x,hd hx,y,hd hy,(hspec x y (hd hx) (hd hy)).mpr
      ⟨rfl,((pair_mem_productRelation a b x y).mp h).2.2⟩⟩

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_TrimmedPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

theorem order_certificate_of_exact_pairs (d r f : ZFSet.{u}) (o : Ordinal.{u})
    (j : ZFSet.{u} → ZFSet.{u})
    (hj : ∀ x ∈ d, j x ∈ o.toZFSet)
    (hs : ∀ z ∈ o.toZFSet, ∃ x ∈ d, j x = z)
    (he : ∀ x ∈ d, ∀ y ∈ d, ZFSet.pair x y ∈ r ↔ j x ∈ j y)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (j x)) :
    OrderTypeCertificate d r o.toZFSet f := by
  have pair (x : ZFSet.{u}) (hx : x ∈ d) := (hf _).mpr ⟨x,hx,rfl⟩
  have eq (x z : ZFSet.{u}) (h : ZFSet.pair x z ∈ f) : z = j x := by
    obtain ⟨y,_,hh⟩ := (hf _).mp h
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hh
    rfl
  refine ⟨ZFSet.isOrdinal_toZFSet _,⟨fun _ h => h,fun _ _ _ h _ => h,?_,?_,?_⟩,?_⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := (hf z).mp hz
    exact ⟨x,hx,j x,hj x hx,rfl⟩
  · intro x hx
    exact ⟨j x,hj x hx,pair x hx,fun z _ hz => eq x z hz⟩
  · intro x hx v _ hxv
    rw [eq x v hxv]
    constructor
    · intro z hz
      obtain ⟨y,hy,rfl⟩ := hs z ((ZFSet.isOrdinal_toZFSet o).subset_of_mem (hj x hx) hz)
      exact ⟨y,hy,(he y hy x hx).mpr hz,pair y hy⟩
    · intro y hy hyx z _ hyz
      rw [eq y z hyz]
      exact (he y hy x hx).mp hyx
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := hs z hz
    exact ⟨x,hx,pair x hx⟩

theorem presentation_graph_at_limit_successor (R : ZFSet.{u}) (γ : Ordinal.{u})
    (hγ : Order.IsSuccLimit γ) (d r : ZFSet.{u}) (o : Ordinal.{u})
    (j : ZFSet.{u} → ZFSet.{u}) (hd : d ⊆ level R γ)
    (hjA : ∀ x ∈ d, j x ∈ level R γ)
    (hj : ∀ x ∈ d, j x ∈ o.toZFSet)
    (hs : ∀ z ∈ o.toZFSet, ∃ x ∈ d, j x = z)
    (he : ∀ x ∈ d, ∀ y ∈ d, ZFSet.pair x y ∈ r ↔ j x ∈ j y)
    (p : SentenceForm) (e : ℕ → ZFSet.{u}) (henv : ∀ i, e i ∈ level R γ)
    (hp : ∀ z ∈ level R γ, p.Sat (level R γ : Set ZFSet) (cons z e) ↔
      ∃ x ∈ d, z = ZFSet.pair x (j x)) :
    ∃ f ∈ level R (γ+1), OrderTypeCertificate d r o.toZFSet f := by
  let A := level R γ
  let f := A.sep (fun z => p.Sat (A : Set ZFSet) (cons z e))
  have hf : f ∈ level R (γ+1) := by
    rw [level_succ]
    exact separation_mem_definablePower A p e (fun i _ => henv i)
  have hexact (z : ZFSet.{u}) : z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (j x) := by
    change z ∈ A.sep _ ↔ _
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz,h⟩; exact (hp z hz).mp h
    · rintro ⟨x,hx,rfl⟩
      have hz := orderedPair_mem_level_limit R γ hγ (hd hx) (hjA x hx)
      exact ⟨hz,(hp _ hz).mpr ⟨x,hx,rfl⟩⟩
  exact ⟨f,hf,order_certificate_of_exact_pairs d r f o j hj hs he hexact⟩

end TuringRigidity.RelationCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_TrimmedProductGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalCoding
universe u

theorem trimmedProductGraphSentence_semantics (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) :
    trimmedProductGraphSentence.Sat (A : Set ZFSet) e ↔
      ∃ s ∈ A, ∃ t ∈ A, ∃ x ∈ A, ∃ y ∈ A, ∃ v ∈ A,
        (s ∈ e 2 ∧ t ∈ e 1 ∧ x = ZFSet.pair s t ∧ e 0 = ZFSet.pair x y) ∧
        (ordinalProductAt 0 6 4).Sat (A : Set ZFSet) (cons v (cons y (cons x (cons t (cons s e))))) ∧
        (codeSumAt 1 0 3).Sat (A : Set ZFSet) (cons v (cons y (cons x (cons t (cons s e))))) := by
  change (∃ s ∈ A, ∃ t ∈ A, ∃ x ∈ A, ∃ y ∈ A, ∃ v ∈ A, _) ↔ _
  apply exists_congr; intro s; apply and_congr_right; intro hs
  apply exists_congr; intro t; apply and_congr_right; intro ht
  apply exists_congr; intro x; apply and_congr_right; intro hx
  apply exists_congr; intro y; apply and_congr_right; intro hy
  apply exists_congr; intro v; apply and_congr_right; intro hv
  have hE : ∀ i, cons v (cons y (cons x (cons t (cons s e)))) i ∈ A := by
    intro i; rcases i with _|_|_|_|_|i
    exact hv; exact hy; exact hx; exact ht; exact hs; exact he i
  rw [SentenceForm.Sat,bounded_sat,Formula.absolute _ A hA _ hE]
  simp only [Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,SentenceForm.Sat]

theorem trimmedProductGraphSentence_spec (R : ZFSet.{u}) (γ a b : Ordinal.{u})
    (hγ : Order.IsSuccLimit γ) (hω : ZFSet.omega.{u} ∈ level R γ)
    (ha : a.toZFSet ∈ level R γ) (hb : b.toZFSet ∈ level R γ)
    (hlocal : ∀ s < b, (a*s).toZFSet ∈ level R γ ∧
      ProductCertificates (level R γ) a s ∧ ∀ t < a,
        (a*s+t).toZFSet ∈ level R γ ∧ SumCertificates (level R γ) (a*s) t)
    (z : ZFSet.{u}) (hz : z ∈ level R γ) :
    trimmedProductGraphSentence.Sat (level R γ : Set ZFSet)
      (cons z (cons a.toZFSet (fun _ => b.toZFSet))) ↔
        ∃ x ∈ ZFSet.prod b.toZFSet a.toZFSet, z = ZFSet.pair x (productValue a x) := by
  let A := level R γ
  let e := cons z (cons a.toZFSet (fun _ => b.toZFSet))
  have he (i : ℕ) : e i ∈ A := by rcases i with _|_|i; exact hz; exact ha; exact hb
  rw [trimmedProductGraphSentence_semantics A (level_transitive R γ) e he]
  constructor
  · rintro ⟨s,hs,t,ht,x,hx,y,hy,v,hv,⟨hsb,hta,hxdef,hzdef⟩,hp,hq⟩
    change s ∈ b.toZFSet at hsb
    obtain ⟨s,hsb,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hsb
    have hsb := Ordinal.toZFSet_mem_toZFSet_iff.mp hsb
    change t ∈ a.toZFSet at hta
    obtain ⟨t,hta,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hta
    have hta := Ordinal.toZFSet_mem_toZFSet_iff.mp hta
    have hE : ∀ i, cons v (cons y (cons x (cons t.toZFSet (cons s.toZFSet e)))) i ∈ A := by
      intro i; rcases i with _|_|_|_|_|i
      exact hv; exact hy; exact hx; exact ht; exact hs; exact he i
    have hvdef : v = (a*s).toZFSet := by
      rw [ordinalProductAt,SentenceForm.sat_rename] at hp
      exact productSentence_sound A (level_transitive R γ) _ (fun i => hE _) a s rfl rfl hp
    have hydef : y = (a*s+t).toZFSet :=
      codeSumAt_sound A (level_transitive R γ) 1 0 3 _ hE (a*s) t hvdef rfl hq
    refine ⟨x,ZFSet.mem_prod.mpr ⟨s.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hsb,
      t.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hta,hxdef⟩,?_⟩
    change z = ZFSet.pair x y at hzdef
    rw [hzdef,hydef,hxdef,productValue_pair,Ordinal.rank_toZFSet,Ordinal.rank_toZFSet]
  · rintro ⟨x,hxd,hzdef⟩
    obtain ⟨s,hsb,t,hta,rfl⟩ := ZFSet.mem_prod.mp hxd
    change s ∈ b.toZFSet at hsb
    obtain ⟨s,hsb,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hsb
    have hsb := Ordinal.toZFSet_mem_toZFSet_iff.mp hsb
    change t ∈ a.toZFSet at hta
    obtain ⟨t,hta,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hta
    have hta := Ordinal.toZFSet_mem_toZFSet_iff.mp hta
    have hs := level_transitive R γ _ hb _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr hsb)
    have ht := level_transitive R γ _ ha _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr hta)
    have hx := orderedPair_mem_level_limit R γ hγ hs ht
    obtain ⟨hv,hp,hrest⟩ := hlocal s hsb
    obtain ⟨hy,hq⟩ := hrest t hta
    let E := cons (a*s).toZFSet (cons (a*s+t).toZFSet
      (cons (ZFSet.pair s.toZFSet t.toZFSet) (cons t.toZFSet (cons s.toZFSet e))))
    have hE (i : ℕ) : E i ∈ A := by
      rcases i with _|_|_|_|_|i
      exact hv; exact hy; exact hx; exact ht; exact hs; exact he i
    refine ⟨s.toZFSet,hs,t.toZFSet,ht,_,hx,(a*s+t).toZFSet,hy,(a*s).toZFSet,hv,
      ⟨Ordinal.toZFSet_mem_toZFSet_iff.mpr hsb,Ordinal.toZFSet_mem_toZFSet_iff.mpr hta,rfl,?_⟩,?_,?_⟩
    · simpa only [e,cons_zero,productValue_pair,Ordinal.rank_toZFSet] using hzdef
    · exact ordinalProductAt_of_certificates A (level_transitive R γ) 0 6 4 E hE a s rfl rfl hp rfl
    · exact codeSumAt_of_certificates A (level_transitive R γ) hω 1 0 3 E hE (a*s) t rfl rfl hq rfl

theorem product_certificates_at_limit_successor (R : ZFSet.{u}) (γ a b : Ordinal.{u})
    (hγ : Order.IsSuccLimit γ) (hω : ZFSet.omega.{u} ∈ level R γ)
    (ha : a.toZFSet ∈ level R γ) (hb : b.toZFSet ∈ level R γ)
    (hlocal : ∀ s < b, (a*s).toZFSet ∈ level R γ ∧
      ProductCertificates (level R γ) a s ∧ ∀ t < a,
        (a*s+t).toZFSet ∈ level R γ ∧ SumCertificates (level R γ) (a*s) t) :
    ProductCertificates (level R (γ+1)) a b := by
  refine ⟨product_domain_at_limit_successor R γ hγ ha hb,
    product_relation_at_limit_successor R γ hγ ha hb,?_⟩
  apply presentation_graph_at_limit_successor R γ hγ _ _ (a*b) (productValue a)
    (product_domain_subset_limit R γ hγ ha hb) ?_
    (productValue_mem a b) (productValue_surjective a b) (productValue_relation a b)
    trimmedProductGraphSentence (cons a.toZFSet (fun _ => b.toZFSet))
    (fun i => by cases i; exact ha; exact hb)
  · exact trimmedProductGraphSentence_spec R γ a b hγ hω ha hb hlocal
  · intro x hx
    obtain ⟨s,hs,t,ht,rfl⟩ := ZFSet.mem_prod.mp hx
    obtain ⟨s,hs,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hs
    obtain ⟨t,ht,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
    have hs := Ordinal.toZFSet_mem_toZFSet_iff.mp hs
    have ht := Ordinal.toZFSet_mem_toZFSet_iff.mp ht
    simpa only [productValue_pair,Ordinal.rank_toZFSet] using ((hlocal s hs).2.2 t ht).1

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_TrimmedSumDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

theorem sum_domain_subset_limit (R : ZFSet.{u}) (γ : Ordinal.{u})
    (hγ : Order.IsSuccLimit γ) {a b : ZFSet.{u}}
    (ha : a ∈ level R γ) (hb : b ∈ level R γ)
    (h0 : (∅ : ZFSet.{u}) ∈ level R γ) (h1 : ({∅} : ZFSet.{u}) ∈ level R γ) :
    sumDomain a b ⊆ level R γ := by
  intro z hz
  rcases (mem_sumDomain a b z).mp hz with ⟨s,hs,rfl⟩|⟨s,hs,rfl⟩
  · exact orderedPair_mem_level_limit R γ hγ h0 (level_transitive R γ _ ha _ hs)
  · exact orderedPair_mem_level_limit R γ hγ h1 (level_transitive R γ _ hb _ hs)

theorem sum_domain_at_limit_successor (R : ZFSet.{u}) (γ : Ordinal.{u})
    (hγ : Order.IsSuccLimit γ) {a b : ZFSet.{u}}
    (ha : a ∈ level R γ) (hb : b ∈ level R γ)
    (h0 : (∅ : ZFSet.{u}) ∈ level R γ) (h1 : ({∅} : ZFSet.{u}) ∈ level R γ) :
    sumDomain a b ∈ level R (γ+1) := by
  let e := cons a (cons b (cons ∅ (fun _ => {∅})))
  have he (i : ℕ) : e i ∈ level R γ := by
    rcases i with _|_|_|i; exact ha; exact hb; exact h0; exact h1
  apply defined_set_at_successor R γ trimmedSumDomainSentence e he _
    (sum_domain_subset_limit R γ hγ ha hb h0 h1)
  intro z hz
  rw [trimmedSumDomainSentence,bounded_sat,Formula.absolute _ _ (level_transitive R γ) _
    (fun i => by cases i; exact hz; exact he _)]
  simp only [Formula.eval_disj,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e,
    mem_sumDomain,leftNode,rightNode]

theorem sum_relation_at_limit_successor (R : ZFSet.{u}) (γ : Ordinal.{u})
    (hγ : Order.IsSuccLimit γ) {a b : ZFSet.{u}}
    (ha : a ∈ level R γ) (hb : b ∈ level R γ)
    (h0 : (∅ : ZFSet.{u}) ∈ level R γ) (h1 : ({∅} : ZFSet.{u}) ∈ level R γ) :
    sumRelation a b ∈ level R (γ+1) := by
  let A := level R γ
  let e := cons a (cons b (cons ∅ (fun _ => {∅})))
  have he (i : ℕ) : e i ∈ A := by
    rcases i with _|_|_|i; exact ha; exact hb; exact h0; exact h1
  have hd := sum_domain_subset_limit R γ hγ ha hb h0 h1
  have hsub : sumRelation a b ⊆ A := by
    intro z hz
    obtain ⟨x,hx,y,hy,rfl⟩ := ZFSet.mem_prod.mp (sumRelation_on a b hz)
    exact orderedPair_mem_level_limit R γ hγ (hd hx) (hd hy)
  apply defined_set_at_successor R γ trimmedSumRelationSentence e he _ hsub
  intro z hz
  change (∃ x ∈ A, ∃ y ∈ A, (fromBounded _).Sat _ (cons y (cons x (cons z e)))) ↔ _
  have hspec (x y : ZFSet.{u}) (hx : x ∈ A) (hy : y ∈ A) :
      (fromBounded (.conj (.orderedPair 2 1 0) (sumLessFormula 3 4 5 6 1 0))).Sat
        (A : Set ZFSet) (cons y (cons x (cons z e))) ↔
          z = ZFSet.pair x y ∧ SumLess a b x y := by
    rw [bounded_sat,Formula.absolute _ A (level_transitive R γ) _ (fun i => by
      rcases i with _|_|_|i; exact hy; exact hx; exact hz; exact he i)]
    simp only [Formula.Eval,Formula.eval_orderedPair]
    rw [sumLessFormula_eval _ _ _ _ _ _ _ rfl rfl]
    rfl
  constructor
  · rintro ⟨x,hx,y,hy,h⟩
    obtain ⟨rfl,hless⟩ := (hspec x y hx hy).mp h
    have hkeep := hless
    have hxy : x ∈ sumDomain a b ∧ y ∈ sumDomain a b := by
      rcases hless with ⟨s,hs,t,ht,rfl,rfl,_⟩|⟨s,hs,t,ht,rfl,rfl⟩|⟨s,hs,t,ht,rfl,rfl,_⟩
      · exact ⟨(mem_sumDomain _ _ _).mpr (Or.inl ⟨s,hs,rfl⟩),
          (mem_sumDomain _ _ _).mpr (Or.inl ⟨t,ht,rfl⟩)⟩
      · exact ⟨(mem_sumDomain _ _ _).mpr (Or.inl ⟨s,hs,rfl⟩),
          (mem_sumDomain _ _ _).mpr (Or.inr ⟨t,ht,rfl⟩)⟩
      · exact ⟨(mem_sumDomain _ _ _).mpr (Or.inr ⟨s,hs,rfl⟩),
          (mem_sumDomain _ _ _).mpr (Or.inr ⟨t,ht,rfl⟩)⟩
    exact (pair_mem_sumRelation a b x y).mpr ⟨hxy.1,hxy.2,hkeep⟩
  · intro h
    obtain ⟨x,hx,y,hy,rfl⟩ := ZFSet.mem_prod.mp (sumRelation_on a b h)
    exact ⟨x,hd hx,y,hd hy,(hspec x y (hd hx) (hd hy)).mpr
      ⟨rfl,((pair_mem_sumRelation a b x y).mp h).2.2⟩⟩

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_TrimmedSumGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalCoding
universe u

theorem trimmedSumGraphSentence_semantics (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) :
    trimmedSumGraphSentence.Sat (A : Set ZFSet) e ↔
      ∃ t ∈ A, ∃ x ∈ A, ∃ y ∈ A,
        (t ∈ e 1 ∧ x = ZFSet.pair (e 3) t ∧ e 0 = ZFSet.pair x y ∧ y = t) ∨
        ((t ∈ e 2 ∧ x = ZFSet.pair (e 4) t ∧ e 0 = ZFSet.pair x y) ∧
          (codeSumAt 0 4 2).Sat (A : Set ZFSet) (cons y (cons x (cons t e)))) := by
  change (∃ t ∈ A, ∃ x ∈ A, ∃ y ∈ A, _) ↔ _
  apply exists_congr; intro t; apply and_congr_right; intro ht
  apply exists_congr; intro x; apply and_congr_right; intro hx
  apply exists_congr; intro y; apply and_congr_right; intro hy
  have hE : ∀ i, cons y (cons x (cons t e)) i ∈ A := by
    intro i; rcases i with _|_|_|i; exact hy; exact hx; exact ht; exact he i
  rw [SentenceForm.sat_disj,SentenceForm.Sat]
  simp only [bounded_sat,Formula.absolute _ A hA _ hE,Formula.Eval,
    Formula.eval_orderedPair,cons_zero,cons_succ]

theorem trimmedSumGraphSentence_spec (R : ZFSet.{u}) (γ a b : Ordinal.{u})
    (hγ : Order.IsSuccLimit γ) (hω : ZFSet.omega.{u} ∈ level R γ)
    (ha : a.toZFSet ∈ level R γ) (hb : b.toZFSet ∈ level R γ)
    (h0 : (∅ : ZFSet.{u}) ∈ level R γ) (h1 : ({∅} : ZFSet.{u}) ∈ level R γ)
    (hlocal : ∀ t < b, (a+t).toZFSet ∈ level R γ ∧ SumCertificates (level R γ) a t)
    (z : ZFSet.{u}) (hz : z ∈ level R γ) :
    trimmedSumGraphSentence.Sat (level R γ : Set ZFSet)
      (cons z (cons a.toZFSet (cons b.toZFSet (cons ∅ (fun _ => {∅}))))) ↔
        ∃ x ∈ sumDomain a.toZFSet b.toZFSet, z = ZFSet.pair x (sumValue a x) := by
  let A := level R γ
  let e := cons z (cons a.toZFSet (cons b.toZFSet (cons ∅ (fun _ => {∅}))))
  have he (i : ℕ) : e i ∈ A := by
    rcases i with _|_|_|_|i; exact hz; exact ha; exact hb; exact h0; exact h1
  rw [trimmedSumGraphSentence_semantics A (level_transitive R γ) e he]
  constructor
  · rintro ⟨t,ht,x,hx,y,hy,hleft|⟨hright,hq⟩⟩
    · obtain ⟨hta,hxdef,hzdef,hydef⟩ := hleft
      change x = leftNode t at hxdef
      refine ⟨x,(mem_sumDomain _ _ _).mpr (Or.inl ⟨t,hta,hxdef⟩),?_⟩
      change z = ZFSet.pair x y at hzdef
      rw [hzdef,hydef,hxdef,sumValue_left]
    · obtain ⟨htb,hxdef,hzdef⟩ := hright
      change t ∈ b.toZFSet at htb
      obtain ⟨t,htb,rfl⟩ := Ordinal.mem_toZFSet_iff.mp htb
      have htb := Ordinal.toZFSet_mem_toZFSet_iff.mp htb
      have hE : ∀ i, cons y (cons x (cons t.toZFSet e)) i ∈ A := by
        intro i; rcases i with _|_|_|i; exact hy; exact hx; exact ht; exact he i
      have hydef := codeSumAt_sound A (level_transitive R γ) 0 4 2 _ hE a t rfl rfl hq
      change x = rightNode t.toZFSet at hxdef
      refine ⟨x,(mem_sumDomain _ _ _).mpr (Or.inr
        ⟨t.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr htb,hxdef⟩),?_⟩
      change z = ZFSet.pair x y at hzdef
      change y = (a+t).toZFSet at hydef
      rw [hzdef,hydef,hxdef,sumValue_right,Ordinal.rank_toZFSet]
  · rintro ⟨x,hx,hzdef⟩
    rcases (mem_sumDomain _ _ _).mp hx with ⟨t,ht,rfl⟩|⟨t,ht,rfl⟩
    · have htA := level_transitive R γ _ ha _ ht
      have hxA := orderedPair_mem_level_limit R γ hγ h0 htA
      refine ⟨t,htA,_,hxA,t,htA,Or.inl ⟨ht,rfl,?_,rfl⟩⟩
      rw [sumValue_left] at hzdef
      simpa only [e,cons_zero,leftNode] using hzdef
    · obtain ⟨t,ht,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
      have ht := Ordinal.toZFSet_mem_toZFSet_iff.mp ht
      have htA := level_transitive R γ _ hb _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr ht)
      have hxA := orderedPair_mem_level_limit R γ hγ h1 htA
      obtain ⟨hy,hq⟩ := hlocal t ht
      let E := cons (a+t).toZFSet (cons (rightNode t.toZFSet) (cons t.toZFSet e))
      have hE (i : ℕ) : E i ∈ A := by
        rcases i with _|_|_|i; exact hy; exact hxA; exact htA; exact he i
      refine ⟨t.toZFSet,htA,_,hxA,(a+t).toZFSet,hy,Or.inr
        ⟨⟨Ordinal.toZFSet_mem_toZFSet_iff.mpr ht,rfl,?_⟩,?_⟩⟩
      · rw [sumValue_right,Ordinal.rank_toZFSet] at hzdef
        simpa only [e,cons_zero,rightNode] using hzdef
      · exact codeSumAt_of_certificates A (level_transitive R γ) hω 0 4 2 E hE a t rfl rfl hq rfl

theorem sum_certificates_at_limit_successor (R : ZFSet.{u}) (γ a b : Ordinal.{u})
    (hγ : Order.IsSuccLimit γ) (hω : ZFSet.omega.{u} ∈ level R γ)
    (ha : a.toZFSet ∈ level R γ) (hb : b.toZFSet ∈ level R γ)
    (h0 : (∅ : ZFSet.{u}) ∈ level R γ) (h1 : ({∅} : ZFSet.{u}) ∈ level R γ)
    (hlocal : ∀ t < b, (a+t).toZFSet ∈ level R γ ∧ SumCertificates (level R γ) a t) :
    SumCertificates (level R (γ+1)) a b := by
  refine ⟨sum_domain_at_limit_successor R γ hγ ha hb h0 h1,
    sum_relation_at_limit_successor R γ hγ ha hb h0 h1,?_⟩
  apply presentation_graph_at_limit_successor R γ hγ _ _ (a+b) (sumValue a)
    (sum_domain_subset_limit R γ hγ ha hb h0 h1) ?_
    (sumValue_mem a b) (sumValue_surjective a b) (sumValue_relation a b)
    trimmedSumGraphSentence (cons a.toZFSet (cons b.toZFSet (cons ∅ (fun _ => {∅}))))
    (fun i => by rcases i with _|_|_|i; exact ha; exact hb; exact h0; exact h1)
  · exact trimmedSumGraphSentence_spec R γ a b hγ hω ha hb h0 h1 hlocal
  · intro x hx
    rcases (mem_sumDomain _ _ _).mp hx with ⟨t,ht,rfl⟩|⟨t,ht,rfl⟩
    · simpa only [sumValue_left] using level_transitive R γ _ ha _ ht
    · obtain ⟨t,ht,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
      have ht := Ordinal.toZFSet_mem_toZFSet_iff.mp ht
      simpa only [sumValue_right,Ordinal.rank_toZFSet] using (hlocal t ht).1

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_TrimmedBoundaryCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalCoding
universe u

theorem sum_certificates_at_exact_cut (R : ZFSet.{u}) (a b : Ordinal.{u})
    (hγ : Order.IsSuccLimit (a+b)) (hcut : ordinalHeight (seed R)+(a+b)=a+b)
    (hω : ZFSet.omega.{u} ∈ level R (a+b))
    (ha : a.toZFSet ∈ level R (a+b)) (hb : b.toZFSet ∈ level R (a+b))
    (h0 : (∅ : ZFSet.{u}) ∈ level R (a+b)) (h1 : ({∅} : ZFSet.{u}) ∈ level R (a+b))
    (hs : ∀ t < b, SumCertificates (level R (a+b)) a t) :
    SumCertificates (level R (a+b+1)) a b := by
  apply sum_certificates_at_limit_successor R (a+b) a b hγ hω ha hb h0 h1
  intro t ht
  refine ⟨?_,hs t ht⟩
  rw [ordinal_mem_level_iff,hcut]
  exact (add_lt_add_iff_left a).mpr ht

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_TrimmedPaddedSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

theorem padded_final_sum_of_smaller_certificates (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) {n : ℕ} (v : Fin n → Ordinal.{u})
    (β : Ordinal.{u}) (hβ : 0 < β) (hoff : realSeedOffset+β=β) (hv : vectorCode v ≤ β)
    (hs : ∀ t < Ordinal.omega0 ^ vectorCode v,
      SumCertificates (level (groundReals M) (paddedCode v β)) (Ordinal.omega0 ^ (β+1)) t) :
    SumCertificates (level (groundReals M) (heightDomainIndex (paddedCode v β)))
      (Ordinal.omega0 ^ (β+1)) (Ordinal.omega0 ^ vectorCode v) := by
  let R := groundReals M
  let a := Ordinal.omega0 ^ (β+1)
  let b := Ordinal.omega0 ^ vectorCode v
  let c := paddedCode v β
  have hc : c = a+b := by change pairCode β (vectorCode v) = _; rw [pairCode,ite_eq_left hv]
  have hca : a < c := by
    rw [hc]
    simpa only [add_zero] using (add_lt_add_iff_left a).mpr (Ordinal.opow_pos (vectorCode v) Ordinal.omega0_pos)
  have hba : b < a := (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr
    (hv.trans_lt (lt_add_one β))
  have habs := offset_absorbed_above realSeedOffset β c hoff (padding_lt_paddedCode v β).le
  have hcut : ordinalHeight (seed R)+c=c := by rw [ground_seed_offset M hM hT]; exact habs
  have hmem (o : Ordinal.{u}) (ho : o < c) : o.toZFSet ∈ level R c := by
    rw [ordinal_mem_level_iff,hcut]; exact ho
  have hω := ground_level_omega_mem M hM hT c
  have h0 := level_transitive R c _ hω _ ZFSet.omega_zero
  have h1 : ({∅} : ZFSet.{u}) ∈ level R c := by
    have h := level_transitive R c _ hω _ ((mem_omega _).mpr ⟨1,rfl⟩)
    simpa [natSet] using h
  have hlim := paddedCode_isSuccLimit v β hβ
  have hresult := sum_certificates_at_exact_cut R a b (hc ▸ hlim)
    (by rw [← hc]; exact hcut) (by rw [← hc]; exact hω)
    (by rw [← hc]; exact hmem a hca) (by rw [← hc]; exact hmem b (hba.trans hca))
    (by rw [← hc]; exact h0) (by rw [← hc]; exact h1) (by rw [← hc]; exact hs)
  rw [heightDomainIndex_of_absorbed _ habs]
  simpa only [← hc] using hresult

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteSumDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

theorem sum_domain_at_successor_of_subset (R : ZFSet.{u}) (γ : Ordinal.{u})
    {a b : ZFSet.{u}}
    (ha : a ∈ level R γ) (hb : b ∈ level R γ)
    (h0 : (∅ : ZFSet.{u}) ∈ level R γ) (h1 : ({∅} : ZFSet.{u}) ∈ level R γ)
    (hd : sumDomain a b ⊆ level R γ) :
    sumDomain a b ∈ level R (γ+1) := by
  let e := cons a (cons b (cons ∅ (fun _ => {∅})))
  have he (i : ℕ) : e i ∈ level R γ := by
    rcases i with _|_|_|i; exact ha; exact hb; exact h0; exact h1
  apply defined_set_at_successor R γ trimmedSumDomainSentence e he _
    hd
  intro z hz
  rw [trimmedSumDomainSentence,bounded_sat,Formula.absolute _ _ (level_transitive R γ) _
    (fun i => by cases i; exact hz; exact he _)]
  simp only [Formula.eval_disj,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e,
    mem_sumDomain,leftNode,rightNode]

theorem sum_relation_at_successor_of_subset (R : ZFSet.{u}) (γ : Ordinal.{u})
    {a b : ZFSet.{u}}
    (ha : a ∈ level R γ) (hb : b ∈ level R γ)
    (h0 : (∅ : ZFSet.{u}) ∈ level R γ) (h1 : ({∅} : ZFSet.{u}) ∈ level R γ)
    (hd : sumDomain a b ⊆ level R γ)
    (hsub : sumRelation a b ⊆ level R γ) :
    sumRelation a b ∈ level R (γ+1) := by
  let A := level R γ
  let e := cons a (cons b (cons ∅ (fun _ => {∅})))
  have he (i : ℕ) : e i ∈ A := by
    rcases i with _|_|_|i; exact ha; exact hb; exact h0; exact h1
  apply defined_set_at_successor R γ trimmedSumRelationSentence e he _ hsub
  intro z hz
  change (∃ x ∈ A, ∃ y ∈ A, (fromBounded _).Sat _ (cons y (cons x (cons z e)))) ↔ _
  have hspec (x y : ZFSet.{u}) (hx : x ∈ A) (hy : y ∈ A) :
      (fromBounded (.conj (.orderedPair 2 1 0) (sumLessFormula 3 4 5 6 1 0))).Sat
        (A : Set ZFSet) (cons y (cons x (cons z e))) ↔
          z = ZFSet.pair x y ∧ SumLess a b x y := by
    rw [bounded_sat,Formula.absolute _ A (level_transitive R γ) _ (fun i => by
      rcases i with _|_|_|i; exact hy; exact hx; exact hz; exact he i)]
    simp only [Formula.Eval,Formula.eval_orderedPair]
    rw [sumLessFormula_eval _ _ _ _ _ _ _ rfl rfl]
    rfl
  constructor
  · rintro ⟨x,hx,y,hy,h⟩
    obtain ⟨rfl,hless⟩ := (hspec x y hx hy).mp h
    have hkeep := hless
    have hxy : x ∈ sumDomain a b ∧ y ∈ sumDomain a b := by
      rcases hless with ⟨s,hs,t,ht,rfl,rfl,_⟩|⟨s,hs,t,ht,rfl,rfl⟩|⟨s,hs,t,ht,rfl,rfl,_⟩
      · exact ⟨(mem_sumDomain _ _ _).mpr (Or.inl ⟨s,hs,rfl⟩),
          (mem_sumDomain _ _ _).mpr (Or.inl ⟨t,ht,rfl⟩)⟩
      · exact ⟨(mem_sumDomain _ _ _).mpr (Or.inl ⟨s,hs,rfl⟩),
          (mem_sumDomain _ _ _).mpr (Or.inr ⟨t,ht,rfl⟩)⟩
      · exact ⟨(mem_sumDomain _ _ _).mpr (Or.inr ⟨s,hs,rfl⟩),
          (mem_sumDomain _ _ _).mpr (Or.inr ⟨t,ht,rfl⟩)⟩
    exact (pair_mem_sumRelation a b x y).mpr ⟨hxy.1,hxy.2,hkeep⟩
  · intro h
    obtain ⟨x,hx,y,hy,rfl⟩ := ZFSet.mem_prod.mp (sumRelation_on a b h)
    exact ⟨x,hd hx,y,hd hy,(hspec x y (hd hx) (hd hy)).mpr
      ⟨rfl,((pair_mem_sumRelation a b x y).mp h).2.2⟩⟩

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteSumGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalCoding
universe u

theorem sum_graph_spec_with_internal_nodes (A : ZFSet.{u}) (hA : Transitive A) (a b : Ordinal.{u}) (hω : ZFSet.omega.{u} ∈ A)
    (ha : a.toZFSet ∈ A) (hb : b.toZFSet ∈ A)
    (h0 : (∅ : ZFSet.{u}) ∈ A) (h1 : ({∅} : ZFSet.{u}) ∈ A)
    (hlocal : ∀ t < b, (a+t).toZFSet ∈ A ∧ SumCertificates (A) a t)
    (hnodes : sumDomain a.toZFSet b.toZFSet ⊆ A)
    (z : ZFSet.{u}) (hz : z ∈ A) :
    trimmedSumGraphSentence.Sat (A : Set ZFSet)
      (cons z (cons a.toZFSet (cons b.toZFSet (cons ∅ (fun _ => {∅}))))) ↔
        ∃ x ∈ sumDomain a.toZFSet b.toZFSet, z = ZFSet.pair x (sumValue a x) := by
  let e := cons z (cons a.toZFSet (cons b.toZFSet (cons ∅ (fun _ => {∅}))))
  have he (i : ℕ) : e i ∈ A := by
    rcases i with _|_|_|_|i; exact hz; exact ha; exact hb; exact h0; exact h1
  rw [trimmedSumGraphSentence_semantics A hA e he]
  constructor
  · rintro ⟨t,ht,x,hx,y,hy,hleft|⟨hright,hq⟩⟩
    · obtain ⟨hta,hxdef,hzdef,hydef⟩ := hleft
      change x = leftNode t at hxdef
      refine ⟨x,(mem_sumDomain _ _ _).mpr (Or.inl ⟨t,hta,hxdef⟩),?_⟩
      change z = ZFSet.pair x y at hzdef
      rw [hzdef,hydef,hxdef,sumValue_left]
    · obtain ⟨htb,hxdef,hzdef⟩ := hright
      change t ∈ b.toZFSet at htb
      obtain ⟨t,htb,rfl⟩ := Ordinal.mem_toZFSet_iff.mp htb
      have htb := Ordinal.toZFSet_mem_toZFSet_iff.mp htb
      have hE : ∀ i, cons y (cons x (cons t.toZFSet e)) i ∈ A := by
        intro i; rcases i with _|_|_|i; exact hy; exact hx; exact ht; exact he i
      have hydef := codeSumAt_sound A hA 0 4 2 _ hE a t rfl rfl hq
      change x = rightNode t.toZFSet at hxdef
      refine ⟨x,(mem_sumDomain _ _ _).mpr (Or.inr
        ⟨t.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr htb,hxdef⟩),?_⟩
      change z = ZFSet.pair x y at hzdef
      change y = (a+t).toZFSet at hydef
      rw [hzdef,hydef,hxdef,sumValue_right,Ordinal.rank_toZFSet]
  · rintro ⟨x,hx,hzdef⟩
    rcases (mem_sumDomain _ _ _).mp hx with ⟨t,ht,rfl⟩|⟨t,ht,rfl⟩
    · have htA := hA _ ha _ ht
      have hxA := hnodes ((mem_sumDomain _ _ _).mpr (Or.inl ⟨t,ht,rfl⟩))
      refine ⟨t,htA,_,hxA,t,htA,Or.inl ⟨ht,rfl,?_,rfl⟩⟩
      rw [sumValue_left] at hzdef
      simpa only [e,cons_zero,leftNode] using hzdef
    · obtain ⟨t,ht,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
      have ht := Ordinal.toZFSet_mem_toZFSet_iff.mp ht
      have htA := hA _ hb _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr ht)
      have hxA := hnodes ((mem_sumDomain _ _ _).mpr (Or.inr ⟨t.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr ht,rfl⟩))
      obtain ⟨hy,hq⟩ := hlocal t ht
      let E := cons (a+t).toZFSet (cons (rightNode t.toZFSet) (cons t.toZFSet e))
      have hE (i : ℕ) : E i ∈ A := by
        rcases i with _|_|_|i; exact hy; exact hxA; exact htA; exact he i
      refine ⟨t.toZFSet,htA,_,hxA,(a+t).toZFSet,hy,Or.inr
        ⟨⟨Ordinal.toZFSet_mem_toZFSet_iff.mpr ht,rfl,?_⟩,?_⟩⟩
      · rw [sumValue_right,Ordinal.rank_toZFSet] at hzdef
        simpa only [e,cons_zero,rightNode] using hzdef
      · exact codeSumAt_of_certificates A hA hω 0 4 2 E hE a t rfl rfl hq rfl

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_FinitePresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

theorem presentation_graph_at_successor_of_pairs (R : ZFSet.{u}) (γ : Ordinal.{u})
    (d r : ZFSet.{u}) (o : Ordinal.{u})
    (j : ZFSet.{u} → ZFSet.{u})
    (hpairs : ∀ x ∈ d, ZFSet.pair x (j x) ∈ level R γ)
    (hj : ∀ x ∈ d, j x ∈ o.toZFSet)
    (hs : ∀ z ∈ o.toZFSet, ∃ x ∈ d, j x = z)
    (he : ∀ x ∈ d, ∀ y ∈ d, ZFSet.pair x y ∈ r ↔ j x ∈ j y)
    (p : SentenceForm) (e : ℕ → ZFSet.{u}) (henv : ∀ i, e i ∈ level R γ)
    (hp : ∀ z ∈ level R γ, p.Sat (level R γ : Set ZFSet) (cons z e) ↔
      ∃ x ∈ d, z = ZFSet.pair x (j x)) :
    ∃ f ∈ level R (γ+1), OrderTypeCertificate d r o.toZFSet f := by
  let A := level R γ
  let f := A.sep (fun z => p.Sat (A : Set ZFSet) (cons z e))
  have hf : f ∈ level R (γ+1) := by
    rw [level_succ]
    exact separation_mem_definablePower A p e (fun i _ => henv i)
  have hexact (z : ZFSet.{u}) : z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (j x) := by
    change z ∈ A.sep _ ↔ _
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz,h⟩; exact (hp z hz).mp h
    · rintro ⟨x,hx,rfl⟩
      have hz := hpairs x hx
      exact ⟨hz,(hp _ hz).mpr ⟨x,hx,rfl⟩⟩
  exact ⟨f,hf,order_certificate_of_exact_pairs d r f o j hj hs he hexact⟩

end TuringRigidity.RelationCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteSumStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalCoding
universe u

theorem sum_certificates_at_add_five (R : ZFSet.{u}) (γ a b : Ordinal.{u})
    (hω : ZFSet.omega.{u} ∈ level R γ)
    (ha : a.toZFSet ∈ level R γ) (hb : b.toZFSet ∈ level R γ)
    (hlocal : ∀ t < b, (a+t).toZFSet ∈ level R γ ∧ SumCertificates (level R γ) a t) :
    SumCertificates (level R (γ+5)) a b := by
  have h0 := level_transitive R γ _ hω _ ZFSet.omega_zero
  have h1 : ({∅} : ZFSet.{u}) ∈ level R γ := by
    have h := level_transitive R γ _ hω _ ((mem_omega _).mpr ⟨1,rfl⟩)
    simpa [natSet] using h
  have h02 : γ ≤ γ+2 := le_self_add
  have h24 : γ+2 ≤ γ+4 := add_le_add le_rfl (by exact_mod_cast (show (2 : ℕ) ≤ 4 by decide) : (2 : Ordinal.{u}) ≤ 4)
  have h04 := h02.trans h24
  have hd2 : sumDomain a.toZFSet b.toZFSet ⊆ level R (γ+2) := by
    intro x hx
    rcases (mem_sumDomain _ _ _).mp hx with ⟨t,ht,rfl⟩|⟨t,ht,rfl⟩
    · exact orderedPair_mem_level_add_two R γ h0 (level_transitive R γ _ ha _ ht)
    · exact orderedPair_mem_level_add_two R γ h1 (level_transitive R γ _ hb _ ht)
  have hd4 : sumDomain a.toZFSet b.toZFSet ⊆ level R (γ+4) :=
    fun _ h => level_mono R h24 (hd2 h)
  have hr4 : sumRelation a.toZFSet b.toZFSet ⊆ level R (γ+4) := by
    intro z hz
    obtain ⟨x,hx,y,hy,rfl⟩ := ZFSet.mem_prod.mp (sumRelation_on _ _ hz)
    simpa only [add_assoc,show (2 : Ordinal.{u})+2=4 from by norm_num] using
      orderedPair_mem_level_add_two R (γ+2) (hd2 hx) (hd2 hy)
  have hv (x : ZFSet.{u}) (hx : x ∈ sumDomain a.toZFSet b.toZFSet) :
      sumValue a x ∈ level R γ := by
    rcases (mem_sumDomain _ _ _).mp hx with ⟨t,ht,rfl⟩|⟨t,ht,rfl⟩
    · simpa only [sumValue_left] using level_transitive R γ _ ha _ ht
    · obtain ⟨t,ht,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
      simpa only [sumValue_right,Ordinal.rank_toZFSet] using (hlocal t (Ordinal.toZFSet_mem_toZFSet_iff.mp ht)).1
  have hpairs (x : ZFSet.{u}) (hx : x ∈ sumDomain a.toZFSet b.toZFSet) :
      ZFSet.pair x (sumValue a x) ∈ level R (γ+4) := by
    simpa only [add_assoc,show (2 : Ordinal.{u})+2=4 from by norm_num] using
      orderedPair_mem_level_add_two R (γ+2) (hd2 hx) (level_mono R h02 (hv x hx))
  have ha4 := level_mono R h04 ha
  have hb4 := level_mono R h04 hb
  have hz4 := level_mono R h04 h0
  have ho4 := level_mono R h04 h1
  have hω4 := level_mono R h04 hω
  have hc4 (t : Ordinal.{u}) (ht : t < b) :
      (a+t).toZFSet ∈ level R (γ+4) ∧ SumCertificates (level R (γ+4)) a t :=
    ⟨level_mono R h04 (hlocal t ht).1,(hlocal t ht).2.mono (level_mono R h04)⟩
  have hd := sum_domain_at_successor_of_subset R (γ+4) ha4 hb4 hz4 ho4 hd4
  have hr := sum_relation_at_successor_of_subset R (γ+4) ha4 hb4 hz4 ho4 hd4 hr4
  have hf := presentation_graph_at_successor_of_pairs R (γ+4) _ _ (a+b) (sumValue a)
    hpairs (sumValue_mem a b) (sumValue_surjective a b) (sumValue_relation a b)
    trimmedSumGraphSentence (cons a.toZFSet (cons b.toZFSet (cons ∅ (fun _ => {∅}))))
    (fun i => by rcases i with _|_|_|i; exact ha4; exact hb4; exact hz4; exact ho4)
    (sum_graph_spec_with_internal_nodes _ (level_transitive R (γ+4)) a b
      hω4 ha4 hb4 hz4 ho4 hc4 hd4)
  simpa only [SumCertificates,add_assoc,show (4 : Ordinal.{u})+1=5 from by norm_num] using And.intro hd (And.intro hr hf)

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RecursiveSumBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalCoding
universe u

theorem sum_certificates_finite_bound (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (a b : Ordinal.{u}) :
    SumCertificates (level (groundReals M) (a+8*b+8)) a b := by
  induction b using WellFoundedLT.induction with
  | ind b ih =>
    let R := groundReals M
    let γ := a+8*b+1
    have hb8 : b ≤ 8*b := Ordinal.le_mul_right b (by exact_mod_cast (show (0 : ℕ) < 8 by decide) : (0 : Ordinal.{u}) < 8)
    have hsmall (t : Ordinal.{u}) (ht : t < b) : a+8*t+8 ≤ a+8*b := by
      rw [add_assoc,← mul_add_one]
      exact add_le_add le_rfl (mul_le_mul_right (Order.add_one_le_iff.mpr ht) 8)
    have hmem (c : Ordinal.{u}) (hc : c ≤ a+8*b) : c.toZFSet ∈ level R γ := by
      rw [ordinal_mem_level_iff]
      exact (hc.trans_lt (lt_add_one _)).trans_le le_add_self
    have ha := hmem a le_self_add
    have hb := hmem b (hb8.trans le_add_self)
    have hc (t : Ordinal.{u}) (ht : t < b) :
        (a+t).toZFSet ∈ level R γ ∧ SumCertificates (level R γ) a t := by
      refine ⟨hmem _ (add_le_add le_rfl (ht.le.trans hb8)),?_⟩
      exact (ih t ht).mono (level_mono R ((hsmall t ht).trans le_self_add))
    have result := sum_certificates_at_add_five R γ a b
      (ground_level_omega_mem M hM hT γ) ha hb hc
    apply result.mono (level_mono R ?_)
    dsimp [γ]
    rw [add_assoc]
    exact add_le_add le_rfl (by norm_num : (1 : Ordinal.{u})+5 ≤ 8)

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteSumPowerBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalCoding
universe u

theorem finite_left_mul_omega_power (n : ℕ) (hn : 0 < n) (β : Ordinal.{u}) (hβ : 0 < β) :
    (n : Ordinal.{u}) * Ordinal.omega0 ^ β = Ordinal.omega0 ^ β := by
  have h1 : (1 : Ordinal.{u}) ≤ β := by simpa only [zero_add] using Order.add_one_le_iff.mpr hβ
  have hsplit : β = 1+(β-1) := (Ordinal.add_sub_cancel_of_le h1).symm
  have hp : Ordinal.omega0 ^ β = Ordinal.omega0 * Ordinal.omega0 ^ (β-1) := by
    conv_lhs => rw [hsplit,Ordinal.opow_add,Ordinal.opow_one]
  rw [hp,← mul_assoc,Ordinal.natCast_mul_omega0 hn]

theorem finite_sum_margin_lt_power (β t : Ordinal.{u}) (hβ : 0 < β)
    (ht : t < Ordinal.omega0 ^ β) : 8*t+8 < Ordinal.omega0 ^ β := by
  have hn : (0 : ℕ) < 8 := by decide
  have h8 : (0 : Ordinal.{u}) < 8 := by exact_mod_cast hn
  have hmul : 8*t < Ordinal.omega0 ^ β := by
    rw [← finite_left_mul_omega_power 8 hn β hβ]
    exact mul_lt_mul_of_pos_left ht h8
  have hω : Ordinal.omega0 ≤ Ordinal.omega0 ^ β := by
    simpa only [Ordinal.opow_one] using
      Ordinal.opow_le_opow_right Ordinal.omega0_pos (show 1 ≤ β from by simpa only [zero_add] using Order.add_one_le_iff.mpr hβ)
  exact Ordinal.isPrincipal_add_omega0_opow β hmul
    ((Ordinal.natCast_lt_omega0 8).trans_le hω)

theorem sum_certificates_below_power_cut (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (a β t : Ordinal.{u}) (hβ : 0 < β)
    (ht : t < Ordinal.omega0 ^ β) :
    SumCertificates (level (groundReals M) (a+Ordinal.omega0 ^ β)) a t := by
  apply (sum_certificates_finite_bound M hM hT a t).mono (level_mono _ ?_)
  rw [add_assoc]
  exact ((add_lt_add_iff_left a).mpr (finite_sum_margin_lt_power β t hβ ht)).le

theorem padded_final_sum_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hβ : 0 < β) (hoff : realSeedOffset+β=β) (hv : vectorCode v ≤ β) :
    SumCertificates (level (groundReals M) (heightDomainIndex (paddedCode v β)))
      (Ordinal.omega0 ^ (β+1)) (Ordinal.omega0 ^ vectorCode v) := by
  apply padded_final_sum_of_smaller_certificates M hM hT v β hβ hoff hv
  intro t ht
  have hc : paddedCode v β = Ordinal.omega0 ^ (β+1)+Ordinal.omega0 ^ vectorCode v := by
    change pairCode β (vectorCode v) = _
    rw [pairCode,ite_eq_left hv]
  rw [hc]
  exact sum_certificates_below_power_cut M hM hT _ _ t (vectorCode_pos v) ht

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteBlockProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalCoding
universe u

theorem finite_block_product_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (β : Ordinal.{u}) (hβ : 0 < β) (n : ℕ) :
    ProductCertificates
      (level (groundReals M) (Ordinal.omega0 ^ β * (n+2)+1))
      (Ordinal.omega0 ^ β) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let R := groundReals M
    let a := Ordinal.omega0 ^ β
    let γ := a*(n+2)
    have ha0 : 0 < a := Ordinal.opow_pos β Ordinal.omega0_pos
    have haLim : Order.IsSuccLimit a := Ordinal.isSuccLimit_opow_left
      Ordinal.isSuccLimit_omega0 (ne_of_gt hβ)
    have hn2 : (0 : Ordinal.{u}) < n+2 := by exact_mod_cast (show 0 < n+2 by omega)
    have hγ : Order.IsSuccLimit γ := Ordinal.isSuccLimit_mul_left haLim hn2
    have haγ : a < γ := by
      have h : (1 : Ordinal.{u}) < n+2 := by exact_mod_cast (show 1 < n+2 by omega)
      simpa only [mul_one] using mul_lt_mul_of_pos_left h ha0
    have hmem (c : Ordinal.{u}) (hc : c < γ) : c.toZFSet ∈ level R γ := by
      rw [ordinal_mem_level_iff]
      exact hc.trans_le le_add_self
    apply product_certificates_at_limit_successor R γ a n hγ
      (ground_level_omega_mem M hM hT γ) (hmem a haγ)
      (hmem n ((Ordinal.natCast_lt_of_isSuccLimit haLim n).trans haγ))
    intro s hsn
    obtain ⟨m,rfl⟩ := Ordinal.lt_omega0.mp (hsn.trans (Ordinal.natCast_lt_omega0 n))
    have hmn : m < n := by exact_mod_cast hsn
    have hm2 : (m : Ordinal.{u})+2 < n+2 := by exact_mod_cast (show m+2 < n+2 by omega)
    have hpγ : a*(m+2) < γ := mul_lt_mul_of_pos_left hm2 ha0
    have hp : ProductCertificates (level R γ) a m :=
      (ih m hmn).mono (level_mono R (Order.add_one_le_iff.mpr hpγ))
    have hmγ : a*m < γ := mul_lt_mul_of_pos_left
      (hsn.trans (by exact_mod_cast (show n < n+2 by omega))) ha0
    refine ⟨hmem _ hmγ,hp,?_⟩
    intro t ht
    have htmargin := finite_sum_margin_lt_power β t hβ ht
    have hbound : a*m+8*t+8 < a*(m+1) := by
      rw [add_assoc,mul_add_one]
      exact (add_lt_add_iff_left (a*m)).mpr htmargin
    have hm1 : (m : Ordinal.{u})+1 ≤ n+2 := by exact_mod_cast (show m+1 ≤ n+2 by omega)
    have hboundγ := hbound.trans_le (mul_le_mul_right hm1 a)
    have hvγ : a*m+t < γ := by
      have hv : a*m+t < a*m+a := (add_lt_add_iff_left (a*m)).mpr ht
      rw [← mul_add_one] at hv
      exact hv.trans_le (mul_le_mul_right hm1 a)
    exact ⟨hmem _ hvγ,(sum_certificates_finite_bound M hM hT (a*m) t).mono
      (level_mono R hboundγ.le)⟩

theorem finite_products_below_omega_boundary (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (β : Ordinal.{u}) (hβ : 0 < β) :
    ∀ s < Ordinal.omega0, ProductCertificates
      (level (groundReals M) (Ordinal.omega0 ^ (β+1))) (Ordinal.omega0 ^ β) s := by
  intro s hs
  obtain ⟨n,rfl⟩ := Ordinal.lt_omega0.mp hs
  have h := finite_block_product_certificates M hM hT β hβ n
  apply h.mono (level_mono _ ?_)
  apply Order.add_one_le_iff.mpr
  rw [Ordinal.opow_add_one]
  apply mul_lt_mul_of_pos_left _ (Ordinal.opow_pos β Ordinal.omega0_pos)
  exact_mod_cast Ordinal.natCast_lt_omega0 (n+2)

theorem partial_sums_below_omega_boundary (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (β : Ordinal.{u}) (hβ : 0 < β) :
    ∀ s < Ordinal.omega0, ∀ t < Ordinal.omega0 ^ β, SumCertificates
      (level (groundReals M) (Ordinal.omega0 ^ (β+1))) (Ordinal.omega0 ^ β*s) t := by
  intro s hs t ht
  have hc := sum_certificates_below_power_cut M hM hT (Ordinal.omega0 ^ β*s) β t hβ ht
  apply hc.mono (level_mono _ ?_)
  rw [← mul_add_one,Ordinal.opow_add_one]
  exact mul_le_mul_right (Order.add_one_le_iff.mpr hs) _

theorem omega_boundary_product_without_offset (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (β : Ordinal.{u}) (hβ : 0 < β) :
    ProductCertificates
      (level (groundReals M) (Ordinal.omega0 ^ (β+1)+1)) (Ordinal.omega0 ^ β) Ordinal.omega0 := by
  let R := groundReals M
  let a := Ordinal.omega0 ^ β
  let b := Ordinal.omega0 ^ (β+1)
  have hab : a*Ordinal.omega0=b := (Ordinal.opow_add_one Ordinal.omega0 β).symm
  have ha0 : 0 < a := Ordinal.opow_pos β Ordinal.omega0_pos
  have hmem (c : Ordinal.{u}) (hc : c < b) : c.toZFSet ∈ level R b := by
    rw [ordinal_mem_level_iff]
    exact hc.trans_le le_add_self
  have hl : Order.IsSuccLimit b := Ordinal.isSuccLimit_opow_left
    Ordinal.isSuccLimit_omega0 (ne_of_gt (hβ.trans (lt_add_one β)))
  have hω := ground_level_omega_mem M hM hT b
  apply product_certificates_at_limit_successor R b a Ordinal.omega0 hl hω
    (hmem a ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (lt_add_one β)))
    (toZFSet_omega.symm ▸ hω)
  intro s hs
  have hv : a*s < b := hab ▸ mul_lt_mul_of_pos_left hs ha0
  refine ⟨hmem _ hv,finite_products_below_omega_boundary M hM hT β hβ s hs,?_⟩
  intro t ht
  have hv' : a*s+t < b := hab ▸ Ordinal.lt_mul_iff.mpr ⟨s,hs,t,ht,rfl⟩
  exact ⟨hmem _ hv',partial_sums_below_omega_boundary M hM hT β hβ s hs t ht⟩

end TuringRigidity.OrdinalArithmetic

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

theorem CodeBranchCertificates.mono {M N : ZFSet.{u}} {twice : Bool} {a b : Ordinal.{u}}
    (h : CodeBranchCertificates M twice a b) (hMN : M ⊆ N) : CodeBranchCertificates N twice a b := by
  obtain ⟨hk,hu,hv,ht,hp,hq,hd,hs⟩ := h
  exact ⟨hMN hk,hMN hu,hMN hv,hMN ht,hp.mono hMN,hq.mono hMN,
    fun h => (hd h).mono hMN,hs.mono hMN⟩

theorem PairCodeCertificates.mono {M N : ZFSet.{u}} {a b : Ordinal.{u}}
    (h : PairCodeCertificates M a b) (hMN : M ⊆ N) : PairCodeCertificates N a b := by
  unfold PairCodeCertificates at h ⊢
  split <;> rename_i hc
  · exact (by simpa only [ite_eq_left hc] using h : CodeBranchCertificates M false a b).mono hMN
  · exact (by simpa only [ite_eq_right hc] using h : CodeBranchCertificates M true b a).mono hMN

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

theorem VectorCodeCertificates.mono {M N : ZFSet.{u}} {n : ℕ} {v : Fin n → Ordinal.{u}}
    (h : VectorCodeCertificates M v) (hMN : M ⊆ N) : VectorCodeCertificates N v := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨hMN h.1,h.2.1.mono hMN,ih h.2.2⟩

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ClosedPaddingCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

theorem padded_certificates_of_lower_closure_oai (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hβ : Order.IsSuccLimit β) (hoff : realSeedOffset+β=β) (hv : vectorCode v < β)
    (hvec : VectorCodeCertificates (level (groundReals M) β) v)
    (hpow : ∀ c < β, (Ordinal.omega0 ^ c).toZFSet ∈ level (groundReals M) β ∧
      OmegaPowerCertificates (level (groundReals M) β) c.toZFSet) :
    PaddedCodeCertificates (level (groundReals M) (heightDomainIndex (paddedCode v β))) v β := by
  let R := groundReals M
  let c := paddedCode v β
  let δ := heightDomainIndex c
  have hβpos : 0 < β := hβ.bot_lt
  have hβc : β < c := padding_lt_paddedCode v β
  have hcodeabs := offset_absorbed_above realSeedOffset β c hoff hβc.le
  have hδ : δ=c+1 := heightDomainIndex_of_absorbed c hcodeabs
  have hβδ : β ≤ δ := hβc.le.trans (hδ ▸ le_self_add)
  have hcut : ordinalHeight (seed R)+c=c := by rw [ground_seed_offset M hM hT]; exact hcodeabs
  have hmem (a : Ordinal.{u}) (ha : a ≤ c) : a.toZFSet ∈ level R δ := by
    rw [hδ,ordinal_mem_level_iff,← add_assoc,hcut]
    exact Order.lt_add_one_iff.mpr ha
  have hb1 : β+1 ≤ c := Order.add_one_le_iff.mpr hβc
  have hu : Ordinal.omega0 ^ (β+1) < c := by
    change Ordinal.omega0 ^ (β+1) < pairCode β (vectorCode v)
    rw [pairCode,ite_eq_left hv.le]
    simpa only [add_zero] using (add_lt_add_iff_left (Ordinal.omega0 ^ (β+1))).mpr
      (Ordinal.opow_pos (vectorCode v) Ordinal.omega0_pos)
  have hvpow := level_mono R hβδ (hpow (vectorCode v) hv).1
  have hcβ := padded_omega_boundary_certificates M hM hT v β hβ hoff hv.le hpow
    (omega_boundary_product_without_offset M hM hT β hβpos)
  have hck := (hpow (vectorCode v) hv).2.mono (level_mono R hβδ)
  have hsum := padded_final_sum_certificates M hM hT v β hβpos hoff hv.le
  refine ⟨hmem β hβc.le,hmem (vectorCode v) (hv.trans hβc).le,?_,hvec.mono (level_mono R hβδ)⟩
  rw [PairCodeCertificates,ite_eq_left hv.le]
  exact ⟨hmem (β+1) hb1,hmem _ hu.le,hvpow,hmem _ hu.le,hcβ,hck,
    fun h => Bool.noConfusion h,hsum⟩

end TuringRigidity.OrdinalCoding

end OAI
end

theorem solution.{u} : type_of% @OAI.TuringRigidity.OrdinalCoding.padded_certificates_of_lower_closure_oai.{u} := @OAI.TuringRigidity.OrdinalCoding.padded_certificates_of_lower_closure_oai.{u}
