-- Prove2me | solution 1 for OAI.TuringRigidity.RelativeConstructible.Construction.largest_domain_definition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:31:23.78495+00:00
-- url     : https://prove2.me/submissions/9c2ff94b-108d-413b-a538-c89b3d648a87

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_Construction_inlined_at_level
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_definablePower_mem
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_ground_relativeModel_ordinal_iff
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_ground_relative_context
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_seed_bound_stage_at_levels
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

theorem iterate_mem {v : ZFSet.{u}} (F : ZFSet.{u} → ZFSet.{u})
    (hF : ∀ x ∈ v, F x ∈ v) {x : ZFSet.{u}} (hx : x ∈ v) (n : ℕ) : F^[n] x ∈ v := by
  induction n with
  | zero => exact hx
  | succ n ih => simpa only [Function.iterate_succ_apply'] using hF _ ih

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

theorem Context.prod_mem {a b : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) :
    ZFSet.prod a b ∈ M :=
  product_mem M C.transitive C.pairing C.union C.power C.separation ha hb

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

theorem atom_primrec : Primrec atom := Primrec₂.natPair.comp (Primrec.const 0) Primrec.id

theorem cell_primrec : Primrec₂ cell :=
  Primrec₂.natPair.comp (Primrec.succ.comp Primrec.fst) Primrec.snd

theorem binary_primrec (t : ℕ) : Primrec₂ (binary t) :=
  cell_primrec.comp (Primrec.const (atom t))
    (cell_primrec.comp Primrec.fst (cell_primrec.comp Primrec.snd (Primrec.const (atom 0))))

theorem unary_primrec (t : ℕ) : Primrec (unary t) :=
  cell_primrec.comp (Primrec.const (atom t))
    (cell_primrec.comp Primrec.id (Primrec.const (atom 0)))

theorem atomic_primrec (t : ℕ) : Primrec₂ (fun i j => binary t (atom i) (atom j)) :=
  (binary_primrec t).comp (atom_primrec.comp Primrec.fst) (atom_primrec.comp Primrec.snd)

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SentenceFamilyFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.SentenceCoding
open ElementaryModel BoundedSetTheory TransitiveNameModel BoundedDefinability SetModelFunctions
universe u

variable {M : ZFSet.{u}}

theorem setStep_nat (S : ZFSet.{u}) (n : ℕ) :
    SetStep S (natSet n) ↔ Step (fun k => natSet k ∈ S) n := by
  simp only [SetStep,Step,BinaryGraph,UnaryGraph]
  have hn (a b : ℕ) : natSet.{u} a = natSet b ↔ a = b := natSet_injective.eq_iff
  simp only [hn]
  constructor
  · intro h
    rcases h with h|h|h|h|h
    · obtain ⟨x,_,y,_,i,j,_,_,he⟩ := h; exact Or.inl ⟨i,j,he⟩
    · obtain ⟨x,_,y,_,i,j,_,_,he⟩ := h; exact Or.inr (Or.inl ⟨i,j,he⟩)
    · obtain ⟨x,hx,y,hy,i,j,rfl,rfl,he⟩ := h
      exact Or.inr (Or.inr (Or.inl ⟨i,j,he,hx,hy⟩))
    · obtain ⟨x,hx,i,rfl,he⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i,he,hx⟩)))
    · obtain ⟨x,hx,i,rfl,he⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i,he,hx⟩)))
  · intro h
    have hw (k : ℕ) : natSet.{u} k ∈ ZFSet.omega := (mem_omega _).mpr ⟨k,rfl⟩
    rcases h with h|h|h|h|h
    · obtain ⟨i,j,he⟩ := h
      exact Or.inl ⟨_,hw i,_,hw j,i,j,rfl,rfl,he⟩
    · obtain ⟨i,j,he⟩ := h
      exact Or.inr (Or.inl ⟨_,hw i,_,hw j,i,j,rfl,rfl,he⟩)
    · obtain ⟨i,j,he,hi,hj⟩ := h
      exact Or.inr (Or.inr (Or.inl ⟨_,hi,_,hj,i,j,rfl,rfl,he⟩))
    · obtain ⟨i,he,hi⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_,hi,i,rfl,he⟩)))
    · obtain ⟨i,he,hi⟩ := h
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_,hi,i,rfl,he⟩)))

theorem setClosed_spec (S : ZFSet.{u}) :
    SetClosed S ↔ S ⊆ ZFSet.omega ∧ ∀ c ∈ S, SetStep S c := by
  constructor
  · rintro ⟨hs,hc⟩
    refine ⟨hs,fun c hm => ?_⟩
    obtain ⟨n,rfl⟩ := (mem_omega c).mp (hs hm)
    exact (setStep_nat S n).mpr (hc n hm)
  · rintro ⟨hs,hc⟩
    exact ⟨hs,fun n hn => (setStep_nat S n).mp (hc _ hn)⟩

end TuringRigidity.SentenceCoding

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_CanonicalAdditionSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic SetModelIteration
universe u

theorem additionSet_members (z : ZFSet.{u}) :
    z ∈ additionSet ↔ ∃ n m, z = ZFSet.pair (ZFSet.pair (natSet n) (natSet m)) (natSet (n+m)) := by
  rw [additionSet,mem_iterationSet setSucc setSucc_omega]
  constructor
  · rintro ⟨n,x,hx,hz⟩
    obtain ⟨m,rfl⟩ := (mem_omega x).mp hx
    exact ⟨n,m,by simpa only [iterate_setSucc,Nat.add_comm] using hz⟩
  · rintro ⟨n,m,rfl⟩
    exact ⟨n,natSet m,(mem_omega _).mpr ⟨m,rfl⟩,by rw [iterate_setSucc,Nat.add_comm]⟩

theorem additionSet_function : TransitiveNameModel.FunctionGraph pairNumbers.{u} ZFSet.omega additionSet := by
  constructor
  · intro z hz
    obtain ⟨n,m,rfl⟩ := (additionSet_members z).mp hz
    exact ⟨_,natPair_mem n m,_,(mem_omega _).mpr ⟨n+m,rfl⟩,rfl⟩
  · intro x hx
    obtain ⟨a,ha,b,hb,rfl⟩ := ZFSet.mem_prod.mp hx
    obtain ⟨n,rfl⟩ := (mem_omega a).mp ha
    obtain ⟨m,rfl⟩ := (mem_omega b).mp hb
    refine ⟨natSet (n+m),(mem_omega _).mpr ⟨n+m,rfl⟩,(addition_code n m _).mpr rfl,?_⟩
    intro z hz hpair
    obtain ⟨k,rfl⟩ := (mem_omega z).mp hz
    exact congrArg natSet ((addition_code n m k).mp hpair)

theorem additionSystem_canonical : AdditionSystem ZFSet.omega pairNumbers.{u} additionSet := by
  refine ⟨additionSet_function,⟨natSet 0,(mem_omega _).mpr ⟨0,rfl⟩,rfl,?_⟩,?_⟩
  · intro x hx
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    exact (addition_code n 0 n).mpr (Nat.add_zero n).symm
  · intro x hx y hy v hv hp y' _ v' _ hy' hv'
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    obtain ⟨m,rfl⟩ := (mem_omega y).mp hy
    obtain ⟨k,rfl⟩ := (mem_omega v).mp hv
    subst y'; subst v'
    change ZFSet.pair (ZFSet.pair (natSet n) (natSet (m+1))) (natSet (k+1)) ∈ additionSet
    exact (addition_code n (m+1) (k+1)).mpr (by have hk := (addition_code n m k).mp hp; omega)

theorem AdditionSystem.exact {A : ZFSet.{u}} (h : AdditionSystem ZFSet.omega pairNumbers A) :
    A = additionSet := by
  have hn (n : ℕ) : natSet.{u} n ∈ ZFSet.omega := (mem_omega _).mpr ⟨n,rfl⟩
  have computes (n m : ℕ) : ZFSet.pair (ZFSet.pair (natSet n) (natSet m)) (natSet (n+m)) ∈ A := by
    induction m with
    | zero =>
      obtain ⟨z,_,rfl,hzero⟩ := h.2.1
      simpa only [Nat.add_zero,natSet] using hzero _ (hn n)
    | succ m ih =>
      have hs := h.2.2 _ (hn n) _ (hn m) _ (hn (n+m)) ih _ (hn (m+1)) _ (hn (n+m+1)) rfl rfl
      simpa only [Nat.add_succ] using hs
  apply ZFSet.ext; intro z
  constructor
  · intro hz
    obtain ⟨x,hx,y,hy,rfl⟩ := h.1.1 z hz
    obtain ⟨a,ha,b,hb,rfl⟩ := ZFSet.mem_prod.mp hx
    obtain ⟨n,rfl⟩ := (mem_omega a).mp ha
    obtain ⟨m,rfl⟩ := (mem_omega b).mp hb
    have eq := h.1.functional (natPair_mem n m) hz (computes n m)
    rw [eq]
    exact (addition_code n m _).mpr rfl
  · intro hz
    obtain ⟨n,m,rfl⟩ := (additionSet_members z).mp hz
    exact computes n m

theorem additionSystemFormula_spec (w d A : ℕ) (e : ℕ → ZFSet.{u})
    (hd : e d = ZFSet.prod (e w) (e w)) :
    (additionSystemFormula w d A).Eval e ↔ AdditionSystem (e w) (e d) (e A) := by
  simp only [additionSystemFormula,AdditionSystem,Formula.Eval,Formula.eval_functionGraph,
    Formula.eval_empty,Formula.eval_allMem,Formula.eval_imp,Formula.eval_successor,
    eval_tripleFormula,cons_zero,cons_succ]
  simp only [hd,ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨hf,⟨z,hz,he,hzero⟩,hstep⟩
    exact ⟨hf,⟨z,hz,he,fun x hx => (hzero x hx).2⟩,
      fun x hx y hy v hv hp y' hy' v' hv' hys hvs =>
        (hstep x hx y hy v hv ⟨⟨hx,hy⟩,hp⟩ y' hy' v' hv' hys hvs).2⟩
  · rintro ⟨hf,⟨z,hz,he,hzero⟩,hstep⟩
    exact ⟨hf,⟨z,hz,he,fun x hx => ⟨⟨hx,hz⟩,hzero x hx⟩⟩,
      fun x hx y hy v hv hp y' hy' v' hv' hys hvs =>
        ⟨⟨hx,hy'⟩,hstep x hx y hy v hv hp.2 y' hy' v' hv' hys hvs⟩⟩

theorem additionSystemFormula_unique (w d A : ℕ) (e : ℕ → ZFSet.{u})
    (hw : e w = ZFSet.omega) (hd : e d = pairNumbers) :
    (additionSystemFormula w d A).Eval e ↔ e A = additionSet := by
  rw [additionSystemFormula_spec w d A e (by rw [hd,hw]; rfl),hw,hd]
  exact ⟨AdditionSystem.exact,fun h => h ▸ additionSystem_canonical⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_BindCanonicalArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic
universe u

theorem squareFormula_spec (w d : ℕ) (e : ℕ → ZFSet.{u}) :
    (squareFormula w d).Eval e ↔ e d = ZFSet.prod (e w) (e w) := by
  simp only [squareFormula,Formula.Eval,Formula.eval_allMem,Formula.eval_orderedPair,cons_zero,cons_succ]
  constructor
  · rintro ⟨h1,h2⟩
    apply ZFSet.ext; intro x
    constructor
    · intro hx
      exact ZFSet.mem_prod.mpr (h1 x hx)
    · intro hx
      obtain ⟨a,ha,b,hb,rfl⟩ := ZFSet.mem_prod.mp hx
      obtain ⟨z,hz,rfl⟩ := h2 a ha b hb
      exact hz
  · intro h
    rw [h]
    exact ⟨fun _ hx => ZFSet.mem_prod.mp hx,
      fun a ha b hb => ⟨ZFSet.pair a b,ZFSet.pair_mem_prod.mpr ⟨ha,hb⟩,rfl⟩⟩

theorem bindArithmetic_spec (M : ZFSet.{u}) (hM : Transitive M)
    (hw : ZFSet.omega.{u} ∈ M) (hd : pairNumbers.{u} ∈ M) (ha : additionSet.{u} ∈ M)
    (p : SentenceForm) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (bindArithmetic p).Sat (M : Set ZFSet) e ↔
      p.Sat (M : Set ZFSet) (cons additionSet (cons pairNumbers (cons ZFSet.omega e))) := by
  have hc (x : ZFSet.{u}) (hx : x ∈ M) : ∀ i, cons x e i ∈ M := by
    intro i; cases i; exact hx; exact he _
  have hwf (x : ZFSet.{u}) (hx : x ∈ M) := canonicalOmega_spec M hM hw 0 (cons x e) (hc x hx)
  have hdf (d : ZFSet.{u}) (hdM : d ∈ M) :
      (fromBounded (squareFormula 1 0)).Sat (M : Set ZFSet) (cons d (cons ZFSet.omega e)) ↔ d = pairNumbers := by
    rw [bounded_sat,Formula.absolute _ M hM _
      (by intro i; rcases i with _|_|i; exact hdM; exact hw; exact he i),squareFormula_spec]
    rfl
  have haf (a : ZFSet.{u}) (haM : a ∈ M) :
      (fromBounded (additionSystemFormula 2 1 0)).Sat (M : Set ZFSet)
        (cons a (cons pairNumbers (cons ZFSet.omega e))) ↔ a = additionSet := by
    rw [bounded_sat,Formula.absolute _ M hM _
      (by intro i; rcases i with _|_|_|i; exact haM; exact hd; exact hw; exact he i)]
    exact additionSystemFormula_unique 2 1 0 _ rfl rfl
  change (∃ w ∈ M, (canonicalOmega 0).Sat (M : Set ZFSet) (cons w e) ∧
    ∃ d ∈ M, (fromBounded (squareFormula 1 0)).Sat (M : Set ZFSet) (cons d (cons w e)) ∧
      ∃ a ∈ M, (fromBounded (additionSystemFormula 2 1 0)).Sat (M : Set ZFSet) (cons a (cons d (cons w e))) ∧
        p.Sat (M : Set ZFSet) (cons a (cons d (cons w e)))) ↔ _
  constructor
  · rintro ⟨w,hwM,hwS,d,hdM,hdS,a,haM,haS,hp⟩
    obtain rfl := (hwf w hwM).mp hwS
    obtain rfl := (hdf d hdM).mp hdS
    obtain rfl := (haf a haM).mp haS
    exact hp
  · intro hp
    exact ⟨_,hw,(hwf _ hw).mpr rfl,_,hd,(hdf _ hd).mpr rfl,_,ha,(haf _ ha).mpr rfl,hp⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticFreeConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic
universe u

theorem Construction.arithmeticSlots_env (t : Construction.{u}) (R : ZFSet.{u})
    (P : Oracle) (z : ZFSet.{u}) :
    (fun i => cons additionSet (cons pairNumbers (cons ZFSet.omega
      (cons z (t.arithmeticFreeInputs R P)))) (arithmeticSlots i)) =
      cons z (t.singleInputs R P) := by
  funext i
  rcases i with _|_|_|_|_|_|i <;> rfl

theorem Construction.arithmeticFreeInputs_mem (t : Construction.{u}) (M R : ZFSet.{u})
    (P : Oracle) (he : ∀ i, t.singleInputs R P i ∈ M) :
    ∀ i, t.arithmeticFreeInputs R P i ∈ M := by
  intro i
  rcases i with _|_|i
  · exact he 0
  · exact he 1
  · exact he (i+5)

theorem Construction.arithmeticFreeMembership_spec (t : Construction.{u}) (M R : ZFSet.{u})
    (hM : Transitive M) (P : Oracle) (ht : t.Certified R P)
    (he : ∀ i, t.singleInputs R P i ∈ M) (hv : t.value R P ∈ M)
    (z : ZFSet.{u}) (hz : z ∈ M) :
    t.arithmeticFreeMembership.Sat (M : Set ZFSet) (cons z (t.arithmeticFreeInputs R P)) ↔
      z ∈ t.value R P := by
  rw [Construction.arithmeticFreeMembership,bindArithmetic_spec M hM (he 2) (he 4) (he 3) _ _
    (by intro i; cases i; exact hz; exact t.arithmeticFreeInputs_mem M R P he _),
    SentenceForm.sat_rename,t.arithmeticSlots_env]
  exact t.singleMembership_of_inputs M R hM P ht he hv z hz

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

theorem ordinalCut_mem_model (M A : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hA : A ∈ M) : ordinalCut A ∈ M := by
  have hs := sep_mem M hM hS (ordinalFormula 0) (fun _ => A) (fun _ => hA) hA
  have heq : A.sep (fun x => (ordinalFormula 0).Eval (cons x (fun _ => A))) = ordinalCut A := by
    apply ZFSet.ext; intro x
    simp only [ZFSet.mem_sep,mem_ordinalCut,eval_ordinalFormula,cons_zero]
  exact heq ▸ hs

theorem ordinalHeight_mem_model (M A : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hA : A ∈ M) (hAt : Transitive A) :
    (ordinalHeight A).toZFSet ∈ M := by
  rw [ordinalHeight_toZFSet A hAt]
  exact ordinalCut_mem_model M A hM hS hA

theorem internal_ordinal_downward (M : ZFSet.{u}) (hM : Transitive M)
    {a b : Ordinal.{u}} (hb : b.toZFSet ∈ M) (hab : a ≤ b) : a.toZFSet ∈ M := by
  rcases lt_or_eq_of_le hab with h|rfl
  · exact hM _ hb _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr h)
  · exact hb

theorem internal_difference_successor (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (a b : Ordinal.{u}) (ha : a.toZFSet ∈ M) :
    (a-b+1).toZFSet ∈ M :=
  internal_ordinal_succ M hM hT _
    (internal_ordinal_downward M hM ha (Ordinal.sub_le_self a b))

theorem internal_domains_with_largest_ordinal (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) (γ : Ordinal.{u}) (hγ : γ.toZFSet ∈ M) :
    ∃ β : Ordinal.{u}, β.toZFSet ∈ M ∧ ∀ a : Ordinal.{u}, a.toZFSet ∈ M → β ≤ a →
      let δ := a - ordinalHeight (seed R) + 1
      δ.toZFSet ∈ M ∧ γ ≤ δ ∧ a.toZFSet ∈ level R δ ∧
        ∀ e : ℕ → ZFSet.{u}, e 0 ∈ level R δ →
          (largestOrdinalSentence.Sat (level R δ : Set ZFSet) e ↔ e 0 = a.toZFSet) := by
  refine ⟨ordinalHeight (level R γ),ordinalHeight_mem_model M _ hM
    hT.separation.finitePrefix.bounded (level_mem M R hM hT hR γ hγ) (level_transitive R γ),?_⟩
  intro a ha hle
  rw [ordinalHeight_level] at hle
  have hoff : ordinalHeight (seed R) ≤ a := (show ordinalHeight (seed R) ≤ ordinalHeight (seed R) + γ from le_self_add).trans hle
  have hγδ : γ ≤ a - ordinalHeight (seed R) + 1 :=
    (Ordinal.le_sub_of_add_le hle).trans (le_of_lt (lt_add_one _))
  have hm := largest_ordinal_at_difference R a hoff
  refine ⟨internal_difference_successor M hM hT a _ ha,hγδ,hm.1,?_⟩
  intro e he
  exact largestOrdinalSentence_unique _ (level_transitive R _) a hm.1
    (fun b hb => (hm.2 b).mp hb) e he

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_HierarchyCertificatePower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding BoundedDefinability SetModelFunctions
universe u

theorem PowerBound.between {M N a Q : ZFSet.{u}} (h : PowerBound M a Q)
    (hN : Transitive N) (hNM : N ⊆ M) (hQ : Q ∈ N) : PowerBound N a Q := by
  intro x
  exact ⟨fun hx => ⟨hN Q hQ x hx,(h x).mp hx |>.2⟩,
    fun hx => (h x).mpr ⟨hNM hx.1,hx.2⟩⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_AmbientDegreeSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.FullSetForcing
open BoundedSetTheory TransitiveNameModel ElementaryModel SentenceForm
universe u

theorem definedSet_spec (M : ZFSet.{u}) (hM : Transitive M)
    (s : ℕ) (p : Formula) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (definedSet s p).Sat (M : Set ZFSet) e ↔
      ∀ x ∈ M, x ∈ e s ↔ p.Eval (cons x e) := by
  simp only [definedSet,sat_all,sat_iff,Sat,cons_zero,cons_succ,bounded_sat]
  apply forall_congr'; intro x
  apply forall_congr'; intro hx
  exact iff_congr Iff.rfl (Formula.absolute p M hM _
    (by intro i; cases i; exact hx; exact he _))

theorem ownPower_spec (M : ZFSet.{u}) (hM : Transitive M)
    (a s : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (ownPower a s).Sat (M : Set ZFSet) e ↔
      ∀ x, x ∈ e s ↔ x ∈ M ∧ x ⊆ e a := by
  rw [ownPower,definedSet_spec M hM s _ e he]
  simp only [Formula.eval_subset,cons_zero,cons_succ]
  constructor
  · intro h x
    exact ⟨fun hx => ⟨hM _ (he s) _ hx,(h x (hM _ (he s) _ hx)).mp hx⟩,
      fun hx => (h x hx.1).mpr hx.2⟩
  · intro h x hx
    exact (h x).trans (and_iff_right hx)

end TuringRigidity.FullSetForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.NumericSyntax
open BoundedSetTheory TransitiveNameModel BoundedDefinability SentenceCoding
universe u

variable {P Q : (ℕ → ZFSet.{u}) → Prop}

theorem Numeric.congr (h : Numeric P) (he : ∀ e, P e ↔ Q e) : Numeric Q := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p,fun B hB e => (hp B hB e).trans (he e)⟩

theorem Numeric.neg (h : Numeric P) : Numeric (fun e => ¬ P e) := by
  obtain ⟨p,hp⟩ := h
  exact ⟨.neg p,fun B hB e => not_congr (hp B hB e)⟩

theorem Numeric.and (h : Numeric P) (k : Numeric Q) : Numeric (fun e => P e ∧ Q e) := by
  obtain ⟨p,hp⟩ := h; obtain ⟨q,hq⟩ := k
  exact ⟨.conj p q,fun B hB e => and_congr (hp B hB e) (hq B hB e)⟩

theorem Numeric.existsMem (h : Numeric P) (i : ℕ) :
    Numeric (fun e => ∃ x ∈ e i, P (cons x e)) := by
  obtain ⟨p,hp⟩ := h
  refine ⟨.existsMem (2*i) (p.rename bindSlots),?_⟩
  intro B hB e
  simp only [Formula.Eval,mix_even,Formula.eval_rename_comp,bind_mix,hp B hB]

theorem Numeric.existsNat (h : Numeric P) :
    Numeric (fun e => ∃ x ∈ ZFSet.omega, P (cons x e)) := by
  obtain ⟨p,hp⟩ := h
  refine ⟨.existsMem 1 (p.rename bindSlots),?_⟩
  intro B hB e
  simp only [Formula.Eval,Formula.eval_rename_comp,bind_mix,hp B hB]
  rfl

theorem defOr (h : Numeric P) (k : Numeric Q) : Numeric (fun e => P e ∨ Q e) :=
  (h.neg.and k.neg).neg.congr (fun _ => by tauto)
theorem defImp (h : Numeric P) (k : Numeric Q) : Numeric (fun e => P e → Q e) :=
  (h.and k.neg).neg.congr (fun _ => by tauto)
theorem defIff (h : Numeric P) (k : Numeric Q) : Numeric (fun e => P e ↔ Q e) :=
  ((defImp h k).and (defImp k h)).congr (fun _ => iff_def.symm)
theorem defAllMem (h : Numeric P) (i : ℕ) : Numeric (fun e => ∀ x ∈ e i, P (cons x e)) :=
  (h.neg.existsMem i).neg.congr (fun _ => by simp)
theorem defAllNat (h : Numeric P) : Numeric (fun e => ∀ x ∈ ZFSet.omega, P (cons x e)) :=
  h.neg.existsNat.neg.congr (fun _ => by simp)

theorem equal_definable (i j : ℕ) : Numeric (fun e => e i = e j) :=
  ⟨.equal (2*i) (2*j),fun _ _ e => by simp [Formula.Eval]⟩
theorem member_definable (i j : ℕ) : Numeric (fun e => e i ∈ e j) :=
  ⟨.member (2*i) (2*j),fun _ _ e => by simp [Formula.Eval]⟩
theorem memberNat (i : ℕ) : Numeric (fun e => e i ∈ ZFSet.omega) :=
  ⟨.member (2*i) 1,fun _ _ e => by simp [Formula.Eval,mix,params]⟩
theorem equalZero (i : ℕ) : Numeric (fun e => e i = natSet 0) :=
  ⟨.empty (2*i),fun _ _ e => by simp only [Formula.eval_empty,mix_even]; rfl⟩
theorem defSubset (i j : ℕ) : Numeric (fun e => e i ⊆ e j) :=
  defAllMem (member_definable 0 (j+1)) i
theorem defPairMem (i j g : ℕ) : Numeric (fun e => ZFSet.pair (e i) (e j) ∈ e g) :=
  ⟨.pairMem (2*i) (2*j) (2*g),fun _ _ e => by simp only [Formula.eval_pairMem,mix_even]⟩
theorem defOrderedPair (z i j : ℕ) : Numeric (fun e => e z = ZFSet.pair (e i) (e j)) :=
  ⟨.orderedPair (2*z) (2*i) (2*j),fun _ _ e => by simp only [Formula.eval_orderedPair,mix_even]⟩

theorem unaryGraph_definable (f : ℕ → ℕ) (hf : Primrec f) (i j : ℕ) :
    Numeric (fun e => UnaryGraph f (e i) (e j)) := by
  obtain ⟨p,hp⟩ := primitive_bounded_definition (Primrec.nat_iff.mp hf)
  refine ⟨.conj (.member (2*i) 1) (Formula.unary p 1 3 (2*i) (2*j)),?_⟩
  intro B hB e
  simp only [Formula.Eval,mix_even]
  change (e i ∈ ZFSet.omega ∧ (Formula.unary p 1 3 (2*i) (2*j)).Eval (mix e (params B))) ↔ _
  constructor
  · rintro ⟨hn,h⟩
    obtain ⟨n,hn⟩ := (mem_omega _).mp hn
    refine ⟨n,hn,?_⟩
    simpa only [mix_even] using (Formula.unary_spec hp 1 3 (2*i) (2*j) (mix e (params B)) rfl hB n
      (by simpa only [mix_even] using hn)).mp h
  · rintro ⟨n,hn,hj⟩
    exact ⟨(mem_omega _).mpr ⟨n,hn⟩,(Formula.unary_spec hp 1 3 (2*i) (2*j) (mix e (params B)) rfl hB n
      (by simpa only [mix_even] using hn)).mpr (by simpa only [mix_even] using hj)⟩

theorem binaryGraph_definable (f : ℕ → ℕ → ℕ) (hf : Primrec₂ f) (i j k : ℕ) :
    Numeric (fun e => BinaryGraph f (e i) (e j) (e k)) := by
  have hu : Primrec (Nat.unpaired f) := hf.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)
  obtain ⟨p,hp⟩ := primitive_bounded_definition (Primrec.nat_iff.mp hu)
  refine ⟨.conj (.member (2*i) 1) (.conj (.member (2*j) 1)
    (Formula.pairedUnary p 1 3 (2*i) (2*j) (2*k))),?_⟩
  intro B hB e
  simp only [Formula.Eval,mix_even]
  change (e i ∈ ZFSet.omega ∧ e j ∈ ZFSet.omega ∧
    (Formula.pairedUnary p 1 3 (2*i) (2*j) (2*k)).Eval (mix e (params B))) ↔ _
  have hs (a b : ℕ) (ha : e i = natSet a) (hb : e j = natSet b) :=
    Formula.pairedUnary_spec hp 1 3 (2*i) (2*j) (2*k) (mix e (params B)) rfl hB a b
      (by simpa only [mix_even] using ha) (by simpa only [mix_even] using hb)
  simp only [mix_even,Nat.unpaired,Nat.unpair_pair] at hs
  constructor
  · rintro ⟨ha,hb,h⟩
    obtain ⟨a,ha⟩ := (mem_omega _).mp ha
    obtain ⟨b,hb⟩ := (mem_omega _).mp hb
    exact ⟨a,b,ha,hb,(hs a b ha hb).mp h⟩
  · rintro ⟨a,b,ha,hb,hc⟩
    exact ⟨(mem_omega _).mpr ⟨a,ha⟩,(mem_omega _).mpr ⟨b,hb⟩,(hs a b ha hb).mpr hc⟩

end TuringRigidity.NumericSyntax

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericFamilySupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.NumericSyntax
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding RelativeConstructible
open BoundedDefinability SetModelFunctions SetModelReals
universe u
theorem setStep_definable (s c : ℕ) :
    Numeric.{u} (fun e => SetStep (e s) (e c)) := by
  have he := ((binaryGraph_definable _ (atomic_primrec 0) 1 0 (c+2)).existsNat).existsNat
  have hm := ((binaryGraph_definable _ (atomic_primrec 1) 1 0 (c+2)).existsNat).existsNat
  have ha := ((binaryGraph_definable _ (binary_primrec 2) 1 0 (c+2)).existsMem (s+1)).existsMem s
  have hn := (unaryGraph_definable _ (unary_primrec 3) 0 (c+1)).existsMem s
  have hx := (unaryGraph_definable _ (unary_primrec 4) 0 (c+1)).existsMem s
  exact defOr he (defOr hm (defOr ha (defOr hn hx)))

theorem setClosed_definable (s : ℕ) :
    Numeric.{u} (fun e => SetClosed (e s)) := by
  have hs := defAllMem (memberNat 0) s
  have hc := defAllMem (setStep_definable (s+1) 0) s
  exact (hs.and hc).congr (fun e => (setClosed_spec (e s)).symm)

theorem leastFamily_definable (q c s : ℕ) :
    Numeric.{u} (fun e => LeastFamily (e q) (e c) (e s)) := by
  have hm := defAllMem (defImp (member_definable (c+1) 0)
    (defImp (setClosed_definable 0) (defSubset (s+1) 0))) q
  exact (member_definable c s).and ((setClosed_definable s).and hm)

theorem setSupportStep_definable (g c b : ℕ) :
    Numeric.{u} (fun e => SetSupportStep (e g) (e c) (e b)) := by
  have hm : Primrec₂ (fun i j : ℕ => max i j + 1) := Primrec.succ.comp Primrec.nat_max
  have ha (t : ℕ) := (((binaryGraph_definable _ (atomic_primrec t) 1 0 (c+2)).and
    (binaryGraph_definable _ hm 1 0 (b+2))).existsNat).existsNat
  have hc := (((((binaryGraph_definable _ (binary_primrec 2) 3 2 (c+4)).and
    ((defPairMem 3 1 (g+4)).and ((defPairMem 2 0 (g+4)).and
      (binaryGraph_definable max Primrec.nat_max 1 0 (b+4))))).existsNat).existsNat).existsNat).existsNat
  have hn := ((unaryGraph_definable _ (unary_primrec 3) 0 (c+1)).and
    (defPairMem 0 (b+1) (g+1))).existsNat
  have hp : Primrec (fun n : ℕ => n-1) := Primrec.nat_sub.comp Primrec.id (Primrec.const 1)
  have hx := (((unaryGraph_definable _ (unary_primrec 4) 1 (c+2)).and
    ((defPairMem 1 0 (g+2)).and (unaryGraph_definable _ hp 0 (b+2)))).existsNat).existsNat
  exact defOr (ha 0) (defOr (ha 1) (defOr hc (defOr hn hx)))

theorem setSupportRecursion_definable (f g : ℕ) :
    Numeric.{u} (fun e => SetSupportRecursion (e f) (e g)) := by
  have hn := defAllMem (((defOrderedPair 2 1 0).existsNat).existsMem (f+1)) g
  have hr := defAllMem (defAllNat (defIff (defPairMem 1 0 (g+2))
    (setSupportStep_definable (g+2) 1 0))) f
  exact hn.and hr

end TuringRigidity.NumericSyntax

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericTruth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.NumericSyntax
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding RelativeConstructible
open BoundedDefinability SetModelFunctions SetModelReals
universe u
theorem tupleLookup_variable (G t i x : ℕ) :
    Numeric.{u} (fun e => TupleLookup (e G) (e t) (e i) (e x)) :=
  (((defOrderedPair (t+2) 1 0).and (defPairMem (i+2) (x+2) 0)).existsMem (G+1)).existsNat

theorem tuplePrefix_variable (a G t x s : ℕ) :
    Numeric.{u} (fun e => TuplePrefix (e a) (e G) (e t) (e x) (e s)) := by
  let r : ℕ → ℕ := fun i => match i with
    | 0 => 2*a | 1 => 1 | 2 => 2*G | 3 => 2*t | 4 => 2*x | 5 => 2*s | _ => 5
  refine ⟨(tuplePrefixFormula 0 1 2 3 4 5 6).rename r,?_⟩
  intro B _ e
  rw [Formula.eval_rename_comp]
  have he : mix e (params B) ∘ r = cons (e a) (cons ZFSet.omega (cons (e G)
      (cons (e t) (cons (e x) (cons (e s) (fun _ => natSet 0)))))) := by
    funext i
    rcases i with _|_|_|_|_|_|i <;> simp only [r,params,Function.comp_apply,mix_even,cons_zero,cons_succ] <;> rfl
  rw [he]
  rfl

theorem setTruthStep_variable (a G T S c t : ℕ) :
    Numeric.{u} (fun e => SetTruthStep (e a) (e G) (e T) (e S) (e c) (e t)) := by
  have ha (tag : ℕ) (hr : Numeric.{u} (fun e => e 1 = e 0)) :=
    (((((binaryGraph_definable _ (atomic_primrec tag) 3 2 (c+4)).and
      ((tupleLookup_variable (G+4) (t+4) 3 1).and
        ((tupleLookup_variable (G+4) (t+4) 2 0).and hr))).existsMem (a+3)).existsMem (a+2)).existsNat).existsNat
  have he := ha 0 (equal_definable 1 0)
  have hm := (((((binaryGraph_definable _ (atomic_primrec 1) 3 2 (c+4)).and
    ((tupleLookup_variable (G+4) (t+4) 3 1).and
      ((tupleLookup_variable (G+4) (t+4) 2 0).and (member_definable 1 0)))).existsMem (a+3)).existsMem
        (a+2)).existsNat).existsNat
  have hc := (((binaryGraph_definable _ (binary_primrec 2) 1 0 (c+2)).and
    ((defPairMem 1 (t+2) (S+2)).and (defPairMem 0 (t+2) (S+2)))).existsNat).existsNat
  have hn := ((unaryGraph_definable _ (unary_primrec 3) 0 (c+1)).and
    (defPairMem 0 (t+1) (S+1)).neg).existsNat
  have hbody := (((tuplePrefix_variable (a+3) (G+3) (t+3) 1 0).and
    (defPairMem 2 0 (S+3))).existsMem (T+2)).existsMem (a+1)
  have hx := ((unaryGraph_definable _ (unary_primrec 4) 0 (c+1)).and hbody).existsNat
  exact defOr he (defOr hm (defOr hc (defOr hn hx)))

theorem definesSubset_variable (a G T Z c t S : ℕ) :
    Numeric.{u} (fun e => DefinesSubset (e a) (e G) (e T) (e Z) (e c) (e t) (e S)) :=
  (defSubset S a).and (defAllMem (defIff (member_definable 0 (S+1))
    (((tuplePrefix_variable (a+2) (G+2) (t+2) 1 0).and
      (defPairMem (c+2) 0 (Z+2))).existsMem (T+1))) a)

theorem tupleSystem_definable (a G T : ℕ) :
    Numeric.{u} (fun e => TupleSystem (e a) (e G) (e T)) := by
  have hfg (f n a : ℕ) : Numeric.{u} (fun e => FunctionGraph (e n) (e a) (e f)) := by
    refine ⟨.functionGraph (2*f) (2*n) (2*a),?_⟩
    intro B hB e
    simp only [Formula.eval_functionGraph,mix_even,FunctionGraph]
  have hn := defAllMem ((((defOrderedPair 2 1 0).and
    (hfg 0 1 (a+3))).existsMem (G+2)).existsNat) T
  have hz : Numeric.{u} (fun e => ZFSet.pair (natSet 0) (natSet 0) ∈ e T) := (((equalZero 0).and
    (defPairMem 0 0 (T+1))).existsNat).congr (fun e => by simp [show natSet.{u} 0 ∈ ZFSet.omega from (mem_omega _).mpr ⟨0,rfl⟩])
  have hc := defAllMem (defAllMem
    ((tuplePrefix_variable (a+3) (G+3) 2 1 0).existsMem (T+2)) (a+1)) T
  exact hn.and (hz.and hc)

end TuringRigidity.NumericSyntax

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericDefSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.NumericSyntax
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding RelativeConstructible
open BoundedDefinability SetModelFunctions SetModelReals
universe u
theorem boundWitness_allBounds (Q B c b : ℕ) :
    Numeric.{u} (fun e => BoundWitness (e Q) (e B) (e c) (e b)) :=
  (((leastFamily_definable (Q+2) (c+2) 1).and
    ((setSupportRecursion_definable 1 0).and (defPairMem (c+2) (b+2) 0))).existsMem
      (B+1)).existsMem Q

theorem tupleAdequate_allBounds (Q B G c t : ℕ) :
    Numeric.{u} (fun e => TupleAdequate (e Q) (e B) (e G) (e c) (e t)) :=
  ((((defOrderedPair (t+3) 2 1).and
    ((boundWitness_allBounds (Q+3) (B+3) (c+3) 0).and
      (defSubset 0 2))).existsNat).existsMem (G+1)).existsNat

theorem setTruthRecursion_allBounds (Q B a G T f s : ℕ) :
    Numeric.{u} (fun e => SetTruthRecursion (e Q) (e B) (e G) (e a) (e T) (e f) (e s)) := by
  have hn := defAllMem ((((tupleAdequate_allBounds (Q+3) (B+3) (G+3) 1 0).and
    (defOrderedPair 2 1 0)).existsMem (T+2)).existsMem (f+1)) s
  have hr := defAllMem (defAllMem (defImp
    (tupleAdequate_allBounds (Q+2) (B+2) (G+2) 1 0)
    (defIff (defPairMem 1 0 (s+2))
      (setTruthStep_variable (a+2) (G+2) (T+2) (s+2) 1 0))) (T+1)) f
  exact hn.and hr

theorem truthWitness_allBounds (Q B a G T c s : ℕ) :
    Numeric.{u} (fun e => TruthWitness (e Q) (e B) (e G) (e a) (e T) (e c) (e s)) :=
  ((leastFamily_definable (Q+1) (c+1) 0).and
    (setTruthRecursion_allBounds (Q+1) (B+1) (a+1) (G+1) (T+1) 0 (s+1))).existsMem Q

theorem satisfactionWitness_allBounds (Q B a G H T z : ℕ) :
    Numeric.{u} (fun e => SatisfactionWitness (e Q) (e B) (e G) (e H) (e a) (e T) (e z)) :=
  ((((truthWitness_allBounds (Q+3) (B+3) (a+3) (G+3) (T+3) 2 0).and
    ((defPairMem 2 1 0).and (defOrderedPair (z+3) 2 1))).existsMem (H+2)).existsMem
      (T+1)).existsNat

theorem parameterAdequate_allBounds (Q B G c t : ℕ) :
    Numeric.{u} (fun e => ParameterAdequate (e Q) (e B) (e G) (e c) (e t)) :=
  ((((defOrderedPair (t+3) 2 1).and
    ((boundWitness_allBounds (Q+3) (B+3) (c+3) 0).and
      (defAllMem (defOr (member_definable 0 3) (equal_definable 0 3)) 0))).existsNat).existsMem (G+1)).existsNat

theorem definitionWitness_allBounds (Q B a G T Z S : ℕ) :
    Numeric.{u} (fun e => DefinitionWitness (e Q) (e B) (e G) (e a) (e T) (e Z) (e S)) :=
  (((parameterAdequate_allBounds (Q+2) (B+2) (G+2) 1 0).and
    (definesSubset_variable (a+2) (G+2) (T+2) (Z+2) 1 0 (S+2))).existsMem (T+1)).existsNat

theorem satisfactionSystem_allBounds (Q B a G T H Z : ℕ) :
    Numeric.{u} (fun e => SatisfactionSystem (e Q) (e B) (e a) (e G) (e T) (e H) (e Z)) := by
  have ht := defAllNat (defAllMem (defImp (leastFamily_definable (Q+2) 1 0)
    ((setTruthRecursion_allBounds (Q+3) (B+3) (a+3) (G+3) (T+3) 1 0).existsMem (H+2))) (Q+1))
  have hn := defAllMem (satisfactionWitness_allBounds (Q+1) (B+1) (a+1) (G+1) (H+1) (T+1) 0) Z
  have hc := defAllNat (defAllMem (defAllMem
    (defImp (truthWitness_allBounds (Q+3) (B+3) (a+3) (G+3) (T+3) 2 0)
      (defImp (defPairMem 2 1 0) (defPairMem 2 1 (Z+3)))) (H+2)) (T+1))
  exact (tupleSystem_definable a G T).and (ht.and (hn.and hc))

theorem defSystem_allBounds (Q B a G T H Z D : ℕ) :
    Numeric.{u} (fun e => DefSystem (e Q) (e B) (e a) (e G) (e T) (e H) (e Z) (e D)) := by
  have hn := defAllMem (definitionWitness_allBounds (Q+1) (B+1) (a+1) (G+1) (T+1) (Z+1) 0) D
  have hc := defAllNat (defAllMem (defImp (parameterAdequate_allBounds (Q+2) (B+2) (G+2) 1 0)
    ((definesSubset_variable (a+3) (G+3) (T+3) (Z+3) 2 1 0).existsMem (D+2))) (T+1))
  exact (satisfactionSystem_allBounds Q B a G T H Z).and (hn.and hc)

end TuringRigidity.NumericSyntax

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.NumericSyntax
open ElementaryModel BoundedSetTheory TransitiveNameModel BoundedDefinability
universe u

variable {P Q : ZFSet.{u} → (ℕ → ZFSet.{u}) → Prop}

theorem Numeric.toDomain {P : (ℕ → ZFSet.{u}) → Prop} (h : Numeric P) :
    Domain (fun _ e => P e) := by
  obtain ⟨p,hp⟩ := h
  refine ⟨fromBounded p,?_⟩
  intro B hB N hN hd e he
  rw [bounded_sat,Formula.absolute p N hN _ (by
    intro i; unfold mix; split <;> first | exact he _ | exact hd _)]
  exact hp B hB e

theorem Domain.congr (h : Domain P) (he : ∀ N e, P N e ↔ Q N e) : Domain Q := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p,fun B hB N hN hd e he' => (hp B hB N hN hd e he').trans (he N e)⟩

theorem Domain.and (h : Domain P) (k : Domain Q) : Domain (fun N e => P N e ∧ Q N e) := by
  obtain ⟨p,hp⟩ := h; obtain ⟨q,hq⟩ := k
  exact ⟨.conj p q,fun B hB N hN hd e he =>
    and_congr (hp B hB N hN hd e he) (hq B hB N hN hd e he)⟩

theorem Domain.neg (h : Domain P) : Domain (fun N e => ¬ P N e) := by
  obtain ⟨p,hp⟩ := h
  exact ⟨.neg p,fun B hB N hN hd e he => not_congr (hp B hB N hN hd e he)⟩

theorem Domain.imp (h : Domain P) (k : Domain Q) : Domain (fun N e => P N e → Q N e) :=
  (h.and k.neg).neg.congr (fun _ _ => by tauto)

theorem Domain.subst (h : Domain P) (r : ℕ → ℕ) : Domain (fun N e => P N (e ∘ r)) := by
  obtain ⟨p,hp⟩ := h
  refine ⟨p.rename (slotMap r id),?_⟩
  intro B hB N hN hd e he
  rw [SentenceForm.sat_rename]
  change p.Sat _ (mix e (params B) ∘ slotMap r id) ↔ _
  rw [mix_slotMap,Function.comp_id]
  exact hp B hB N hN hd (e ∘ r) (fun i => he (r i))

theorem Domain.existsSet (h : Domain P) : Domain (fun N e => ∃ x ∈ N, P N (cons x e)) := by
  obtain ⟨p,hp⟩ := h
  refine ⟨.ex (p.rename bindSlots),?_⟩
  intro B hB N hN hd e he
  change (∃ x ∈ N, (p.rename bindSlots).Sat _ (cons x (mix e (params B)))) ↔ _
  apply exists_congr; intro x
  apply and_congr_right; intro hx
  rw [SentenceForm.sat_rename]
  change p.Sat _ (cons x (mix e (params B)) ∘ bindSlots) ↔ _
  rw [bind_mix]
  exact hp B hB N hN hd (cons x e) (by intro i; cases i; exact hx; exact he _)

theorem Domain.allMem (h : Domain P) (a : ℕ) : Domain (fun N e => ∀ x ∈ e a, P N (cons x e)) := by
  obtain ⟨p,hp⟩ := ((member_definable 0 (a+1)).toDomain.and h.neg).existsSet.neg
  refine ⟨p,?_⟩
  intro B hB N hN hd e he
  rw [hp B hB N hN hd e he]
  change (¬ ∃ x ∈ N, x ∈ e a ∧ ¬ P N (cons x e)) ↔ _
  classical
  constructor
  · intro h x hx
    by_contra hn
    exact h ⟨x,hN _ (he a) x hx,hx,hn⟩
  · intro h ⟨x,_,hx,hn⟩
    exact hn (h x hx)

theorem powerBound_domain (a q : ℕ) : Domain (fun N e => RelativeConstructible.PowerBound N (e a) (e q)) := by
  refine ⟨FullSetForcing.ownPower (2*a) (2*q),?_⟩
  intro B hB N hN hd e he
  rw [FullSetForcing.ownPower_spec N hN _ _ _ (by
    intro i; unfold mix; split <;> first | exact he _ | exact hd _)]
  simp only [mix_even,RelativeConstructible.PowerBound]

end TuringRigidity.NumericSyntax

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.NumericSyntax
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding RelativeConstructible
open BoundedDefinability SetModelFunctions SetModelReals
universe u
theorem stageStep_definable (s f r x A : ℕ) :
    Numeric.{u} (fun e => StageStep (e s) (e f) (e r) (e x) (e A)) := by
  have hn := defAllMem (defOr (member_definable 0 (s+1))
    ((((defPairMem 1 0 (f+3)).and (member_definable 2 0)).existsMem (r+2)).existsMem (x+1))) A
  have hc := defAllMem (defAllMem (defImp (defPairMem 1 0 (f+2))
    (defSubset 0 (A+2))) (r+1)) x
  exact (defSubset s A).and (hn.and hc)

theorem functionGraph_definable (d r f : ℕ) :
    Numeric.{u} (fun e => FunctionGraph (e d) (e r) (e f)) := by
  refine ⟨.functionGraph (2*f) (2*d) (2*r),?_⟩
  intro B hB e
  simp only [Formula.eval_functionGraph,mix_even,FunctionGraph]

theorem insertedSelf_definable (s R : ℕ) :
    Numeric.{u} (fun e => e s = insert (e R) (e R)) := by
  have h := (member_definable R s).and ((defSubset R s).and
    (defAllMem (defOr (equal_definable 0 (R+1)) (member_definable 0 (R+1))) s))
  apply h.congr
  intro e
  constructor
  · rintro ⟨hR,hsub,hall⟩
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_insert_iff]
    exact ⟨fun hz => hall z hz,fun h => h.elim (fun he => he ▸ hR) (fun hz => hsub hz)⟩
  · rintro he
    rw [he]
    exact ⟨ZFSet.mem_insert_iff.mpr (Or.inl rfl),
      fun _ hz => ZFSet.mem_insert_iff.mpr (Or.inr hz),fun _ hz => ZFSet.mem_insert_iff.mp hz⟩

theorem checkedDefSuccessor_domainDefinable :
    Domain.{u} (fun N e => CheckedDefSuccessor N (e 2) (e 3) (e 1) (e 0)) := by
  have hs := (defSystem_allBounds 5 4 7 3 2 1 0 6).toDomain.existsSet.existsSet.existsSet.existsSet
  have hb := (powerBound_domain 4 1).and (powerBound_domain 5 0)
  exact (hb.and hs).existsSet.existsSet

theorem checkedHierarchyGraph_domainDefinable
    (w sq s d r f : ℕ) :
    Domain.{u} (fun N e => CheckedHierarchyGraph N (e w) (e sq) (e s) (e d) (e r) (e f)) := by
  have hd := (defAllMem (defSubset 0 (d+1)) d).toDomain
  have hf := (functionGraph_definable d r f).toDomain
  have hv := (checkedDefSuccessor_domainDefinable).subst
    (fun i => match i with | 0 => 1 | 1 => 0 | 2 => w+3 | _ => sq+3)
  have hs := (stageStep_definable (s+3) (f+3) (r+3) 2 0).toDomain.and hv
  have hi := (defPairMem 1 0 (f+2)).toDomain.imp hs.existsSet
  exact hd.and (hf.and ((hi.allMem (r+1)).allMem d))

theorem seedBoundStage_domainDefinable :
    Domain.{u} (fun N e => SeedBoundStage N (e 3) (e 4) (e 2) (e 1) (e 0)) := by
  have h := (insertedSelf_definable 3 6).toDomain.and
    ((member_definable 5 2).toDomain.and
      ((checkedHierarchyGraph_domainDefinable 7 8 3 2 0 1).and
        (stageStep_definable 3 1 0 5 4).toDomain))
  exact h.existsSet.existsSet.existsSet.existsSet

end TuringRigidity.NumericSyntax

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericBinding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.NumericSyntax
open ElementaryModel BoundedSetTheory TransitiveNameModel BoundedDefinability RelativeConstructible
universe u

theorem bindNumbers_spec (N : ZFSet.{u}) (hN : Transitive N)
    (hw : ZFSet.omega.{u} ∈ N) (hs : ZFSet.prod ZFSet.omega ZFSet.omega ∈ N)
    (p : SentenceForm) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ N) :
    (bindNumbers p).Sat (N : Set ZFSet) e ↔
      ∃ B ∈ N, PowerBound N (ZFSet.prod ZFSet.omega ZFSet.omega) B ∧
        p.Sat (N : Set ZFSet) (cons (natSet 0) (cons B
          (cons (ZFSet.prod ZFSet.omega ZFSet.omega) (cons ZFSet.omega e)))) := by
  have hc {a : ZFSet.{u}} {d : ℕ → ZFSet.{u}} (ha : a ∈ N) (hd : ∀ i, d i ∈ N) :
      ∀ i, cons a d i ∈ N := by intro i; cases i; exact ha; exact hd _
  have hz : natSet.{u} 0 ∈ N := hN _ hw _ ((mem_omega _).mpr ⟨0,rfl⟩)
  have hwf (w : ZFSet.{u}) (hwN : w ∈ N) := canonicalOmega_spec N hN hw 0 (cons w e) (hc hwN he)
  have hsf (s : ZFSet.{u}) (hsN : s ∈ N) :
      (fromBounded (squareFormula 1 0)).Sat (N : Set ZFSet) (cons s (cons ZFSet.omega e)) ↔
        s = ZFSet.prod ZFSet.omega ZFSet.omega := by
    rw [bounded_sat,Formula.absolute _ N hN _ (hc hsN (hc hw he)),squareFormula_spec]
    rfl
  have hbf (B : ZFSet.{u}) (hBN : B ∈ N) :
      (FullSetForcing.ownPower 1 0).Sat (N : Set ZFSet)
        (cons B (cons (ZFSet.prod ZFSet.omega ZFSet.omega) (cons ZFSet.omega e))) ↔
      PowerBound N (ZFSet.prod ZFSet.omega ZFSet.omega) B := by
    rw [FullSetForcing.ownPower_spec N hN _ _ _ (hc hBN (hc hs (hc hw he)))]
    rfl
  have hzf (B z : ZFSet.{u}) (hBN : B ∈ N) (hzN : z ∈ N) :
      (fromBounded (.empty 0)).Sat (N : Set ZFSet)
        (cons z (cons B (cons (ZFSet.prod ZFSet.omega ZFSet.omega) (cons ZFSet.omega e)))) ↔
      z = natSet 0 := by
    rw [bounded_sat,Formula.absolute _ N hN _ (hc hzN (hc hBN (hc hs (hc hw he)))),Formula.eval_empty]
    rfl
  change (∃ w ∈ N, (canonicalOmega 0).Sat _ (cons w e) ∧
    ∃ s ∈ N, (fromBounded (squareFormula 1 0)).Sat _ (cons s (cons w e)) ∧
    ∃ B ∈ N, (FullSetForcing.ownPower 1 0).Sat _ (cons B (cons s (cons w e))) ∧
    ∃ z ∈ N, (fromBounded (.empty 0)).Sat _ (cons z (cons B (cons s (cons w e)))) ∧
      p.Sat _ (cons z (cons B (cons s (cons w e))))) ↔ _
  constructor
  · rintro ⟨w,hwN,hwS,s,hsN,hsS,B,hBN,hBS,z,hzN,hzS,hp⟩
    obtain rfl := (hwf w hwN).mp hwS
    obtain rfl := (hsf s hsN).mp hsS
    obtain rfl := (hzf B z hBN hzN).mp hzS
    exact ⟨B,hBN,(hbf B hBN).mp hBS,hp⟩
  · rintro ⟨B,hBN,hBS,hp⟩
    exact ⟨_,hw,(hwf _ hw).mpr rfl,_,hs,(hsf _ hs).mpr rfl,B,hBN,(hbf B hBN).mpr hBS,
      _,hz,(hzf B _ hBN hz).mpr rfl,hp⟩

theorem finiteGraph_subset (f : ℕ → ℕ) (k : ℕ) :
    finiteNaturalGraph.{u} f k ⊆ ZFSet.prod ZFSet.omega ZFSet.omega := by
  intro z hz
  obtain ⟨i,_,rfl⟩ := (mem_finiteNaturalGraph f k z).mp hz
  exact ZFSet.mem_prod.mpr ⟨_,(mem_omega _).mpr ⟨i,rfl⟩,_,(mem_omega _).mpr ⟨f i,rfl⟩,rfl⟩

theorem covers_of_power {N B : ZFSet.{u}}
    (hfin : ∀ f k, finiteNaturalGraph f k ∈ N)
    (hB : PowerBound N (ZFSet.prod ZFSet.omega ZFSet.omega) B) : Covers B :=
  fun f k => (hB _).mpr ⟨hfin f k,finiteGraph_subset f k⟩

end TuringRigidity.NumericSyntax

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.NumericSyntax
open ElementaryModel BoundedSetTheory TransitiveNameModel BoundedDefinability RelativeConstructible
universe u

theorem stageSlots_comp (B : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    cons (natSet 0) (cons B (cons (ZFSet.prod ZFSet.omega ZFSet.omega)
      (cons ZFSet.omega e))) ∘ stageSlots = mix (stageInputs e) (params B) := by
  apply parity_ext
  · intro n
    rcases n with _|_|_|_|n <;> simp [stageSlots,stageInputs,mix]
  · intro n
    rcases n with _|_|n <;> simp [stageSlots,params,Nat.add_div,mix]

theorem stage_formula :
    ∃ p : SentenceForm, ∀ N : ZFSet.{u}, Transitive N →
      ZFSet.omega ∈ N → ZFSet.prod ZFSet.omega ZFSet.omega ∈ N →
      (∀ f k, finiteNaturalGraph f k ∈ N) →
      (∃ B ∈ N, PowerBound N (ZFSet.prod ZFSet.omega ZFSet.omega) B) →
      ∀ e, (∀ i, e i ∈ N) →
        (p.Sat (N : Set ZFSet) e ↔
          SeedBoundStage N ZFSet.omega (ZFSet.prod ZFSet.omega ZFSet.omega) (e 2) (e 1) (e 0)) := by
  obtain ⟨p,hp⟩ := seedBoundStage_domainDefinable.{u}
  refine ⟨bindNumbers (p.rename stageSlots),?_⟩
  intro N hN hw hs hfin hex e he
  rw [bindNumbers_spec N hN hw hs _ e he]
  have hbody (B : ZFSet.{u}) (hBN : B ∈ N)
      (hB : PowerBound N (ZFSet.prod ZFSet.omega ZFSet.omega) B) :
      (p.rename stageSlots).Sat (N : Set ZFSet)
        (cons (natSet 0) (cons B (cons (ZFSet.prod ZFSet.omega ZFSet.omega) (cons ZFSet.omega e)))) ↔
      SeedBoundStage N ZFSet.omega (ZFSet.prod ZFSet.omega ZFSet.omega) (e 2) (e 1) (e 0) := by
    rw [SentenceForm.sat_rename]
    change p.Sat (N : Set ZFSet)
      (cons (natSet 0) (cons B (cons (ZFSet.prod ZFSet.omega ZFSet.omega) (cons ZFSet.omega e))) ∘ stageSlots) ↔ _
    rw [stageSlots_comp]
    apply hp B (covers_of_power hfin hB) N hN
    · intro i
      rcases i with _|_|i
      · exact hw
      · exact hBN
      · exact hN _ hw _ ((mem_omega _).mpr ⟨0,rfl⟩)
    · intro i
      rcases i with _|_|_|_|i
      · exact he 0
      · exact he 1
      · exact he 2
      · exact hw
      · exact hs
  constructor
  · rintro ⟨B,hBN,hB,h⟩
    exact (hbody B hBN hB).mp h
  · intro h
    obtain ⟨B,hBN,hB⟩ := hex
    exact ⟨B,hBN,hB,(hbody B hBN hB).mpr h⟩

end TuringRigidity.NumericSyntax

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ParameterFreeOrdinalStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelFunctions
universe u

theorem parameter_free_ordinal_stage :
    ∃ p : SentenceForm, ∀ M : ZFSet.{u}, Transitive M → SourceT M →
      ∀ o : Ordinal.{u}, o.toZFSet ∈ M →
        ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧
          ∀ δ : Ordinal.{u}, δ.toZFSet ∈ M → γ ≤ δ →
            o.toZFSet ∈ level (groundReals M) δ ∧ level (groundReals M) o ∈ level (groundReals M) δ ∧
            groundReals M ∈ level (groundReals M) δ ∧
            ∀ A ∈ level (groundReals M) δ,
              p.Sat (level (groundReals M) δ : Set ZFSet)
                (cons A (cons o.toZFSet (fun _ => groundReals M))) ↔ A = level (groundReals M) o := by
  obtain ⟨p,hp⟩ := NumericSyntax.stage_formula.{u}
  refine ⟨p,?_⟩
  intro M hM hT o ho
  let R := groundReals M
  let N := relativeModel M R
  have hR := groundReals_mem M hM hT
  have C := ground_relative_context M hM hT
  obtain ⟨B,hBN,hB,hcover⟩ := internal_finite_natural_graph_bound N C.transitive C.pairing C.union
    C.power C.separation C.omega_mem
  let e := cons ZFSet.omega (cons (ZFSet.prod ZFSet.omega ZFSet.omega) (cons B (fun _ => R)))
  have he (i : ℕ) (_hi : i < 4) : InRelativeModel M R (e i) := by
    apply (mem_relativeModel M R _ hM hT hR).mp
    rcases i with _|_|_|i
    · exact C.omega_mem
    · exact C.prod_mem C.omega_mem C.omega_mem
    · exact hBN
    · exact (mem_relativeModel M R R hM hT hR).mpr (parameter_in_relativeModel M R hM hT)
  obtain ⟨β,hβ,hβe⟩ := finite_parameters_in_relative_level M R hM hT e 4 he
  obtain ⟨α,hα,hαspec⟩ := seed_bound_stage_at_levels M o.toZFSet hM hT
    ((ground_relativeModel_ordinal_iff M hM hT o).mpr ho)
  refine ⟨max α β,internal_ordinal_max M hα hβ,?_⟩
  intro δ hδ hle
  have hin (i : ℕ) (hi : i < 4) : e i ∈ level R δ :=
    level_mono R ((le_max_right α β).trans hle) (hβe i hi)
  have hL := level_transitive R δ
  have hsub : level R δ ⊆ N := fun x hx => (mem_relativeModel M R x hM hT hR).mpr ⟨δ,hδ,hx⟩
  have hBL : PowerBound (level R δ) (ZFSet.prod ZFSet.omega ZFSet.omega) B :=
    PowerBound.between hB hL hsub (hin 2 (by decide))
  have hfin (f : ℕ → ℕ) (k : ℕ) : finiteNaturalGraph f k ∈ level R δ :=
    hL B (hin 2 (by decide)) _ (hcover f k)
  obtain ⟨hoL,hAL,hstage⟩ := hαspec δ hδ ((le_max_left α β).trans hle)
  refine ⟨hoL,hAL,hin 3 (by decide),?_⟩
  intro A hA
  have hv : ∀ i, cons A (cons o.toZFSet (fun _ => R)) i ∈ level R δ := by
    intro i; rcases i with _|_|i
    · exact hA
    · exact hoL
    · exact hin 3 (by decide)
  exact (hp (level R δ) hL (hin 0 (by decide)) (hin 1 (by decide)) hfin
    ⟨B,hin 2 (by decide),hBL⟩ _ hv).trans (hstage A)

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

theorem Construction.stageInputs_eq (t : Construction.{u}) (R : ZFSet.{u}) (k : ℕ) :
    t.stageInputs R k = stageParameter R (t.ordinalData k) := by
  unfold Construction.stageInputs Construction.ordinalData
  cases t.inputData k <;> rfl

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_CanonicalRealsSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem canonicalReals_spec (M : ZFSet.{u}) (hM : Transitive M)
    (hw : ZFSet.omega.{u} ∈ M)
    (r : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (canonicalReals r).Sat (M : Set ZFSet) e ↔ e r = groundReals M := by
  have hc (w : ZFSet.{u}) (hwM : w ∈ M) : ∀ i, cons w e i ∈ M := by
    intro i; cases i; exact hwM; exact he _
  have hpower : (FullSetForcing.ownPower 0 (r+1)).Sat (M : Set ZFSet) (cons ZFSet.omega e) ↔
      e r = groundReals M := by
    rw [FullSetForcing.ownPower_spec M hM 0 (r+1) _ (hc _ hw)]
    simp only [cons_succ,cons_zero]
    constructor
    · intro h
      exact ZFSet.ext fun x => (h x).trans (mem_groundReals M x).symm
    · intro h x
      rw [h,mem_groundReals]
  change (∃ w ∈ M, (canonicalOmega 0).Sat (M : Set ZFSet) (cons w e) ∧
    (FullSetForcing.ownPower 0 (r+1)).Sat (M : Set ZFSet) (cons w e)) ↔ _
  constructor
  · rintro ⟨w,hwM,hwS,hp⟩
    obtain rfl := (canonicalOmega_spec M hM hw 0 _ (hc w hwM)).mp hwS
    exact hpower.mp hp
  · intro h
    exact ⟨_,hw,(canonicalOmega_spec M hM hw 0 _ (hc _ hw)).mpr rfl,hpower.mpr h⟩

theorem groundReals_between (M N : ZFSet.{u}) (hN : Transitive N)
    (hNM : N ⊆ M) (hR : groundReals M ∈ N) : groundReals N = groundReals M := by
  apply ZFSet.ext; intro x
  rw [mem_groundReals,mem_groundReals]
  exact ⟨fun hx => ⟨hNM hx.1,hx.2⟩,
    fun hx => ⟨hN _ hR x ((mem_groundReals M x).mpr hx),hx.2⟩⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_OwnRealsConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem Construction.ownRealsSlots_env (t : Construction.{u}) (R : ZFSet.{u})
    (P : Oracle) (z : ZFSet.{u}) :
    (fun i => cons R (cons z (t.ownRealsInputs R P)) (t.ownRealsSlots i)) =
      cons z (t.arithmeticFreeInputs R P) := by
  funext i
  rcases i with _|_|_|i
  · rfl
  · rfl
  · rfl
  · change (cons R (cons z (t.ownRealsInputs R P)))
      (match t.ordinalData i with | none => 0 | some _ => i+3) = t.stageInputs R i
    rw [t.stageInputs_eq]
    cases hidx : t.ordinalData i <;> simp [Construction.ownRealsInputs,hidx,cons,stageParameter]

theorem Construction.ownRealsInputs_mem (t : Construction.{u}) (M R : ZFSet.{u})
    (P : Oracle) (he : ∀ i, t.singleInputs R P i ∈ M) : ∀ i, t.ownRealsInputs R P i ∈ M := by
  intro i
  cases i with
  | zero => exact he 1
  | succ k =>
    have hs : t.stageInputs R k ∈ M := he (k+5)
    rw [t.stageInputs_eq] at hs
    change (match t.ordinalData k with | none => realCode P | some o => level R o) ∈ M
    cases hidx : t.ordinalData k with
    | none => exact he 1
    | some o => simpa only [hidx,stageParameter] using hs

theorem Construction.ownRealsMembership_spec (t : Construction.{u}) (M R : ZFSet.{u})
    (hM : Transitive M) (hR : groundReals M = R) (P : Oracle) (ht : t.Certified R P)
    (he : ∀ i, t.singleInputs R P i ∈ M) (hv : t.value R P ∈ M)
    (z : ZFSet.{u}) (hz : z ∈ M) :
    t.ownRealsMembership.Sat (M : Set ZFSet) (cons z (t.ownRealsInputs R P)) ↔ z ∈ t.value R P := by
  let e := cons z (t.ownRealsInputs R P)
  have he' (i : ℕ) : e i ∈ M := by
    cases i; exact hz; exact t.ownRealsInputs_mem M R P he _
  have hf (r : ZFSet.{u}) (hr : r ∈ M) :
      (canonicalReals 0).Sat (M : Set ZFSet) (cons r e) ↔ r = R := by
    rw [canonicalReals_spec M hM (he 2) 0 _
      (by intro i; cases i; exact hr; exact he' _),hR]
    rfl
  have hb : (t.arithmeticFreeMembership.rename t.ownRealsSlots).Sat (M : Set ZFSet) (cons R e) ↔
      z ∈ t.value R P := by
    rw [SentenceForm.sat_rename]
    change t.arithmeticFreeMembership.Sat (M : Set ZFSet)
      (fun i => cons R (cons z (t.ownRealsInputs R P)) (t.ownRealsSlots i)) ↔ _
    rw [t.ownRealsSlots_env]
    exact t.arithmeticFreeMembership_spec M R hM P ht he hv z hz
  change (∃ r ∈ M, (canonicalReals 0).Sat (M : Set ZFSet) (cons r e) ∧
    (t.arithmeticFreeMembership.rename t.ownRealsSlots).Sat (M : Set ZFSet) (cons r e)) ↔ _
  constructor
  · rintro ⟨r,hr,hrS,hp⟩
    obtain rfl := (hf r hr).mp hrS
    exact hb.mp hp
  · intro hp
    exact ⟨R,he 0,(hf R (he 0)).mpr rfl,hb.mpr hp⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalInputSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem ownStageFormula_spec (p : SentenceForm) (N R x A : ZFSet.{u}) (hN : Transitive N)
    (hw : ZFSet.omega.{u} ∈ N) (hR : groundReals N = R) (hRN : R ∈ N)
    (hA : A ∈ N) (hx : x ∈ N) :
    (ownStageFormula p).Sat (N : Set ZFSet) (cons A (fun _ => x)) ↔
      p.Sat (N : Set ZFSet) (cons A (cons x (fun _ => R))) := by
  have hf (r : ZFSet.{u}) (hr : r ∈ N) :
      (canonicalReals 0).Sat (N : Set ZFSet) (cons r (cons A (fun _ => x))) ↔ r = R := by
    rw [canonicalReals_spec N hN hw 0 _
      (by intro i; rcases i with _|_|i; exact hr; exact hA; exact hx),hR]
    rfl
  have he (r : ZFSet.{u}) :
      (fun i => cons r (cons A (fun _ => x)) (match i with | 0 => 1 | 1 => 2 | _ => 0)) =
        cons A (cons x (fun _ => r)) := by
    funext i; rcases i with _|_|i <;> rfl
  change (∃ r ∈ N, (canonicalReals 0).Sat _ (cons r (cons A (fun _ => x))) ∧
    (p.rename _).Sat _ (cons r (cons A (fun _ => x)))) ↔ _
  simp only [SentenceForm.sat_rename]
  constructor
  · rintro ⟨r,hr,h,hp⟩
    obtain rfl := (hf r hr).mp h
    exact Eq.mp (congrArg (fun f => SentenceForm.Sat (N : Set ZFSet) f p) (funext fun i => by rcases i with _|_|i <;> rfl)) hp
  · intro hp
    exact ⟨R,hRN,(hf R hRN).mpr rfl,Eq.mp (congrArg (fun f => SentenceForm.Sat (N : Set ZFSet) f p) (funext fun i => by rcases i with _|_|i <;> rfl)) hp⟩

theorem ordinalBodySlots_spec (p : SentenceForm) (N : ZFSet.{u})
    (e w : ℕ → ZFSet.{u}) :
    (p.rename (ordinalBodySlots p.bound)).Sat (N : Set ZFSet) (prependValues w p.bound e) ↔
      p.Sat (N : Set ZFSet) (cons (e 0) (cons (e 1) w)) := by
  rw [SentenceForm.sat_rename]
  apply p.finite_support
  intro i hi
  rcases i with _|_|k
  · exact prependValues_tail w p.bound e 0
  · exact prependValues_tail w p.bound e 1
  · simp only [ordinalBodySlots,ite_eq_left (show k < p.bound by omega),cons_succ]
    exact prependValues_lt w p.bound e k (by omega)

theorem Construction.ordinalMembership_spec (t : Construction.{u}) (p : SentenceForm)
    (N R : ZFSet.{u}) (P : Oracle) (z : ZFSet.{u})
    (hw : ∀ k, k < t.ownRealsMembership.bound → t.ownRealsInputs R P (k+1) ∈ N)
    (hf : ∀ k, k < t.ownRealsMembership.bound → ∀ A ∈ N,
      (t.ordinalInputFormula p k).Sat (N : Set ZFSet) (cons A (cons z (t.ordinalInputs P))) ↔
        A = t.ownRealsInputs R P (k+1)) :
    (t.ordinalMembership p).Sat (N : Set ZFSet) (cons z (t.ordinalInputs P)) ↔
      t.ownRealsMembership.Sat (N : Set ZFSet) (cons z (t.ownRealsInputs R P)) := by
  rw [Construction.ordinalMembership,bindComputed_spec N _ _ _ _ _ hw hf,
    ordinalBodySlots_spec]
  rfl

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u
attribute [local irreducible] Construction.ownRealsMembership SentenceForm.bound

theorem Construction.ordinal_definition (t : Construction.{u}) :
    ∃ q : SentenceForm, ∀ M : ZFSet.{u}, Transitive M → SourceT M →
      ∀ P : Oracle, P ∈ modelReals M → t.Certified (groundReals M) P → t.Indexed M →
        ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧
          ∀ δ : Ordinal.{u}, δ.toZFSet ∈ M → γ ≤ δ →
            t.value (groundReals M) P ∈ level (groundReals M) δ ∧
            (∀ i, t.ordinalInputs P i ∈ level (groundReals M) δ) ∧
            ∀ z ∈ level (groundReals M) δ,
              q.Sat (level (groundReals M) δ : Set ZFSet) (cons z (t.ordinalInputs P)) ↔
                z ∈ t.value (groundReals M) P := by
  classical
  obtain ⟨p,hp⟩ := parameter_free_ordinal_stage.{u}
  refine ⟨t.ordinalMembership p,?_⟩
  intro M hM hT P hP ht hi
  let R := groundReals M
  let n := t.ownRealsMembership.bound
  obtain ⟨α,hα,hvα,heα,_⟩ := t.inlined_at_level M hM hT P hP ht hi
  have hbound (k : Fin n) : ∃ β : Ordinal.{u}, β.toZFSet ∈ M ∧
      ∀ δ : Ordinal.{u}, δ.toZFSet ∈ M → β ≤ δ →
        ∀ o : Ordinal.{u}, t.ordinalData k = some o →
          o.toZFSet ∈ level R δ ∧ level R o ∈ level R δ ∧
          ∀ A ∈ level R δ,
            p.Sat (level R δ : Set ZFSet) (cons A (cons o.toZFSet (fun _ => R))) ↔ A = level R o := by
    cases hk : t.ordinalData k with
    | none =>
      refine ⟨0,internal_ordinal_zero M hM hT,?_⟩
      intro δ hδ hle o ho
      cases ho
    | some o =>
      obtain ⟨β,hβ,hβspec⟩ := hp M hM hT o (t.ordinalData_mem M hi k o hk)
      refine ⟨β,hβ,?_⟩
      intro δ hδ hle o' ho'
      have heq : o = o' := Option.some.inj ho'
      subst o'
      obtain ⟨hoL,hsL,_,hdef⟩ := hβspec δ hδ hle
      exact ⟨hoL,hsL,hdef⟩
  choose b hb hbs using hbound
  let β : Ordinal.{u} := Finset.univ.sup b
  have hβ : β.toZFSet ∈ M := internal_ordinal_finite_sup M hM hT Finset.univ b (fun i _ => hb i)
  refine ⟨max α β,internal_ordinal_max M hα hβ,?_⟩
  intro δ hδ hle
  have hαδ : α ≤ δ := (le_max_left α β).trans hle
  have hβδ : β ≤ δ := (le_max_right α β).trans hle
  have hbδ (k : Fin n) : b k ≤ δ := (Finset.le_sup (Finset.mem_univ k)).trans hβδ
  have hL := level_transitive R δ
  have hv : t.value R P ∈ level R δ := level_mono R hαδ hvα
  have he : ∀ i, t.singleInputs R P i ∈ level R δ := fun i => level_mono R hαδ (heα i)
  have hown := t.ownRealsInputs_mem (level R δ) R P he
  have hR := groundReals_mem M hM hT
  have hsame : groundReals (level R δ) = R := groundReals_between M (level R δ) hL
    (level_subset_model M R hM hT hR δ hδ) (he 0)
  have hord : ∀ i, t.ordinalInputs P i ∈ level R δ := by
    intro i
    cases i with
    | zero => exact he 1
    | succ k =>
      change (if k < n then match t.ordinalData k with | none => realCode P | some o => o.toZFSet
        else realCode P) ∈ level R δ
      by_cases hk : k < n
      · rw [ite_eq_left hk]
        cases ho : t.ordinalData k with
        | none => exact he 1
        | some o => exact (hbs ⟨k,hk⟩ δ hδ (hbδ ⟨k,hk⟩) o ho).1
      · rw [ite_eq_right hk]; exact he 1
  refine ⟨hv,hord,?_⟩
  intro z hz
  have hf (k : ℕ) (hk : k < n) (A : ZFSet.{u}) (hA : A ∈ level R δ) :
      (t.ordinalInputFormula p k).Sat (level R δ : Set ZFSet) (cons A (cons z (t.ordinalInputs P))) ↔
      A = t.ownRealsInputs R P (k+1) := by
    cases ho : t.ordinalData k with
    | none =>
      simp only [Construction.ordinalInputFormula,ho,SentenceForm.Sat,cons_zero,cons_succ,
        Construction.ordinalInputs,Construction.ownRealsInputs]
    | some o =>
      have hstage := hbs ⟨k,hk⟩ δ hδ (hbδ ⟨k,hk⟩) o ho
      simp only [Construction.ordinalInputFormula,ho,SentenceForm.sat_rename]
      have henv : (fun i => cons A (cons z (t.ordinalInputs P)) (if i = 0 then 0 else k+3)) =
          cons A (fun _ => o.toZFSet) := by
        funext i
        cases i with
        | zero => rfl
        | succ i => simp [Construction.ordinalInputs,show k < t.ownRealsMembership.bound from hk,ho]
      rw [henv,ownStageFormula_spec p (level R δ) R o.toZFSet A hL (he 2) hsame (he 0) hA hstage.1]
      simpa only [Construction.ownRealsInputs,cons_succ,ho] using hstage.2.2 A hA
  exact (t.ordinalMembership_spec p (level R δ) R P z (fun k _ => hown (k+1)) hf).trans
    (t.ownRealsMembership_spec (level R δ) R hL hsame P ht he hv z hz)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructionHeightDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u
attribute [local irreducible] Construction.ownRealsMembership SentenceForm.bound

theorem Construction.largest_domain_definition_oai (t : Construction.{u}) :
    ∃ q : SentenceForm, ∀ M : ZFSet.{u}, Transitive M → SourceT M →
      ∀ P : Oracle, P ∈ modelReals M → t.Certified (groundReals M) P → t.Indexed M →
        ∃ β : Ordinal.{u}, β.toZFSet ∈ M ∧
          ∀ a : Ordinal.{u}, a.toZFSet ∈ M → β ≤ a →
            let R := groundReals M
            let δ := a - ordinalHeight (seed R) + 1
            δ.toZFSet ∈ M ∧ t.value R P ∈ level R δ ∧
            (∀ i, t.ordinalInputs P i ∈ level R δ) ∧
            (∀ e : ℕ → ZFSet.{u}, e 0 ∈ level R δ →
              (largestOrdinalSentence.Sat (level R δ : Set ZFSet) e ↔ e 0 = a.toZFSet)) ∧
            ∀ z ∈ level R δ,
              q.Sat (level R δ : Set ZFSet) (cons z (t.ordinalInputs P)) ↔ z ∈ t.value R P := by
  obtain ⟨q,hq⟩ := t.ordinal_definition
  refine ⟨q,?_⟩
  intro M hM hT P hP ht hi
  obtain ⟨γ,hγ,hγspec⟩ := hq M hM hT P hP ht hi
  obtain ⟨β,hβ,hβspec⟩ := internal_domains_with_largest_ordinal M (groundReals M) hM hT
    (groundReals_mem M hM hT) γ hγ
  refine ⟨β,hβ,?_⟩
  intro a ha hle
  obtain ⟨hδ,hγδ,_,hmax⟩ := hβspec a ha hle
  obtain ⟨hv,he,hq⟩ := hγspec _ hδ hγδ
  exact ⟨hδ,hv,he,hmax,hq⟩

end TuringRigidity.RelativeConstructible

end OAI
end

theorem solution.{u} : type_of% @OAI.TuringRigidity.RelativeConstructible.Construction.largest_domain_definition_oai.{u} := @OAI.TuringRigidity.RelativeConstructible.Construction.largest_domain_definition_oai.{u}
