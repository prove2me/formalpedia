-- Prove2me | solution 1 for GlobalTheory.SS.LiftTorus.exists_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:10:26.577337+00:00
-- url     : https://prove2.me/submissions/9c14cef5-8a05-48bc-8ef9-081439b83754

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UniqueFactorizationMonoidAddMonoidAlgebraOfFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftOneParameterQuotientTorus
import Theorems.Thm_GlobalTheory_SS_LiftTorus_coaction_base
import Theorems.Thm_GlobalTheory_SS_LiftTorus_exists_eq_of_invariant
import Theorems.Thm_GlobalTheory_SS_LiftTorus_exists_homogeneous_cofactor
import Theorems.Thm_GlobalTheory_TorsorUnit_exists_homogeneous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.LiftTorus
open GlobalTheory.TorsorUnit
variable {X : Type} [AddCommGroup X] {A C : Type} [CommRing A] [CommRing C]
  {α : A →+* C} {ρ : C →+* AddMonoidAlgebra C X}
namespace GlobalTheory.SS.LiftTorus
theorem _root_.solution [Subsingleton (CommRing.Pic A)] (hα : α.FaithfullyFlat)
    (h : ∀ (R : Type) [CommRing R], IsTorsorOn R α ρ) (χ : X) :
    ∃ u : Cˣ, ρ u.val = AddMonoidAlgebra.single χ u.val := by
  letI : Algebra A C := α.toAlgebra
  haveI : Module.FaithfullyFlat A C := hα
  let M : X → Submodule A C := fun x =>
    { carrier := {c | ρ c = AddMonoidAlgebra.single x c}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, ha, hb, AddMonoidAlgebra.single_add]
      zero_mem' := by simp
      smul_mem' := fun a c hc => by
        simp only [Set.mem_setOf_eq] at hc ⊢
        change ρ (α a * c) = AddMonoidAlgebra.single x (α a * c)
        rw [map_mul, coaction_base h, hc, AddMonoidAlgebra.single_mul_single, zero_add] }
  have hM : ∀ x c, c ∈ M x ↔ ρ c = AddMonoidAlgebra.single x c := fun _ _ => Iff.rfl
  have hmul : M χ * M (-χ) = 1 := by
    apply le_antisymm
    · refine Submodule.mul_le.2 fun c hc d hd => ?_
      obtain ⟨a, ha⟩ := exists_eq_of_invariant hα h (c * d) (by
        rw [map_mul, (hM _ _).1 hc, (hM _ _).1 hd, AddMonoidAlgebra.single_mul_single,
          add_neg_cancel])
      exact Submodule.mem_one.2 ⟨a, ha⟩
    · rw [Submodule.one_le]
      let p : Ideal A := (M χ * M (-χ)).comap (Algebra.linearMap A C)
      by_cases hp : p = ⊤
      · have : (1 : A) ∈ p := hp ▸ Submodule.mem_top
        simpa [p] using this
      · obtain ⟨a, ha, c, c', hcc, hc⟩ := exists_homogeneous hα h χ p hp
        obtain ⟨d, hd, hd'⟩ := exists_homogeneous_cofactor h hcc hc
        refine absurd ?_ ha
        change α a ∈ M χ * M (-χ)
        rw [← hd]
        exact Submodule.mul_mem_mul hc hd'
  let I : (Submodule A C)ˣ := Units.mkOfMulEqOne _ _ hmul
  have hI : I ∈ (Submodule.unitsToPic A C).ker := Subsingleton.elim _ _
  rw [Submodule.ker_unitsToPic] at hI
  obtain ⟨u, hu⟩ := hI
  refine ⟨u, (hM _ _).1 ?_⟩
  have h1 : Submodule.span A {u.val} = M χ := congrArg Units.val hu
  rw [← h1]
  exact Submodule.mem_span_singleton_self _
end GlobalTheory.SS.LiftTorus
