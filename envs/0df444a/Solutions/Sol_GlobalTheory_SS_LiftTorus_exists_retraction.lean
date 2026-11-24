-- Prove2me | solution 1 for GlobalTheory.SS.LiftTorus.exists_retraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:32:50.605914+00:00
-- url     : https://prove2.me/submissions/0353e8e6-39f6-47cf-9781-0f278bcf36d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UniqueFactorizationMonoidAddMonoidAlgebraOfFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftOneParameterQuotientTorus
import Theorems.Thm_GlobalTheory_SS_LiftTorus_exists_eq_of_invariant
import Theorems.Thm_GlobalTheory_SS_LiftTorus_exists_units
import Theorems.Thm_GlobalTheory_TorsorUnit_coaction_coeff
import Theorems.Thm_GlobalTheory_TorsorUnit_cst_apply
import Theorems.Thm_GlobalTheory_TorsorUnit_ev_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
theorem _root_.solution [Subsingleton (CommRing.Pic A)] [Module.Free ℤ X]
    (hα : α.FaithfullyFlat) (h : ∀ (R : Type) [CommRing R], IsTorsorOn R α ρ) :
    ∃ σ : C →+* A, σ.comp α = RingHom.id A := by
  obtain ⟨u, hu⟩ := exists_units hα h
  let τ : C →+* C := (ev (RingHom.id C) u⁻¹).comp ρ
  have hτα : τ.comp α = α := (h C).2.1 _ _
  have hτ : ∀ c, ∃ a, α a = τ c := fun c => by
    refine exists_eq_of_invariant hα h _ ?_
    change ρ (ev (RingHom.id C) u⁻¹ (ρ c)) = cst X C (ev (RingHom.id C) u⁻¹ (ρ c))
    rw [← AddMonoidAlgebra.sum_coeff_single (ρ c), Finsupp.sum]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h1 : u⁻¹ (Multiplicative.ofAdd x) = u (Multiplicative.ofAdd (-x)) := by
      rw [ofAdd_neg, map_inv]; rfl
    rw [ev_single, h1, RingHom.id_apply, map_mul, coaction_coeff (h _), hu,
      AddMonoidAlgebra.single_mul_single, add_neg_cancel, cst_apply]
  choose σ hσ using hτ
  have inj := hα.injective
  refine ⟨⟨⟨⟨σ, inj ?_⟩, fun a b => inj ?_⟩, inj ?_, fun a b => inj ?_⟩, RingHom.ext fun a => inj ?_⟩
  · rw [hσ, map_one, map_one]
  · simp only [hσ, map_mul]
  · simp only [hσ, map_zero]
  · simp only [hσ, map_add]
  · exact (hσ _).trans (RingHom.congr_fun hτα a)
end GlobalTheory.SS.LiftTorus
