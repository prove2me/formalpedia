-- Prove2me | solution 1 for GlobalTheory.SS.FrobSub.Raises.pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:19:11.802748+00:00
-- url     : https://prove2.me/submissions/08f68460-a8dd-43a5-a7e0-c4eeed1815ef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FrobGPowAndClosedSubgroup

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FrobSub
namespace GlobalTheory.SS.FrobSub
namespace Raises
theorem _root_.solution {X Y : Scheme.{0}} (ν : Y ⟶ X) {φ : X ⟶ X} {ψ : Y ⟶ Y} (hc : ψ ≫ ν = ν ≫ φ) {a : ℕ}
    {V : X.Opens} {g : Γ(X, V)} (h : Raises φ a V g) : Raises ψ a (ν ⁻¹ᵁ V) ((ν.app V).hom g) := by
  obtain ⟨e, p⟩ := h
  have e' : ν ⁻¹ᵁ V = ψ ⁻¹ᵁ ν ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, hc, Scheme.Hom.comp_preimage, ← e]
  refine ⟨e', ?_⟩
  have k : ∀ (θ θ' : Y ⟶ X) (_ : θ = θ') h h', θ.appLE V (ν ⁻¹ᵁ V) h = θ'.appLE V (ν ⁻¹ᵁ V) h' := by
    rintro _ _ rfl _ _; rfl
  have k2 : ν.appLE V (ν ⁻¹ᵁ V) le_rfl ≫ ψ.appLE _ _ e'.le =
      φ.appLE V V e.le ≫ ν.appLE V (ν ⁻¹ᵁ V) le_rfl := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact k _ _ hc _ _
  rw [Scheme.Hom.app_eq_appLE]
  have := congrArg (fun t => t.hom g) k2
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [this, p, map_pow]
end Raises
end GlobalTheory.SS.FrobSub
