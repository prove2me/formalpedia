-- Prove2me | solution 1 for GlobalTheory.SegreCoord.loc_of_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:39:07.763083+00:00
-- url     : https://prove2.me/submissions/70ee804e-6b21-425a-a69b-12bd86acb8fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates
import Theorems.Thm_GlobalTheory_SegreCoord_gs_stalkMap
import Theorems.Thm_GlobalTheory_SegreCoord_ev_stalkMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SegreCoord
variable {X : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec} {T T' : Type} [CommRing T] [CommRing T']
namespace GlobalTheory.SegreCoord
theorem _root_.solution {x : Sp T ⟶ X} {v : σ → T}
    (h : ∀ y : PrimeSpectrum T, ∃ f ∉ y.asIdeal, Loc M th (spMap (algebraMap T (Localization.Away f)) ≫ x)
      (fun i => algebraMap T (Localization.Away f) (v i))) : Loc M th x v := fun y j hy => by
  obtain ⟨f, hf, h⟩ := h y
  obtain ⟨z, rfl⟩ : ∃ z, spMap (algebraMap T (Localization.Away f)) z = y := by
    have : (y : PrimeSpectrum T) ∈ Set.range (PrimeSpectrum.comap (algebraMap T (Localization.Away f))) := by
      rw [PrimeSpectrum.localization_away_comap_range _ f]; exact hf
    exact this
  obtain ⟨u, hu⟩ := h z j hy
  let e := (asIso ((spMap (algebraMap T (Localization.Away f))).stalkMap z)).commRingCatIsoToRingEquiv
  refine ⟨Units.map e.symm.toMonoidHom u, fun i => e.injective ?_⟩
  have := hu i
  rw [gs_stalkMap _ x z _ hy, ev_stalkMap] at this
  rw [map_mul]
  exact this.trans (congrArg _ (e.apply_symm_apply _).symm)
end GlobalTheory.SegreCoord
