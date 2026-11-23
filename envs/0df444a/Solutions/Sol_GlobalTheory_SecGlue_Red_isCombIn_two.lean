-- Prove2me | solution 1 for GlobalTheory.SecGlue.Red.isCombIn_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:14.47115+00:00
-- url     : https://prove2.me/submissions/f759445b-6b78-438e-9bbb-64b5afc7a00d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapEqOfRed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapCompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlgHomEqMulPowOfEqLocalizationAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowCocycle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Red
namespace GlobalTheory.SecGlue.Red
theorem _root_.solution {Y : Scheme.{0}} {V : Y.Opens} {S : Type} [CommRing S] {u c w₀ w₁ : Sp S ⟶ Y}
    {a₀ a₁ : S} (h : IsCombIn V u c ![w₀, w₁] ![a₀, a₁]) :
    ∃ (hu : u ⁻¹ᵁ V = ⊤) (hc : c ⁻¹ᵁ V = ⊤) (hw₀ : w₀ ⁻¹ᵁ V = ⊤) (hw₁ : w₁ ⁻¹ᵁ V = ⊤),
      ∀ x, chartHom V c hc x = chartHom V u hu x + a₀ * (chartHom V w₀ hw₀ x - chartHom V u hu x)
        + a₁ * (chartHom V w₁ hw₁ x - chartHom V u hu x) := by
  obtain ⟨hu, hc, hw, hx⟩ := h
  exact ⟨hu, hc, hw 0, hw 1, fun x => by simpa [Fin.sum_univ_two, add_assoc] using hx x⟩
end GlobalTheory.SecGlue.Red
