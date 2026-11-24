-- Prove2me | solution 1 for GlobalTheory.Conv.exists_sumsAt_halfCurve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:01.350381+00:00
-- url     : https://prove2.me/submissions/f7e64f72-bb89-4754-b4df-8eb3267553c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSumsAtHalfCurveFraction
import Theorems.Thm_P2M_GlobalTheory_Conv_exists_valAt__halfCurve_23b766881e41
import Theorems.Thm_GlobalTheory_Conv_sumsAt_ev_of_eq
import Theorems.Thm_GlobalTheory_HolHom_HolAt_comp
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_comp
import Theorems.Thm_GlobalTheory_HolHom_valR_spMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Filter Topology
open scoped PowerSeries LaurentSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HolHom
open GlobalTheory GlobalTheory.Conv
variable {Z : Scheme.{0}}
namespace GlobalTheory.Conv
theorem _root_.solution {T : ℝ} {yT : Sp (halfRing T) ⟶ Z} {y : Sp convLaurent ⟶ Z}
    (hy : spMap (halfIncl T : halfRing T →+* convLaurent) ≫ yT = y) {χ : Sp ℂ⟦X⟧ ⟶ Z}
    {F : Type} [Field F] (ι : ℂ⸨X⸩ →+* F)
    (hχ : spMap (ι.comp (algebraMap ℂ⟦X⟧ ℂ⸨X⸩)) ≫ χ =
      spMap (ι.comp (algebraMap convLaurent ℂ⸨X⸩)) ≫ y)
    {U : Z.Opens} (hU : ⊤ ≤ χ ⁻¹ᵁ U) :
    ∃ T' ≥ T, ∀ w : ℂ, T' < w.im → ⊤ ≤ halfCurve yT w ⁻¹ᵁ U ∧
      ∀ f : Γ(Z, U), SumsAt (valR χ U f) w (valAt' (halfCurve yT w) U f) := by
  have hyU : ⊤ ≤ y ⁻¹ᵁ U := by
    intro p _
    have h1 : ⊤ ≤ (spMap (ι.comp (algebraMap convLaurent ℂ⸨X⸩)) ≫ y) ⁻¹ᵁ U := by
      rw [← hχ]
      exact fun q _ => hU (x := spMap _ q) trivial
    obtain rfl : p = spMap (ι.comp (algebraMap convLaurent ℂ⸨X⸩)) (default : PrimeSpectrum F) :=
      Subsingleton.elim (α := PrimeSpectrum convLaurent) _ _
    exact h1 (x := (default : PrimeSpectrum F)) trivial
  obtain ⟨T', hT, h₁, h₂⟩ := exists_valAt'_halfCurve hy hyU
  refine ⟨T', hT, fun w hw => ⟨h₁ w hw, fun f => ?_⟩⟩
  obtain ⟨hf, hv⟩ := h₂ f
  rw [hv w hw]
  refine sumsAt_ev_of_eq hw (ι.injective ?_)
  have e := valR_spMap (ι.comp (algebraMap ℂ⟦X⟧ ℂ⸨X⸩)) χ U hU f
  rw [hχ, valR_spMap _ y U hyU] at e
  exact e.symm
end GlobalTheory.Conv
