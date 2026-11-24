-- Prove2me | solution 1 for GlobalTheory.nabValN_eq_sum_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:35:30.992113+00:00
-- url     : https://prove2.me/submissions/f99ebb02-4322-45f3-9e44-b35d2e4be1d5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NablaValueCopiesBilinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_InvariantValueCopiesEqZeroOfLowCoeffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NabValNEqSumCoeff
import Theorems.Thm_GlobalTheory_functional_eq_sum_coeff_of_vanish
import Theorems.Thm_GlobalTheory_T_invariantValueCopies_eq_zero_of_low_coeff
import Theorems.Thm_GlobalTheory_T_nablaValueCopies_bilinear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), ∀ (P : MvPolynomial ι K), ∃ S : Finset (Fin n × Fin d →₀ ℕ), ∀ f : PS K n d, nabValN B K h w0 m f cp u P = ∑ μ ∈ S, MvPowerSeries.coeff μ f * nabValN B K h w0 m (MvPowerSeries.monomial μ (1 : K)) cp u P := by
  intro K _ _ d O _ _ B h w0 m n ι _ cp u P
  obtain ⟨h1, h2, -, -⟩ := GlobalTheory.T.nablaValueCopies_bilinear K d O B h w0 m n ι cp u
  exact functional_eq_sum_coeff_of_vanish (fun f => nabValN B K h w0 m f cp u P) P.totalDegree
    (fun f g => h1 f g P) (fun t f => h2 t f P)
    (fun f hf => GlobalTheory.T.invariantValueCopies_eq_zero_of_low_coeff K d O B h w0 m n ι cp u f P hf)
end GlobalTheory
