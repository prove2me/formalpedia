-- Prove2me | solution 1 for GlobalTheory.T.invariantValueCopies_eq_zero_of_low_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:28:45.366949+00:00
-- url     : https://prove2.me/submissions/9f0b28a0-eb51-4838-84cd-1f9583b43f2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_InvariantValueCopiesEqZeroOfLowCoeff
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_InvariantValueCopiesEqZeroOfLowCoeffStatement
import Theorems.Thm_GlobalTheory_PowGerm_nabValN_eq_zero_of_coeff_eq_zero


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), ∀ (f : PS K n d) (P : MvPolynomial ι K), (∀ μ : Fin n × Fin d →₀ ℕ, μ.degree ≤ P.totalDegree → MvPowerSeries.coeff μ f = 0) → nabValN B K h w0 m f cp u P = 0 := by
  first | exact @GlobalTheory.PowGerm.nabValN_eq_zero_of_coeff_eq_zero | exact GlobalTheory.PowGerm.nabValN_eq_zero_of_coeff_eq_zero | (intros; apply GlobalTheory.PowGerm.nabValN_eq_zero_of_coeff_eq_zero <;> assumption)
end _root_.GlobalTheory.T
