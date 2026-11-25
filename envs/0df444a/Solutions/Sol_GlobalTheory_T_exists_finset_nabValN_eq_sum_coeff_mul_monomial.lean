-- Prove2me | solution 1 for GlobalTheory.T.exists_finset_nabValN_eq_sum_coeff_mul_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:43:13.492514+00:00
-- url     : https://prove2.me/submissions/b480afec-6ca0-4d80-afcc-202ea6ef25ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NabValNEqSumCoeff
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NabValNEqSumCoeffStatement
import Theorems.Thm_GlobalTheory_nabValN_eq_sum_coeff


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
theorem _root_.solution : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), ∀ (P : MvPolynomial ι K), ∃ S : Finset (Fin n × Fin d →₀ ℕ), ∀ f : PS K n d, nabValN B K h w0 m f cp u P = ∑ μ ∈ S, MvPowerSeries.coeff μ f * nabValN B K h w0 m (MvPowerSeries.monomial μ (1 : K)) cp u P := by
  first | exact @GlobalTheory.nabValN_eq_sum_coeff | exact GlobalTheory.nabValN_eq_sum_coeff | (intros; apply GlobalTheory.nabValN_eq_sum_coeff <;> assumption)
end _root_.GlobalTheory.T
