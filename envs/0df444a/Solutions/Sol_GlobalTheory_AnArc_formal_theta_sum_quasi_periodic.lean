-- Prove2me | solution 1 for GlobalTheory.AnArc.formal_theta_sum_quasi_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:34:26.505933+00:00
-- url     : https://prove2.me/submissions/0d570837-2276-4d6d-aad7-1d7e509cb1cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_term_add_P0
import Theorems.Thm_GlobalTheory_AnArc_coeff_FSum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution {j : ℕ} [NeZero j] {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) {la : A.La}
    (hy : la.y = 0) (v : A.V) : A.FSum j α th (v + A.P0 la) = A.ah la.l v.2 ^ j • A.FSum j α th v := by
  ext n
  simp only [coeff_FSum, HahnSeries.coeff_smul, smul_eq_mul, A.term_add_P0 h hy, Finset.mul_sum]
end GlobalTheory.AnArc
