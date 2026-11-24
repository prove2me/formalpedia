-- Prove2me | solution 1 for GlobalTheory.AnArc.FSum_eq_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:57:38.513031+00:00
-- url     : https://prove2.me/submissions/8181252f-6b16-4228-a392-9fbd0cd7f60a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_exponent_add
import Theorems.Thm_GlobalTheory_AnArc_term_add_index
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
theorem _root_.solution (j : ℕ) [NeZero j] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (y : A.X) (v : A.V) :
    A.FSum j α th v = HahnSeries.single (A.exponent j α y) ((A.psi y : ℂ) ^ j * eTwoPi (A.T y α)) *
      A.FSum j (α + j • y) (fun z => th (z + A.ct y)) v := by
  ext n
  obtain ⟨n, rfl⟩ : ∃ m, n = m + A.exponent j α y := ⟨n - _, (sub_add_cancel _ _).symm⟩
  rw [HahnSeries.coeff_single_mul_add, coeff_FSum, coeff_FSum, Finset.mul_sum]
  symm
  refine Finset.sum_equiv (Equiv.addRight y) (fun μ => ?_) fun μ _ => ?_
  · simp [exponent_add]
  · rw [Equiv.coe_addRight, term_add_index]
end GlobalTheory.AnArc
