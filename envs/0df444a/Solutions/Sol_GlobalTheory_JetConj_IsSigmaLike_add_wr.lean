-- Prove2me | solution 1 for GlobalTheory.JetConj.IsSigmaLike.add_wr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:43:54.705245+00:00
-- url     : https://prove2.me/submissions/ef611578-a979-429d-bb36-addf2e369adc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SecondDerivSigmaProductAtZero
import Theorems.Thm_GlobalTheory_JetConj_eq_of_eqOn_compl_lattice
import Theorems.Thm_GlobalTheory_JetConj_second_deriv_sigma_product_at_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology PeriodPair
open GlobalTheory GlobalTheory.JetConj
variable {L : PeriodPair} {σ : ℂ → ℂ}
namespace GlobalTheory.JetConj
namespace IsSigmaLike
theorem _root_.solution (H : IsSigmaLike L σ) (a : ℂ) {b : ℂ} (hb : b ∉ L.lattice) :
    σ (a + b) * σ (a - b) = wr σ a * σ b ^ 2 - wr σ b * σ a ^ 2 := by
  have hσ := H.diff
  have hc := hσ.continuous
  have h1 := hσ.deriv.continuous
  have h2 := hσ.deriv.deriv.continuous
  refine congrFun (eq_of_eqOn_compl_lattice L (f := fun a => σ (a + b) * σ (a - b))
    (g := fun a => wr σ a * σ b ^ 2 - wr σ b * σ a ^ 2) (by fun_prop) (by unfold wr; fun_prop) ?_) a
  intro a ha
  have e : (fun v => σ (a + v) * σ (a - v) * σ b ^ 2 + (℘[L] a * (σ a ^ 2 * σ b ^ 2)) * σ v ^ 2) =
      fun v => σ (b + v) * σ (b - v) * σ a ^ 2 + (℘[L] b * (σ a ^ 2 * σ b ^ 2)) * σ v ^ 2 := by
    refine eq_of_eqOn_compl_lattice L (by fun_prop) (by fun_prop) fun v hv => ?_
    linear_combination σ b ^ 2 * H.add a v ha hv - σ a ^ 2 * H.add b v hb hv
  have e2 := congrArg (fun f => deriv (deriv f) 0) e
  simp only [second_deriv_sigma_product_at_zero hσ, H.deriv_zero, (H.zero_iff 0).2 (zero_mem _)] at e2
  linear_combination H.add a b ha hb - e2 / 2
end IsSigmaLike
end GlobalTheory.JetConj
