-- Prove2me | solution 1 for GlobalTheory.JetConj.IsSigmaLike.double
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:21:13.274409+00:00
-- url     : https://prove2.me/submissions/72a6b4a7-f8ab-407d-b3ff-206744630e39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SecondDerivSigmaProductAtZero
import Theorems.Thm_GlobalTheory_eventually_notMem_periodLattice
import Theorems.Thm_GlobalTheory_hasDerivAt_weierstrassP


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
theorem _root_.solution (H : IsSigmaLike L σ) {u : ℂ} (hu : u ∉ L.lattice) :
    σ (u + u) = -℘'[L] u * σ u ^ 4 := by
  have hσ := H.diff
  have e : (fun v => (℘[L] u - ℘[L] v) * (σ u ^ 2 * σ v ^ 2)) =ᶠ[𝓝 u] fun v => -(σ (u + v) * σ (u - v)) := by
    filter_upwards [eventually_notMem_periodLattice L hu] with v hv using H.add u v hu hv
  have d1 := ((hasDerivAt_weierstrassP L hu).const_sub (℘[L] u)).fun_mul
    (((hσ u).hasDerivAt.fun_pow 2).const_mul (σ u ^ 2))
  have d2 := (((hσ _).hasDerivAt.comp_const_add u u).fun_mul
    ((hσ _).hasDerivAt.comp_const_sub u u)).fun_neg
  have := d1.unique (d2.congr_of_eventuallyEq e)
  simp only [sub_self, H.deriv_zero, (H.zero_iff 0).2 (zero_mem _)] at this
  linear_combination -this
end IsSigmaLike
end GlobalTheory.JetConj
