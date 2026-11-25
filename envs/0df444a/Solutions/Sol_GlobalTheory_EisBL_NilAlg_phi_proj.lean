-- Prove2me | solution 1 for GlobalTheory.EisBL.NilAlg.phi_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:43:04.463196+00:00
-- url     : https://prove2.me/submissions/3d62499a-4a7a-424e-87c6-9b0d38127424

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2HaarMeasure_PhiEqZeroIff
import Theorems.Thm_GlobalTheory_EisBL_NilAlg_phi_eq_zero_iff
import Theorems.Thm_GlobalTheory_EisBL_NilAlg_tau_add
import Theorems.Thm_GlobalTheory_EisBL_NilAlg_tau_smul
import Theorems.Thm_GlobalTheory_EisBL_NilAlg_tau_tau

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.EisBL GlobalTheory.EisBL.NilAlg
variable {B : Type} [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.EisBL.NilAlg
theorem _root_.solution (c : B →+* B) (hc : ∀ x, c (c x) = x) {J K : Matrix n n B} (ε : B) (hε : ε * ε = 1)
    (hJc : (J.map c)ᵀ = ε • J) (hKc : (K.map c)ᵀ = ε • K) (hJK : J * K = 1) (hKJ : K * J = 1) (h : B) (hh : c h = h)
    (X : Matrix n n B) : phi c J (proj c J K h X) = 0 := by
  rw [phi_eq_zero_iff c hJK hKJ]
  unfold proj
  rw [tau_smul c J K h hh, tau_add, tau_tau c hc ε hε hJc hKc hJK, add_comm]
end GlobalTheory.EisBL.NilAlg
