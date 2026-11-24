-- Prove2me | solution 1 for GlobalTheory.WeightTwoSum.modPt_im_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:14:25.090245+00:00
-- url     : https://prove2.me/submissions/796aa387-1330-4074-81d1-978bd01c9dd2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Theorems.Thm_GlobalTheory_WeightTwoSum_dz_apply
import Theorems.Thm_GlobalTheory_WeightTwoSum_dzbar_apply
import Theorems.Thm_GlobalTheory_WeightTwoSum_one_add_ne_zero
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


attribute [local simp] GlobalTheory.WeightTwoSum.dz_apply
attribute [local simp] GlobalTheory.WeightTwoSum.dzbar_apply

set_option autoImplicit false
noncomputable section
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open scoped ContDiff
open GlobalTheory GlobalTheory.WeightTwoSum
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
omit [Fintype I]
namespace GlobalTheory.WeightTwoSum
theorem _root_.solution {Φ : Type} (φ : I → E →+* ℂ) (e : I ≃ Φ) (θ : E) (hθ : ∀ i, 0 < (φ i θ).im)
    {z : I → ℂ} (hz : z ∈ polydisc I) (τ : Φ) : 0 < (modPt φ e θ z τ).im := by
  unfold modPt defCoord
  set i := e.symm τ
  have h0 : 0 < Complex.normSq (1 + z i) := Complex.normSq_pos.2 (one_add_ne_zero hz i)
  have h1 : Complex.normSq (z i) < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have := hz i
    nlinarith [norm_nonneg (z i)]
  rw [Complex.div_im, ← sub_div]
  refine div_pos ?_ h0
  rw [Complex.normSq_apply] at h1
  have h2 := hθ i
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.one_re,
    Complex.one_im]
  nlinarith [mul_pos h2 (sub_pos.2 h1)]
end GlobalTheory.WeightTwoSum
