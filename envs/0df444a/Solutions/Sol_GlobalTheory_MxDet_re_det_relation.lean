-- Prove2me | solution 1 for GlobalTheory.MxDet.re_det_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:02:34.693221+00:00
-- url     : https://prove2.me/submissions/0f18c08e-5477-4c17-b987-55af7a7b2fe7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ReDetRelation
import Theorems.Thm_GlobalTheory_MxDet_exists_functional
import Theorems.Thm_GlobalTheory_MxDet_det_comb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
namespace GlobalTheory.MxDet
theorem _root_.solution : ∀ (ι J : Type) [Fintype ι] [Fintype J] (e : ℕ) (a : J → ℝ) (n : J → ι → ℝ), ∑ j, MvPolynomial.C (a j) * (∑ i, MvPolynomial.C (n j i) * MvPolynomial.X i : MvPolynomial ι ℝ) ^ e = 0 → ∀ H : ι → Matrix (Fin e) (Fin e) ℂ, ∑ j, a j * (∑ i, (n j i : ℂ) • H i).det.re = 0 := by
  intro ι J _ _ e a n hrel H
  obtain ⟨T, hT⟩ := GlobalTheory.MxDet.exists_functional e fun c : Fin e → ι =>
    (∑ σ : Equiv.Perm (Fin e), (Equiv.Perm.sign σ : ℂ) * ∏ l, H (c l) (σ l) l).re
  have h := congrArg T hrel
  simp only [map_sum, map_zero, MvPolynomial.C_mul', LinearMap.map_smul, smul_eq_mul] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have := hT (n j)
  simp only [GlobalTheory.MxDet.linF, MvPolynomial.C_mul'] at this
  rw [this, GlobalTheory.MxDet.det_comb, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.re_ofReal_mul]
end GlobalTheory.MxDet
