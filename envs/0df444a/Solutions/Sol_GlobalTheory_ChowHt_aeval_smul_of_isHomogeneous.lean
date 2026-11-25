-- Prove2me | solution 1 for GlobalTheory.ChowHt.aeval_smul_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:33:22.114985+00:00
-- url     : https://prove2.me/submissions/7e27bf6c-f684-4795-aec3-8a682109238a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BlockSphereMeanLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallAevalLineVanishingIdealIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial NumberField
open GlobalTheory GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.ChowHt
theorem _root_.solution {k K : Type} [Field k] [Field K] [Algebra k K] {N d : ℕ}
    {g : MvPolynomial (Fin N) k} (hg : g.IsHomogeneous d) (t : K) (z : Fin N → K) :
    aeval (t • z) g = t ^ d * aeval z g := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h := hg (mem_support_iff.1 hs)
  have hd : ∑ i, s i = d := by
    rw [← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hd]
  ring
end GlobalTheory.ChowHt
