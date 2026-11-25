-- Prove2me | solution 1 for GlobalTheory.SW.det_gram_rowEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:14:17.447829+00:00
-- url     : https://prove2.me/submissions/9985e3df-1736-4282-b36d-0209a8241f6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot


attribute [local simp] GlobalTheory.SW.rowEmb_apply

set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW
open Classical
namespace GlobalTheory.SW
theorem _root_.solution {E m : Type} [Field E] [NumberField E] [Fintype m] {N : ℕ}
    (W : Matrix (Fin N) m E) (ω : (E →+* ℂ) → E) :
    (((gram ℝ fun p : Fin N × (E →+* ℂ) => rowEmb W (Pi.single p.1 (ω p.2))).det : ℝ) : ℂ) =
      (normSq (Matrix.of fun k σ : E →+* ℂ => σ (ω k)).det : ℂ) ^ N *
        ∏ σ : E →+* ℂ, (W.map σ * (W.map σ)ᴴ).det := by
  set A : Matrix (E →+* ℂ) (E →+* ℂ) ℂ := Matrix.of fun k σ : E →+* ℂ => σ (ω k) with hA
  set P : Matrix (Fin N × (E →+* ℂ)) (Fin N × (E →+* ℂ)) ℂ :=
    kroneckerMap (· * ·) (1 : Matrix (Fin N) (Fin N) ℂ) A with hP
  have hdP : P.det = A.det ^ N := by simp [hP, det_kronecker]
  have key : (gram ℝ fun p : Fin N × (E →+* ℂ) => rowEmb W (Pi.single p.1 (ω p.2))).map ofRealHom
      = (P * blockDiagonal (fun σ : E →+* ℂ => W.map σ * (W.map σ)ᴴ) * Pᴴ)ᵀ := by
    ext ⟨i, k⟩ ⟨i', k'⟩
    have hR : (P * blockDiagonal (fun σ : E →+* ℂ => W.map σ * (W.map σ)ᴴ) * Pᴴ)ᵀ (i, k) (i', k')
        = ∑ σ : E →+* ℂ, ∑ j, σ (ω k' * W i' j) * conj (σ (ω k * W i j)) := by
      simp only [transpose_apply, mul_apply, Fintype.sum_prod_type, hP, hA, kroneckerMap_apply,
        one_apply, blockDiagonal_apply, conjTranspose_apply, of_apply, map_apply]
      simp [Finset.mul_sum, Finset.sum_mul, apply_ite]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [hR]
    have hreal : conj (∑ σ : E →+* ℂ, ∑ j, σ (ω k' * W i' j) * conj (σ (ω k * W i j))) =
        ∑ σ : E →+* ℂ, ∑ j, σ (ω k' * W i' j) * conj (σ (ω k * W i j)) := by
      rw [map_sum]
      refine Fintype.sum_equiv (Function.Involutive.toPerm _
        (ComplexEmbedding.involutive_conjugate E)) _ _ fun σ => ?_
      simp [map_sum]
    rw [← conj_eq_iff_re.1 hreal]
    simp [gram_apply, PiLp.inner_apply, Fintype.sum_prod_type, Complex.inner, single_vecMul]
  rw [← ofRealHom_eq_coe, RingHom.map_det, RingHom.mapMatrix_apply, key, det_transpose, det_mul,
    det_mul, det_conjTranspose, hdP, det_blockDiagonal, normSq_eq_conj_mul_self]
  simp only [star_pow, RCLike.star_def]
  ring
end GlobalTheory.SW
