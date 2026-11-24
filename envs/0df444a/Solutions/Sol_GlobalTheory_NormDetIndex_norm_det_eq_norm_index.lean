-- Prove2me | solution 1 for GlobalTheory.NormDetIndex.norm_det_eq_norm_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:31:06.733832+00:00
-- url     : https://prove2.me/submissions/9eb5389b-5f24-4882-a508-79efd44d2af6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NormCardQuotientSpan
import Theorems.Thm_GlobalTheory_NormDetIndex_norm_card_quotient_span
import Theorems.Thm_GlobalTheory_NormDetIndex_norm_eq_of_associated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormDetIndex
open Module Submodule
namespace GlobalTheory.NormDetIndex
theorem _root_.solution (l : ℕ) [Fact (Nat.Prime l)] {κ : Type} [Fintype κ]
    [DecidableEq κ] (M : Matrix κ κ ℤ_[l]) (hM : M.det ≠ 0) :
    ‖M.det‖ = ‖((LinearMap.range M.mulVecLin).toAddSubgroup.index : ℚ_[l])‖ := by
  set N := LinearMap.range M.mulVecLin with hN
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hM hv
  let e : (κ → ℤ_[l]) ≃ₗ[ℤ_[l]] N := LinearEquiv.ofInjective _ hinj
  let b : Basis κ ℤ_[l] (κ → ℤ_[l]) := Pi.basisFun _ _
  have h : finrank ℤ_[l] N = finrank ℤ_[l] (κ → ℤ_[l]) := e.symm.finrank_eq
  let a := smithNormalFormCoeffs b h
  let b' := smithNormalFormTopBasis b h
  let ab := smithNormalFormBotBasis b h
  let e' : (κ → ℤ_[l]) ≃ₗ[ℤ_[l]] N := b'.equiv ab (Equiv.refl _)
  have h1 : M.det = LinearMap.det (N.subtype ∘ₗ (e : (κ → ℤ_[l]) →ₗ[ℤ_[l]] N)) := by
    rw [← LinearMap.det_toLin' M]
    rfl
  have h2 : LinearMap.det (N.subtype ∘ₗ (e' : (κ → ℤ_[l]) →ₗ[ℤ_[l]] N)) = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    have ha : (N.subtype ∘ₗ (e' : (κ → ℤ_[l]) →ₗ[ℤ_[l]] N)) (b' j) = a j • b' j := by
      change ((b'.equiv ab (Equiv.refl _) (b' j) : N) : κ → ℤ_[l]) = _
      rw [b'.equiv_apply, Equiv.refl_apply]
      exact smithNormalFormBotBasis_def b h j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have h3 : N.toAddSubgroup.index
      = ∏ i, Nat.card (ℤ_[l] ⧸ Ideal.span ({a i} : Set ℤ_[l])) := by
    change Nat.card ((κ → ℤ_[l]) ⧸ N) = _
    rw [Nat.card_congr (quotientEquivPiSpan N b h).toEquiv, Nat.card_pi]
  rw [h1, norm_eq_of_associated l (LinearMap.associated_det_comp_equiv N.subtype e e'), h2, h3,
    Nat.cast_prod, norm_prod, norm_prod]
  exact Finset.prod_congr rfl fun i _ =>
    (norm_card_quotient_span l (smithNormalFormCoeffs_ne_zero b h i)).symm
end GlobalTheory.NormDetIndex
