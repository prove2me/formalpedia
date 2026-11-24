-- Prove2me | solution 1 for GlobalTheory.Hadamard.norm_orthonormalBasis_det_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:15:52.860427+00:00
-- url     : https://prove2.me/submissions/cee330d0-a1a7-486e-89bc-711fdb9a6186

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
open scoped InnerProductSpace ComplexOrder
open GlobalTheory GlobalTheory.Hadamard
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace GlobalTheory.Hadamard
theorem _root_.solution (b : OrthonormalBasis ι 𝕜 E) (x : ι → E) :
    ‖b.toBasis.det x‖ ≤ ∏ k, ‖x k‖ := by
  classical
  haveI : FiniteDimensional 𝕜 E := b.toBasis.finiteDimensional_of_finite
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  letI : LocallyFiniteOrderBot ι :=
    LocallyFiniteOrderBot.ofIic ι (fun a => Finset.univ.filter (· ≤ a)) (by simp)
  have h : finrank 𝕜 E = Fintype.card ι := finrank_eq_card_basis b.toBasis
  set c := InnerProductSpace.gramSchmidtOrthonormalBasis h x with hc
  have h1 : b.toBasis.det x = b.toBasis.det c * c.toBasis.det x := by
    conv_lhs => rw [b.toBasis.det.eq_smul_basis_det c.toBasis]
    simp
  have h2 : c.toBasis.det x = ∏ i, ⟪c i, x i⟫_𝕜 := by
    convert InnerProductSpace.gramSchmidtOrthonormalBasis_det h x
  rw [h1, norm_mul, b.det_to_matrix_orthonormalBasis c, one_mul, h2, norm_prod]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_
  simpa [c.orthonormal.1 i] using norm_inner_le_norm (𝕜 := 𝕜) (c i) (x i)
end GlobalTheory.Hadamard
