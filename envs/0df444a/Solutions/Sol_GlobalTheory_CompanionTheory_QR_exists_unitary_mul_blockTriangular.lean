-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QR.exists_unitary_mul_blockTriangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:36:11.383583+00:00
-- url     : https://prove2.me/submissions/459fe96a-d428-4fdd-8c20-7cdfce35bf59

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwasawaUnitaryUpperTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QR
namespace GlobalTheory.CompanionTheory.QR
theorem _root_.solution {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (_hg : IsUnit g) :
    ∃ k ∈ Matrix.unitaryGroup (Fin m) ℂ, ∃ b : Matrix (Fin m) (Fin m) ℂ,
      g = k * b ∧ b.BlockTriangular id := by
  let e := EuclideanSpace.basisFun (Fin m) ℂ
  let f : Fin m → EuclideanSpace ℂ (Fin m) := fun j => WithLp.toLp 2 fun i => g i j
  have h : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) = Fintype.card (Fin m) := by simp
  let o := InnerProductSpace.gramSchmidtOrthonormalBasis h f
  refine ⟨e.toBasis.toMatrix o, e.toMatrix_orthonormalBasis_mem_unitary o, o.toBasis.toMatrix f, ?_,
    InnerProductSpace.gramSchmidtOrthonormalBasis_inv_isUpperTriangular h f⟩
  have hmul := Module.Basis.toMatrix_mul_toMatrix e.toBasis o.toBasis f
  rw [OrthonormalBasis.coe_toBasis] at hmul
  rw [hmul]
  ext i j
  rw [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr]
end GlobalTheory.CompanionTheory.QR
