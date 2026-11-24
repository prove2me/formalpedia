-- Prove2me | solution 1 for GlobalTheory.IwahoriFactor.flip_triple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:57:36.48771+00:00
-- url     : https://prove2.me/submissions/175f4b1e-4f4a-420c-8761-0149d90c08bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UdlApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdInvOfBlockTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.IwahoriFactor
variable {O : Type} [CommRing O] {n : ℕ}
namespace GlobalTheory.IwahoriFactor
theorem _root_.solution (u l : Matrix (Fin n) (Fin n) O) (d : Fin n → O) :
    flip (u * Matrix.diagonal d * l) =
      flip u * Matrix.diagonal (fun i => d i.rev) * flip l := by
  unfold flip
  rw [← Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm, ← Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm,
    Matrix.submatrix_diagonal_equiv]
  rfl
end GlobalTheory.IwahoriFactor
