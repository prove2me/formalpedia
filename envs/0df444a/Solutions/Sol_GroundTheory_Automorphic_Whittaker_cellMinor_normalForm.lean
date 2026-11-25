-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.cellMinor_normalForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:19:54.339432+00:00
-- url     : https://prove2.me/submissions/5529c5c2-3228-4985-916e-fdbfd74c77d9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_bottomRows_injective
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_bottomRows_eq
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_submatrix_mul_of_isUpperTriangular
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_det_submatrix_of_mem_unipotent
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_mem_unipotent
import Theorems.Thm_GroundTheory_Automorphic_permGL_mul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (w : Equiv.Perm (Fin n)) {u v : GL (Fin n) F}
    (hu : u ∈ Iwasawa.unipotent F n) (hv : v ∈ Iwasawa.unipotent F n) (t : Fin n → Fˣ) :
    cellMinor w (u * Iwasawa.diagGL F n t * permGL F w * v) =
      fun k => ∏ a : Fin (k.val + 1), (t (bottomRows k a) : F) := by
  funext k
  unfold cellMinor
  have hX : ((Iwasawa.diagGL F n t * permGL F w * v : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F).submatrix (bottomRows k) (fun a => w⁻¹ (bottomRows k a)) =
      diagonal (fun a => (t (bottomRows k a) : F)) *
        (v : Matrix (Fin n) (Fin n) F).submatrix (fun a => w⁻¹ (bottomRows k a))
          (fun a => w⁻¹ (bottomRows k a)) := by
    ext a b
    simp only [Units.val_mul, Iwasawa.coe_diagGL, submatrix_apply, diagonal_mul, mul_assoc,
      permGL_mul_apply]
  have hinj : Function.Injective fun a => w⁻¹ (bottomRows k a) :=
    (Equiv.injective _).comp (bottomRows_injective k)
  rw [show u * Iwasawa.diagGL F n t * permGL F w * v =
      u * (Iwasawa.diagGL F n t * permGL F w * v) by group, Units.val_mul,
    submatrix_mul_of_isUpperTriangular ((Iwasawa.mem_unipotent F n).1 hu).1 (bottomRows_injective k)
      (fun a s h => exists_bottomRows_eq h), det_mul, hX, det_mul, det_diagonal,
    det_submatrix_of_mem_unipotent hu (bottomRows_injective k),
    det_submatrix_of_mem_unipotent hv hinj, one_mul, mul_one]
end GroundTheory.Automorphic.Whittaker
