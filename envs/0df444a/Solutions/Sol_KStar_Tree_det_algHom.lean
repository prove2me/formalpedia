-- Prove2me | solution 1 for KStar.Tree.det_algHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:25:33.462715+00:00
-- url     : https://prove2.me/submissions/2197e29f-21f2-4ee2-a725-7f4bca361711

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_SkolemNoether
import Theorems.Thm_KStar_Tree_exists_conj_of_algHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar KStar.Tree
namespace KStar.Tree
theorem _root_.solution {B : Type} [CommRing B] [IsLocalRing B] {r : ℕ}
    (θ : Matrix (Fin r) (Fin r) B →ₐ[B] Matrix (Fin r) (Fin r) B) (x : Matrix (Fin r) (Fin r) B) : (θ x).det = x.det := by
  obtain ⟨J, hJ⟩ := exists_conj_of_algHom θ
  have h := congrArg Matrix.det (hJ x)
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (J : Matrix (Fin r) (Fin r) B).det] at h
  have hu : IsUnit (J : Matrix (Fin r) (Fin r) B).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp J.isUnit
  exact hu.mul_right_cancel h
end KStar.Tree
