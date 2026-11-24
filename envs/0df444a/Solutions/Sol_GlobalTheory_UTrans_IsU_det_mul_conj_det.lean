-- Prove2me | solution 1 for GlobalTheory.UTrans.IsU.det_mul_conj_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:55:59.920218+00:00
-- url     : https://prove2.me/submissions/148419fa-72d9-4172-bbf7-f859abd2de40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidNormalDetOne
import Theorems.Thm_GlobalTheory_UTrans_IsU_transpose_mul_mul_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
open GlobalTheory GlobalTheory.UTrans
namespace GlobalTheory.UTrans
namespace IsU
theorem _root_.solution {E : Type} [Field E] {n : ℕ} {σ : E →+* E}
    {G γ : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0) (h : IsU σ G γ) : γ.det * σ γ.det = 1 := by
  have h1 := congrArg Matrix.det h.transpose_mul_mul_map
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
  have h2 : (γ.map σ).det = σ γ.det := by
    rw [RingHom.map_det]; rfl
  rw [h2] at h1
  apply mul_left_cancel₀ hG
  linear_combination h1
end IsU
end GlobalTheory.UTrans
