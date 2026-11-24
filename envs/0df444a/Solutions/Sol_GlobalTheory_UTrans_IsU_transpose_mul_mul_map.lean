-- Prove2me | solution 1 for GlobalTheory.UTrans.IsU.transpose_mul_mul_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:43:33.527824+00:00
-- url     : https://prove2.me/submissions/126bc0e0-b876-41b7-9c88-b9e4d1f7fdae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidNormalDetOne

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
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} {σ : R →+* R}
    {G γ : Matrix (Fin n) (Fin n) R} (h : IsU σ G γ) : γᵀ * G * γ.map σ = G := by
  ext a b
  have h1 := h (Pi.single a 1) (Pi.single b 1)
  have h2 : hf σ G (Pi.single a 1) (Pi.single b 1) = G a b := by
    simp [hf, Pi.single_apply, apply_ite σ]
  rw [h2] at h1
  rw [← h1]
  simp only [hf, Matrix.mulVec_single_one, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.col_apply, Finset.sum_mul]
  exact Finset.sum_comm
end IsU
end GlobalTheory.UTrans
