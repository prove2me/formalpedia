-- Prove2me | solution 1 for GlobalTheory.TvAdjust.tv_mul_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:39:10.288419+00:00
-- url     : https://prove2.me/submissions/c0cbdf87-d6e5-48f5-8c2d-df62623ecae6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ImportsTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNsmulMulVecMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsTraceZeroAdjustmentOfHermitianLattice

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
open GlobalTheory GlobalTheory.TvAdjust
namespace GlobalTheory.TvAdjust
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)
    (x v : Fin n → R) (t : R) (q : ℤ) :
    tv σ G x (q * t) *ᵥ v = v + q • ((tv σ G x t - 1) *ᵥ v) := by
  have : tv σ G x (q * t) = 1 + q • (tv σ G x t - 1) := by
    ext a b
    simp [tv, mul_assoc]
  rw [this, add_mulVec, one_mulVec, smul_mulVec]
end GlobalTheory.TvAdjust
