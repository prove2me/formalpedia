-- Prove2me | solution 1 for GlobalTheory.UTrans.PlaneRefl.hf_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:21.497888+00:00
-- url     : https://prove2.me/submissions/d6c5f339-82cd-4c28-bfb8-19aa3faadf65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SpecialUnitaryHyperbolicPlaneMemTransvections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_QuasiReflectionEqMulTransvectionsOfHyperbolicPla

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
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.PlaneRefl
variable {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)
namespace GlobalTheory.UTrans.PlaneRefl
theorem _root_.solution (a : R) (x v : Fin n → R) : hf σ G v (a • x) = σ a * hf σ G v x := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end GlobalTheory.UTrans.PlaneRefl
