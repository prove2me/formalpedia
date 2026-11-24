-- Prove2me | solution 1 for GlobalTheory.UTrans.Chain.hf_line_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:43:24.273092+00:00
-- url     : https://prove2.me/submissions/1d232dd8-cf74-4215-8b71-1bf69bf8d694

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsotropicBasisNonorthogonalTwoVectorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidNormalDetOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_QuasiReflectionEqMulTransvectionsOfHyperbolicPlaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_QuasiReflectionEqUnitaryTransvectionMul

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
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.Chain
variable {E : Type} [Field E] [CharZero E] {n : ℕ}
namespace GlobalTheory.UTrans.Chain
theorem _root_.solution (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w z : Fin n → E) (t : E) :
    hf σ G z (x + t • w) = hf σ G z x + σ t * hf σ G z w := by
  simp only [hf, Finset.mul_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end GlobalTheory.UTrans.Chain
