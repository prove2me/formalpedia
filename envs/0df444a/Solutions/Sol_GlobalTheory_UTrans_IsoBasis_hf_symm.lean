-- Prove2me | solution 1 for GlobalTheory.UTrans.IsoBasis.hf_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:13:49.066816+00:00
-- url     : https://prove2.me/submissions/2604842e-1211-4438-90b2-017f5d03316d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsotropicBasisNonorthogonalTwoVectors

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
noncomputable section
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.IsoBasis
variable {E : Type} [Field E] {n : ℕ}
namespace GlobalTheory.UTrans.IsoBasis
theorem _root_.solution {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E} (hG : IsHerm σ G) (x y : Fin n → E) :
    σ (hf σ G x y) = hf σ G y x := by
  simp only [hf, map_sum, map_mul, hG.invol, hG.herm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end GlobalTheory.UTrans.IsoBasis
