-- Prove2me | solution 1 for GlobalTheory.UnitLemma.OrthBasis.herm_sum_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:59:06.784986+00:00
-- url     : https://prove2.me/submissions/710c55e8-af04-453d-8236-b76eb48ce165

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermBasisOrthonormal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.OrthBasis
open GlobalTheory.UnitLemma
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.UnitLemma.OrthBasis
theorem _root_.solution {n : ℕ} (x z : B.A) (a : Fin n → K.E) (v : Fin n → B.A) :
    B.herm x (∑ j, a j • v j) z = ∑ j, a j * B.herm x (v j) z := by
  unfold InvAlg.herm
  rw [Finset.mul_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]
end GlobalTheory.UnitLemma.OrthBasis
