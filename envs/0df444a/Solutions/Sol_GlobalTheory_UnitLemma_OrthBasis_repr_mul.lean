-- Prove2me | solution 1 for GlobalTheory.UnitLemma.OrthBasis.repr_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:59:08.387371+00:00
-- url     : https://prove2.me/submissions/8b97b24b-db89-4601-a0ef-484f8d9be54b

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
theorem _root_.solution {n : ℕ} (e : Module.Basis (Fin n) K.E B.A) (g z : B.A) (i : Fin n) :
    e.repr (g * z) i = ∑ j, e.repr z j * e.repr (g * e j) i := by
  conv_lhs => rw [← e.sum_repr z]
  rw [Finset.mul_sum, map_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]
end GlobalTheory.UnitLemma.OrthBasis
