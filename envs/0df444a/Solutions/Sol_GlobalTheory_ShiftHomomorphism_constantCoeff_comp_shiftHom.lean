-- Prove2me | solution 1 for GlobalTheory.ShiftHomomorphism.constantCoeff_comp_shiftHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:32:17.147274+00:00
-- url     : https://prove2.me/submissions/9323500d-e838-413f-ad1c-d27e6fff6983

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftsOfSeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormalBranchesOfSeparableReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.ShiftHomomorphism
namespace GlobalTheory.ShiftHomomorphism
theorem _root_.solution (D : ℕ) (c : Fin D → ℂ) :
    (MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ)).comp (shiftHom D c).toRingHom
      = MvPolynomial.eval c := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [shiftHom, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.aeval_C, MvPolynomial.eval_C]
    first | rfl | simp [MvPowerSeries.algebraMap_apply] | simp [Algebra.algebraMap_eq_smul_one]
  · intro i; simp [shiftHom]
end GlobalTheory.ShiftHomomorphism
