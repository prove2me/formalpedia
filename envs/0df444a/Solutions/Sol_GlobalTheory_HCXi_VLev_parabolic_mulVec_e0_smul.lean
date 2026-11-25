-- Prove2me | solution 1 for GlobalTheory.HCXi.VLev.parabolic_mulVec_e0_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:02:52.833156+00:00
-- url     : https://prove2.me/submissions/b7b99732-9ce9-420e-a509-669cfe80471f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLeviStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_KsetTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeLeviRecursion
import Theorems.Thm_GlobalTheory_HCXi_VLev_fvec_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.VLev
namespace GlobalTheory.HCXi.VLev
theorem _root_.solution {k r' : ℕ} {p : Mat k (1 + r')} (hp : p ∈ Pset k (1 + r')) :
    ∃ a : ℂ, p *ᵥ e0 k r' = a • e0 k r' := by
  obtain ⟨-, u, hu, hpu⟩ := hp
  refine ⟨u 0 0, ?_⟩
  ext i
  have h1 := congrFun (congrFun hpu i) 0
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_succ (n := 1 + r'), Finset.sum_eq_zero (s := Finset.univ)
    (f := fun b : Fin (1 + r') => frame k (1 + r') i b.succ * u b.succ 0)
    (fun b _ => by rw [hu (show id (0 : Fin (1 + r' + 1)) < id b.succ from Fin.succ_pos b), mul_zero])] at h1
  simp only [frame, Matrix.of_apply, fvec_zero k r' 0 rfl, add_zero] at h1
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [h1, mul_comm]
end GlobalTheory.HCXi.VLev
