-- Prove2me | solution 1 for GlobalTheory.HCXi.Funct.inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:44:58.219813+00:00
-- url     : https://prove2.me/submissions/83c87625-bd15-409f-9837-6600eb9f81fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramPositiveVolumeContinuousStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_KsetTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeEquivariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SphericalFunctionFunctionalEq
import Theorems.Thm_GlobalTheory_HCXi_Funct_gv_mul
import Theorems.Thm_GlobalTheory_HCXi_Funct_meas_v
import Theorems.Thm_GlobalTheory_HCXi_Funct_cont_of
import Theorems.Thm_GlobalTheory_T_exists_mem_Kset_mul_mem_Pset_eq
import Theorems.Thm_GlobalTheory_T_gram_positive_volume_continuous
import Theorems.Thm_GlobalTheory_T_half_volume_equivariant


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
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.Funct
namespace GlobalTheory.HCXi.Funct
theorem _root_.solution {k r : ℕ} (μK : Measure (Mt k r)) (hk : 1 ≤ k) (hμ : IsKMeas k r μK) {x : Mat k r} (hx : x ∈ GV k r)
    {g : Mat k r} (hg : g ∈ GV k r) :
    (∫⁻ κ : Mt k r, ENNReal.ofReal (vHalf k r (x * Matrix.of κ * g)) ∂μK)
      = XiE k r μK x * ENNReal.ofReal (vHalf k r g) := by
  obtain ⟨κ₀, hκ₀, p, hp, rfl⟩ := GlobalTheory.T.exists_mem_Kset_mul_mem_Pset_eq k r hk g hg
  obtain ⟨hl, hr⟩ := GlobalTheory.T.half_volume_equivariant k r hk
  have hpos := (GlobalTheory.T.gram_positive_volume_continuous k r hk).2.1
  have hae : ∀ᵐ κ ∂μK, (Matrix.of κ : Mat k r) ∈ Kset k r := hμ.1.conc
  have hm : Measurable fun κ : Mt k r => ENNReal.ofReal (vHalf k r (x * Matrix.of κ)) :=
    meas_v hk (continuous_const.matrix_mul cont_of)
  have hm2 : Measurable fun κ : Mt k r => ENNReal.ofReal (vHalf k r (x * (Matrix.of κ * κ₀))) :=
    meas_v hk (continuous_const.matrix_mul (cont_of.matrix_mul continuous_const))
  have hrm : Measurable (rmulF κ₀ : Mt k r → Mt k r) :=
    Continuous.measurable (by unfold Formalism.FourierDecayAlt.B.rmulF; exact continuous_id.matrix_mul continuous_const)
  have h1 : XiE k r μK x = ∫⁻ κ : Mt k r, ENNReal.ofReal (vHalf k r (x * (Matrix.of κ * κ₀))) ∂μK := by
    unfold XiE
    conv_lhs => rw [← hμ.1.right κ₀ hκ₀]
    rw [lintegral_map hm hrm]
    rfl
  rw [h1, ← lintegral_mul_const _ hm2, hl κ₀ hκ₀ p]
  refine lintegral_congr_ae (hae.mono fun κ hκ => ?_)
  have hmem : x * (Matrix.of κ * κ₀) ∈ GV k r := gv_mul hx (gv_mul hκ.1 hκ₀.1)
  have e : x * Matrix.of κ * (κ₀ * p) = x * (Matrix.of κ * κ₀) * p := by
    simp only [Matrix.mul_assoc]
  show ENNReal.ofReal _ = ENNReal.ofReal _ * ENNReal.ofReal _
  rw [e, hr _ hmem p hp, ENNReal.ofReal_mul (hpos _ hmem).le]
end GlobalTheory.HCXi.Funct
