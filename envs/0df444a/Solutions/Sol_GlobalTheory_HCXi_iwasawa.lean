-- Prove2me | solution 1 for GlobalTheory.HCXi.iwasawa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:04.893024+00:00
-- url     : https://prove2.me/submissions/834a54ad-c8a7-4767-83b8-d401b1618046

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FrameIsotropicOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MaximalCompactSubgroupProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsUnitaryOfGramEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsQr
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_KsetTransitive
import Theorems.Thm_GlobalTheory_HCXi_isUnit_det_gram_of_leftInverse
import Theorems.Thm_GlobalTheory_HCXi_Iwasawa_kset_transitive
import Theorems.Thm_GlobalTheory_HCXi_FrameOrth_frame_orthonormal_isotropic
import Theorems.Thm_GlobalTheory_HCXi_KGroup_kset_facts
import Theorems.Thm_GlobalTheory_QRDecomp_exists_qr


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
open GlobalTheory GlobalTheory.HCXi
namespace GlobalTheory.HCXi
theorem _root_.solution : ∀ k r : ℕ, 1 ≤ k → ∀ g ∈ GV k r, ∃ κ ∈ Kset k r, ∃ p ∈ Pset k r, g = κ * p := by
  intro k r hk g hg
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  obtain ⟨hF1, hF0⟩ := FrameOrth.frame_orthonormal_isotropic k r hk
  obtain ⟨-, -, hH, hK, -⟩ := KGroup.kset_facts k r
  have hHH : (Hpk k r)ᴴ * Hpk k r = 1 := hH.2
  have hL : ((frame k r)ᴴ * (Hpk k r)ᴴ * gᴴ * Hpk k r) * (g * frame k r) = 1 := by
    calc ((frame k r)ᴴ * (Hpk k r)ᴴ * gᴴ * Hpk k r) * (g * frame k r)
        = (frame k r)ᴴ * ((Hpk k r)ᴴ * (gᴴ * Hpk k r * g)) * frame k r := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hHH, Matrix.mul_one, hF1]
  obtain ⟨Q, u, hQ, hu, hud, hA⟩ := GlobalTheory.QRDecomp.exists_qr _ _ (g * frame k r)
    (isUnit_det_gram_of_leftInverse _ _ hL)
  have hQA : Q = g * frame k r * u⁻¹ := by
    rw [hA, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hud, Matrix.mul_one]
  have hQ0 : Qᴴ * Hpk k r * Q = 0 := by
    calc Qᴴ * Hpk k r * Q
        = (u⁻¹)ᴴ * ((frame k r)ᴴ * (gᴴ * Hpk k r * g) * frame k r) * u⁻¹ := by
          rw [hQA]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hg', hF0, Matrix.mul_zero, Matrix.zero_mul]
  obtain ⟨κ, hκ, hκF⟩ := Iwasawa.kset_transitive k r (r + 1) (frame k r) Q (by rw [hF1, hQ]) (by rw [hF0, hQ0])
  have hκ1 : κᴴ * κ = 1 := hκ.2
  have hκ2 : κ * κᴴ = 1 := mul_eq_one_comm.1 hκ1
  have hκs : κᴴᴴ * Hpk k r * κᴴ = Hpk k r := (hK κ hκ).1.1
  refine ⟨κ, hκ, κᴴ * g, ⟨?_, u, hu, ?_⟩, ?_⟩
  · show (κᴴ * g)ᴴ * Hpk k r * (κᴴ * g) = Hpk k r
    calc (κᴴ * g)ᴴ * Hpk k r * (κᴴ * g) = gᴴ * (κᴴᴴ * Hpk k r * κᴴ) * g := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [hκs, hg']
  · rw [Matrix.mul_assoc, hA, ← hκF, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hκ1, Matrix.one_mul]
  · rw [← Matrix.mul_assoc, hκ2, Matrix.one_mul]
end GlobalTheory.HCXi
