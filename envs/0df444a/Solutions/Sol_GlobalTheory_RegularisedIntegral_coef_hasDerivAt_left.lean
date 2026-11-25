-- Prove2me | solution 1 for GlobalTheory.RegularisedIntegral.coef_hasDerivAt_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:18:19.020915+00:00
-- url     : https://prove2.me/submissions/cd50f617-8ab0-4c90-99b9-c87f57f99d55

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IntegrandAestronglyMeasurable
import Theorems.Thm_GlobalTheory_RegularisedIntegral_coef_dilate
import Theorems.Thm_GlobalTheory_RegularisedIntegral_coef_hasDerivAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_gN_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_inv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_curveL
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_rr_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open GlobalTheory GlobalTheory.RegularisedIntegral
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B6
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {α : ℝ}
namespace GlobalTheory.RegularisedIntegral
theorem _root_.solution (H : SqIntegrable D α) {A B : Mat k r → (Wq →L[ℂ] Wp)} {cA cB : ℝ} (hA : admitted α cA A)
    (hA' : admitted α cA (Ll A)) (hB : admitted α cB B) (hB' : admitted α cB (Ll B)) (dA : DL A) (dB : DL B)
    {p : SS k r} (hp : D.inSS p) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun x' : ℝ => Ph D A B (dilation₂ (x', y) p))
      (((-(rr r / x) : ℝ) : ℂ) * (Ph D (Ll A) B (dilation₂ (x, y) p) + Ph D A (Ll B) (dilation₂ (x, y) p))) x := by
  obtain ⟨K1, hK1, hK1b⟩ := aDil_gN_bound k r (a := x / 2) (b := 2 * x) (by linarith)
  have hs : Set.Ioo (x / 2) (2 * x) ∈ 𝓝 x := Ioo_mem_nhds (by linarith) (by linarith)
  have hpos : ∀ t ∈ Set.Ioo (x / 2) (2 * x), 0 < t := fun t ht => by have := ht.1; linarith
  have hr := rr_pos r
  have hd : ∀ {f : Mat k r → (Wq →L[ℂ] Wp)}, DL f → ∀ z ∈ GV k r, ∀ t ∈ Set.Ioo (x / 2) (2 * x),
      HasDerivAt (fun t => f (aDil k r t * z * (aDil k r y)⁻¹))
        ((-(rr r / t)) • Ll f (aDil k r t * z * (aDil k r y)⁻¹)) t := by
    intro f df z hz t ht
    have h := curveL f (z * (aDil k r y)⁻¹) (hpos t ht)
      (df _ (WeylGroupFacts.uh_mul (aDil_mem k r (hpos t ht)) (WeylGroupFacts.uh_mul hz (aDil_inv_mem k r hy))))
    simpa only [Matrix.mul_assoc] using h
  have key := coef_hasDerivAt H hA hA' hB hB' hp (a := fun t => aDil k r t) (b := fun _ => (aDil k r y)⁻¹)
    (κ := fun t => -(rr r / t)) hs (K := K1 + gN ((aDil k r y)⁻¹)⁻¹ + 2 * rr r / x)
    (fun t ht => aDil_mem k r (hpos t ht)) (fun t _ => aDil_inv_mem k r hy)
    (fun t ht => by
      have h1 : 0 ≤ 2 * rr r / x := by positivity
      have h2 := gN_nonneg ((aDil k r y)⁻¹)⁻¹
      have h3 := (hK1b t ⟨ht.1.le, ht.2.le⟩).2
      linarith)
    (fun t _ => by
      have h1 : 0 ≤ 2 * rr r / x := by positivity
      linarith)
    (fun t ht => by
      have h2 := gN_nonneg ((aDil k r y)⁻¹)⁻¹
      have h3 : |-(rr r / t)| ≤ 2 * rr r / x := by
        rw [abs_neg, abs_of_pos (div_pos hr (hpos t ht)), div_le_div_iff₀ (hpos t ht) hx]
        have := ht.1
        nlinarith
      linarith)
    (hd dA) (hd dB)
  rw [coef_dilate H (Ll A) B hp hx hy, coef_dilate H A (Ll B) hp hx hy]
  refine key.congr_of_eventuallyEq ?_
  filter_upwards [hs] with t ht
  exact coef_dilate H A B hp (hpos t ht) hy
end GlobalTheory.RegularisedIntegral
