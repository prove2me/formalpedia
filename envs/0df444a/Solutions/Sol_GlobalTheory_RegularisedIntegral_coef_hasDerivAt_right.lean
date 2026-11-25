-- Prove2me | solution 1 for GlobalTheory.RegularisedIntegral.coef_hasDerivAt_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:50:27.575804+00:00
-- url     : https://prove2.me/submissions/9644cf20-6af5-457c-b954-8069f8602a01

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IntegrandAestronglyMeasurable
import Theorems.Thm_GlobalTheory_RegularisedIntegral_coef_dilate
import Theorems.Thm_GlobalTheory_RegularisedIntegral_coef_hasDerivAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_gN_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_inv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_curveR
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_rr_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
    (hA' : admitted α cA (Rr A)) (hB : admitted α cB B) (hB' : admitted α cB (Rr B)) (dA : DR A) (dB : DR B)
    {p : SS k r} (hp : D.inSS p) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun y' : ℝ => Ph D A B (dilation₂ (x, y') p))
      (((-(rr r / y) : ℝ) : ℂ) * (Ph D (Rr A) B (dilation₂ (x, y) p) + Ph D A (Rr B) (dilation₂ (x, y) p))) y := by
  obtain ⟨K1, hK1, hK1b⟩ := aDil_gN_bound k r (a := y / 2) (b := 2 * y) (by linarith)
  have hs : Set.Ioo (y / 2) (2 * y) ∈ 𝓝 y := Ioo_mem_nhds (by linarith) (by linarith)
  have hpos : ∀ t ∈ Set.Ioo (y / 2) (2 * y), 0 < t := fun t ht => by have := ht.1; linarith
  have hr := rr_pos r
  have hd : ∀ {f : Mat k r → (Wq →L[ℂ] Wp)}, DR f → ∀ z ∈ GV k r, ∀ t ∈ Set.Ioo (y / 2) (2 * y),
      HasDerivAt (fun t => f (aDil k r x * z * (aDil k r t)⁻¹))
        ((-(rr r / t)) • Rr f (aDil k r x * z * (aDil k r t)⁻¹)) t := by
    intro f df z hz t ht
    exact curveR f (aDil k r x * z) (hpos t ht)
      (df _ (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (aDil_mem k r hx) hz) (aDil_inv_mem k r (hpos t ht))))
  have key := coef_hasDerivAt H hA hA' hB hB' hp (a := fun _ => aDil k r x) (b := fun t => (aDil k r t)⁻¹)
    (κ := fun t => -(rr r / t)) hs (K := K1 + gN (aDil k r x)⁻¹ + 2 * rr r / y)
    (fun t _ => aDil_mem k r hx) (fun t ht => aDil_inv_mem k r (hpos t ht))
    (fun t _ => by
      have h1 : 0 ≤ 2 * rr r / y := by positivity
      linarith)
    (fun t ht => by
      have h1 : 0 ≤ 2 * rr r / y := by positivity
      have h2 := gN_nonneg (aDil k r x)⁻¹
      have h3 := (hK1b t ⟨ht.1.le, ht.2.le⟩).1
      rw [Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh (aDil_mem k r (hpos t ht)))]
      linarith)
    (fun t ht => by
      have h2 := gN_nonneg (aDil k r x)⁻¹
      have h3 : |-(rr r / t)| ≤ 2 * rr r / y := by
        rw [abs_neg, abs_of_pos (div_pos hr (hpos t ht)), div_le_div_iff₀ (hpos t ht) hy]
        have := ht.1
        nlinarith
      linarith)
    (hd dA) (hd dB)
  rw [coef_dilate H (Rr A) B hp hx hy, coef_dilate H A (Rr B) hp hx hy]
  refine key.congr_of_eventuallyEq ?_
  filter_upwards [hs] with t ht
  exact coef_dilate H A B hp hx (hpos t ht)
end GlobalTheory.RegularisedIntegral
