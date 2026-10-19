-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.soft_information_identity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:19:57.171282+00:00
-- url     : https://prove2.me/submissions/d74ab708-ece8-475b-94ea-6d9e8ec7687a

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/SoftChannel/SoftInformation.lean:L70-L87
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.soft_information_identity. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SoftChannel204
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Model
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LambdaScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_JensenGaps__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeVariance__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_NormalizedPair__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveLogTrapezoid__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveCalculus__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveInequality__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Comparison__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment__SoftChannel204
import Definitions.Def_OAI_InformationTheory_SoftChannel_Canonical
import Definitions.Def_OAI_InformationTheory_SoftChannel_Thinning
import Definitions.Def_OAI_InformationTheory_SoftChannel_Payment
import Definitions.Def_OAI_InformationTheory_SoftChannel_HighReserve
import Definitions.Def_OAI_InformationTheory_SoftChannel_RateSlope
import Definitions.Def_OAI_InformationTheory_SoftChannel_Wall
import Definitions.Def_OAI_InformationTheory_SoftChannel_Contraction
import Definitions.Def_OAI_InformationTheory_SoftChannel_SoftInformation
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_cubeAverage_signProbability
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_noiseOperator_signProbability

-- ---- from OAI.InformationTheory.BooleanNoise.FiniteNoise ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open scoped BigOperators

noncomputable section

universe u

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem cubeAverage_nonneg {g : Cube n → ℝ} (hg : ∀ x, 0 ≤ g x) :
    0 ≤ cubeAverage g :=
  div_nonneg (Finset.sum_nonneg fun x _ => hg x) (le_of_lt (cube_denominator_pos n))

theorem noiseKernel_symm (u : ℝ) (x y : Cube n) :
    noiseKernel u x y = noiseKernel u y x := by
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : x i = y i
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

theorem noiseKernel_col_sum (u : ℝ) (y : Cube n) :
    ∑ x, noiseKernel u x y = 1 := by
  simp_rw [noiseKernel_symm u]
  exact noiseKernel_row_sum u y

theorem cubeAverage_noiseOperator (u : ℝ) (g : Cube n → ℝ) :
    cubeAverage (noiseOperator u g) = cubeAverage g := by
  unfold cubeAverage noiseOperator
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, noiseKernel_col_sum, one_mul]

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.FiniteInformation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators

universe u v

namespace LeanBlast.CourtadeKumar

theorem xlogx_mul (a b : ℝ) :
    xlogx (a * b) = a * xlogx b + b * xlogx a := by
  by_cases ha : a = 0
  · simp [ha, xlogx]
  by_cases hb : b = 0
  · simp [hb, xlogx]
  simp only [xlogx, Real.log_mul ha hb]
  ring

theorem finite_kl_eq_entropy_sums {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (j : A → B → ℝ) (hj : ∀ a b, 0 ≤ j a b) :
    (∑ a : A, ∑ b : B,
      if 0 < j a b then j a b * Real.log
        (j a b / ((∑ z : B, j a z) * (∑ z : A, j z b))) else 0) =
      (∑ a : A, ∑ b : B, xlogx (j a b)) -
        (∑ a : A, xlogx (∑ b : B, j a b)) -
        (∑ b : B, xlogx (∑ a : A, j a b)) := by
  classical
  have hterm (a : A) (b : B) :
      (if 0 < j a b then j a b * Real.log
        (j a b / ((∑ z : B, j a z) * (∑ z : A, j z b))) else 0) =
      xlogx (j a b) - j a b * Real.log (∑ z : B, j a z) -
        j a b * Real.log (∑ z : A, j z b) := by
    by_cases hp : 0 < j a b
    · have hr : 0 < ∑ z : B, j a z := lt_of_lt_of_le hp
        (Finset.single_le_sum (fun z _ => hj a z) (Finset.mem_univ b))
      have hc : 0 < ∑ z : A, j z b := lt_of_lt_of_le hp
        (Finset.single_le_sum (fun z _ => hj z b) (Finset.mem_univ a))
      rw [ite_eq_left hp, Real.log_div (ne_of_gt hp) (ne_of_gt (mul_pos hr hc)),
        Real.log_mul (ne_of_gt hr) (ne_of_gt hc)]
      unfold xlogx
      ring
    · have hz : j a b = 0 := le_antisymm (le_of_not_gt hp) (hj a b)
      simp [hz, xlogx]
  have hrow : (∑ a : A, ∑ b : B, j a b * Real.log (∑ z : B, j a z)) =
      ∑ a : A, xlogx (∑ b : B, j a b) := by
    simp only [xlogx, Finset.sum_mul]
  have hcol : (∑ a : A, ∑ b : B, j a b * Real.log (∑ z : A, j z b)) =
      ∑ b : B, xlogx (∑ a : A, j a b) := by
    rw [Finset.sum_comm]
    simp only [xlogx, Finset.sum_mul]
  simp_rw [hterm, Finset.sum_sub_distrib]
  rw [hrow, hcol]

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.FiniteDistribution ----
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem sum_signProbability (v : ℝ) : (∑ b : Bool, signProbability v b) = 1 := by
  simp only [Fintype.sum_bool, signProbability, Bool.false_eq_true, ite_false, ite_true]
  ring

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.InformationIdentity ----
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem sum_xlogx_signProbability (v : ℝ) :
    (∑ b : Bool, xlogx (signProbability v b)) = -entropy v := by
  rw [entropy_eq_binEntropy]
  have hhalf : 1 - (1 + v) / 2 = (1 - v) / 2 := by ring
  simp only [Fintype.sum_bool, signProbability, Bool.false_eq_true, ite_false, ite_true]
  rw [Real.binEntropy, hhalf]
  simp only [Real.log_inv, xlogx]
  ring

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.SoftChannel.SoftInformation ----
namespace OAI

section

noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace LeanBlast.CourtadeKumar

universe u v

lemma noiseKernel_nonneg_closed {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Icc (-1) 1) (x y : Cube n) :
    0 ≤ noiseKernel ρ x y := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith [hρ.1,hρ.2]

lemma signProbability_nonneg_soft {v : ℝ} (hv : v ∈ Icc (-1) 1) (b : Bool) :
    0 ≤ signProbability v b := by
  cases b <;> simp only [signProbability, Bool.false_eq_true, ite_false, ite_true] <;> linarith [hv.1,hv.2]

lemma softJointNat_nonneg {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Icc (-1) 1)
    (g : Cube n → ℝ) (hg : IsClosedSoft g) (b : Bool) (y : Cube n) :
    0 ≤ softJointNat ρ g b y :=
  cubeAverage_nonneg (fun x => mul_nonneg (signProbability_nonneg_soft (hg x) b) (noiseKernel_nonneg_closed hρ x y))

lemma softJointNat_posterior {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) (b : Bool) (y : Cube n) :
    softJointNat ρ g b y=signProbability (noiseOperator ρ g y) b / (2:ℝ)^n := by
  unfold softJointNat cubeAverage
  simp_rw [noiseKernel_symm ρ _ y,mul_comm (signProbability _ b)]
  change noiseOperator ρ (fun x => signProbability (g x) b) y / (2:ℝ)^n = _
  rw [noiseOperator_signProbability]

lemma softJointNat_left {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) (b : Bool) :
    (∑ y, softJointNat ρ g b y)=signProbability (cubeAverage g) b := by
  simp_rw [softJointNat_posterior]
  rw [← Finset.sum_div]
  change cubeAverage (fun y => signProbability (noiseOperator ρ g y) b)=_
  rw [cubeAverage_signProbability,cubeAverage_noiseOperator]

lemma softJointNat_right {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) (y : Cube n) :
    (∑ b, softJointNat ρ g b y)=1/(2:ℝ)^n := by
  simp_rw [softJointNat_posterior]
  rw [← Finset.sum_div,sum_signProbability]

lemma softJointNat_xlogx_bool {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) (y : Cube n) :
    (∑ b, xlogx (softJointNat ρ g b y))=xlogx (((2:ℝ)^n)⁻¹)-
      entropy (noiseOperator ρ g y)/(2:ℝ)^n := by
  simp_rw [softJointNat_posterior,div_eq_mul_inv,xlogx_mul]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum,
    sum_signProbability,sum_xlogx_signProbability]
  ring

theorem soft_information_identity {n : ℕ} (g : Cube n → ℝ) (hg : IsClosedSoft g)
    {ρ : ℝ} (hρ : ρ ∈ Icc (-1) 1) :
    mutualInformationNat (softJointNat ρ g)=informationDeficit (noiseOperator ρ g) := by
  unfold mutualInformationNat
  rw [finite_kl_eq_entropy_sums _ (softJointNat_nonneg hρ g hg)]
  have hj : (∑ b, ∑ y, xlogx (softJointNat ρ g b y))=
      (2:ℝ)^n*xlogx (((2:ℝ)^n)⁻¹)-entropyAverage (noiseOperator ρ g) := by
    rw [Finset.sum_comm]
    simp_rw [softJointNat_xlogx_bool]
    simp [Finset.sum_sub_distrib,entropyAverage,cubeAverage,Finset.sum_div]
  rw [hj]
  simp_rw [softJointNat_left,softJointNat_right]
  rw [sum_xlogx_signProbability]
  simp only [Finset.sum_const,Finset.card_univ,card_cube,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  unfold informationDeficit
  rw [cubeAverage_noiseOperator]
  simp only [one_div]
  ring

end LeanBlast.CourtadeKumar
end
end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter
open scoped BigOperators Topology


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.soft_information_identity := @_root_.OAI.LeanBlast.CourtadeKumar.soft_information_identity
