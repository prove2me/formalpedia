-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.all_soft_sharp_production
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:13:34.262132+00:00
-- url     : https://prove2.me/submissions/6096c062-3e8d-427e-a5c4-02e3e84dd757

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/SoftChannel/Production.lean:L99-L129
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.all_soft_sharp_production. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_curvatureNumerator_upper
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_high_information_reserve
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_low_information_joining
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_psi_symmetric_pair_mono

-- ---- from OAI.Combinatorics.GotsmanLinial.Statement ----
namespace OAI

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

theorem flip_involutive {n : ℕ} (i : Fin n) : Function.Involutive (flip i) :=
  flip_flip i

theorem flip_bijective {n : ℕ} (i : Fin n) : Function.Bijective (flip i) :=
  (flip_involutive i).bijective

end LeanBlast.GotsmanLinial

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.EntropyScalars ----
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem ell_pos : 0 < ell := Real.log_pos (by norm_num)

theorem psi_nonneg (v : ℝ) : 0 ≤ psi v := by
  have h := Real.binEntropy_le_log_two (p := (1 + v) / 2)
  rw [← entropy_eq_binEntropy] at h
  unfold entropy ell at *
  linarith

theorem entropy_le_ell (v : ℝ) : entropy v ≤ ell := by
  exact sub_le_self _ (psi_nonneg v)

theorem entropy_nonneg {v : ℝ} (hv : v ∈ Icc (-1) 1) : 0 ≤ entropy v := by
  rw [entropy_eq_binEntropy]
  exact Real.binEntropy_nonneg (by linarith [hv.1]) (by linarith [hv.2])

theorem entropy_pos {v : ℝ} (hv : v ∈ Ioo (-1) 1) : 0 < entropy v := by
  rw [entropy_eq_binEntropy]
  exact Real.binEntropy_pos (by linarith [hv.1]) (by linarith [hv.2])

theorem artanh_eq_log_sub {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    Real.artanh v = (Real.log (1 + v) - Real.log (1 - v)) / 2 := by
  rw [Real.artanh_eq_half_log ⟨hv.1.le, hv.2.le⟩,
    Real.log_div (by linarith [hv.1]) (by linarith [hv.2])]
  ring

theorem hasDerivAt_psi {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    HasDerivAt psi (Real.artanh v) v := by
  have hp : 1 + v ≠ 0 := by linarith [hv.1]
  have hm : 1 - v ≠ 0 := by linarith [hv.2]
  have h1 := ((Real.hasDerivAt_mul_log hp).comp v
    ((hasDerivAt_id v).const_add 1)).div_const 2
  have h2 := ((Real.hasDerivAt_mul_log hm).comp v
    ((hasDerivAt_id v).const_sub 1)).div_const 2
  convert! h1.add h2 using 1
  · ext u
    dsimp [psi]
    ring
  · rw [artanh_eq_log_sub hv]
    ring

theorem hasDerivAt_entropy {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    HasDerivAt entropy (-Real.artanh v) v := by
  exact (hasDerivAt_psi hv).const_sub ell

theorem hasDerivAt_artanh {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    HasDerivAt Real.artanh (1 / (1 - v ^ 2)) v := by
  have hp : 1 + v ≠ 0 := by linarith [hv.1]
  have hm : 1 - v ≠ 0 := by linarith [hv.2]
  have hq : 1 - v ^ 2 ≠ 0 := by
    have hp' : 0 < 1 + v := by linarith [hv.1]
    have hm' : 0 < 1 - v := by linarith [hv.2]
    nlinarith [mul_pos hp' hm']
  have h := ((((hasDerivAt_id v).const_add 1).log hp).sub
    (((hasDerivAt_id v).const_sub 1).log hm)).div_const 2
  have he : Real.artanh =ᶠ[𝓝 v]
      (fun u => (Real.log (1 + u) - Real.log (1 - u)) / 2) := by
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with u hu
    exact artanh_eq_log_sub hu
  apply (h.congr_of_eventuallyEq he).congr_deriv
  change (1 / (1 + v) - -1 / (1 - v)) / 2 = 1 / (1 - v ^ 2)
  field_simp [hp, hm, hq]
  ring

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.CurvatureCertificates ----
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

theorem bernsteinSum_pos (d : ℕ) (B : Fin (d + 1) → ℝ)
    (hB : ∀ i, 0 < B i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < bernsteinSum d B t := by
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  unfold bernsteinSum
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (hB i).le (Nat.cast_nonneg _)) (pow_nonneg ht0 _))
      (pow_nonneg h1t _)
  · by_cases hlt : t < 1
    · refine ⟨⟨0, Nat.zero_lt_succ d⟩, Finset.mem_univ _, ?_⟩
      simpa only [Fin.val_zero, Nat.choose_zero_right, Nat.cast_one, pow_zero,
        mul_one, Nat.sub_zero] using
        mul_pos (hB ⟨0, Nat.zero_lt_succ d⟩) (pow_pos (sub_pos.mpr hlt) d)
    · have ht : t = 1 := le_antisymm ht1 (le_of_not_gt hlt)
      refine ⟨⟨d, Nat.lt_succ_self d⟩, Finset.mem_univ _, ?_⟩
      simpa [ht] using hB ⟨d, Nat.lt_succ_self d⟩

private theorem curvatureBernstein_pos (i : Fin 19) : 0 < curvatureBernstein i := by
  fin_cases i <;> norm_num [curvatureBernstein]

theorem curvaturePolynomial_bernstein (t : ℝ) :
    curvaturePolynomial ((2 / 3) * t) = bernsteinSum 18 curvatureBernstein t := by
  simp only [bernsteinSum, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
  norm_num [curvatureBernstein, Matrix.cons_val_two, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial]
  unfold curvaturePolynomial curvatureT curvatureP curvatureN
  ring

theorem curvatureCertificate_pos {z : ℝ} (hz0 : 0 ≤ z) (hz2 : z ≤ 2 / 3) :
    0 < curvaturePolynomial z := by
  have ht0 : 0 ≤ (3 / 2 : ℝ) * z := by positivity
  have ht1 : (3 / 2 : ℝ) * z ≤ 1 := by linarith
  have h := bernsteinSum_pos 18 curvatureBernstein curvatureBernstein_pos ht0 ht1
  rw [← curvaturePolynomial_bernstein] at h
  have he : (2 / 3 : ℝ) * ((3 / 2) * z) = z := by ring
  simpa only [he] using h

private theorem lambdaBernsteinLow_pos (i : Fin 9) : 0 < lambdaBernsteinLow i := by
  fin_cases i <;> norm_num [lambdaBernsteinLow]

private theorem lambdaBernsteinHigh_pos (i : Fin 9) : 0 < lambdaBernsteinHigh i := by
  fin_cases i <;> norm_num [lambdaBernsteinHigh]

theorem lambdaPolynomial_bernstein_low (t : ℝ) :
    lambdaPolynomial ((3 / 4) * t) = bernsteinSum 8 lambdaBernsteinLow t := by
  unfold bernsteinSum
  simp_rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [lambdaPolynomial, lambdaBernsteinLow, Fin.sum_univ_succ,
    Nat.descFactorial, Nat.factorial]
  ring

theorem lambdaPolynomial_bernstein_high (t : ℝ) :
    lambdaPolynomial (3 / 4 + (1 / 4) * t) = bernsteinSum 8 lambdaBernsteinHigh t := by
  unfold bernsteinSum
  simp_rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [lambdaPolynomial, lambdaBernsteinHigh, Fin.sum_univ_succ,
    Nat.descFactorial, Nat.factorial]
  ring

theorem lambdaCertificate_pos {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 < lambdaPolynomial b := by
  by_cases hb : b ≤ 3 / 4
  · have ht0 : 0 ≤ (4 / 3 : ℝ) * b := by positivity
    have ht1 : (4 / 3 : ℝ) * b ≤ 1 := by linarith
    have h := bernsteinSum_pos 8 lambdaBernsteinLow lambdaBernsteinLow_pos ht0 ht1
    rw [← lambdaPolynomial_bernstein_low] at h
    have he : (3 / 4 : ℝ) * ((4 / 3) * b) = b := by ring
    simpa only [he] using h
  · have ht0 : 0 ≤ 4 * b - 3 := by linarith
    have ht1 : 4 * b - 3 ≤ 1 := by linarith
    have h := bernsteinSum_pos 8 lambdaBernsteinHigh lambdaBernsteinHigh_pos ht0 ht1
    rw [← lambdaPolynomial_bernstein_high] at h
    have he : (3 / 4 : ℝ) + (1 / 4) * (4 * b - 3) = b := by ring
    simpa only [he] using h

theorem two_lt_exp_347_div_500 : (2 : ℝ) < Real.exp (347 / 500) := by
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 347 / 500) 5)
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem ell_lt_347_div_500 : ell < 347 / 500 :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).mpr two_lt_exp_347_div_500

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.InverseScalars ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem L_eq_zero_of_ell_le {x : ℝ} (hx : ell ≤ x) : L x = 0 := by
  simp [L, not_lt.mpr hx]

theorem L_eq_rGap {x : ℝ} (hx : x ∈ Set.Ioo 0 ell) :
    L x = rGap (ell - x) := by simp [L, hx.1, hx.2]

theorem psi_psiInv {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) : psi (psiInv s) = s :=
  psi_psiInv_Icc ⟨hs, hsell.le⟩

theorem psiInv_mem_Ico {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) :
    psiInv s ∈ Ico 0 1 := by
  have hu := psiInv_mem_Icc ⟨hs, hsell.le⟩
  refine ⟨hu.1, ?_⟩
  by_contra h
  have he : psiInv s = 1 := le_antisymm hu.2 (le_of_not_gt h)
  have hv := psi_psiInv hs hsell
  rw [he, psi_one] at hv
  linarith

theorem psiInv_mem_Ioo {s : ℝ} (hs : s ∈ Ioo 0 ell) : psiInv s ∈ Ioo 0 1 := by
  have hu := psiInv_mem_Ico hs.1.le hs.2
  refine ⟨?_, hu.2⟩
  by_contra h
  have he : psiInv s = 0 := le_antisymm (le_of_not_gt h) hu.1
  have hv := psi_psiInv hs.1.le hs.2
  rw [he, psi_zero] at hv
  linarith [hs.1]

theorem continuousOn_psiInv : ContinuousOn psiInv (Icc 0 ell) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp psiOrderIso.symm.continuous

theorem continuousAt_psiInv {s : ℝ} (hs : s ∈ Ioo 0 ell) : ContinuousAt psiInv s :=
  (continuousOn_psiInv s ⟨hs.1.le, hs.2.le⟩).continuousAt (Icc_mem_nhds hs.1 hs.2)

theorem hasDerivAt_psiInv {s : ℝ} (hs : s ∈ Ioo 0 ell) :
    HasDerivAt psiInv (Real.artanh (psiInv s))⁻¹ s := by
  have hu := psiInv_mem_Ioo hs
  apply HasDerivAt.of_local_left_inverse (continuousAt_psiInv hs)
    (hasDerivAt_psi ⟨by linarith [hu.1], hu.2⟩) (Real.artanh_pos hu).ne'
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
  exact psi_psiInv ht.1.le ht.2

theorem continuousOn_r : ContinuousOn r (Ico 0 ell) := by
  have hi : ContinuousOn psiInv (Ico 0 ell) :=
    continuousOn_psiInv.mono (fun _ h => ⟨h.1, h.2.le⟩)
  intro s hs
  have hu := psiInv_mem_Ico hs.1 hs.2
  exact (hi s hs).mul
    ((hasDerivAt_artanh ⟨by linarith [hu.1], hu.2⟩).continuousAt.comp_continuousWithinAt
      (hi s hs))

theorem hasDerivAt_r {s : ℝ} (hs : s ∈ Ioo 0 ell) : HasDerivAt r (rDeriv s) s := by
  have hu := psiInv_mem_Ioo hs
  have hi := hasDerivAt_psiInv hs
  have ht := (hasDerivAt_artanh ⟨by linarith [hu.1], hu.2⟩).comp s hi
  have hn : Real.artanh (psiInv s) ≠ 0 := (Real.artanh_pos hu).ne'
  have hq : 1 - (psiInv s) ^ 2 ≠ 0 := by nlinarith [hu.1, hu.2]
  convert! hi.mul ht using 1
  unfold rDeriv
  rw [ite_eq_right (not_le.mpr hs.1)]
  simp only [Function.comp_apply]
  field_simp

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.EndpointLimits ----
namespace OAI

noncomputable section

open Filter Set
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem tendsto_artanh_div_id_zero_right :
    Tendsto (fun u : ℝ => Real.artanh u / u) (𝓝[>] 0) (𝓝 1) := by
  have hd : HasDerivAt Real.artanh 1 0 := by
    simpa using hasDerivAt_artanh (show (0 : ℝ) ∈ Ioo (-1) 1 by constructor <;> norm_num)
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right

theorem tendsto_id_div_artanh_zero_right :
    Tendsto (fun u : ℝ => u / Real.artanh u) (𝓝[>] 0) (𝓝 1) := by
  simpa only [inv_div, inv_one] using
    tendsto_artanh_div_id_zero_right.inv₀ (show (1 : ℝ) ≠ 0 by norm_num)

theorem tendsto_entropy_inverse_derivative_zero_right :
    Tendsto (fun u : ℝ => 1 + u / ((1 - u ^ 2) * Real.artanh u))
      (𝓝[>] 0) (𝓝 2) := by
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hden : Tendsto (fun u : ℝ => 1 - u ^ 2) (𝓝[>] 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hu.pow 2)
  have hquot := tendsto_id_div_artanh_zero_right.div hden (show (1 : ℝ) ≠ 0 by norm_num)
  have hadd :
    Tendsto (fun u : ℝ => 1 + (u / Real.artanh u) / (1 - u ^ 2))
      (𝓝[>] 0) (𝓝 ((1 : ℝ) + 1 / 1)) := tendsto_const_nhds.add hquot
  norm_num [div_div, mul_comm] at hadd ⊢
  exact hadd

theorem tendsto_artanh_mul_id_div_psi_zero_right :
    Tendsto (fun u : ℝ => (u * Real.artanh u) / psi u) (𝓝[>] 0) (𝓝 2) := by
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hda : HasDerivAt Real.artanh 1 0 := by
    simpa using hasDerivAt_artanh (show (0 : ℝ) ∈ Ioo (-1) 1 by constructor <;> norm_num)
  have ha : Tendsto Real.artanh (𝓝[>] 0) (𝓝 0) := by
    simpa using hda.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hp : Tendsto psi (𝓝[>] 0) (𝓝 0) := by
    simpa [psi] using
      (hasDerivAt_psi (show (0 : ℝ) ∈ Ioo (-1) 1 by constructor <;> norm_num)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
  have hquot : Tendsto
      (fun u : ℝ => (Real.artanh u + u / (1 - u ^ 2)) / Real.artanh u)
      (𝓝[>] 0) (𝓝 2) := by
    apply tendsto_entropy_inverse_derivative_zero_right.congr'
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
    have hne : Real.artanh u ≠ 0 := ne_of_gt (Real.artanh_pos hu)
    rw [add_div, div_self hne, div_div]
  apply HasDerivAt.lhopital_zero_right_on_Ioo
    (f' := fun u => Real.artanh u + u / (1 - u ^ 2))
    (g' := Real.artanh) (show (0 : ℝ) < 1 by norm_num)
  · intro u hu
    convert! (hasDerivAt_id u).mul
      (hasDerivAt_artanh (show u ∈ Ioo (-1) 1 from ⟨by linarith [hu.1], hu.2⟩)) using 1
    simp [id_eq, div_eq_mul_inv]
  · intro u hu
    exact hasDerivAt_psi ⟨by linarith [hu.1], hu.2⟩
  · intro u hu
    exact ne_of_gt (Real.artanh_pos hu)
  · simpa using hu.mul ha
  · exact hp
  · exact hquot

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.EntropySeries ----
namespace OAI

noncomputable section

open Set Filter Finset
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

theorem psiCoeff_pos (k : ℕ) : 0 < psiCoeff k := by unfold psiCoeff; positivity

theorem psiCoeff_nonneg (k : ℕ) : 0 ≤ psiCoeff k := (psiCoeff_pos k).le

theorem hasSum_artanh {v : ℝ} (hv : |v| < 1) :
    HasSum (fun k : ℕ => v ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) (Real.artanh v) := by
  have h := (Real.hasSum_log_sub_log_of_abs_lt_one hv).mul_left (1 / 2)
  convert! h using 1
  · ext k
    ring
  · rw [artanh_eq_log_sub (abs_lt.mp hv)]
    ring

theorem hasSum_mul_artanh {v : ℝ} (hv : |v| < 1) :
    HasSum (fun k : ℕ => (2 * ((k : ℝ) + 1)) * psiCoeff k * v ^ (2 * (k + 1)))
      (v * Real.artanh v) := by
  have h := (hasSum_artanh hv).mul_left v
  convert! h using 1
  ext k
  have h1 : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
  have h2 : 2 * (k : ℝ) + 2 ≠ 0 := by positivity
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, pow_succ]
  unfold psiCoeff
  field_simp

theorem psi_eq_mul_artanh_add_log {v : ℝ} (hv : |v| < 1) :
    psi v = v * Real.artanh v + 1 / 2 * Real.log (1 - v ^ 2) := by
  have hp : 1 + v ≠ 0 := by linarith [(abs_lt.mp hv).1]
  have hm : 1 - v ≠ 0 := by linarith [(abs_lt.mp hv).2]
  have hl : Real.log (1 - v ^ 2) = Real.log (1 + v) + Real.log (1 - v) := by
    rw [← Real.log_mul hp hm]
    congr 1
    ring
  rw [artanh_eq_log_sub (abs_lt.mp hv), hl]
  unfold psi
  ring

theorem hasSum_psi {v : ℝ} (hv : |v| < 1) :
    HasSum (fun k : ℕ => psiCoeff k * v ^ (2 * (k + 1))) (psi v) := by
  have hv2 : |v ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg v)]
    have h1 : 0 < 1 + v := by linarith [(abs_lt.mp hv).1]
    have h2 : 0 < 1 - v := by linarith [(abs_lt.mp hv).2]
    nlinarith [mul_pos h1 h2]
  have h := ((hasSum_artanh hv).mul_left v).add
    ((Real.hasSum_pow_div_log_of_abs_lt_one hv2).mul_left (-(1 / 2)))
  convert! h using 1
  · ext k
    have h1 : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (k : ℝ) + 1 ≠ 0 := by positivity
    have h3 : 2 * (k : ℝ) + 2 ≠ 0 := by positivity
    rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by omega, pow_succ]
    unfold psiCoeff
    field_simp
    ring
  · rw [psi_eq_mul_artanh_add_log hv]
    ring

theorem sum_range_artanh_le {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (m : ℕ) :
    (∑ k ∈ Finset.range m, v ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) ≤ Real.artanh v := by
  have h := hasSum_artanh (show |v| < 1 by rwa [abs_of_nonneg hv0])
  rw [← h.tsum_eq]
  exact h.summable.sum_le_tsum (Finset.range m) (fun k hk => by positivity)

theorem sum_range_psi_le {v : ℝ} (hv : |v| < 1) (m : ℕ) :
    (∑ k ∈ Finset.range m, psiCoeff k * v ^ (2 * (k + 1))) ≤ psi v := by
  have h := hasSum_psi hv
  rw [← h.tsum_eq]
  exact h.summable.sum_le_tsum (Finset.range m) (fun k hk =>
    mul_nonneg (psiCoeff_nonneg k) (Even.pow_nonneg (even_two_mul (k + 1)) v))

theorem summable_psiCoeff : Summable psiCoeff := by
  have h : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  apply Summable.of_nonneg_of_le psiCoeff_nonneg ?_ h
  intro k
  unfold psiCoeff
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [sq_nonneg (k : ℝ), Nat.cast_nonneg (α := ℝ) k]

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.ArtanhBounds ----
namespace OAI

namespace LeanBlast.CourtadeKumar

theorem self_le_artanh {u : ℝ} (hu : u ∈ Set.Ico 0 1) : u ≤ Real.artanh u := by
  simpa using sum_range_artanh_le hu.1 hu.2 1

theorem artanh_le_div_one_sub_sq {u : ℝ} (hu : u ∈ Set.Ico 0 1) :
    Real.artanh u ≤ u / (1 - u ^ 2) := by
  have huabs : |u| < 1 := by simpa only [abs_of_nonneg hu.1] using hu.2
  have hu2 : u ^ 2 < 1 := by
    have hmul := mul_pos (sub_pos.mpr hu.2) (show 0 < 1 + u by linarith [hu.1])
    nlinarith
  have hgeom := (hasSum_geometric_of_lt_one (sq_nonneg u) hu2).mul_left u
  have hseries := hasSum_artanh huabs
  have hle : Real.artanh u ≤ u * (1 - u ^ 2)⁻¹ := by
    apply hasSum_le _ hseries hgeom
    intro k
    have hpow : u ^ (2 * k + 1) = u * (u ^ 2) ^ k := by
      rw [pow_add, pow_one, pow_mul]
      ring
    rw [hpow]
    exact div_le_self (mul_nonneg hu.1 (pow_nonneg (sq_nonneg u) k))
      (by linarith [Nat.cast_nonneg (α := ℝ) k])
  simpa only [div_eq_mul_inv] using hle

theorem one_sub_sq_mul_artanh_le_self {u : ℝ} (hu : u ∈ Set.Ico 0 1) :
    (1 - u ^ 2) * Real.artanh u ≤ u := by
  have hden : 0 < 1 - u ^ 2 := by
    have hmul := mul_pos (sub_pos.mpr hu.2) (show 0 < 1 + u by linarith [hu.1])
    nlinarith
  have hle := (le_div_iff₀ hden).mp (artanh_le_div_one_sub_sq hu)
  simpa only [mul_comm] using hle

end LeanBlast.CourtadeKumar

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.InverseRegularity ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem hasDerivAt_rDerivativeFormula {u : ℝ} (hu : u ∈ Ioo 0 1) :
    HasDerivAt (fun v => 1 + v / ((1 - v ^ 2) * Real.artanh v))
      (((1 + u ^ 2) * Real.artanh u - u) /
        ((1 - u ^ 2) ^ 2 * (Real.artanh u) ^ 2)) u := by
  have ht : Real.artanh u ≠ 0 := (Real.artanh_pos hu).ne'
  have hq : 1 - u ^ 2 ≠ 0 := by nlinarith [hu.1, hu.2]
  have hd := (((hasDerivAt_id u).pow 2).const_sub 1).mul
    (hasDerivAt_artanh ⟨by linarith [hu.1], hu.2⟩)
  have h := ((hasDerivAt_id u).div hd (mul_ne_zero hq ht)).const_add 1
  convert! h using 1
  dsimp
  field_simp [hq, ht]
  ring

theorem hasDerivAt_rDeriv {s : ℝ} (hs : s ∈ Ioo 0 ell) :
    HasDerivAt rDeriv (rSecondDeriv s) s := by
  have hu := psiInv_mem_Ioo hs
  have h := (hasDerivAt_rDerivativeFormula hu).comp s (hasDerivAt_psiInv hs)
  have he : rDeriv =ᶠ[𝓝 s]
      (fun z => 1 + psiInv z / ((1 - (psiInv z) ^ 2) * Real.artanh (psiInv z))) := by
    filter_upwards [Ioi_mem_nhds hs.1] with z hz
    simp only [rDeriv, ite_eq_right (not_le.mpr (show 0 < z from hz))]
  apply (h.congr_of_eventuallyEq he).congr_deriv
  have ht : Real.artanh (psiInv s) ≠ 0 := (Real.artanh_pos hu).ne'
  have hq : 1 - (psiInv s) ^ 2 ≠ 0 := by nlinarith [hu.1, hu.2]
  simp only [rSecondDeriv, ite_eq_right (not_le.mpr hs.1)]
  field_simp [hq, ht]

theorem continuousOn_rGap : ContinuousOn rGap (Ico 0 ell) :=
  continuousOn_r.sub (continuous_const.mul continuous_id).continuousOn

theorem hasDerivAt_rGap {s : ℝ} (hs : s ∈ Ioo 0 ell) :
    HasDerivAt rGap (rDeriv s - 2) s := by
  convert! (hasDerivAt_r hs).sub ((hasDerivAt_id s).const_mul 2) using 1
  simp

theorem L_ell_sub {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) :
    L (ell - s) = r s - 2 * s := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [L]
  · have hx : 0 < ell - s ∧ ell - s < ell := by constructor <;> linarith
    simp only [L, ite_eq_left hx, rGap, sub_sub_cancel]

theorem hasDerivAt_L_of_lt {x : ℝ} (hx : x ∈ Ioo 0 ell) :
    HasDerivAt L (LDeriv x) x := by
  have hs : ell - x ∈ Ioo 0 ell := by constructor <;> linarith [hx.1, hx.2]
  have h := (hasDerivAt_rGap hs).comp x ((hasDerivAt_id x).const_sub ell)
  have he : L =ᶠ[𝓝 x] (fun z => rGap (ell - z)) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with z hz
    exact L_eq_rGap hz
  apply (h.congr_of_eventuallyEq he).congr_deriv
  rw [LDeriv, ite_eq_left (show 0 < x ∧ x < ell from hx)]
  ring

theorem hasDerivAt_LDeriv_of_lt {x : ℝ} (hx : x ∈ Ioo 0 ell) :
    HasDerivAt LDeriv (rSecondDeriv (ell - x)) x := by
  have hs : ell - x ∈ Ioo 0 ell := by constructor <;> linarith [hx.1, hx.2]
  have h := ((hasDerivAt_rDeriv hs).comp x ((hasDerivAt_id x).const_sub ell)).const_sub 2
  have he : LDeriv =ᶠ[𝓝 x] (fun z => 2 - rDeriv (ell - z)) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with z hz
    exact ite_eq_left hz
  apply (h.congr_of_eventuallyEq he).congr_deriv
  ring

theorem rDeriv_ge_two {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) : 2 ≤ rDeriv s := by
  rcases hs.eq_or_lt with rfl | hs
  · simp
  · have hu := psiInv_mem_Ioo ⟨hs, hsell⟩
    have hq : 0 < 1 - (psiInv s) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hu.2) (show 0 < 1 + psiInv s by linarith [hu.1])]
    have ht := Real.artanh_pos hu
    have hb := one_sub_sq_mul_artanh_le_self ⟨hu.1.le, hu.2⟩
    have hd : 1 ≤ psiInv s / ((1 - (psiInv s) ^ 2) * Real.artanh (psiInv s)) :=
      (le_div_iff₀ (mul_pos hq ht)).mpr (by simpa using hb)
    simp only [rDeriv, ite_eq_right (not_le.mpr hs)]
    linarith

theorem rSecondDeriv_pos {s : ℝ} (hs : s ∈ Ioo 0 ell) : 0 < rSecondDeriv s := by
  have hu := psiInv_mem_Ioo hs
  have hq : 0 < 1 - (psiInv s) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hu.2) (show 0 < 1 + psiInv s by linarith [hu.1])]
  have ht := Real.artanh_pos hu
  have hb := self_le_artanh ⟨hu.1.le, hu.2⟩
  have hn : 0 < (1 + (psiInv s) ^ 2) * Real.artanh (psiInv s) - psiInv s := by
    nlinarith [mul_pos (sq_pos_of_pos hu.1) ht]
  simp only [rSecondDeriv, ite_eq_right (not_le.mpr hs.1)]
  exact div_pos hn (mul_pos (sq_pos_of_pos hq) (pow_pos ht 3))

theorem convexOn_r : ConvexOn ℝ (Ico 0 ell) r := by
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (f' := rDeriv) (f'' := rSecondDeriv) (convex_Ico 0 ell) continuousOn_r ?_ ?_ ?_
  · intro s hs
    exact (hasDerivAt_r (by simpa using hs)).hasDerivWithinAt
  · intro s hs
    exact (hasDerivAt_rDeriv (by simpa using hs)).hasDerivWithinAt
  · intro s hs
    exact (rSecondDeriv_pos (by simpa using hs)).le

theorem convexOn_rGap : ConvexOn ℝ (Ico 0 ell) rGap := by
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (f' := fun s => rDeriv s - 2) (f'' := rSecondDeriv)
    (convex_Ico 0 ell) continuousOn_rGap ?_ ?_ ?_
  · intro s hs
    exact (hasDerivAt_rGap (by simpa using hs)).hasDerivWithinAt
  · intro s hs
    simpa only [sub_zero] using
      ((hasDerivAt_rDeriv (by simpa using hs)).sub_const 2).hasDerivWithinAt
  · intro s hs
    exact (rSecondDeriv_pos (by simpa using hs)).le

theorem monotoneOn_rGap : MonotoneOn rGap (Ico 0 ell) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun s => rDeriv s - 2)
    (convex_Ico 0 ell) continuousOn_rGap ?_ ?_
  · intro s hs
    exact (hasDerivAt_rGap (by simpa using hs)).hasDerivWithinAt
  · intro s hs
    have hs' : s ∈ Ioo 0 ell := by simpa using hs
    exact sub_nonneg.mpr (rDeriv_ge_two hs'.1.le hs'.2)

theorem rGap_nonneg {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) : 0 ≤ rGap s := by
  simpa only [rGap_zero] using monotoneOn_rGap ⟨le_rfl, ell_pos⟩ ⟨hs, hsell⟩ hs

theorem tendsto_psiInv_zero_right : Tendsto psiInv (𝓝[>] 0) (𝓝[>] 0) := by
  have hc : Tendsto psiInv (𝓝[≥] 0) (𝓝 0) := by
    simpa only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE ell_pos, psiInv_zero] using
      continuousOn_psiInv 0 ⟨le_rfl, ell_pos.le⟩
  refine tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self), ?_⟩
  filter_upwards [Ioo_mem_nhdsGT ell_pos] with s hs
  exact (psiInv_mem_Ioo hs).1

theorem tendsto_rDeriv_zero_right : Tendsto rDeriv (𝓝[>] 0) (𝓝 2) := by
  apply (tendsto_entropy_inverse_derivative_zero_right.comp tendsto_psiInv_zero_right).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Function.comp_apply, rDeriv, ite_eq_right (not_le.mpr (show 0 < s from hs))]

theorem continuousOn_rDeriv : ContinuousOn rDeriv (Ico 0 ell) := by
  intro s hs
  rcases hs.1.eq_or_lt with rfl | hs0
  · have hright : ContinuousWithinAt rDeriv (Ioi 0) 0 := by
      simpa only [ContinuousWithinAt, rDeriv_zero] using tendsto_rDeriv_zero_right
    apply hright.insert.mono
    intro s hs
    rcases hs.1.eq_or_lt with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  · exact (hasDerivAt_rDeriv ⟨hs0, hs.2⟩).continuousAt.continuousWithinAt

theorem tendsto_r_div_zero_right :
    Tendsto (fun s : ℝ => r s / s) (𝓝[>] 0) (𝓝 2) := by
  apply (tendsto_artanh_mul_id_div_psi_zero_right.comp tendsto_psiInv_zero_right).congr'
  filter_upwards [Ioo_mem_nhdsGT ell_pos] with s hs
  simp only [Function.comp_apply, r, psi_psiInv hs.1.le hs.2]

theorem hasDerivWithinAt_r_zero : HasDerivWithinAt r 2 (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left]
  have he : slope r 0 = fun s : ℝ => r s / s := by
    ext s
    simp only [slope_def_field, r_zero, sub_zero]
  rw [he]
  exact tendsto_r_div_zero_right

theorem hasDerivWithinAt_rGap_zero : HasDerivWithinAt rGap 0 (Ici 0) 0 := by
  convert! hasDerivWithinAt_r_zero.sub
    (((hasDerivAt_id (0 : ℝ)).const_mul 2).hasDerivWithinAt) using 1
  simp

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.EntropyBounds ----
namespace OAI

noncomputable section

open Set Filter Finset
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

theorem norm_psiSeries_term_le {v : ℝ} (hv : |v| ≤ 1) (k : ℕ) :
    ‖psiCoeff k * v ^ (2 * (k + 1))‖ ≤ psiCoeff k := by
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (psiCoeff_nonneg k)]
  exact mul_le_of_le_one_right (psiCoeff_nonneg k)
    (pow_le_one₀ (abs_nonneg v) hv)

theorem summable_psi_closed {v : ℝ} (hv : |v| ≤ 1) :
    Summable (fun k : ℕ => psiCoeff k * v ^ (2 * (k + 1))) :=
  Summable.of_norm_bounded summable_psiCoeff (norm_psiSeries_term_le hv)

theorem continuousOn_psiSeries : ContinuousOn psiSeries (Icc (-1) 1) := by
  apply continuousOn_tsum
  · intro k
    fun_prop
  · exact summable_psiCoeff
  · intro k v hv
    exact norm_psiSeries_term_le (abs_le.mpr hv) k

theorem psiSeries_eq_psi {v : ℝ} (hv : |v| ≤ 1) : psiSeries v = psi v := by
  have h : EqOn psiSeries psi (Ioo (-1) 1) := by
    intro x hx
    exact (hasSum_psi (abs_lt.mpr hx)).tsum_eq
  have h' := h.of_subset_closure continuousOn_psiSeries continuous_psi.continuousOn
    Ioo_subset_Icc_self (show Icc (-1 : ℝ) 1 ⊆ closure (Ioo (-1) 1) by
      rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)])
  exact h' (abs_le.mp hv)

theorem hasSum_psi_closed {v : ℝ} (hv : |v| ≤ 1) :
    HasSum (fun k : ℕ => psiCoeff k * v ^ (2 * (k + 1))) (psi v) := by
  rw [← psiSeries_eq_psi hv]
  exact (summable_psi_closed hv).hasSum

theorem hasSum_psiCoeff : HasSum psiCoeff ell := by
  simpa using hasSum_psi_closed (v := 1) (by norm_num)

theorem psi_le_ell_mul_sq {v : ℝ} (hv : |v| ≤ 1) : psi v ≤ ell * v ^ 2 := by
  have hsq : v ^ 2 ≤ 1 := by
    have h := abs_le.mp hv
    nlinarith [mul_nonneg (sub_nonneg.mpr h.2) (show 0 ≤ 1 + v by linarith [h.1])]
  apply hasSum_le _ (hasSum_psi_closed hv) (hasSum_psiCoeff.mul_right (v ^ 2))
  intro k
  apply mul_le_mul_of_nonneg_left _ (psiCoeff_nonneg k)
  rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add, pow_mul]
  exact mul_le_of_le_one_left (sq_nonneg v) (pow_le_one₀ (sq_nonneg v) hsq)

theorem ell_mul_one_sub_sq_le_entropy {v : ℝ} (hv : |v| ≤ 1) :
    ell * (1 - v ^ 2) ≤ entropy v := by
  have h := psi_le_ell_mul_sq hv
  unfold entropy
  nlinarith

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.MediumCurvature ----
namespace OAI

noncomputable section

open Finset Set
open scoped BigOperators

namespace LeanBlast.CourtadeKumar

theorem curvatureT_lower {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    u * curvatureT (u ^ 2) ≤ Real.artanh u := by
  have h := sum_range_artanh_le hu0.le hu1 6
  convert h using 1
  norm_num [curvatureT, Finset.sum_range_succ]
  ring

theorem curvatureP_upper {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    entropy u ≤ curvatureP (u ^ 2) := by
  have h := sum_range_psi_le (show |u| < 1 by rwa [abs_of_pos hu0]) 5
  have hs : (∑ k ∈ Finset.range 5, psiCoeff k * u ^ (2 * (k + 1))) =
      u ^ 2 / 2 + (u ^ 2) ^ 2 / 12 + (u ^ 2) ^ 3 / 30 +
        (u ^ 2) ^ 4 / 56 + (u ^ 2) ^ 5 / 90 := by
    norm_num [psiCoeff, Finset.sum_range_succ]
    ring
  rw [hs] at h
  unfold entropy curvatureP
  linarith [ell_lt_347_div_500]

theorem medium_curvature_bound {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hz : u ^ 2 ≤ (2 / 3 : ℝ)) :
    entropy u ^ 2 * (((1 + u ^ 2) * Real.artanh u - u) /
      ((1 - u ^ 2) ^ 2 * (Real.artanh u) ^ 3)) ≤ 2 / 3 := by
  have hz0 : 0 ≤ u ^ 2 := sq_nonneg u
  have hz1 : 0 < 1 - u ^ 2 := by linarith
  have ht : 0 < Real.artanh u := Real.artanh_pos ⟨hu0, hu1⟩
  have hH : 0 < entropy u := entropy_pos ⟨by linarith, hu1⟩
  have hHP := curvatureP_upper hu0 hu1
  have hP : 0 < curvatureP (u ^ 2) := hH.trans_le hHP
  have hT : 0 < curvatureT (u ^ 2) := by unfold curvatureT; positivity
  have hTl := curvatureT_lower hu0 hu1
  have hN := curvatureNumerator_upper hu0 hu1
  have hnum : (1 + u ^ 2) * Real.artanh u - u ≤
      (curvatureN (u ^ 2) / (1 - u ^ 2)) * u ^ 3 :=
    (div_le_iff₀ (pow_pos hu0 3)).mp hN
  have hu_atanh : u ≤ Real.artanh u := by
    simpa using sum_range_artanh_le hu0.le hu1 1
  have hnum0 : 0 ≤ (1 + u ^ 2) * Real.artanh u - u := by
    nlinarith [mul_nonneg hz0 ht.le]
  have hsq : entropy u ^ 2 ≤ curvatureP (u ^ 2) ^ 2 :=
    pow_le_pow_left₀ hH.le hHP 2
  have hprod := mul_le_mul hsq hnum hnum0 (sq_nonneg (curvatureP (u ^ 2)))
  have hc := curvatureCertificate_pos hz0 hz
  unfold curvaturePolynomial at hc
  have hc' : 3 * curvatureP (u ^ 2) ^ 2 * curvatureN (u ^ 2) <
      2 * (1 - u ^ 2) ^ 3 * curvatureT (u ^ 2) ^ 3 := by linarith
  have hcert : curvatureP (u ^ 2) ^ 2 *
      ((curvatureN (u ^ 2) / (1 - u ^ 2)) * u ^ 3) <
      (2 / 3 : ℝ) * (1 - u ^ 2) ^ 2 * (u * curvatureT (u ^ 2)) ^ 3 := by
    rw [show curvatureP (u ^ 2) ^ 2 *
        ((curvatureN (u ^ 2) / (1 - u ^ 2)) * u ^ 3) =
        (curvatureP (u ^ 2) ^ 2 * curvatureN (u ^ 2) * u ^ 3) / (1 - u ^ 2) by ring]
    apply (div_lt_iff₀ hz1).mpr
    have hc'' := mul_lt_mul_of_pos_right hc' (pow_pos hu0 3)
    nlinarith
  have hpow : (u * curvatureT (u ^ 2)) ^ 3 ≤ (Real.artanh u) ^ 3 :=
    pow_le_pow_left₀ (mul_nonneg hu0.le hT.le) hTl 3
  have hden := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ (2 / 3 : ℝ) * (1 - u ^ 2) ^ 2 by positivity)
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (mul_pos (pow_pos hz1 2) (pow_pos ht 3))).mpr
  calc
    entropy u ^ 2 * ((1 + u ^ 2) * Real.artanh u - u) ≤
        curvatureP (u ^ 2) ^ 2 *
          ((curvatureN (u ^ 2) / (1 - u ^ 2)) * u ^ 3) := hprod
    _ ≤ (2 / 3 : ℝ) * (1 - u ^ 2) ^ 2 * (u * curvatureT (u ^ 2)) ^ 3 := hcert.le
    _ ≤ (2 / 3 : ℝ) * ((1 - u ^ 2) ^ 2 * (Real.artanh u) ^ 3) := by
      simpa only [mul_assoc] using hden

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.LargeCurvature ----
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

theorem large_parameter_gt_81 {u : ℝ} (hu0 : 0 ≤ u) (hu2 : (2 / 3 : ℝ) ≤ u ^ 2) :
    (81 / 100 : ℝ) < u := by
  by_contra h
  have hsq := pow_le_pow_left₀ hu0 (le_of_not_gt h) 2
  norm_num at hsq
  linarith

theorem large_artanh_gt_eleven_tenths {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hu2 : (2 / 3 : ℝ) ≤ u ^ 2) : (11 / 10 : ℝ) < Real.artanh u := by
  have hu81 := (large_parameter_gt_81 hu0 hu2).le
  have hpoly : (∑ k ∈ Finset.range 5,
      (81 / 100 : ℝ) ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) ≤
      ∑ k ∈ Finset.range 5, u ^ (2 * k + 1) / (2 * (k : ℝ) + 1) := by
    apply Finset.sum_le_sum
    intro k _
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 81 / 100) hu81 _) (by positivity)
  have hnum : (11 / 10 : ℝ) < ∑ k ∈ Finset.range 5,
      (81 / 100 : ℝ) ^ (2 * k + 1) / (2 * (k : ℝ) + 1) := by
    norm_num [Finset.sum_range_succ]
  exact hnum.trans_le (hpoly.trans (sum_range_artanh_le hu0 hu1 5))

theorem entropy_eq_large_parameter_form {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    entropy u = (1 - u) * Real.artanh u + Real.log (1 + (1 - u) / (1 + u)) := by
  have hp : 0 < 1 + u := by linarith
  have heq : 1 + (1 - u) / (1 + u) = 2 / (1 + u) := by
    field_simp
    ring
  rw [heq, Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hp.ne',
    artanh_eq_log_sub ⟨by linarith, hu1⟩]
  unfold entropy psi ell
  ring

theorem large_parameter_polynomial_bound {y : ℝ} (hy0 : 0 ≤ y)
    (hy1 : y ≤ (5 / 11 : ℝ)) :
    (1 / 2 : ℝ) * (1 - y + (1 + y) / 81) * (1 + 10 * y / 9) ^ 2 ≤ 2 / 3 := by
  have hfirst : (1 - y) * (1 + 10 * y / 9) ^ 2 ≤ (13718 / 10935 : ℝ) := by
    have hc : (13718 / 10935 : ℝ) - (1 - y) * (1 + 10 * y / 9) ^ 2 =
        (y - 11 / 30) ^ 2 * ((100 / 81 : ℝ) * y + 460 / 243) := by ring
    have hp : 0 ≤ (y - 11 / 30) ^ 2 * ((100 / 81 : ℝ) * y + 460 / 243) :=
      mul_nonneg (sq_nonneg _) (by positivity)
    linarith
  have hsecond : (1 + y) * (1 + 10 * y / 9) ^ 2 / 81 ≤
      (355216 / 8732691 : ℝ) := by
    calc
      _ ≤ (1 + (5 / 11 : ℝ)) * (1 + 10 * (5 / 11 : ℝ) / 9) ^ 2 / 81 := by
        gcongr
      _ = _ := by norm_num
  nlinarith

theorem large_curvature_bound {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hu2 : (2 / 3 : ℝ) ≤ u ^ 2) :
    entropy u ^ 2 * (((1 + u ^ 2) * Real.artanh u - u) /
      ((1 - u ^ 2) ^ 2 * (Real.artanh u) ^ 3)) ≤ 2 / 3 := by
  let t : ℝ := Real.artanh u
  let e : ℝ := (1 - u) / (1 + u)
  let y : ℝ := 1 / (2 * t)
  let R : ℝ := 1 + (1 + e) * y
  let A : ℝ := 1 - y + (1 + y) * e ^ 2
  let Q : ℝ := ((1 + u ^ 2) * t - u) / ((1 - u ^ 2) ^ 2 * t ^ 3)
  have ht11 : (11 / 10 : ℝ) < t := large_artanh_gt_eleven_tenths hu0 hu1 hu2
  have ht : 0 < t := by linarith
  have hp : 0 < 1 + u := by linarith
  have hm : 0 < 1 - u := by linarith
  have hsq : 0 < 1 - u ^ 2 := by nlinarith [mul_pos hm hp]
  have he0 : 0 ≤ e := div_nonneg hm.le hp.le
  have he1 : e ≤ (1 / 9 : ℝ) := by
    dsimp only [e]
    apply (div_le_iff₀ hp).mpr
    linarith [large_parameter_gt_81 hu0 hu2]
  have hy0 : 0 ≤ y := by dsimp only [y]; positivity
  have hy1 : y ≤ (5 / 11 : ℝ) := by
    dsimp only [y]
    apply (div_le_iff₀ (by positivity : 0 < 2 * t)).mpr
    linarith
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hA0 : 0 ≤ A := by
    have hy : 0 ≤ 1 - y := by linarith
    dsimp only [A]
    positivity
  have hQ : 0 ≤ Q := by
    apply div_nonneg
    · nlinarith [mul_nonneg (sq_nonneg u) ht.le]
    · positivity
  have hH0 : 0 ≤ entropy u := entropy_nonneg ⟨by linarith, hu1.le⟩
  have hH : entropy u ≤ (1 - u) * t * R := by
    have hlog : Real.log (1 + e) ≤ e := by
      have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + e)
      linarith
    have hid : entropy u = (1 - u) * t + Real.log (1 + e) :=
      entropy_eq_large_parameter_form hu0 hu1
    have hr : (1 - u) * t * R = (1 - u) * t + e := by
      dsimp only [R, e, y]
      field_simp [ht.ne', hp.ne']
      ring
    rw [hr, hid]
    linarith
  have hcoef : ((1 - u) * t) ^ 2 * Q = (1 / 2 : ℝ) * A := by
    dsimp only [Q, A, e, y]
    field_simp [ht.ne', hp.ne', hsq.ne']
    ring
  have hRsq : R ^ 2 ≤ (1 + 10 * y / 9) ^ 2 := by
    apply pow_le_pow_left₀ hR0
    dsimp only [R]
    nlinarith [mul_le_mul_of_nonneg_right he1 hy0]
  have hA : A ≤ 1 - y + (1 + y) / 81 := by
    have he2 := pow_le_pow_left₀ he0 he1 2
    have hmul := mul_le_mul_of_nonneg_left he2 (by linarith : 0 ≤ 1 + y)
    dsimp only [A]
    nlinarith
  have hprod : A * R ^ 2 ≤ (1 - y + (1 + y) / 81) * (1 + 10 * y / 9) ^ 2 :=
    mul_le_mul hA hRsq (sq_nonneg R) (hA0.trans hA)
  change entropy u ^ 2 * Q ≤ 2 / 3
  calc
    entropy u ^ 2 * Q ≤ ((1 - u) * t * R) ^ 2 * Q :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hH0 hH 2) hQ
    _ = (((1 - u) * t) ^ 2 * Q) * R ^ 2 := by ring
    _ = (1 / 2 : ℝ) * (A * R ^ 2) := by rw [hcoef]; ring
    _ ≤ (1 / 2 : ℝ) * ((1 - y + (1 + y) / 81) * (1 + 10 * y / 9) ^ 2) :=
      mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ ≤ 2 / 3 := by simpa only [mul_assoc] using large_parameter_polynomial_bound hy0 hy1

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.CurvatureBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem entropy_curvature_bound {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    entropy u ^ 2 * curvatureModel u (Real.artanh u) ≤ 2 / 3 := by
  by_cases hz : u ^ 2 ≤ 2 / 3
  · exact medium_curvature_bound hu0 hu1 hz
  · exact large_curvature_bound hu0.le hu1 (le_of_not_ge hz)

theorem inverseEntropy_curvature_bound {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) ell) :
    (ell - s) ^ 2 * rSecondDeriv s ≤ 2 / 3 := by
  have hu := psiInv_mem_Ioo hs
  have h := entropy_curvature_bound hu.1 hu.2
  rw [rSecondDeriv, ite_eq_right (not_le.mpr hs.1)]
  simpa only [entropy, psi_psiInv hs.1.le hs.2, curvatureModel] using h

theorem L_curvature_bound {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) ell) :
    x ^ 2 * rSecondDeriv (ell - x) ≤ 2 / 3 := by
  have hs : ell - x ∈ Ioo (0 : ℝ) ell := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  simpa only [sub_sub_cancel] using inverseEntropy_curvature_bound hs

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.LRegularity ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem LDeriv_eq_zero_of_ell_le {x : ℝ} (hx : ell ≤ x) : LDeriv x = 0 := by
  simp [LDeriv, not_lt.mpr hx]

theorem LSecondDeriv_eq_zero_of_ell_le {x : ℝ} (hx : ell ≤ x) : LSecondDeriv x = 0 := by
  simp [LSecondDeriv, not_lt.mpr hx]

private theorem L_eq_rGap_on_left {x : ℝ} (hx : x ∈ Ioc 0 ell) :
    L x = rGap (ell - x) := by
  rcases hx.2.lt_or_eq with hlt | rfl
  · exact L_eq_rGap ⟨hx.1, hlt⟩
  · simp [L]

private theorem LDeriv_eq_formula_on_left {x : ℝ} (hx : x ∈ Ioc 0 ell) :
    LDeriv x = 2 - rDeriv (ell - x) := by
  rcases hx.2.lt_or_eq with hlt | rfl
  · exact ite_eq_left ⟨hx.1, hlt⟩
  · simp [LDeriv]

private theorem L_join_neighborhood : Ioc (0 : ℝ) ell ∪ Ici ell ∈ 𝓝 ell := by
  apply mem_of_superset (Ioi_mem_nhds ell_pos)
  intro x hx
  rcases le_total x ell with h | h
  · exact Or.inl ⟨hx, h⟩
  · exact Or.inr h

theorem hasDerivAt_L_of_gt {x : ℝ} (hx : ell < x) :
    HasDerivAt L (LDeriv x) x := by
  have he : L =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact L_eq_zero_of_ell_le (le_of_lt hy)
  rw [LDeriv_eq_zero_of_ell_le hx.le]
  exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he

theorem hasDerivAt_LDeriv_of_gt {x : ℝ} (hx : ell < x) :
    HasDerivAt LDeriv 0 x := by
  have he : LDeriv =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact LDeriv_eq_zero_of_ell_le (le_of_lt hy)
  exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he

theorem hasDerivAt_LDeriv {x : ℝ} (hx : 0 < x) (hne : x ≠ ell) :
    HasDerivAt LDeriv (LSecondDeriv x) x := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · simpa only [LSecondDeriv, ite_eq_left hlt] using hasDerivAt_LDeriv_of_lt ⟨hx, hlt⟩
  · rw [LSecondDeriv_eq_zero_of_ell_le hgt.le]
    exact hasDerivAt_LDeriv_of_gt hgt

theorem hasDerivAt_L_at_ell : HasDerivAt L (LDeriv ell) ell := by
  have hleft0 : HasDerivWithinAt (fun x : ℝ => rGap (ell - x)) 0 (Ioc 0 ell) ell := by
    convert! hasDerivWithinAt_rGap_zero.comp_of_eq ell
      ((hasDerivAt_id ell).const_sub ell).hasDerivWithinAt
      (show MapsTo (fun x : ℝ => ell - x) (Ioc 0 ell) (Ici 0) from
        fun x hx => sub_nonneg.mpr hx.2) (by simp) using 1
    simp
  have hleft : HasDerivWithinAt L 0 (Ioc 0 ell) ell :=
    hleft0.congr (fun _ hx => L_eq_rGap_on_left hx) (by simp [L])
  have hright : HasDerivWithinAt L 0 (Ici ell) ell :=
    (hasDerivAt_const ell (0 : ℝ)).hasDerivWithinAt.congr
      (fun _ hx => L_eq_zero_of_ell_le hx) (L_eq_zero_of_ell_le le_rfl)
  simpa only [LDeriv_eq_zero_of_ell_le (le_refl ell)] using
    (hleft.union hright).hasDerivAt L_join_neighborhood

theorem hasDerivAt_L {x : ℝ} (hx : 0 < x) : HasDerivAt L (LDeriv x) x := by
  rcases lt_trichotomy x ell with hlt | rfl | hgt
  · exact hasDerivAt_L_of_lt ⟨hx, hlt⟩
  · exact hasDerivAt_L_at_ell
  · exact hasDerivAt_L_of_gt hgt

theorem continuousAt_LDeriv_at_ell : ContinuousAt LDeriv ell := by
  have hr : ContinuousWithinAt rDeriv (Ico 0 ell) 0 :=
    continuousOn_rDeriv 0 ⟨le_rfl, ell_pos⟩
  have hcomp : ContinuousWithinAt (fun x : ℝ => rDeriv (ell - x)) (Ioc 0 ell) ell := by
    exact hr.comp_of_eq
      ((continuous_const.sub continuous_id).continuousWithinAt :
        ContinuousWithinAt (fun x : ℝ => ell - x) (Ioc 0 ell) ell)
      (show MapsTo (fun x : ℝ => ell - x) (Ioc 0 ell) (Ico 0 ell) from
        fun x hx => ⟨sub_nonneg.mpr hx.2, by linarith [hx.1]⟩) (by simp)
  have hleft : ContinuousWithinAt LDeriv (Ioc 0 ell) ell :=
    (continuousWithinAt_const.sub hcomp).congr
      (fun _ hx => LDeriv_eq_formula_on_left hx) (by simp [LDeriv])
  have hright : ContinuousWithinAt LDeriv (Ici ell) ell :=
    continuousWithinAt_const.congr (fun _ hx => LDeriv_eq_zero_of_ell_le hx)
      (LDeriv_eq_zero_of_ell_le le_rfl)
  exact (hleft.union hright).continuousAt L_join_neighborhood

theorem continuousOn_LDeriv : ContinuousOn LDeriv (Ioi 0) := by
  intro x hx
  by_cases hxe : x = ell
  · subst x
    exact continuousAt_LDeriv_at_ell.continuousWithinAt
  · exact (hasDerivAt_LDeriv hx hxe).continuousAt.continuousWithinAt

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.LShape ----
namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

theorem L_eq_rGap_max {x : ℝ} (hx : 0 < x) :
    L x = rGap (max (ell - x) 0) := by
  by_cases hxl : x < ell
  · rw [L_eq_rGap ⟨hx, hxl⟩, max_eq_left (sub_nonneg.mpr hxl.le)]
  · rw [L_eq_zero_of_ell_le (le_of_not_gt hxl),
      max_eq_right (sub_nonpos.mpr (le_of_not_gt hxl)), rGap_zero]

theorem positivePart_ell_sub_mem {x : ℝ} (hx : 0 < x) :
    max (ell - x) 0 ∈ Ico 0 ell := by
  exact ⟨le_max_right _ _, max_lt (by linarith) ell_pos⟩

theorem L_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ L x := by
  rw [L_eq_rGap_max hx]
  exact rGap_nonneg (positivePart_ell_sub_mem hx).1 (positivePart_ell_sub_mem hx).2

theorem antitoneOn_L : AntitoneOn L (Ioi 0) := by
  intro x hx y hy hxy
  rw [L_eq_rGap_max hx, L_eq_rGap_max hy]
  exact monotoneOn_rGap (positivePart_ell_sub_mem hy) (positivePart_ell_sub_mem hx)
    (max_le_max (sub_le_sub_left hxy ell) le_rfl)

theorem convexOn_L : ConvexOn ℝ (Ioi 0) L := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz : 0 < a * x + b * y := by
    simpa only [smul_eq_mul, mem_Ioi] using (convex_Ioi (0 : ℝ)) hx hy ha hb hab
  have hsum : a * max (ell - x) 0 + b * max (ell - y) 0 ∈ Ico 0 ell := by
    simpa only [smul_eq_mul] using
      (convex_Ico (0 : ℝ) ell) (positivePart_ell_sub_mem hx)
        (positivePart_ell_sub_mem hy) ha hb hab
  have hmax : max (ell - (a * x + b * y)) 0 ≤
      a * max (ell - x) 0 + b * max (ell - y) 0 := by
    apply max_le
    · calc
        ell - (a * x + b * y) = a * (ell - x) + b * (ell - y) := by
          nlinarith [congrArg (fun t : ℝ => t * ell) hab]
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _))
        (mul_nonneg hb (le_max_right _ _))
  simp only [smul_eq_mul]
  rw [L_eq_rGap_max hz, L_eq_rGap_max hx, L_eq_rGap_max hy]
  exact (monotoneOn_rGap (positivePart_ell_sub_mem hz) hsum hmax).trans
    (convexOn_rGap.2 (positivePart_ell_sub_mem hx) (positivePart_ell_sub_mem hy)
      ha hb hab)

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.FiniteNoise ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators

noncomputable section

universe u

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem cubeAverage_zeroDim (g : Cube 0 → ℝ) :
    cubeAverage g = g (fun _ => false) := by
  simp only [cubeAverage, pow_zero, div_one, Fintype.sum_unique]
  exact congrArg g (Subsingleton.elim _ _)

theorem cubeAverage_sub (g h : Cube n → ℝ) :
    cubeAverage (fun x => g x - h x) = cubeAverage g - cubeAverage h := by
  simp [cubeAverage, Finset.sum_sub_distrib, sub_div]

theorem cubeAverage_neg (g : Cube n → ℝ) :
    cubeAverage (fun x => -g x) = -cubeAverage g := by
  simp [cubeAverage, neg_div]

theorem cubeAverage_smul (c : ℝ) (g : Cube n → ℝ) :
    cubeAverage (fun x => c * g x) = c * cubeAverage g := by
  simp [cubeAverage, ← Finset.mul_sum, mul_div_assoc]

theorem cubeAverage_nonneg {g : Cube n → ℝ} (hg : ∀ x, 0 ≤ g x) :
    0 ≤ cubeAverage g :=
  div_nonneg (Finset.sum_nonneg fun x _ => hg x) (le_of_lt (cube_denominator_pos n))

theorem cubeAverage_mono {g h : Cube n → ℝ} (hgh : ∀ x, g x ≤ h x) :
    cubeAverage g ≤ cubeAverage h := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => hgh x)
    (le_of_lt (cube_denominator_pos n))

theorem cubeAverage_strict_mono {g h : Cube n → ℝ} (hgh : ∀ x, g x ≤ h x)
    (hlt : ∃ x, g x < h x) : cubeAverage g < cubeAverage h := by
  apply (div_lt_div_iff_of_pos_right (cube_denominator_pos n)).2
  apply Finset.sum_lt_sum (fun x _ => hgh x)
  obtain ⟨x, hx⟩ := hlt
  exact ⟨x, Finset.mem_univ x, hx⟩

theorem cubeAverage_lt {g h : Cube n → ℝ} (hgh : ∀ x, g x < h x) :
    cubeAverage g < cubeAverage h := by
  exact cubeAverage_strict_mono (fun x => (hgh x).le) ⟨fun _ => false, hgh _⟩

theorem IsInterior.cubeAverage {g : Cube n → ℝ} (hg : IsInterior g) :
    -1 < cubeAverage g ∧ cubeAverage g < 1 := by
  constructor
  · simpa using cubeAverage_lt (fun x => (hg x).1)
  · simpa using cubeAverage_lt (fun x => (hg x).2)

theorem noiseKernel_symm (u : ℝ) (x y : Cube n) :
    noiseKernel u x y = noiseKernel u y x := by
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : x i = y i
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

theorem noiseKernel_nonneg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (x y : Cube n) : 0 ≤ noiseKernel u x y := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith

theorem noiseKernel_col_sum (u : ℝ) (y : Cube n) :
    ∑ x, noiseKernel u x y = 1 := by
  simp_rw [noiseKernel_symm u]
  exact noiseKernel_row_sum u y

theorem noiseKernel_split_coord (u : ℝ) (x y : Cube n) (i : Fin n) :
    noiseKernel u x y =
      (if x i = y i then (1 + u) / 2 else (1 - u) / 2) *
        ∏ j ∈ Finset.univ.erase i, if x j = y j then (1 + u) / 2 else (1 - u) / 2 := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

theorem cubeAverage_noiseOperator (u : ℝ) (g : Cube n → ℝ) :
    cubeAverage (noiseOperator u g) = cubeAverage g := by
  unfold cubeAverage noiseOperator
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, noiseKernel_col_sum, one_mul]

theorem noiseOperator_mono {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    {g h : Cube n → ℝ} (hgh : ∀ y, g y ≤ h y) (x : Cube n) :
    noiseOperator u g x ≤ noiseOperator u h x := by
  exact Finset.sum_le_sum fun y _ =>
    mul_le_mul_of_nonneg_left (hgh y) (noiseKernel_nonneg hu0 hu1 x y)

theorem noiseOperator_bounds {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    {g : Cube n → ℝ} (hg : ∀ y, -1 ≤ g y ∧ g y ≤ 1) (x : Cube n) :
    -1 ≤ noiseOperator u g x ∧ noiseOperator u g x ≤ 1 := by
  constructor
  · simpa using noiseOperator_mono hu0 hu1 (fun y => (hg y).1) x
  · simpa using noiseOperator_mono hu0 hu1 (fun y => (hg y).2) x

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.Rearrangement ----
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem sortCoordinate_increasingIn (i : Fin n) (F : Cube n → ℝ) :
    IsIncreasingIn i (sortCoordinate i F) := by
  intro x
  simp only [sortCoordinate_false, sortCoordinate_true]
  exact min_le_max

theorem sortCoordinate_preserves_increasingIn (i j : Fin n) {F : Cube n → ℝ}
    (hF : IsIncreasingIn j F) : IsIncreasingIn j (sortCoordinate i F) := by
  by_cases hij : i = j
  · subst j
    exact sortCoordinate_increasingIn i F
  · intro x
    have h0 := hF (setBit i false x)
    have h1 := hF (setBit i true x)
    simp only [sortCoordinate, setBit, Function.update_of_ne hij,
      Function.update_comm (Ne.symm hij)]
    cases hx : x i <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact min_le_min h0 h1
    · exact max_le_max h0 h1

theorem increasingIn_setBit_mono {F : Cube n → ℝ} {i : Fin n}
    (hF : IsIncreasingIn i F) (x : Cube n) (a b : Bool) (hab : a ≤ b) :
    F (setBit i a x) ≤ F (setBit i b x) := by
  cases a <;> cases b
  · exact le_rfl
  · exact hF x
  · exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) hab)
  · exact le_rfl

theorem isIncreasing_of_forall_increasingIn {F : Cube n → ℝ}
    (hF : ∀ i, IsIncreasingIn i F) : IsIncreasing F := by
  intro x y hxy
  let fill (s : Finset (Fin n)) : Cube n := fun i => if i ∈ s then y i else x i
  have hfill : ∀ s : Finset (Fin n), F x ≤ F (fill s) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [fill]
    | @insert i s hi ih =>
      have hstep : F (fill s) ≤ F (setBit i (y i) (fill s)) := by
        have horder : fill s i ≤ y i := by simp [fill, hi, hxy i]
        simpa only [setBit_self] using
          increasingIn_setBit_mono (hF i) (fill s) (fill s i) (y i) horder
      have heq : setBit i (y i) (fill s) = fill (insert i s) := by
        funext j
        by_cases hji : j = i
        · subst j; simp [fill]
        · simp [setBit, fill, hji]
      exact ih.trans (heq ▸ hstep)
  simpa [fill] using hfill Finset.univ

theorem pair_sum_setBit (i : Fin n) (F : Cube n → ℝ) (x : Cube n) :
    F (setBit i false x) + F (setBit i true x) = F x + F (flip i x) := by
  have hself := setBit_self i x
  cases hx : x i
  · simpa [setBit, flip, LeanBlast.GotsmanLinial.flip, hx] using
      congrArg (fun z => F z + F (setBit i true x)) hself
  · simpa [setBit, flip, LeanBlast.GotsmanLinial.flip, hx, add_comm] using
      congrArg (fun z => F (setBit i false x) + F z) hself

theorem sum_comp_flip (i : Fin n) (F : Cube n → ℝ) :
    (∑ x, F (flip i x)) = ∑ x, F x := by
  exact Fintype.sum_bijective (flip i) (LeanBlast.GotsmanLinial.flip_bijective i) _ _
    (fun _ => rfl)

theorem sum_setBit_pair (i : Fin n) (F : Cube n → ℝ) :
    (∑ x, (F (setBit i false x) + F (setBit i true x))) = 2 * ∑ x, F x := by
  simp_rw [pair_sum_setBit]
  rw [Finset.sum_add_distrib, sum_comp_flip]
  ring

theorem cubeAverage_sortCoordinate (i : Fin n) (F : Cube n → ℝ) :
    cubeAverage (sortCoordinate i F) = cubeAverage F := by
  have h : (∑ x, (sortCoordinate i F (setBit i false x) +
      sortCoordinate i F (setBit i true x))) =
      ∑ x, (F (setBit i false x) + F (setBit i true x)) := by
    simp only [sortCoordinate_false, sortCoordinate_true, min_add_max]
  rw [sum_setBit_pair, sum_setBit_pair] at h
  have hs : (∑ x, sortCoordinate i F x) = ∑ x, F x := by linarith
  exact congrArg (fun z : ℝ => z / (2 : ℝ) ^ n) hs

theorem coordinateOffKernel_setBit_left (i : Fin n) (u : ℝ) (x y : Cube n) (b : Bool) :
    coordinateOffKernel i u (setBit i b x) y = coordinateOffKernel i u x y := by
  apply Finset.prod_congr rfl
  intro j hj
  simp only [setBit, Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem coordinateOffKernel_setBit_right (i : Fin n) (u : ℝ) (x y : Cube n) (b : Bool) :
    coordinateOffKernel i u x (setBit i b y) = coordinateOffKernel i u x y := by
  apply Finset.prod_congr rfl
  intro j hj
  simp only [setBit, Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem noiseKernel_setBit_pair (i : Fin n) (u : ℝ) (x y : Cube n) (a b : Bool) :
    noiseKernel u (setBit i a x) (setBit i b y) =
      (if a = b then (1 + u) / 2 else (1 - u) / 2) * coordinateOffKernel i u x y := by
  rw [noiseKernel_split_coord _ _ _ i]
  simp only [setBit_apply_same]
  change (if a = b then _ else _) *
    coordinateOffKernel i u (setBit i a x) (setBit i b y) = _
  rw [coordinateOffKernel_setBit_left, coordinateOffKernel_setBit_right]

theorem coordinateOffKernel_nonneg (i : Fin n) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    (x y : Cube n) : 0 ≤ coordinateOffKernel i u x y := by
  apply Finset.prod_nonneg
  intro j _
  split_ifs <;> linarith [hu.1, hu.2]

theorem coordinateOffNoise_add (i : Fin n) (u : ℝ) (F G : Cube n → ℝ) (x : Cube n) :
    coordinateOffNoise i u (fun y => F y + G y) x =
      coordinateOffNoise i u F x + coordinateOffNoise i u G x := by
  simp only [coordinateOffNoise, mul_add, Finset.sum_add_distrib]

theorem coordinateOffNoise_smul (i : Fin n) (u c : ℝ) (F : Cube n → ℝ) (x : Cube n) :
    coordinateOffNoise i u (fun y => c * F y) x = c * coordinateOffNoise i u F x := by
  simp only [coordinateOffNoise, Finset.mul_sum, mul_left_comm]

theorem coordinateOffNoise_mono (i : Fin n) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    {F G : Cube n → ℝ} (hFG : ∀ y, F y ≤ G y) (x : Cube n) :
    coordinateOffNoise i u F x ≤ coordinateOffNoise i u G x := by
  exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hFG y)
    (div_nonneg (coordinateOffKernel_nonneg i hu x y) (by norm_num))

theorem coordinateOffNoise_nonneg (i : Fin n) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    {F : Cube n → ℝ} (hF : ∀ y, 0 ≤ F y) (x : Cube n) :
    0 ≤ coordinateOffNoise i u F x := by
  exact Finset.sum_nonneg fun y _ =>
    mul_nonneg (div_nonneg (coordinateOffKernel_nonneg i hu x y) (by norm_num)) (hF y)

theorem coordinateOffNoise_abs_bound (i : Fin n) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    (F : Cube n → ℝ) (x : Cube n) :
    -coordinateOffNoise i u (fun y => |F y|) x ≤ coordinateOffNoise i u F x ∧
      coordinateOffNoise i u F x ≤ coordinateOffNoise i u (fun y => |F y|) x := by
  constructor
  · have h := coordinateOffNoise_mono i hu (fun y => neg_abs_le (F y)) x
    have heq : coordinateOffNoise i u (fun y => -|F y|) x =
        -coordinateOffNoise i u (fun y => |F y|) x := by
      simp [coordinateOffNoise]
    rw [heq] at h
    exact h
  · exact coordinateOffNoise_mono i hu (fun y => le_abs_self (F y)) x

theorem noiseOperator_setBit (i : Fin n) (u : ℝ) (F : Cube n → ℝ)
    (x : Cube n) (b : Bool) :
    noiseOperator u F (setBit i b x) =
      coordinateOffNoise i u (coordinatePairMean i F) x +
        (if b then u else -u) * coordinateOffNoise i u (coordinatePairDifference i F) x := by
  have h := sum_setBit_pair i (fun y => noiseKernel u (setBit i b x) y * F y)
  change _ = 2 * noiseOperator u F (setBit i b x) at h
  have heq : (∑ y, (noiseKernel u (setBit i b x) (setBit i false y) * F (setBit i false y) +
      noiseKernel u (setBit i b x) (setBit i true y) * F (setBit i true y))) =
      2 * coordinateOffNoise i u (fun y => coordinatePairMean i F y +
        (if b then u else -u) * coordinatePairDifference i F y) x := by
    rw [coordinateOffNoise, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [noiseKernel_setBit_pair, noiseKernel_setBit_pair]
    cases b <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
      coordinatePairMean, coordinatePairDifference] <;> ring
  rw [heq, coordinateOffNoise_add, coordinateOffNoise_smul] at h
  linarith

theorem informationDeficit_eq_psi_difference (F : Cube n → ℝ) :
    informationDeficit F = cubeAverage (fun x => psi (F x)) - psi (cubeAverage F) := by
  unfold informationDeficit entropyAverage entropy
  rw [cubeAverage_sub, cubeAverage_const]
  ring

theorem sortCoordinates_increasingIn (is : List (Fin n)) {F : Cube n → ℝ}
    (j : Fin n) (hj : j ∈ is ∨ IsIncreasingIn j F) :
    IsIncreasingIn j (sortCoordinates is F) := by
  induction is generalizing F with
  | nil => exact hj.resolve_left (by simp)
  | cons i is ih =>
      apply ih
      rcases hj with hmem | hinc
      · rcases List.mem_cons.mp hmem with hji | hmem
        · subst j
          exact Or.inr (sortCoordinate_increasingIn i F)
        · exact Or.inl hmem
      · exact Or.inr (sortCoordinate_preserves_increasingIn i j hinc)

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.SemigroupFlow ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

private theorem noiseKernel_flip_derivative_term (u : ℝ)
    (x y : Cube n) (i : Fin n) :
    (∏ j ∈ Finset.univ.erase i,
      if x j = y j then (1 + u) / 2 else (1 - u) / 2) *
      (if x i = y i then -u / 2 else u / 2) =
        -((noiseKernel u x y - noiseKernel u (flip i x) y) / 2) := by
  have hrest : (∏ j ∈ Finset.univ.erase i,
      if (flip i x) j = y j then (1 + u) / 2 else (1 - u) / 2) =
      ∏ j ∈ Finset.univ.erase i,
        if x j = y j then (1 + u) / 2 else (1 - u) / 2 := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp only [flip, LeanBlast.GotsmanLinial.flip, Function.update_of_ne hji]
  rw [noiseKernel_split_coord u x y i, noiseKernel_split_coord u (flip i x) y i, hrest]
  cases hx : x i <;> cases hy : y i <;>
    simp [flip, LeanBlast.GotsmanLinial.flip, hx] <;> ring

private theorem hasDerivAt_noise_factor (x y : Cube n) (i : Fin n) (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
      if x i = y i then (1 + Real.exp (-s)) / 2 else (1 - Real.exp (-s)) / 2)
      (if x i = y i then -Real.exp (-t) / 2 else Real.exp (-t) / 2) t := by
  have hu : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  by_cases hxy : x i = y i
  · simp only [ite_eq_left hxy]
    exact (hu.const_add 1).div_const 2
  · simp only [ite_eq_right hxy]
    simpa using (hu.const_sub 1).div_const 2

theorem hasDerivAt_noiseKernel_flow (x y : Cube n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => noiseKernel (Real.exp (-s)) x y)
      (-(∑ i : Fin n,
        (noiseKernel (Real.exp (-t)) x y -
          noiseKernel (Real.exp (-t)) (flip i x) y) / 2)) t := by
  have h := HasDerivAt.fun_finsetProd
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hasDerivAt_noise_factor x y i t)
  convert! h using 1
  simp only [smul_eq_mul, noiseKernel_flip_derivative_term, Finset.sum_neg_distrib]

theorem cubeDerivative_noiseOperator (u : ℝ) (F : Cube n → ℝ)
    (i : Fin n) (x : Cube n) :
    cubeDerivative i (noiseOperator u F) x =
      ∑ y, ((noiseKernel u x y - noiseKernel u (flip i x) y) / 2) * F y := by
  simp [cubeDerivative, noiseOperator, sub_div, sub_mul,
    div_mul_eq_mul_div, Finset.sum_sub_distrib, Finset.sum_div]

theorem hasDerivAt_noiseFlow (F : Cube n → ℝ) (t : ℝ) (x : Cube n) :
    HasDerivAt (fun s : ℝ => noiseFlow F s x)
      (-(∑ i : Fin n, cubeDerivative i (noiseFlow F t) x)) t := by
  have h := HasDerivAt.fun_sum
    (fun y (_ : y ∈ (Finset.univ : Finset (Cube n))) =>
      (hasDerivAt_noiseKernel_flow x y t).mul_const (F y))
  convert! h using 1
  simp only [noiseFlow, cubeDerivative_noiseOperator, neg_mul,
    Finset.sum_mul, Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_comm

theorem cubeAverage_noiseFlow (F : Cube n → ℝ) (t : ℝ) :
    cubeAverage (noiseFlow F t) = cubeAverage F :=
  cubeAverage_noiseOperator _ _

theorem hasDerivAt_entropyAverage_noiseFlow_of_isInterior
    (F : Cube n → ℝ) (t : ℝ) (hinterior : IsInterior (noiseFlow F t)) :
    HasDerivAt (fun s : ℝ => entropyAverage (noiseFlow F s))
      (dissipation (noiseFlow F t)) t := by
  have h := (HasDerivAt.fun_sum
    (fun x (_ : x ∈ (Finset.univ : Finset (Cube n))) =>
      (hasDerivAt_entropy (hinterior x)).comp t (hasDerivAt_noiseFlow F t x))).div_const
      ((2 : ℝ) ^ n)
  convert! h using 1
  simp only [dissipation, cubeAverage, neg_mul_neg, Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_comm

theorem hasDerivAt_informationDeficit_noiseFlow_of_isInterior
    (F : Cube n → ℝ) (t : ℝ) (hinterior : IsInterior (noiseFlow F t)) :
    HasDerivAt (fun s : ℝ => informationDeficit (noiseFlow F s))
      (-dissipation (noiseFlow F t)) t := by
  simpa only [informationDeficit, cubeAverage_noiseFlow] using
    (hasDerivAt_entropyAverage_noiseFlow_of_isInterior F t hinterior).const_sub
      (entropy (cubeAverage F))

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.CubeSplits ----
namespace OAI

open scoped BigOperators

noncomputable section

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem cubeAverage_pairHalfDifference (g : Cube (n + 1) → ℝ) :
    cubeAverage (pairHalfDifference g) =
      (cubeAverage (restrict g true) - cubeAverage (restrict g false)) / 2 := by
  unfold pairHalfDifference
  rw [cubeAverage_div, cubeAverage_sub]

theorem cubeAverage_pairMean_add_halfDifference (g : Cube (n + 1) → ℝ) :
    cubeAverage (pairMean g) + cubeAverage (pairHalfDifference g) =
      cubeAverage (restrict g true) := by
  rw [cubeAverage_pairMean, cubeAverage_split, cubeAverage_pairHalfDifference]
  ring

theorem cubeAverage_pairMean_sub_halfDifference (g : Cube (n + 1) → ℝ) :
    cubeAverage (pairMean g) - cubeAverage (pairHalfDifference g) =
      cubeAverage (restrict g false) := by
  rw [cubeAverage_pairMean, cubeAverage_split, cubeAverage_pairHalfDifference]
  ring

theorem entropyAverage_split (g : Cube (n + 1) → ℝ) :
    entropyAverage g = (entropyAverage (restrict g true) + entropyAverage (restrict g false)) / 2 := by
  exact cubeAverage_split (fun x => entropy (g x))

theorem informationDeficit_split (g : Cube (n + 1) → ℝ) :
    (informationDeficit (restrict g true) + informationDeficit (restrict g false)) / 2 =
      informationDeficit g - pairEntropyGap (cubeAverage (pairMean g))
        (cubeAverage (pairHalfDifference g)) := by
  rw [pairEntropyGap, cubeAverage_pairMean_add_halfDifference,
    cubeAverage_pairMean_sub_halfDifference, cubeAverage_pairMean]
  simp only [informationDeficit]
  rw [entropyAverage_split]
  ring

theorem meanVariance_split (g : Cube (n + 1) → ℝ) :
    (meanVariance (restrict g true) + meanVariance (restrict g false)) / 2 =
      meanVariance g - (cubeAverage (pairHalfDifference g)) ^ 2 := by
  simp only [meanVariance]
  rw [cubeAverage_split, cubeAverage_pairHalfDifference]
  ring

theorem flip_zero_cases (b : Bool) (x : Cube n) :
    flip (0 : Fin (n + 1)) (Fin.cases b x) = Fin.cases (!b) x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [flip, LeanBlast.GotsmanLinial.flip]
  · simp [flip, LeanBlast.GotsmanLinial.flip]

theorem flip_succ_cases (i : Fin n) (b : Bool) (x : Cube n) :
    flip i.succ (Fin.cases b x) = Fin.cases b (flip i x) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · have h0 : (0 : Fin (n + 1)) ≠ i.succ := Ne.symm (Fin.succ_ne_zero i)
    simp [flip, LeanBlast.GotsmanLinial.flip, h0]
  · by_cases hki : k = i
    · subst k
      simp [flip, LeanBlast.GotsmanLinial.flip]
    · simp [flip, LeanBlast.GotsmanLinial.flip, hki]

theorem cubeAverage_first_coordinate_energy (g : Cube (n + 1) → ℝ) :
    cubeAverage (fun x => Real.artanh (g x) * cubeDerivative 0 g x) =
      cubeAverage (fun x => pairDissipation (pairMean g x) (pairHalfDifference g x)) := by
  rw [cubeAverage_split_pair]
  congr 1
  funext x
  simp only [restrict, cubeDerivative, flip_zero_cases, Bool.not_true, Bool.not_false]
  rw [pairDissipation, pairMean_add_halfDifference, pairMean_sub_halfDifference]
  dsimp only [pairHalfDifference, restrict]
  ring

theorem cubeAverage_succ_coordinate_energy (g : Cube (n + 1) → ℝ) (i : Fin n) :
    cubeAverage (fun x => Real.artanh (g x) * cubeDerivative i.succ g x) =
      (cubeAverage (fun x => Real.artanh (restrict g true x) * cubeDerivative i (restrict g true) x) +
        cubeAverage (fun x => Real.artanh (restrict g false x) * cubeDerivative i (restrict g false) x)) / 2 := by
  have hr (b : Bool) :
      restrict (fun x => Real.artanh (g x) * cubeDerivative i.succ g x) b =
        (fun x => Real.artanh (restrict g b x) * cubeDerivative i (restrict g b) x) := by
    funext x
    simp only [restrict, cubeDerivative, flip_succ_cases]
  rw [cubeAverage_split, hr true, hr false]

theorem dissipation_split (g : Cube (n + 1) → ℝ) :
    dissipation g = (dissipation (restrict g true) + dissipation (restrict g false)) / 2 +
      cubeAverage (fun x => pairDissipation (pairMean g x) (pairHalfDifference g x)) := by
  simp only [dissipation]
  rw [Fin.sum_univ_succ, cubeAverage_first_coordinate_energy]
  simp_rw [cubeAverage_succ_coordinate_energy]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  ring

theorem IsInterior.restrict {g : Cube (n + 1) → ℝ} (hg : IsInterior g) (b : Bool) :
    IsInterior (LeanBlast.CourtadeKumar.restrict g b) := by
  intro x
  exact hg (Fin.cases b x)

theorem IsInterior.pairMean {g : Cube (n + 1) → ℝ} (hg : IsInterior g) :
    IsInterior (LeanBlast.CourtadeKumar.pairMean g) := by
  intro x
  have h1 := hg.restrict true x
  have h0 := hg.restrict false x
  dsimp only [LeanBlast.CourtadeKumar.pairMean]
  constructor <;> linarith

theorem IsInterior.pairDomain {g : Cube (n + 1) → ℝ} (hg : IsInterior g) :
    ∀ x, |LeanBlast.CourtadeKumar.pairMean g x| + |pairHalfDifference g x| < 1 := by
  intro x
  have h1 := hg.restrict true x
  have h0 := hg.restrict false x
  have hsum := pairMean_add_halfDifference g x
  have hsub := pairMean_sub_halfDifference g x
  rcases le_total 0 (LeanBlast.CourtadeKumar.pairMean g x) with ha | ha <;>
    rcases le_total 0 (pairHalfDifference g x) with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb]
    linarith
  · rw [abs_of_nonneg ha, abs_of_nonpos hb]
    linarith
  · rw [abs_of_nonpos ha, abs_of_nonneg hb]
    linarith
  · rw [abs_of_nonpos ha, abs_of_nonpos hb]
    linarith

theorem cubeVariance_nonneg (g : Cube n → ℝ) : 0 ≤ cubeVariance g :=
  cubeAverage_nonneg fun _ => sq_nonneg _

theorem cubeVariance_eq (g : Cube n → ℝ) :
    cubeVariance g = cubeAverage (fun x => (g x) ^ 2) - (cubeAverage g) ^ 2 := by
  unfold cubeVariance
  have heq : (fun x => (g x - cubeAverage g) ^ 2) =
      (fun x => (g x) ^ 2 - (2 * cubeAverage g) * g x + (cubeAverage g) ^ 2) := by
    funext x
    ring
  rw [heq, cubeAverage_add, cubeAverage_sub, cubeAverage_smul, cubeAverage_const]
  ring

theorem average_one_sub_sq_eq_meanVariance_sub_variance (g : Cube n → ℝ) :
    cubeAverage (fun x => 1 - (g x) ^ 2) = meanVariance g - cubeVariance g := by
  rw [cubeAverage_sub, cubeAverage_const, cubeVariance_eq]
  unfold meanVariance
  ring

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.PairEntropy ----
namespace OAI

noncomputable section

namespace LeanBlast.CourtadeKumar

theorem pair_mean_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) : a ∈ Set.Ioo (-1) 1 := by
  have ha : |a| < 1 := lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg b)) h
  exact abs_lt.mp ha

theorem pair_add_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) : a + b ∈ Set.Ioo (-1) 1 := by
  exact abs_lt.mp (lt_of_le_of_lt (abs_add_le a b) h)

theorem pair_sub_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) : a - b ∈ Set.Ioo (-1) 1 := by
  exact abs_lt.mp (lt_of_le_of_lt (abs_sub a b) h)

theorem pair_denom_add_pos (a b : ℝ) (h : |a| + |b| < 1) : 0 < 1 + a := by
  have ha := (pair_mean_mem_Ioo a b h).1
  linarith

theorem pair_denom_sub_pos (a b : ℝ) (h : |a| + |b| < 1) : 0 < 1 - a := by
  have ha := (pair_mean_mem_Ioo a b h).2
  linarith

theorem pair_abs_lt_denom_add (a b : ℝ) (h : |a| + |b| < 1) : |b| < 1 + a := by
  linarith [neg_le_abs a]

theorem pair_abs_lt_denom_sub (a b : ℝ) (h : |a| + |b| < 1) : |b| < 1 - a := by
  linarith [le_abs_self a]

private theorem div_mem_Ioo (s b : ℝ) (hs : 0 < s) (hb : |b| < s) :
    b / s ∈ Set.Ioo (-1) 1 := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hb
  constructor
  · apply (lt_div_iff₀ hs).2
    linarith
  · apply (div_lt_iff₀ hs).2
    linarith

theorem pair_ratio_add_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) :
    b / (1 + a) ∈ Set.Ioo (-1) 1 :=
  div_mem_Ioo (1 + a) b (pair_denom_add_pos a b h) (pair_abs_lt_denom_add a b h)

theorem pair_ratio_sub_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) :
    b / (1 - a) ∈ Set.Ioo (-1) 1 :=
  div_mem_Ioo (1 - a) b (pair_denom_sub_pos a b h) (pair_abs_lt_denom_sub a b h)

theorem pair_variance_pos (a b : ℝ) (h : |a| + |b| < 1) : 0 < 1 - a ^ 2 := by
  have hp := mul_pos (pair_denom_add_pos a b h) (pair_denom_sub_pos a b h)
  nlinarith

theorem pair_abs_lt_variance (a b : ℝ) (h : |a| + |b| < 1) :
    |b| < 1 - a ^ 2 := by
  have ha1 : |a| < 1 := lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg b)) h
  have hprod := mul_nonneg (abs_nonneg a) (show 0 ≤ 1 - |a| by linarith)
  nlinarith [sq_abs a]

theorem pair_weighted_sq (a b : ℝ) (h : |a| + |b| < 1) :
    (1 + a) / 2 * (b / (1 + a)) ^ 2 + (1 - a) / 2 * (b / (1 - a)) ^ 2 =
      b ^ 2 / (1 - a ^ 2) := by
  have hp := ne_of_gt (pair_denom_add_pos a b h)
  have hm := ne_of_gt (pair_denom_sub_pos a b h)
  have hv := ne_of_gt (pair_variance_pos a b h)
  field_simp
  ring

private theorem weighted_psi_div (s b : ℝ) (hs : 0 < s) (hb : |b| < s) :
    s / 2 * psi (b / s) =
      (s + b) / 4 * Real.log (s + b) + (s - b) / 4 * Real.log (s - b) -
        s / 2 * Real.log s := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hb
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hp : s + b ≠ 0 := ne_of_gt (by linarith)
  have hm : s - b ≠ 0 := ne_of_gt (by linarith)
  have hplus : 1 + b / s = (s + b) / s := by field_simp
  have hminus : 1 - b / s = (s - b) / s := by field_simp
  rw [psi, hplus, hminus, Real.log_div hp hs0, Real.log_div hm hs0]
  field_simp
  ring

theorem pairEntropyGap_weighted (a b : ℝ) (h : |a| + |b| < 1) :
    pairEntropyGap a b =
      (1 + a) / 2 * psi (b / (1 + a)) + (1 - a) / 2 * psi (b / (1 - a)) := by
  rw [weighted_psi_div (1 + a) b (pair_denom_add_pos a b h) (pair_abs_lt_denom_add a b h),
    weighted_psi_div (1 - a) b (pair_denom_sub_pos a b h) (pair_abs_lt_denom_sub a b h)]
  unfold pairEntropyGap entropy psi
  ring_nf

private theorem pair_artanh_eq_log_sub (x : ℝ) (hx : x ∈ Set.Ioo (-1) 1) :
    Real.artanh x = (Real.log (1 + x) - Real.log (1 - x)) / 2 := by
  rw [Real.artanh_eq_half_log ⟨le_of_lt hx.1, le_of_lt hx.2⟩,
    Real.log_div (ne_of_gt (by linarith [hx.1])) (ne_of_gt (by linarith [hx.2]))]
  ring

private theorem artanh_div (s b : ℝ) (hs : 0 < s) (hb : |b| < s) :
    Real.artanh (b / s) = (Real.log (s + b) - Real.log (s - b)) / 2 := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hb
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hp : s + b ≠ 0 := ne_of_gt (by linarith)
  have hm : s - b ≠ 0 := ne_of_gt (by linarith)
  have hplus : 1 + b / s = (s + b) / s := by field_simp
  have hminus : 1 - b / s = (s - b) / s := by field_simp
  rw [pair_artanh_eq_log_sub _ (div_mem_Ioo s b hs hb), hplus, hminus,
    Real.log_div hp hs0, Real.log_div hm hs0]
  ring

theorem pairDissipation_weighted (a b : ℝ) (h : |a| + |b| < 1) :
    pairDissipation a b =
      (1 + a) / 2 * (b / (1 + a) * Real.artanh (b / (1 + a))) +
        (1 - a) / 2 * (b / (1 - a) * Real.artanh (b / (1 - a))) := by
  have hp : 1 + a ≠ 0 := ne_of_gt (pair_denom_add_pos a b h)
  have hm : 1 - a ≠ 0 := ne_of_gt (pair_denom_sub_pos a b h)
  rw [pairDissipation, pair_artanh_eq_log_sub _ (pair_add_mem_Ioo a b h),
    pair_artanh_eq_log_sub _ (pair_sub_mem_Ioo a b h),
    artanh_div (1 + a) b (pair_denom_add_pos a b h) (pair_abs_lt_denom_add a b h),
    artanh_div (1 - a) b (pair_denom_sub_pos a b h) (pair_abs_lt_denom_sub a b h)]
  field_simp
  ring_nf

theorem pairEntropyGap_nonneg (a b : ℝ) (h : |a| + |b| < 1) :
    0 ≤ pairEntropyGap a b := by
  rw [pairEntropyGap_weighted a b h]
  exact add_nonneg
    (mul_nonneg (by linarith [pair_denom_add_pos a b h]) (psi_nonneg _))
    (mul_nonneg (by linarith [pair_denom_sub_pos a b h]) (psi_nonneg _))

theorem pairEntropyGap_div_variance_nonneg (a b : ℝ) (h : |a| + |b| < 1) :
    0 ≤ pairEntropyGap a b / (1 - a ^ 2) :=
  div_nonneg (pairEntropyGap_nonneg a b h) (le_of_lt (pair_variance_pos a b h))

theorem pairEntropyGap_le_quadratic (a b : ℝ) (h : |a| + |b| < 1) :
    pairEntropyGap a b ≤ ell * (b ^ 2 / (1 - a ^ 2)) := by
  calc
    _ = (1 + a) / 2 * psi (b / (1 + a)) +
        (1 - a) / 2 * psi (b / (1 - a)) := pairEntropyGap_weighted a b h
    _ ≤ (1 + a) / 2 * (ell * (b / (1 + a)) ^ 2) +
        (1 - a) / 2 * (ell * (b / (1 - a)) ^ 2) :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (psi_le_ell_mul_sq (le_of_lt (abs_lt.mpr (pair_ratio_add_mem_Ioo a b h))))
          (by linarith [pair_denom_add_pos a b h]))
        (mul_le_mul_of_nonneg_left
          (psi_le_ell_mul_sq (le_of_lt (abs_lt.mpr (pair_ratio_sub_mem_Ioo a b h))))
          (by linarith [pair_denom_sub_pos a b h]))
    _ = ell * ((1 + a) / 2 * (b / (1 + a)) ^ 2 +
        (1 - a) / 2 * (b / (1 - a)) ^ 2) := by ring
    _ = _ := by rw [pair_weighted_sq a b h]

theorem pairEntropyGap_div_variance_lt_ell (a b : ℝ) (h : |a| + |b| < 1) :
    pairEntropyGap a b / (1 - a ^ 2) < ell := by
  have hA := pair_variance_pos a b h
  have hb := pair_abs_lt_variance a b h
  have hprod := mul_pos (show 0 < 1 - a ^ 2 - |b| by linarith)
    (show 0 < 1 - a ^ 2 + |b| by linarith [abs_nonneg b])
  have hsq : b ^ 2 < (1 - a ^ 2) * (1 - a ^ 2) := by nlinarith [sq_abs b]
  have hratio : b ^ 2 / (1 - a ^ 2) < 1 - a ^ 2 := (div_lt_iff₀ hA).2 hsq
  apply (div_lt_iff₀ hA).2
  exact (pairEntropyGap_le_quadratic a b h).trans_lt
    (mul_lt_mul_of_pos_left hratio ell_pos)

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.LambdaScalars ----
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Set Filter

namespace LeanBlast.CourtadeKumar

theorem lambda_of_ne_zero {z : ℝ} (hz : z ≠ 0) :
    lambda z = -Real.log (1 - z) / z := by simp [lambda, hz]

theorem mul_lambda (z : ℝ) : z * lambda z = -Real.log (1 - z) := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [lambda_of_ne_zero hz]
    field_simp

theorem hasSum_lambda {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    HasSum (fun j : ℕ => z ^ j / ((j : ℝ) + 1)) (lambda z) := by
  by_cases hz : z = 0
  · subst z
    rw [lambda_zero]
    convert (hasSum_ite_eq (0 : ℕ) (1 : ℝ)) using 1
    ext j
    by_cases hj : j = 0 <;> simp [hj]
  · have hlog := (Real.hasSum_pow_div_log_of_abs_lt_one
      (show |z| < 1 by rwa [abs_of_nonneg hz0])).div_const z
    rw [lambda_of_ne_zero hz]
    convert! hlog using 1
    ext j
    rw [pow_succ]
    field_simp

theorem monotoneOn_lambda : MonotoneOn lambda (Ico (0 : ℝ) 1) := by
  intro x hx y hy hxy
  apply hasSum_le _ (hasSum_lambda hx.1 hx.2) (hasSum_lambda hy.1 hy.2)
  intro j
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hx.1 hxy j) (by positivity)

theorem one_le_lambda {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) : 1 ≤ lambda z := by
  simpa using monotoneOn_lambda (show (0 : ℝ) ∈ Ico 0 1 by norm_num) ⟨hz0, hz1⟩ hz0

theorem lambda_nonneg {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) : 0 ≤ lambda z :=
  zero_le_one.trans (one_le_lambda hz0 hz1)

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.JensenGaps ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators

universe u

namespace LeanBlast.CourtadeKumar

theorem pow_tangent_remainder_nonneg (n : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ x ^ (n + 1) - y ^ (n + 1) - (n + 1 : ℝ) * y ^ n * (x - y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := add_nonneg (mul_nonneg hx ih)
      (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ n + 1) (pow_nonneg hy n))
        (sq_nonneg (x - y)))
    convert! hp using 1
    push_cast
    simp only [pow_succ]
    ring

theorem pow_tangent_remainder_lower (n : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (n + 1 : ℝ) * y ^ n * (x - y) ^ 2 ≤
      x ^ (n + 2) - y ^ (n + 2) - (n + 2 : ℝ) * y ^ (n + 1) * (x - y) := by
  have hp := mul_nonneg hx (pow_tangent_remainder_nonneg n x y hx hy)
  have hid : x ^ (n + 2) - y ^ (n + 2) - (n + 2 : ℝ) * y ^ (n + 1) * (x - y) =
      x * (x ^ (n + 1) - y ^ (n + 1) - (n + 1 : ℝ) * y ^ n * (x - y)) +
        (n + 1 : ℝ) * y ^ n * (x - y) ^ 2 := by
    simp only [pow_succ]
    ring
  rw [hid]
  linarith

section Weighted

variable {ι : Type u} [Fintype ι]

theorem weighted_centered_second_moment (w x : ι → ℝ) (y : ℝ)
    (hprob : ∑ i, w i = 1) (hmean : ∑ i, w i * x i = y) :
    (∑ i, w i * (x i - y) ^ 2) = (∑ i, w i * (x i) ^ 2) - y ^ 2 := by
  calc
    (∑ i, w i * (x i - y) ^ 2) =
        ∑ i, (w i * (x i) ^ 2 - 2 * y * (w i * x i) + y ^ 2 * w i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, w i * (x i) ^ 2) - 2 * y * (∑ i, w i * x i) + y ^ 2 * (∑ i, w i) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [hprob, hmean]; ring

theorem weighted_pow_gap_lower (w x : ι → ℝ) (y : ℝ) (n : ℕ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hx : ∀ i, 0 ≤ x i) (hy : 0 ≤ y) (hmean : ∑ i, w i * x i = y) :
    (n + 1 : ℝ) * y ^ n * ((∑ i, w i * (x i) ^ 2) - y ^ 2) ≤
      (∑ i, w i * (x i) ^ (n + 2)) - y ^ (n + 2) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (pow_tangent_remainder_lower n (x i) y (hx i) hy) (hw i))
  have hleft : (∑ i, w i * ((n + 1 : ℝ) * y ^ n * (x i - y) ^ 2)) =
      (n + 1 : ℝ) * y ^ n * ((∑ i, w i * (x i) ^ 2) - y ^ 2) := by
    rw [← weighted_centered_second_moment w x y hprob hmean, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hright : (∑ i, w i *
      ((x i) ^ (n + 2) - y ^ (n + 2) - (n + 2 : ℝ) * y ^ (n + 1) * (x i - y))) =
      (∑ i, w i * (x i) ^ (n + 2)) - y ^ (n + 2) := by
    calc
      _ = ∑ i, (w i * (x i) ^ (n + 2) - y ^ (n + 2) * w i -
          (n + 2 : ℝ) * y ^ (n + 1) * (w i * x i - y * w i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, w i * (x i) ^ (n + 2)) - y ^ (n + 2) * (∑ i, w i) -
          (n + 2 : ℝ) * y ^ (n + 1) * ((∑ i, w i * x i) - y * (∑ i, w i)) := by
        simp only [Finset.sum_sub_distrib, mul_sub, Finset.mul_sum]
      _ = _ := by rw [hprob, hmean]; ring
  rwa [hleft, hright] at h

theorem weighted_series_gap_hasSum (c : ℕ → ℝ) (p : ℕ → ℕ) (F : ℝ → ℝ)
    (w x : ι → ℝ) (y : ℝ)
    (hx : ∀ i, HasSum (fun j => c j * (x i) ^ (p j)) (F (x i)))
    (hy : HasSum (fun j => c j * y ^ (p j)) (F y)) :
    HasSum (fun j => 2 * c j * ((∑ i, w i * (x i) ^ (p j)) - y ^ (p j)))
      (2 * ((∑ i, w i * F (x i)) - F y)) := by
  have hsum := hasSum_sum (s := Finset.univ) (fun i _ => (hx i).mul_left (w i))
  have h := (hsum.sub hy).mul_left 2
  have heq : ∀ j, (∑ i, w i * (c j * (x i) ^ (p j))) =
      c j * (∑ i, w i * (x i) ^ (p j)) := by
    intro j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [heq] at h
  convert! h using 1
  ext j
  ring

private theorem entropy_series_gap_strengthened (F : ℝ → ℝ) (w x : ι → ℝ) (y : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1) (hmean : ∑ i, w i * x i = y)
    (hx0 : ∀ i, 0 ≤ x i) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hx : ∀ i, HasSum (fun j => entropySeriesCoeff j * (x i) ^ (2 * (j + 1))) (F (x i)))
    (hy : HasSum (fun j => entropySeriesCoeff j * y ^ (2 * (j + 1))) (F y)) :
    ((∑ i, w i * (x i) ^ 2) - y ^ 2) * lambda (y ^ 2) ≤
      2 * ((∑ i, w i * F (x i)) - F y) := by
  have hsum := weighted_series_gap_hasSum entropySeriesCoeff (fun j => 2 * (j + 1)) F w x y hx hy
  have hlambda := (hasSum_lambda (sq_nonneg y) (by nlinarith : y ^ 2 < 1)).mul_left
    ((∑ i, w i * (x i) ^ 2) - y ^ 2)
  apply hasSum_le _ hlambda hsum
  intro j
  have hp := weighted_pow_gap_lower w x y (2 * j) hw hprob hx0 hy0 hmean
  have hc : 0 ≤ 2 * entropySeriesCoeff j := mul_nonneg (by norm_num) (psiCoeff_nonneg j)
  have h := mul_le_mul_of_nonneg_left hp hc
  have heq : 2 * entropySeriesCoeff j *
      ((2 * j + 1 : ℝ) * y ^ (2 * j) * ((∑ i, w i * (x i) ^ 2) - y ^ 2)) =
      ((∑ i, w i * (x i) ^ 2) - y ^ 2) * ((y ^ 2) ^ j / ((j : ℝ) + 1)) := by
    simp only [entropySeriesCoeff, psiCoeff, pow_mul]
    field_simp
  rw [show 2 * j + 2 = 2 * (j + 1) by omega] at h
  push_cast at h
  rwa [heq] at h

theorem weighted_psi_gap_strengthened (w x : ι → ℝ) (y : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1) (hmean : ∑ i, w i * x i = y)
    (hx : ∀ i, |x i| < 1) (hx0 : ∀ i, 0 ≤ x i) :
    ((∑ i, w i * (x i) ^ 2) - y ^ 2) * lambda (y ^ 2) ≤
      2 * ((∑ i, w i * psi (x i)) - psi y) := by
  have hy : |y| < 1 := by
    apply abs_lt.mpr
    rw [← hmean]
    simpa only [smul_eq_mul, Set.mem_Ioo] using (convex_Ioo (-1 : ℝ) 1).sum_mem
      (fun i _ => hw i) hprob (fun i _ => abs_lt.mp (hx i))
  have hy0 : 0 ≤ y := by
    rw [← hmean]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hx0 i))
  exact entropy_series_gap_strengthened psi w x y hw hprob hmean hx0 hy0
    (abs_lt.mp hy).2 (fun i => hasSum_psi (hx i)) (hasSum_psi hy)

private theorem normalized_ratio_weights_data (w t b : ι → ℝ) (T k : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, 0 < t i) (hT : 0 < T)
    (hmass : ∑ i, w i * t i = T) (hmean : ∑ i, w i * b i = k) :
    (∀ i, 0 ≤ w i * t i / T) ∧ (∑ i, w i * t i / T) = 1 ∧
      (∑ i, (w i * t i / T) * (b i / t i)) = k / T := by
  refine ⟨fun i => div_nonneg (mul_nonneg (hw i) (ht i).le) hT.le, ?_, ?_⟩
  · rw [← Finset.sum_div, hmass, div_self hT.ne']
  · calc
      _ = ∑ i, (w i * b i) / T := by
        apply Finset.sum_congr rfl
        intro i _
        field_simp [(ht i).ne']
      _ = k / T := by rw [← Finset.sum_div, hmean]

private theorem rescale_perspective_gap (w t b : ι → ℝ) (T k C : ℝ)
    (ht : ∀ i, 0 < t i) (hT : 0 < T)
    (hgap : ((∑ i, (w i * t i / T) * (b i / t i) ^ 2) - (k / T) ^ 2) * C ≤
      2 * ((∑ i, (w i * t i / T) * psi (b i / t i)) - psi (k / T))) :
    ((∑ i, w i * (b i) ^ 2 / t i) - k ^ 2 / T) * C ≤
      2 * ((∑ i, w i * t i * psi (b i / t i)) - T * psi (k / T)) := by
  have hsecond : (∑ i, (w i * t i / T) * (b i / t i) ^ 2) =
      (∑ i, w i * (b i) ^ 2 / t i) / T := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(ht i).ne']
  have hentropy : (∑ i, (w i * t i / T) * psi (b i / t i)) =
      (∑ i, w i * t i * psi (b i / t i)) / T := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsecond, hentropy] at hgap
  have h := mul_le_mul_of_nonneg_left hgap hT.le
  convert! h using 1 <;> field_simp

theorem weighted_perspective_gap_strengthened (w t b : ι → ℝ) (T k : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, 0 < t i) (hT : 0 < T)
    (hmass : ∑ i, w i * t i = T) (hmean : ∑ i, w i * b i = k)
    (hdom : ∀ i, |b i| < t i) (hb : ∀ i, 0 ≤ b i) :
    ((∑ i, w i * (b i) ^ 2 / t i) - k ^ 2 / T) * lambda ((k / T) ^ 2) ≤
      2 * ((∑ i, w i * t i * psi (b i / t i)) - T * psi (k / T)) := by
  obtain ⟨hq0, hq1, hqm⟩ := normalized_ratio_weights_data w t b T k hw ht hT hmass hmean
  have hx : ∀ i, |b i / t i| < 1 := by
    intro i
    rw [abs_div, abs_of_pos (ht i)]
    exact (div_lt_one (ht i)).mpr (hdom i)
  have hg := weighted_psi_gap_strengthened (fun i => w i * t i / T) (fun i => b i / t i)
    (k / T) hq0 hq1 hqm hx (fun i => div_nonneg (hb i) (ht i).le)
  exact rescale_perspective_gap w t b T k (lambda ((k / T) ^ 2)) ht hT hg

theorem weighted_abs_mean_le (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    |∑ i, w i * x i| ≤ ∑ i, w i * |x i| := by
  calc
    |∑ i, w i * x i| ≤ ∑ i, |w i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, abs_of_nonneg (hw _)]

theorem weighted_pair_mean_interior (w a b : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hdom : ∀ i, |a i| + |b i| < 1) :
    |∑ i, w i * a i| + |∑ i, w i * b i| < 1 := by
  have havg : (∑ i, w i * (|a i| + |b i|)) < 1 := by
    simpa only [smul_eq_mul, Set.mem_Iio] using (convex_Iio (1 : ℝ)).sum_mem
      (fun i _ => hw i) hprob (fun i _ => hdom i)
  have h := add_le_add (weighted_abs_mean_le w a hw) (weighted_abs_mean_le w b hw)
  rw [← Finset.sum_add_distrib] at h
  simp only [← mul_add] at h
  exact h.trans_lt havg

theorem weighted_positive_mean (w t : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1) (ht : ∀ i, 0 < t i) :
    0 < ∑ i, w i * t i := by
  simpa only [smul_eq_mul, Set.mem_Ioi] using (convex_Ioi (0 : ℝ)).sum_mem
    (fun i _ => hw i) hprob (fun i _ => ht i)

theorem weighted_ratio_centered_identity (w t b : ι → ℝ) (y : ℝ)
    (ht : ∀ i, t i ≠ 0) :
    (∑ i, w i * t i * (b i / t i - y) ^ 2) =
      (∑ i, w i * (b i) ^ 2 / t i) - 2 * y * (∑ i, w i * b i) +
        y ^ 2 * (∑ i, w i * t i) := by
  calc
    _ = ∑ i, (w i * (b i) ^ 2 / t i - 2 * y * (w i * b i) +
        y ^ 2 * (w i * t i)) := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp [ht i]
      ring
    _ = _ := by simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

theorem weighted_ratio_variance_identity (w t b : ι → ℝ) (T k : ℝ)
    (ht : ∀ i, t i ≠ 0) (hT : T ≠ 0)
    (hmass : ∑ i, w i * t i = T) (hmean : ∑ i, w i * b i = k) :
    (∑ i, w i * t i * (b i / t i - k / T) ^ 2) =
      (∑ i, w i * (b i) ^ 2 / t i) - k ^ 2 / T := by
  rw [weighted_ratio_centered_identity w t b _ ht, hmass, hmean]
  field_simp
  ring

theorem weighted_ratio_variance_nonneg (w t b : ι → ℝ) (T k : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, 0 < t i) (hT : 0 < T)
    (hmass : ∑ i, w i * t i = T) (hmean : ∑ i, w i * b i = k) :
    0 ≤ (∑ i, w i * (b i) ^ 2 / t i) - k ^ 2 / T := by
  rw [← weighted_ratio_variance_identity w t b T k (fun i => (ht i).ne') hT.ne'
    hmass hmean]
  exact Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (hw i) (ht i).le) (sq_nonneg _))

theorem weighted_variance_gap_lower_bound (w a b : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hdom : ∀ i, |a i| + |b i| < 1) :
    (∑ i, w i * b i) ^ 2 / (∑ i, w i * (1 - (a i) ^ 2)) -
        (∑ i, w i * b i) ^ 2 / (1 - (∑ i, w i * a i) ^ 2) ≤
      (∑ i, w i * (b i) ^ 2 / (1 - (a i) ^ 2)) -
        (∑ i, w i * b i) ^ 2 / (1 - (∑ i, w i * a i) ^ 2) := by
  have ht : ∀ i, 0 < 1 - (a i) ^ 2 := by
    intro i
    have hi := hdom i
    have hsq := sq_abs (a i)
    nlinarith [abs_nonneg (a i), abs_nonneg (b i)]
  have hT := weighted_positive_mean w (fun i => 1 - (a i) ^ 2) hw hprob ht
  have h := weighted_ratio_variance_nonneg w (fun i => 1 - (a i) ^ 2) b _ _
    hw ht hT rfl rfl
  linarith

private theorem pair_reciprocal_square_identity (a b : ℝ) (h : |a| + |b| < 1) :
    b ^ 2 / (1 + a) + b ^ 2 / (1 - a) = 2 * (b ^ 2 / (1 - a ^ 2)) := by
  have hp := (pair_denom_add_pos a b h).ne'
  have hm := (pair_denom_sub_pos a b h).ne'
  have hv := (pair_variance_pos a b h).ne'
  field_simp
  ring

private theorem weighted_pair_gap_combine (w a b : ι → ℝ) (m k C : ℝ)
    (hdom : ∀ i, |a i| + |b i| < 1) (hcenter : |m| + |k| < 1)
    (hp : ((∑ i, w i * (b i) ^ 2 / (1 + a i)) - k ^ 2 / (1 + m)) * C ≤
      2 * ((∑ i, w i * (1 + a i) * psi (b i / (1 + a i))) -
        (1 + m) * psi (k / (1 + m))))
    (hm : ((∑ i, w i * (b i) ^ 2 / (1 - a i)) - k ^ 2 / (1 - m)) * C ≤
      2 * ((∑ i, w i * (1 - a i) * psi (b i / (1 - a i))) -
        (1 - m) * psi (k / (1 - m)))) :
    ((∑ i, w i * (b i) ^ 2 / (1 - (a i) ^ 2)) - k ^ 2 / (1 - m ^ 2)) * C ≤
      2 * ((∑ i, w i * pairEntropyGap (a i) (b i)) - pairEntropyGap m k) := by
  have hv : (∑ i, w i * (b i) ^ 2 / (1 + a i)) +
      (∑ i, w i * (b i) ^ 2 / (1 - a i)) =
      2 * (∑ i, w i * (b i) ^ 2 / (1 - (a i) ^ 2)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = w i * ((b i) ^ 2 / (1 + a i) + (b i) ^ 2 / (1 - a i)) := by ring
      _ = _ := by rw [pair_reciprocal_square_identity (a i) (b i) (hdom i)]; ring
  have hvc := pair_reciprocal_square_identity m k hcenter
  have he : (∑ i, w i * (1 + a i) * psi (b i / (1 + a i))) +
      (∑ i, w i * (1 - a i) * psi (b i / (1 - a i))) =
      2 * (∑ i, w i * pairEntropyGap (a i) (b i)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pairEntropyGap_weighted (a i) (b i) (hdom i)]
    ring
  have hec : (1 + m) * psi (k / (1 + m)) + (1 - m) * psi (k / (1 - m)) =
      2 * pairEntropyGap m k := by
    rw [pairEntropyGap_weighted m k hcenter]
    ring
  have hvC := congrArg (fun z : ℝ => z * C) hv
  have hvcC := congrArg (fun z : ℝ => z * C) hvc
  nlinarith only [hp, hm, hvC, hvcC, he, hec]

private theorem lambda_ratio_min_le (m k t : ℝ) (hk : 0 ≤ k)
    (ht : 0 < t) (htmax : t ≤ 1 + |m|) (hkt : k < t) :
    lambda ((k / (1 + |m|)) ^ 2) ≤ lambda ((k / t) ^ 2) := by
  have hmax : 0 < 1 + |m| := by positivity
  have hx : 0 ≤ k / (1 + |m|) := div_nonneg hk hmax.le
  have hy : 0 ≤ k / t := div_nonneg hk ht.le
  have hxy := div_le_div_of_nonneg_left hk ht htmax
  have hy1 : k / t < 1 := (div_lt_one ht).mpr hkt
  apply monotoneOn_lambda
  · exact ⟨sq_nonneg _, by nlinarith⟩
  · exact ⟨sq_nonneg _, by nlinarith⟩
  · exact pow_le_pow_left₀ hx hxy 2

theorem weighted_pair_jensen_gap_strengthened (w a b : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hdom : ∀ i, |a i| + |b i| < 1) (hb : ∀ i, 0 ≤ b i) :
    ((∑ i, w i * (b i) ^ 2 / (1 - (a i) ^ 2)) -
      (∑ i, w i * b i) ^ 2 / (1 - (∑ i, w i * a i) ^ 2)) *
        lambda (((∑ i, w i * b i) / (1 + |∑ i, w i * a i|)) ^ 2) ≤
      2 * ((∑ i, w i * pairEntropyGap (a i) (b i)) -
        pairEntropyGap (∑ i, w i * a i) (∑ i, w i * b i)) := by
  let m := ∑ i, w i * a i
  let k := ∑ i, w i * b i
  have hc : |m| + |k| < 1 := weighted_pair_mean_interior w a b hw hprob hdom
  have hk : 0 ≤ k := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hb i))
  have htp := pair_denom_add_pos m k hc
  have htm := pair_denom_sub_pos m k hc
  have hp0 : ∀ i, 0 < 1 + a i := fun i => pair_denom_add_pos (a i) (b i) (hdom i)
  have hm0 : ∀ i, 0 < 1 - a i := fun i => pair_denom_sub_pos (a i) (b i) (hdom i)
  have hmp : (∑ i, w i * (1 + a i)) = 1 + m := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib, hprob, m]
  have hmm : (∑ i, w i * (1 - a i)) = 1 - m := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hprob, m]
  have hp := weighted_perspective_gap_strengthened w (fun i => 1 + a i) b (1 + m) k
    hw hp0 htp hmp rfl (fun i => pair_abs_lt_denom_add (a i) (b i) (hdom i)) hb
  have hm := weighted_perspective_gap_strengthened w (fun i => 1 - a i) b (1 - m) k
    hw hm0 htm hmm rfl (fun i => pair_abs_lt_denom_sub (a i) (b i) (hdom i)) hb
  have hvp := weighted_ratio_variance_nonneg w (fun i => 1 + a i) b (1 + m) k
    hw hp0 htp hmp rfl
  have hvm := weighted_ratio_variance_nonneg w (fun i => 1 - a i) b (1 - m) k
    hw hm0 htm hmm rfl
  have hcp := lambda_ratio_min_le m k (1 + m) hk htp (by linarith [le_abs_self m])
    (by simpa only [abs_of_nonneg hk] using pair_abs_lt_denom_add m k hc)
  have hcm := lambda_ratio_min_le m k (1 - m) hk htm (by linarith [neg_le_abs m])
    (by simpa only [abs_of_nonneg hk] using pair_abs_lt_denom_sub m k hc)
  exact weighted_pair_gap_combine w a b m k _ hdom hc
    ((mul_le_mul_of_nonneg_left hcp hvp).trans hp)
    ((mul_le_mul_of_nonneg_left hcm hvm).trans hm)

end Weighted

private theorem cube_uniform_weights_sum_one (n : ℕ) :
    ∑ _ : Cube n, ((2 : ℝ) ^ n)⁻¹ = 1 := by
  simp [Cube, LeanBlast.GotsmanLinial.Cube]

private theorem cubeAverage_as_weighted_sum {n : ℕ} (f : Cube n → ℝ) :
    cubeAverage f = ∑ x, ((2 : ℝ) ^ n)⁻¹ * f x := by
  rw [cubeAverage, ← Finset.mul_sum]
  ring

theorem pair_variance_gap_lower_bound {n : ℕ} (a b : Cube n → ℝ)
    (hdom : ∀ x, |a x| + |b x| < 1) :
    (cubeAverage b) ^ 2 / cubeAverage (fun x => 1 - (a x) ^ 2) -
        (cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2) ≤
      cubeAverage (fun x => (b x) ^ 2 / (1 - (a x) ^ 2)) -
        (cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2) := by
  simpa only [cubeAverage_as_weighted_sum, ← mul_div_assoc] using
    weighted_variance_gap_lower_bound (fun _ => ((2 : ℝ) ^ n)⁻¹) a b
      (fun _ => by positivity) (cube_uniform_weights_sum_one n) hdom

theorem pair_jensen_gap_strengthened {n : ℕ} (a b : Cube n → ℝ)
    (hdom : ∀ x, |a x| + |b x| < 1) (hb : ∀ x, 0 ≤ b x) :
    (cubeAverage (fun x => (b x) ^ 2 / (1 - (a x) ^ 2)) -
      (cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2)) *
        lambda (((cubeAverage b) / (1 + |cubeAverage a|)) ^ 2) ≤
      2 * (cubeAverage (fun x => pairEntropyGap (a x) (b x)) -
        pairEntropyGap (cubeAverage a) (cubeAverage b)) := by
  simpa only [cubeAverage_as_weighted_sum, ← mul_div_assoc] using
    weighted_pair_jensen_gap_strengthened (fun _ => ((2 : ℝ) ^ n)⁻¹) a b
      (fun _ => by positivity) (cube_uniform_weights_sum_one n) hdom hb

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.CubeVariance ----
namespace OAI

open scoped BigOperators

noncomputable section

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem binaryRelativeEntropy_eq {a m : ℝ}
    (ha : -1 < a ∧ a < 1) (hm : -1 < m ∧ m < 1) :
    binaryRelativeEntropy a m = psi a - psi m -
      (a - m) / 2 * (Real.log (1 + m) - Real.log (1 - m)) := by
  have hap : 1 + a ≠ 0 := ne_of_gt (by linarith)
  have ham : 1 - a ≠ 0 := ne_of_gt (by linarith)
  have hmp : 1 + m ≠ 0 := ne_of_gt (by linarith)
  have hmm : 1 - m ≠ 0 := ne_of_gt (by linarith)
  unfold binaryRelativeEntropy psi
  rw [Real.log_div hap hmp, Real.log_div ham hmm]
  ring

theorem sub_le_mul_log_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a - b ≤ a * Real.log (a / b) := by
  have h := mul_le_mul_of_nonneg_left
    (Real.one_sub_inv_le_log_of_pos (div_pos ha hb)) ha.le
  have heq : a * (1 - (a / b)⁻¹) = a - b := by
    field_simp
  rwa [heq] at h

theorem binaryRelativeEntropy_nonneg {a m : ℝ}
    (ha : -1 < a ∧ a < 1) (hm : -1 < m ∧ m < 1) :
    0 ≤ binaryRelativeEntropy a m := by
  have hp := sub_le_mul_log_div (a := 1 + a) (b := 1 + m)
    (by linarith) (by linarith)
  have hm' := sub_le_mul_log_div (a := 1 - a) (b := 1 - m)
    (by linarith) (by linarith)
  unfold binaryRelativeEntropy
  nlinarith

theorem informationDeficit_eq_average_psi (g : Cube n → ℝ) :
    informationDeficit g = cubeAverage (fun x => psi (g x)) - psi (cubeAverage g) := by
  unfold informationDeficit entropyAverage entropy
  rw [cubeAverage_sub, cubeAverage_const]
  ring

theorem informationDeficit_eq_average_binaryRelativeEntropy
    {g : Cube n → ℝ} (hg : IsInterior g) :
    informationDeficit g =
      cubeAverage (fun x => binaryRelativeEntropy (g x) (cubeAverage g)) := by
  let m := cubeAverage g
  let c := Real.log (1 + m) - Real.log (1 - m)
  have hlin : cubeAverage (fun x => (g x - m) / 2 * c) = 0 := by
    have heq : (fun x => (g x - m) / 2 * c) = (fun x => (c / 2) * (g x - m)) := by
      funext x
      ring
    rw [heq, cubeAverage_smul, cubeAverage_sub, cubeAverage_const]
    dsimp [m]
    ring
  have heq : (fun x => binaryRelativeEntropy (g x) m) =
      (fun x => psi (g x) - psi m - (g x - m) / 2 * c) := by
    funext x
    exact binaryRelativeEntropy_eq (hg x) hg.cubeAverage
  rw [show (fun x => binaryRelativeEntropy (g x) (cubeAverage g)) =
      (fun x => binaryRelativeEntropy (g x) m) from rfl, heq]
  rw [cubeAverage_sub, cubeAverage_sub, cubeAverage_const, hlin, sub_zero]
  exact informationDeficit_eq_average_psi g

theorem informationDeficit_nonneg {g : Cube n → ℝ} (hg : IsInterior g) :
    0 ≤ informationDeficit g := by
  rw [informationDeficit_eq_average_binaryRelativeEntropy hg]
  exact cubeAverage_nonneg fun x => binaryRelativeEntropy_nonneg (hg x) hg.cubeAverage

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.PerspectiveJensen ----
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Set Filter

universe u

namespace LeanBlast.CourtadeKumar

theorem weighted_perspective_jensen {ι : Type u} [Fintype ι]
    (f : ℝ → ℝ) (hf : ConvexOn ℝ (Ioi 0) f)
    (p A H : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hA : ∀ i, 0 < A i)
    (hH : ∀ i, 0 < H i) (hS : 0 < ∑ i, p i * A i) :
    (∑ i, p i * A i) * f ((∑ i, p i * H i) / (∑ i, p i * A i)) ≤
      ∑ i, p i * A i * f (H i / A i) := by
  have hj := hf.map_centerMass_le
    (t := Finset.univ) (w := fun i => p i * A i) (p := fun i => H i / A i)
    (fun i _ => mul_nonneg (hp i) (hA i).le) hS (fun i _ => div_pos (hH i) (hA i))
  have heq : (∑ i, p i * A i * (H i / A i)) = ∑ i, p i * H i := by
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(hA i).ne']
  simp only [Finset.centerMass, smul_eq_mul, Function.comp_apply] at hj
  rw [heq] at hj
  have hm := mul_le_mul_of_nonneg_left hj hS.le
  simp only [← mul_assoc, mul_inv_cancel₀ hS.ne', one_mul] at hm
  simpa [← div_eq_inv_mul, mul_assoc] using hm

theorem cubeAverage_perspective_jensen {n : ℕ}
    (f : ℝ → ℝ) (hf : ConvexOn ℝ (Ioi 0) f)
    (A H : Cube n → ℝ) (hA : ∀ i, 0 < A i) (hH : ∀ i, 0 < H i) :
    cubeAverage A * f (cubeAverage H / cubeAverage A) ≤
      cubeAverage (fun i => A i * f (H i / A i)) := by
  have hc : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hs : 0 < ∑ i, ((2 : ℝ) ^ n)⁻¹ * A i :=
    Finset.sum_pos (fun i _ => mul_pos (inv_pos.mpr hc) (hA i)) Finset.univ_nonempty
  have h := weighted_perspective_jensen f hf (fun _ => ((2 : ℝ) ^ n)⁻¹)
    A H (fun _ => (inv_pos.mpr hc).le) hA hH hs
  have havg (g : Cube n → ℝ) :
      (∑ i, ((2 : ℝ) ^ n)⁻¹ * g i) = cubeAverage g := by
    rw [← Finset.mul_sum, cubeAverage, div_eq_mul_inv]
    ring
  simpa only [mul_assoc, havg] using h

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.NormalizedPair ----
namespace OAI

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

theorem hasSum_weighted_nonneg_of_single_crossing
    {x weight : ℕ → ℝ} {total : ℝ}
    (hs : HasSum x 0) (hws : HasSum (fun j => weight j * x j) total)
    (hw : Monotone weight)
    (hcross : ∀ i j, i ≤ j → 0 < x i → 0 ≤ x j) : 0 ≤ total := by
  classical
  by_cases hpos : ∃ j, 0 < x j
  · let k := Nat.find hpos
    have hk : 0 < x k := Nat.find_spec hpos
    have hbefore : ∀ j, j < k → x j ≤ 0 := by
      intro j hj
      exact le_of_not_gt (Nat.find_min hpos hj)
    have hafter : ∀ j, k ≤ j → 0 ≤ x j := fun j hj => hcross k j hj hk
    have hshift : HasSum (fun j => (weight j - weight k) * x j) total := by
      convert! hws.sub (hs.mul_left (weight k)) using 1
      · ext j
        ring
      · ring
    apply hshift.nonneg
    intro j
    by_cases hj : j < k
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hw hj.le)) (hbefore j hj)
    · exact mul_nonneg (sub_nonneg.mpr (hw (le_of_not_gt hj)))
        (hafter j (le_of_not_gt hj))
  · have hx : ∀ j, x j ≤ 0 := fun j => le_of_not_gt (fun hj => hpos ⟨j, hj⟩)
    have hzero : ∀ j, x j = 0 := by
      intro j
      have hle : -x j ≤ (0 : ℝ) := by
        simpa using le_hasSum hs.neg j (fun i _ => neg_nonneg.mpr (hx i))
      linarith [hx j]
    exact hws.nonneg (fun j => by rw [hzero j]; simp)

theorem logconvex_single_crossing {z : ℕ → ℝ}
    (hz : ∀ j, 0 ≤ z j) (hz0 : z 0 ≤ 1)
    (hlog : ∀ j, z (j + 1) ^ 2 ≤ z j * z (j + 2))
    (i j : ℕ) (hij : i ≤ j) (hi : 1 < z i) : 1 < z j := by
  have hprevious : ∀ n, 1 < z (n + 1) → z n ≤ z (n + 1) := by
    intro n
    induction n with
    | zero =>
      intro h
      exact hz0.trans h.le
    | succ n ih =>
      intro h
      change 1 < z (n + 2) at h
      change z (n + 1) ≤ z (n + 2)
      by_contra hnot
      have hdesc : z (n + 2) < z (n + 1) := lt_of_not_ge hnot
      have hprev := ih (h.trans hdesc)
      have hmul := mul_le_mul_of_nonneg_right hprev (hz (n + 2))
      have hsq := hlog n
      nlinarith
  have hnext : ∀ n, 1 < z n → 1 < z (n + 1) := by
    intro n hn
    cases n with
    | zero => exact (not_lt_of_ge hz0 hn).elim
    | succ n =>
      have hprev := hprevious n hn
      have hmul := mul_le_mul_of_nonneg_right hprev (hz (n + 2))
      have hsq := hlog n
      change 1 < z (n + 2)
      nlinarith
  exact Nat.le_induction hi (fun n _ hn => hnext n hn) j hij

theorem logconvex_mul_pow {m : ℕ → ℝ}
    (hlog : ∀ j, m (j + 1) ^ 2 ≤ m j * m (j + 2)) (c : ℝ) (j : ℕ) :
    (m (j + 1) * c ^ (j + 1)) ^ 2 ≤
      (m j * c ^ j) * (m (j + 2) * c ^ (j + 2)) := by
  calc
    (m (j + 1) * c ^ (j + 1)) ^ 2 =
        m (j + 1) ^ 2 * (c ^ (j + 1)) ^ 2 := mul_pow _ _ _
    _ ≤ (m j * m (j + 2)) * (c ^ (j + 1)) ^ 2 :=
      mul_le_mul_of_nonneg_right (hlog j) (sq_nonneg _)
    _ = (m j * c ^ j) * (m (j + 2) * c ^ (j + 2)) := by
      simp only [pow_add, pow_one, pow_two]
      ring

theorem logconvex_geometric_single_crossing {m : ℕ → ℝ}
    (hm : ∀ j, 0 ≤ m j) (hm0 : m 0 ≤ 1)
    (hlog : ∀ j, m (j + 1) ^ 2 ≤ m j * m (j + 2))
    {t : ℝ} (ht : 0 ≤ t) (i j : ℕ) (hij : i ≤ j)
    (hi : t ^ i < m i) : t ^ j < m j := by
  by_cases ht0 : t = 0
  · subst t
    by_cases hi0 : i = 0
    · subst i
      simp only [pow_zero] at hi
      exact (not_lt_of_ge hm0 hi).elim
    · have hmi : 0 < m i := by simpa [zero_pow hi0] using hi
      have hpositive : ∀ n, 0 < m (n + 1) → 0 < m (n + 2) := by
        intro n hn
        have hsq := hlog n
        have hm0 := hm n
        have hm2 := hm (n + 2)
        nlinarith
      have htail : ∀ k, i ≤ k → 0 < m k := by
        intro k hk
        induction k, hk using Nat.le_induction with
        | base => exact hmi
        | succ k hk ih =>
          obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          exact hpositive l ih
      have hj0 : j ≠ 0 := by omega
      simpa [zero_pow hj0] using htail j hij
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hzi : 1 < m i * (t⁻¹) ^ i := by
      rw [inv_pow, ← div_eq_mul_inv]
      exact (lt_div_iff₀ (pow_pos htpos i)).mpr (by simpa using hi)
    have hzj := logconvex_single_crossing
      (z := fun k => m k * (t⁻¹) ^ k)
      (fun k => mul_nonneg (hm k) (pow_nonneg (inv_nonneg.mpr ht) k))
      (by simpa using hm0) (logconvex_mul_pow hlog (t⁻¹)) i j hij hzi
    change 1 < m j * (t⁻¹) ^ j at hzj
    rw [inv_pow, ← div_eq_mul_inv] at hzj
    simpa only [one_mul] using (lt_div_iff₀ (pow_pos htpos j)).mp hzj

theorem weighted_hasSum_le_of_logconvex
    {m c weight : ℕ → ℝ} {t mass moment geometricMoment : ℝ}
    (hm : ∀ j, 0 ≤ m j) (hm0 : m 0 ≤ 1)
    (hlog : ∀ j, m (j + 1) ^ 2 ≤ m j * m (j + 2))
    (hc : ∀ j, 0 ≤ c j) (hw : Monotone weight) (ht : 0 ≤ t)
    (hs : HasSum (fun k => c k * m (k + 1)) mass)
    (hts : HasSum (fun k => c k * t ^ (k + 1)) mass)
    (hws : HasSum (fun k => weight k * (c k * m (k + 1))) moment)
    (hwts : HasSum (fun k => weight k * (c k * t ^ (k + 1))) geometricMoment) :
    geometricMoment ≤ moment := by
  have hdiff : HasSum (fun k => c k * (m (k + 1) - t ^ (k + 1))) 0 := by
    convert! hs.sub hts using 1
    · ext k
      ring
    · ring
  have hwdiff : HasSum
      (fun k => weight k * (c k * (m (k + 1) - t ^ (k + 1))))
      (moment - geometricMoment) := by
    convert! hws.sub hwts using 1
    ext k
    ring
  have hnonneg := hasSum_weighted_nonneg_of_single_crossing hdiff hwdiff hw ?_
  · linarith
  · intro i j hij hi
    have hmi : t ^ (i + 1) < m (i + 1) := by
      have hci := hc i
      nlinarith
    have hmj := logconvex_geometric_single_crossing hm hm0 hlog ht
      (i + 1) (j + 1) (Nat.add_le_add_right hij 1) hmi
    exact mul_nonneg (hc j) (sub_nonneg.mpr hmj.le)

theorem normalized_pair_scale_pos {a b : ℝ} (hab : |a| + |b| < 1) : 0 < 1 - a ^ 2 := by
  have h := mul_pos (pair_denom_add_pos a b hab) (pair_denom_sub_pos a b hab)
  nlinarith

theorem two_atom_moment_logconvex (w u p q : ℝ)
    (hw : 0 ≤ w) (hu : 0 ≤ u) (hp : 0 ≤ p) (hq : 0 ≤ q) (j : ℕ) :
    (w * p ^ (j + 1) + u * q ^ (j + 1)) ^ 2 ≤
      (w * p ^ j + u * q ^ j) * (w * p ^ (j + 2) + u * q ^ (j + 2)) := by
  have hnonneg : 0 ≤ w * u * p ^ j * q ^ j * (p - q) ^ 2 := by positivity
  have heq :
      (w * p ^ j + u * q ^ j) * (w * p ^ (j + 2) + u * q ^ (j + 2)) -
          (w * p ^ (j + 1) + u * q ^ (j + 1)) ^ 2 =
        w * u * p ^ j * q ^ j * (p - q) ^ 2 := by
    simp only [pow_add, pow_one, pow_two]
    ring
  linarith

theorem rawPairMoment_logconvex {a b : ℝ} (hab : |a| + |b| < 1) (j : ℕ) :
    rawPairMoment a b (j + 1) ^ 2 ≤
      rawPairMoment a b j * rawPairMoment a b (j + 2) := by
  simpa only [rawPairMoment, ← pow_mul] using
    two_atom_moment_logconvex ((1 + a) / 2) ((1 - a) / 2)
      ((b / (1 + a)) ^ 2) ((b / (1 - a)) ^ 2)
      (le_of_lt (div_pos (pair_denom_add_pos a b hab) (by norm_num)))
      (le_of_lt (div_pos (pair_denom_sub_pos a b hab) (by norm_num)))
      (sq_nonneg _) (sq_nonneg _) j

theorem normalizedPairMoment_nonneg {a b : ℝ} (hab : |a| + |b| < 1) (j : ℕ) :
    0 ≤ normalizedPairMoment a b j := by
  unfold normalizedPairMoment
  split_ifs with hj
  · norm_num
  · apply div_nonneg _ (normalized_pair_scale_pos hab).le
    unfold rawPairMoment
    apply add_nonneg
    · apply mul_nonneg (by linarith [pair_denom_add_pos a b hab])
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) j
    · apply mul_nonneg (by linarith [pair_denom_sub_pos a b hab])
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) j

theorem normalizedPairMoment_one {a b : ℝ} (hab : |a| + |b| < 1) :
    normalizedPairMoment a b 1 = b ^ 2 / (1 - a ^ 2) ^ 2 := by
  have hp := ne_of_gt (pair_denom_add_pos a b hab)
  have hm := ne_of_gt (pair_denom_sub_pos a b hab)
  have hA := ne_of_gt (normalized_pair_scale_pos hab)
  norm_num [normalizedPairMoment, rawPairMoment]
  field_simp
  ring

theorem normalizedPairMoment_two {a b : ℝ} (hab : |a| + |b| < 1) :
    normalizedPairMoment a b 2 = b ^ 4 * (1 + 3 * a ^ 2) / (1 - a ^ 2) ^ 4 := by
  have hp := ne_of_gt (pair_denom_add_pos a b hab)
  have hm := ne_of_gt (pair_denom_sub_pos a b hab)
  have hA := ne_of_gt (normalized_pair_scale_pos hab)
  norm_num [normalizedPairMoment, rawPairMoment]
  field_simp
  ring

theorem normalizedPairMoment_logconvex {a b : ℝ} (hab : |a| + |b| < 1) (j : ℕ) :
    normalizedPairMoment a b (j + 1) ^ 2 ≤
      normalizedPairMoment a b j * normalizedPairMoment a b (j + 2) := by
  cases j with
  | zero =>
    rw [normalizedPairMoment_zero, one_mul, normalizedPairMoment_one hab,
      normalizedPairMoment_two hab]
    calc
      (b ^ 2 / (1 - a ^ 2) ^ 2) ^ 2 = b ^ 4 / (1 - a ^ 2) ^ 4 := by
        rw [div_pow, ← pow_mul, ← pow_mul]
      _ ≤ b ^ 4 * (1 + 3 * a ^ 2) / (1 - a ^ 2) ^ 4 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [show 0 ≤ 3 * a ^ 2 * b ^ 4 by positivity]
  | succ j =>
    change (rawPairMoment a b (j + 2) / (1 - a ^ 2)) ^ 2 ≤
      (rawPairMoment a b (j + 1) / (1 - a ^ 2)) *
        (rawPairMoment a b (j + 3) / (1 - a ^ 2))
    rw [div_pow, div_mul_div_comm, ← pow_two (1 - a ^ 2)]
    exact div_le_div_of_nonneg_right (rawPairMoment_logconvex hab (j + 1))
      (sq_nonneg (1 - a ^ 2))

theorem hasSum_normalizedPairEntropy {a b : ℝ} (hab : |a| + |b| < 1) :
    HasSum (fun k => psiCoeff k * normalizedPairMoment a b (k + 1))
      (pairEntropyGap a b / (1 - a ^ 2)) := by
  have hp := hasSum_psi (abs_lt.mpr (pair_ratio_add_mem_Ioo a b hab))
  have hm := hasSum_psi (abs_lt.mpr (pair_ratio_sub_mem_Ioo a b hab))
  have hs := ((hp.mul_left ((1 + a) / 2)).add
    (hm.mul_left ((1 - a) / 2))).div_const (1 - a ^ 2)
  convert! hs using 1
  · ext k
    rw [normalizedPairMoment_succ]
    unfold rawPairMoment
    ring
  · rw [pairEntropyGap_weighted a b hab]

theorem hasSum_normalizedPairDissipation {a b : ℝ} (hab : |a| + |b| < 1) :
    HasSum (fun k : ℕ => (2 * ((k : ℝ) + 1)) *
      (psiCoeff k * normalizedPairMoment a b (k + 1)))
      (pairDissipation a b / (1 - a ^ 2)) := by
  have hp := hasSum_mul_artanh (abs_lt.mpr (pair_ratio_add_mem_Ioo a b hab))
  have hm := hasSum_mul_artanh (abs_lt.mpr (pair_ratio_sub_mem_Ioo a b hab))
  have hs := ((hp.mul_left ((1 + a) / 2)).add
    (hm.mul_left ((1 - a) / 2))).div_const (1 - a ^ 2)
  convert! hs using 1
  · ext k
    rw [normalizedPairMoment_succ]
    unfold rawPairMoment
    ring
  · rw [pairDissipation_weighted a b hab]

theorem normalized_pair_dissipation_ge_of_psi {a b v : ℝ}
    (hab : |a| + |b| < 1) (hv : |v| < 1)
    (hvpsi : psi v = pairEntropyGap a b / (1 - a ^ 2)) :
    v * Real.artanh v ≤ pairDissipation a b / (1 - a ^ 2) := by
  apply weighted_hasSum_le_of_logconvex
    (m := normalizedPairMoment a b) (c := psiCoeff)
    (weight := fun k => 2 * ((k : ℝ) + 1)) (t := v ^ 2)
    (normalizedPairMoment_nonneg hab)
    (by simp) (normalizedPairMoment_logconvex hab) psiCoeff_nonneg
  · intro i j hij
    have hcast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    dsimp
    linarith
  · exact sq_nonneg v
  · exact hasSum_normalizedPairEntropy hab
  · simpa only [← pow_mul, hvpsi] using hasSum_psi hv
  · exact hasSum_normalizedPairDissipation hab
  · simpa only [← pow_mul, mul_assoc] using hasSum_mul_artanh hv

theorem normalized_pair_dissipation_ge_r {a b : ℝ} (hab : |a| + |b| < 1) :
    r (pairEntropyGap a b / (1 - a ^ 2)) ≤ pairDissipation a b / (1 - a ^ 2) := by
  have hs0 := pairEntropyGap_div_variance_nonneg a b hab
  have hs1 := pairEntropyGap_div_variance_lt_ell a b hab
  have hv := psiInv_mem_Ico hs0 hs1
  exact normalized_pair_dissipation_ge_of_psi hab
    (by simpa only [abs_of_nonneg hv.1] using hv.2) (psi_psiInv hs0 hs1)

private theorem normalized_pair_bound_of_antitone
    (hanti : AntitoneOn L (Set.Ioi 0)) {a b : ℝ} (hab : |a| + |b| < 1) :
    (1 - a ^ 2) *
        L (((entropy (a + b) + entropy (a - b)) / 2) / (1 - a ^ 2)) ≤
      pairDissipation a b - 2 * pairEntropyGap a b := by
  have hA := normalized_pair_scale_pos hab
  have hs0 := pairEntropyGap_div_variance_nonneg a b hab
  have hs1 := pairEntropyGap_div_variance_lt_ell a b hab
  have hlow : 0 < ell - pairEntropyGap a b / (1 - a ^ 2) := sub_pos.mpr hs1
  have ha : |a| ≤ 1 :=
    (lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg b)) hab).le
  have hH := ell_mul_one_sub_sq_le_entropy ha
  have hratio : ell - pairEntropyGap a b / (1 - a ^ 2) ≤
      ((entropy (a + b) + entropy (a - b)) / 2) / (1 - a ^ 2) := by
    apply (le_div_iff₀ hA).mpr
    calc
      (ell - pairEntropyGap a b / (1 - a ^ 2)) * (1 - a ^ 2) =
          ell * (1 - a ^ 2) - pairEntropyGap a b := by
        field_simp
      _ ≤ entropy a - pairEntropyGap a b := sub_le_sub_right hH _
      _ = (entropy (a + b) + entropy (a - b)) / 2 := by
        unfold pairEntropyGap
        ring
  have hL := hanti hlow (hlow.trans_le hratio) hratio
  rw [L_ell_sub hs0 hs1] at hL
  have hr := normalized_pair_dissipation_ge_r hab
  have hbound :
      L (((entropy (a + b) + entropy (a - b)) / 2) / (1 - a ^ 2)) ≤
        (pairDissipation a b - 2 * pairEntropyGap a b) / (1 - a ^ 2) := by
    calc
      _ ≤ r (pairEntropyGap a b / (1 - a ^ 2)) -
          2 * (pairEntropyGap a b / (1 - a ^ 2)) := hL
      _ ≤ pairDissipation a b / (1 - a ^ 2) -
          2 * (pairEntropyGap a b / (1 - a ^ 2)) := sub_le_sub_right hr _
      _ = _ := by ring
  simpa only [mul_comm] using (le_div_iff₀ hA).mp hbound

theorem normalized_pair_bound {a b : ℝ} (hab : |a| + |b| < 1) :
    (1 - a ^ 2) *
        L (((entropy (a + b) + entropy (a - b)) / 2) / (1 - a ^ 2)) ≤
      pairDissipation a b - 2 * pairEntropyGap a b :=
  normalized_pair_bound_of_antitone antitoneOn_L hab

end LeanBlast.CourtadeKumar

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.PerspectiveLogTrapezoid ----
namespace OAI

noncomputable section

namespace LeanBlast.CourtadeKumar

private theorem hasDerivAt_trapezoidGap (q w : ℝ) (hw0 : 0 < w) (hqw : q < w) :
    HasDerivAt (trapezoidGap q) (trapezoidGapDeriv q w) w := by
  have ha := ((hasDerivAt_id w).const_add (1 : ℝ)).sub_const (2 * q)
  have hb := HasDerivAt.const_sub (Real.log (1 - q))
    (((hasDerivAt_id w).sub_const q).log (ne_of_gt (sub_pos.mpr hqw)))
  have hc := ((hasDerivAt_id w).const_add (1 : ℝ)).mul
    (Real.hasDerivAt_log (ne_of_gt hw0))
  convert! (ha.mul hb).add hc using 1
  dsimp [trapezoidGap, trapezoidGapDeriv]
  ring

private theorem trapezoidGapDeriv_nonpos (q w : ℝ)
    (hq0 : 0 ≤ q) (hqw : q < w) (hw1 : w ≤ 1) : trapezoidGapDeriv q w ≤ 0 := by
  have hw0 : 0 < w := lt_of_le_of_lt hq0 hqw
  have hd : 0 < w - q := sub_pos.mpr hqw
  have hq1 : q < 1 := lt_of_lt_of_le hqw hw1
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  let r : ℝ := (1 - q) * w / (w - q)
  have hr : 0 < r := div_pos (mul_pos h1q hw0) hd
  have hlog := Real.log_le_sub_one_of_pos hr
  have hlogeq : Real.log r = Real.log (1 - q) + Real.log w - Real.log (w - q) := by
    dsimp [r]
    rw [Real.log_div (ne_of_gt (mul_pos h1q hw0)) (ne_of_gt hd),
      Real.log_mul (ne_of_gt h1q) (ne_of_gt hw0)]
  rw [hlogeq] at hlog
  have hrem : r - 1 + (1 + w) / w - (1 + w - 2 * q) / (w - q) =
      -q * (1 - w) ^ 2 / (w * (w - q)) := by
    dsimp [r]
    field_simp [ne_of_gt hw0, ne_of_gt hd]
    ring
  have hrest : r - 1 + (1 + w) / w - (1 + w - 2 * q) / (w - q) ≤ 0 := by
    rw [hrem]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq0) (sq_nonneg _))
      (mul_nonneg hw0.le hd.le)
  unfold trapezoidGapDeriv
  linarith

private theorem trapezoidGap_nonneg (q w : ℝ)
    (hq0 : 0 ≤ q) (hqw : q < w) (hw1 : w ≤ 1) : 0 ≤ trapezoidGap q w := by
  have hw0 : 0 < w := lt_of_le_of_lt hq0 hqw
  have hd (v : ℝ) (hv : v ∈ Set.Icc w 1) :
      HasDerivAt (trapezoidGap q) (trapezoidGapDeriv q v) v :=
    hasDerivAt_trapezoidGap q v (lt_of_lt_of_le hw0 hv.1) (lt_of_lt_of_le hqw hv.1)
  have hanti : AntitoneOn (trapezoidGap q) (Set.Icc w 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc w 1)
    · intro v hv
      exact (hd v hv).continuousAt.continuousWithinAt
    · intro v hv
      exact (hd v (interior_subset hv)).differentiableAt.differentiableWithinAt
    · intro v hv
      have hvm : v ∈ Set.Icc w 1 := interior_subset hv
      rw [(hd v hvm).deriv]
      exact trapezoidGapDeriv_nonpos q v hq0 (lt_of_lt_of_le hqw hvm.1) hvm.2
  have h := hanti ⟨le_refl w, hw1⟩ ⟨hw1, le_refl 1⟩ hw1
  simpa [trapezoidGap] using h

theorem perspective_log_trapezoid (q w : ℝ)
    (hq0 : 0 ≤ q) (hqw : q < w) (hw1 : w ≤ 1) :
    2 * ((w - q) * Real.log (w - q) - (1 - q) * Real.log (1 - q) -
      w * Real.log w) ≤
      (1 - w) * (-Real.log (1 - q / w) - Real.log (1 - q)) := by
  have hw0 : 0 < w := lt_of_le_of_lt hq0 hqw
  have hd : 0 < w - q := sub_pos.mpr hqw
  have hlog : Real.log (1 - q / w) = Real.log (w - q) - Real.log w := by
    rw [show 1 - q / w = (w - q) / w by field_simp]
    exact Real.log_div (ne_of_gt hd) (ne_of_gt hw0)
  have hgap := trapezoidGap_nonneg q w hq0 hqw hw1
  rw [hlog]
  unfold trapezoidGap at hgap
  nlinarith only [hgap]

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.ConcavityAcrossJoin ----
namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

theorem antitoneOn_Ioi_of_hasDerivAt_nonpos_except
    (f f' : ℝ → ℝ) (a c : ℝ)
    (hf : ContinuousOn f (Ioi a))
    (hd : ∀ x, a < x → x ≠ c → HasDerivAt f (f' x) x)
    (hneg : ∀ x, a < x → x ≠ c → f' x ≤ 0) :
    AntitoneOn f (Ioi a) := by
  have hsegment (l r : ℝ) (hal : a < l) (hlr : l ≤ r)
      (hc : c ∉ Ioo l r) : f r ≤ f l := by
    have hanti : AntitoneOn f (Icc l r) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := f') (convex_Icc l r)
      · exact hf.mono (fun _ hz => hal.trans_le hz.1)
      · intro z hz
        rw [interior_Icc] at hz
        have hzc : z ≠ c := by
          rintro rfl
          exact hc hz
        exact (hd z (hal.trans hz.1) hzc).hasDerivWithinAt
      · intro z hz
        rw [interior_Icc] at hz
        have hzc : z ≠ c := by
          rintro rfl
          exact hc hz
        exact hneg z (hal.trans hz.1) hzc
    exact hanti ⟨le_rfl, hlr⟩ ⟨hlr, le_rfl⟩ hlr
  intro x hx y hy hxy
  by_cases hc : c ∈ Ioo x y
  · exact (hsegment c y (hx.trans hc.1) hc.2.le (by simp)).trans
      (hsegment x c hx hc.1.le (by simp))
  · exact hsegment x y hx hxy hc

theorem concaveOn_Ioi_of_hasDerivAt2_nonpos_except
    (f f' f'' : ℝ → ℝ) (a c : ℝ)
    (hd : ∀ x, a < x → HasDerivAt f (f' x) x)
    (hcf' : ContinuousOn f' (Ioi a))
    (hd' : ∀ x, a < x → x ≠ c → HasDerivAt f' (f'' x) x)
    (hneg : ∀ x, a < x → x ≠ c → f'' x ≤ 0) :
    ConcaveOn ℝ (Ioi a) f := by
  have hanti := antitoneOn_Ioi_of_hasDerivAt_nonpos_except f' f'' a c hcf' hd' hneg
  apply AntitoneOn.concaveOn_of_deriv (convex_Ioi a)
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hd x hx).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    rw [interior_Ioi] at hx hy
    rw [(hd x hx).deriv, (hd y hy).deriv]
    exact hanti hx hy hxy

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.PerspectiveCalculus ----
namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

private theorem hasDerivAt_const_quotient (x v : ℝ) (hv : 0 < v) :
    HasDerivAt (fun w : ℝ => x / w) (-x / v ^ 2) v := by
  convert! (hasDerivAt_const v x).div (hasDerivAt_id v) (ne_of_gt hv) using 1
  simp

theorem hasDerivAt_logCorrectedPerspective (f f' : ℝ → ℝ) (x C : ℝ)
    {v : ℝ} (hv : 0 < v) (hf : HasDerivAt f (f' (x / v)) (x / v)) :
    HasDerivAt (logCorrectedPerspective f x C)
      (logCorrectedPerspectiveDeriv f f' x C v) v := by
  have hi := hasDerivAt_const_quotient x v hv
  have hp := (hasDerivAt_id v).mul (hf.comp v hi)
  have hl := ((hasDerivAt_id v).mul (Real.hasDerivAt_log (ne_of_gt hv))).const_mul C
  convert! hp.sub hl using 1
  · ext w
    change w * f (x / w) - C * w * Real.log w =
      w * f (x / w) - C * (w * Real.log w)
    ring
  · dsimp only [logCorrectedPerspectiveDeriv, id_eq, Function.comp_def]
    field_simp [ne_of_gt hv]
    ring

theorem hasDerivAt_logCorrectedPerspectiveDeriv (f f' f'' : ℝ → ℝ) (x C : ℝ)
    {v : ℝ} (hv : 0 < v) (hf : HasDerivAt f (f' (x / v)) (x / v))
    (hf' : HasDerivAt f' (f'' (x / v)) (x / v)) :
    HasDerivAt (logCorrectedPerspectiveDeriv f f' x C)
      (logCorrectedPerspectiveSecondDeriv f'' x C v) v := by
  have hi := hasDerivAt_const_quotient x v hv
  have hfirst := hf.comp v hi
  have hsecond := hi.mul (hf'.comp v hi)
  have hlog := ((Real.hasDerivAt_log (ne_of_gt hv)).add_const 1).const_mul C
  convert! (hfirst.sub hsecond).sub hlog using 1
  dsimp only [logCorrectedPerspectiveSecondDeriv, Function.comp_apply]
  field_simp [ne_of_gt hv]
  ring

theorem continuousOn_logCorrectedPerspectiveDeriv (f f' : ℝ → ℝ) (x C : ℝ)
    (hx : 0 < x) (hf : ∀ y, 0 < y → HasDerivAt f (f' y) y)
    (hf' : ContinuousOn f' (Ioi 0)) :
    ContinuousOn (logCorrectedPerspectiveDeriv f f' x C) (Ioi 0) := by
  have hi : ContinuousOn (fun v : ℝ => x / v) (Ioi 0) :=
    continuousOn_const.div continuousOn_id (fun _ hv => ne_of_gt hv)
  have hmap : MapsTo (fun v : ℝ => x / v) (Ioi 0) (Ioi 0) :=
    fun _ hv => div_pos hx hv
  have hcf : ContinuousOn f (Ioi 0) :=
    fun y hy => (hf y hy).continuousAt.continuousWithinAt
  have hl : ContinuousOn Real.log (Ioi 0) :=
    continuousOn_id.log (fun _ hv => ne_of_gt hv)
  exact ((hcf.comp hi hmap).sub (hi.mul (hf'.comp hi hmap))).sub
    (continuousOn_const.mul (hl.add continuousOn_const))

theorem concaveOn_logCorrectedPerspective (f f' f'' : ℝ → ℝ)
    (x C join : ℝ) (hx : 0 < x) (hjoin : 0 < join)
    (hf : ∀ y, 0 < y → HasDerivAt f (f' y) y)
    (hcf' : ContinuousOn f' (Ioi 0))
    (hf' : ∀ y, 0 < y → y ≠ join → HasDerivAt f' (f'' y) y)
    (hcurv : ∀ y, 0 < y → y ≠ join → y ^ 2 * f'' y ≤ C) :
    ConcaveOn ℝ (Ioi 0) (logCorrectedPerspective f x C) := by
  have hneq {v : ℝ} (hv : 0 < v) (hvc : v ≠ x / join) : x / v ≠ join := by
    intro heq
    apply hvc
    apply (eq_div_iff (ne_of_gt hjoin)).mpr
    have h := (div_eq_iff (ne_of_gt hv)).mp heq
    linarith
  apply concaveOn_Ioi_of_hasDerivAt2_nonpos_except
    (logCorrectedPerspective f x C) (logCorrectedPerspectiveDeriv f f' x C)
    (logCorrectedPerspectiveSecondDeriv f'' x C) 0 (x / join)
  · intro v hv
    exact hasDerivAt_logCorrectedPerspective f f' x C hv (hf _ (div_pos hx hv))
  · exact continuousOn_logCorrectedPerspectiveDeriv f f' x C hx hf hcf'
  · intro v hv hvc
    exact hasDerivAt_logCorrectedPerspectiveDeriv f f' f'' x C hv
      (hf _ (div_pos hx hv)) (hf' _ (div_pos hx hv) (hneq hv hvc))
  · intro v hv hvc
    exact div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (hcurv _ (div_pos hx hv) (hneq hv hvc))) hv.le

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.PerspectiveInequality ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Set Filter

namespace LeanBlast.CourtadeKumar

theorem hasDerivAt_logBarrier {b : ℝ} (hb : b < 1) :
    HasDerivAt logBarrier (1 / (1 - b)) b := by
  have h := (((hasDerivAt_const b (1 : ℝ)).sub (hasDerivAt_id b)).log
    (show 1 - b ≠ 0 by linarith)).neg
  convert! h using 1
  simp [neg_div]

theorem lambda_truncated_upper {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) (k m : ℕ) :
    (1 - z ^ k) * lambda z ≤
      (∑ j ∈ Finset.range k, z ^ j / ((j : ℝ) + 1)) -
      ∑ j ∈ Finset.range m,
        (z ^ k * (z ^ j / ((j : ℝ) + 1)) -
          z ^ (j + k) / ((j : ℝ) + k + 1)) := by
  have hs := hasSum_lambda hz0 hz1
  have ht := (hasSum_nat_add_iff' k).mpr hs
  have hd := (hs.mul_left (z ^ k)).sub ht
  simp only [Nat.cast_add] at hd
  have hnonneg : ∀ j : ℕ,
      0 ≤ z ^ k * (z ^ j / ((j : ℝ) + 1)) -
        z ^ (j + k) / ((j : ℝ) + k + 1) := by
    intro j
    rw [sub_nonneg, ← mul_div_assoc, ← pow_add, Nat.add_comm k j]
    apply div_le_div_of_nonneg_left (pow_nonneg hz0 _) (by positivity)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hp := sum_le_hasSum (Finset.range m) (fun j _ => hnonneg j) hd
  linarith

theorem lambda_cutoff_four {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    (1 - b ^ 4) * lambda b ≤
      1 + b / 2 + b ^ 2 / 3 + b ^ 3 / 4 - (4 / 5 : ℝ) * b ^ 4 -
        b ^ 5 / 3 - (4 / 21 : ℝ) * b ^ 6 - b ^ 7 / 8 - (4 / 45 : ℝ) * b ^ 8 := by
  have h := lambda_truncated_upper hb0 hb1 4 5
  norm_num [Finset.sum_range_succ] at h
  nlinarith

private theorem sq_lt_one_of_nonneg {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) : b ^ 2 < 1 := by
  have h := mul_pos (sub_pos.mpr hb1) (show 0 < 1 + b by linarith)
  nlinarith

theorem lambda_cutoff_two_sq {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    (1 - b ^ 4) * lambda (b ^ 2) ≤
      1 + b ^ 2 / 2 - (2 / 3 : ℝ) * b ^ 4 - b ^ 6 / 4 - (2 / 15 : ℝ) * b ^ 8 := by
  have h := lambda_truncated_upper (sq_nonneg b) (sq_lt_one_of_nonneg hb0 hb1) 2 3
  norm_num [Finset.sum_range_succ] at h
  nlinarith

theorem lambda_polynomial_le_factor {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    4 - (5 / 2 : ℝ) * b - 5 * b ^ 2 - (7 / 4 : ℝ) * b ^ 3 +
      (56 / 15 : ℝ) * b ^ 4 + b ^ 5 + (15 / 14 : ℝ) * b ^ 6 +
      (3 / 8 : ℝ) * b ^ 7 + (8 / 15 : ℝ) * b ^ 8 ≤ lambdaDerivativeFactor b := by
  unfold lambdaDerivativeFactor
  have h1 := lambda_cutoff_four hb0 hb1
  have h2 := lambda_cutoff_two_sq hb0 hb1
  nlinarith

theorem hasDerivAt_lambdaAuxiliary {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    HasDerivAt lambdaAuxiliary (lambdaAuxiliaryDerivative b) b := by
  have hb2 := sq_lt_one_of_nonneg hb0 hb1
  have hb4 : b ^ 4 < 1 := by
    have h := sq_lt_one_of_nonneg (sq_nonneg b) hb2
    nlinarith
  have h1 := hasDerivAt_logBarrier hb1
  have h2 := (hasDerivAt_logBarrier hb2).comp b (h := fun t : ℝ => t ^ 2) (hasDerivAt_pow 2 b)
  have h4 := (hasDerivAt_logBarrier hb4).comp b (h := fun t : ℝ => t ^ 4) (hasDerivAt_pow 4 b)
  have hd := ((h4.const_mul 3).sub ((hasDerivAt_pow 3 b).mul h1)).sub
    ((hasDerivAt_pow 2 b).mul h2)
  convert! hd using 1
  simp only [lambdaAuxiliaryDerivative, Function.comp_apply]
  ring

theorem lambdaAuxiliaryDerivative_factor {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    lambdaAuxiliaryDerivative b = b ^ 3 / (1 - b ^ 4) * lambdaDerivativeFactor b := by
  have hb2 := sq_lt_one_of_nonneg hb0.le hb1
  have hb4 : b ^ 4 < 1 := by
    have h := sq_lt_one_of_nonneg (sq_nonneg b) hb2
    nlinarith
  have hne : b ≠ 0 := hb0.ne'
  have hne2 : b ^ 2 ≠ 0 := pow_ne_zero _ hne
  have h1 : 1 - b ≠ 0 := by linarith
  have h2 : 1 - b ^ 2 ≠ 0 := by linarith
  have h4 : 1 - b ^ 4 ≠ 0 := by linarith
  simp only [lambdaAuxiliaryDerivative, lambdaDerivativeFactor, logBarrier,
    lambda_of_ne_zero hne, lambda_of_ne_zero hne2]
  field_simp
  ring

theorem lambdaDerivativeFactor_pos {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    0 < lambdaDerivativeFactor b := by
  have hp := lambdaCertificate_pos hb0 hb1.le
  have hf := lambda_polynomial_le_factor hb0 hb1
  unfold lambdaPolynomial at hp
  linarith

theorem lambdaAuxiliaryDerivative_nonneg {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    0 ≤ lambdaAuxiliaryDerivative b := by
  rw [lambdaAuxiliaryDerivative_factor hb0 hb1]
  have hb4 : b ^ 4 < 1 := by
    have h := sq_lt_one_of_nonneg (sq_nonneg b) (sq_lt_one_of_nonneg hb0.le hb1)
    nlinarith
  exact mul_nonneg (div_nonneg (pow_nonneg hb0.le _) (sub_nonneg.mpr hb4.le))
    (lambdaDerivativeFactor_pos hb0.le hb1).le

theorem monotoneOn_lambdaAuxiliary : MonotoneOn lambdaAuxiliary (Ico (0 : ℝ) 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
    (fun b hb => (hasDerivAt_lambdaAuxiliary hb.1 hb.2).continuousAt.continuousWithinAt)
  · intro b hb
    simp only [interior_Ico, mem_Ioo] at hb
    exact (hasDerivAt_lambdaAuxiliary hb.1.le hb.2).hasDerivWithinAt
  · intro b hb
    simp only [interior_Ico, mem_Ioo] at hb
    exact lambdaAuxiliaryDerivative_nonneg hb.1 hb.2

theorem lambdaAuxiliary_nonneg {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    0 ≤ lambdaAuxiliary b := by
  simpa using monotoneOn_lambdaAuxiliary
    (show (0 : ℝ) ∈ Ico 0 1 by norm_num) ⟨hb0, hb1⟩ hb0

theorem lambdaAuxiliary_eq (b : ℝ) :
    lambdaAuxiliary b = b ^ 4 * (3 * lambda (b ^ 4) - lambda b - lambda (b ^ 2)) := by
  have hM (z : ℝ) : logBarrier z = z * lambda z := (mul_lambda z).symm
  rw [lambdaAuxiliary, hM, hM, hM]
  ring

theorem lambda_add_sq_le (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) :
    lambda b + lambda (b ^ 2) ≤ 3 * lambda (b ^ 4) := by
  by_cases hb : b = 0
  · subst b
    norm_num
  have h := lambdaAuxiliary_nonneg hb0 hb1
  rw [lambdaAuxiliary_eq] at h
  have hp : 0 < b ^ 4 := pow_pos (lt_of_le_of_ne hb0 (Ne.symm hb)) _
  have ht := nonneg_of_mul_nonneg_right h hp
  linarith

theorem lambda_sqrt_add_le (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    lambda (Real.sqrt q) + lambda q ≤ 3 * lambda (q ^ 2) := by
  have hsq := Real.sq_sqrt hq0
  have hq : Real.sqrt q < 1 := by nlinarith [Real.sqrt_nonneg q]
  have h := lambda_add_sq_le (Real.sqrt q) (Real.sqrt_nonneg q) hq
  have hfour : (Real.sqrt q) ^ 4 = q ^ 2 := by nlinarith [sq_nonneg (Real.sqrt q)]
  simpa only [hsq, hfour] using h

theorem concave_perspective_exchange (f : ℝ → ℝ) (hf : ConcaveOn ℝ (Ioi 0) f)
    (w q : ℝ) (hq0 : 0 < q) (hqw : q < w) (hw1 : w ≤ 1) :
    f 1 + f (w - q) ≤ f w + f (1 - q) := by
  let a := q / (1 - w + q)
  let b := (1 - w) / (1 - w + q)
  have hr : 0 < 1 - w + q := by linarith
  have ha : 0 ≤ a := div_nonneg hq0.le hr.le
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hw1) hr.le
  have hab : a + b = 1 := by dsimp [a, b]; field_simp; ring
  have hab' : b + a = 1 := by linarith
  have hp1 : a * 1 + b * (w - q) = w := by dsimp [a, b]; field_simp; ring
  have hp2 : b * 1 + a * (w - q) = 1 - q := by dsimp [a, b]; field_simp; ring
  have h1 := hf.2 (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show w - q ∈ Ioi 0 from sub_pos.mpr hqw) ha hb hab
  have h2 := hf.2 (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show w - q ∈ Ioi 0 from sub_pos.mpr hqw) hb ha hab'
  simp only [smul_eq_mul, hp1, hp2] at h1 h2
  calc
    f 1 + f (w - q) = (a * f 1 + b * f (w - q)) +
        (b * f 1 + a * f (w - q)) := by
      calc
        _ = (a + b) * f 1 + (a + b) * f (w - q) := by rw [hab]; ring
        _ = _ := by ring
    _ ≤ f w + f (1 - q) := add_le_add h1 h2

theorem perspective_kernel_upper (f : ℝ → ℝ) (x w q : ℝ)
    (hx : 0 < x) (hq0 : 0 < q) (hqw : q < w) (hw1 : w ≤ 1)
    (hf0 : ∀ t, 0 < t → 0 ≤ f t)
    (hconc : ConcaveOn ℝ (Ioi 0)
      (fun v => v * f (x / v) - (2 / 3 : ℝ) * v * Real.log v)) :
    f x - (1 - q) * f (x / (1 - q)) - w * f (x / w) ≤
      (2 / 3 : ℝ) * ((w - q) * Real.log (w - q) -
        (1 - q) * Real.log (1 - q) - w * Real.log w) := by
  have he := concave_perspective_exchange _ hconc w q hq0 hqw hw1
  have hn : 0 ≤ (w - q) * f (x / (w - q)) :=
    mul_nonneg (sub_nonneg.mpr hqw.le) (hf0 _ (div_pos hx (sub_pos.mpr hqw)))
  simp only [one_mul, div_one, Real.log_one, mul_zero, sub_zero] at he
  nlinarith

theorem lt_weight_of_le_weight_sq {w q : ℝ}
    (hw0 : 0 < w) (hw1 : w ≤ 1) (hq1 : q < 1) (hqw : q ≤ w ^ 2) : q < w := by
  rcases eq_or_lt_of_le hw1 with rfl | hwlt
  · simpa using hq1
  · have hsq : w ^ 2 < w := by nlinarith [mul_pos hw0 (sub_pos.mpr hwlt)]
    exact hqw.trans_lt hsq

theorem lambda_trapezoid_bound (w q : ℝ)
    (hw0 : 0 < w) (hw1 : w ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hqw : q ≤ w ^ 2) :
    (1 - w) / 3 * (logBarrier (q / w) + logBarrier q) ≤
      q * (1 / w - 1) * lambda (q ^ 2) := by
  have hlt := lt_weight_of_le_weight_sq hw0 hw1 hq1 hqw
  have hqdiv0 : 0 ≤ q / w := div_nonneg hq0 hw0.le
  have hqdiv1 : q / w < 1 := (div_lt_one hw0).mpr hlt
  have hs0 := Real.sqrt_nonneg q
  have hs2 := Real.sq_sqrt hq0
  have hs1 : Real.sqrt q < 1 := by nlinarith
  have hsw : Real.sqrt q ≤ w := by nlinarith
  have hdivsqrt : q / w ≤ Real.sqrt q := by
    apply (div_le_iff₀ hw0).mpr
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hsw)]
  have hl1 := monotoneOn_lambda ⟨hqdiv0, hqdiv1⟩ ⟨hs0, hs1⟩ hdivsqrt
  have hl2 : w * lambda q ≤ lambda q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hw1) (lambda_nonneg hq0 hq1)]
  have hls := lambda_sqrt_add_le q hq0 hq1
  have hsum : lambda (q / w) + w * lambda q ≤ 3 * lambda (q ^ 2) := by linarith
  have hcoef : 0 ≤ q * (1 - w) / (3 * w) :=
    div_nonneg (mul_nonneg hq0 (sub_nonneg.mpr hw1)) (mul_nonneg (by norm_num) hw0.le)
  have hm := mul_le_mul_of_nonneg_left hsum hcoef
  have hM (z : ℝ) : logBarrier z = z * lambda z := (mul_lambda z).symm
  rw [hM, hM]
  convert! hm using 1 <;> field_simp

theorem perspective_inequality_of_adjusted_concave (f : ℝ → ℝ) (x w q : ℝ)
    (hx : 0 < x) (hw0 : 0 < w) (hw1 : w ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hqw : q ≤ w ^ 2) (hf0 : ∀ t, 0 < t → 0 ≤ f t)
    (hconc : ConcaveOn ℝ (Ioi 0)
      (fun v => v * f (x / v) - (2 / 3 : ℝ) * v * Real.log v)) :
    f x - (1 - q) * f (x / (1 - q)) - w * f (x / w) ≤
      q * (1 / w - 1) * lambda (q ^ 2) := by
  rcases eq_or_lt_of_le hq0 with hq | hq
  · subst q
    have hn := mul_nonneg hw0.le (hf0 _ (div_pos hx hw0))
    simpa using neg_nonpos.mpr hn
  have hlt := lt_weight_of_le_weight_sq hw0 hw1 hq1 hqw
  have hk := perspective_kernel_upper f x w q hx hq hlt hw1 hf0 hconc
  have ht := perspective_log_trapezoid q w hq0 hlt hw1
  have hl := lambda_trapezoid_bound w q hw0 hw1 hq0 hq1 hqw
  have hc : (2 / 3 : ℝ) * ((w - q) * Real.log (w - q) -
        (1 - q) * Real.log (1 - q) - w * Real.log w) ≤
      (1 - w) / 3 * (logBarrier (q / w) + logBarrier q) := by
    unfold logBarrier
    nlinarith
  exact hk.trans (hc.trans hl)

theorem LSecondDeriv_curvature_bound {x : ℝ} (hx : 0 < x) :
    x ^ 2 * LSecondDeriv x ≤ 2 / 3 := by
  by_cases hxl : x < ell
  · simpa only [LSecondDeriv, ite_eq_left hxl] using L_curvature_bound ⟨hx, hxl⟩
  · simp only [LSecondDeriv, ite_eq_right hxl, mul_zero]
    norm_num

theorem concaveOn_L_logCorrectedPerspective (x : ℝ) (hx : 0 < x) :
    ConcaveOn ℝ (Ioi 0)
      (fun v => v * L (x / v) - (2 / 3 : ℝ) * v * Real.log v) := by
  exact concaveOn_logCorrectedPerspective L LDeriv LSecondDeriv x (2 / 3) ell
    hx ell_pos (fun y hy => hasDerivAt_L hy) continuousOn_LDeriv
    (fun y hy hne => hasDerivAt_LDeriv hy hne)
    (fun y hy _ => LSecondDeriv_curvature_bound hy)

theorem perspective_inequality (x w q : ℝ)
    (hx : 0 < x) (hw0 : 0 < w) (hw1 : w ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hqw : q ≤ w ^ 2) :
    L x - (1 - q) * L (x / (1 - q)) - w * L (x / w) ≤
      q * (1 / w - 1) * lambda (q ^ 2) :=
  perspective_inequality_of_adjusted_concave L x w q hx hw0 hw1 hq0 hq1 hqw
    (fun _ ht => L_nonneg ht) (concaveOn_L_logCorrectedPerspective x hx)

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.MonotoneDissipation ----
namespace OAI

noncomputable section

open scoped BigOperators
open Set

namespace LeanBlast.CourtadeKumar

theorem IsIncreasing.restrict {n : ℕ} {g : Cube (n + 1) → ℝ}
    (hg : IsIncreasing g) (b : Bool) : IsIncreasing (restrict g b) := by
  intro x y hxy
  apply hg
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · exact hxy j

theorem IsIncreasing.pairHalfDifference_nonneg {n : ℕ} {g : Cube (n + 1) → ℝ}
    (hg : IsIncreasing g) (x : Cube n) : 0 ≤ pairHalfDifference g x := by
  have horder : CourtadeKumar.restrict g false x ≤ CourtadeKumar.restrict g true x := by
    apply hg
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · exact le_rfl
  exact div_nonneg (sub_nonneg.mpr horder) (by norm_num)

theorem scalar_meanVariance_pos {m : ℝ} (hm : |m| < 1) : 0 < 1 - m ^ 2 := by
  have hsq := (sq_lt_sq₀ (abs_nonneg m) (by norm_num : (0 : ℝ) ≤ 1)).mpr hm
  rw [sq_abs] at hsq
  nlinarith

theorem scalar_meanVariance_le_one (m : ℝ) : 1 - m ^ 2 ≤ 1 := by
  nlinarith [sq_nonneg m]

theorem IsInterior.meanVariance_pos {n : ℕ} {g : Cube n → ℝ}
    (hg : IsInterior g) : 0 < meanVariance g :=
  scalar_meanVariance_pos (abs_lt.mpr hg.cubeAverage)

theorem IsInterior.entropyAverage_pos {n : ℕ} {g : Cube n → ℝ}
    (hg : IsInterior g) : 0 < entropyAverage g := by
  have h := cubeAverage_lt (fun x => entropy_pos (hg x))
  simpa only [cubeAverage_const, entropyAverage] using h

theorem average_one_sub_sq_le_meanVariance {n : ℕ} (a : Cube n → ℝ) :
    cubeAverage (fun x => 1 - (a x) ^ 2) ≤ meanVariance a := by
  rw [average_one_sub_sq_eq_meanVariance_sub_variance]
  linarith [cubeVariance_nonneg a]

theorem monotone_pair_average_geometry {n : ℕ} (a b : Cube n → ℝ)
    (hdom : ∀ x, |a x| + |b x| < 1) (hb : ∀ x, 0 ≤ b x) :
    |cubeAverage a| < 1 ∧ 0 ≤ cubeAverage b ∧
      cubeAverage b < 1 - |cubeAverage a| ∧
      0 < cubeAverage (fun x => 1 - (a x) ^ 2) ∧
      cubeAverage (fun x => 1 - (a x) ^ 2) ≤ 1 - (cubeAverage a) ^ 2 ∧
      cubeAverage b ≤ cubeAverage (fun x => 1 - (a x) ^ 2) := by
  have ha : IsInterior a := by
    intro x
    apply abs_lt.mp
    linarith [hdom x, abs_nonneg (b x)]
  have hm : |cubeAverage a| < 1 := abs_lt.mpr ha.cubeAverage
  have hk : 0 ≤ cubeAverage b := cubeAverage_nonneg hb
  have hplus : cubeAverage a + cubeAverage b < 1 := by
    have h := cubeAverage_lt (g := fun x => a x + b x) (h := fun _ => 1) (by
      intro x
      have hd := hdom x
      rw [abs_of_nonneg (hb x)] at hd
      linarith [le_abs_self (a x)])
    simpa only [cubeAverage_add, cubeAverage_const] using h
  have hminus : -cubeAverage a + cubeAverage b < 1 := by
    have h := cubeAverage_lt (g := fun x => -a x + b x) (h := fun _ => 1) (by
      intro x
      have hd := hdom x
      rw [abs_of_nonneg (hb x)] at hd
      linarith [neg_le_abs (a x)])
    simpa only [cubeAverage_add, cubeAverage_neg, cubeAverage_const] using h
  have hkm : cubeAverage b < 1 - |cubeAverage a| := by
    by_cases hm0 : 0 ≤ cubeAverage a
    · rw [abs_of_nonneg hm0]
      linarith
    · rw [abs_of_nonpos (le_of_not_ge hm0)]
      linarith
  have hW : 0 < cubeAverage (fun x => 1 - (a x) ^ 2) := by
    have h := cubeAverage_lt (fun x => scalar_meanVariance_pos (abs_lt.mpr (ha x)))
    simpa only [cubeAverage_const] using h
  have hkW : cubeAverage b ≤ cubeAverage (fun x => 1 - (a x) ^ 2) := by
    apply cubeAverage_mono
    intro x
    have hd := hdom x
    rw [abs_of_nonneg (hb x)] at hd
    have ha1 : |a x| ≤ 1 := (abs_lt.mpr (ha x)).le
    have hasq : |a x| ^ 2 ≤ |a x| := by
      nlinarith [mul_nonneg (abs_nonneg (a x)) (sub_nonneg.mpr ha1)]
    nlinarith [sq_abs (a x)]
  exact ⟨hm, hk, hkm, hW, average_one_sub_sq_le_meanVariance a, hkW⟩

theorem halfDifference_sq_lt_meanVariance {m k : ℝ}
    (hm : |m| < 1) (hk : 0 ≤ k) (hkm : k < 1 - |m|) :
    k ^ 2 < 1 - m ^ 2 := by
  have hsq := (sq_lt_sq₀ hk (sub_nonneg.mpr hm.le)).mpr hkm
  have ha : |m| ^ 2 ≤ |m| := by
    nlinarith [mul_nonneg (abs_nonneg m) (sub_nonneg.mpr hm.le)]
  nlinarith [sq_abs m]

theorem monotone_split_parameter_bounds {m k W : ℝ}
    (hm : |m| < 1) (hk : 0 ≤ k) (hkm : k < 1 - |m|)
    (hW : 0 < W) (hWA : W ≤ 1 - m ^ 2) (hkW : k ≤ W) :
    0 ≤ k ^ 2 / (1 - m ^ 2) ∧ k ^ 2 / (1 - m ^ 2) < 1 ∧
      0 < W / (1 - m ^ 2) ∧ W / (1 - m ^ 2) ≤ 1 ∧
      k ^ 2 / (1 - m ^ 2) ≤ (W / (1 - m ^ 2)) ^ 2 := by
  have hA := scalar_meanVariance_pos hm
  have hA1 := scalar_meanVariance_le_one m
  refine ⟨div_nonneg (sq_nonneg _) hA.le,
    (div_lt_one hA).mpr (halfDifference_sq_lt_meanVariance hm hk hkm),
    div_pos hW hA, (div_le_one hA).mpr hWA, ?_⟩
  have hk2W2 : k ^ 2 ≤ W ^ 2 := (sq_le_sq₀ hk hW.le).mpr hkW
  have hk2A : k ^ 2 * (1 - m ^ 2) ≤ W ^ 2 := by
    calc
      k ^ 2 * (1 - m ^ 2) ≤ k ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hA1 (sq_nonneg _)
      _ = k ^ 2 := mul_one _
      _ ≤ W ^ 2 := hk2W2
  rw [div_pow]
  apply (div_le_div_iff₀ hA (sq_pos_of_pos hA)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hk2A hA.le]

theorem meanSquare_ratio_le_jensen_ratio {m k : ℝ}
    (hm : |m| < 1) (hk : 0 ≤ k) (hkm : k < 1 - |m|) :
    k ^ 2 / (1 - m ^ 2) ≤ k / (1 + |m|) := by
  have hA := scalar_meanVariance_pos hm
  have hden : 0 < 1 + |m| := by positivity
  apply (div_le_div_iff₀ hA hden).mpr
  have hprod := mul_le_mul_of_nonneg_left hkm.le
    (mul_nonneg hk hden.le)
  rw [← sq_abs m]
  nlinarith [hprod]

theorem jensen_ratio_mem_unit_interval {m k : ℝ}
    (hk : 0 ≤ k) (hkm : k < 1 - |m|) :
    0 ≤ k / (1 + |m|) ∧ k / (1 + |m|) < 1 := by
  have hden : 0 < 1 + |m| := by positivity
  refine ⟨div_nonneg hk hden.le, (div_lt_one hden).mpr ?_⟩
  linarith [abs_nonneg m]

theorem normalized_variance_gap_nonneg {q w : ℝ}
    (hq : 0 ≤ q) (hw : 0 < w) (hw1 : w ≤ 1) :
    0 ≤ q * (1 / w - 1) := by
  have hinv : 1 ≤ 1 / w := (le_div_iff₀ hw).mpr (by simpa using hw1)
  exact mul_nonneg hq (sub_nonneg.mpr hinv)

theorem normalized_variance_gap_identity {A W k : ℝ} (hA : A ≠ 0) (hW : W ≠ 0) :
    k ^ 2 / W - k ^ 2 / A = (k ^ 2 / A) * (1 / (W / A) - 1) := by
  field_simp

theorem normalized_jensen_correction_le {m k W V : ℝ}
    (hm : |m| < 1) (hk : 0 ≤ k) (hkm : k < 1 - |m|)
    (hW : 0 < W) (hWA : W ≤ 1 - m ^ 2) (hkW : k ≤ W)
    (hV : k ^ 2 / W - k ^ 2 / (1 - m ^ 2) ≤ V) :
    (k ^ 2 / (1 - m ^ 2)) * (1 / (W / (1 - m ^ 2)) - 1) *
        lambda ((k ^ 2 / (1 - m ^ 2)) ^ 2) ≤
      V * lambda ((k / (1 + |m|)) ^ 2) := by
  obtain ⟨hq, hq1, hw, hw1, _⟩ :=
    monotone_split_parameter_bounds hm hk hkm hW hWA hkW
  obtain ⟨hs, hs1⟩ := jensen_ratio_mem_unit_interval hk hkm
  have hq2 : (k ^ 2 / (1 - m ^ 2)) ^ 2 < 1 := by nlinarith
  have hs2 : (k / (1 + |m|)) ^ 2 < 1 := by nlinarith
  have hqs : (k ^ 2 / (1 - m ^ 2)) ^ 2 ≤ (k / (1 + |m|)) ^ 2 :=
    (sq_le_sq₀ hq hs).mpr (meanSquare_ratio_le_jensen_ratio hm hk hkm)
  have hB := normalized_variance_gap_nonneg hq hw hw1
  have hBV : (k ^ 2 / (1 - m ^ 2)) * (1 / (W / (1 - m ^ 2)) - 1) ≤ V := by
    rwa [← normalized_variance_gap_identity (scalar_meanVariance_pos hm).ne' hW.ne']
  have hlambda := monotoneOn_lambda ⟨sq_nonneg _, hq2⟩ ⟨sq_nonneg _, hs2⟩ hqs
  exact mul_le_mul hBV hlambda (lambda_nonneg (sq_nonneg _) hq2) (hB.trans hBV)

theorem scaled_perspective_bound (F : ℝ → ℝ) {A W k h B : ℝ}
    (hA : 0 < A) (hA1 : A ≤ 1) (hW : 0 < W) (hAk : 0 < A - k ^ 2)
    (hB : 0 ≤ B)
    (hperspective : F (h / A) - (1 - k ^ 2 / A) * F ((h / A) / (1 - k ^ 2 / A)) -
      (W / A) * F ((h / A) / (W / A)) ≤ B) :
    A * F (h / A) - (A - k ^ 2) * F (h / (A - k ^ 2)) - W * F (h / W) ≤ B := by
  have harg1 : (h / A) / (1 - k ^ 2 / A) = h / (A - k ^ 2) := by
    have hden : 1 - k ^ 2 / A = (A - k ^ 2) / A := by field_simp
    rw [hden]
    field_simp
  have harg2 : (h / A) / (W / A) = h / W := by field_simp
  rw [harg1, harg2] at hperspective
  have hscaled := mul_le_mul_of_nonneg_left hperspective hA.le
  have hcoef1 : A * (1 - k ^ 2 / A) = A - k ^ 2 := by field_simp
  have hcoef2 : A * (W / A) = W := by field_simp
  have hleft : A * (F (h / A) - (1 - k ^ 2 / A) * F (h / (A - k ^ 2)) -
      (W / A) * F (h / W)) =
      A * F (h / A) - (A - k ^ 2) * F (h / (A - k ^ 2)) - W * F (h / W) := by
    rw [mul_sub, mul_sub, ← mul_assoc, hcoef1, ← mul_assoc, hcoef2]
  rw [hleft] at hscaled
  exact hscaled.trans (by nlinarith)

theorem monotone_dissipation_step_algebra (F : ℝ → ℝ)
    {S Jm A k h W B Drestr Dpair : ℝ}
    (hrestr : 2 * (S - Jm) + (A - k ^ 2) * F (h / (A - k ^ 2)) ≤ Drestr)
    (hpair : W * F (h / W) + B ≤ Dpair - 2 * Jm)
    (hperspective : A * F (h / A) - (A - k ^ 2) * F (h / (A - k ^ 2)) -
      W * F (h / W) ≤ B) :
    2 * S + A * F (h / A) ≤ Drestr + Dpair := by
  linarith

theorem monotone_pair_correction {m k W h Je Jm V Dpair : ℝ}
    (hm : |m| < 1) (hk : 0 ≤ k) (hkm : k < 1 - |m|)
    (hW : 0 < W) (hWA : W ≤ 1 - m ^ 2) (hkW : k ≤ W)
    (hV : k ^ 2 / W - k ^ 2 / (1 - m ^ 2) ≤ V)
    (hnormalized : W * L (h / W) ≤ Dpair - 2 * Je)
    (hgap : V * lambda ((k / (1 + |m|)) ^ 2) ≤ 2 * (Je - Jm)) :
    W * L (h / W) +
        (k ^ 2 / (1 - m ^ 2)) * (1 / (W / (1 - m ^ 2)) - 1) *
          lambda ((k ^ 2 / (1 - m ^ 2)) ^ 2) ≤ Dpair - 2 * Jm := by
  have hcorrection := normalized_jensen_correction_le hm hk hkm hW hWA hkW hV
  linarith

theorem monotone_dissipation_step_of_perspective
    {m k W h S Je Jm V Drestr Dpair : ℝ}
    (hm : |m| < 1) (hk : 0 ≤ k) (hkm : k < 1 - |m|)
    (hW : 0 < W) (hWA : W ≤ 1 - m ^ 2) (hkW : k ≤ W)
    (hV : k ^ 2 / W - k ^ 2 / (1 - m ^ 2) ≤ V)
    (hrestr : 2 * (S - Jm) + (1 - m ^ 2 - k ^ 2) *
      L (h / (1 - m ^ 2 - k ^ 2)) ≤ Drestr)
    (hnormalized : W * L (h / W) ≤ Dpair - 2 * Je)
    (hgap : V * lambda ((k / (1 + |m|)) ^ 2) ≤ 2 * (Je - Jm))
    (hperspective : L (h / (1 - m ^ 2)) -
      (1 - k ^ 2 / (1 - m ^ 2)) *
        L ((h / (1 - m ^ 2)) / (1 - k ^ 2 / (1 - m ^ 2))) -
      (W / (1 - m ^ 2)) * L ((h / (1 - m ^ 2)) / (W / (1 - m ^ 2))) ≤
      (k ^ 2 / (1 - m ^ 2)) * (1 / (W / (1 - m ^ 2)) - 1) *
        lambda ((k ^ 2 / (1 - m ^ 2)) ^ 2)) :
    2 * S + (1 - m ^ 2) * L (h / (1 - m ^ 2)) ≤ Drestr + Dpair := by
  have hA := scalar_meanVariance_pos hm
  have hAk : 0 < 1 - m ^ 2 - k ^ 2 := by
    linarith [halfDifference_sq_lt_meanVariance hm hk hkm]
  obtain ⟨hq, hq1, hw, hw1, _⟩ :=
    monotone_split_parameter_bounds hm hk hkm hW hWA hkW
  have hq2 : (k ^ 2 / (1 - m ^ 2)) ^ 2 < 1 := by nlinarith
  have hB := mul_nonneg (normalized_variance_gap_nonneg hq hw hw1)
    (lambda_nonneg (sq_nonneg _) hq2)
  have hp := scaled_perspective_bound L hA (scalar_meanVariance_le_one m) hW hAk hB
    hperspective
  have hc := monotone_pair_correction hm hk hkm hW hWA hkW hV hnormalized hgap
  exact monotone_dissipation_step_algebra L hrestr hc hp

theorem two_point_perspective_jensen (F : ℝ → ℝ)
    (hF : ConvexOn ℝ (Ioi 0) F) {A₀ A₁ H₀ H₁ : ℝ}
    (hA₀ : 0 < A₀) (hA₁ : 0 < A₁) (hH₀ : 0 < H₀) (hH₁ : 0 < H₁) :
    ((A₁ + A₀) / 2) * F (((H₁ + H₀) / 2) / ((A₁ + A₀) / 2)) ≤
      (A₁ * F (H₁ / A₁) + A₀ * F (H₀ / A₀)) / 2 := by
  have hsum : 0 < A₁ + A₀ := add_pos hA₁ hA₀
  have hweights : A₁ / (A₁ + A₀) + A₀ / (A₁ + A₀) = 1 := by field_simp
  have hJ := hF.2 (show H₁ / A₁ ∈ Ioi 0 from div_pos hH₁ hA₁)
    (show H₀ / A₀ ∈ Ioi 0 from div_pos hH₀ hA₀)
    (div_nonneg hA₁.le hsum.le) (div_nonneg hA₀.le hsum.le) hweights
  simp only [smul_eq_mul] at hJ
  have harg : A₁ / (A₁ + A₀) * (H₁ / A₁) +
      A₀ / (A₁ + A₀) * (H₀ / A₀) = (H₁ + H₀) / (A₁ + A₀) := by
    field_simp
  rw [harg] at hJ
  have hhalf : ((H₁ + H₀) / 2) / ((A₁ + A₀) / 2) =
      (H₁ + H₀) / (A₁ + A₀) := by field_simp
  rw [hhalf]
  have hscaled := mul_le_mul_of_nonneg_left hJ (show 0 ≤ (A₁ + A₀) / 2 by positivity)
  have hright : (A₁ + A₀) / 2 *
      (A₁ / (A₁ + A₀) * F (H₁ / A₁) + A₀ / (A₁ + A₀) * F (H₀ / A₀)) =
      (A₁ * F (H₁ / A₁) + A₀ * F (H₀ / A₀)) / 2 := by
    field_simp
  rwa [hright] at hscaled

theorem monotone_dissipation_zero (g : Cube 0 → ℝ) (hg : IsInterior g) :
    2 * informationDeficit g +
      meanVariance g * L (entropyAverage g / meanVariance g) ≤ dissipation g := by
  have hA : 0 < meanVariance g := hg.meanVariance_pos
  have hscalar := ell_mul_one_sub_sq_le_entropy
    (abs_lt.mpr (hg (fun _ => false))).le
  have hratio : ell ≤ entropyAverage g / meanVariance g := by
    apply (le_div_iff₀ hA).mpr
    simpa only [entropyAverage, meanVariance, cubeAverage_zeroDim] using hscalar
  rw [informationDeficit_dim_zero, dissipation_dim_zero, L_eq_zero_of_ell_le hratio]
  simp

theorem averaged_normalized_pair_of_pointwise
    (hconvex : ConvexOn ℝ (Ioi 0) L)
    (hpair : ∀ a b : ℝ, |a| + |b| < 1 →
      (1 - a ^ 2) * L (((entropy (a + b) + entropy (a - b)) / 2) / (1 - a ^ 2)) ≤
        pairDissipation a b - 2 * pairEntropyGap a b)
    {n : ℕ} (g : Cube (n + 1) → ℝ) (hg : IsInterior g) :
    cubeAverage (fun x => 1 - (pairMean g x) ^ 2) *
        L (entropyAverage g / cubeAverage (fun x => 1 - (pairMean g x) ^ 2)) ≤
      cubeAverage (fun x => pairDissipation (pairMean g x) (pairHalfDifference g x)) -
        2 * cubeAverage (fun x => pairEntropyGap (pairMean g x) (pairHalfDifference g x)) := by
  let A : Cube n → ℝ := fun x => 1 - (pairMean g x) ^ 2
  let H : Cube n → ℝ := fun x =>
    (entropy (pairMean g x + pairHalfDifference g x) +
      entropy (pairMean g x - pairHalfDifference g x)) / 2
  have hA : ∀ x, 0 < A x := fun x =>
    scalar_meanVariance_pos (abs_lt.mpr (hg.pairMean x))
  have hH : ∀ x, 0 < H x := by
    intro x
    dsimp [H]
    rw [pairMean_add_halfDifference, pairMean_sub_halfDifference]
    exact div_pos (add_pos (entropy_pos (hg.restrict true x))
      (entropy_pos (hg.restrict false x))) (by norm_num)
  have hHavg : cubeAverage H = entropyAverage g := by
    dsimp [H]
    simp only [pairMean_add_halfDifference, pairMean_sub_halfDifference]
    rw [cubeAverage_half_sum]
    exact (entropyAverage_split g).symm
  have hJ := cubeAverage_perspective_jensen L hconvex A H hA hH
  rw [hHavg] at hJ
  have hpoint := cubeAverage_mono (fun x => hpair _ _ (hg.pairDomain x))
  have hcombined := hJ.trans hpoint
  simpa only [A, cubeAverage_sub, cubeAverage_smul] using hcombined

theorem restricted_monotone_dissipation_lower
    (hconvex : ConvexOn ℝ (Ioi 0) L)
    {n : ℕ} (g : Cube (n + 1) → ℝ) (hg : IsInterior g)
    (htrue : 2 * informationDeficit (restrict g true) +
      meanVariance (restrict g true) *
        L (entropyAverage (restrict g true) / meanVariance (restrict g true)) ≤
      dissipation (restrict g true))
    (hfalse : 2 * informationDeficit (restrict g false) +
      meanVariance (restrict g false) *
        L (entropyAverage (restrict g false) / meanVariance (restrict g false)) ≤
      dissipation (restrict g false)) :
    2 * (informationDeficit g - pairEntropyGap (cubeAverage (pairMean g))
        (cubeAverage (pairHalfDifference g))) +
      (meanVariance g - (cubeAverage (pairHalfDifference g)) ^ 2) *
        L (entropyAverage g / (meanVariance g - (cubeAverage (pairHalfDifference g)) ^ 2)) ≤
      (dissipation (restrict g true) + dissipation (restrict g false)) / 2 := by
  have hJ := two_point_perspective_jensen L hconvex
    (hg.restrict false).meanVariance_pos (hg.restrict true).meanVariance_pos
    (hg.restrict false).entropyAverage_pos (hg.restrict true).entropyAverage_pos
  rw [meanVariance_split, ← entropyAverage_split g] at hJ
  have hS := informationDeficit_split g
  linarith

theorem monotone_dissipation_from_scalar_lemmas
    (hconvex : ConvexOn ℝ (Ioi 0) L)
    (hpair : ∀ a b : ℝ, |a| + |b| < 1 →
      (1 - a ^ 2) * L (((entropy (a + b) + entropy (a - b)) / 2) / (1 - a ^ 2)) ≤
        pairDissipation a b - 2 * pairEntropyGap a b)
    (hperspective : ∀ x w q : ℝ, 0 < x → 0 < w → w ≤ 1 → 0 ≤ q → q < 1 → q ≤ w ^ 2 →
      L x - (1 - q) * L (x / (1 - q)) - w * L (x / w) ≤
        q * (1 / w - 1) * lambda (q ^ 2)) :
    ∀ {n : ℕ} (g : Cube n → ℝ), IsInterior g → IsIncreasing g →
      2 * informationDeficit g + meanVariance g * L (entropyAverage g / meanVariance g) ≤
        dissipation g := by
  intro n
  induction n with
  | zero =>
      intro g hg _
      exact monotone_dissipation_zero g hg
  | succ n ih =>
      intro g hg hmono
      let a := pairMean g
      let b := pairHalfDifference g
      have hdom : ∀ x, |a x| + |b x| < 1 := hg.pairDomain
      have hb : ∀ x, 0 ≤ b x := hmono.pairHalfDifference_nonneg
      obtain ⟨hm, hk, hkm, hW, hWA, hkW⟩ := monotone_pair_average_geometry a b hdom hb
      have htrue := ih (restrict g true) (hg.restrict true) (hmono.restrict true)
      have hfalse := ih (restrict g false) (hg.restrict false) (hmono.restrict false)
      have hrestr := restricted_monotone_dissipation_lower hconvex g hg htrue hfalse
      have hrestr' :
          2 * (informationDeficit g - pairEntropyGap (cubeAverage a) (cubeAverage b)) +
          (1 - (cubeAverage a) ^ 2 - (cubeAverage b) ^ 2) *
            L (entropyAverage g / (1 - (cubeAverage a) ^ 2 - (cubeAverage b) ^ 2)) ≤
          (dissipation (restrict g true) + dissipation (restrict g false)) / 2 := by
        simpa only [a, b, meanVariance, cubeAverage_pairMean] using hrestr
      have hnorm := averaged_normalized_pair_of_pointwise hconvex hpair g hg
      have hgap := pair_jensen_gap_strengthened a b hdom hb
      have hV := pair_variance_gap_lower_bound a b hdom
      obtain ⟨hq, hq1, hw, hw1, hqw⟩ :=
        monotone_split_parameter_bounds hm hk hkm hW hWA hkW
      have hx : 0 < entropyAverage g / (1 - (cubeAverage a) ^ 2) :=
        div_pos hg.entropyAverage_pos (scalar_meanVariance_pos hm)
      have hp := hperspective _ _ _ hx hw hw1 hq hq1 hqw
      have hfinal := monotone_dissipation_step_of_perspective hm hk hkm hW hWA hkW
        hV hrestr' hnorm hgap hp
      rw [dissipation_split g]
      simpa only [a, b, meanVariance, cubeAverage_pairMean] using hfinal

theorem monotone_dissipation {n : ℕ} (g : Cube n → ℝ)
    (hg : IsInterior g) (hmono : IsIncreasing g) :
    2 * informationDeficit g + meanVariance g * L (entropyAverage g / meanVariance g) ≤
      dissipation g := by
  exact monotone_dissipation_from_scalar_lemmas convexOn_L
    (fun _ _ hab => normalized_pair_bound hab) perspective_inequality g hg hmono

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.Attainment ----
namespace OAI

open scoped BigOperators

noncomputable section

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem entropyAverage_neg (g : Cube n → ℝ) :
    entropyAverage (fun x => -g x) = entropyAverage g := by
  simp [entropyAverage]

theorem informationDeficit_neg (g : Cube n → ℝ) :
    informationDeficit (fun x => -g x) = informationDeficit g := by
  simp only [informationDeficit, cubeAverage_neg, entropy_neg, entropyAverage_neg]

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.SoftChannel.Canonical ----
namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology
namespace LeanBlast.CourtadeKumar

lemma joiningCost_nonneg {x y : ℝ} (hx : x ∈ Ioo (-1) 1) (hy : y ∈ Ioo (-1) 1) :
    0 ≤ joiningCost x y := by
  unfold joiningCost
  rcases le_total y x with h | h
  · apply mul_nonneg (div_nonneg (sub_nonneg.mpr h) (by norm_num))
    exact sub_nonneg.mpr (Real.strictMonoOn_artanh.monotoneOn hy hx h)
  · apply mul_nonneg_of_nonpos_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (by norm_num))
    exact sub_nonpos.mpr (Real.strictMonoOn_artanh.monotoneOn hx hy h)

end LeanBlast.CourtadeKumar
end
end

end OAI

-- ---- from OAI.InformationTheory.SoftChannel.HighReserve ----
namespace OAI

section

noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace LeanBlast.CourtadeKumar

lemma meanReserve_zero_mean {I : ℝ} (hI : I ∈ Ico 0 ell) : meanReserve 0 I = r I := by
  simp only [meanReserve, entropy_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, sub_zero, div_one, one_mul]
  rw [L_ell_sub hI.1 hI.2]
  ring

end LeanBlast.CourtadeKumar
end
end

end OAI

-- ---- from OAI.InformationTheory.SoftChannel.Wall ----
namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology
namespace LeanBlast.CourtadeKumar

lemma artanh_neg_interior {u : ℝ} (hu : u ∈ Ioo (-1) 1) : Real.artanh (-u) = -Real.artanh u := by
  rw [artanh_eq_log_sub (show -u ∈ Ioo (-1) 1 by constructor <;> linarith [hu.1,hu.2]),
    artanh_eq_log_sub hu]
  simp only [← sub_eq_add_neg,sub_neg_eq_add]
  ring

end LeanBlast.CourtadeKumar
end
end

end OAI

-- ---- from OAI.InformationTheory.SoftChannel.SoftReserve ----
namespace OAI

section

noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace LeanBlast.CourtadeKumar
variable {n : ℕ}

theorem sortCoordinate_property (i : Fin n) (F : Cube n → ℝ)
    (P : ℝ → Prop) (hF : ∀ x, P (F x)) : ∀ x, P (sortCoordinate i F x) := by
  intro x
  unfold sortCoordinate
  split <;> first | exact (max_rec (fun _ => hF _) (fun _ => hF _)) | exact (min_rec (fun _ => hF _) (fun _ => hF _))

theorem sortCoordinate_interior (i : Fin n) {F : Cube n → ℝ} (hF : IsInterior F) :
    IsInterior (sortCoordinate i F) := sortCoordinate_property i F (fun v => v ∈ Ioo (-1 : ℝ) 1) hF

theorem sortCoordinate_closed (i : Fin n) {F : Cube n → ℝ}
    (hF : ∀ x, F x ∈ Icc (-1 : ℝ) 1) : ∀ x, sortCoordinate i F x ∈ Icc (-1 : ℝ) 1 :=
  sortCoordinate_property i F _ hF

theorem cubeAverage_comp_sortCoordinate (i : Fin n) (F : Cube n → ℝ) (h : ℝ → ℝ) :
    cubeAverage (fun x => h (sortCoordinate i F x)) = cubeAverage (fun x => h (F x)) := by
  have hp (x : Cube n) : h (sortCoordinate i F (setBit i false x)) +
      h (sortCoordinate i F (setBit i true x)) =
      h (F (setBit i false x)) + h (F (setBit i true x)) := by
    simp only [sortCoordinate_false, sortCoordinate_true]
    rcases le_total (F (setBit i false x)) (F (setBit i true x)) with hz | hz
    · rw [min_eq_left hz, max_eq_right hz]
    · rw [min_eq_right hz, max_eq_left hz, add_comm]
  have hh := congrArg (fun f : Cube n → ℝ => ∑ x, f x) (funext hp)
  rw [sum_setBit_pair i (fun x => h (sortCoordinate i F x)),
    sum_setBit_pair i (fun x => h (F x))] at hh
  unfold cubeAverage
  have hs : (∑ x, h (sortCoordinate i F x)) = ∑ x, h (F x) := by linarith
  rw [hs]

theorem psi_noise_sortCoordinate_pair_closed (i : Fin n) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) {F : Cube n → ℝ} (hF : ∀ x, F x ∈ Icc (-1 : ℝ) 1) (x : Cube n) :
    psi (noiseOperator u F (setBit i false x)) +
        psi (noiseOperator u F (setBit i true x)) ≤
      psi (noiseOperator u (sortCoordinate i F) (setBit i false x)) +
        psi (noiseOperator u (sortCoordinate i F) (setBit i true x)) := by
  let A := coordinateOffNoise i u (coordinatePairMean i F) x
  let B := u * coordinateOffNoise i u (coordinatePairDifference i F) x
  let C := u * coordinateOffNoise i u (fun y => |coordinatePairDifference i F y|) x
  have hc : 0 ≤ C := mul_nonneg hu.1
    (coordinateOffNoise_nonneg i hu (fun y => abs_nonneg _) x)
  have hbound := coordinateOffNoise_abs_bound i hu (coordinatePairDifference i F) x
  have hb : -C ≤ B ∧ B ≤ C := by
    dsimp only [B, C]
    constructor
    · have h := mul_le_mul_of_nonneg_left hbound.1 hu.1
      nlinarith
    · exact mul_le_mul_of_nonneg_left hbound.2 hu.1
  have hfminus : noiseOperator u F (setBit i false x) = A - B := by
    rw [noiseOperator_setBit]
    dsimp [A, B]
    ring
  have hfplus : noiseOperator u F (setBit i true x) = A + B := by
    rw [noiseOperator_setBit]
    rfl
  have hsminus : noiseOperator u (sortCoordinate i F) (setBit i false x) = A - C := by
    rw [noiseOperator_setBit, coordinatePairMean_sortCoordinate, coordinatePairDifference_sortCoordinate]
    dsimp [A, C]
    ring
  have hsplus : noiseOperator u (sortCoordinate i F) (setBit i true x) = A + C := by
    rw [noiseOperator_setBit, coordinatePairMean_sortCoordinate, coordinatePairDifference_sortCoordinate]
    rfl
  have hsort := sortCoordinate_closed i hF
  have hminus : A - C ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [← hsminus]
    exact noiseOperator_bounds hu.1 hu.2 hsort _
  have hplus : A + C ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [← hsplus]
    exact noiseOperator_bounds hu.1 hu.2 hsort _
  rw [hfminus, hfplus, hsminus, hsplus]
  simpa only [add_comm] using psi_symmetric_pair_mono A B C hc hb hminus hplus

theorem cubeAverage_psi_noise_sortCoordinate_closed (i : Fin n) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) {F : Cube n → ℝ} (hF : ∀ x, F x ∈ Icc (-1 : ℝ) 1) :
    cubeAverage (fun x => psi (noiseOperator u F x)) ≤
      cubeAverage (fun x => psi (noiseOperator u (sortCoordinate i F) x)) := by
  have h := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Cube n))) =>
    psi_noise_sortCoordinate_pair_closed i hu hF x)
  rw [sum_setBit_pair i (fun x => psi (noiseOperator u F x)),
    sum_setBit_pair i (fun x => psi (noiseOperator u (sortCoordinate i F) x))] at h
  have hs : (∑ x, psi (noiseOperator u F x)) ≤
      ∑ x, psi (noiseOperator u (sortCoordinate i F) x) := by linarith
  exact div_le_div_of_nonneg_right hs (cube_denominator_pos n).le

theorem informationDeficit_noise_sortCoordinate_closed (i : Fin n) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) {F : Cube n → ℝ} (hF : ∀ x, F x ∈ Icc (-1 : ℝ) 1) :
    informationDeficit (noiseOperator u F) ≤
      informationDeficit (noiseOperator u (sortCoordinate i F)) := by
  rw [informationDeficit_eq_psi_difference, informationDeficit_eq_psi_difference,
    cubeAverage_noiseOperator, cubeAverage_noiseOperator, cubeAverage_sortCoordinate]
  exact sub_le_sub_right (cubeAverage_psi_noise_sortCoordinate_closed i hu hF) _

theorem sortCoordinates_interior (is : List (Fin n)) {F : Cube n → ℝ}
    (hF : IsInterior F) : IsInterior (sortCoordinates is F) := by
  induction is generalizing F with
  | nil => exact hF
  | cons i is ih => exact ih (sortCoordinate_interior i hF)

theorem cubeAverage_comp_sortCoordinates (is : List (Fin n)) (F : Cube n → ℝ) (h : ℝ → ℝ) :
    cubeAverage (fun x => h (sortCoordinates is F x)) = cubeAverage (fun x => h (F x)) := by
  induction is generalizing F with
  | nil => rfl
  | cons i is ih => rw [sortCoordinates, ih, cubeAverage_comp_sortCoordinate]

theorem informationDeficit_noise_sortCoordinates_closed (is : List (Fin n)) {u : ℝ}
    (hu : u ∈ Icc 0 1) {F : Cube n → ℝ} (hF : ∀ x, F x ∈ Icc (-1 : ℝ) 1) :
    informationDeficit (noiseOperator u F) ≤
      informationDeficit (noiseOperator u (sortCoordinates is F)) := by
  induction is generalizing F with
  | nil => exact le_rfl
  | cons i is ih =>
      exact (informationDeficit_noise_sortCoordinate_closed i hu hF).trans
        (ih (sortCoordinate_closed i hF))

theorem exists_increasing_dissipation_le (F : Cube n → ℝ) (hF : IsInterior F) :
    ∃ G : Cube n → ℝ, IsInterior G ∧ IsIncreasing G ∧
      (∀ h : ℝ → ℝ, cubeAverage (fun x => h (G x)) = cubeAverage (fun x => h (F x))) ∧
      dissipation G ≤ dissipation F := by
  classical
  let is : List (Fin n) := Finset.univ.toList
  let G := sortCoordinates is F
  have hG : IsInterior G := sortCoordinates_interior is hF
  have hlaw (h : ℝ → ℝ) : cubeAverage (fun x => h (G x)) =
      cubeAverage (fun x => h (F x)) := cubeAverage_comp_sortCoordinates is F h
  have hinc : IsIncreasing G := by
    apply isIncreasing_of_forall_increasingIn
    intro j
    apply sortCoordinates_increasingIn is j
    exact Or.inl (by simp [is])
  have heq : informationDeficit G = informationDeficit F := by
    unfold informationDeficit entropyAverage
    have hm : cubeAverage G = cubeAverage F := hlaw id
    rw [hlaw entropy, hm]
  let f : ℝ → ℝ := fun t =>
    informationDeficit (noiseFlow G t) - informationDeficit (noiseFlow F t)
  have hf0 : f 0 = 0 := by simp [f, noiseFlow_zero, heq]
  have hd : HasDerivAt f (dissipation F - dissipation G) 0 := by
    have h1 := hasDerivAt_informationDeficit_noiseFlow_of_isInterior G 0
      (by simpa only [noiseFlow_zero] using hG)
    have h2 := hasDerivAt_informationDeficit_noiseFlow_of_isInterior F 0
      (by simpa only [noiseFlow_zero] using hF)
    convert! h1.sub h2 using 1; simp [noiseFlow_zero]; ring
  have hnonneg (t : ℝ) (ht : 0 < t) : 0 ≤ f t := by
    have hu : Real.exp (-t) ∈ Icc (0 : ℝ) 1 :=
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩
    exact sub_nonneg.mpr (informationDeficit_noise_sortCoordinates_closed is hu
      (fun x => ⟨(hF x).1.le, (hF x).2.le⟩))
  have hderiv : 0 ≤ dissipation F - dissipation G := by
    apply ge_of_tendsto hd.tendsto_slope_zero_right
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [zero_add, hf0, sub_zero, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr ht.le) (hnonneg t ht)
  exact ⟨G, hG, hinc, hlaw, by linarith⟩

theorem all_soft_reserve {n : ℕ} (g : Cube n → ℝ) (hg : IsInterior g) :
    2 * informationDeficit g + meanVariance g * L (entropyAverage g / meanVariance g) ≤
      dissipation g := by
  obtain ⟨G, hG, hinc, hlaw, hD⟩ := exists_increasing_dissipation_le g hg
  have hmean : cubeAverage G = cubeAverage g := hlaw id
  have hent : entropyAverage G = entropyAverage g := hlaw entropy
  have hI : informationDeficit G = informationDeficit g := by
    simp only [informationDeficit, hent, hmean]
  have hv : meanVariance G = meanVariance g := by simp only [meanVariance, hmean]
  have h := monotone_dissipation G hG hinc
  rw [hI, hent, hv] at h
  exact h.trans hD

end LeanBlast.CourtadeKumar
end
end

end OAI

-- ---- from OAI.InformationTheory.SoftChannel.Joining ----
namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology
namespace LeanBlast.CourtadeKumar

lemma joiningCost_pair (c d : ℝ) : joiningCost (c+d) (c-d) = pairDissipation c d := by
  unfold joiningCost pairDissipation
  ring

lemma joiningCost_symm (a b : ℝ) : joiningCost a b = joiningCost b a := by
  unfold joiningCost; ring

end LeanBlast.CourtadeKumar
end
end

end OAI

-- ---- from OAI.InformationTheory.SoftChannel.Production ----
namespace OAI

section

noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace LeanBlast.CourtadeKumar

lemma IsInterior.neg_soft {n : ℕ} {g : Cube n → ℝ} (hg : IsInterior g) :
    IsInterior (fun x => -g x) := by
  intro x
  constructor <;> linarith [(hg x).1,(hg x).2]

lemma dissipation_neg_soft {n : ℕ} (g : Cube n → ℝ) (hg : IsInterior g) :
    dissipation (fun x => -g x)=dissipation g := by
  unfold dissipation cubeDerivative
  congr 1
  funext i
  congr 1
  funext x
  dsimp only
  rw [artanh_neg_interior (hg x)]
  ring

lemma IsInterior.information_lt_entropy {n : ℕ} {g : Cube n → ℝ} (hg : IsInterior g) :
    informationDeficit g < entropy (CourtadeKumar.cubeAverage g) := by
  unfold informationDeficit
  linarith [hg.entropyAverage_pos]

lemma IsInterior.information_mem {n : ℕ} {g : Cube n → ℝ} (hg : IsInterior g) :
    informationDeficit g ∈ Ico 0 ell :=
  ⟨informationDeficit_nonneg hg,hg.information_lt_entropy.trans_le (entropy_le_ell _)⟩

lemma r_pooled_child_information {n : ℕ} (A B : Cube n → ℝ)
    (hA : IsInterior A) (hB : IsInterior B) :
    r ((informationDeficit A+informationDeficit B)/2) ≤
      (r (informationDeficit A)+r (informationDeficit B))/2 := by
  have h := convexOn_r.2 hA.information_mem hB.information_mem
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simpa only [smul_eq_mul, ← add_div, one_div_mul_eq_div] using h

lemma ordered_positive_joining {n : ℕ} (A B : Cube n → ℝ)
    (hA : IsInterior A) (hB : IsInterior B) (horder : cubeAverage B ≤ cubeAverage A)
    (hm : 0 < (cubeAverage A+cubeAverage B)/2)
    (hI : entropy ((cubeAverage A+cubeAverage B)/2)-(entropyAverage A+entropyAverage B)/2 ≤ softCutoff) :
    r (entropy ((cubeAverage A+cubeAverage B)/2)-(entropyAverage A+entropyAverage B)/2) ≤
      (r (informationDeficit A)+r (informationDeficit B))/2+
        cubeAverage (fun x => joiningCost (A x) (B x)) := by
  let m := (cubeAverage A+cubeAverage B)/2
  let d := (cubeAverage A-cubeAverage B)/2
  let e := (entropyAverage A+entropyAverage B)/2
  have hd : 0 ≤ d := by dsimp [d]; linarith
  have ha : cubeAverage A=m+d := by dsimp [m,d]; ring
  have hb : cubeAverage B=m-d := by dsimp [m,d]; ring
  have herr : entropy m-e = entropy ((cubeAverage A+cubeAverage B)/2)-(entropyAverage A+entropyAverage B)/2 := rfl
  have hj : pairH m d-e=(informationDeficit A+informationDeficit B)/2 := by
    dsimp [pairH,informationDeficit,e]; rw [← ha,← hb]; ring
  have hp : e ≤ pairH m d := by
    have h1 := informationDeficit_nonneg hA
    have h2 := informationDeficit_nonneg hB
    nlinarith [hj]
  have hc : wallDemand m d e ≤ cubeAverage (fun x => joiningCost (A x) (B x)) := by
    rcases hd.eq_or_lt with hd | hd
    · have hd0 : d=0 := hd.symm
      simp only [wallDemand,hd0,pairH,add_zero,sub_zero,add_self_div_two,sub_self]
      exact cubeAverage_nonneg (fun x => joiningCost_nonneg (hA x) (hB x))
    · exact low_information_joining A B hA hB hm hd
        (by rw [← ha]; exact hA.cubeAverage.2) ha hb hp hI
  have hpool := r_pooled_child_information A B hA hB
  dsimp [wallDemand] at hc
  rw [hj] at hc
  linarith

lemma positive_joining {n : ℕ} (A B : Cube n → ℝ)
    (hA : IsInterior A) (hB : IsInterior B)
    (hm : 0 < (cubeAverage A+cubeAverage B)/2)
    (hI : entropy ((cubeAverage A+cubeAverage B)/2)-(entropyAverage A+entropyAverage B)/2 ≤ softCutoff) :
    r (entropy ((cubeAverage A+cubeAverage B)/2)-(entropyAverage A+entropyAverage B)/2) ≤
      (r (informationDeficit A)+r (informationDeficit B))/2+
        cubeAverage (fun x => joiningCost (A x) (B x)) := by
  rcases le_total (cubeAverage B) (cubeAverage A) with hab | hab
  · exact ordered_positive_joining A B hA hB hab hm hI
  · have h := ordered_positive_joining B A hB hA hab
      (by simpa only [add_comm] using hm) (by simpa only [add_comm] using hI)
    simpa only [add_comm, joiningCost_symm] using h

lemma all_soft_meanReserve {n : ℕ} (g : Cube n → ℝ) (hg : IsInterior g) :
    meanReserve (cubeAverage g) (informationDeficit g) ≤ dissipation g := by
  have h := all_soft_reserve g hg
  convert! h using 1
  simp only [meanReserve,meanVariance,informationDeficit]
  ring_nf

theorem all_soft_sharp_production {n : ℕ} (g : Cube n → ℝ) (hg : IsInterior g) :
    r (informationDeficit g) ≤ dissipation g := by
  induction n with
  | zero => simp only [informationDeficit_dim_zero,dissipation_dim_zero,r_zero]; exact le_rfl
  | succ n ih =>
    have positive (G : Cube (n+1) → ℝ) (hG : IsInterior G) (hm : 0 < cubeAverage G) :
        r (informationDeficit G) ≤ dissipation G := by
      by_cases hI : softCutoff ≤ informationDeficit G
      · exact (high_information_reserve (abs_lt.mpr hG.cubeAverage) hI hG.information_lt_entropy).trans
          (all_soft_meanReserve G hG)
      · have hj := positive_joining (restrict G true) (restrict G false)
          (hG.restrict true) (hG.restrict false)
          (by rwa [← cubeAverage_split])
          (by rw [← cubeAverage_split, ← entropyAverage_split]; exact (le_of_not_ge hI))
        have hc : (fun x => joiningCost (restrict G true x) (restrict G false x))=
            (fun x => pairDissipation (pairMean G x) (pairHalfDifference G x)) := by
          funext x
          rw [← pairMean_add_halfDifference G x,← pairMean_sub_halfDifference G x,joiningCost_pair]
        rw [← cubeAverage_split, ← entropyAverage_split,hc] at hj
        have ht := ih (restrict G true) (hG.restrict true)
        have hf := ih (restrict G false) (hG.restrict false)
        rw [dissipation_split]
        change r (entropy (cubeAverage G)-entropyAverage G) ≤ _
        linarith
    rcases lt_trichotomy 0 (cubeAverage g) with hm | hm | hm
    · exact positive g hg hm
    · have h := all_soft_meanReserve g hg
      rw [← hm,meanReserve_zero_mean hg.information_mem] at h
      exact h
    · have h := positive (fun x => -g x) hg.neg_soft (by rw [cubeAverage_neg]; linarith)
      rwa [informationDeficit_neg,dissipation_neg_soft g hg] at h

end LeanBlast.CourtadeKumar
end
end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter
open scoped BigOperators Topology


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.all_soft_sharp_production := @_root_.OAI.LeanBlast.CourtadeKumar.all_soft_sharp_production
