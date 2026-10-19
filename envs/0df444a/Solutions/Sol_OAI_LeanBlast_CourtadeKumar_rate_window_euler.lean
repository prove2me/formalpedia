-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.rate_window_euler
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:58:41.826632+00:00
-- url     : https://prove2.me/submissions/540d7030-fe0d-4c40-a1a0-740338f70dd3

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/SoftChannel/RateWindow.lean:L45-L72
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.rate_window_euler. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_curvatureNumerator_upper

-- ---- from OAI.InformationTheory.BooleanNoise.EntropyScalars ----
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

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

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.SoftChannel.Thinning ----
namespace OAI

section

noncomputable section
open Set
namespace SoftChannel204

theorem clipKernel_of_le {β v : ℝ} (h : v ≤ β) : clipKernel β v = 0 := by
  simp [clipKernel, max_eq_right (sub_nonpos.mpr h)]

theorem clipKernel_eq {β v : ℝ} (h : β ≤ v) :
    clipKernel β v = (v - β) / v ^ 2 := by
  rw [clipKernel, max_eq_left (sub_nonneg.mpr h)]

open MeasureTheory

theorem continuousAt_clipKernel (β : ℝ) {v : ℝ} (hv : 0 < v) :
    ContinuousAt (clipKernel β) v := by
  unfold clipKernel
  exact ((continuousAt_id.sub continuousAt_const).max continuousAt_const).div
    (continuousAt_id.pow 2) (pow_ne_zero _ hv.ne')

end SoftChannel204
end
end

end OAI

-- ---- from OAI.InformationTheory.SoftChannel.RateWindow ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace LeanBlast.CourtadeKumar
open SoftChannel204

lemma continuousAt_rSecondDeriv {s : ℝ} (hs : s ∈ Ioo (0:ℝ) ell) :
    ContinuousAt rSecondDeriv s := by
  have hu := psiInv_mem_Ioo hs
  have hi := continuousAt_psiInv hs
  have ht := (hasDerivAt_artanh ⟨by linarith [hu.1],hu.2⟩).continuousAt.comp hi
  have ht0 : Real.artanh (psiInv s) ≠ 0 := (Real.artanh_pos hu).ne'
  have hq0 : 1-(psiInv s)^2 ≠ 0 := by nlinarith [hu.1,hu.2]
  have hc := (((continuousAt_const (y := (1:ℝ))).add (hi.pow 2)).mul ht |>.sub hi).div
    (((continuousAt_const.sub (hi.pow 2)).pow 2).mul (ht.pow 3))
    (mul_ne_zero (pow_ne_zero _ hq0) (pow_ne_zero _ ht0))
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs.1] with x hx
  simp [rSecondDeriv,ite_eq_right (not_le.mpr (show 0<x from hx))]

lemma rate_window_point {u b : ℝ} (hu : u ∈ Ioo (0:ℝ) ell) :
    -(2/3:ℝ)*clipKernel b (ell-u) ≤ (u-(ell-b))*rSecondDeriv u := by
  have hsec := (rSecondDeriv_pos hu).le
  have hs : 0 < ell-u := by linarith [hu.2]
  by_cases h : ell-u ≤ b
  · rw [clipKernel_of_le h,mul_zero]
    exact mul_nonneg (by linarith) hsec
  · have hb : b < ell-u := lt_of_not_ge h
    rw [clipKernel_eq hb.le]
    have hupper : rSecondDeriv u ≤ (2/3:ℝ)/(ell-u)^2 := by
      exact (le_div_iff₀ (sq_pos_of_pos hs)).mpr (by
        simpa only [mul_comm] using inverseEntropy_curvature_bound hu)
    have hm := mul_le_mul_of_nonneg_left hupper (show 0 ≤ ell-u-b by linarith)
    convert! neg_le_neg hm using 1 <;> ring

lemma rate_window_euler {v I b k : ℝ} (hv : 0 < v) (hvI : v ≤ I) (hI : I < ell)
    (hk : 0 ≤ k)
    (hwindow : (∫ h in (ell-I)..(ell-v), clipKernel b h) ≤ 3*k) :
    0 ≤ ((I-(ell-b))*rDeriv I-r I)-((v-(ell-b))*rDeriv v-r v)+rDeriv v*k := by
  have hdom : ∀ u ∈ uIcc v I, u ∈ Ioo (0:ℝ) ell := by
    intro u hu
    rw [uIcc_of_le hvI] at hu
    exact ⟨hv.trans_le hu.1,hu.2.trans_lt hI⟩
  have hfc : ContinuousOn (fun u => (u-(ell-b))*rSecondDeriv u) (uIcc v I) := by
    intro u hu
    exact ((continuousAt_id.sub continuousAt_const).mul
      (continuousAt_rSecondDeriv (hdom u hu))).continuousWithinAt
  have hkc : ContinuousOn (fun u => -(2/3:ℝ)*clipKernel b (ell-u)) (uIcc v I) := by
    intro u hu
    exact (continuousAt_const.mul ((continuousAt_clipKernel b (by dsimp; linarith [(hdom u hu).2])).comp
      (continuousAt_const.sub continuousAt_id))).continuousWithinAt
  have hder : ∀ u ∈ uIcc v I,
      HasDerivAt (fun z => (z-(ell-b))*rDeriv z-r z) ((u-(ell-b))*rSecondDeriv u) u := by
    intro u hu
    convert! (((hasDerivAt_id u).sub_const (ell-b)).mul (hasDerivAt_rDeriv (hdom u hu))).sub
      (hasDerivAt_r (hdom u hu)) using 1; dsimp; ring
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hfc.intervalIntegrable
  have hcomp := intervalIntegral.integral_mono_on (μ := volume) hvI hkc.intervalIntegrable hfc.intervalIntegrable
    (fun u hu => rate_window_point (hdom u (by rwa [uIcc_of_le hvI])))
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left] at hcomp
  rw [heq] at hcomp
  have hsl := mul_le_mul_of_nonneg_right (rDeriv_ge_two hv.le (hvI.trans_lt hI)) hk
  nlinarith

end LeanBlast.CourtadeKumar
end
end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter MeasureTheory
open scoped Topology
open SoftChannel204


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.rate_window_euler := @_root_.OAI.LeanBlast.CourtadeKumar.rate_window_euler
