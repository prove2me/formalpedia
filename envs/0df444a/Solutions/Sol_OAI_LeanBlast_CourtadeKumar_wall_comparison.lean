-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.wall_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:07:37.471514+00:00
-- url     : https://prove2.me/submissions/c8a9e6e4-b68f-4f9b-8a88-4c667df622fc

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/SoftChannel/Wall.lean:L181-L203
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.wall_comparison. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_hasDerivAt_pairEntropyGap

-- ---- from OAI.InformationTheory.BooleanNoise.EntropyScalars ----
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem psi_nonneg (v : ℝ) : 0 ≤ psi v := by
  have h := Real.binEntropy_le_log_two (p := (1 + v) / 2)
  rw [← entropy_eq_binEntropy] at h
  unfold entropy ell at *
  linarith

theorem entropy_le_ell (v : ℝ) : entropy v ≤ ell := by
  exact sub_le_self _ (psi_nonneg v)

theorem entropy_pos {v : ℝ} (hv : v ∈ Ioo (-1) 1) : 0 < entropy v := by
  rw [entropy_eq_binEntropy]
  exact Real.binEntropy_pos (by linarith [hv.1]) (by linarith [hv.2])

theorem psi_lt_ell {v : ℝ} (hv : v ∈ Ioo (-1) 1) : psi v < ell := by
  have := entropy_pos hv
  unfold entropy at this
  linarith

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

theorem hasSum_artanh {v : ℝ} (hv : |v| < 1) :
    HasSum (fun k : ℕ => v ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) (Real.artanh v) := by
  have h := (Real.hasSum_log_sub_log_of_abs_lt_one hv).mul_left (1 / 2)
  convert! h using 1
  · ext k
    ring
  · rw [artanh_eq_log_sub (abs_lt.mp hv)]
    ring

theorem sum_range_artanh_le {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (m : ℕ) :
    (∑ k ∈ Finset.range m, v ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) ≤ Real.artanh v := by
  have h := hasSum_artanh (show |v| < 1 by rwa [abs_of_nonneg hv0])
  rw [← h.tsum_eq]
  exact h.summable.sum_le_tsum (Finset.range m) (fun k hk => by positivity)

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.ArtanhBounds ----
namespace OAI

namespace LeanBlast.CourtadeKumar

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

theorem psi_pos_of_pos {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) : 0 < psi u := by
  simpa only [psi_zero] using
    strictMonoOn_psi (show (0 : ℝ) ∈ Icc 0 1 by norm_num) ⟨hu.le, hu1⟩ hu

theorem rDeriv_psi {u : ℝ} (hu : u ∈ Ioo 0 1) :
    rDeriv (psi u) = 1 + u / ((1 - u ^ 2) * Real.artanh u) := by
  simp only [rDeriv, ite_eq_right (not_le.mpr (psi_pos_of_pos hu.1 hu.2.le)),
    psiInv_psi ⟨hu.1.le, hu.2.le⟩]

theorem rSecondDeriv_psi {u : ℝ} (hu : u ∈ Ioo 0 1) :
    rSecondDeriv (psi u) = ((1 + u ^ 2) * Real.artanh u - u) /
      ((1 - u ^ 2) ^ 2 * (Real.artanh u) ^ 3) := by
  simp only [rSecondDeriv, ite_eq_right (not_le.mpr (psi_pos_of_pos hu.1 hu.2.le)),
    psiInv_psi ⟨hu.1.le, hu.2.le⟩]

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

theorem pairEntropyGap_nonneg (a b : ℝ) (h : |a| + |b| < 1) :
    0 ≤ pairEntropyGap a b := by
  rw [pairEntropyGap_weighted a b h]
  exact add_nonneg
    (mul_nonneg (by linarith [pair_denom_add_pos a b h]) (psi_nonneg _))
    (mul_nonneg (by linarith [pair_denom_sub_pos a b h]) (psi_nonneg _))

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.SoftChannel.HighReserve ----
namespace OAI

section

noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace LeanBlast.CourtadeKumar

lemma softCutoff_lt_ell : softCutoff < ell := psi_lt_ell (by norm_num)

end LeanBlast.CourtadeKumar
end
end

end OAI

-- ---- from OAI.InformationTheory.SoftChannel.RateSlope ----
namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace LeanBlast.CourtadeKumar

lemma RateSlope_slopeBernstein_pos (i : Fin 10) : 0 < RateSlope_slopeBernstein i := by
  fin_cases i <;> norm_num [RateSlope_slopeBernstein]

lemma slopePolynomial_bernstein (t : ℝ) :
    slopePolynomial ((3/5)*t) = bernsteinSum 9 RateSlope_slopeBernstein t := by
  unfold bernsteinSum
  simp_rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [slopePolynomial,slopeT,curvatureN,RateSlope_slopeBernstein,Fin.sum_univ_succ,
    Nat.descFactorial,Nat.factorial]
  ring

lemma slopePolynomial_pos {z : ℝ} (hz : z ∈ Icc 0 (3/5:ℝ)) : 0 < slopePolynomial z := by
  have h := bernsteinSum_pos 9 RateSlope_slopeBernstein RateSlope_slopeBernstein_pos (by linarith [hz.1] : 0 ≤ (5/3:ℝ)*z)
    (by linarith [hz.2] : (5/3:ℝ)*z ≤ 1)
  rw [← slopePolynomial_bernstein] at h
  convert! h using 1; congr 1; ring

lemma slopeT_lower {u : ℝ} (hu : u ∈ Ioo 0 1) : u*slopeT (u^2) ≤ Real.artanh u := by
  have h := sum_range_artanh_le hu.1.le hu.2 3
  norm_num [Finset.sum_range_succ] at h
  convert! h using 1; unfold slopeT; ring

lemma r_slope_bound_psi {u : ℝ} (hu : u ∈ Ioo 0 1) (hu2 : u^2 ≤ (3/5:ℝ)) :
    rSecondDeriv (psi u) < 2*rDeriv (psi u) := by
  have ha : 0 < 1-u^2 := by linarith
  have hv := Real.artanh_pos hu
  have ht : 0 < slopeT (u^2) := by unfold slopeT; positivity
  have hT := slopeT_lower hu
  have hN := curvatureNumerator_upper hu.1 hu.2
  have hP := slopePolynomial_pos ⟨sq_nonneg u,hu2⟩
  unfold slopePolynomial at hP
  have hn := (div_le_iff₀ (pow_pos hu.1 3)).mp hN
  have hn' := (mul_le_mul_of_nonneg_right hn ha.le)
  have hcancel : (curvatureN (u^2)/(1-u^2)*u^3)*(1-u^2) = curvatureN (u^2)*u^3 := by field_simp
  rw [hcancel] at hn'
  have hc := mul_pos hP (pow_pos hu.1 3)
  have hp2 := pow_le_pow_left₀ (mul_pos hu.1 ht).le hT 2
  have hp3 := pow_le_pow_left₀ (mul_pos hu.1 ht).le hT 3
  have hm2 := mul_le_mul_of_nonneg_left hp2 (show 0 ≤ 2*(1-u^2)^2*u by exact mul_nonneg (by positivity) hu.1.le)
  have hm3 := mul_le_mul_of_nonneg_left hp3 (show 0 ≤ 2*(1-u^2)^3 by positivity)
  rw [rSecondDeriv_psi hu,rDeriv_psi hu]
  apply (div_lt_iff₀ (mul_pos (sq_pos_of_pos ha) (pow_pos hv 3))).mpr
  have hden : (1+u/((1-u^2)*Real.artanh u))*((1-u^2)^2*Real.artanh u^3) =
    (1-u^2)^2*Real.artanh u^3+u*(1-u^2)*Real.artanh u^2 := by field_simp
  rw [mul_assoc,hden]
  have hcore : ((1+u^2)*Real.artanh u-u)*(1-u^2) <
      (2*((1-u^2)^2*Real.artanh u^3+u*(1-u^2)*Real.artanh u^2))*(1-u^2) := by
    nlinarith
  exact (mul_lt_mul_iff_left₀ ha).mp (by simpa only [mul_comm (1-u^2)] using hcore)

lemma r_slope_bound {I : ℝ} (hI : I ∈ Icc 0 softCutoff) : rSecondDeriv I < 2*rDeriv I := by
  rcases hI.1.eq_or_lt with rfl | hI0
  · norm_num
  have hIL := hI.2.trans_lt softCutoff_lt_ell
  have hu := psiInv_mem_Ioo ⟨hI0,hIL⟩
  have hule : psiInv I ≤ (77/100:ℝ) := by
    apply (strictMonoOn_psi.le_iff_le ⟨hu.1.le,hu.2.le⟩ (by norm_num)).mp
    rw [psi_psiInv hI0.le hIL]; exact hI.2
  have h := r_slope_bound_psi hu (by nlinarith [hu.1])
  rwa [psi_psiInv hI0.le hIL] at h

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

lemma entropySlopeAux_neg {u : ℝ} (hu : u ∈ Ioo (-1) 1) : entropySlopeAux (-u) = entropySlopeAux u := by
  simp [entropySlopeAux,artanh_neg_interior hu]

lemma hasDerivAt_entropySlopeAux {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    HasDerivAt entropySlopeAux (2*(u-(1-u^2)*Real.artanh u)/(1-u^2)^2) u := by
  have hd : 1-u^2 ≠ 0 := by nlinarith [hu.1,hu.2]
  have h := ((hasDerivAt_const u (1:ℝ)).div (((hasDerivAt_id u).pow 2).const_sub 1) hd).sub
    ((hasDerivAt_artanh hu).pow 2)
  convert! h using 1; dsimp [entropySlopeAux]; field_simp; ring

lemma monotoneOn_entropySlopeAux : MonotoneOn entropySlopeAux (Ico 0 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := fun u => 2*(u-(1-u^2)*Real.artanh u)/(1-u^2)^2) (convex_Ico _ _)
  · intro u hu
    exact (hasDerivAt_entropySlopeAux ⟨by linarith [hu.1],hu.2⟩).continuousAt.continuousWithinAt
  · intro u hu
    simp only [interior_Ico,mem_Ioo] at hu
    exact (hasDerivAt_entropySlopeAux ⟨by linarith [hu.1],hu.2⟩).hasDerivWithinAt
  · intro u hu
    simp only [interior_Ico,mem_Ioo] at hu
    exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (one_sub_sq_mul_artanh_le_self ⟨hu.1.le,hu.2⟩))) (sq_nonneg _)

lemma wall_domain {m d : ℝ} (hm : 0 ≤ m) (hd : 0 ≤ d) (hmd : m+d < 1) : |m|+|d|<1 := by
  rwa [abs_of_nonneg hm,abs_of_nonneg hd]

lemma wallA_nonneg {m d : ℝ} (hm : 0 ≤ m) (hd : 0 ≤ d) (hmd : m+d < 1) : 0 ≤ wallA m d := by
  have hh := wall_domain hm hd hmd
  have hp := pair_add_mem_Ioo m d hh
  have hn := pair_sub_mem_Ioo m d hh
  have h := Real.strictMonoOn_artanh.monotoneOn
    (show -(m-d) ∈ Ioo (-1) 1 by constructor <;> linarith [hn.1,hn.2]) hp (by linarith : -(m-d) ≤ m+d)
  rw [artanh_neg_interior hn] at h
  unfold wallA; linarith

lemma wallC_nonneg {m d : ℝ} (hm : 0 ≤ m) (hd : 0 ≤ d) (hmd : m+d < 1) : 0 ≤ wallC m d := by
  have hh := wall_domain hm hd hmd
  have h := Real.strictMonoOn_artanh.monotoneOn (pair_sub_mem_Ioo m d hh) (pair_add_mem_Ioo m d hh)
    (by linarith : m-d ≤ m+d)
  unfold wallC; linarith

lemma wallADeriv_lower {m d : ℝ} (hm : 0 ≤ m) (hd : 0 ≤ d) (hmd : m+d < 1) :
    2*wallA m d*wallC m d ≤ wallADeriv m d := by
  have hh := wall_domain hm hd hmd
  have hn := pair_sub_mem_Ioo m d hh
  have h := monotoneOn_entropySlopeAux
    (show |m-d| ∈ Ico 0 1 by exact ⟨abs_nonneg _,by rw [abs_lt]; exact hn⟩)
    (show m+d ∈ Ico 0 1 by exact ⟨by linarith,hmd⟩)
    (show |m-d| ≤ m+d by rw [abs_le]; constructor <;> linarith)
  have he : entropySlopeAux |m-d| = entropySlopeAux (m-d) := by
    rcases le_total 0 (m-d) with hpos | hneg
    · rw [abs_of_nonneg hpos]
    · rw [abs_of_nonpos hneg,entropySlopeAux_neg hn]
  rw [he] at h
  dsimp [entropySlopeAux,wallA,wallC,wallADeriv] at *
  nlinarith

lemma hasDerivAt_wallA_d {m d : ℝ} (hh : |m|+|d|<1) :
    HasDerivAt (wallA m) (wallADeriv m d) d := by
  have h := (((hasDerivAt_artanh (pair_add_mem_Ioo m d hh)).comp d
    ((hasDerivAt_id d).const_add m)).add ((hasDerivAt_artanh (pair_sub_mem_Ioo m d hh)).comp d
    ((hasDerivAt_id d).const_sub m))).div_const 2
  convert! h using 1; dsimp [wallA,wallADeriv]; ring

lemma hasDerivAt_pairH_d {m d : ℝ} (hh : |m|+|d|<1) :
    HasDerivAt (pairH m) (-wallC m d) d := by
  have h := (hasDerivAt_pairEntropyGap m d hh).const_sub (entropy m)
  convert! h using 1
  ext t; dsimp [pairH,pairEntropyGap]; ring

lemma hasDerivAt_pairH_m {m d : ℝ} (hh : |m|+|d|<1) :
    HasDerivAt (fun x => pairH x d) (-wallA m d) m := by
  have h := (((hasDerivAt_entropy (pair_add_mem_Ioo m d hh)).comp m
    ((hasDerivAt_id m).add_const d)).add ((hasDerivAt_entropy (pair_sub_mem_Ioo m d hh)).comp m
    ((hasDerivAt_id m).sub_const d))).div_const 2
  convert! h using 1; dsimp [pairH,wallA]; ring

lemma pairH_antitone_d {m d : ℝ} (hm : 0 ≤ m) (_hd : 0 ≤ d) (hmd : m+d<1) :
    AntitoneOn (pairH m) (Icc 0 d) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => -wallC m t) (convex_Icc _ _)
  · intro t ht
    exact (hasDerivAt_pairH_d (wall_domain hm ht.1 (by linarith [ht.2]))).continuousAt.continuousWithinAt
  · intro t ht
    simp only [interior_Icc,mem_Ioo] at ht
    exact (hasDerivAt_pairH_d (wall_domain hm ht.1.le (by linarith [ht.2]))).hasDerivWithinAt
  · intro t ht
    simp only [interior_Icc,mem_Ioo] at ht
    exact neg_nonpos.mpr (wallC_nonneg hm ht.1.le (by linarith [ht.2]))

lemma pairH_le_entropy {m d : ℝ} (hm : 0 ≤ m) (hd : 0 ≤ d) (hmd : m+d<1) :
    pairH m d ≤ entropy m := by
  have h := pairEntropyGap_nonneg m d (wall_domain hm hd hmd)
  dsimp [pairEntropyGap,pairH] at *
  linarith

lemma rate_entropy_slope {m d e : ℝ} (hm : 0 ≤ m) (hd : 0 ≤ d) (hmd : m+d<1)
    (he : 0 < e) (hj : e < pairH m d) (hI : entropy m-e ≤ softCutoff) :
    rDeriv (entropy m-e)*Real.artanh m ≤ rDeriv (pairH m d-e)*wallA m d := by
  have hdom (t : ℝ) (ht : t ∈ Icc 0 d) : |m|+|t|<1 :=
    wall_domain hm ht.1 (by linarith [ht.2])
  have hjdom (t : ℝ) (ht : t ∈ Icc 0 d) : pairH m t-e ∈ Ioo 0 ell := by
    have ha := pairH_antitone_d hm hd hmd ht ⟨hd,le_rfl⟩ ht.2
    have hb := pairH_le_entropy hm ht.1 (by linarith [ht.2])
    constructor <;> linarith [entropy_le_ell m]
  have hjcut (t : ℝ) (ht : t ∈ Icc 0 d) : pairH m t-e ≤ softCutoff := by
    linarith [pairH_le_entropy hm ht.1 (by linarith [ht.2])]
  let f := fun t => rDeriv (pairH m t-e)*wallA m t
  let f' := fun t => -rSecondDeriv (pairH m t-e)*wallC m t*wallA m t+
      rDeriv (pairH m t-e)*wallADeriv m t
  have hf (t : ℝ) (ht : t ∈ Icc 0 d) : HasDerivAt f (f' t) t := by
    have h := (((hasDerivAt_rDeriv (hjdom t ht)).comp t
      ((hasDerivAt_pairH_d (hdom t ht)).sub_const e)).mul (hasDerivAt_wallA_d (hdom t ht)))
    convert! h using 1; dsimp [f,f']; ring
  have hf' (t : ℝ) (ht : t ∈ Icc 0 d) : 0 ≤ f' t := by
    have hs := r_slope_bound ⟨(hjdom t ht).1.le,hjcut t ht⟩
    have ha := wallA_nonneg hm ht.1 (by linarith [ht.2])
    have hc := wallC_nonneg hm ht.1 (by linarith [ht.2])
    have hb := wallADeriv_lower hm ht.1 (by linarith [ht.2])
    have hr := rDeriv_ge_two (hjdom t ht).1.le (hjdom t ht).2
    have h1 := mul_le_mul_of_nonneg_right hs.le (mul_nonneg hc ha)
    have h2 := mul_le_mul_of_nonneg_left hb (show 0 ≤ rDeriv (pairH m t-e) by linarith)
    dsimp [f']; nlinarith
  have hmono : MonotoneOn f (Icc 0 d) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := f') (convex_Icc _ _)
    · intro t ht; exact (hf t ht).continuousAt.continuousWithinAt
    · intro t ht; exact (hf t (interior_subset ht)).hasDerivWithinAt
    · intro t ht; exact hf' t (interior_subset ht)
  have h := hmono ⟨le_rfl,hd⟩ ⟨hd,le_rfl⟩ hd
  simpa [f,pairH,wallA] using h

lemma hasDerivAt_wallDemand {m d e : ℝ} (hm : 0 ≤ m) (hd : 0 ≤ d) (hmd : m+d<1)
    (he : 0 < e) (hj : e < pairH m d) :
    HasDerivAt (fun x => wallDemand x d e) (wallDemandDeriv m d e) m := by
  have hp := pairH_le_entropy hm hd hmd
  have hI : entropy m-e ∈ Ioo 0 ell := by constructor <;> linarith [entropy_le_ell m]
  have hJ : pairH m d-e ∈ Ioo 0 ell := by constructor <;> linarith [entropy_le_ell m]
  have hh := wall_domain hm hd hmd
  have h := (((hasDerivAt_r hI).comp m
    ((hasDerivAt_entropy (pair_mean_mem_Ioo m d hh)).sub_const e)).sub
    ((hasDerivAt_r hJ).comp m ((hasDerivAt_pairH_m hh).sub_const e)))
  convert! h using 1; dsimp [wallDemand,wallDemandDeriv]; ring

lemma pairH_antitone_m {m d : ℝ} (_hm : 0 ≤ m) (hd : 0 ≤ d) (hmd : m+d<1) :
    AntitoneOn (fun x => pairH x d) (Icc 0 m) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => -wallA t d) (convex_Icc _ _)
  · intro t ht
    exact (hasDerivAt_pairH_m (wall_domain ht.1 hd (by linarith [ht.2]))).continuousAt.continuousWithinAt
  · intro t ht
    simp only [interior_Icc,mem_Ioo] at ht
    exact (hasDerivAt_pairH_m (wall_domain ht.1.le hd (by linarith [ht.2]))).hasDerivWithinAt
  · intro t ht
    simp only [interior_Icc,mem_Ioo] at ht
    exact neg_nonpos.mpr (wallA_nonneg ht.1.le hd (by linarith [ht.2]))

lemma wall_comparison {m w d e : ℝ} (hm : 0 ≤ m) (hmw : m ≤ w) (hd : 0 ≤ d) (hwd : w+d<1)
    (he : 0 < e) (hj : e < pairH w d) (hI : entropy m-e ≤ softCutoff) :
    wallDemand m d e ≤ wallDemand w d e := by
  have hdom (t : ℝ) (ht : t ∈ Icc m w) : 0 ≤ t ∧ t+d<1 ∧ e < pairH t d := by
    have h := pairH_antitone_m (hm.trans hmw) hd hwd ⟨hm.trans ht.1,ht.2⟩ ⟨hm.trans hmw,le_rfl⟩ ht.2
    exact ⟨hm.trans ht.1,by linarith [ht.2],hj.trans_le h⟩
  have hcut (t : ℝ) (ht : t ∈ Icc m w) : entropy t-e ≤ softCutoff := by
    have h := strictMonoOn_psi.monotoneOn (show m ∈ Icc 0 1 by constructor; exact hm; linarith)
      (show t ∈ Icc 0 1 by constructor; exact hm.trans ht.1; linarith [ht.2]) ht.1
    dsimp [entropy] at *; linarith
  have hmono : MonotoneOn (fun x => wallDemand x d e) (Icc m w) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => wallDemandDeriv t d e) (convex_Icc _ _)
    · intro t ht
      obtain ⟨ht0,htd,htj⟩ := hdom t ht
      exact (hasDerivAt_wallDemand ht0 hd htd he htj).continuousAt.continuousWithinAt
    · intro t ht
      obtain ⟨ht0,htd,htj⟩ := hdom t (interior_subset ht)
      exact (hasDerivAt_wallDemand ht0 hd htd he htj).hasDerivWithinAt
    · intro t ht
      obtain ⟨ht0,htd,htj⟩ := hdom t (interior_subset ht)
      have h := rate_entropy_slope ht0 hd htd he htj (hcut t (interior_subset ht))
      unfold wallDemandDeriv; linarith
  exact hmono ⟨le_rfl,hmw⟩ ⟨hmw,le_rfl⟩ hmw

end LeanBlast.CourtadeKumar
end
end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.wall_comparison := @_root_.OAI.LeanBlast.CourtadeKumar.wall_comparison
