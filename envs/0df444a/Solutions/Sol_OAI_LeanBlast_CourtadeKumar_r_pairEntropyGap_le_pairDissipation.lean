-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.r_pairEntropyGap_le_pairDissipation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:35:14.624181+00:00
-- url     : https://prove2.me/submissions/89eb2291-456c-4c07-bbce-69fbe8b32c67

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/PairEntropy.lean:L253-L265
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.r_pairEntropyGap_le_pairDissipation. The node keeps its source
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

theorem r_psi_nonneg {u : ℝ} (hu : u ∈ Icc 0 1) :
    r (psi u) = u * Real.artanh u := by rw [r, psiInv_psi hu]

theorem r_psi {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    r (psi u) = u * Real.artanh u := by
  by_cases h0 : 0 ≤ u
  · exact r_psi_nonneg ⟨h0, hu.2.le⟩
  · have hn : -u ∈ Ioo (-1) 1 := by constructor <;> linarith [hu.1, hu.2]
    have hodd : Real.artanh (-u) = -Real.artanh u := by
      rw [artanh_eq_log_sub hn, artanh_eq_log_sub hu]
      simp only [sub_eq_add_neg, neg_neg]
      ring
    calc
      r (psi u) = r (psi (-u)) := by rw [psi_neg]
      _ = (-u) * Real.artanh (-u) := r_psi_nonneg ⟨by linarith, hn.2.le⟩
      _ = u * Real.artanh u := by rw [hodd]; ring

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

theorem self_le_artanh {u : ℝ} (hu : u ∈ Set.Ico 0 1) : u ≤ Real.artanh u := by
  simpa using sum_range_artanh_le hu.1 hu.2 1

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

theorem pairDissipation_weighted_r (a b : ℝ) (h : |a| + |b| < 1) :
    pairDissipation a b =
      (1 + a) / 2 * r (psi (b / (1 + a))) +
        (1 - a) / 2 * r (psi (b / (1 - a))) := by
  rw [r_psi (pair_ratio_add_mem_Ioo a b h), r_psi (pair_ratio_sub_mem_Ioo a b h)]
  exact pairDissipation_weighted a b h

theorem r_pairEntropyGap_le_pairDissipation (a b : ℝ) (h : |a| + |b| < 1) :
    r (pairEntropyGap a b) ≤ pairDissipation a b := by
  have hp := pair_ratio_add_mem_Ioo a b h
  have hm := pair_ratio_sub_mem_Ioo a b h
  have hJ := convexOn_r.2
    (show psi (b / (1 + a)) ∈ Set.Ico 0 ell from ⟨psi_nonneg _, psi_lt_ell hp⟩)
    (show psi (b / (1 - a)) ∈ Set.Ico 0 ell from ⟨psi_nonneg _, psi_lt_ell hm⟩)
    (show 0 ≤ (1 + a) / 2 by linarith [pair_denom_add_pos a b h])
    (show 0 ≤ (1 - a) / 2 by linarith [pair_denom_sub_pos a b h])
    (show (1 + a) / 2 + (1 - a) / 2 = 1 by ring)
  simp only [smul_eq_mul] at hJ
  rw [← pairEntropyGap_weighted a b h] at hJ
  exact hJ.trans_eq (pairDissipation_weighted_r a b h).symm

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.r_pairEntropyGap_le_pairDissipation := @_root_.OAI.LeanBlast.CourtadeKumar.r_pairEntropyGap_le_pairDissipation
