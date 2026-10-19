-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.convexOn_L
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:21:09.077765+00:00
-- url     : https://prove2.me/submissions/c60244f8-f6ed-4a20-af04-7dde21b19d4c

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/LShape.lean:L32-L55
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.convexOn_L. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_ComparisonEstimates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_hasDerivAt_artanh
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_hasDerivAt_psi
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_hasDerivAt_rDeriv
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_rDeriv_ge_two

-- ---- from OAI.InformationTheory.BooleanNoise.EntropyScalars ----
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem ell_pos : 0 < ell := Real.log_pos (by norm_num)

theorem artanh_eq_log_sub {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    Real.artanh v = (Real.log (1 + v) - Real.log (1 - v)) / 2 := by
  rw [Real.artanh_eq_half_log ⟨hv.1.le, hv.2.le⟩,
    Real.log_div (by linarith [hv.1]) (by linarith [hv.2])]
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

theorem continuousOn_rGap : ContinuousOn rGap (Ico 0 ell) :=
  continuousOn_r.sub (continuous_const.mul continuous_id).continuousOn

theorem hasDerivAt_rGap {s : ℝ} (hs : s ∈ Ioo 0 ell) :
    HasDerivAt rGap (rDeriv s - 2) s := by
  convert! (hasDerivAt_r hs).sub ((hasDerivAt_id s).const_mul 2) using 1
  simp

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

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.convexOn_L := @_root_.OAI.LeanBlast.CourtadeKumar.convexOn_L
