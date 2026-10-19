-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.rSecondDeriv_le_inv_ell
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:19:12.432549+00:00
-- url     : https://prove2.me/submissions/22a6474a-a261-4024-bec7-63dd46bcd3d2

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/CurvatureBounds.lean:L104-L119
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.rSecondDeriv_le_inv_ell. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_artanh_le_cubic_tail

-- ---- from OAI.InformationTheory.BooleanNoise.EntropyScalars ----
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

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

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.CurvatureCertificates ----
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

theorem two_lt_exp_347_div_500 : (2 : ℝ) < Real.exp (347 / 500) := by
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 347 / 500) 5)
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem ell_lt_347_div_500 : ell < 347 / 500 :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).mpr two_lt_exp_347_div_500

theorem ten_sevenths_lt_inv_ell : (10 / 7 : ℝ) < 1 / ell := by
  have hpos : 0 < ell := Real.log_pos (by norm_num)
  apply (lt_div_iff₀ hpos).mpr
  have h := ell_lt_347_div_500
  linarith

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.InverseScalars ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

theorem s0_lt_ell : s0 < ell := psi_lt_ell (by norm_num)

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

-- ---- from OAI.InformationTheory.BooleanNoise.SmallCurvatureAux ----
namespace OAI

namespace LeanBlast.CourtadeKumar

theorem cubic_le_artanh {u : ℝ} (hu : u ∈ Set.Ico 0 1) :
    u + u ^ 3 / 3 ≤ Real.artanh u := by
  have h := sum_range_artanh_le hu.1 hu.2 2
  norm_num [Finset.sum_range_succ] at h
  exact h

end LeanBlast.CourtadeKumar

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.CurvatureBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

private theorem smallCoarseBound_lt_ten_sevenths {z : ℝ}
    (hz0 : 0 ≤ z) (hz25 : z ≤ 1 / 25) : smallCoarseBound z < 10 / 7 := by
  have hz1 : 0 < 1 - z := by linarith
  have hratio : z / (1 - z) ≤ 1 / 24 := (div_le_iff₀ hz1).mpr (by linarith)
  have hnum : (4 / 3 : ℝ) + (2 / 3) * (z / (1 - z)) ≤ 49 / 36 := by linarith
  have hzsq : z ^ 2 ≤ 1 / 625 := by
    nlinarith [mul_nonneg hz0 (show 0 ≤ 1 / 25 - z by linarith)]
  have hcube : 1 + z ≤ (1 + z / 3) ^ 3 := by
    nlinarith [sq_nonneg z, pow_nonneg hz0 3]
  have hbase : (599 / 625 : ℝ) ≤ (1 - z) ^ 2 * (1 + z) := by
    nlinarith [pow_nonneg hz0 3]
  have hden : (599 / 625 : ℝ) ≤ (1 - z) ^ 2 * (1 + z / 3) ^ 3 :=
    hbase.trans (mul_le_mul_of_nonneg_left hcube (sq_nonneg _))
  have hden0 : 0 < (1 - z) ^ 2 * (1 + z / 3) ^ 3 := by linarith
  apply (div_lt_iff₀ hden0).mpr
  calc
    (4 / 3 : ℝ) + (2 / 3) * (z / (1 - z)) ≤ 49 / 36 := hnum
    _ < (10 / 7) * (599 / 625) := by norm_num
    _ ≤ (10 / 7) * ((1 - z) ^ 2 * (1 + z / 3) ^ 3) :=
      mul_le_mul_of_nonneg_left hden (by norm_num)

private theorem normalized_small_curvature_le {z a : ℝ}
    (hz0 : 0 < z) (hz25 : z ≤ 1 / 25)
    (hal : 1 + z / 3 ≤ a) (hau : a ≤ 1 + z / (3 * (1 - z))) :
    (((1 + z) * a - 1) / z) / ((1 - z) ^ 2 * a ^ 3) ≤ smallCoarseBound z := by
  have hz1 : 0 < 1 - z := by linarith
  have ha0 : 0 < a := by linarith
  have hnum : ((1 + z) * a - 1) / z ≤ (4 / 3) + (2 / 3) * (z / (1 - z)) := by
    calc
      ((1 + z) * a - 1) / z ≤
          ((1 + z) * (1 + z / (3 * (1 - z))) - 1) / z :=
        div_le_div_of_nonneg_right
          (sub_le_sub_right (mul_le_mul_of_nonneg_left hau (by linarith)) 1) hz0.le
      _ = (4 / 3) + (2 / 3) * (z / (1 - z)) := by
        field_simp [hz0.ne', hz1.ne']
        ring
  have hupper0 : 0 ≤ (4 / 3 : ℝ) + (2 / 3) * (z / (1 - z)) := by positivity
  have hden0 : 0 < (1 - z) ^ 2 * (1 + z / 3) ^ 3 := by positivity
  have hdena0 : 0 < (1 - z) ^ 2 * a ^ 3 := by positivity
  have hdencmp : (1 - z) ^ 2 * (1 + z / 3) ^ 3 ≤ (1 - z) ^ 2 * a ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hal 3) (sq_nonneg _)
  calc
    (((1 + z) * a - 1) / z) / ((1 - z) ^ 2 * a ^ 3) ≤
        ((4 / 3) + (2 / 3) * (z / (1 - z))) / ((1 - z) ^ 2 * a ^ 3) :=
      div_le_div_of_nonneg_right hnum hdena0.le
    _ ≤ smallCoarseBound z := div_le_div_of_nonneg_left hupper0 hden0 hdencmp

theorem curvatureModel_small_of_cubic_bounds {u t : ℝ}
    (hu0 : 0 < u) (hu5 : u ≤ 1 / 5)
    (hl : u + u ^ 3 / 3 ≤ t) (hu : t ≤ u + u ^ 3 / (3 * (1 - u ^ 2))) :
    curvatureModel u t < 1 / ell := by
  have hz0 : 0 < u ^ 2 := sq_pos_of_pos hu0
  have hz25 : u ^ 2 ≤ 1 / 25 := by
    nlinarith [mul_nonneg hu0.le (show 0 ≤ 1 / 5 - u by linarith)]
  have hq : 0 < 1 - u ^ 2 := by linarith
  have ht0 : 0 < t := by nlinarith [pow_pos hu0 3]
  have hal : 1 + u ^ 2 / 3 ≤ t / u := by
    apply (le_div_iff₀ hu0).mpr
    nlinarith
  have hau : t / u ≤ 1 + u ^ 2 / (3 * (1 - u ^ 2)) := by
    apply (div_le_iff₀ hu0).mpr
    calc
      t ≤ u + u ^ 3 / (3 * (1 - u ^ 2)) := hu
      _ = (1 + u ^ 2 / (3 * (1 - u ^ 2))) * u := by ring
  have he : curvatureModel u t =
      (((1 + u ^ 2) * (t / u) - 1) / u ^ 2) / ((1 - u ^ 2) ^ 2 * (t / u) ^ 3) := by
    unfold curvatureModel
    field_simp [hu0.ne', ht0.ne', hq.ne']
  rw [he]
  exact (normalized_small_curvature_le hz0 hz25 hal hau).trans_lt
    ((smallCoarseBound_lt_ten_sevenths hz0.le hz25).trans ten_sevenths_lt_inv_ell)

theorem curvatureModel_artanh_small {u : ℝ} (hu0 : 0 < u) (hu5 : u ≤ 1 / 5) :
    curvatureModel u (Real.artanh u) < 1 / ell := by
  have hu : u ∈ Set.Ico (0 : ℝ) 1 := ⟨hu0.le, by linarith⟩
  exact curvatureModel_small_of_cubic_bounds hu0 hu5
    (cubic_le_artanh hu) (artanh_le_cubic_tail hu)

theorem rSecondDeriv_le_inv_ell {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ s0) :
    rSecondDeriv s ≤ 1 / ell := by
  by_cases hs_zero : s = 0
  · subst s
    rw [rSecondDeriv_zero]
    exact (show (4 / 3 : ℝ) < 10 / 7 by norm_num).trans ten_sevenths_lt_inv_ell |>.le
  · have hsp : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs_zero)
    have hsell : s < ell := hs.trans_lt s0_lt_ell
    have hu := psiInv_mem_Ioo ⟨hsp, hsell⟩
    have hu5 : psiInv s ≤ 1 / 5 := by
      apply (strictMonoOn_psi.le_iff_le ⟨hu.1.le, hu.2.le⟩ (by norm_num)).mp
      rw [psi_psiInv hs0 hsell]
      exact hs
    change (if s ≤ 0 then 4 / 3 else curvatureModel (psiInv s) (Real.artanh (psiInv s))) ≤ _
    rw [ite_eq_right (not_le.mpr hsp)]
    exact (curvatureModel_artanh_small hu.1 hu5).le

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.rSecondDeriv_le_inv_ell := @_root_.OAI.LeanBlast.CourtadeKumar.rSecondDeriv_le_inv_ell
