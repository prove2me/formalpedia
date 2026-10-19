-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.hasDerivAt_K_pos
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:25:00.549427+00:00
-- url     : https://prove2.me/submissions/1f4e8a30-9811-4971-bfc1-97be5c7b3942

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/KRegularity.lean:L69-L100
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.hasDerivAt_K_pos. The node keeps its source
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
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_hasDerivAt_artanh
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_hasDerivAt_psi

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

theorem K_eq_rGap {s : ℝ} (hs : 0 < s) (hs0 : s ≤ s0) : K s = rGap s := by
  simp [K, not_le.mpr hs, hs0]

theorem K_eq_tangent {s : ℝ} (hs : 0 < s) (hs0 : s0 ≤ s) :
    K s = rGap s0 + (rDeriv s0 - 2) * (s - s0) := by
  rcases hs0.eq_or_lt with rfl | hs0
  · simp [K, not_le.mpr hs]
  · simp [K, not_le.mpr hs, not_le.mpr hs0]

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

theorem s0_pos : 0 < s0 := by
  change 0 < psi (1 / 5)
  rw [← psi_zero]
  exact strictMonoOn_psi (by norm_num) (by norm_num) (by norm_num)

theorem s0_lt_ell : s0 < ell := psi_lt_ell (by norm_num)

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

-- ---- from OAI.InformationTheory.BooleanNoise.InverseRegularity ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem hasDerivAt_rGap {s : ℝ} (hs : s ∈ Ioo 0 ell) :
    HasDerivAt rGap (rDeriv s - 2) s := by
  convert! (hasDerivAt_r hs).sub ((hasDerivAt_id s).const_mul 2) using 1
  simp

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.KRegularity ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem hasDerivAt_tangent_extension (F : ℝ → ℝ) {c d : ℝ}
    (hF : HasDerivAt F d c) :
    HasDerivAt (fun s => if s ≤ c then F s else F c + d * (s - c)) d c := by
  let T : ℝ → ℝ := fun s => if s ≤ c then F s else F c + d * (s - c)
  have hleft : HasDerivWithinAt T d (Iic c) c := by
    apply hF.hasDerivWithinAt.congr
    · intro s hs
      change s ≤ c at hs
      simp only [T, ite_eq_left hs]
    · simp [T]
  have hline : HasDerivAt (fun s : ℝ => F c + d * (s - c)) d c := by
    convert! (((hasDerivAt_id c).sub_const c).const_mul d).const_add (F c) using 1
    ring
  have hright : HasDerivWithinAt T d (Ici c) c := by
    apply hline.hasDerivWithinAt.congr
    · intro s hs
      change c ≤ s at hs
      rcases hs.eq_or_lt with rfl | hs
      · simp [T]
      · simp [T, not_le.mpr hs]
    · simp [T]
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hleft.union hright

theorem hasDerivAt_K_pos {s : ℝ} (hs : 0 < s) : HasDerivAt K (KDeriv s) s := by
  by_cases hsc : s < s0
  · have he : K =ᶠ[𝓝 s] rGap := by
      filter_upwards [Ioo_mem_nhds hs hsc] with t ht
      exact K_eq_rGap ht.1 ht.2.le
    have hKd : KDeriv s = rDeriv s - 2 := by simp [KDeriv, not_le.mpr hs, hsc.le]
    rw [hKd]
    exact (hasDerivAt_rGap ⟨hs, hsc.trans s0_lt_ell⟩).congr_of_eventuallyEq he
  · have hsc' : s0 ≤ s := le_of_not_gt hsc
    rcases hsc'.eq_or_lt with rfl | hsc'
    · have hjoin := hasDerivAt_tangent_extension rGap (hasDerivAt_rGap ⟨s0_pos, s0_lt_ell⟩)
      have he : K =ᶠ[𝓝 s0]
          (fun t => if t ≤ s0 then rGap t else rGap s0 + (rDeriv s0 - 2) * (t - s0)) := by
        filter_upwards [Ioi_mem_nhds s0_pos] with t ht
        change 0 < t at ht
        simp only [K, ite_eq_right (not_le.mpr ht)]
      have hKd : KDeriv s0 = rDeriv s0 - 2 := by simp [KDeriv, not_le.mpr s0_pos]
      rw [hKd]
      exact hjoin.congr_of_eventuallyEq he
    · have hline : HasDerivAt
          (fun t : ℝ => rGap s0 + (rDeriv s0 - 2) * (t - s0)) (rDeriv s0 - 2) s := by
        convert! (((hasDerivAt_id s).sub_const s0).const_mul (rDeriv s0 - 2)).const_add
          (rGap s0) using 1
        ring
      have he : K =ᶠ[𝓝 s]
          (fun t => rGap s0 + (rDeriv s0 - 2) * (t - s0)) := by
        filter_upwards [Ioi_mem_nhds hsc'] with t ht
        exact K_eq_tangent (s0_pos.trans ht) ht.le
      have hKd : KDeriv s = rDeriv s0 - 2 := by
        simp [KDeriv, not_le.mpr hs, not_le.mpr hsc']
      rw [hKd]
      exact hline.congr_of_eventuallyEq he

end LeanBlast.CourtadeKumar

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.hasDerivAt_K_pos := @_root_.OAI.LeanBlast.CourtadeKumar.hasDerivAt_K_pos
