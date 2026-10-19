-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.common_output_payment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:01:50.612972+00:00
-- url     : https://prove2.me/submissions/f5ac11e7-b108-41fa-a6a4-3184b976265b

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/SoftChannel/Payment.lean:L250-L278
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.common_output_payment. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_concaveOn_entropy
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_pair_entropy_floor
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_rate_window_euler
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_thinning_window

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

theorem pair_entropyAverage_pos (a b : ℝ) (h : |a| + |b| < 1) :
    0 < (entropy (a + b) + entropy (a - b)) / 2 := by
  have hp := entropy_pos (pair_add_mem_Ioo a b h)
  have hm := entropy_pos (pair_sub_mem_Ioo a b h)
  linarith

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.SoftChannel.Window ----
namespace OAI

section

noncomputable section
open Set MeasureTheory
open scoped Topology
namespace LeanBlast.CourtadeKumar
open SoftChannel204

lemma entropy_common_output {a k : ℝ} (ha : a ∈ Icc (-1) 1) (hk : k ∈ Icc (0:ℝ) 1) :
    k*entropy a ≤ entropy (1-k+k*a) := by
  have h := concaveOn_entropy.2 (by norm_num : (1:ℝ) ∈ Icc (-1) 1) ha
    (by linarith [hk.2] : 0 ≤ 1-k) hk.1 (by ring : 1-k+k=1)
  simpa only [smul_eq_mul,mul_one,entropy_one,mul_zero,zero_add] using h

end LeanBlast.CourtadeKumar
end
end

end OAI

-- ---- from OAI.InformationTheory.SoftChannel.Payment ----
namespace OAI

section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace LeanBlast.CourtadeKumar
open SoftChannel204

lemma thinX_mem {c l : ℝ} (hc : c ∈ Ioo (-1) 1) (hl : l ∈ Ioc (0:ℝ) 1) :
    thinX c l ∈ Ioo (-1) 1 := by
  dsimp [thinX]
  constructor
  · have := mul_le_mul_of_nonneg_right hl.2 (show 0 ≤ 1-c by linarith [hc.2])
    nlinarith [hc.1]
  · nlinarith [mul_pos hl.1 (show 0 < 1-c by linarith [hc.2])]

lemma thinX_add (c d l : ℝ) : thinX c l+l*d=thinX (c+d) l := by unfold thinX; ring
lemma thinX_sub (c d l : ℝ) : thinX c l-l*d=thinX (c-d) l := by unfold thinX; ring

lemma entropy_thinX {a l : ℝ} (ha : a ∈ Icc (-1) 1) (hl : l ∈ Icc (0:ℝ) 1) :
    l*entropy a ≤ entropy (thinX a l) := by
  have h := entropy_common_output ha hl
  convert! h using 1
  congr 1
  unfold thinX
  ring

lemma entropy_thinX_strict {a l : ℝ} (ha : a ∈ Ioo (-1) 1) (hl : l ∈ Ioo (0:ℝ) 1) :
    l*entropy a < entropy (thinX a l) := by
  have hap : (1+a)/2 ∈ Icc (0:ℝ) 1 := by constructor <;> linarith [ha.1,ha.2]
  have h := Real.strictConcave_binEntropy.2 (by norm_num : (1:ℝ) ∈ Icc 0 1) hap
    (by linarith [ha.2] : (1:ℝ) ≠ (1+a)/2) (by linarith [hl.2] : 0 < 1-l) hl.1
    (by ring : 1-l+l=1)
  rw [entropy_eq_binEntropy,entropy_eq_binEntropy]
  simp only [smul_eq_mul,Real.binEntropy_one,mul_zero,zero_add,mul_one] at h
  convert! h using 1
  congr 1
  unfold thinX
  ring

lemma thinJ_nonneg {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) : 0 ≤ thinJ c d l := by
  have hh : |c|+|d| < 1 := by rw [abs_of_nonneg hc,abs_of_nonneg hd]; exact hcd
  have ha := pair_add_mem_Ioo c d hh
  have hb := pair_sub_mem_Ioo c d hh
  have h₁ := entropy_thinX ⟨ha.1.le,ha.2.le⟩ ⟨hl.1.le,hl.2⟩
  have h₂ := entropy_thinX ⟨hb.1.le,hb.2.le⟩ ⟨hl.1.le,hl.2⟩
  dsimp [thinJ,pairH]
  rw [thinX_add,thinX_sub]
  linarith

lemma thinJ_pos {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c+d < 1)
    (hl : l ∈ Ioo (0:ℝ) 1) : 0 < thinJ c d l := by
  have hh : |c|+|d| < 1 := by rw [abs_of_nonneg hc,abs_of_nonneg hd]; exact hcd
  have h₁ := entropy_thinX_strict (pair_add_mem_Ioo c d hh) hl
  have h₂ := entropy_thinX_strict (pair_sub_mem_Ioo c d hh) hl
  dsimp [thinJ,pairH]
  rw [thinX_add,thinX_sub]
  linarith

lemma thinning_domain {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) :
    0 ≤ thinX c l ∧ 0 < l*d ∧ thinX c l+l*d < 1 ∧ 0 < l*pairH c d := by
  have hc1 : c < 1 := by linarith
  have hh : |c|+|d| < 1 := by rw [abs_of_nonneg hc,abs_of_pos hd]; exact hcd
  refine ⟨?_,mul_pos hl.1 hd,?_,mul_pos hl.1 (pair_entropyAverage_pos c d hh)⟩
  · dsimp [thinX]
    have := mul_le_mul_of_nonneg_right hl.2 (show 0 ≤ 1-c by linarith)
    nlinarith
  · rw [thinX_add]
    exact (thinX_mem (pair_add_mem_Ioo c d hh) hl).2

lemma thinJ_le_thinI {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) : thinJ c d l ≤ thinI c d l := by
  obtain ⟨hx,hy,hxy,_⟩ := thinning_domain hc hd hcd hl
  have hh : |thinX c l|+|l*d| < 1 := by rw [abs_of_nonneg hx,abs_of_pos hy]; exact hxy
  have h := pairEntropyGap_nonneg (thinX c l) (l*d) hh
  dsimp [thinJ,thinI,pairH]
  unfold pairEntropyGap at h
  linarith

lemma thinI_lt_ell {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) : thinI c d l < ell := by
  have hpos := (thinning_domain hc hd hcd hl).2.2.2
  have h := entropy_le_ell (thinX c l)
  dsimp [thinI]
  linarith

lemma thinning_entropy_floor {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) :
    (1-thinX c l)*entropy (l*d/(1-thinX c l)) ≤ l*pairH c d := by
  have hc0 : 1-c ≠ 0 := by linarith
  have h := mul_le_mul_of_nonneg_left (pair_entropy_floor hc hd.le hcd) hl.1.le
  have he : l*d/(1-thinX c l) = d/(1-c) := by
    rw [show 1-thinX c l=l*(1-c) by dsimp [thinX]; ring]
    field_simp [hl.1.ne',hc0]
  rw [he]
  dsimp [thinX,pairH] at *
  nlinarith

lemma thinning_path_window {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) :
    (∫ h in (ell-thinI c d l)..(ell-thinJ c d l),
      clipKernel (Real.log (1+thinX c l)) h) ≤
      -(3/2:ℝ)*Real.log (1-(l*d)^2/(1+thinX c l)^2) := by
  obtain ⟨hx,hy,hxy,_⟩ := thinning_domain hc hd hcd hl
  have H := thinning_window hx hy hxy (thinning_entropy_floor hc hd hcd hl)
    (show l*pairH c d ≤ (entropy (thinX c l+l*d)+entropy (thinX c l-l*d))/2 by
      have := thinJ_nonneg hc hd.le hcd hl
      dsimp [thinJ,pairH] at this ⊢
      linarith)
  convert! H using 1; congr 1 <;> simp only [thinI,thinJ,entropy,pairH] <;> ring

lemma entropy_euler {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    entropy x-(1-x)*Real.artanh x = ell-Real.log (1+x) := by
  rw [Real.artanh_eq_half_log ⟨hx.1.le,hx.2.le⟩,
    Real.log_div (by linarith [hx.1] : 1+x ≠ 0) (by linarith [hx.2] : 1-x ≠ 0)]
  unfold entropy psi
  ring

lemma log_pair_defect {x d : ℝ} (hx : 0 ≤ x) (hd : 0 < d) (hxd : x+d < 1) :
    (Real.log (1+(x+d))+Real.log (1+(x-d)))/2 =
      Real.log (1+x)+(1/2:ℝ)*Real.log (1-d^2/(1+x)^2) := by
  have hp : 0 < 1+x := by linarith
  have hpm : 0 < 1+(x-d) := by linarith
  have hpp : 0 < 1+(x+d) := by linarith
  have hr : 1-d^2/(1+x)^2 = ((1+(x+d))*(1+(x-d)))/(1+x)^2 := by field_simp; ring
  rw [hr,Real.log_div (mul_ne_zero hpp.ne' hpm.ne') (pow_ne_zero _ hp.ne'),
    Real.log_mul hpp.ne' hpm.ne',Real.log_pow]
  ring

lemma thinning_defect_nonneg {x d : ℝ} (hx : 0 ≤ x) (hd : 0 < d) (hxd : x+d < 1) :
    0 ≤ -(1/2:ℝ)*Real.log (1-d^2/(1+x)^2) := by
  have hr : 0 < 1-d^2/(1+x)^2 := by
    have hp : 0 < (1+x)^2 := sq_pos_of_pos (by linarith)
    have hs : d^2 < (1+x)^2 := by
      nlinarith [mul_pos (show 0 < 1+x-d by linarith) (show 0 < 1+x+d by linarith)]
    linarith [(div_lt_one hp).mpr hs]
  have hle : 1-d^2/(1+x)^2 ≤ 1 := sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))
  have hlog := Real.log_nonpos hr.le hle
  linarith

lemma hasDerivAt_thinX (c l : ℝ) : HasDerivAt (thinX c) (-(1-c)) l := by
  convert! (((hasDerivAt_id l).mul_const (1-c)).const_sub 1) using 1; simp

lemma hasDerivAt_entropy_thinX {c l : ℝ} (hc : c ∈ Ioo (-1) 1) (hl : l ∈ Ioc (0:ℝ) 1) :
    HasDerivAt (fun z => entropy (thinX c z)) ((1-c)*Real.artanh (thinX c l)) l := by
  convert! (hasDerivAt_entropy (thinX_mem hc hl)).comp l (hasDerivAt_thinX c l) using 1; ring

lemma hasDerivAt_thinI {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) : HasDerivAt (thinI c d) (thinIDeriv c d l) l := by
  convert!
    (hasDerivAt_entropy_thinX (show c ∈ Ioo (-1) 1 from ⟨by linarith,by linarith⟩) hl).sub
      ((hasDerivAt_id l).mul_const (pairH c d)) using 1; simp [thinIDeriv]

lemma hasDerivAt_thinJ {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) : HasDerivAt (thinJ c d) (thinJDeriv c d l) l := by
  have hh : |c|+|d| < 1 := by rw [abs_of_nonneg hc,abs_of_pos hd]; exact hcd
  have h := (((hasDerivAt_entropy_thinX (pair_add_mem_Ioo c d hh) hl).add
    (hasDerivAt_entropy_thinX (pair_sub_mem_Ioo c d hh) hl)).div_const 2).sub
    ((hasDerivAt_id l).mul_const (pairH c d))
  convert! h using 1
  · ext z
    simp [thinJ,pairH,thinX_add,thinX_sub]
  · simp [thinJDeriv]

lemma thinI_euler {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) : l*thinIDeriv c d l = thinI c d l-thinA c l := by
  have hx := thinX_mem (show c ∈ Ioo (-1) 1 by constructor <;> linarith) hl
  have h := entropy_euler hx
  dsimp [thinIDeriv,thinI,thinA,thinX] at *
  nlinarith

lemma thinJ_euler {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) : l*thinJDeriv c d l = thinJ c d l-thinA c l-thinK c d l := by
  have hh : |c|+|d| < 1 := by rw [abs_of_nonneg hc,abs_of_pos hd]; exact hcd
  have h₁ := entropy_euler (thinX_mem (pair_add_mem_Ioo c d hh) hl)
  have h₂ := entropy_euler (thinX_mem (pair_sub_mem_Ioo c d hh) hl)
  obtain ⟨hx,hy,hxy,_⟩ := thinning_domain hc hd hcd hl
  have hlog := log_pair_defect hx hy hxy
  rw [thinX_add,thinX_sub] at hlog
  dsimp [thinJDeriv,thinJ,thinA,thinK,pairH]
  rw [thinX_add,thinX_sub]
  simp only [thinX] at h₁ h₂ hlog ⊢
  nlinarith

lemma continuous_thinI (c d : ℝ) : Continuous (thinI c d) := by
  unfold thinI thinX
  exact (continuous_entropy.comp (continuous_const.sub (continuous_id.mul continuous_const))).sub
    (continuous_id.mul continuous_const)

lemma continuous_thinJ (c d : ℝ) : Continuous (thinJ c d) := by
  unfold thinJ pairH thinX
  have he := continuous_entropy
  fun_prop

lemma hasDerivAt_normalizedDemand {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioo (0:ℝ) 1) : HasDerivAt (normalizedDemand c d) (normalizedDemandDeriv c d l) l := by
  have hl' : l ∈ Ioc (0:ℝ) 1 := ⟨hl.1,hl.2.le⟩
  have hj := thinJ_pos hc hd.le hcd hl
  have hjI := thinJ_le_thinI hc hd hcd hl'
  have hI := thinI_lt_ell hc hd hcd hl'
  have h := (((hasDerivAt_r ⟨hj.trans_le hjI,hI⟩).comp l (hasDerivAt_thinI hc hd hcd hl')).sub
    ((hasDerivAt_r ⟨hj,hjI.trans_lt hI⟩).comp l (hasDerivAt_thinJ hc hd hcd hl'))).div
    (hasDerivAt_id l) hl.1.ne'
  convert! h using 1; dsimp [normalizedDemand,normalizedDemandDeriv]; ring

lemma normalizedDemandDeriv_nonneg {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioo (0:ℝ) 1) : 0 ≤ normalizedDemandDeriv c d l := by
  have hl' : l ∈ Ioc (0:ℝ) 1 := ⟨hl.1,hl.2.le⟩
  obtain ⟨hx,hy,hxy,_⟩ := thinning_domain hc hd hcd hl'
  have hk : 0 ≤ thinK c d l := thinning_defect_nonneg hx hy hxy
  have hw : (∫ h in (ell-thinI c d l)..(ell-thinJ c d l),
      clipKernel (Real.log (1+thinX c l)) h) ≤ 3*thinK c d l := by
    convert! thinning_path_window hc hd hcd hl' using 1; unfold thinK; ring
  have H := rate_window_euler (thinJ_pos hc hd.le hcd hl) (thinJ_le_thinI hc hd hcd hl')
    (thinI_lt_ell hc hd hcd hl') hk hw
  have hI := thinI_euler hc hd hcd hl'
  have hJ := thinJ_euler hc hd hcd hl'
  change 0 ≤ ((thinI c d l-thinA c l)*rDeriv (thinI c d l)-r (thinI c d l))-
    ((thinJ c d l-thinA c l)*rDeriv (thinJ c d l)-r (thinJ c d l))+
    rDeriv (thinJ c d l)*thinK c d l at H
  unfold normalizedDemandDeriv
  apply div_nonneg _ (sq_nonneg l)
  nlinarith [congrArg (fun z => z*rDeriv (thinI c d l)) hI,
    congrArg (fun z => z*rDeriv (thinJ c d l)) hJ]

lemma common_output_payment {c d l : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hcd : c+d < 1)
    (hl : l ∈ Ioc (0:ℝ) 1) :
    r (thinI c d l)-r (thinJ c d l) ≤ l*r (pairEntropyGap c d) := by
  have hdom (z : ℝ) (hz : z ∈ Icc l 1) : z ∈ Ioc (0:ℝ) 1 := ⟨hl.1.trans_le hz.1,hz.2⟩
  have hci : ContinuousOn (fun z => r (thinI c d z)) (Icc l 1) := by
    apply continuousOn_r.comp (continuous_thinI c d).continuousOn
    intro z hz
    have h := hdom z hz
    exact ⟨(thinJ_nonneg hc hd.le hcd h).trans (thinJ_le_thinI hc hd hcd h),thinI_lt_ell hc hd hcd h⟩
  have hcj : ContinuousOn (fun z => r (thinJ c d z)) (Icc l 1) := by
    apply continuousOn_r.comp (continuous_thinJ c d).continuousOn
    intro z hz
    have h := hdom z hz
    exact ⟨thinJ_nonneg hc hd.le hcd h,(thinJ_le_thinI hc hd hcd h).trans_lt (thinI_lt_ell hc hd hcd h)⟩
  have hmono : MonotoneOn (normalizedDemand c d) (Icc l 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := normalizedDemandDeriv c d) (convex_Icc l 1)
    · exact (hci.sub hcj).div continuousOn_id (fun z hz => (hdom z hz).1.ne')
    · intro z hz
      have hz' : z ∈ Ioo (0:ℝ) 1 := by rw [interior_Icc] at hz; exact ⟨hl.1.trans hz.1,hz.2⟩
      exact (hasDerivAt_normalizedDemand hc hd hcd hz').hasDerivWithinAt
    · intro z hz
      have hz' : z ∈ Ioo (0:ℝ) 1 := by rw [interior_Icc] at hz; exact ⟨hl.1.trans hz.1,hz.2⟩
      exact normalizedDemandDeriv_nonneg hc hd hcd hz'
  have H := hmono ⟨le_rfl,hl.2⟩ ⟨hl.2,le_rfl⟩ hl.2
  have hI : thinI c d 1 = pairEntropyGap c d := by simp [thinI,thinX,pairH,pairEntropyGap]
  have hJ : thinJ c d 1 = 0 := by simp [thinJ,thinX]
  unfold normalizedDemand at H
  rw [hI,hJ,r_zero,sub_zero,div_one] at H
  exact (div_le_iff₀ hl.1).mp H |>.trans_eq (by ring)

end LeanBlast.CourtadeKumar
end
end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter MeasureTheory
open scoped Topology
open SoftChannel204


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.common_output_payment := @_root_.OAI.LeanBlast.CourtadeKumar.common_output_payment
