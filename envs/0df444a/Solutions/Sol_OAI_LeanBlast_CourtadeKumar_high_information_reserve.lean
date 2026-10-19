-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.high_information_reserve
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:03:51.189704+00:00
-- url     : https://prove2.me/submissions/5bbd5410-df67-4db2-bc42-482c3f3ef2c2

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/SoftChannel/HighReserve.lean:L86-L111
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.high_information_reserve. The node keeps its source
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

theorem rSecondDeriv_nonneg {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) :
    0 ≤ rSecondDeriv s := by
  rcases hs.eq_or_lt with rfl | hs
  · norm_num
  · exact (rSecondDeriv_pos ⟨hs, hsell⟩).le

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

theorem half_sq_le_psi {v : ℝ} (hv : |v| ≤ 1) : v ^ 2 / 2 ≤ psi v := by
  have h := (summable_psi_closed hv).sum_le_tsum {0} (fun k hk =>
    mul_nonneg (psiCoeff_nonneg k) (Even.pow_nonneg (even_two_mul (k + 1)) v))
  rw [(hasSum_psi_closed hv).tsum_eq] at h
  simpa [psiCoeff_zero, div_eq_mul_inv, mul_comm] using h

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

lemma softCutoff_pos : 0 < softCutoff := psi_pos_of_pos (by norm_num) (by norm_num)
lemma softCutoff_lt_ell : softCutoff < ell := psi_lt_ell (by norm_num)

lemma artanh_77_upper : Real.artanh (77/100:ℝ) < 1021/1000 := by
  have he : (177/23:ℝ) < Real.exp (1021/500) := by
    refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 1021/500) 8)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hl := (Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ)<177/23)).mpr he
  rw [artanh_eq_log_sub (by norm_num : (77/100:ℝ) ∈ Ioo (-1) 1)]
  rw [← Real.log_div (by norm_num : (1+(77/100:ℝ)) ≠ 0) (by norm_num : (1-(77/100:ℝ)) ≠ 0)]
  norm_num at *
  linarith

lemma softCutoff_lower : (336/1000:ℝ) ≤ softCutoff := by
  have h := sum_range_psi_le (by norm_num : |(77/100:ℝ)| < 1) 6
  norm_num [psiCoeff, Finset.sum_range_succ] at h
  exact le_trans (by norm_num) h

lemma softCutoff_above_center : ell-1/2 < softCutoff := by
  linarith [ell_lt_347_div_500,softCutoff_lower]

lemma centeredRate_cutoff_pos : 0 < centeredRate softCutoff := by
  have hv0 := Real.artanh_pos (show (77/100:ℝ) ∈ Ioo 0 1 by norm_num)
  have hv := artanh_77_upper
  have hs := softCutoff_lower
  have hL := ell_lt_347_div_500
  have hD : (185/100:ℝ) ≤ (77/100)/((1-(77/100:ℝ)^2)*Real.artanh (77/100)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  unfold centeredRate rGap
  rw [show softCutoff = psi (77/100) from rfl, rDeriv_psi (by norm_num), r_psi (by norm_num)]
  change 0 < (softCutoff-(ell-1/2))*(1+(77/100)/((1-(77/100:ℝ)^2)*Real.artanh (77/100))-2)-
    ((77/100)*Real.artanh (77/100)-2*softCutoff)
  have hmul := mul_le_mul_of_nonneg_left (show (85/100:ℝ) ≤ 1+(77/100)/((1-(77/100:ℝ)^2)*Real.artanh (77/100))-2 by linarith)
    (sub_nonneg.mpr softCutoff_above_center.le)
  nlinarith

lemma hasDerivAt_centeredRate {I : ℝ} (hI : I ∈ Ioo 0 ell) :
    HasDerivAt centeredRate ((I-(ell-1/2))*rSecondDeriv I) I := by
  have h := (((hasDerivAt_id I).sub_const (ell-1/2)).mul
    ((hasDerivAt_rDeriv hI).sub_const 2)).sub (hasDerivAt_rGap hI)
  convert! h using 1; dsimp [centeredRate]; ring

lemma centeredRate_nonneg {I : ℝ} (hI : I ∈ Ico softCutoff ell) : 0 ≤ centeredRate I := by
  have hm : MonotoneOn centeredRate (Ico softCutoff ell) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun I => (I-(ell-1/2))*rSecondDeriv I)
      (convex_Ico _ _)
    · intro x hx
      exact (hasDerivAt_centeredRate ⟨softCutoff_pos.trans_le hx.1,hx.2⟩).continuousAt.continuousWithinAt
    · intro x hx
      exact (hasDerivAt_centeredRate ⟨by simp only [interior_Ico,mem_Ioo] at hx; exact softCutoff_pos.trans hx.1,
        by simp only [interior_Ico,mem_Ioo] at hx; exact hx.2⟩).hasDerivWithinAt
    · intro x hx
      simp only [interior_Ico,mem_Ioo] at hx
      exact mul_nonneg (by linarith [softCutoff_above_center])
        (rSecondDeriv_nonneg (by linarith [softCutoff_pos]) hx.2)
  exact centeredRate_cutoff_pos.le.trans (hm ⟨le_rfl,softCutoff_lt_ell⟩ hI hI.1)

lemma rGap_tangent {I s : ℝ} (hI : I ∈ Ioo 0 ell) (hs : s ∈ Ico I ell) :
    rGap I+(s-I)*(rDeriv I-2) ≤ rGap s := by
  rcases hs.1.eq_or_lt with he | hlt
  · rw [← he]; simp
  · have h := convexOn_rGap.le_slope_of_hasDerivAt ⟨hI.1.le,hI.2⟩ ⟨hI.1.le.trans hs.1,hs.2⟩ hlt
      (hasDerivAt_rGap hI)
    rw [slope_def_field] at h
    have hh := (le_div_iff₀ (sub_pos.mpr hlt)).mp h
    nlinarith

lemma high_information_reserve {m I : ℝ} (hm : |m| < 1)
    (hI : softCutoff ≤ I) (hIe : I < entropy m) : r I ≤ meanReserve m I := by
  have hm2 : m^2 < 1 := by nlinarith [abs_lt.mp hm, sq_abs m]
  have ha : 0 < 1-m^2 := by linarith
  have hI0 : 0 < I := softCutoff_pos.trans_le hI
  have hIL : I < ell := hIe.trans_le (entropy_le_ell m)
  have hc := half_sq_le_psi hm.le
  let c := entropy m-(1-m^2)*ell
  have hcub : c ≤ m^2*(ell-1/2) := by dsimp [c,entropy]; nlinarith
  let s := ell-(entropy m-I)/(1-m^2)
  have hsline : (1-m^2)*s = I-c := by dsimp [s,c]; field_simp; ring
  have hsI : I ≤ s := by
    have hp := mul_nonneg (sq_nonneg m) (show 0 ≤ I-(ell-1/2) by linarith [softCutoff_above_center])
    nlinarith
  have hsL : s < ell := by dsimp [s]; exact sub_lt_self _ (div_pos (sub_pos.mpr hIe) ha)
  have hL : L ((entropy m-I)/(1-m^2)) = rGap s := by
    rw [L_eq_rGap ⟨div_pos (sub_pos.mpr hIe) ha,by dsimp [s] at hsI; linarith⟩]
  have htan := mul_le_mul_of_nonneg_left (rGap_tangent ⟨hI0,hIL⟩ ⟨hsI,hsL⟩) ha.le
  have hcd := mul_le_mul_of_nonneg_right hcub (sub_nonneg.mpr (rDeriv_ge_two hI0.le hIL))
  have hxi := mul_nonneg (sq_nonneg m) (centeredRate_nonneg ⟨hI,hIL⟩)
  have hident := congrArg (fun t => t*(rDeriv I-2)) hsline
  unfold centeredRate at hxi
  unfold meanReserve
  rw [hL]
  dsimp [rGap] at *
  nlinarith

end LeanBlast.CourtadeKumar
end
end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter
open scoped BigOperators Topology


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.high_information_reserve := @_root_.OAI.LeanBlast.CourtadeKumar.high_information_reserve
