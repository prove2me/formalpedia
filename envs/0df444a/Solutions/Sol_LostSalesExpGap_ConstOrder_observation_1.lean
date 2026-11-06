-- Prove2me | solution 1 for LostSalesExpGap.ConstOrder.observation_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T07:36:01.811414+00:00
-- url     : https://prove2.me/submissions/c84c2bb9-5dde-405d-9de2-04b9cc62087c

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LSExpGapObs1

open CappedBaseStock LostSalesExpGap.ConstOrder

/-- The `j`-th affine piece of `𝔣_d`. -/
noncomputable def piece (L : ℕ) (d χ : Fin L → ℝ) (I : ℝ) (j : ℕ) : ℝ :=
  (∑ i ∈ Finset.Icc 1 j, (vget χ (L - i) - vget d (L - i))) + if j = L then I else 0

lemma fObs_eq (L : ℕ) (d χ : Fin L → ℝ) (I : ℝ) :
    fObs L d χ I = (Finset.range (L + 1)).sup' Finset.nonempty_range_add_one (piece L d χ I) :=
  rfl

lemma continuous_vget {L : ℕ} (k : ℕ) : Continuous (fun χ : Fin L → ℝ => vget χ k) := by
  unfold vget
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

lemma abs_vget_le {L : ℕ} (χ : Fin L → ℝ) (k : ℕ) : |vget χ k| ≤ ∑ i, |χ i| := by
  unfold vget
  split_ifs with h
  · exact Finset.single_le_sum (f := fun i => |χ i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ (⟨k, h⟩ : Fin L))
  · simp only [abs_zero]; exact Finset.sum_nonneg fun i _ => abs_nonneg _

lemma continuous_fObs (L : ℕ) :
    Continuous (fun w : (Fin L → ℝ) × ((Fin L → ℝ) × ℝ) => fObs L w.1 w.2.1 w.2.2) := by
  simp only [fObs_eq]
  apply Continuous.finset_sup'_apply
  intro j _
  unfold piece
  refine Continuous.add (continuous_finset_sum _ fun i _ => ?_) ?_
  · exact ((continuous_vget _).comp (continuous_fst.comp continuous_snd)).sub
      ((continuous_vget _).comp continuous_fst)
  · split_ifs
    · exact continuous_snd.comp continuous_snd
    · exact continuous_const

lemma continuous_fObs_right (L : ℕ) (d : Fin L → ℝ) :
    Continuous (fun v : (Fin L → ℝ) × ℝ => fObs L d v.1 v.2) := by
  simp only [fObs_eq]
  apply Continuous.finset_sup'_apply
  intro j _
  unfold piece
  refine Continuous.add (continuous_finset_sum _ fun i _ => ?_) ?_
  · exact ((continuous_vget _).comp continuous_fst).sub continuous_const
  · split_ifs
    · exact continuous_snd
    · exact continuous_const

lemma measurable_vget {L : ℕ} (k : ℕ) : Measurable (fun χ : Fin L → ℝ => vget χ k) := by
  unfold vget
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

lemma measurable_fObs_comp {α : Type*} [MeasurableSpace α] (L : ℕ) {f g : α → Fin L → ℝ}
    {I : α → ℝ} (hf : Measurable f) (hg : Measurable g) (hI : Measurable I) :
    Measurable (fun a => fObs L (f a) (g a) (I a)) := by
  simp only [fObs_eq]
  apply Finset.measurable_range_sup''
  intro j _
  unfold piece
  refine Measurable.add (Finset.measurable_sum _ fun i _ => ?_) ?_
  · exact ((measurable_vget _).comp hg).sub ((measurable_vget _).comp hf)
  · split_ifs
    · exact hI
    · exact measurable_const

lemma abs_piece_le (L : ℕ) (d χ : Fin L → ℝ) (I : ℝ) (j : ℕ) (hj : j ≤ L) :
    |piece L d χ I j| ≤ L * (∑ i, |χ i| + ∑ i, |d i|) + |I| := by
  unfold piece
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ Finset.Icc 1 j, |vget χ (L - i) - vget d (L - i)|
        ≤ ∑ _i ∈ Finset.Icc 1 j, (∑ i, |χ i| + ∑ i, |d i|) :=
          Finset.sum_le_sum fun i _ =>
            (abs_sub _ _).trans (add_le_add (abs_vget_le _ _) (abs_vget_le _ _))
      _ = j * (∑ i, |χ i| + ∑ i, |d i|) := by simp; ring
      _ ≤ L * (∑ i, |χ i| + ∑ i, |d i|) := by
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast hj)
          positivity
  · split_ifs
    · exact le_rfl
    · simp

lemma abs_fObs_le (L : ℕ) (d χ : Fin L → ℝ) (I : ℝ) :
    |fObs L d χ I| ≤ L * (∑ i, |χ i| + ∑ i, |d i|) + |I| := by
  rw [fObs_eq, abs_le]
  constructor
  · have h0 := abs_piece_le L d χ I 0 (Nat.zero_le _)
    have := Finset.le_sup' (piece L d χ I) (Finset.mem_range.mpr (Nat.succ_pos L))
    have := (abs_le.mp h0).1
    linarith
  · apply Finset.sup'_le
    intro j hj
    exact (le_abs_self _).trans
      (abs_piece_le L d χ I j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))

/-- The reversal permutation of the first `L` coordinates. -/
def revFun (L : ℕ) (k : ℕ) : ℕ := if k < L then L - 1 - k else k

lemma revFun_invol (L : ℕ) : Function.Involutive (revFun L) := by
  intro k
  unfold revFun
  by_cases hk : k < L
  · have : L - 1 - k < L := by omega
    simp only [hk, if_true, this]
    omega
  · simp [hk]

def revPerm (L : ℕ) : Equiv.Perm ℕ := (revFun_invol L).toPerm

lemma map_rev (P : DemandLaw) (L : ℕ) :
    (demandPathLaw P).map (fun d : DemandPath => fun k => d (revPerm L k)) = demandPathLaw P := by
  have h := Measure.infinitePi_map_piCongrLeft (X := fun _ : ℕ => ℝ≥0)
    (μ := fun _ : ℕ => P.law) (revPerm L)
  have hfun : (⇑(MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℝ≥0) (revPerm L))) =
      (fun d : DemandPath => fun k => d (revPerm L k)) := by
    funext d k
    simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, cast_eq]
    rfl
  rw [hfun] at h
  simpa [demandPathLaw] using h

end LSExpGapObs1

open LostSalesExpGap.ConstOrder LSExpGapObs1 CappedBaseStock in
theorem solution (P : CappedBaseStock.DemandLaw) (L : ℕ) (hL : 1 ≤ L) :
    (∀ d : Fin L → ℝ, ConvexOn ℝ Set.univ (fun v : (Fin L → ℝ) × ℝ => fObs L d v.1 v.2)) ∧
    (∀ ν : Measure ((Fin L → ℝ) × ℝ), IsProbabilityMeasure ν →
      (∀ᵐ v ∂ν, (∀ i, 0 ≤ v.1 i) ∧ 0 ≤ v.2) →
      (∀ i, Integrable (fun v : (Fin L → ℝ) × ℝ => v.1 i) ν) →
      Integrable (fun v : (Fin L → ℝ) × ℝ => v.2) ν →
      ∫ v, v.2 ∂ν =
        ∫ w, fObs L (firstDemands L w.2) w.1.1 w.1.2
          ∂(ν.prod (CappedBaseStock.demandPathLaw P)) →
      (∀ i, ∫ v, v.1 i ∂ν = ∫ v, v.1 ⟨0, hL⟩ ∂ν) →
      ∫ v, v.1 ⟨0, hL⟩ ∂ν ≤ CappedBaseStock.mean P →
      ∫ d, (Finset.range (L + 1)).sup' Finset.nonempty_range_add_one (fun j =>
          (j : ℝ) * ∫ v, v.1 ⟨0, hL⟩ ∂ν - ∑ i ∈ Finset.Icc 1 j, (d (i - 1) : ℝ) +
            if j = L then ∫ v, v.2 ∂ν else 0) ∂CappedBaseStock.demandPathLaw P
        ≤ ∫ v, v.2 ∂ν) := by
  -- (a) convexity
  have hconv : ∀ d : Fin L → ℝ, ConvexOn ℝ Set.univ
      (fun v : (Fin L → ℝ) × ℝ => fObs L d v.1 v.2) := by
    intro d
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul, fObs_eq]
    apply Finset.sup'_le
    intro j hj
    have hv : ∀ k, vget (a • x + b • y).1 k = a * vget x.1 k + b * vget y.1 k := by
      intro k; unfold vget; split_ifs
      · simp
      · simp
    have key : piece L d (a • x + b • y).1 (a • x + b • y).2 j =
        a * piece L d x.1 x.2 j + b * piece L d y.1 y.2 j := by
      unfold piece
      simp only [hv]
      have hs : ∑ i ∈ Finset.Icc 1 j, (a * vget x.1 (L - i) + b * vget y.1 (L - i) - vget d (L - i))
          = a * ∑ i ∈ Finset.Icc 1 j, (vget x.1 (L - i) - vget d (L - i)) +
            b * ∑ i ∈ Finset.Icc 1 j, (vget y.1 (L - i) - vget d (L - i)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        linear_combination (vget d (L - i)) * hab
      rw [hs]
      split_ifs
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; ring
      · ring
    rw [key]
    exact add_le_add (mul_le_mul_of_nonneg_left (Finset.le_sup' (piece L d x.1 x.2) hj) ha)
      (mul_le_mul_of_nonneg_left (Finset.le_sup' (piece L d y.1 y.2) hj) hb)
  refine ⟨hconv, ?_⟩
  intro ν hν _ hχint hIint hE hχeq _
  set μ := demandPathLaw P with hμ
  set a0 := ∫ v, v.1 ⟨0, hL⟩ ∂ν
  set e := ∫ v, v.2 ∂ν
  -- mean vector
  have hvint : Integrable (fun v : (Fin L → ℝ) × ℝ => v) ν :=
    (Integrable.of_eval hχint).prodMk hIint
  have hmean : ∫ v, v ∂ν = ((fun _ : Fin L => a0), e) := by
    have : ∫ v, v ∂ν = (∫ v, v.1 ∂ν, ∫ v, v.2 ∂ν) :=
      integral_pair (f := fun v : (Fin L → ℝ) × ℝ => v.1) (Integrable.of_eval hχint) hIint
    rw [this]
    congr 1
    funext i
    rw [eval_integral hχint i, hχeq i]
  -- integrability bounds
  have hFcont : ∀ d : Fin L → ℝ, Continuous (fun v : (Fin L → ℝ) × ℝ => fObs L d v.1 v.2) :=
    fun d => continuous_fObs_right L d
  have hbound_int : Integrable (fun v : (Fin L → ℝ) × ℝ =>
      (L : ℝ) * (∑ i, |v.1 i|) + |v.2|) ν :=
    ((integrable_finset_sum _ fun i _ => (hχint i).abs).const_mul _).add hIint.abs
  have hFint : ∀ d : Fin L → ℝ, Integrable (fun v : (Fin L → ℝ) × ℝ => fObs L d v.1 v.2) ν := by
    intro d
    refine Integrable.mono' (hbound_int.add (integrable_const ((L : ℝ) * ∑ i, |d i|)))
      (hFcont d).aestronglyMeasurable (ae_of_all _ fun v => ?_)
    rw [Real.norm_eq_abs]
    have := abs_fObs_le L d v.1 v.2
    simp only [Pi.add_apply]
    linarith
  -- Jensen for each demand vector
  have hjensen : ∀ d : Fin L → ℝ, fObs L d (fun _ => a0) e ≤ ∫ v, fObs L d v.1 v.2 ∂ν := by
    intro d
    have := (hconv d).map_integral_le (μ := ν) (f := fun v => v) (hFcont d).continuousOn
      isClosed_univ (ae_of_all _ fun _ => Set.mem_univ _) hvint (hFint d)
    rw [hmean] at this
    exact this
  -- Fubini
  have hfd : Measurable (fun d : DemandPath => firstDemands L d) := by
    unfold firstDemands
    exact measurable_pi_lambda _ fun k => by fun_prop
  have hGm : Measurable (fun w : ((Fin L → ℝ) × ℝ) × DemandPath =>
      fObs L (firstDemands L w.2) w.1.1 w.1.2) := by
    exact measurable_fObs_comp L (hfd.comp measurable_snd) (measurable_fst.comp measurable_fst)
      (measurable_snd.comp measurable_fst)
  have hsumD : Integrable (fun d : DemandPath => ∑ i : Fin L, |(d i : ℝ)|) μ := by
    refine integrable_finset_sum _ fun i _ => ?_
    have : Integrable (fun d : DemandPath => (d (i : ℕ) : ℝ)) μ := by
      have hmap : μ.map (fun d : DemandPath => d (i : ℕ)) = P.law := by
        rw [hμ, demandPathLaw]; exact Measure.infinitePi_map_eval _ (i : ℕ)
      have := P.finiteMean
      rw [← hmap] at this
      exact this.comp_measurable (measurable_pi_apply (i : ℕ))
    exact this.abs
  have hGint : Integrable (fun w : ((Fin L → ℝ) × ℝ) × DemandPath =>
      fObs L (firstDemands L w.2) w.1.1 w.1.2) (ν.prod μ) := by
    refine Integrable.mono' ((hbound_int.comp_fst μ).add ((hsumD.const_mul (L : ℝ)).comp_snd ν))
      hGm.aestronglyMeasurable (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs]
    have := abs_fObs_le L (firstDemands L w.2) w.1.1 w.1.2
    simp only [firstDemands] at this
    simp only [Pi.add_apply]
    linarith
  rw [integral_prod_symm _ hGint] at hE
  -- the Jensen lower bound integrated over the demands
  have hJint : Integrable (fun d : DemandPath => fObs L (firstDemands L d) (fun _ => a0) e) μ := by
    refine Integrable.mono' ((hsumD.const_mul (L : ℝ)).add (integrable_const
      ((L : ℝ) * ∑ _i : Fin L, |a0| + |e|)))
      (measurable_fObs_comp L hfd measurable_const measurable_const).aestronglyMeasurable
      (ae_of_all _ fun d => ?_)
    rw [Real.norm_eq_abs]
    have := abs_fObs_le L (firstDemands L d) (fun _ => a0) e
    simp only [firstDemands] at this
    simp only [Pi.add_apply]
    have hmul : (L : ℝ) * (∑ _i : Fin L, |a0| + ∑ i : Fin L, |(d (i : ℕ) : ℝ)|) =
        (L : ℝ) * ∑ i : Fin L, |(d (i : ℕ) : ℝ)| + (L : ℝ) * ∑ _i : Fin L, |a0| := by ring
    linarith
  have hstep : ∫ d, fObs L (firstDemands L d) (fun _ => a0) e ∂μ ≤ e := by
    have h1 := integral_mono hJint hGint.integral_prod_right (fun d => hjensen (firstDemands L d))
    rw [← hE] at h1
    exact h1
  -- exchangeability: reverse the first `L` demands
  set T : DemandPath → ℝ := fun d => (Finset.range (L + 1)).sup' Finset.nonempty_range_add_one
    (fun j => (j : ℝ) * a0 - ∑ i ∈ Finset.Icc 1 j, (d (i - 1) : ℝ) + if j = L then e else 0)
    with hT
  have hrev : ∀ d : DemandPath,
      T (fun k => d (revPerm L k)) = fObs L (firstDemands L d) (fun _ => a0) e := by
    intro d
    simp only [hT, fObs_eq]
    refine Finset.sup'_congr _ rfl ?_
    intro j hj
    have hjL : j ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    unfold piece
    have hsum : ∑ i ∈ Finset.Icc 1 j, (vget (fun _ : Fin L => a0) (L - i) -
        vget (firstDemands L d) (L - i)) =
        (j : ℝ) * a0 - ∑ i ∈ Finset.Icc 1 j, (d (revPerm L (i - 1)) : ℝ) := by
      rw [Finset.sum_sub_distrib]
      congr 1
      · rw [Finset.sum_congr rfl (g := fun _ => a0) (fun i hi => by
          have := (Finset.mem_Icc.mp hi).1
          unfold vget; rw [dif_pos (by omega)])]
        simp
      · refine Finset.sum_congr rfl (fun i hi => ?_)
        have h1 := (Finset.mem_Icc.mp hi).1
        have h2 := (Finset.mem_Icc.mp hi).2
        unfold vget firstDemands
        rw [dif_pos (by omega)]
        have : revPerm L (i - 1) = L - i := by
          show revFun L (i - 1) = L - i
          unfold revFun; rw [if_pos (by omega)]; omega
        rw [this]
    rw [hsum]
  have hTm : Measurable T := by
    simp only [hT]
    apply Finset.measurable_range_sup''
    intro k _
    fun_prop
  have hexch : ∫ d, T d ∂μ = ∫ d, fObs L (firstDemands L d) (fun _ => a0) e ∂μ := by
    have hφ : Measurable (fun d : DemandPath => fun k => d (revPerm L k)) :=
      measurable_pi_lambda _ fun k => measurable_pi_apply _
    calc ∫ d, T d ∂μ = ∫ d, T d ∂(μ.map (fun d : DemandPath => fun k => d (revPerm L k))) := by
          rw [hμ, map_rev P L]
      _ = ∫ d, T (fun k => d (revPerm L k)) ∂μ :=
          integral_map hφ.aemeasurable hTm.aestronglyMeasurable
      _ = _ := by congr 1; funext d; exact hrev d
  calc ∫ d, T d ∂μ = _ := hexch
    _ ≤ e := hstep
