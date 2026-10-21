-- Prove2me | solution 1 for GravesIMA.Stages.eq_16
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T04:35:18.732571+00:00
-- url     : https://prove2.me/submissions/d7c047d4-0f25-4617-afec-d25c68221293

import Mathlib
import Definitions.Def_GravesIMA_Stages_Model
open MeasureTheory ProbabilityTheory

set_option autoImplicit false

namespace GravesIMA711

open GravesIMA.Stages

lemma det_closed (μ α : ℝ) (hα0 : 0 ≤ α) (L K : ℕ) (e d F q x G p y : ℤ → ℝ)
    (h : IsTwoStage μ α L K e d F q x G p y) :
    ∀ t : ℤ, 0 ≤ t → y t = y 0 -
      ∑ i ∈ Finset.range K, (1 + ((L : ℝ) + i) * α) * masked e (t - i) := by
  obtain ⟨⟨hd1, hd, hF1, hF, hq0, hq, hx⟩, ⟨hG1, hG, hp0, hp, hy⟩⟩ := h
  set β := upBeta α L with hβdef
  have hc0 : (0 : ℝ) < 1 + (L : ℝ) * α := by positivity
  have hβ : β * (1 + (L : ℝ) * α) = α := by
    rw [hβdef, upBeta]; field_simp
  -- s1: d t - F t = e t
  have s1 : ∀ t : ℤ, 1 ≤ t → d t - F t = e t := by
    intro t ht
    induction t, ht using Int.le_induction with
    | base => rw [hd1, hF1]; ring
    | succ t ht ih =>
      have h1 := hd (t + 1) (by omega)
      have h2 := hF t ht
      simp only [add_sub_cancel_right] at h1
      rw [h1, h2]; linear_combination (1 - α) * ih
  -- s2: q t = d t + L α e t
  have s2 : ∀ t : ℤ, 1 ≤ t → q t = d t + (L : ℝ) * α * e t := by
    intro t ht
    rw [hq t ht, hF t ht]; have := s1 t ht; linear_combination (L : ℝ) * α * this
  -- s3: q t - G t = (1 + L α) e t
  have s3 : ∀ t : ℤ, 1 ≤ t → q t - G t = (1 + (L : ℝ) * α) * e t := by
    intro t ht
    induction t, ht using Int.le_induction with
    | base => rw [s2 1 le_rfl, hd1, hG1]; ring
    | succ t ht ih =>
      have hq1 := s2 (t + 1) (by omega)
      have hdd := hd (t + 1) (by omega)
      simp only [add_sub_cancel_right] at hdd
      have hq0' := s2 t ht
      have hGG := hG t ht
      linear_combination hq1 + hdd - hGG - hq0' + (1 - β) * ih - e t * hβ
  -- s4: p t = q t + K α e t
  have s4 : ∀ s : ℤ, p s = q s + (K : ℝ) * α * masked e s := by
    intro s
    by_cases hs : 1 ≤ s
    · rw [hp s hs, hG s hs, masked, if_pos hs]
      have := s3 s hs
      linear_combination (K : ℝ) * β * this + (K : ℝ) * e s * hβ
    · rw [hp0 s (by omega), hq0 s (by omega), masked, if_neg hs]; ring
  -- s5: increments of q
  have s5 : ∀ s : ℤ, q s - q (s - 1) =
      (1 + (L : ℝ) * α) * masked e s - (1 + (L : ℝ) * α - α) * masked e (s - 1) := by
    intro s
    rcases lt_trichotomy s 1 with hs | hs | hs
    · rw [hq0 s (by omega), hq0 (s - 1) (by omega), masked, masked, if_neg (by omega),
        if_neg (by omega)]; ring
    · subst hs
      rw [s2 1 le_rfl, hd1, hq0 _ (by norm_num), masked, masked, if_pos le_rfl,
        if_neg (by norm_num)]; ring
    · rw [s2 s (by omega), s2 (s - 1) (by omega), hd s (by omega), masked, masked,
        if_pos (by omega), if_pos (by omega)]; ring
  -- s6: telescoping identity, by induction on the lead time
  have s6 : ∀ (k : ℕ) (t : ℤ), ∑ i ∈ Finset.range k,
      (1 + ((L : ℝ) + i) * α) * (masked e (t - i) - masked e (t - 1 - i)) =
      q t - q (t - k) - (k : ℝ) * α * masked e (t - k) := by
    intro k t
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have h5 := s5 (t - k)
      have e1 : t - 1 - (k : ℤ) = t - k - 1 := by ring
      have e2 : t - ((k + 1 : ℕ) : ℤ) = t - k - 1 := by push_cast; ring
      rw [e1, e2]
      push_cast
      linear_combination -h5
  -- s7: closed form
  intro t ht
  induction t, ht using Int.le_induction with
  | base =>
    have : ∀ i ∈ Finset.range K, (1 + ((L : ℝ) + i) * α) * masked e (0 - i) = 0 := by
      intro i _
      rw [masked, if_neg (by omega)]; ring
    rw [Finset.sum_eq_zero this]; ring
  | succ t ht ih =>
    have h6 := s6 K (t + 1)
    simp only [add_sub_cancel_right] at h6
    have hsplit : ∑ i ∈ Finset.range K, (1 + ((L : ℝ) + i) * α) * masked e (t + 1 - i) -
        ∑ i ∈ Finset.range K, (1 + ((L : ℝ) + i) * α) * masked e (t - i) =
        ∑ i ∈ Finset.range K,
          (1 + ((L : ℝ) + i) * α) * (masked e (t + 1 - i) - masked e (t - i)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _; ring
    have hyy := hy (t + 1) (by omega)
    simp only [add_sub_cancel_right] at hyy
    rw [hyy, ih, s4]
    linarith

lemma gsum {ι : Type*} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ι → Ω → ℝ) (hind : iIndepFun Z P) (hm : ∀ k, Measurable (Z k)) (v : ι → NNReal)
    (hlaw : ∀ k, P.map (Z k) = gaussianReal 0 (v k)) (S : Finset ι) :
    P.map (∑ k ∈ S, Z k) = gaussianReal 0 (∑ k ∈ S, v k) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, gaussianReal_zero_var]
    have : (0 : Ω → ℝ) = fun _ => (0 : ℝ) := rfl
    rw [this, Measure.map_const]; simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have := gaussianReal_add_gaussianReal_of_indepFun
      ((hind.indepFun_finsetSum_of_notMem hm ha).symm) (hlaw a) ih
    simpa using this

end GravesIMA711

open MeasureTheory ProbabilityTheory GravesIMA.Stages in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (σ : ℝ) (ε : ℤ → Ω → ℝ) (hmeas : ∀ t, Measurable (ε t))
    (hind : iIndepFun (fun t : {s : ℤ // 1 ≤ s} => ε t) P)
    (hlaw : ∀ t : ℤ, 1 ≤ t → P.map (ε t) = gaussianReal 0 (Real.toNNReal (σ ^ 2)))
    (μ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (L K : ℕ) (d F q x G p y : ℤ → Ω → ℝ)
    (hsys : ∀ ω, IsTwoStage μ α L K (fun s => ε s ω) (fun s => d s ω) (fun s => F s ω)
      (fun s => q s ω) (fun s => x s ω) (fun s => G s ω) (fun s => p s ω) (fun s => y s ω))
    (y0 : ℝ) (hy0 : ∀ ω, y 0 ω = y0) (t : ℤ) (ht1 : 1 ≤ t) (htK : (K : ℤ) ≤ t) :
    P.map (y t) = gaussianReal y0
      (Real.toNNReal (σ ^ 2 * ∑ i ∈ Finset.range K, (1 + ((L : ℝ) + i) * α) ^ 2)) := by
  set c : Fin K → ℝ := fun i => 1 + ((L : ℝ) + ((i : ℕ) : ℝ)) * α with hc
  let g : Fin K → {s : ℤ // 1 ≤ s} := fun i => ⟨t - ((i : ℕ) : ℤ), by have := i.isLt; omega⟩
  have hg : g.Injective := by
    intro i j hij
    simp only [g, Subtype.mk.injEq] at hij
    exact Fin.ext (by omega)
  let Z : Fin K → Ω → ℝ := fun i ω => c i * ε (t - ((i : ℕ) : ℤ)) ω
  have hindZ : iIndepFun Z P :=
    (hind.precomp hg).comp (fun i x => c i * x) (fun i => measurable_const.mul measurable_id)
  have hmZ : ∀ i, Measurable (Z i) := fun i => measurable_const.mul (hmeas _)
  have hlawZ : ∀ i, P.map (Z i) =
      gaussianReal 0 (Real.toNNReal (c i ^ 2) * Real.toNNReal (σ ^ 2)) := by
    intro i
    have hZ : Z i = (fun x => c i * x) ∘ ε (t - ((i : ℕ) : ℤ)) := rfl
    rw [hZ, ← Measure.map_map (by fun_prop : Measurable (fun x : ℝ => c i * x)) (hmeas _),
      hlaw _ (by have := i.isLt; omega), gaussianReal_map_const_mul, mul_zero,
      Real.toNNReal_of_nonneg (sq_nonneg (c i))]
  have hW := GravesIMA711.gsum P Z hindZ hmZ _ hlawZ Finset.univ
  have hdet : ∀ ω, y t ω = y0 - (∑ i, Z i) ω := by
    intro ω
    rw [GravesIMA711.det_closed μ α hα0 L K _ _ _ _ _ _ _ _ (hsys ω) t (by omega), hy0, Finset.sum_apply,
      ← Fin.sum_univ_eq_sum_range
        (fun i => (1 + ((L : ℝ) + (i : ℝ)) * α) * masked (fun s => ε s ω) (t - i)) K]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro i _
    have := i.isLt
    simp only [Z, hc, masked]
    rw [if_pos (by omega)]
  have hy : y t = (fun w => y0 - w) ∘ (∑ i, Z i) := funext hdet
  have hWm : Measurable (∑ i, Z i) := by
    have he : (∑ i, Z i) = fun a => ∑ i, Z i a := by ext; simp
    rw [he]; exact Finset.measurable_sum Finset.univ (fun i _ => hmZ i)
  rw [hy, ← Measure.map_map (by fun_prop : Measurable (fun w : ℝ => y0 - w))
    hWm, hW, gaussianReal_map_const_sub, sub_zero]
  congr 1
  apply NNReal.eq
  rw [NNReal.coe_sum, Real.coe_toNNReal _ (by positivity)]
  simp only [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg σ), Real.coe_toNNReal _ (sq_nonneg _)]
  rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range
    (fun i => σ ^ 2 * (1 + ((L : ℝ) + (i : ℝ)) * α) ^ 2) K]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp only [hc]; ring
