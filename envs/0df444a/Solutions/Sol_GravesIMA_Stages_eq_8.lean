-- Prove2me | solution 1 for GravesIMA.Stages.eq_8
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:06:02.455344+00:00
-- url     : https://prove2.me/submissions/dfe73d9a-3fc9-4da6-9e93-5358585d8f8a

import Mathlib
import Definitions.Def_GravesIMA_Stages_Model

set_option autoImplicit false
open GravesIMA.Stages

lemma gis_err {μ a : ℝ} {L : ℕ} {e d F q x : ℤ → ℝ} (h : IsStage μ a L e d F q x)
    (t : ℤ) (ht : 1 ≤ t) : d t - F t = e t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  induction t, ht using Int.le_induction with
  | base => rw [h1, h3]; ring
  | succ t ht ih =>
    have h2' := h2 (t + 1) (by omega)
    simp only [add_sub_cancel_right] at h2'
    have hd : d t = F t + e t := by linarith
    rw [h2', h4 t ht, hd]; ring

lemma gis_Fstep {μ a : ℝ} {L : ℕ} {e d F q x : ℤ → ℝ} (h : IsStage μ a L e d F q x)
    (t : ℤ) (ht : 1 ≤ t) : F (t + 1) = F t + a * e t := by
  have := gis_err h t ht
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  rw [h4 t ht]
  have hd : d t = F t + e t := by linarith
  rw [hd]; ring

lemma gis_Ico_succ (m : ℤ → ℝ) (s : ℤ) (hs : 1 ≤ s) :
    ∑ j ∈ Finset.Ico (1 : ℤ) (s + 1), m j = ∑ j ∈ Finset.Ico (1 : ℤ) s, m j + m s := by
  have : Finset.Ico (1 : ℤ) (s + 1) = insert s (Finset.Ico (1 : ℤ) s) := by
    ext j; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  rw [this, Finset.sum_insert (by simp), add_comm]

lemma gis_d {μ a : ℝ} {L : ℕ} {e d F q x : ℤ → ℝ} (h : IsStage μ a L e d F q x)
    (t : ℤ) (ht : 1 ≤ t) : d t = e t + a * ∑ j ∈ Finset.Ico (1 : ℤ) t, e j + μ := by
  have h1 := h.1
  have h2 := h.2.1
  induction t, ht using Int.le_induction with
  | base => rw [h1]; simp; ring
  | succ t ht ih =>
    have h2' := h2 (t + 1) (by omega)
    simp only [add_sub_cancel_right] at h2'
    rw [h2', ih, gis_Ico_succ e t ht]; ring

lemma gis_q {μ a : ℝ} {L : ℕ} {e d F q x : ℤ → ℝ} (h : IsStage μ a L e d F q x)
    (t : ℤ) (ht : 1 ≤ t) :
    q t = (1 + (L : ℝ) * a) * e t + a * ∑ j ∈ Finset.Ico (1 : ℤ) t, e j + μ := by
  have hq := h.2.2.2.2.2.1 t ht
  have hF := gis_Fstep h t ht
  rw [hq, gis_d h t ht, hF]; ring

lemma gis_F {μ a : ℝ} {L : ℕ} {e d F q x : ℤ → ℝ} (h : IsStage μ a L e d F q x)
    (t : ℤ) (ht : 1 ≤ t) : F (t + 1) = a * ∑ j ∈ Finset.Icc (1 : ℤ) t, e j + μ := by
  have h3 := h.2.2.1
  induction t, ht using Int.le_induction with
  | base => rw [gis_Fstep h 1 le_rfl, h3]; simp; ring
  | succ t ht ih =>
    rw [gis_Fstep h (t + 1) (by omega), ih]
    have : Finset.Icc (1 : ℤ) (t + 1) = insert (t + 1) (Finset.Icc (1 : ℤ) t) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [this, Finset.sum_insert (by simp)]; ring

/-- prefix sums of masked shocks -/
noncomputable def gisP (m : ℤ → ℝ) (s : ℤ) : ℝ := ∑ j ∈ Finset.Ico (1 : ℤ) s, m j

lemma gisP_succ (m : ℤ → ℝ) (hm : ∀ s, s ≤ 0 → m s = 0) (s : ℤ) :
    gisP m (s + 1) = gisP m s + m s := by
  rcases le_or_gt 1 s with hs | hs
  · exact gis_Ico_succ m s hs
  · have h0 : m s = 0 := hm s (by omega)
    have e1 : Finset.Ico (1 : ℤ) (s + 1) = ∅ := by
      ext j; simp only [Finset.mem_Ico]; simp; omega
    have e2 : Finset.Ico (1 : ℤ) s = ∅ := by
      ext j; simp only [Finset.mem_Ico]; simp; omega
    simp [gisP, e1, e2, h0]

lemma gisP_of_le (m : ℤ → ℝ) (s : ℤ) (hs : s ≤ 1) : gisP m s = 0 := by
  have e2 : Finset.Ico (1 : ℤ) s = ∅ := by
    ext j; simp only [Finset.mem_Ico]; simp; omega
  simp [gisP, e2]

/-- telescoping identity for the weighted window sums -/
lemma gis_tele (c a : ℝ) (m : ℤ → ℝ) (hm : ∀ s, s ≤ 0 → m s = 0) (t : ℤ) (K : ℕ) :
    ∑ i ∈ Finset.range K, m (t - i) * (c + i * a) - ∑ i ∈ Finset.range K, m (t - 1 - i) * (c + i * a)
      = (c * m t + a * gisP m t) - ((c + K * a) * m (t - K) + a * gisP m (t - K)) := by
  induction K with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hP := gisP_succ m hm (t - n - 1)
    have e : t - n - 1 + 1 = t - n := by ring
    rw [e] at hP
    have e2 : t - 1 - (n : ℤ) = t - n - 1 := by ring
    have e3 : t - ((n + 1 : ℕ) : ℤ) = t - n - 1 := by push_cast; ring
    rw [e2, e3]
    push_cast
    rw [hP] at ih
    linarith

lemma gis_masked_zero (e : ℤ → ℝ) : ∀ s : ℤ, s ≤ 0 → (fun s : ℤ => if 1 ≤ s then e s else 0) s = 0 := by
  intro s hs; simp only; rw [if_neg (by omega)]

lemma gisP_eq (e : ℤ → ℝ) (s : ℤ) :
    gisP (fun s : ℤ => if 1 ≤ s then e s else 0) s = ∑ j ∈ Finset.Ico (1 : ℤ) s, e j := by
  unfold gisP
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_Ico] at hj
  simp [hj.1]

lemma gis_q_all {μ a : ℝ} {L : ℕ} {e d F q x : ℤ → ℝ} (h : IsStage μ a L e d F q x) (s : ℤ) :
    q s = (1 + (L : ℝ) * a) * (fun s : ℤ => if 1 ≤ s then e s else 0) s
      + a * gisP (fun s : ℤ => if 1 ≤ s then e s else 0) s + μ := by
  rcases le_or_gt 1 s with hs | hs
  · rw [gis_q h s hs, gisP_eq]; simp [hs]
  · have h5 := h.2.2.2.2.1 s (by omega)
    rw [h5, gisP_of_le _ s (by omega)]; simp [not_le.mpr hs]

lemma gis_G {μ α : ℝ} (hα0 : 0 ≤ α) {L K : ℕ} {ε d F q x G p y : ℤ → ℝ}
    (h : IsTwoStage μ α L K ε d F q x G p y) (t : ℤ) (ht : 1 ≤ t) : G t = F t := by
  obtain ⟨hs, hu⟩ := h
  obtain ⟨u1, u2, u3, u4, u5⟩ := hu
  have hpos : (1 + (L : ℝ) * α) ≠ 0 := by positivity
  have hbeta : upBeta α L * (1 + (L : ℝ) * α) = α := by
    unfold upBeta; field_simp
  induction t, ht using Int.le_induction with
  | base => rw [u1, hs.2.2.1]
  | succ t ht ih =>
    have hq : q t = F t + (1 + (L : ℝ) * α) * ε t := by
      have e1 := hs.2.2.2.2.2.1 t ht
      have e2 := gis_err hs t ht
      have e3 := gis_Fstep hs t ht
      rw [e1, e3]; linarith
    rw [u2 t ht, gis_Fstep hs t ht, ih, hq]
    linear_combination (ε t) * hbeta

lemma gis_p_all {μ α : ℝ} (hα0 : 0 ≤ α) {L K : ℕ} {ε d F q x G p y : ℤ → ℝ}
    (h : IsTwoStage μ α L K ε d F q x G p y) (s : ℤ) :
    p s = (1 + ((L : ℝ) + K) * α) * (fun s : ℤ => if 1 ≤ s then ε s else 0) s
      + α * gisP (fun s : ℤ => if 1 ≤ s then ε s else 0) s + μ := by
  rcases le_or_gt 1 s with hs | hs
  · have hp := h.2.2.2.2.1 s hs
    have hG1 := gis_G hα0 h s hs
    have hG2 := gis_G hα0 h (s + 1) (by omega)
    have hF := gis_Fstep h.1 s hs
    have hq := gis_q h.1 s hs
    rw [hp, hG2, hG1, hF, hq, gisP_eq]
    simp [hs]; ring
  · have h5 := h.2.2.2.1 s (by omega)
    rw [h5, gisP_of_le _ s (by omega)]; simp [not_le.mpr hs]

lemma gis_p1 (μ a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (L : ℕ) (e d F q x : ℤ → ℝ)
    (h : IsStage μ a L e d F q x) (t : ℤ) (ht : 1 ≤ t) :
    x t = x 0 - ∑ i ∈ Finset.range L, masked e (t - (i : ℤ)) * (1 + (i : ℝ) * a) := by
  have hm : ∀ s : ℤ, s ≤ 0 → (fun s : ℤ => if 1 ≤ s then e s else 0) s = 0 :=
    gis_masked_zero e
  have hmm : masked e = fun s : ℤ => if 1 ≤ s then e s else 0 := rfl
  rw [hmm]
  have h7 := h.2.2.2.2.2.2
  have key : ∀ t : ℤ, 0 ≤ t → x t = x 0 - ∑ i ∈ Finset.range L,
      (fun s : ℤ => if 1 ≤ s then e s else 0) (t - (i : ℤ)) * (1 + (i : ℝ) * a) := by
    intro t ht
    induction t, ht using Int.le_induction with
    | base =>
      rw [Finset.sum_eq_zero]; · simp
      intro i _
      rw [hm (0 - (i : ℤ)) (by omega)]; simp
    | succ t ht ih =>
      have hx := h7 (t + 1) (by omega)
      have hT := gis_tele 1 a _ hm (t + 1) L
      simp only [add_sub_cancel_right] at hT
      have hd := gis_d h (t + 1) (by omega)
      have hdd : d (t + 1) = (fun s : ℤ => if 1 ≤ s then e s else 0) (t + 1)
          + a * gisP (fun s : ℤ => if 1 ≤ s then e s else 0) (t + 1) + μ := by
        rw [hd, gisP_eq]; simp [show 1 ≤ t + 1 by omega]
      have hqq := gis_q_all h (t + 1 - (L : ℤ))
      simp only [add_sub_cancel_right] at hx
      rw [hx, hdd, hqq]
      push_cast at hT
      rw [ih]
      beta_reduce at *
      linarith
  exact key t (by omega)

lemma gis_p2 (μ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (L K : ℕ) (ε d F q x G p y : ℤ → ℝ)
    (h : IsTwoStage μ α L K ε d F q x G p y) (t : ℤ) (ht : 1 ≤ t) :
    y t = y 0 - ∑ i ∈ Finset.range K, masked ε (t - (i : ℤ)) * (1 + ((L : ℝ) + i) * α) := by
  have hm : ∀ s : ℤ, s ≤ 0 → (fun s : ℤ => if 1 ≤ s then ε s else 0) s = 0 :=
    gis_masked_zero ε
  have hmm : masked ε = fun s : ℤ => if 1 ≤ s then ε s else 0 := rfl
  rw [hmm]
  have h5 := h.2.2.2.2.2
  have hw : ∀ t : ℤ, ∑ i ∈ Finset.range K,
      (fun s : ℤ => if 1 ≤ s then ε s else 0) (t - (i : ℤ)) * (1 + ((L : ℝ) + i) * α)
      = ∑ i ∈ Finset.range K,
      (fun s : ℤ => if 1 ≤ s then ε s else 0) (t - (i : ℤ)) * ((1 + (L : ℝ) * α) + i * α) := by
    intro t
    apply Finset.sum_congr rfl
    intro i _; ring
  simp only [hw]
  have key : ∀ t : ℤ, 0 ≤ t → y t = y 0 - ∑ i ∈ Finset.range K,
      (fun s : ℤ => if 1 ≤ s then ε s else 0) (t - (i : ℤ)) * ((1 + (L : ℝ) * α) + i * α) := by
    intro t ht
    induction t, ht using Int.le_induction with
    | base =>
      rw [Finset.sum_eq_zero]; · simp
      intro i _
      rw [hm (0 - (i : ℤ)) (by omega)]; simp
    | succ t ht ih =>
      have hy := h5 (t + 1) (by omega)
      have hT := gis_tele (1 + (L : ℝ) * α) α _ hm (t + 1) K
      simp only [add_sub_cancel_right] at hT
      have hqq := gis_q_all h.1 (t + 1)
      have hpp := gis_p_all hα0 h (t + 1 - (K : ℤ))
      simp only [add_sub_cancel_right] at hy
      rw [hy, hqq, hpp]
      push_cast at hT
      rw [ih]
      beta_reduce at *
      linarith
  exact key t (by omega)


open MeasureTheory ProbabilityTheory
open scoped NNReal

lemma gis_gauss_sum {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [DecidableEq ι]
    (X : ι → Ω → ℝ) (hind : iIndepFun X P) (hmeas : ∀ i, Measurable (X i)) (v : ι → ℝ≥0)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i)) (s : Finset ι) :
    P.map (fun ω => ∑ i ∈ s, X i ω) = gaussianReal 0 (∑ i ∈ s, v i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp [gaussianReal_zero_var]
  | insert a s ha ih =>
    have hindep : IndepFun (fun ω => ∑ i ∈ s, X i ω) (X a) P := by
      have := hind.indepFun_finset_sum_of_notMem hmeas ha
      have e : (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, X i := by
        ext ω; simp [Finset.sum_apply]
      rw [e]; exact this
    have h := gaussianReal_add_gaussianReal_of_indepFun hindep ih (hlaw a)
    rw [Finset.sum_insert ha]
    have e : (fun ω => ∑ i ∈ insert a s, X i ω) = (fun ω => ∑ i ∈ s, X i ω) + X a := by
      ext ω; simp [Finset.sum_insert ha, add_comm]
    rw [e, h]
    simp [add_comm]

lemma gis_law_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (X : Ω → ℝ)
    (hX : Measurable X) (v : ℝ≥0) (hl : P.map X = gaussianReal 0 v) (c : ℝ) :
    P.map (fun ω => c * X ω) = gaussianReal 0 (Real.toNNReal (c ^ 2) * v) := by
  have : (fun ω => c * X ω) = (fun x : ℝ => c * x) ∘ X := rfl
  rw [this, ← Measure.map_map (measurable_const_mul c) hX, hl, gaussianReal_map_const_mul,
    mul_zero]
  congr 2
  exact NNReal.eq (by simp [Real.coe_toNNReal _ (sq_nonneg c)])

lemma gis_window {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (σ : ℝ) (ε : ℤ → Ω → ℝ) (hmeas : ∀ t, Measurable (ε t))
    (hind : iIndepFun (fun t : {s : ℤ // 1 ≤ s} => ε t) P)
    (hlaw : ∀ t : ℤ, 1 ≤ t → P.map (ε t) = gaussianReal 0 (Real.toNNReal (σ ^ 2)))
    (t : ℤ) (K : ℕ) (hK : (K : ℤ) ≤ t) (w : ℕ → ℝ) (z0 : ℝ) (ht : 1 ≤ t) :
    P.map (fun ω => z0 - ∑ i ∈ Finset.range K, w i * ε (t - i) ω)
      = gaussianReal z0 (Real.toNNReal (σ ^ 2 * ∑ i ∈ Finset.range K, (w i) ^ 2)) := by
  classical
  let g : Fin K → {s : ℤ // 1 ≤ s} := fun i => ⟨t - (i : ℕ), by have := i.2; omega⟩
  have hg : Function.Injective g := by
    intro i j hij
    simp only [g, Subtype.mk.injEq] at hij
    apply Fin.ext; omega
  let X : Fin K → Ω → ℝ := fun i ω => w i * ε (t - (i : ℕ)) ω
  have hindX : iIndepFun X P := by
    have h1 := hind.precomp hg
    exact h1.comp (fun i x => w i * x) (fun i => measurable_const_mul _)
  have hmeasX : ∀ i, Measurable (X i) := fun i => measurable_const_mul _ |>.comp (hmeas _)
  let v : Fin K → ℝ≥0 := fun i => Real.toNNReal ((w i) ^ 2) * Real.toNNReal (σ ^ 2)
  have hlawX : ∀ i, P.map (X i) = gaussianReal 0 (v i) := by
    intro i
    exact gis_law_mul (ε (t - (i : ℕ))) (hmeas _) _ (hlaw _ (by have := i.2; omega)) (w i)
  have hS := gis_gauss_sum X hindX hmeasX v hlawX Finset.univ
  have hS' : ∀ ω, ∑ i : Fin K, X i ω = ∑ i ∈ Finset.range K, w i * ε (t - i) ω := fun ω =>
    Fin.sum_univ_eq_sum_range (fun i => w i * ε (t - (i : ℕ)) ω) K
  simp_rw [hS'] at hS
  have hSm : Measurable (fun ω => ∑ i ∈ Finset.range K, w i * ε (t - i) ω) :=
    Finset.measurable_sum _ (fun i _ => measurable_const_mul _ |>.comp (hmeas _))
  have e : (fun ω => z0 - ∑ i ∈ Finset.range K, w i * ε (t - i) ω)
      = (fun s : ℝ => z0 - s) ∘
        (fun ω => ∑ i ∈ Finset.range K, w i * ε (t - i) ω) := rfl
  have hm0 : Measurable (fun s : ℝ => z0 - s) := by fun_prop
  rw [e, ← Measure.map_map hm0 hSm, hS,
    gaussianReal_map_const_sub, sub_zero]
  have hvar : (∑ i : Fin K, v i) = Real.toNNReal (σ ^ 2 * ∑ i ∈ Finset.range K, (w i) ^ 2) := by
    apply NNReal.eq
    simp only [NNReal.coe_sum, NNReal.coe_mul, v, Real.coe_toNNReal _ (sq_nonneg σ)]
    rw [Real.coe_toNNReal _ (by positivity), Finset.mul_sum,
      ← Fin.sum_univ_eq_sum_range (fun i => σ ^ 2 * w i ^ 2) K]
    apply Finset.sum_congr rfl; intro i _
    rw [Real.coe_toNNReal _ (sq_nonneg _)]
    ring
  rw [hvar]

lemma gis_sumsq (α : ℝ) (L : ℕ) :
    ∑ i ∈ Finset.range L, (1 + (i : ℝ) * α) ^ 2 =
      (L : ℝ) * (1 + α * ((L : ℝ) - 1) + α ^ 2 * ((L : ℝ) - 1) * (2 * (L : ℝ) - 1) / 6) := by
  induction L with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast; ring

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (σ : ℝ) (ε : ℤ → Ω → ℝ) (hmeas : ∀ t, Measurable (ε t))
    (hind : iIndepFun (fun t : {s : ℤ // 1 ≤ s} => ε t) P)
    (hlaw : ∀ t : ℤ, 1 ≤ t → P.map (ε t) = gaussianReal 0 (Real.toNNReal (σ ^ 2)))
    (μ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (L : ℕ) (d F q x : ℤ → Ω → ℝ)
    (hsys : ∀ ω, IsStage μ α L (fun s => ε s ω) (fun s => d s ω) (fun s => F s ω)
      (fun s => q s ω) (fun s => x s ω))
    (x0 : ℝ) (hx0 : ∀ ω, x 0 ω = x0) (t : ℤ) (ht1 : 1 ≤ t) (htL : (L : ℤ) ≤ t) :
    P.map (x t) =
        gaussianReal x0 (Real.toNNReal (σ ^ 2 * ∑ i ∈ Finset.range L, (1 + (i : ℝ) * α) ^ 2)) ∧
      ∑ i ∈ Finset.range L, (1 + (i : ℝ) * α) ^ 2 =
        (L : ℝ) * (1 + α * ((L : ℝ) - 1) + α ^ 2 * ((L : ℝ) - 1) * (2 * (L : ℝ) - 1) / 6) := by
  refine ⟨?_, ?_⟩
  · have key : x t = fun ω => x0 - ∑ i ∈ Finset.range L, (1 + (i : ℝ) * α) * ε (t - i) ω := by
      ext ω
      have h := gis_p1 μ α hα0 hα1 L (fun s => ε s ω) (fun s => d s ω) (fun s => F s ω)
        (fun s => q s ω) (fun s => x s ω) (hsys ω) t ht1
      rw [h, hx0 ω]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      unfold masked
      rw [if_pos (by omega)]; ring
    rw [key]
    exact gis_window P σ ε hmeas hind hlaw t L htL (fun i => 1 + (i : ℝ) * α) x0 ht1
  · exact gis_sumsq α L
