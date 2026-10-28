-- Prove2me | solution 1 for KleywegtSAA.ValueCLT.scaled_gap_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:11:40.707877+00:00
-- url     : https://prove2.me/submissions/77a2927e-d37c-4030-a760-1bca705ac084

import Mathlib
import Definitions.Def_KleywegtSAA_ValueCLT_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace Aux_KSAA_sg

lemma meas_inf' {ι α : Type*} [MeasurableSpace α] (s : Finset ι) (hs : s.Nonempty)
    (f : ι → α → ℝ) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun a => s.inf' hs (fun i => f i a)) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i =>
    simp only [Finset.inf'_singleton]
    exact hf i (Finset.mem_singleton_self i)
  | cons i s hi hs ih =>
    have e : (fun a => (Finset.cons i s hi).inf' (Finset.cons_nonempty hi) (fun j => f j a)) =
        fun a => (f i a ⊓ s.inf' hs (fun j => f j a) : ℝ) := by
      funext a; exact Finset.inf'_cons (H := hs) (f := fun j => f j a)
    rw [e]
    exact (hf i (Finset.mem_cons_self i s)).inf
      (ih (fun j hj => hf j (Finset.mem_cons_of_mem hj)))

open KleywegtSAA.ValueCLT in
theorem vhat_ev
    {X : Type*} (S : Finset X) (hS : S.Nonempty)
    {𝒲 : Type*} [MeasurableSpace 𝒲] (G : X → 𝒲 → ℝ) (hG : ∀ x ∈ S, Measurable (G x))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℕ → Ω → 𝒲) (hWm : ∀ n, Measurable (W n)) (hind : iIndepFun W P)
    (hid : ∀ n, IdentDistrib (W n) (W 0) P P)
    (hint : ∀ x ∈ S, Integrable (fun ω => G x (W 0 ω)) P) :
    ∀ᵐ ω ∂P, ∀ᶠ N in atTop,
      S.inf' hS (KleywegtSAA.ExpRate.sampleObj G W N ω) - minOnOpt S hS G P W N ω = 0 := by
  classical
  set g := KleywegtSAA.ExpRate.trueObj G P W with hg
  -- strong law for every x ∈ S
  have hslln : ∀ x ∈ S, ∀ᵐ ω ∂P,
      Tendsto (fun N => KleywegtSAA.ExpRate.sampleObj G W N ω x) atTop (𝓝 (g x)) := by
    intro x hx
    have hind' : iIndepFun (fun i ω => G x (W i ω)) P :=
      hind.comp (fun _ => G x) (fun _ => hG x hx)
    have h := strong_law_ae_real (μ := P) (fun i ω => G x (W i ω)) (hint x hx)
      (fun i j hij => hind'.indepFun hij) (fun i => (hid i).comp (hG x hx))
    filter_upwards [h] with ω hω
    have e : (fun N => KleywegtSAA.ExpRate.sampleObj G W N ω x) =
        fun N : ℕ => (∑ i ∈ Finset.range N, G x (W i ω)) / N := by
      funext N
      simp only [KleywegtSAA.ExpRate.sampleObj, one_div_mul_eq_div]
    rw [e]
    exact hω
  have hall : ∀ᵐ ω ∂P, ∀ x ∈ S,
      Tendsto (fun N => KleywegtSAA.ExpRate.sampleObj G W N ω x) atTop (𝓝 (g x)) :=
    (eventually_all_finset S).mpr hslln
  filter_upwards [hall] with ω hω
  set m := S.inf' hS g with hm
  set T := S.filter (fun x => m < g x) with hT
  set δ : ℝ := if hTne : T.Nonempty then T.inf' hTne g - m else 1 with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    split_ifs with hTne
    · obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_inf' hTne g
      rw [hxe]
      have := (Finset.mem_filter.mp hx).2
      linarith
    · norm_num
  have hgap : ∀ x ∈ S, x ∉ optSet S hS g → m + δ ≤ g x := by
    intro x hx hxo
    have hlt : m < g x := by
      by_contra hc
      push_neg at hc
      exact hxo (Finset.mem_filter.mpr ⟨hx, hc⟩)
    have hxT : x ∈ T := Finset.mem_filter.mpr ⟨hx, hlt⟩
    have hTne : T.Nonempty := ⟨x, hxT⟩
    rw [hδ, dif_pos hTne]
    have := Finset.inf'_le g hxT
    linarith
  have hev : ∀ᶠ N in atTop, ∀ x ∈ S,
      |KleywegtSAA.ExpRate.sampleObj G W N ω x - g x| < δ / 2 := by
    apply (eventually_all_finset S).mpr
    intro x hx
    have := (hω x hx)
    have h2 : ∀ᶠ N in atTop, dist (KleywegtSAA.ExpRate.sampleObj G W N ω x) (g x) < δ / 2 :=
      this.eventually (Metric.ball_mem_nhds _ (by linarith))
    filter_upwards [h2] with N hN
    rwa [Real.dist_eq] at hN
  filter_upwards [hev] with N hN
  set gh := KleywegtSAA.ExpRate.sampleObj G W N ω with hgh
  have hopt_sub : optSet S hS g ⊆ S := Finset.filter_subset _ _
  have hmin : minOnOpt S hS G P W N ω = (optSet S hS g).inf' (optSet_nonempty S hS g) gh := rfl
  rw [hmin, sub_eq_zero]
  apply le_antisymm
  · exact Finset.inf'_mono gh hopt_sub (optSet_nonempty S hS g)
  · apply Finset.le_inf'
    intro x hx
    by_cases hxo : x ∈ optSet S hS g
    · exact Finset.inf'_le gh hxo
    · obtain ⟨xs, hxs, hxse⟩ := Finset.exists_mem_eq_inf' hS g
      have hxso : xs ∈ optSet S hS g := Finset.mem_filter.mpr ⟨hxs, by rw [← hxse]⟩
      have h1 := hgap x hx hxo
      have h2 := abs_lt.mp (hN x hx)
      have h3 := abs_lt.mp (hN xs hxs)
      have h4 : g xs = m := hxse.symm
      have h5 := Finset.inf'_le gh hxso
      linarith [h1, h2.1, h3.2]

end Aux_KSAA_sg

open KleywegtSAA.ValueCLT in
theorem solution
    {X : Type*} (S : Finset X) (hS : S.Nonempty)
    {𝒲 : Type*} [MeasurableSpace 𝒲] (G : X → 𝒲 → ℝ) (hG : ∀ x ∈ S, Measurable (G x))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℕ → Ω → 𝒲) (hWm : ∀ n, Measurable (W n)) (hind : iIndepFun W P)
    (hid : ∀ n, IdentDistrib (W n) (W 0) P P)
    (hint : ∀ x ∈ S, Integrable (fun ω => G x (W 0 ω)) P) :
    (∀ᵐ ω ∂P, Tendsto (fun N : ℕ =>
        Real.sqrt N * (S.inf' hS (KleywegtSAA.ExpRate.sampleObj G W N ω) - minOnOpt S hS G P W N ω)) atTop (𝓝 0)) ∧
    TendstoInMeasure P (fun (N : ℕ) ω =>
        Real.sqrt N * (S.inf' hS (KleywegtSAA.ExpRate.sampleObj G W N ω) - minOnOpt S hS G P W N ω))
      atTop (fun _ => 0) := by
  have hev := Aux_KSAA_sg.vhat_ev S hS G hG P W hWm hind hid hint
  have hae : ∀ᵐ ω ∂P, Tendsto (fun N : ℕ =>
      Real.sqrt N * (S.inf' hS (KleywegtSAA.ExpRate.sampleObj G W N ω) - minOnOpt S hS G P W N ω))
        atTop (𝓝 0) := by
    filter_upwards [hev] with ω hω
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hω] with N hN
    rw [hN, mul_zero]
  refine ⟨hae, tendstoInMeasure_of_tendsto_ae (fun N => ?_) hae⟩
  have hsm : ∀ x ∈ S, Measurable (fun ω => KleywegtSAA.ExpRate.sampleObj G W N ω x) := by
    intro x hx
    unfold KleywegtSAA.ExpRate.sampleObj
    exact measurable_const.mul (Finset.measurable_sum _ (fun n _ => (hG x hx).comp (hWm n)))
  have h1 : Measurable (fun ω => S.inf' hS (KleywegtSAA.ExpRate.sampleObj G W N ω)) :=
    Aux_KSAA_sg.meas_inf' S hS (fun x ω => KleywegtSAA.ExpRate.sampleObj G W N ω x) hsm
  have h2 : Measurable (fun ω => minOnOpt S hS G P W N ω) := by
    unfold minOnOpt
    exact Aux_KSAA_sg.meas_inf' _ _ (fun x ω => KleywegtSAA.ExpRate.sampleObj G W N ω x)
      (fun x hx => hsm x (Finset.mem_filter.mp hx).1)
  exact (measurable_const.mul (h1.sub h2)).aestronglyMeasurable
