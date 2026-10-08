-- Prove2me | solution 1 for HartSchmeidler.Compact.general_case_of_special_case
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:31:31.575009+00:00
-- url     : https://prove2.me/submissions/5f3842de-599d-409e-b1e0-13d6e4bae378

import Definitions.Def_HartSchmeidler_Compact_Game



namespace HartSchmeidler.Compact

open MeasureTheory

theorem eup_core {ι : Type*} [Nonempty ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] [∀ i, T2Space (S i)]
    [∀ i, Nonempty (S i)] [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (h : ι → Profile S → ℝ) (hcont : ∀ i, Continuous (h i))
    (i : ι) (ε : ℝ) (hε : 0 < ε) :
    ∃ (K : ℕ) (A : Fin K → Set (S i)),
      (∀ k, MeasurableSet (A k)) ∧ (∀ k, (A k).Nonempty) ∧ Pairwise (Function.onFun Disjoint A) ∧
        (⋃ k, A k) = Set.univ ∧
        ∀ k, ∀ a ∈ A k, ∀ b ∈ A k, ∀ s : Profile S,
          |h i (Function.update s i a) - h i (Function.update s i b)| < ε := by
  classical
  -- the curried map
  have hΦ : Continuous (fun q : S i × Profile S => h i (Function.update q.2 i q.1)) := by
    apply (hcont i).comp
    show Continuous (fun q : S i × (∀ j, S j) => Function.update q.2 i q.1)
    exact Continuous.update continuous_snd i continuous_fst
  let g : C(S i, C(Profile S, ℝ)) := ContinuousMap.curry ⟨_, hΦ⟩
  have hK : IsCompact (Set.range g) := isCompact_range g.continuous
  obtain ⟨t, htK, htf, hcov⟩ := hK.finite_cover_balls (e := ε / 2) (by linarith)
  have : Fintype t := htf.fintype
  let n := Fintype.card t
  let x : Fin n → C(Profile S, ℝ) := fun k => ((Fintype.equivFin t).symm k).1
  let U : Fin n → Set (S i) := fun k => g ⁻¹' Metric.ball (x k) (ε / 2)
  have hUo : ∀ k, IsOpen (U k) := fun k => Metric.isOpen_ball.preimage g.continuous
  have hUcov : (⋃ k, U k) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro a
    have := hcov ⟨a, rfl⟩
    simp only [Set.mem_iUnion] at this
    obtain ⟨y, hy, hay⟩ := this
    refine Set.mem_iUnion.2 ⟨Fintype.equivFin t ⟨y, hy⟩, ?_⟩
    simpa [U, x] using hay
  let V : Fin n → Set (S i) := disjointed U
  have hVm : ∀ k, MeasurableSet (V k) := fun k => by
    show MeasurableSet (disjointed U k)
    rw [disjointed_apply]
    refine (hUo k).measurableSet.diff ?_
    rw [Finset.sup_set_eq_biUnion]
    exact Finset.measurableSet_biUnion _ fun j _ => (hUo j).measurableSet
  have hVd : Pairwise (Function.onFun Disjoint V) := disjoint_disjointed U
  have hVu : (⋃ k, V k) = Set.univ := by rw [iUnion_disjointed, hUcov]
  have hVU : ∀ k, V k ⊆ U k := disjointed_subset U
  let P : Set (Fin n) := {k | (V k).Nonempty}
  let e : P ≃ Fin (Fintype.card P) := Fintype.equivFin P
  refine ⟨Fintype.card P, fun j => V (e.symm j).1, fun j => hVm _, fun j => (e.symm j).2, ?_, ?_, ?_⟩
  · intro j j' hjj'
    apply hVd
    intro heq
    apply hjj'
    have : e.symm j = e.symm j' := Subtype.ext heq
    exact e.symm.injective this
  · apply Set.eq_univ_of_forall
    intro a
    have : a ∈ ⋃ k, V k := by rw [hVu]; trivial
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 this
    refine Set.mem_iUnion.2 ⟨e ⟨k, ⟨a, hk⟩⟩, ?_⟩
    simpa using hk
  · intro j a ha b hb s
    have ha' := hVU _ ha
    have hb' := hVU _ hb
    have hd : dist (g a) (g b) < ε := by
      calc dist (g a) (g b) ≤ dist (g a) (x (e.symm j).1) + dist (g b) (x (e.symm j).1) := by
            rw [dist_comm (g b)]; exact dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add ha' hb'
        _ = ε := by ring
    have := ContinuousMap.dist_apply_le_dist (f := g a) (g := g b) s
    rw [Real.dist_eq] at this
    exact lt_of_le_of_lt this hd


theorem gcs_core {ι : Type*} [Nonempty ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] [∀ i, T2Space (S i)]
    [∀ i, Nonempty (S i)] [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (h : ι → Profile S → ℝ) (hcont : ∀ i, Continuous (h i))
    (p : Measure (Profile S)) [IsProbabilityMeasure p] (i : ι)
    (hspec : ∀ (t : S i) (R : Set (S i)), MeasurableSet R →
      Integrable
          (fun s : Profile S => h i s - h i (Function.update s i (specialDeviation t R (s i)))) p ∧
        0 ≤ ∫ s : Profile S,
          (h i s - h i (Function.update s i (specialDeviation t R (s i)))) ∂p)
    (ζ : S i → S i) (hζ : Measurable ζ) :
    Integrable (fun s : Profile S => h i s - h i (Function.update s i (ζ (s i)))) p ∧
      0 ≤ ∫ s : Profile S, (h i s - h i (Function.update s i (ζ (s i)))) ∂p := by
  classical
  set f : Profile S → ℝ := fun s => h i s - h i (Function.update s i (ζ (s i))) with hf
  -- approximation
  have approx : ∀ ε : ℝ, 0 < ε → ∃ G : Profile S → ℝ, Integrable G p ∧ 0 ≤ ∫ s, G s ∂p ∧
      ∀ s, |f s - G s| < ε := by
    intro ε hε
    obtain ⟨K, A, hAm, hAne, hAd, hAu, hAosc⟩ := eup_core h hcont i ε hε
    choose a ha using hAne
    let R : Fin K → Set (S i) := fun k => ζ ⁻¹' (A k)
    have hRm : ∀ k, MeasurableSet (R k) := fun k => hζ (hAm k)
    let G : Profile S → ℝ := fun s => ∑ k, (h i s - h i (Function.update s i (specialDeviation (a k) (R k) (s i))))
    refine ⟨G, ?_, ?_, ?_⟩
    · exact integrable_finset_sum _ fun k _ => (hspec (a k) (R k) (hRm k)).1
    · rw [integral_finset_sum _ fun k _ => (hspec (a k) (R k) (hRm k)).1]
      exact Finset.sum_nonneg fun k _ => (hspec (a k) (R k) (hRm k)).2
    · intro s
      have : ζ (s i) ∈ ⋃ k, A k := by rw [hAu]; trivial
      obtain ⟨k0, hk0⟩ := Set.mem_iUnion.1 this
      have hG : G s = h i s - h i (Function.update s i (a k0)) := by
        simp only [G]
        rw [Finset.sum_eq_single k0]
        · have : s i ∈ R k0 := hk0
          simp [specialDeviation, this]
        · intro b _ hb
          have hnot : s i ∉ R b := by
            intro hsb
            have hsb' : ζ (s i) ∈ A b := hsb
            exact Set.disjoint_left.1 (hAd hb) hsb' hk0
          have e2 : (Function.update s i (s i) : Profile S) = s := Function.update_eq_self i s
          simp [specialDeviation, hnot, e2]
        · simp
      rw [hG]
      have := hAosc k0 (a k0) (ha k0) (ζ (s i)) hk0 s
      simp only [hf]
      have e3 : h i s - h i (Function.update s i (ζ (s i))) - (h i s - h i (Function.update s i (a k0)))
          = h i (Function.update s i (a k0)) - h i (Function.update s i (ζ (s i))) := by ring
      rw [e3]; exact this
  choose! G hGi hGnn hGap using fun n : ℕ => approx (1 / ((n : ℝ) + 1)) (by positivity)
  -- measurability of f
  have hlim : ∀ᵐ s ∂p, Filter.Tendsto (fun n : ℕ => G n s) Filter.atTop (nhds (f s)) := by
    refine Filter.Eventually.of_forall fun s => ?_
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Real.dist_eq, abs_sub_comm]
    exact (hGap n s).le
  have hfm : AEStronglyMeasurable f p :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop (fun n => (hGi n).aestronglyMeasurable) hlim
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ s, |h i s| ≤ M := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hcont i).continuousOn
    exact ⟨C, fun s => by simpa using hC s trivial⟩
  have hfi : Integrable f p := by
    refine Integrable.of_bound hfm (M + M) (Filter.Eventually.of_forall fun s => ?_)
    simp only [hf, Real.norm_eq_abs]
    calc |h i s - h i (Function.update s i (ζ (s i)))| ≤ |h i s| + |h i (Function.update s i (ζ (s i)))| := abs_sub _ _
      _ ≤ M + M := add_le_add (hM _) (hM _)
  refine ⟨hfi, ?_⟩
  by_contra hneg
  push_neg at hneg
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.2 hneg)
  have hc : Integrable (fun _ : Profile S => (1 / ((n : ℝ) + 1))) p := integrable_const _
  have hle : ∫ s, (G n s - 1 / ((n : ℝ) + 1)) ∂p ≤ ∫ s, f s ∂p := by
    apply integral_mono ((hGi n).sub hc) hfi
    intro s
    have := hGap n s
    rw [abs_lt] at this
    show G n s - 1 / ((n : ℝ) + 1) ≤ f s
    linarith [this.1, this.2]
  rw [integral_sub (hGi n) hc] at hle
  have h1 : ∫ s : Profile S, (1 / ((n : ℝ) + 1)) ∂p = 1 / ((n : ℝ) + 1) := by simp
  rw [h1] at hle
  linarith [hGnn n]

end HartSchmeidler.Compact

open HartSchmeidler.Compact
open MeasureTheory

theorem solution {ι : Type*} [Nonempty ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] [∀ i, T2Space (S i)]
    [∀ i, Nonempty (S i)] [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (h : ι → Profile S → ℝ) (hcont : ∀ i, Continuous (h i))
    (p : Measure (Profile S)) [IsProbabilityMeasure p] (i : ι)
    (hspec : ∀ (t : S i) (R : Set (S i)), MeasurableSet R →
      Integrable
          (fun s : Profile S => h i s - h i (Function.update s i (specialDeviation t R (s i)))) p ∧
        0 ≤ ∫ s : Profile S,
          (h i s - h i (Function.update s i (specialDeviation t R (s i)))) ∂p)
    (ζ : S i → S i) (hζ : Measurable ζ) :
    Integrable (fun s : Profile S => h i s - h i (Function.update s i (ζ (s i)))) p ∧
      0 ≤ ∫ s : Profile S, (h i s - h i (Function.update s i (ζ (s i)))) ∂p := by
  exact gcs_core h hcont p i hspec ζ hζ
