-- Prove2me | solution 1 for HartSchmeidler.Compact.special_case
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:33:30.562982+00:00
-- url     : https://prove2.me/submissions/10751e72-b538-4e55-8a58-9d9925494f9a

import Definitions.Def_HartSchmeidler_Compact_Game



namespace HartSchmeidler.Compact

open MeasureTheory

theorem mco_core {ι : Type*} {S : ι → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] [∀ i, T2Space (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (p : Measure (Profile S)) [IsProbabilityMeasure p] (hp : p.Regular)
    (i : ι) (R : Set (S i)) (hR : MeasurableSet R) (ε : ℝ) (hε : 0 < ε) :
    ∃ F G : Set (S i), IsClosed F ∧ IsOpen G ∧ F ⊆ R ∧ R ⊆ G ∧
      p ((fun s : Profile S => s i) ⁻¹' (G \ F)) < ENNReal.ofReal ε := by
  have hπc : Continuous (fun s : Profile S => s i) := continuous_apply i
  set π : Profile S → S i := fun s => s i with hπ
  have hA : MeasurableSet (π ⁻¹' R) := hπc.measurable hR
  have hδ : (ENNReal.ofReal ε / 2) ≠ 0 := by
    simp [ENNReal.div_eq_zero_iff, hε]
  obtain ⟨C, hCA, hCc, hC⟩ := hA.exists_isCompact_sdiff_lt (μ := p) (measure_ne_top _ _) hδ
  obtain ⟨C', hCA', hCc', hC'⟩ := hA.compl.exists_isCompact_sdiff_lt (μ := p) (measure_ne_top _ _) hδ
  refine ⟨π '' C, (π '' C')ᶜ, (hCc.image hπc).isClosed, (hCc'.image hπc).isClosed.isOpen_compl, ?_, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩; exact hCA hc
  · intro r hr ⟨c', hc', hcr⟩
    exact hCA' hc' (show π c' ∈ R from by rw [hcr]; exact hr)
  · calc p (π ⁻¹' ((π '' C')ᶜ \ π '' C)) ≤ p ((π ⁻¹' R \ C) ∪ ((π ⁻¹' R)ᶜ \ C')) := by
          apply measure_mono
          intro s hs
          have h1 : s ∉ C' := fun h => hs.1 ⟨s, h, rfl⟩
          have h2 : s ∉ C := fun h => hs.2 ⟨s, h, rfl⟩
          by_cases hsA : s ∈ π ⁻¹' R
          · exact Or.inl ⟨hsA, h2⟩
          · exact Or.inr ⟨hsA, h1⟩
      _ ≤ p (π ⁻¹' R \ C) + p ((π ⁻¹' R)ᶜ \ C') := measure_union_le _ _
      _ < ENNReal.ofReal ε / 2 + ENNReal.ofReal ε / 2 := ENNReal.add_lt_add hC hC'
      _ = ENNReal.ofReal ε := ENNReal.add_halves _


lemma sc_upd_cont {ι : Type*} [DecidableEq ι] {S : ι → Type*} [∀ j, TopologicalSpace (S j)]
    (i : ι) (t : S i) : Continuous (fun s : Profile S => (Function.update s i t : Profile S)) := by
  show Continuous (fun s : ∀ j, S j => Function.update s i t)
  exact Continuous.update continuous_id i continuous_const

theorem sc_core {ι : Type*} [Nonempty ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] [∀ i, T2Space (S i)]
    [∀ i, Nonempty (S i)] [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (h : ι → Profile S → ℝ) (hcont : ∀ i, Continuous (h i))
    (ŝ : Profile S)
    (F : (∀ i, Finset (S i)) → Finset (Profile S)) (w : (∀ i, Finset (S i)) → Profile S → ℝ)
    (hFw : ∀ T, IsAnchoredFSet ŝ T → IsFSetCE h T (F T) (w T))
    (p : Measure (Profile S)) [IsProbabilityMeasure p] (hp : p.Regular)
    (hclus : ∀ (f : C(Profile S, ℝ)) (ε : ℝ), 0 < ε →
      ∀ T₀, IsAnchoredFSet ŝ T₀ → ∃ T, IsAnchoredFSet ŝ T ∧ (∀ i, T₀ i ⊆ T i) ∧
        |∫ s, f s ∂p - ∑ s ∈ F T, w T s * f s| < ε)
    (i : ι) (t : S i) (R : Set (S i)) (hR : MeasurableSet R) :
    Integrable
        (fun s : Profile S => h i s - h i (Function.update s i (specialDeviation t R (s i)))) p ∧
      0 ≤ ∫ s : Profile S, (h i s - h i (Function.update s i (specialDeviation t R (s i)))) ∂p := by
  classical
  have hπc : Continuous (fun s : Profile S => s i) := continuous_apply i
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ s, |h i s| ≤ M := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hcont i).continuousOn
    exact ⟨C, fun s => by simpa using hC s trivial⟩
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM ŝ)
  let g : Profile S → ℝ := fun s => h i s - h i (Function.update s i t)
  have hgc : Continuous g := (hcont i).sub ((hcont i).comp (sc_upd_cont i t))
  have hgb : ∀ s, |g s| ≤ 2 * M := fun s => by
    calc |g s| ≤ |h i s| + |h i (Function.update s i t)| := abs_sub _ _
      _ ≤ 2 * M := by linarith [hM s, hM (Function.update s i t)]
  let sp : Profile S → ℝ := fun s =>
    h i s - h i (Function.update s i (specialDeviation t R (s i)))
  have hsp : sp = Set.indicator ((fun s : Profile S => s i) ⁻¹' R) g := by
    funext s
    by_cases hs : s i ∈ R
    · simp [sp, specialDeviation, hs, g, Set.indicator]
    · have e2 : (Function.update s i (s i) : Profile S) = s := Function.update_eq_self i s
      simp [sp, specialDeviation, hs, e2, Set.indicator]
  have hRm : MeasurableSet ((fun s : Profile S => s i) ⁻¹' R) := hπc.measurable hR
  have hspi : Integrable sp p := by
    rw [hsp]
    refine Integrable.indicator ?_ hRm
    exact Integrable.of_bound hgc.aestronglyMeasurable (2 * M)
      (Filter.Eventually.of_forall fun s => by simpa using hgb s)
  refine ⟨hspi, ?_⟩
  by_contra hneg
  push_neg at hneg
  set δ : ℝ := -(∫ s, sp s ∂p) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set ε : ℝ := δ / (4 * (M + 1)) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨Fc, G, hFc, hGo, hFR, hRG, hFG⟩ := mco_core p hp i R hR ε hε
  obtain ⟨φ, hφ0, hφ1, hφI⟩ := exists_continuous_zero_one_of_isClosed hGo.isClosed_compl hFc
    (Set.disjoint_left.2 fun x hx hxF => hx (hRG (hFR hxF)))
  let ft : C(Profile S, ℝ) := ⟨fun s => φ (s i) * g s, (φ.continuous.comp hπc).mul hgc⟩
  -- claim 1
  have hB : MeasurableSet ((fun s : Profile S => s i) ⁻¹' (G \ Fc)) :=
    hπc.measurable (hGo.measurableSet.diff hFc.measurableSet)
  have hpt : ∀ s, ‖sp s - ft s‖ ≤ Set.indicator ((fun s : Profile S => s i) ⁻¹' (G \ Fc)) (fun _ => 2 * M) s := by
    intro s
    by_cases hsF : s i ∈ Fc
    · have h1 : φ (s i) = 1 := hφ1 hsF
      have h2 : s i ∈ R := hFR hsF
      have : sp s - ft s = 0 := by
        rw [hsp]; simp [ft, h1, h2, Set.indicator]
      rw [this]; simp only [norm_zero]
      exact Set.indicator_nonneg (fun _ _ => by linarith) s
    · by_cases hsG : s i ∈ G
      · have hmem : s ∈ (fun s : Profile S => s i) ⁻¹' (G \ Fc) := ⟨hsG, hsF⟩
        rw [Set.indicator_of_mem hmem]
        have hφb := hφI (s i)
        have hRs : sp s = (if s i ∈ R then g s else 0) := by rw [hsp]; simp [Set.indicator]
        simp only [ft, ContinuousMap.coe_mk, Real.norm_eq_abs]
        rw [hRs]
        have hgs := abs_le.1 (hgb s)
        obtain ⟨hφa, hφb'⟩ := hφb
        split_ifs
        · rw [abs_le]; constructor <;> nlinarith [hgs.1, hgs.2]
        · rw [abs_le]; constructor <;> nlinarith [hgs.1, hgs.2]
      · have h1 : φ (s i) = 0 := hφ0 hsG
        have h2 : s i ∉ R := fun hr => hsG (hRG hr)
        have : sp s - ft s = 0 := by
          rw [hsp]; simp [ft, h1, h2, Set.indicator]
        rw [this]; simp only [norm_zero]
        exact Set.indicator_nonneg (fun _ _ => by linarith) s
  have hfti : Integrable ft p :=
    Integrable.of_bound ft.continuous.aestronglyMeasurable (2 * M) (Filter.Eventually.of_forall fun s => by
      have := hφI (s i)
      simp only [ft, ContinuousMap.coe_mk, norm_mul, Real.norm_eq_abs]
      have hgs := hgb s
      rw [abs_of_nonneg this.1]
      nlinarith [abs_nonneg (g s), this.1, this.2])
  have hc1 : |∫ s, sp s ∂p - ∫ s, ft s ∂p| ≤ 2 * M * ε := by
    rw [← integral_sub hspi hfti]
    have hInd : Integrable (Set.indicator ((fun s : Profile S => s i) ⁻¹' (G \ Fc)) (fun _ => 2 * M)) p :=
      (integrable_const _).indicator hB
    have := norm_integral_le_of_norm_le hInd (Filter.Eventually.of_forall hpt)
    rw [integral_indicator_const _ hB] at this
    simp only [Real.norm_eq_abs, smul_eq_mul, measureReal_def] at this
    have hlt : (p ((fun s : Profile S => s i) ⁻¹' (G \ Fc))).toReal < ε := by
      have := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 hFG
      rwa [ENNReal.toReal_ofReal hε.le] at this
    calc |∫ s, (sp s - ft s) ∂p| ≤ (p ((fun s : Profile S => s i) ⁻¹' (G \ Fc))).toReal * (2 * M) := this
      _ ≤ ε * (2 * M) := by gcongr
      _ = 2 * M * ε := by ring
  -- claim 2
  have hc2 : -(δ / 2) < ∫ s, ft s ∂p := by
    let T₀ : ∀ j, Finset (S j) := fun j => if hj : j = i then (by subst hj; exact {ŝ j, t}) else {ŝ j}
    have hT₀i : T₀ i = {ŝ i, t} := by simp [T₀]
    have hT₀ : IsAnchoredFSet ŝ T₀ := by
      refine ⟨⟨fun j => ?_, ?_⟩, fun j => ?_⟩
      · by_cases hj : j = i
        · subst hj; rw [hT₀i]; simp
        · simp [T₀, hj]
      · apply (Set.finite_singleton i).subset
        intro j hj
        by_contra hji
        have : T₀ j = {ŝ j} := by simp [T₀, show ¬ j = i from hji]
        exact hj (by simp [this])
      · by_cases hj : j = i
        · subst hj; rw [hT₀i]; simp
        · simp [T₀, hj]
    obtain ⟨T, hT, hTT, hclose⟩ := hclus ft (δ / 2) (by positivity) T₀ hT₀
    have htT : t ∈ T i := hTT i (by rw [hT₀i]; simp)
    obtain ⟨hsupp, hw0, hw1, hce⟩ := hFw T hT
    have hsum : 0 ≤ ∑ s ∈ F T, w T s * ft s := by
      have : ∑ s ∈ F T, w T s * ft s =
          ∑ r ∈ T i, φ r * ∑ s ∈ (F T).filter (fun s : Profile S => s i = r), w T s * g s := by
        rw [← Finset.sum_fiberwise_of_maps_to (s := F T) (t := T i) (g := fun s : Profile S => s i)
          (fun s hs => hsupp s hs i)]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s hs => ?_
        have : s i = r := (Finset.mem_filter.1 hs).2
        simp only [ft, ContinuousMap.coe_mk, this]
        ring
      rw [this]
      refine Finset.sum_nonneg fun r hr => mul_nonneg (hφI r).1 ?_
      exact hce i r hr t htT
    have := (abs_lt.1 hclose).1
    linarith
  have hfinal : ∫ s, sp s ∂p > -δ := by
    have h2 := (abs_le.1 hc1).1
    have h3 : 2 * M * ε ≤ δ / 2 := by
      rw [hεdef]
      rw [show 2 * M * (δ / (4 * (M + 1))) = δ / 2 * (M / (M + 1)) by field_simp; ring]
      have : M / (M + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      nlinarith
    linarith
  rw [hδdef] at hfinal
  linarith

end HartSchmeidler.Compact

open HartSchmeidler.Compact
open MeasureTheory

theorem solution {ι : Type*} [Nonempty ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] [∀ i, T2Space (S i)]
    [∀ i, Nonempty (S i)] [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (h : ι → Profile S → ℝ) (hcont : ∀ i, Continuous (h i))
    (ŝ : Profile S)
    (F : (∀ i, Finset (S i)) → Finset (Profile S)) (w : (∀ i, Finset (S i)) → Profile S → ℝ)
    (hFw : ∀ T, IsAnchoredFSet ŝ T → IsFSetCE h T (F T) (w T))
    (p : Measure (Profile S)) [IsProbabilityMeasure p] (hp : p.Regular)
    (hclus : ∀ (f : C(Profile S, ℝ)) (ε : ℝ), 0 < ε →
      ∀ T₀, IsAnchoredFSet ŝ T₀ → ∃ T, IsAnchoredFSet ŝ T ∧ (∀ i, T₀ i ⊆ T i) ∧
        |∫ s, f s ∂p - ∑ s ∈ F T, w T s * f s| < ε)
    (i : ι) (t : S i) (R : Set (S i)) (hR : MeasurableSet R) :
    Integrable
        (fun s : Profile S => h i s - h i (Function.update s i (specialDeviation t R (s i)))) p ∧
      0 ≤ ∫ s : Profile S, (h i s - h i (Function.update s i (specialDeviation t R (s i)))) ∂p := by
  exact sc_core h hcont ŝ F w hFw p hp hclus i t R hR
