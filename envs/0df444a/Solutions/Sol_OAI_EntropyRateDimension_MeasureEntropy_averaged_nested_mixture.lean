-- Prove2me | solution 1 for OAI.EntropyRateDimension.MeasureEntropy.averaged_nested_mixture
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:02:07.435449+00:00
-- url     : https://prove2.me/submissions/2dbe8a80-73e7-4808-9cf3-5e264c55b822

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory
theorem h44_masscomp {α : Type*} {β : Type*} {γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq γ]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (hf : Measurable f)
    (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) (g : β → γ) (c : γ) :
    mass μ (g ∘ f) c = FiniteEntropy.mass s (mass μ f) g c := by
  classical
  simp only [FiniteEntropy.mass, mass, Measure.real_def]
  rw [← ENNReal.toReal_sum (fun b _ => measure_ne_top _ _)]
  congr 1
  have h := sum_measure_preimage_singleton (μ := μ) (s.filter fun b => g b = c)
    (fun y _ => hf (measurableSet_singleton y))
  change _ = ∑ b ∈ s.filter (fun b => g b = c), μ (f ⁻¹' {b})
  rw [h]
  apply measure_congr
  filter_upwards [hs] with x hx
  apply propext
  change g (f x) = c ↔ f x ∈ (s.filter fun b => g b = c)
  rw [Finset.mem_filter]
  exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩

theorem h44_mentfin {α : Type*} {β : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → β)
    (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) :
    entropy μ f = FiniteEntropy.entropy s (mass μ f) := by
  unfold entropy FiniteEntropy.entropy
  exact tsum_eq_sum (fun b hb => by rw [mass_eq_zero_of_ae μ f s hs hb, Real.negMulLog_zero])

theorem h44_mentcomp {α : Type*} {β : Type*} {γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq γ]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (hf : Measurable f)
    (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) (g : β → γ) :
    entropy μ (g ∘ f) = FiniteEntropy.observableEntropy s (mass μ f) g := by
  have hs' : ∀ᵐ x ∂μ, (g ∘ f) x ∈ s.image g := hs.mono fun x hx => Finset.mem_image_of_mem g hx
  rw [h44_mentfin μ _ _ hs']
  unfold FiniteEntropy.observableEntropy FiniteEntropy.entropy
  apply Finset.sum_congr rfl
  intro c _
  rw [h44_masscomp μ f hf s hs g c]

theorem h44_nml_sum {ι : Type*} (t : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ t, 0 ≤ x i) :
    Real.negMulLog (∑ i ∈ t, x i) ≤ ∑ i ∈ t, Real.negMulLog (x i) := by
  have e : Real.negMulLog (∑ i ∈ t, x i) = ∑ i ∈ t, -x i * Real.log (∑ j ∈ t, x j) := by
    rw [Real.negMulLog, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    simp only [neg_mul]
  rw [e]
  apply Finset.sum_le_sum
  intro i hi
  rcases (hx i hi).eq_or_lt with h | h
  · rw [← h]; simp
  · rw [Real.negMulLog]
    have : Real.log (x i) ≤ Real.log (∑ j ∈ t, x j) :=
      Real.log_le_log h (Finset.single_le_sum hx hi)
    nlinarith

theorem h44_fdp {α : Type*} {γ : Type*} [DecidableEq γ] (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (g : α → γ) :
    FiniteEntropy.observableEntropy s p g ≤ FiniteEntropy.entropy s p := by
  unfold FiniteEntropy.observableEntropy FiniteEntropy.entropy FiniteEntropy.mass
  calc ∑ c ∈ s.image g, Real.negMulLog (∑ a ∈ s.filter (fun a => g a = c), p a)
      ≤ ∑ c ∈ s.image g, ∑ a ∈ s.filter (fun a => g a = c), Real.negMulLog (p a) :=
        Finset.sum_le_sum fun c _ => h44_nml_sum _ _ (fun a ha => hp a (Finset.mem_filter.mp ha).1)
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem g ha) _

theorem h44_mass_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (f : ℝ → ℤ) (j : ℤ) :
    mass ν f j ≤ 1 := by
  unfold mass
  exact measureReal_le_one

theorem h44_grid_ii (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : CompactlyCarried ν)
    {s : ℝ} (hs : 0 < s) (a b : ℝ) : IntervalIntegrable (grid ν s) volume a b := by
  obtain ⟨B, hB0, hB⟩ := hν
  apply MeasureTheory.IntegrableOn.intervalIntegrable
  set lo := min a b
  set hi := max a b
  set J : Finset ℤ := Finset.Icc ⌊-B/s + lo⌋ ⌊B/s + hi⌋ with hJ
  set F : ℝ → ℝ := fun u => ∑ j ∈ J, Real.negMulLog (mass ν (label s u) j) with hF
  have hEq : Set.EqOn F (grid ν s) (Set.Icc lo hi) := by
    intro u hu
    have hae : ∀ᵐ x ∂ν, label s u x ∈ J := (label_ae_finite ν (u := u) hs hB).mono fun x hx => by
      rw [Finset.mem_Icc] at hx ⊢
      exact ⟨le_trans (Int.floor_le_floor (by linarith [hu.1])) hx.1,
        le_trans hx.2 (Int.floor_le_floor (by linarith [hu.2]))⟩
    show F u = entropy ν (label s u)
    rw [h44_mentfin ν _ J hae]
    rfl
  have hm : ∀ j : ℤ, Measurable (fun u => mass ν (label s u) j) := by
    intro j
    have hE : MeasurableSet {p : ℝ × ℝ | ⌊p.2 / s + p.1⌋ = j} :=
      (((measurable_snd.div_const s).add measurable_fst).floor) (measurableSet_singleton j)
    exact (measurable_measure_prodMk_left hE).ennreal_toReal
  have hFm : Measurable F :=
    Finset.measurable_sum _ (fun j _ => Real.continuous_negMulLog.measurable.comp (hm j))
  have hFI : IntegrableOn F (Set.Icc lo hi) volume := by
    refine Measure.integrableOn_of_bounded (M := (J.card : ℝ)) (by simp)
      hFm.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ =>
      Real.negMulLog_nonneg (mass_nonneg _ _ _) (h44_mass_le_one _ _ _))]
    calc F u ≤ ∑ j ∈ J, (1 : ℝ) := Finset.sum_le_sum fun j _ => by
            have := Real.negMulLog_le_one_sub_self (mass_nonneg ν (label s u) j)
            linarith [mass_nonneg ν (label s u) j]
      _ = J.card := by simp
  exact hFI.congr_fun hEq measurableSet_Icc

theorem h44_ment_inj {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℤ)
    (h : ℤ → ℤ) (hinj : Function.Injective h) : entropy μ (h ∘ f) = entropy μ f := by
  unfold entropy
  rw [← hinj.tsum_eq]
  · congr 1
    ext b
    congr 1
    unfold mass
    congr 1
    ext x
    exact hinj.eq_iff
  · intro c hc
    by_contra hr
    apply hc
    show Real.negMulLog (mass μ (h ∘ f) c) = 0
    have : {x | (h ∘ f) x = c} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Function.comp_apply]
      exact fun hx => hr ⟨f x, hx⟩
    unfold mass
    rw [this]
    simp

theorem h44_grid_per (μ : Measure ℝ) (s : ℝ) : Function.Periodic (grid μ s) 1 := by
  intro u
  unfold grid
  have : label s (u + 1) = (fun j => j + 1) ∘ label s u := by
    funext x
    simp only [label, Function.comp_apply]
    rw [← add_assoc, Int.floor_add_one]
  rw [this, h44_ment_inj μ _ _ (fun a b h => by simpa using h)]

theorem h44_grid_map (μ : Measure ℝ) {s : ℝ} (hs : s ≠ 0) (u v : ℝ) :
    entropy (μ.map (fun x => x+v)) (label s u) = grid μ s (u + v/s) := by
  unfold grid entropy
  congr 1
  ext j
  congr 1
  unfold mass
  simp only [Measure.real_def]
  rw [Measure.map_apply (s := {x | label s u x = j}) (by fun_prop)
    (label_measurable s u (measurableSet_singleton j))]
  congr 2
  ext x
  show ⌊(x+v)/s+u⌋ = j ↔ ⌊x/s+(u+v/s)⌋ = j
  rw [show (x+v)/s+u = x/s+(u+v/s) by field_simp; ring]

theorem h44_avg_eq (ν : Measure ℝ) (s : ℝ) :
    averaged ν s = ∫ u in (0:ℝ)..1, grid ν s u := by
  unfold averaged
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]

theorem h44_int_shift (μ : Measure ℝ) (s c : ℝ) :
    ∫ u in (0:ℝ)..1, grid μ s (u + c) = ∫ u in (0:ℝ)..1, grid μ s u := by
  rw [intervalIntegral.integral_comp_add_right]
  have := (h44_grid_per μ s).intervalIntegral_add_eq c 0
  simp only [zero_add] at this
  rw [zero_add, add_comm 1 c]
  exact this

theorem h44_lsum {ι : Type*} (t : Finset ι) (a A : ι → ℝ) (ha : ∀ i ∈ t, 0 ≤ a i)
    (haA : ∀ i ∈ t, a i ≤ A i) :
    (∑ i ∈ t, a i) * Real.log ((∑ i ∈ t, a i) / (∑ i ∈ t, A i)) ≤
      ∑ i ∈ t, a i * Real.log (a i / A i) := by
  have hA0 : ∀ i ∈ t, 0 ≤ A i := fun i hi => (ha i hi).trans (haA i hi)
  set S := ∑ i ∈ t, A i with hS
  rcases (Finset.sum_nonneg hA0).eq_or_lt with h0 | hpos
  · have hz : ∀ i ∈ t, A i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hA0).mp h0.symm
    have hz' : ∀ i ∈ t, a i = 0 := fun i hi => le_antisymm (hz i hi ▸ haA i hi) (ha i hi)
    rw [Finset.sum_eq_zero hz', zero_mul]
    exact le_of_eq (Finset.sum_eq_zero (fun i hi => by rw [hz' i hi, zero_mul])).symm
  · have hJ := Real.convexOn_mul_log.map_sum_le (t := t) (w := fun i => A i / S)
      (p := fun i => a i / A i)
      (fun i hi => div_nonneg (hA0 i hi) hpos.le) (by rw [← Finset.sum_div]; exact div_self hpos.ne')
      (fun i hi => Set.mem_Ici.mpr (div_nonneg (ha i hi) (hA0 i hi)))
    simp only [smul_eq_mul] at hJ
    have e1 : ∑ i ∈ t, A i / S * (a i / A i) = (∑ i ∈ t, a i) / S := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      rcases (hA0 i hi).eq_or_lt with h | h
      · have : a i = 0 := le_antisymm (h ▸ haA i hi) (ha i hi)
        rw [← h, this]; simp
      · field_simp
    have e2 : ∀ i ∈ t, A i / S * (a i / A i * Real.log (a i / A i)) =
        (a i * Real.log (a i / A i)) / S := by
      intro i hi
      rcases (hA0 i hi).eq_or_lt with h | h
      · have : a i = 0 := le_antisymm (h ▸ haA i hi) (ha i hi)
        rw [← h, this]; simp
      · field_simp
    rw [e1, Finset.sum_congr rfl e2, ← Finset.sum_div] at hJ
    have := mul_le_mul_of_nonneg_left hJ hpos.le
    rwa [mul_div_cancel₀ _ hpos.ne', ← mul_assoc, mul_div_cancel₀ _ hpos.ne'] at this

theorem h44_Dform (J : Finset ℤ) (h : ℤ → ℤ) (p : ℤ → ℝ) (hp : ∀ j ∈ J, 0 ≤ p j) :
    FiniteEntropy.entropy J p - FiniteEntropy.observableEntropy J p h =
      -∑ c ∈ J.image h, ∑ j ∈ J.filter (fun j => h j = c),
        p j * Real.log (p j / FiniteEntropy.mass J p h c) := by
  unfold FiniteEntropy.observableEntropy
  unfold FiniteEntropy.entropy
  rw [← Finset.sum_fiberwise_of_maps_to (g := h) (t := J.image h)
    (fun j hj => Finset.mem_image_of_mem h hj) (fun j => Real.negMulLog (p j))]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c _
  have hM : FiniteEntropy.mass J p h c = ∑ j ∈ J.filter (fun j => h j = c), p j := rfl
  have e : Real.negMulLog (FiniteEntropy.mass J p h c) =
      ∑ j ∈ J.filter (fun j => h j = c), -(p j) * Real.log (FiniteEntropy.mass J p h c) := by
    rw [hM, Real.negMulLog, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [e, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hpj := hp j (Finset.mem_filter.mp hj).1
  rcases hpj.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · have hMpos : 0 < FiniteEntropy.mass J p h c := by
      rw [hM]
      exact lt_of_lt_of_le hpos (Finset.single_le_sum
        (fun k hk => hp k (Finset.mem_filter.mp hk).1) hj)
    rw [Real.negMulLog, Real.log_div hpos.ne' hMpos.ne']
    ring

theorem h44_conc {ι : Type*} [Fintype ι] (J : Finset ℤ) (h : ℤ → ℤ) (p : ι → ℤ → ℝ)
    (hp : ∀ i, ∀ j ∈ J, 0 ≤ p i j) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∑ c ∈ J.image h, ∑ j ∈ J.filter (fun j => h j = c),
        (∑ i, w i * p i j) * Real.log ((∑ i, w i * p i j) /
          FiniteEntropy.mass J (fun k => ∑ i, w i * p i k) h c) ≤
      ∑ i, w i * ∑ c ∈ J.image h, ∑ j ∈ J.filter (fun j => h j = c),
        p i j * Real.log (p i j / FiniteEntropy.mass J (p i) h c) := by
  have hmass : ∀ c, FiniteEntropy.mass J (fun k => ∑ i, w i * p i k) h c =
      ∑ i, w i * FiniteEntropy.mass J (p i) h c := by
    intro c
    unfold FiniteEntropy.mass
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  calc _ ≤ ∑ c ∈ J.image h, ∑ j ∈ J.filter (fun j => h j = c),
        ∑ i, w i * (p i j * Real.log (p i j / FiniteEntropy.mass J (p i) h c)) := by
        apply Finset.sum_le_sum
        intro c _
        apply Finset.sum_le_sum
        intro j hj
        rw [hmass c]
        have hJj := (Finset.mem_filter.mp hj).1
        have hl := h44_lsum Finset.univ (fun i => w i * p i j)
          (fun i => w i * FiniteEntropy.mass J (p i) h c)
          (fun i _ => mul_nonneg (hw i) (hp i j hJj))
          (fun i _ => mul_le_mul_of_nonneg_left (Finset.single_le_sum
            (fun k hk => hp i k (Finset.mem_filter.mp hk).1) hj) (hw i))
        refine hl.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
        rcases (hw i).eq_or_lt with h0 | hpos
        · rw [← h0]; simp
        · rw [mul_div_mul_left _ _ hpos.ne']
          ring
    _ = _ := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_congr rfl (fun c _ => Finset.sum_comm), Finset.sum_comm]
theorem h44_int_scale (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    ∫ u in (0:ℝ)..1, grid μ s ((N:ℝ)*u) = ∫ u in (0:ℝ)..1, grid μ s u := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  rw [intervalIntegral.integral_comp_mul_left (grid μ s) hN'.ne']
  have := (h44_grid_per μ s).intervalIntegral_add_zsmul_eq (N : ℤ) 0 (h44_grid_ii μ hμ hs)
  simp only [zero_add, zsmul_eq_mul, Int.cast_natCast, mul_one] at this
  rw [mul_zero, mul_one, this, smul_eq_mul]
  field_simp

theorem h44_mass_mix {ι : Type*} [Fintype ι] (μ : Measure ℝ) (ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : μ = ∑ i, ENNReal.ofReal (w i) • ν i) (f : ℝ → ℤ) (j : ℤ) :
    mass μ f j = ∑ i, w i * mass (ν i) f j := by
  rw [hm]
  unfold mass
  simp only [Measure.real_def, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw i)]

theorem h44_ptconc {ι : Type*} [Fintype ι] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : μ = ∑ i, ENNReal.ofReal (w i) • ν i) {B : ℝ} (hB : μ (Set.Icc (-B) B)ᶜ = 0)
    (hBi : ∀ i, ν i (Set.Icc (-B) B)ᶜ = 0) {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) (u : ℝ) :
    ∑ i, w i * (grid (ν i) s ((N : ℝ)*u) - grid (ν i) ((N : ℝ)*s) u) ≤
      grid μ s ((N : ℝ)*u) - grid μ ((N : ℝ)*s) u := by
  classical
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  set fine := label s ((N : ℝ)*u) with hfine
  set h : ℤ → ℤ := fun j => j / (N:ℤ) with hh
  have hcf : label ((N:ℝ)*s) u = h ∘ fine := by
    funext x
    simp only [hh, hfine, label, Function.comp_apply]
    rw [← Int.floor_div_natCast]
    congr 1
    field_simp
  set J := Finset.Icc ⌊-B/s + (N:ℝ)*u⌋ ⌊B/s + (N:ℝ)*u⌋ with hJ
  have hfm : Measurable fine := label_measurable _ _
  have hD : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ], ρ (Set.Icc (-B) B)ᶜ = 0 →
      grid ρ s ((N : ℝ)*u) - grid ρ ((N : ℝ)*s) u =
        -∑ c ∈ J.image h, ∑ j ∈ J.filter (fun j => h j = c),
          mass ρ fine j * Real.log (mass ρ fine j / FiniteEntropy.mass J (mass ρ fine) h c) := by
    intro ρ _ hρ
    have hJa : ∀ᵐ x ∂ρ, fine x ∈ J := label_ae_finite ρ hs hρ
    unfold grid
    rw [hcf, h44_mentcomp ρ fine hfm J hJa, ← hfine, h44_mentfin ρ fine J hJa]
    exact h44_Dform J h _ (fun j _ => mass_nonneg ρ fine j)
  rw [hD μ hB, Finset.sum_congr rfl (fun i _ => by rw [hD (ν i) (hBi i)])]
  have hq : mass μ fine = fun k => ∑ i, w i * mass (ν i) fine k :=
    funext fun k => h44_mass_mix μ ν w hw hm fine k
  rw [hq]
  have hc := h44_conc J h (fun i => mass (ν i) fine) (fun i j _ => mass_nonneg _ _ _) w hw
  simp only [mul_neg, Finset.sum_neg_distrib]
  linarith

theorem h44_Dint (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : CompactlyCarried ν)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    IntervalIntegrable (fun u => grid ν s ((N:ℝ)*u) - grid ν ((N:ℝ)*s) u) volume 0 1 ∧
    averaged ν s - averaged ν ((N:ℝ)*s) =
      ∫ u in (0:ℝ)..1, (grid ν s ((N:ℝ)*u) - grid ν ((N:ℝ)*s) u) := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hNs : 0 < (N:ℝ)*s := mul_pos hN' hs
  have hA : IntervalIntegrable (fun u => grid ν s ((N:ℝ)*u)) volume 0 1 := by
    have := (h44_grid_ii ν hν hs 0 N).comp_mul_left (c := (N:ℝ))
    rwa [zero_div, div_self hN'.ne'] at this
  have hB := h44_grid_ii ν hν hNs 0 1
  refine ⟨hA.sub hB, ?_⟩
  rw [intervalIntegral.integral_sub hA hB, h44_avg_eq, h44_avg_eq, h44_int_scale ν hν hs hN]

theorem solution {ι : Type uι} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, CompactlyCarried (ν i)) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : μ = ∑ i, ENNReal.ofReal (w i) • ν i)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    (∑ i, w i*(averaged (ν i) s-averaged (ν i) ((N : ℝ)*s))) ≤
      averaged μ s-averaged μ ((N : ℝ)*s) := by
  obtain ⟨B0, hB00, hB0⟩ := hμ
  choose Bi hBi0 hBi using hν
  set B := B0 + ∑ i, Bi i with hBdef
  have hsum : 0 ≤ ∑ i, Bi i := Finset.sum_nonneg fun i _ => hBi0 i
  have hB : μ (Set.Icc (-B) B)ᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.mpr (Set.Icc_subset_Icc (by linarith) (by linarith))) hB0
  have hBB : ∀ i, ν i (Set.Icc (-B) B)ᶜ = 0 := by
    intro i
    have hle : Bi i ≤ ∑ j, Bi j := Finset.single_le_sum (fun j _ => hBi0 j) (Finset.mem_univ i)
    exact measure_mono_null (Set.compl_subset_compl.mpr
      (Set.Icc_subset_Icc (by linarith) (by linarith))) (hBi i)
  have hμc : CompactlyCarried μ := ⟨B0, hB00, hB0⟩
  have hνc : ∀ i, CompactlyCarried (ν i) := fun i => ⟨Bi i, hBi0 i, hBi i⟩
  haveI : IsProbabilityMeasure μ := ‹_›
  rw [(h44_Dint μ hμc hs hN).2,
    Finset.sum_congr rfl (fun i _ => by rw [(h44_Dint (ν i) (hνc i) hs hN).2])]
  have hint : ∀ i ∈ (Finset.univ : Finset ι), IntervalIntegrable
      (fun u => w i * (grid (ν i) s ((N:ℝ)*u) - grid (ν i) ((N:ℝ)*s) u)) volume 0 1 :=
    fun i _ => (h44_Dint (ν i) (hνc i) hs hN).1.const_mul (w i)
  have e : ∑ i, w i * ∫ u in (0:ℝ)..1, (grid (ν i) s ((N:ℝ)*u) - grid (ν i) ((N:ℝ)*s) u) =
      ∫ u in (0:ℝ)..1, ∑ i, w i * (grid (ν i) s ((N:ℝ)*u) - grid (ν i) ((N:ℝ)*s) u) := by
    rw [intervalIntegral.integral_finset_sum hint]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_const_mul]
  rw [e]
  have hsI : IntervalIntegrable
      (fun u => ∑ i, w i * (grid (ν i) s ((N:ℝ)*u) - grid (ν i) ((N:ℝ)*s) u)) volume 0 1 := by
    have := IntervalIntegrable.sum Finset.univ hint
    rw [Finset.sum_fn] at this
    exact this
  exact intervalIntegral.integral_mono_on zero_le_one hsI (h44_Dint μ hμc hs hN).1
    (fun u _ => h44_ptconc μ ν w hw hm hB hBB hs hN u)

