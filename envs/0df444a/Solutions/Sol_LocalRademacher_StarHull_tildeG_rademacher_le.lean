-- Prove2me | solution 1 for LocalRademacher.StarHull.tildeG_rademacher_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:32:07.830686+00:00
-- url     : https://prove2.me/submissions/de9b32e9-c5d3-4a87-b3b7-3bb3c30f1a06

import Mathlib
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_LocalRademacher_StarHull_Classes

set_option autoImplicit false

open MeasureTheory ProbabilityTheory VarianceRegularization.Localized

namespace BB227DF6

lemma sum_bound {n : ℕ} (σ : Fin n → Bool) (v : Fin n → ℝ) (M : ℝ)
    (hv : ∀ i, |v i| ≤ M) :
    |∑ i, UnderstandingML.signVec σ i * v i| ≤ n * M := by
  calc |∑ i, UnderstandingML.signVec σ i * v i|
      ≤ ∑ i, |UnderstandingML.signVec σ i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, M := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        have h1 : |UnderstandingML.signVec σ i| = 1 := by
          unfold UnderstandingML.signVec; split_ifs <;> simp
        rw [h1, one_mul]; exact hv i
    _ = n * M := by simp

lemma iSup_abs_bound {ι : Sort*} (f : ι → ℝ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ i, |f i| ≤ C) :
    |⨆ i, f i| ≤ C := by
  rw [abs_le]
  constructor
  · rcases isEmpty_or_nonempty ι with hι | hι
    · rw [Real.iSup_of_isEmpty]; linarith
    · obtain ⟨i⟩ := hι
      have hb : BddAbove (Set.range f) := ⟨C, by
        rintro _ ⟨j, rfl⟩; exact (abs_le.mp (hf j)).2⟩
      exact le_ciSup_of_le hb i (abs_le.mp (hf i)).1
  · exact Real.iSup_le (fun i => (abs_le.mp (hf i)).2) hC

lemma iSup_subset_mono {n : ℕ} (A A' : Set (Fin n → ℝ)) (hAA : A ⊆ A') (hA : A.Nonempty)
    (φ : (Fin n → ℝ) → ℝ) (hb : BddAbove (Set.range fun a : A' => φ a)) :
    (⨆ a : A, φ a) ≤ ⨆ a : A', φ a := by
  have : Nonempty A := hA.to_subtype
  apply ciSup_le
  intro a
  exact le_ciSup_of_le hb ⟨a.1, hAA a.2⟩ le_rfl

lemma iSup_evalSet {X : Type*} {n : ℕ} (G : Set (X → ℝ)) (s : Fin n → X)
    (φ : (Fin n → ℝ) → ℝ) :
    (⨆ a : UnderstandingML.evalSet G s, φ a) = ⨆ g : G, φ (fun i => (g : X → ℝ) (s i)) := by
  show sSup (Set.range _) = sSup (Set.range _)
  congr 1
  ext y
  constructor
  · rintro ⟨⟨v, f, hf, rfl⟩, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩
  · rintro ⟨⟨f, hf⟩, rfl⟩
    exact ⟨⟨_, f, hf, rfl⟩, rfl⟩

end BB227DF6

open MeasureTheory ProbabilityTheory VarianceRegularization.Localized LocalRademacher.StarHull in
theorem solution {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n) (F : Set (X → ℝ)) (hFc : F.Countable)
    (hmeas : ∀ f ∈ F, Measurable f) (a b : ℝ) (hrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc a b)
    (T : (X → ℝ) → ℝ) (B : ℝ) (hB : 0 < B) (hT0 : ∀ f ∈ F, 0 ≤ T f)
    (hTsq : ∀ f ∈ F, ∀ α ∈ Set.Icc (0 : ℝ) 1, T (fun x => α * f x) ≤ α ^ 2 * T f)
    (ψ : ℝ → ℝ) (r : ℝ) (hr : 0 < r)
    (hint : Integrable (fun s : Fin n → X => empRademacher (localClass F T r) s)
      (Measure.pi fun _ : Fin n => P))
    (hloc : B * expRademacher P n (localClass F T r) ≤ ψ r) :
    Integrable (fun s : Fin n → X => empRademacher (tildeG F T r) s)
        (Measure.pi fun _ : Fin n => P) ∧
      expRademacher P n (tildeG F T r) ≤ ψ r / B := by
  set M : ℝ := |a| + |b| with hM
  have hM0 : 0 ≤ M := by positivity
  have hfM : ∀ f ∈ F, ∀ x, |f x| ≤ M := by
    intro f hf x
    have h := hrange f hf x
    rw [abs_le]
    constructor
    · have := neg_abs_le a; have := abs_nonneg b; linarith [h.1]
    · have := le_abs_self b; have := abs_nonneg a; linarith [h.2]
  -- coefficient facts
  have hc : ∀ f ∈ F, r / max (T f) r ∈ Set.Icc (0 : ℝ) 1 := by
    intro f _
    have hpos : 0 < max (T f) r := lt_of_lt_of_le hr (le_max_right _ _)
    refine ⟨div_nonneg hr.le hpos.le, ?_⟩
    rw [div_le_one hpos]; exact le_max_right _ _
  -- tildeG ⊆ localClass
  have hsub : tildeG F T r ⊆ localClass F T r := by
    rintro g ⟨f, hf, rfl⟩
    refine ⟨⟨f, hf, r / max (T f) r, hc f hf, ?_⟩, ?_⟩
    · funext x; simp
    · have h1 := hTsq f hf _ (hc f hf)
      refine le_trans h1 ?_
      have hT := hT0 f hf
      rcases le_total (T f) r with h | h
      · rw [max_eq_right h, div_self hr.ne']; simpa using h
      · rw [max_eq_left h]
        have hTpos : 0 < T f := lt_of_lt_of_le hr h
        rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg (mul_nonneg hr.le hT) (sub_nonneg.mpr h)]
  -- bounds on localClass members
  have hlocM : ∀ g ∈ localClass F T r, ∀ x, |g x| ≤ M := by
    rintro g ⟨⟨f, hf, α, hα, rfl⟩, -⟩ x
    simp only [Pi.zero_apply, sub_zero, zero_add]
    rw [abs_mul, abs_of_nonneg hα.1]
    calc α * |f x| ≤ 1 * M := mul_le_mul hα.2 (hfM f hf x) (abs_nonneg _) zero_le_one
      _ = M := one_mul M
  have htilM : ∀ g ∈ tildeG F T r, ∀ x, |g x| ≤ M := fun g hg => hlocM g (hsub hg)
  -- empRademacher bounded for tildeG
  have hbound : ∀ s : Fin n → X, |empRademacher (tildeG F T r) s| ≤ n * M := by
    intro s
    unfold empRademacher UnderstandingML.rademacher
    have hsup : ∀ σ : Fin n → Bool,
        |⨆ v : UnderstandingML.evalSet (tildeG F T r) s,
          ∑ i, UnderstandingML.signVec σ i * (v : Fin n → ℝ) i| ≤ n * M := by
      intro σ
      apply BB227DF6.iSup_abs_bound _ _ (by positivity)
      rintro ⟨v, g, hg, rfl⟩
      exact BB227DF6.sum_bound σ _ M (fun i => htilM g hg (s i))
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / n),
      abs_of_pos (by positivity : (0:ℝ) < 1 / 2 ^ n)]
    calc 1 / (n:ℝ) * (1 / 2 ^ n * |∑ σ : Fin n → Bool,
            ⨆ v : UnderstandingML.evalSet (tildeG F T r) s,
              ∑ i, UnderstandingML.signVec σ i * (v : Fin n → ℝ) i|)
        ≤ 1 / (n:ℝ) * (1 / 2 ^ n * ∑ _σ : Fin n → Bool, (n * M)) := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ _ => hsup σ)
      _ ≤ n * M := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin, nsmul_eq_mul]
          have h2 : (0:ℝ) < 2 ^ n := by positivity
          have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
          field_simp
          push_cast
          nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (mul_nonneg h2.le hM0)]
  -- measurability
  have hGc : (tildeG F T r).Countable := by
    refine (hFc.image (fun f => fun x => (r / max (T f) r) * f x)).mono ?_
    rintro g ⟨f, hf, rfl⟩
    exact ⟨f, hf, rfl⟩
  have hmeasG : Measurable (fun s : Fin n → X => empRademacher (tildeG F T r) s) := by
    unfold empRademacher UnderstandingML.rademacher
    apply Measurable.const_mul
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro σ _
    have key : (fun s : Fin n → X => ⨆ v : UnderstandingML.evalSet (tildeG F T r) s,
          ∑ i, UnderstandingML.signVec σ i * (v : Fin n → ℝ) i) =
        fun s => ⨆ g : tildeG F T r,
          ∑ i, UnderstandingML.signVec σ i * (g : X → ℝ) (s i) :=
      funext fun s => BB227DF6.iSup_evalSet _ s (fun v => ∑ i, UnderstandingML.signVec σ i * v i)
    have : Countable (tildeG F T r) := hGc.to_subtype
    have hm : Measurable (fun s : Fin n → X => ⨆ g : tildeG F T r,
          ∑ i, UnderstandingML.signVec σ i * (g : X → ℝ) (s i)) := by
      apply Measurable.iSup
      rintro ⟨g, f, hf, rfl⟩
      apply Finset.measurable_sum
      intro i _
      exact measurable_const.mul
        (((hmeas f hf).const_mul _).comp (measurable_pi_apply i))
    rw [← key] at hm
    exact hm
  have hintG : Integrable (fun s : Fin n → X => empRademacher (tildeG F T r) s)
      (Measure.pi fun _ : Fin n => P) := by
    refine Integrable.mono' (integrable_const ((n:ℝ) * M)) hmeasG.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun s => by
      rw [Real.norm_eq_abs]; exact hbound s)
  refine ⟨hintG, ?_⟩
  -- pointwise monotonicity
  have hpt : ∀ s : Fin n → X,
      empRademacher (tildeG F T r) s ≤ empRademacher (localClass F T r) s := by
    intro s
    rcases (tildeG F T r).eq_empty_or_nonempty with hE | hNE
    · -- F is empty
      have hF : F = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro f hf
        have : (fun x => (r / max (T f) r) * f x) ∈ tildeG F T r := ⟨f, hf, rfl⟩
        rw [hE] at this; exact this
      have hL : localClass F T r = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro g ⟨⟨f, hf, -⟩, -⟩
        rw [hF] at hf; exact hf
      rw [hE, hL]
    · unfold empRademacher UnderstandingML.rademacher
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      gcongr with σ _
      refine BB227DF6.iSup_subset_mono _ _ ?_ ?_ (fun v => ∑ i, UnderstandingML.signVec σ i * v i) ?_
      · rintro v ⟨g, hg, rfl⟩; exact ⟨g, hsub hg, rfl⟩
      · obtain ⟨g, hg⟩ := hNE; exact ⟨_, g, hg, rfl⟩
      · refine ⟨n * M, ?_⟩
        rintro _ ⟨⟨v, g, hg, rfl⟩, rfl⟩
        exact (abs_le.mp (BB227DF6.sum_bound σ _ M (fun i => hlocM g hg (s i)))).2
  have hmono : expRademacher P n (tildeG F T r) ≤ expRademacher P n (localClass F T r) :=
    integral_mono hintG hint hpt
  rw [le_div_iff₀ hB]
  nlinarith
