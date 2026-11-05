-- Prove2me | solution 1 for InfoRelax.IdealPenalty.eq_10_dual_recursion
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T23:18:44.609684+00:00
-- url     : https://prove2.me/submissions/55a7f6e6-d522-4866-8d31-e34634636ee3

import Mathlib
import Definitions.Def_InfoRelax_IdealPenalty_Framework
import Definitions.Def_InfoRelax_IdealPenalty_RecursiveModel
import Definitions.Def_InfoRelax_IdealPenalty_Penalty

set_option autoImplicit false
open MeasureTheory InfoRelax.IdealPenalty



namespace IPAux

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace ι] [Countable ι]
  [MeasurableSingletonClass ι]

/-- integrability of a countable substitution of uniformly bounded measurable functions -/
lemma integrable_subst (μ : Measure Ω) [IsFiniteMeasure μ] (g : ι → Ω → ℝ)
    (hg : ∀ b, Measurable (g b)) (K : ℝ) (hK : ∀ b, ∀ᵐ ω ∂μ, |g b ω| ≤ K)
    (β : Ω → ι) (hβ : Measurable β) :
    Integrable (fun ω => g (β ω) ω) μ := by
  have hm : Measurable (fun p : Ω × ι => g p.2 p.1) :=
    measurable_from_prod_countable_left (fun b => hg b)
  have hm2 : Measurable (fun ω => g (β ω) ω) :=
    hm.comp (measurable_id.prodMk hβ)
  refine Integrable.of_bound hm2.aestronglyMeasurable K ?_
  have : ∀ᵐ ω ∂μ, ∀ b, |g b ω| ≤ K := ae_all_iff.2 hK
  filter_upwards [this] with ω hω
  simpa [Real.norm_eq_abs] using hω (β ω)

lemma measurable_subst (g : ι → Ω → ℝ)
    (hg : ∀ b, Measurable (g b)) (β : Ω → ι) (hβ : Measurable β) :
    Measurable (fun ω => g (β ω) ω) :=
  (measurable_from_prod_countable_left (f := fun p : Ω × ι => g p.2 p.1)
    (fun b => hg b)).comp (measurable_id.prodMk hβ)

/-- splitting the integral of a substitution along the fibres of `β`. -/
lemma setIntegral_subst (μ : Measure Ω) (g : ι → Ω → ℝ)
    (β : Ω → ι) (hβ : Measurable β) (s : Set Ω) (hs : MeasurableSet s)
    (hint : IntegrableOn (fun ω => g (β ω) ω) s μ) :
    ∫ ω in s, g (β ω) ω ∂μ = ∑' b, ∫ ω in s ∩ β ⁻¹' {b}, g b ω ∂μ := by
  have hU : (⋃ b, s ∩ β ⁻¹' {b}) = s := by
    ext ω; simp
  have hmeas : ∀ b, MeasurableSet (s ∩ β ⁻¹' {b}) :=
    fun b => hs.inter (hβ (measurableSet_singleton b))
  have hdisj : Pairwise (Function.onFun Disjoint fun b => s ∩ β ⁻¹' {b}) := by
    intro b b' hbb'
    refine Set.disjoint_left.2 ?_
    intro ω h1 h2
    exact hbb' (h1.2.symm.trans h2.2)
  have hint' : IntegrableOn (fun ω => g (β ω) ω) (⋃ b, s ∩ β ⁻¹' {b}) μ := by
    rw [hU]; exact hint
  have := integral_iUnion hmeas hdisj hint'
  rw [hU] at this
  rw [this]
  congr 1
  funext b
  refine setIntegral_congr_fun (hmeas b) ?_
  intro ω hω
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at hω
  simp [hω.2]

/-- The key substitution lemma: integrating a conditional expectation along an
`m`-measurable countable-valued selection. -/
lemma setIntegral_condExp_subst (μ : Measure Ω) [IsFiniteMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) (g : ι → Ω → ℝ) (hgi : ∀ b, Integrable (g b) μ)
    (K : ℝ) (hK : ∀ b, ∀ᵐ ω ∂μ, |g b ω| ≤ K)
    (β : Ω → ι) (hβ : Measurable[m] β) (s : Set Ω) (hs : MeasurableSet[m] s) :
    ∫ ω in s, (μ[g (β ω) | m]) ω ∂μ = ∑' b, ∫ ω in s ∩ β ⁻¹' {b}, g b ω ∂μ := by
  have hβ' : Measurable[mΩ] β := hβ.mono hm le_rfl
  have hint : Integrable (fun ω => (μ[g (β ω) | m]) ω) μ := by
    refine integrable_subst (mΩ := mΩ) μ (fun b => μ[g b | m])
      (fun b => (stronglyMeasurable_condExp.mono hm).measurable) K ?_ β hβ'
    intro b
    exact ae_bdd_abs_condExp_of_ae_bdd_abs (hK b)
  rw [setIntegral_subst (mΩ := mΩ) μ (fun b => μ[g b | m]) β hβ' s (hm s hs) hint.integrableOn]
  congr 1
  funext b
  exact setIntegral_condExp hm (hgi b) (hs.inter (hβ (measurableSet_singleton b)))

lemma setIntegral_condExp_subst' (μ : Measure Ω) [IsFiniteMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) (g : ι → Ω → ℝ) (hgm : ∀ b, Measurable[mΩ] (g b))
    (K : ℝ) (hK : ∀ b, ∀ᵐ ω ∂μ, |g b ω| ≤ K)
    (β : Ω → ι) (hβ : Measurable[m] β) (s : Set Ω) (hs : MeasurableSet[m] s) :
    ∫ ω in s, (μ[g (β ω) | m]) ω ∂μ = ∫ ω in s, g (β ω) ω ∂μ := by
  have hβ' : Measurable[mΩ] β := hβ.mono hm le_rfl
  have hgi : ∀ b, Integrable (g b) μ := fun b =>
    Integrable.of_bound (hgm b).aestronglyMeasurable K
      (by filter_upwards [hK b] with ω h; simpa [Real.norm_eq_abs] using h)
  rw [setIntegral_condExp_subst (mΩ := mΩ) μ hm g hgi K hK β hβ s hs,
    setIntegral_subst (mΩ := mΩ) μ g β hβ' s (hm s hs) (integrable_subst (mΩ := mΩ) μ g hgm K hK β hβ').integrableOn]

end IPAux



namespace IPAux

variable {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
  [DiscreteMeasurableSpace X] [Countable X] [DecidableEq X] {T : ℕ}

lemma bellman_fin (μ : Measure Ω) (𝔾 : Filtration (Fin (T + 1)) mΩ)
    (Afeas : Fin (T + 1) → (Fin (T + 1) → X) → Set X)
    (f : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ) (t : Fin (T + 1)) (a : Fin (T + 1) → X) :
    bellman μ 𝔾 Afeas f (t : ℕ) a = fun ω => ⨆ x : Afeas t a,
        f t (Function.update a t x.1) ω +
          μ[bellman μ 𝔾 Afeas f ((t : ℕ) + 1) (Function.update a t x.1) | 𝔾 t] ω := by
  rw [bellman, dif_pos (Nat.lt_succ_iff.mp t.isLt)]

lemma bellman_gt (μ : Measure Ω) (𝔾 : Filtration (Fin (T + 1)) mΩ)
    (Afeas : Fin (T + 1) → (Fin (T + 1) → X) → Set X)
    (f : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ) (t : ℕ) (ht : T < t)
    (a : Fin (T + 1) → X) :
    bellman μ 𝔾 Afeas f t a = 0 := by
  rw [bellman, dif_neg (by omega)]

section
variable (μ : Measure Ω) (𝔾 : Filtration (Fin (T + 1)) mΩ)
    (Afeas : Fin (T + 1) → (Fin (T + 1) → X) → Set X)
    (f : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ)

/-- dependence only on the past actions -/
lemma bellman_dep
    (hA : ∀ t a a', (∀ s, s < t → a s = a' s) → Afeas t a = Afeas t a')
    (hf : ∀ t a a', (∀ s, s ≤ t → a s = a' s) → f t a = f t a') :
    ∀ k t, T + 1 - t = k → ∀ a a' : Fin (T + 1) → X,
      (∀ s : Fin (T + 1), (s : ℕ) < t → a s = a' s) →
        bellman μ 𝔾 Afeas f t a = bellman μ 𝔾 Afeas f t a' := by
  intro k
  induction k with
  | zero =>
    intro t ht a a' _
    rw [bellman_gt μ 𝔾 Afeas f t (by omega), bellman_gt μ 𝔾 Afeas f t (by omega)]
  | succ k ih =>
    intro t ht a a' haa
    have htT : t < T + 1 := by omega
    have e := bellman_fin μ 𝔾 Afeas f ⟨t, htT⟩
    simp only at e
    rw [e a, e a']
    have hAe : Afeas ⟨t, htT⟩ a = Afeas ⟨t, htT⟩ a' :=
      hA _ a a' (fun s hs => haa s (by simpa [Fin.lt_def] using hs))
    have hup : ∀ x : X, ∀ s, s ≤ (⟨t, htT⟩ : Fin (T + 1)) →
        Function.update a ⟨t, htT⟩ x s = Function.update a' ⟨t, htT⟩ x s := by
      intro x s hs
      by_cases hst : s = ⟨t, htT⟩
      · subst hst; simp
      · rw [Function.update_of_ne hst, Function.update_of_ne hst]
        apply haa
        have : s ≠ ⟨t, htT⟩ := hst
        have h1 : (s : ℕ) ≤ t := by simpa [Fin.le_def] using hs
        have h2 : (s : ℕ) ≠ t := fun h => hst (Fin.ext h)
        omega
    have hf' : ∀ x : X, f ⟨t, htT⟩ (Function.update a ⟨t, htT⟩ x) =
        f ⟨t, htT⟩ (Function.update a' ⟨t, htT⟩ x) := fun x => hf _ _ _ (hup x)
    have hV : ∀ x : X, bellman μ 𝔾 Afeas f (t + 1) (Function.update a ⟨t, htT⟩ x) =
        bellman μ 𝔾 Afeas f (t + 1) (Function.update a' ⟨t, htT⟩ x) := by
      intro x
      apply ih (t + 1) (by omega)
      intro s hs
      exact hup x s (by rw [Fin.le_def]; simp; omega)
    funext ω
    simp_rw [hf', hV]
    rw [hAe]

end

section
variable (μ : Measure Ω) (𝔾 : Filtration (Fin (T + 1)) mΩ)
    (Afeas : Fin (T + 1) → (Fin (T + 1) → X) → Set X)
    (f : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ)

lemma bellman_meas_fin (hfm : ∀ t a, Measurable[𝔾 t] (f t a)) (t : Fin (T + 1))
    (a : Fin (T + 1) → X) : Measurable[𝔾 t] (bellman μ 𝔾 Afeas f (t : ℕ) a) := by
  rw [bellman_fin]
  exact Measurable.iSup (fun x => (hfm _ _).add stronglyMeasurable_condExp.measurable)

lemma bellman_meas (hfm : ∀ t a, Measurable[𝔾 t] (f t a)) (t : ℕ)
    (a : Fin (T + 1) → X) : Measurable (bellman μ 𝔾 Afeas f t a) := by
  by_cases ht : t ≤ T
  · have := bellman_meas_fin μ 𝔾 Afeas f hfm ⟨t, by omega⟩ a
    exact this.mono (𝔾.le _) le_rfl
  · rw [bellman_gt μ 𝔾 Afeas f t (by omega)]
    exact measurable_const

lemma bellman_bound (hne : ∀ t a, (Afeas t a).Nonempty) (C : ℝ) (hC : 0 ≤ C)
    (hfb : ∀ t a, ∀ᵐ ω ∂μ, |f t a ω| ≤ C) :
    ∀ k t, T + 1 ≤ t + k → ∀ a, ∀ᵐ ω ∂μ, |bellman μ 𝔾 Afeas f t a ω| ≤ k * C := by
  intro k
  induction k with
  | zero =>
    intro t ht a
    rw [bellman_gt μ 𝔾 Afeas f t (by omega)]
    simp
  | succ k ih =>
    intro t ht a
    by_cases htT : T < t
    · rw [bellman_gt μ 𝔾 Afeas f t htT]
      filter_upwards with ω
      simp only [Pi.zero_apply, abs_zero]
      positivity
    have htT' : t < T + 1 := by omega
    have e := bellman_fin μ 𝔾 Afeas f ⟨t, htT'⟩ a
    simp only at e
    rw [e]
    have h1 : ∀ b, ∀ᵐ ω ∂μ,
        |(μ[bellman μ 𝔾 Afeas f (t + 1) b | 𝔾 ⟨t, htT'⟩]) ω| ≤ k * C := fun b =>
      ae_bdd_abs_condExp_of_ae_bdd_abs (ih (t + 1) (by omega) b)
    have h2 := ae_all_iff.2 h1
    have h3 := ae_all_iff.2 (fun x : X => hfb ⟨t, htT'⟩ (Function.update a ⟨t, htT'⟩ x))
    filter_upwards [h2, h3] with ω hω hfω
    have hg : ∀ x : X, |f ⟨t, htT'⟩ (Function.update a ⟨t, htT'⟩ x) ω +
        (μ[bellman μ 𝔾 Afeas f (t + 1) (Function.update a ⟨t, htT'⟩ x) | 𝔾 ⟨t, htT'⟩]) ω|
          ≤ C + k * C := fun x =>
      (abs_add_le _ _).trans (add_le_add (hfω x) (hω _))
    haveI : Nonempty (Afeas ⟨t, htT'⟩ a) := (hne _ a).to_subtype
    have hbdd : BddAbove (Set.range fun x : Afeas ⟨t, htT'⟩ a =>
        f ⟨t, htT'⟩ (Function.update a ⟨t, htT'⟩ x.1) ω +
        (μ[bellman μ 𝔾 Afeas f (t + 1) (Function.update a ⟨t, htT'⟩ x.1) | 𝔾 ⟨t, htT'⟩]) ω) := by
      refine ⟨C + k * C, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact (abs_le.1 (hg x.1)).2
    rw [abs_le]
    obtain ⟨x0⟩ := (inferInstance : Nonempty (Afeas ⟨t, htT'⟩ a))
    push_cast
    constructor
    · refine le_ciSup_of_le hbdd x0 ?_
      have := (abs_le.1 (hg x0.1)).1
      linarith
    · refine ciSup_le fun x => ?_
      have := (abs_le.1 (hg x.1)).2
      linarith

lemma bellman_ge (hne : ∀ t a, (Afeas t a).Nonempty) (C : ℝ) (hC : 0 ≤ C)
    (hfb : ∀ t a, ∀ᵐ ω ∂μ, |f t a ω| ≤ C) (t : Fin (T + 1)) (a : Fin (T + 1) → X) :
    ∀ᵐ ω ∂μ, ∀ x ∈ Afeas t a, f t (Function.update a t x) ω +
      (μ[bellman μ 𝔾 Afeas f ((t : ℕ) + 1) (Function.update a t x) | 𝔾 t]) ω ≤
        bellman μ 𝔾 Afeas f t a ω := by
  have h1 : ∀ b, ∀ᵐ ω ∂μ,
      |(μ[bellman μ 𝔾 Afeas f ((t : ℕ) + 1) b | 𝔾 t]) ω| ≤ (T + 1 : ℕ) * C := fun b =>
    ae_bdd_abs_condExp_of_ae_bdd_abs (bellman_bound μ 𝔾 Afeas f hne C hC hfb (T + 1) _
      (by omega) b)
  have h3 := ae_all_iff.2 (fun x : X => hfb t (Function.update a t x))
  filter_upwards [ae_all_iff.2 h1, h3] with ω hω hfω
  intro x hx
  rw [bellman_fin]
  have hbdd : BddAbove (Set.range fun x : Afeas t a =>
      f t (Function.update a t x.1) ω +
      (μ[bellman μ 𝔾 Afeas f ((t : ℕ) + 1) (Function.update a t x.1) | 𝔾 t]) ω) := by
    refine ⟨C + (T + 1 : ℕ) * C, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact add_le_add (abs_le.1 (hfω _)).2 (abs_le.1 (hω _)).2
  exact le_ciSup hbdd (⟨x, hx⟩ : Afeas t a)

end

lemma tele (h : ℕ → ℝ) : ∑ t : Fin (T + 1), (h t - h ((t : ℕ) + 1)) = h 0 - h (T + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => h i - h (i + 1)), Finset.sum_range_sub']

/-- truncation of an action sequence after period `t` -/
def truncSeq (x0 : X) (t : Fin (T + 1)) (a : Fin (T + 1) → X) : Fin (T + 1) → X :=
  fun s => if s ≤ t then a s else x0

lemma truncSeq_meas (x0 : X) (𝔾 : Filtration (Fin (T + 1)) mΩ) (t : Fin (T + 1))
    (α : Ω → Fin (T + 1) → X) (hα : ∀ s, Measurable[𝔾 s] (fun ω => α ω s)) :
    Measurable[𝔾 t] (fun ω => truncSeq x0 t (α ω)) := by
  refine @measurable_pi_lambda Ω (Fin (T + 1)) (fun _ => X) (𝔾 t) _ _ (fun s => ?_)
  unfold truncSeq
  by_cases hs : s ≤ t
  · simp only [hs, if_true]
    exact (hα s).mono (𝔾.mono hs) le_rfl
  · simp only [hs, if_false]
    exact measurable_const

/-- the regularity used by the value-function lemmas (no condition on `𝓕_0`,
a.e. bounded rewards) -/
def Valid' (μ : Measure Ω) (M : RecursiveDP Ω X T) : Prop :=
  (∀ t a a', (∀ s, s < t → a s = a' s) → M.Afeas t a = M.Afeas t a') ∧
  (∀ t a, (M.Afeas t a).Nonempty) ∧
  (∀ t a, Measurable[M.𝔽 t] (M.rt t a)) ∧
  (∀ t a a', (∀ s, s ≤ t → a s = a' s) → M.rt t a = M.rt t a') ∧
  (∃ C : ℝ, ∀ t a, ∀ᵐ ω ∂μ, |M.rt t a ω| ≤ C)

lemma valid'_of_valid (μ : Measure Ω) (M : RecursiveDP Ω X T) (hM : M.Valid) : Valid' μ M := by
  obtain ⟨C, hC⟩ := hM.2.2.2.2.2
  exact ⟨hM.2.1, hM.2.2.1, hM.2.2.2.1, hM.2.2.2.2.1, C,
    fun t a => Filter.Eventually.of_forall (hC t a)⟩

section DP
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (M : RecursiveDP Ω X T)

lemma V_dep (hM : Valid' μ M) (t : ℕ) (a a' : Fin (T + 1) → X)
    (h : ∀ s : Fin (T + 1), (s : ℕ) < t → a s = a' s) : valueFn M μ t a = valueFn M μ t a' :=
  bellman_dep μ M.𝔽 M.Afeas M.rt hM.1 hM.2.2.2.1 _ t rfl a a' h

lemma V_meas (hM : Valid' μ M) (t : ℕ) (a : Fin (T + 1) → X) : Measurable (valueFn M μ t a) :=
  bellman_meas μ M.𝔽 M.Afeas M.rt hM.2.2.1 t a

lemma V_meas_fin (hM : Valid' μ M) (t : Fin (T + 1)) (a : Fin (T + 1) → X) :
    Measurable[M.𝔽 t] (valueFn M μ t a) :=
  bellman_meas_fin μ M.𝔽 M.Afeas M.rt hM.2.2.1 t a

lemma rt_bound (hM : Valid' μ M) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t a, ∀ᵐ ω ∂μ, |M.rt t a ω| ≤ C := by
  obtain ⟨C, hC⟩ := hM.2.2.2.2
  exact ⟨max C 0, le_max_right _ _, fun t a => by
    filter_upwards [hC t a] with ω h; exact h.trans (le_max_left _ _)⟩

lemma V_bound (hM : Valid' μ M) : ∃ K : ℝ, ∀ t a, ∀ᵐ ω ∂μ, |valueFn M μ t a ω| ≤ K := by
  obtain ⟨C, hC0, hC⟩ := rt_bound μ M hM
  refine ⟨(T + 1 : ℕ) * C, fun t a => ?_⟩
  exact bellman_bound μ M.𝔽 M.Afeas M.rt hM.2.1 C hC0 hC (T + 1) t (by omega) a

lemma V_ge (hM : Valid' μ M) (t : Fin (T + 1)) :
    ∀ᵐ ω ∂μ, ∀ a : Fin (T + 1) → X, a t ∈ M.Afeas t a →
      M.rt t a ω + (μ[valueFn M μ ((t : ℕ) + 1) a | M.𝔽 t]) ω ≤ valueFn M μ t a ω := by
  obtain ⟨C, hC0, hC⟩ := rt_bound μ M hM
  have h := fun a => bellman_ge μ M.𝔽 M.Afeas M.rt hM.2.1 C hC0 hC t a
  filter_upwards [ae_all_iff.2 h] with ω hω
  intro a ha
  have := hω a (a t) ha
  simp only [Function.update_eq_self] at this
  exact this

lemma V_last (t : ℕ) (ht : T < t) (a : Fin (T + 1) → X) : valueFn M μ t a = 0 :=
  bellman_gt μ M.𝔽 M.Afeas M.rt t ht a

lemma int_V (hM : Valid' μ M) (t : ℕ) (α : Ω → Fin (T + 1) → X) (hα : Measurable α) :
    Integrable (fun ω => valueFn M μ t (α ω) ω) μ := by
  obtain ⟨K, hK⟩ := V_bound μ M hM
  exact integrable_subst μ (fun b => valueFn M μ t b) (fun b => V_meas μ M hM t b) K
    (fun b => hK t b) α hα

lemma int_rt (hM : Valid' μ M) (t : Fin (T + 1)) (α : Ω → Fin (T + 1) → X) (hα : Measurable α) :
    Integrable (fun ω => M.rt t (α ω) ω) μ := by
  obtain ⟨C, _, hC⟩ := rt_bound μ M hM
  exact integrable_subst μ (fun b => M.rt t b)
    (fun b => (hM.2.2.1 t b).mono (M.𝔽.le t) le_rfl) C
    (fun b => hC t b) α hα

lemma int_CE (hM : Valid' μ M) (𝔾 : Filtration (Fin (T + 1)) mΩ) (t' : Fin (T + 1)) (t : ℕ)
    (α : Ω → Fin (T + 1) → X) (hα : Measurable α) :
    Integrable (fun ω => (μ[valueFn M μ t (α ω) | 𝔾 t']) ω) μ := by
  obtain ⟨K, hK⟩ := V_bound μ M hM
  exact integrable_subst μ (fun b => μ[valueFn M μ t b | 𝔾 t'])
    (fun b => (stronglyMeasurable_condExp.mono (𝔾.le t')).measurable) K
    (fun b => ae_bdd_abs_condExp_of_ae_bdd_abs (hK t b)) α hα

lemma integral_CE_V (hM : Valid' μ M) (x0 : X) (𝔾 : Filtration (Fin (T + 1)) mΩ)
    (t : Fin (T + 1)) (α : Ω → Fin (T + 1) → X)
    (hα : ∀ s, Measurable[𝔾 s] (fun ω => α ω s)) :
    ∫ ω, (μ[valueFn M μ ((t : ℕ) + 1) (α ω) | 𝔾 t]) ω ∂μ =
      ∫ ω, valueFn M μ ((t : ℕ) + 1) (α ω) ω ∂μ := by
  have e : ∀ ω, valueFn M μ ((t : ℕ) + 1) (α ω) =
      valueFn M μ ((t : ℕ) + 1) (truncSeq x0 t (α ω)) := by
    intro ω
    apply V_dep μ M hM
    intro s hs
    have : s ≤ t := by rw [Fin.le_def]; omega
    simp [truncSeq, this]
  have e1 : (fun ω => (μ[valueFn M μ ((t : ℕ) + 1) (α ω) | 𝔾 t]) ω) =
      fun ω => (μ[valueFn M μ ((t : ℕ) + 1) (truncSeq x0 t (α ω)) | 𝔾 t]) ω := by
    funext ω; rw [e ω]
  have e2 : (fun ω => valueFn M μ ((t : ℕ) + 1) (α ω) ω) =
      fun ω => valueFn M μ ((t : ℕ) + 1) (truncSeq x0 t (α ω)) ω := by
    funext ω; rw [e ω]
  rw [e1, e2]
  obtain ⟨K, hK⟩ := V_bound μ M hM
  have := setIntegral_condExp_subst' (mΩ := mΩ) μ (𝔾.le t)
    (fun b => valueFn M μ ((t : ℕ) + 1) b) (fun b => V_meas μ M hM _ b) K (fun b => hK _ b)
    (fun ω => truncSeq x0 t (α ω)) (truncSeq_meas x0 𝔾 t α hα) Set.univ MeasurableSet.univ
  simpa only [setIntegral_univ] using this

end DP

end IPAux



namespace IPAux

variable {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
  [DiscreteMeasurableSpace X] [Countable X] [DecidableEq X] {T : ℕ}

section DP2
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (M : RecursiveDP Ω X T)

lemma expand_pen (𝔾 : Filtration (Fin (T + 1)) mΩ) (a : Fin (T + 1) → X) (ω : Ω) :
    M.r a ω - idealPenalty M μ 𝔾 a ω = ∑ t : Fin (T + 1), (M.rt t a ω -
      ((μ[valueFn M μ ((t : ℕ) + 1) a | 𝔾 t]) ω -
        (μ[valueFn M μ ((t : ℕ) + 1) a | M.𝔽 t]) ω)) := by
  simp only [RecursiveDP.r, idealPenalty, penalty, penaltyComp, idealGen, Pi.sub_apply,
    Finset.sum_sub_distrib]

lemma meas_of_adapted (A : Set (Fin (T + 1) → X)) (𝔾 : Filtration (Fin (T + 1)) mΩ)
    (α : Ω → Fin (T + 1) → X) (hα : α ∈ adaptedPolicies A 𝔾) : Measurable α :=
  measurable_pi_lambda _ (fun t => (hα.2 t).mono (𝔾.le t) le_rfl)

lemma V_tele (hM : Valid' μ M) (α : Ω → Fin (T + 1) → X) (hα : Measurable α) :
    ∑ t : Fin (T + 1), (∫ ω, valueFn M μ (t : ℕ) (α ω) ω ∂μ -
      ∫ ω, valueFn M μ ((t : ℕ) + 1) (α ω) ω ∂μ) = ∫ ω, valueFn M μ 0 (α ω) ω ∂μ := by
  have := tele (T := T) (fun n : ℕ => ∫ ω, valueFn M μ n (α ω) ω ∂μ)
  rw [this]
  have h0 : (fun ω => valueFn M μ (T + 1) (α ω) ω) = fun _ => 0 := by
    funext ω; rw [V_last μ M (T + 1) (by omega)]; rfl
  rw [h0]; simp

/-- Main inequality: along every `𝔾`-adapted feasible policy, the penalized reward has
expectation at most `𝔼[V_0]`. -/
lemma dual_le (hM : Valid' μ M) (x0 : X) (𝔾 : Filtration (Fin (T + 1)) mΩ)
    (α : Ω → Fin (T + 1) → X) (hα : α ∈ adaptedPolicies M.A 𝔾) :
    ∫ ω, (M.r (α ω) ω - idealPenalty M μ 𝔾 (α ω) ω) ∂μ ≤
      ∫ ω, valueFn M μ 0 (α ω) ω ∂μ := by
  have hαm := meas_of_adapted M.A 𝔾 α hα
  have hint1 : ∀ t : Fin (T + 1), Integrable (fun ω => M.rt t (α ω) ω -
      ((μ[valueFn M μ ((t : ℕ) + 1) (α ω) | 𝔾 t]) ω -
        (μ[valueFn M μ ((t : ℕ) + 1) (α ω) | M.𝔽 t]) ω)) μ := fun t =>
    (int_rt μ M hM t α hαm).sub
      ((int_CE μ M hM 𝔾 t _ α hαm).sub (int_CE μ M hM M.𝔽 t _ α hαm))
  have hint2 : ∀ t : Fin (T + 1), Integrable (fun ω => valueFn M μ (t : ℕ) (α ω) ω -
      (μ[valueFn M μ ((t : ℕ) + 1) (α ω) | 𝔾 t]) ω) μ := fun t =>
    (int_V μ M hM _ α hαm).sub (int_CE μ M hM 𝔾 t _ α hαm)
  calc ∫ ω, (M.r (α ω) ω - idealPenalty M μ 𝔾 (α ω) ω) ∂μ
      = ∫ ω, ∑ t : Fin (T + 1), (M.rt t (α ω) ω -
          ((μ[valueFn M μ ((t : ℕ) + 1) (α ω) | 𝔾 t]) ω -
            (μ[valueFn M μ ((t : ℕ) + 1) (α ω) | M.𝔽 t]) ω)) ∂μ := by
        congr 1; funext ω; exact expand_pen μ M 𝔾 (α ω) ω
    _ ≤ ∫ ω, ∑ t : Fin (T + 1), (valueFn M μ (t : ℕ) (α ω) ω -
          (μ[valueFn M μ ((t : ℕ) + 1) (α ω) | 𝔾 t]) ω) ∂μ := by
        refine integral_mono_ae (integrable_finset_sum _ (fun t _ => hint1 t))
          (integrable_finset_sum _ (fun t _ => hint2 t)) ?_
        filter_upwards [ae_all_iff.2 (V_ge μ M hM)] with ω hω
        refine Finset.sum_le_sum (fun t _ => ?_)
        have := hω t (α ω) (hα.1 ω t)
        linarith
    _ = ∑ t : Fin (T + 1), (∫ ω, valueFn M μ (t : ℕ) (α ω) ω ∂μ -
          ∫ ω, valueFn M μ ((t : ℕ) + 1) (α ω) ω ∂μ) := by
        rw [integral_finset_sum _ (fun t _ => hint2 t)]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [integral_sub (int_V μ M hM _ α hαm) (int_CE μ M hM 𝔾 t _ α hαm),
          integral_CE_V μ M hM x0 𝔾 t α hα.2]
    _ = ∫ ω, valueFn M μ 0 (α ω) ω ∂μ := V_tele μ M hM α hαm

end DP2

section Construct
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (M : RecursiveDP Ω X T)
  (hne : ∀ t a, (M.Afeas t a).Nonempty) (e : ℕ → X) (ε : ℝ)

/-- an `ε`-good action index -/
def good (t : Fin (T + 1)) (a : Fin (T + 1) → X) (ω : Ω) (n : ℕ) : Prop :=
  e n ∈ M.Afeas t a ∧ valueFn M μ t a ω - ε <
    M.rt t (Function.update a t (e n)) ω +
      (μ[valueFn M μ ((t : ℕ) + 1) (Function.update a t (e n)) | M.𝔽 t]) ω

open Classical in
/-- measurable selection of an `ε`-optimal action -/
noncomputable def sel (t : Fin (T + 1)) (a : Fin (T + 1) → X) (ω : Ω) : X :=
  if h : ∃ n, good μ M e ε t a ω n then e (Nat.find h) else (hne t a).some

open Classical in
lemma sel_mem (t : Fin (T + 1)) (a : Fin (T + 1) → X) (ω : Ω) :
    sel μ M hne e ε t a ω ∈ M.Afeas t a := by
  unfold sel
  split_ifs with h
  · exact (Nat.find_spec h).1
  · exact (hne t a).some_mem

open Classical in
lemma sel_good (t : Fin (T + 1)) (a : Fin (T + 1) → X) (ω : Ω)
    (h : ∃ n, good μ M e ε t a ω n) :
    valueFn M μ t a ω - ε <
      M.rt t (Function.update a t (sel μ M hne e ε t a ω)) ω +
        (μ[valueFn M μ ((t : ℕ) + 1) (Function.update a t (sel μ M hne e ε t a ω)) |
          M.𝔽 t]) ω := by
  unfold sel
  rw [dif_pos h]
  exact (Nat.find_spec h).2

include hne in
lemma good_exists (he : Function.Surjective e) (hε : 0 < ε) (t : Fin (T + 1))
    (a : Fin (T + 1) → X) (ω : Ω) : ∃ n, good μ M e ε t a ω n := by
  have hV := bellman_fin μ M.𝔽 M.Afeas M.rt t a
  have hV' : valueFn M μ t a ω = ⨆ x : M.Afeas t a,
      (M.rt t (Function.update a t x.1) ω +
        (μ[valueFn M μ ((t : ℕ) + 1) (Function.update a t x.1) | M.𝔽 t]) ω) := by
    unfold valueFn; rw [hV]
  have : Nonempty (M.Afeas t a) := (hne t a).to_subtype
  have hlt : valueFn M μ t a ω - ε < valueFn M μ t a ω := by linarith
  rw [hV'] at hlt
  obtain ⟨x, hx⟩ := exists_lt_of_lt_ciSup hlt
  obtain ⟨n, hn⟩ := he x.1
  refine ⟨n, ?_, ?_⟩
  · rw [hn]; exact x.2
  · rw [hn, hV']; exact hx

lemma sel_meas (hM : Valid' μ M) (t : Fin (T + 1)) (a : Fin (T + 1) → X) :
    Measurable[M.𝔽 t] (sel μ M hne e ε t a) := by
  classical
  have hgm : ∀ n, MeasurableSet[M.𝔽 t] {ω | good μ M e ε t a ω n} := by
    intro n
    have h1 : MeasurableSet[M.𝔽 t] {ω : Ω | e n ∈ M.Afeas t a} := MeasurableSet.const _
    have h2 : MeasurableSet[M.𝔽 t] {ω | valueFn M μ t a ω - ε <
        M.rt t (Function.update a t (e n)) ω +
          (μ[valueFn M μ ((t : ℕ) + 1) (Function.update a t (e n)) | M.𝔽 t]) ω} :=
      measurableSet_lt ((V_meas_fin μ M hM t a).sub_const ε)
        ((hM.2.2.1 t _).add stronglyMeasurable_condExp.measurable)
    exact h1.inter h2
  have hex : MeasurableSet[M.𝔽 t] {ω | ∃ n, good μ M e ε t a ω n} := by
    rw [Set.setOf_exists]; exact MeasurableSet.iUnion hgm
  let p : ℕ → Ω → Prop := fun n ω => good μ M e ε t a ω n ∨ ¬ ∃ k, good μ M e ε t a ω k
  have hp : ∀ ω, ∃ n, p n ω := by
    intro ω
    by_cases h : ∃ k, good μ M e ε t a ω k
    · obtain ⟨k, hk⟩ := h; exact ⟨k, Or.inl hk⟩
    · exact ⟨0, Or.inr h⟩
  have hpm : ∀ n, MeasurableSet[M.𝔽 t] {ω | p n ω} := fun n =>
    (hgm n).union hex.compl
  let f : ℕ → Ω → X := fun n ω =>
    if ∃ k, good μ M e ε t a ω k then e n else (hne t a).some
  have hfm : ∀ n, Measurable[M.𝔽 t] (f n) := fun n =>
    Measurable.ite hex measurable_const measurable_const
  have hmf : Measurable[M.𝔽 t] (fun ω => f (Nat.find (hp ω)) ω) := Measurable.find hfm hpm hp
  convert hmf using 1
  funext ω
  by_cases h : ∃ k, good μ M e ε t a ω k
  · simp only [sel, dif_pos h, f, if_pos h]
    congr 1
    exact Nat.find_congr' (fun {n} => by simp only [p]; tauto)
  · simp only [sel, dif_neg h, f, if_neg h]

/-- the recursively built `ε`-optimal policy -/
noncomputable def build (x0 : X) : ℕ → Ω → Fin (T + 1) → X
  | 0 => fun _ _ => x0
  | k + 1 => fun ω => if h : k < T + 1 then
      Function.update (build x0 k ω) ⟨k, h⟩ (sel μ M hne e ε ⟨k, h⟩ (build x0 k ω) ω)
    else build x0 k ω

lemma build_succ (x0 : X) (t : Fin (T + 1)) (ω : Ω) :
    build μ M hne e ε x0 ((t : ℕ) + 1) ω =
      Function.update (build μ M hne e ε x0 t ω) t
        (sel μ M hne e ε t (build μ M hne e ε x0 t ω) ω) := by
  rw [build]; dsimp only; rw [dif_pos t.isLt]

lemma build_stable (x0 : X) (ω : Ω) (k : ℕ) :
    ∀ j, k ≤ j → ∀ s : Fin (T + 1), (s : ℕ) < k →
      build μ M hne e ε x0 j ω s = build μ M hne e ε x0 k ω s := by
  intro j hkj
  induction j, hkj using Nat.le_induction with
  | base => intro s _; rfl
  | succ j hkj ih =>
    intro s hs
    rw [build]
    dsimp only
    split_ifs with h
    · rw [Function.update_of_ne]
      · exact ih s hs
      · intro hh; rw [hh] at hs; simp at hs; omega
    · exact ih s hs

lemma build_meas (hM : Valid' μ M) (x0 : X) :
    ∀ k, ∀ j : Fin (T + 1), k ≤ (j : ℕ) + 1 → Measurable[M.𝔽 j] (build μ M hne e ε x0 k) := by
  intro k
  induction k with
  | zero => intro j _; exact measurable_const
  | succ k ih =>
    intro j hkj
    have hk : k < T + 1 := by omega
    have hb : Measurable[M.𝔽 j] (build μ M hne e ε x0 k) := ih j (by omega)
    have hbk : Measurable[M.𝔽 ⟨k, hk⟩] (build μ M hne e ε x0 k) := ih ⟨k, hk⟩ (by simp)
    have hsel : Measurable[M.𝔽 ⟨k, hk⟩]
        (fun ω => sel μ M hne e ε ⟨k, hk⟩ (build μ M hne e ε x0 k ω) ω) := by
      have h1 : Measurable[(M.𝔽 ⟨k, hk⟩).prod inferInstance]
          (fun p : Ω × (Fin (T + 1) → X) => sel μ M hne e ε ⟨k, hk⟩ p.2 p.1) :=
        measurable_from_prod_countable_left (m := M.𝔽 ⟨k, hk⟩)
          (fun b => sel_meas μ M hne e ε hM ⟨k, hk⟩ b)
      exact h1.comp (Measurable.prodMk (m := M.𝔽 ⟨k, hk⟩) measurable_id hbk)
    have hsel' : Measurable[M.𝔽 j]
        (fun ω => sel μ M hne e ε ⟨k, hk⟩ (build μ M hne e ε x0 k ω) ω) :=
      hsel.mono (M.𝔽.mono (by rw [Fin.le_def]; simp; omega)) le_rfl
    have e1 : build μ M hne e ε x0 (k + 1) = fun ω =>
        Function.update (build μ M hne e ε x0 k ω) ⟨k, hk⟩
          (sel μ M hne e ε ⟨k, hk⟩ (build μ M hne e ε x0 k ω) ω) := by
      funext ω; rw [build]; dsimp only; rw [dif_pos hk]
    rw [e1]
    refine @measurable_pi_lambda Ω (Fin (T + 1)) (fun _ => X) (M.𝔽 j) _ _ (fun s => ?_)
    by_cases hs : s = ⟨k, hk⟩
    · subst hs; simpa using hsel'
    · simp only [Function.update_of_ne hs]
      exact (measurable_pi_apply s).comp hb

end Construct

section Policy
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (M : RecursiveDP Ω X T)
  (hne : ∀ t a, (M.Afeas t a).Nonempty) (e : ℕ → X) (ε : ℝ) (x0 : X)

lemma pol_agree (ω : Ω) (t : ℕ) (ht : t ≤ T + 1) (s : Fin (T + 1)) (hs : (s : ℕ) < t) :
    build μ M hne e ε x0 (T + 1) ω s = build μ M hne e ε x0 t ω s :=
  build_stable μ M hne e ε x0 ω t (T + 1) ht s hs

lemma pol_succ_agree (ω : Ω) (t : Fin (T + 1)) (s : Fin (T + 1)) (hs : s ≤ t) :
    build μ M hne e ε x0 (T + 1) ω s = build μ M hne e ε x0 ((t : ℕ) + 1) ω s :=
  pol_agree μ M hne e ε x0 ω _ (by omega) s (by rw [Fin.le_def] at hs; omega)

lemma pol_coord (ω : Ω) (t : Fin (T + 1)) :
    build μ M hne e ε x0 (T + 1) ω t =
      sel μ M hne e ε t (build μ M hne e ε x0 t ω) ω := by
  rw [pol_succ_agree μ M hne e ε x0 ω t t le_rfl, build_succ, Function.update_self]

lemma pol_mem (hM : Valid' μ M) (ω : Ω) : build μ M hne e ε x0 (T + 1) ω ∈ M.A := by
  intro t
  rw [pol_coord]
  have : M.Afeas t (build μ M hne e ε x0 (T + 1) ω) =
      M.Afeas t (build μ M hne e ε x0 t ω) :=
    hM.1 t _ _ (fun s hs => pol_agree μ M hne e ε x0 ω t (by omega) s (by
      rw [Fin.lt_def] at hs; exact hs))
  rw [this]
  exact sel_mem μ M hne e ε t _ ω

lemma pol_adapted (hM : Valid' μ M) (t : Fin (T + 1)) :
    Measurable[M.𝔽 t] (fun ω => build μ M hne e ε x0 (T + 1) ω t) := by
  have : (fun ω => build μ M hne e ε x0 (T + 1) ω t) =
      fun ω => build μ M hne e ε x0 ((t : ℕ) + 1) ω t := by
    funext ω; exact pol_succ_agree μ M hne e ε x0 ω t t le_rfl
  rw [this]
  exact (measurable_pi_apply t).comp (build_meas μ M hne e ε hM x0 _ t le_rfl)

lemma pol_good (hM : Valid' μ M) (he : Function.Surjective e) (hε : 0 < ε) (ω : Ω)
    (t : Fin (T + 1)) :
    valueFn M μ t (build μ M hne e ε x0 (T + 1) ω) ω - ε <
      M.rt t (build μ M hne e ε x0 (T + 1) ω) ω +
        (μ[valueFn M μ ((t : ℕ) + 1) (build μ M hne e ε x0 (T + 1) ω) | M.𝔽 t]) ω := by
  have h := sel_good μ M hne e ε t (build μ M hne e ε x0 t ω) ω
    (good_exists μ M hne e ε he hε t _ ω)
  rw [← build_succ] at h
  have h1 : valueFn M μ t (build μ M hne e ε x0 (T + 1) ω) =
      valueFn M μ t (build μ M hne e ε x0 t ω) :=
    V_dep μ M hM _ _ _ (fun s hs => pol_agree μ M hne e ε x0 ω t (by omega) s hs)
  have h2 : valueFn M μ ((t : ℕ) + 1) (build μ M hne e ε x0 (T + 1) ω) =
      valueFn M μ ((t : ℕ) + 1) (build μ M hne e ε x0 ((t : ℕ) + 1) ω) :=
    V_dep μ M hM _ _ _ (fun s hs => pol_agree μ M hne e ε x0 ω _ (by omega) s hs)
  have h3 : M.rt t (build μ M hne e ε x0 (T + 1) ω) =
      M.rt t (build μ M hne e ε x0 ((t : ℕ) + 1) ω) :=
    hM.2.2.2.1 t _ _ (fun s hs => pol_succ_agree μ M hne e ε x0 ω t s hs)
  rw [h1, h2, h3]
  exact h

end Policy

lemma primal_approx (μ : Measure Ω) [IsProbabilityMeasure μ] (M : RecursiveDP Ω X T)
    (hM : Valid' μ M) [Nonempty X] (ε : ℝ) (hε : 0 < ε) :
    ∃ α ∈ adaptedPolicies M.A M.𝔽,
      ∫ ω, valueFn M μ 0 (α ω) ω ∂μ - (T + 1 : ℕ) * ε ≤ ∫ ω, M.r (α ω) ω ∂μ := by
  obtain ⟨e, he⟩ := exists_surjective_nat X
  have hne := hM.2.1
  set α := build μ M hne e ε (e 0) (T + 1) with hαdef
  have hα : α ∈ adaptedPolicies M.A M.𝔽 :=
    ⟨fun ω => pol_mem μ M hne e ε (e 0) hM ω, fun t => pol_adapted μ M hne e ε (e 0) hM t⟩
  refine ⟨α, hα, ?_⟩
  have hαm := meas_of_adapted M.A M.𝔽 α hα
  have hint2 : ∀ t : Fin (T + 1), Integrable (fun ω => valueFn M μ (t : ℕ) (α ω) ω -
      (μ[valueFn M μ ((t : ℕ) + 1) (α ω) | M.𝔽 t]) ω - ε) μ := fun t =>
    ((int_V μ M hM _ α hαm).sub (int_CE μ M hM M.𝔽 t _ α hαm)).sub (integrable_const ε)
  calc ∫ ω, valueFn M μ 0 (α ω) ω ∂μ - (T + 1 : ℕ) * ε
      = ∑ t : Fin (T + 1), (∫ ω, valueFn M μ (t : ℕ) (α ω) ω ∂μ -
          ∫ ω, valueFn M μ ((t : ℕ) + 1) (α ω) ω ∂μ - ε) := by
        rw [Finset.sum_sub_distrib, V_tele μ M hM α hαm]
        simp
    _ = ∫ ω, ∑ t : Fin (T + 1), (valueFn M μ (t : ℕ) (α ω) ω -
          (μ[valueFn M μ ((t : ℕ) + 1) (α ω) | M.𝔽 t]) ω - ε) ∂μ := by
        rw [integral_finset_sum _ (fun t _ => hint2 t)]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        have hA : Integrable (fun ω => valueFn M μ (t : ℕ) (α ω) ω -
            (μ[valueFn M μ ((t : ℕ) + 1) (α ω) | M.𝔽 t]) ω) μ :=
          (int_V μ M hM _ α hαm).sub (int_CE μ M hM M.𝔽 t _ α hαm)
        rw [integral_sub hA (integrable_const ε),
          integral_sub (int_V μ M hM _ α hαm) (int_CE μ M hM M.𝔽 t _ α hαm),
          integral_CE_V μ M hM (e 0) M.𝔽 t α hα.2]
        simp
    _ ≤ ∫ ω, ∑ t : Fin (T + 1), M.rt t (α ω) ω ∂μ := by
        refine integral_mono (integrable_finset_sum _ (fun t _ => hint2 t))
          (integrable_finset_sum _ (fun t _ => int_rt μ M hM t α hαm)) ?_
        intro ω
        refine Finset.sum_le_sum (fun t _ => ?_)
        have := pol_good μ M hne e ε (e 0) hM he hε ω t
        linarith
    _ = ∫ ω, M.r (α ω) ω ∂μ := rfl

end IPAux



namespace IPAux

lemma prop22i {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Countable X] {T : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Set (Fin (T + 1) → X)) (𝔽 𝔾 : Filtration (Fin (T + 1)) mΩ)
    (h𝔾 : IsRelaxation 𝔽 𝔾) (w : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ)
    (hw : GeneratingFns μ w) :
    penalty μ 𝔽 𝔾 w ∈ penalties μ A ∧
      ∀ α ∈ adaptedPolicies A 𝔽,
        (∀ t, μ[fun ω => penaltyComp μ 𝔽 𝔾 w t (α ω) ω | 𝔽 t] =ᵐ[μ] 0) ∧
          ∫ ω, penalty μ 𝔽 𝔾 w (α ω) ω ∂μ = 0 := by
  classical
  have hFG : 𝔽 ≤ 𝔾 := h𝔾
  obtain ⟨C, hC⟩ := hw.2.2
  have hwi : ∀ t b, Integrable (w t b) μ := fun t b =>
    Integrable.of_bound (hw.2.1 t b) C
      (by filter_upwards [hC t b] with ω h; simpa [Real.norm_eq_abs] using h)
  -- integrability of a substituted conditional expectation
  have hCEint : ∀ (𝔾' : Filtration (Fin (T + 1)) mΩ) (t : Fin (T + 1))
      (β : Ω → Fin (T + 1) → X), Measurable β →
      Integrable (fun ω => (μ[w t (β ω) | 𝔾' t]) ω) μ := by
    intro 𝔾' t β hβ
    exact integrable_subst μ (fun b => μ[w t b | 𝔾' t])
      (fun b => (stronglyMeasurable_condExp.mono (𝔾'.le t)).measurable) C
      (fun b => ae_bdd_abs_condExp_of_ae_bdd_abs (hC t b)) β hβ
  have hcompint : ∀ (t : Fin (T + 1)) (β : Ω → Fin (T + 1) → X), Measurable β →
      Integrable (fun ω => penaltyComp μ 𝔽 𝔾 w t (β ω) ω) μ := by
    intro t β hβ
    exact (hCEint 𝔾 t β hβ).sub (hCEint 𝔽 t β hβ)
  have hpenint : ∀ (β : Ω → Fin (T + 1) → X), Measurable β →
      Integrable (fun ω => penalty μ 𝔽 𝔾 w (β ω) ω) μ := by
    intro β hβ
    exact integrable_finset_sum _ (fun t _ => hcompint t β hβ)
  refine ⟨fun α hα => hpenint α (measurable_pi_lambda _ (fun t => hα.2 t)), ?_⟩
  intro α hα
  have hαm : Measurable α := measurable_pi_lambda _ (fun t => (hα.2 t).mono (𝔽.le t) le_rfl)
  -- key: the set integral of each penalty component vanishes on `𝓕_t`-sets
  have hkey : ∀ (t : Fin (T + 1)) (s : Set Ω), MeasurableSet[𝔽 t] s →
      ∫ ω in s, penaltyComp μ 𝔽 𝔾 w t (α ω) ω ∂μ = 0 := by
    intro t s hs
    obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
    have x0 : X := α ω0 0
    set β : Ω → Fin (T + 1) → X := fun ω => truncSeq x0 t (α ω)
    have hβF : Measurable[𝔽 t] β := truncSeq_meas x0 𝔽 t α hα.2
    have hβG : Measurable[𝔾 t] β := truncSeq_meas x0 𝔾 t α
      (fun s => (hα.2 s).mono (hFG s) le_rfl)
    have hβ : Measurable β := hβF.mono (𝔽.le t) le_rfl
    have e : ∀ ω, w t (α ω) = w t (β ω) := by
      intro ω
      apply hw.1
      intro s hs
      simp [β, truncSeq, hs]
    have e2 : (fun ω => penaltyComp μ 𝔽 𝔾 w t (α ω) ω) =
        fun ω => (μ[w t (β ω) | 𝔾 t]) ω - (μ[w t (β ω) | 𝔽 t]) ω := by
      funext ω; simp only [penaltyComp, Pi.sub_apply, e ω]
    rw [e2, integral_sub (hCEint 𝔾 t β hβ).integrableOn (hCEint 𝔽 t β hβ).integrableOn,
      setIntegral_condExp_subst (mΩ := mΩ) μ (𝔾.le t) (w t) (hwi t) C (hC t) β hβG s
        (hFG t s hs),
      setIntegral_condExp_subst (mΩ := mΩ) μ (𝔽.le t) (w t) (hwi t) C (hC t) β hβF s hs,
      sub_self]
  refine ⟨fun t => ?_, ?_⟩
  · have := ae_eq_condExp_of_forall_setIntegral_eq (μ := μ) (𝔽.le t)
      (f := fun ω => penaltyComp μ 𝔽 𝔾 w t (α ω) ω) (g := 0) (hcompint t α hαm)
      (fun s _ _ => integrableOn_zero)
      (fun s hs _ => by rw [hkey t s hs]; simp)
      aestronglyMeasurable_zero
    exact this.symm
  · have : (fun ω => penalty μ 𝔽 𝔾 w (α ω) ω) =
        fun ω => ∑ t, penaltyComp μ 𝔽 𝔾 w t (α ω) ω := rfl
    rw [this, integral_finset_sum _ (fun t _ => hcompint t α hαm)]
    refine Finset.sum_eq_zero (fun t _ => ?_)
    have := hkey t Set.univ MeasurableSet.univ
    rwa [setIntegral_univ] at this

end IPAux

open IPAux in
theorem solution {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Countable X] [DecidableEq X] {T : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : RecursiveDP Ω X T) (hM : M.Valid)
    (𝔾 : Filtration (Fin (T + 1)) mΩ) (h𝔾 : IsRelaxation M.𝔽 𝔾)
    (w : Fin (T + 1) → (Fin (T + 1) → X) → Ω → ℝ) (hw : GeneratingFns μ w) :
    ∀ a : Fin (T + 1) → X,
      ((∫ ω, dualValueFn M μ 𝔾 w 0 a ω ∂μ : ℝ) : EReal) =
          dualBound μ M.A 𝔾 M.r (penalty μ M.𝔽 𝔾 w) ∧
        primalValue μ M.A M.𝔽 M.r ≤ ((∫ ω, dualValueFn M μ 𝔾 w 0 a ω ∂μ : ℝ) : EReal) := by
  intro a
  have hFG : M.𝔽 ≤ 𝔾 := h𝔾
  haveI : Nonempty X := ⟨a 0⟩
  have x0 : X := a 0
  obtain ⟨Cw, hCw⟩ := hw.2.2
  have hMv : Valid' μ M := valid'_of_valid μ M hM
  let M' : RecursiveDP Ω X T :=
    ⟨𝔾, M.Afeas, fun t a ω => M.rt t a ω - penaltyComp μ M.𝔽 𝔾 w t a ω⟩
  have hM' : Valid' μ M' := by
    refine ⟨hM.2.1, hM.2.2.1, fun t b => ?_, fun t b b' h => ?_, ?_⟩
    · show Measurable[𝔾 t] (fun ω => M.rt t b ω - penaltyComp μ M.𝔽 𝔾 w t b ω)
      unfold penaltyComp
      exact ((hM.2.2.2.1 t b).mono (hFG t) le_rfl).sub
        ((stronglyMeasurable_condExp.measurable).sub
          ((stronglyMeasurable_condExp.mono (hFG t)).measurable))
    · show (fun ω => M.rt t b ω - penaltyComp μ M.𝔽 𝔾 w t b ω) =
        fun ω => M.rt t b' ω - penaltyComp μ M.𝔽 𝔾 w t b' ω
      simp only [penaltyComp, hM.2.2.2.2.1 t b b' h, hw.1 t b b' h]
    · obtain ⟨C, hC⟩ := hM.2.2.2.2.2
      refine ⟨C + (Cw + Cw), fun t b => ?_⟩
      have h1 := ae_bdd_abs_condExp_of_ae_bdd_abs (m := 𝔾 t) (hCw t b)
      have h2 := ae_bdd_abs_condExp_of_ae_bdd_abs (m := M.𝔽 t) (hCw t b)
      filter_upwards [h1, h2] with ω hω1 hω2
      show |M.rt t b ω - penaltyComp μ M.𝔽 𝔾 w t b ω| ≤ C + (Cw + Cw)
      unfold penaltyComp
      simp only [Pi.sub_apply]
      have := hC t b ω
      calc |M.rt t b ω - ((μ[w t b | 𝔾 t]) ω - (μ[w t b | M.𝔽 t]) ω)|
          ≤ |M.rt t b ω| + (|(μ[w t b | 𝔾 t]) ω| + |(μ[w t b | M.𝔽 t]) ω|) :=
            (abs_sub _ _).trans (add_le_add le_rfl (abs_sub _ _))
        _ ≤ C + (Cw + Cw) := add_le_add this (add_le_add hω1 hω2)
  have hr' : ∀ b ω, M'.r b ω = M.r b ω - penalty μ M.𝔽 𝔾 w b ω := by
    intro b ω
    simp only [RecursiveDP.r, penalty, M', Finset.sum_sub_distrib]
  set c : ℝ := ∫ ω, dualValueFn M μ 𝔾 w 0 a ω ∂μ with hc
  have hW0 : ∀ α : Ω → Fin (T + 1) → X, ∫ ω, valueFn M' μ 0 (α ω) ω ∂μ = c := by
    intro α
    have : (fun ω => valueFn M' μ 0 (α ω) ω) = fun ω => dualValueFn M μ 𝔾 w 0 a ω := by
      funext ω
      rw [V_dep μ M' hM' 0 (α ω) a (fun s hs => absurd hs (Nat.not_lt_zero _))]
      rfl
    rw [this]
  have hpol : adaptedPolicies M'.A M'.𝔽 = adaptedPolicies M.A 𝔾 := rfl
  have hupper : ∀ α ∈ adaptedPolicies M.A 𝔾,
      ∫ ω, (M.r (α ω) ω - penalty μ M.𝔽 𝔾 w (α ω) ω) ∂μ ≤ c := by
    intro α hα
    have h := dual_le μ M' hM' x0 M'.𝔽 α hα
    have hz : ∀ b ω, idealPenalty M' μ M'.𝔽 b ω = 0 := by
      intro b ω; simp [idealPenalty, penalty, penaltyComp]
    simp only [hz, sub_zero, hr', hW0] at h
    exact h
  have hlower : ∀ ε : ℝ, 0 < ε → ∃ α ∈ adaptedPolicies M.A 𝔾,
      c - (T + 1 : ℕ) * ε ≤ ∫ ω, (M.r (α ω) ω - penalty μ M.𝔽 𝔾 w (α ω) ω) ∂μ := by
    intro ε hε
    obtain ⟨α, hα, h⟩ := primal_approx μ M' hM' ε hε
    refine ⟨α, hα, ?_⟩
    simp only [hr', hW0] at h
    exact h
  have hDc : dualBound μ M.A 𝔾 M.r (penalty μ M.𝔽 𝔾 w) ≤ (c : EReal) := by
    unfold dualBound supValue
    exact iSup₂_le fun α hα => EReal.coe_le_coe_iff.2 (hupper α hα)
  have hcD : (c : EReal) ≤ dualBound μ M.A 𝔾 M.r (penalty μ M.𝔽 𝔾 w) := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    have hq2' : q < c := EReal.coe_lt_coe_iff.1 hq2
    have hT : (0 : ℝ) < (T + 1 : ℕ) := by positivity
    obtain ⟨α, hα, hval⟩ := hlower ((c - q) / (T + 1 : ℕ)) (div_pos (by linarith) hT)
    have hq : q ≤ ∫ ω, (M.r (α ω) ω - penalty μ M.𝔽 𝔾 w (α ω) ω) ∂μ := by
      have : (T + 1 : ℕ) * ((c - q) / (T + 1 : ℕ)) = c - q := by field_simp
      rw [this] at hval; linarith
    have : ((∫ ω, (M.r (α ω) ω - penalty μ M.𝔽 𝔾 w (α ω) ω) ∂μ : ℝ) : EReal) ≤
        dualBound μ M.A 𝔾 M.r (penalty μ M.𝔽 𝔾 w) := by
      unfold dualBound supValue
      exact le_iSup₂ (f := fun α (_ : α ∈ adaptedPolicies M.A 𝔾) =>
        ((∫ ω, (M.r (α ω) ω - penalty μ M.𝔽 𝔾 w (α ω) ω) ∂μ : ℝ) : EReal)) α hα
    have := (EReal.coe_le_coe_iff.2 hq).trans this
    exact absurd hq1 (not_lt.2 this)
  have hDeq : dualBound μ M.A 𝔾 M.r (penalty μ M.𝔽 𝔾 w) = c := le_antisymm hDc hcD
  refine ⟨hDeq.symm, ?_⟩
  have hp := prop22i μ M.A M.𝔽 𝔾 h𝔾 w hw
  unfold primalValue supValue
  refine iSup₂_le fun α hα => ?_
  have hαm : Measurable α := meas_of_adapted M.A M.𝔽 α hα
  have hαpol : α ∈ policies (Ω := Ω) M.A := ⟨hα.1, fun t => (hα.2 t).mono (M.𝔽.le t) le_rfl⟩
  have hrint : Integrable (fun ω => M.r (α ω) ω) μ :=
    integrable_finset_sum _ (fun t _ => int_rt μ M hMv t α hαm)
  have e : ∫ ω, M.r (α ω) ω ∂μ = ∫ ω, (M.r (α ω) ω - penalty μ M.𝔽 𝔾 w (α ω) ω) ∂μ := by
    rw [integral_sub hrint (hp.1 α hαpol), (hp.2 α hα).2, sub_zero]
  rw [e]
  have hαG : α ∈ adaptedPolicies M.A 𝔾 := ⟨hα.1, fun t => (hα.2 t).mono (hFG t) le_rfl⟩
  exact EReal.coe_le_coe_iff.2 (hupper α hαG)
