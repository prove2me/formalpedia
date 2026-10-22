-- Prove2me | solution 1 for HolleyLiggett.Duality.theorem_1_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T13:09:23.780274+00:00
-- url     : https://prove2.me/submissions/5d6946da-e7d7-43cb-a087-b7fd3909db38

import Mathlib
import Definitions.Def_HolleyLiggett_Duality_Setting

set_option autoImplicit false

namespace HLDualityAux

open MeasureTheory ProbabilityTheory HolleyLiggett.Duality
open scoped ENNReal NNReal Classical

/-- Product of tsums over a finite index type. -/
theorem tsum_pi_prod (ι : Type*) [Fintype ι] :
    ∀ g : ι → ℕ → ℝ≥0∞, ∑' x : ι → ℕ, ∏ i, g i (x i) = ∏ i, ∑' n, g i n := by
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ g : ι → ℕ → ℝ≥0∞, ∑' x : ι → ℕ, ∏ i, g i (x i) = ∏ i, ∑' n, g i n)
    ?_ ?_ ?_ ι
  · intro α β _ e h g
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    have h1 := h (fun a => g (e a))
    rw [← (Equiv.arrowCongr e (Equiv.refl ℕ)).tsum_eq]
    have h2 : ∀ x : α → ℕ, ∏ i, g i ((Equiv.arrowCongr e (Equiv.refl ℕ)) x i)
        = ∏ a, g (e a) (x a) := by
      intro x
      rw [← e.prod_comp]
      simp [Equiv.arrowCongr_apply]
    simp_rw [h2]
    rw [h1]
    exact e.prod_comp (fun i => ∑' n, g i n)
  · intro g
    simp
  · intro α _ h g
    rw [← (Equiv.piOptionEquivProd (β := fun _ => ℕ)).symm.tsum_eq]
    simp only [Fintype.prod_option]
    have h3 : ∀ c : ℕ × (α → ℕ),
        g none ((Equiv.piOptionEquivProd (β := fun _ => ℕ)).symm c none) *
          ∏ i, g (some i) ((Equiv.piOptionEquivProd (β := fun _ => ℕ)).symm c (some i))
        = g none c.1 * ∏ i, g (some i) (c.2 i) := by
      intro c; rfl
    simp_rw [h3]
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left, h (fun i => g (some i)), ENNReal.tsum_mul_right]

variable {I : Type*} [DecidableEq I]

theorem alpha_le_one (N : I → ℕ → Finset I) (f : I → PMF ℕ) (i : I) (η : Config I) :
    alpha N f i η ≤ 1 := by
  unfold alpha
  calc ∑' k, {k | ((N i k : Set I) ∩ occupied η).Nonempty}.indicator (fun k => f i k) k
      ≤ ∑' k, f i k := ENNReal.tsum_le_tsum (fun k => Set.indicator_le_self _ _ k)
    _ = 1 := (f i).tsum_coe

theorem tsum_disj (N : I → ℕ → Finset I) (f : I → PMF ℕ) (i : I) (η : Config I) :
    ∑' k, f i k * (if Disjoint (N i k : Set I) (occupied η) then 1 else 0)
      = 1 - alpha N f i η := by
  have hne : alpha N f i η ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (alpha_le_one N f i η)
  apply ENNReal.eq_sub_of_add_eq hne
  unfold alpha
  rw [← ENNReal.tsum_add]
  rw [← (f i).tsum_coe]
  congr 1
  funext k
  by_cases h : ((N i k : Set I) ∩ occupied η).Nonempty
  · have : ¬ Disjoint (N i k : Set I) (occupied η) := by
      rw [Set.not_disjoint_iff_nonempty_inter]; exact h
    simp [this, h]
  · have : Disjoint (N i k : Set I) (occupied η) := by
      rw [Set.disjoint_iff_inter_eq_empty]; exact Set.not_nonempty_iff_eq_empty.mp h
    simp [this, h]

theorem disj_iff (F : Finset I) (η : Config I) :
    Disjoint (F : Set I) (occupied η) ↔ η ∈ zeroOn F := by
  simp [zeroOn, occupied, Set.disjoint_left]

theorem zeroOn_eq (F : Finset I) :
    zeroOn F = (F : Set I).pi (fun _ => ({false} : Set Bool)) := by
  ext η; simp [zeroOn]

theorem measurableSet_zeroOn (F : Finset I) : MeasurableSet (zeroOn F) := by
  rw [zeroOn_eq]
  exact MeasurableSet.pi F.countable_toSet (fun _ _ => measurableSet_singleton _)

theorem factor_prob (a : ℝ≥0∞) (ha : a ≤ 1) :
    IsProbabilityMeasure (a • Measure.dirac true + (1 - a) • Measure.dirac false) := by
  constructor
  simp [add_tsub_cancel_of_le ha]

theorem factor_isProb (N : I → ℕ → Finset I) (f : I → PMF ℕ) (η : Config I) :
    ∀ i, IsProbabilityMeasure (alpha N f i η • Measure.dirac true
      + (1 - alpha N f i η) • Measure.dirac false) :=
  fun i => factor_prob _ (alpha_le_one N f i η)

theorem step_zeroOn (N : I → ℕ → Finset I) (f : I → PMF ℕ) (η : Config I) (F : Finset I) :
    proxStep N f η (zeroOn F) = ∏ i ∈ F, (1 - alpha N f i η) := by
  haveI := factor_isProb N f η
  rw [zeroOn_eq, proxStep, Measure.infinitePi_pi]
  · apply Finset.prod_congr rfl
    intro i _
    simp
  · intro i _; exact measurableSet_singleton _

theorem step_dual (N : I → ℕ → Finset I) (f : I → PMF ℕ) (η : Config I) (F : Finset I) :
    ∏ i ∈ F, (1 - alpha N f i η)
      = ∑' G, bpiStep N f F G * (if Disjoint (G : Set I) (occupied η) then 1 else 0) := by
  unfold bpiStep
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  have h1 : ∀ k : ↥F → ℕ,
      ∑' G : Finset I, (if Finset.univ.biUnion (fun i : ↥F => N i (k i)) = G
          then ∏ i : ↥F, f i (k i) else 0) * (if Disjoint (G : Set I) (occupied η) then 1 else 0)
        = ∏ i : ↥F, (f i (k i) *
            (if Disjoint (N i (k i) : Set I) (occupied η) then 1 else 0)) := by
    intro k
    rw [tsum_eq_single (Finset.univ.biUnion (fun i : ↥F => N i (k i)))]
    · rw [if_pos rfl, Finset.prod_mul_distrib, Fintype.prod_boole]
      congr 2
      simp [Finset.coe_biUnion, Set.disjoint_iUnion_left]
    · intro G hG
      rw [if_neg (Ne.symm hG), zero_mul]
  simp_rw [h1]
  rw [tsum_pi_prod ↥F (fun i n => f i n *
      (if Disjoint (N i n : Set I) (occupied η) then 1 else 0))]
  simp_rw [tsum_disj]
  exact (Finset.prod_coe_sort F (fun i => 1 - alpha N f i η)).symm

theorem measurable_alpha (N : I → ℕ → Finset I) (f : I → PMF ℕ) (i : I) :
    Measurable (fun η : Config I => alpha N f i η) := by
  unfold alpha
  refine Measurable.ennreal_tsum (fun k => ?_)
  have hs : MeasurableSet {η : Config I | ((N i k : Set I) ∩ occupied η).Nonempty} := by
    have : {η : Config I | ((N i k : Set I) ∩ occupied η).Nonempty}
        = ⋃ j ∈ N i k, (fun η : Config I => η j) ⁻¹' {true} := by
      ext η; simp [occupied, Set.Nonempty]
    rw [this]
    exact MeasurableSet.biUnion (N i k).countable_toSet
      (fun j _ => measurable_pi_apply j (measurableSet_singleton true))
  have : (fun η : Config I => {k | ((N i k : Set I) ∩ occupied η).Nonempty}.indicator
      (fun k => f i k) k)
      = {η : Config I | ((N i k : Set I) ∩ occupied η).Nonempty}.indicator (fun _ => f i k) := by
    funext η; first | rfl | simp [Set.indicator_apply]
  rw [this]
  exact measurable_const.indicator hs

theorem measurable_step (N : I → ℕ → Finset I) (f : I → PMF ℕ) :
    Measurable (fun η : Config I => proxStep N f η) := by
  haveI : ∀ η, IsProbabilityMeasure (proxStep N f η) := fun η => by
    haveI := factor_isProb N f η
    unfold proxStep; infer_instance
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ => MeasurableSpace.isPiSystem_measurableSet)
      (fun _ => Set.mem_setOf.mpr MeasurableSet.univ))
    ?_
  rintro S ⟨s, t, ht, rfl⟩
  have ht' : ∀ i, MeasurableSet (t i) := fun i => ht i (Set.mem_univ i)
  have : (fun η => proxStep N f η ((s : Set I).pi t))
      = fun η => ∏ i ∈ s, (alpha N f i η * Measure.dirac true (t i)
          + (1 - alpha N f i η) * Measure.dirac false (t i)) := by
    funext η
    haveI := factor_isProb N f η
    rw [proxStep, Measure.infinitePi_pi]
    · apply Finset.prod_congr rfl
      intro i _
      simp
    · intro i _; exact ht' i
  rw [this]
  refine Finset.measurable_prod s (fun i _ => ?_)
  have ha := measurable_alpha N f i
  exact (ha.mul_const _).add ((measurable_const.sub ha).mul_const _)

theorem bpi_ck (N : I → ℕ → Finset I) (f : I → PMF ℕ) :
    ∀ n F B, bpiProb N f (n + 1) F B = ∑' G, bpiStep N f F G * bpiProb N f n G B := by
  intro n
  induction n with
  | zero =>
    intro F B
    simp only [bpiProb]
    rw [tsum_eq_single F, tsum_eq_single B]
    · simp
    · intro G hG; simp [hG]
    · intro G hG; simp [Ne.symm hG]
  | succ n ih =>
    intro F B
    have e1 : ∀ H, bpiProb N f (n + 1) H B = ∑' G, bpiProb N f n H G * bpiStep N f G B :=
      fun H => rfl
    rw [show bpiProb N f (n + 1 + 1) F B = ∑' G, bpiProb N f (n + 1) F G * bpiStep N f G B
      from rfl]
    simp_rw [e1, ih]
    simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
    conv_lhs => rw [ENNReal.tsum_comm]
    simp_rw [mul_assoc]

theorem main [Countable I] (N : I → ℕ → Finset I) (f : I → PMF ℕ) (η : Config I) :
    ∀ n F, proxLaw N f η n (zeroOn F) = dualProb N f n F η := by
  intro n
  induction n with
  | zero =>
    intro F
    simp only [proxLaw, dualProb, bpiProb]
    rw [Measure.dirac_apply' _ (measurableSet_zeroOn F), tsum_eq_single F]
    · by_cases h : η ∈ zeroOn F
      · simp [Set.indicator_of_mem h, (disj_iff F η).mpr h]
      · have : ¬ Disjoint (F : Set I) (occupied η) := fun h' => h ((disj_iff F η).mp h')
        simp [Set.indicator_of_notMem h, this]
    · intro G hG; simp [Ne.symm hG]
  | succ n ih =>
    intro F
    rw [proxLaw, Measure.bind_apply (measurableSet_zeroOn F)
      (measurable_step N f).aemeasurable]
    simp_rw [step_zeroOn, step_dual]
    have hD : ∀ G : Finset I, (fun ξ : Config I =>
        (if Disjoint (G : Set I) (occupied ξ) then (1 : ℝ≥0∞) else 0))
        = (zeroOn G).indicator 1 := by
      intro G; funext ξ
      by_cases h : ξ ∈ zeroOn G
      · rw [Set.indicator_of_mem h, if_pos ((disj_iff G ξ).mpr h)]; rfl
      · rw [Set.indicator_of_notMem h, if_neg (fun h' => h ((disj_iff G ξ).mp h'))]
    rw [lintegral_tsum]
    · have h2 : ∀ G : Finset I, ∫⁻ ξ, bpiStep N f F G *
          (if Disjoint (G : Set I) (occupied ξ) then (1 : ℝ≥0∞) else 0) ∂(proxLaw N f η n)
          = bpiStep N f F G * dualProb N f n G η := by
        intro G
        have hm : Measurable (fun ξ : Config I =>
            (if Disjoint (G : Set I) (occupied ξ) then (1 : ℝ≥0∞) else 0)) := by
          rw [hD G]; exact measurable_one.indicator (measurableSet_zeroOn G)
        rw [lintegral_const_mul _ hm]
        rw [hD G, lintegral_indicator_one (measurableSet_zeroOn G), ih G]
      simp_rw [h2]
      unfold dualProb
      simp_rw [bpi_ck, ← ENNReal.tsum_mul_right]
      rw [ENNReal.tsum_comm]
      simp_rw [mul_assoc, ENNReal.tsum_mul_left]
    · intro G
      refine Measurable.aemeasurable ?_
      refine Measurable.const_mul ?_ _
      rw [hD G]; exact measurable_one.indicator (measurableSet_zeroOn G)

end HLDualityAux

open MeasureTheory ProbabilityTheory HolleyLiggett.Duality in
theorem solution {I : Type*} [Countable I] [DecidableEq I] (N : I → ℕ → Finset I)
    (hN0 : ∀ i, N i 0 = ∅) (f : I → PMF ℕ)
    (n : ℕ) (η : Config I) (F : Finset I) :
    proxLaw N f η n (zeroOn F) = dualProb N f n F η := by
  exact HLDualityAux.main N f η n F
