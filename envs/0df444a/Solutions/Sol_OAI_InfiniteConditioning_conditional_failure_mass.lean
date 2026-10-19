-- Prove2me | solution 1 for OAI.InfiniteConditioning.conditional_failure_mass
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:12:33.227985+00:00
-- url     : https://prove2.me/submissions/6f0e71e7-b2a0-4e58-ad2c-ae2707314e0c

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality

open OAI OAI.InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]
theorem hc_map_replace {E : Type} (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool) :
    (ProductCylinder.law p).map (replace J ξ) = ProductCylinder.law (fixedParameter p J ξ) := by
  have hr : replace J ξ = fun ω e => (fun (b : Bool) => if e ∈ J then ξ e else b) (ω e) := by
    funext ω e; simp [replace]
  unfold ProductCylinder.law
  rw [hr, Measure.infinitePi_map_pi _ (fun e => Measurable.of_discrete)]
  congr 1; funext e
  by_cases he : e ∈ J
  · have h1 : (ite (e ∈ J) (ξ e) : Bool → Bool) = fun _ => ξ e := by funext b; simp [he]
    rw [h1, Measure.map_const, measure_univ, one_smul]
    unfold fixedParameter
    rw [if_pos he]
    cases ξ e
    · simp
    · simp
  · have h1 : (ite (e ∈ J) (ξ e) : Bool → Bool) = id := by funext b; simp [he]
    rw [h1, Measure.map_id]
    unfold fixedParameter
    rw [if_neg he]

theorem hc_bits_iIndep {E : Type} (p : E → Set.Icc (0 : ℝ) 1) :
    iIndep (fun e => bitSigma e) (ProductCylinder.law p) := by
  have := iIndepFun_infinitePi (P := fun e => bernoulliMeasure true false (p e))
    (X := fun _ (b : Bool) => b) (fun _ => measurable_id)
  rw [iIndepFun_iff_iIndep (fun _ => inferInstance)] at this
  exact this

theorem hc_indep_split {E : Type} (p : E → Set.Icc (0 : ℝ) 1) {S T : Set E} (hST : Disjoint S T)
    {s t : Set (E → Bool)} (hs : MeasurableSet[⨆ e ∈ S, bitSigma e] s)
    (ht : MeasurableSet[⨆ e ∈ T, bitSigma e] t) :
    ProductCylinder.law p (s ∩ t) = ProductCylinder.law p s * ProductCylinder.law p t :=
  (Indep_iff _ _ _).mp (indep_iSup_of_disjoint (fun e => (measurable_pi_apply e).comap_le)
    (hc_bits_iIndep p) hST) s t hs ht

theorem hc_bit_meas {E : Type} {S : Set E} {e : E} (he : e ∈ S) (b : Bool) :
    MeasurableSet[⨆ e ∈ S, bitSigma e] {ω : E → Bool | ω e = b} := by
  have h : MeasurableSet[bitSigma e] {ω : E → Bool | ω e = b} :=
    MeasurableSpace.measurableSet_comap.mpr ⟨{b}, trivial, rfl⟩
  exact (le_iSup₂ (f := fun e (_ : e ∈ S) => bitSigma e) e he) _ h

theorem hc_pattern_meas {E : Type} (J : Finset E) (ξ : E → Bool) :
    MeasurableSet[⨆ e ∈ (J : Set E), bitSigma e] (pattern J ξ) := by
  have : pattern J ξ = ⋂ e ∈ J, {ω : E → Bool | ω e = ξ e} := by
    ext ω; simp [pattern]
  rw [this]
  exact MeasurableSet.biInter J.countable_toSet (fun e he => hc_bit_meas he (ξ e))

theorem hc_replace_meas {E : Type} (J : Finset E) (ξ : E → Bool) :
    Measurable[⨆ e ∈ ((J : Set E)ᶜ), bitSigma e] (replace J ξ) := by
  rw [@measurable_pi_iff]
  intro e
  by_cases he : e ∈ J
  · have : (fun ω : E → Bool => replace J ξ ω e) = fun _ => ξ e := by funext ω; simp [replace, he]
    rw [this]; exact measurable_const
  · have : (fun ω : E → Bool => replace J ξ ω e) = fun ω => ω e := by funext ω; simp [replace, he]
    rw [this]
    exact (comap_measurable (fun ω : E → Bool => ω e)).mono
      (le_iSup₂ (f := fun e (_ : e ∈ ((J : Set E)ᶜ)) => bitSigma e) e (by simpa using he)) le_rfl

theorem hc_pattern_inter {E : Type} (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool)
    (A : Set (E → Bool)) (hA : MeasurableSet A) :
    ProductCylinder.law p (pattern J ξ ∩ A) =
      ProductCylinder.law p (pattern J ξ) * ProductCylinder.law (fixedParameter p J ξ) A := by
  have hset : pattern J ξ ∩ A = pattern J ξ ∩ (replace J ξ ⁻¹' A) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have : replace J ξ ω = ω := by
        funext e; by_cases he : e ∈ J
        · simp [replace, he, h1 e he]
        · simp [replace, he]
      rwa [this]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have : replace J ξ ω = ω := by
        funext e; by_cases he : e ∈ J
        · simp [replace, he, h1 e he]
        · simp [replace, he]
      rwa [this] at h2
  rw [hset, hc_indep_split p disjoint_compl_right (hc_pattern_meas J ξ) (hc_replace_meas J ξ hA),
    ← hc_map_replace p J ξ, Measure.map_apply (hc_replace_meas J ξ |>.mono (iSup₂_le (fun e _ => (measurable_pi_apply e).comap_le)) le_rfl) hA]

theorem hc_mem_pattern_extend {E : Type} (J : Finset E) (a : J → Bool) (ω : E → Bool) :
    ω ∈ pattern J (ProductCylinder.extend J a) ↔ J.restrict ω = a := by
  constructor
  · intro h; funext e
    have := h e e.2
    simpa [ProductCylinder.extend] using this
  · rintro rfl e he
    simp [ProductCylinder.extend, he]

theorem hc_measure_select {E : Type} (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (A : (J → Bool) → Set (E → Bool)) (hA : ∀ a, MeasurableSet (A a)) :
    (ProductCylinder.law p).real {ω | ω ∈ A (J.restrict ω)} =
      ∑ a : J → Bool, (ProductCylinder.law p).real (pattern J (ProductCylinder.extend J a)) *
        (ProductCylinder.law (fixedParameter p J (ProductCylinder.extend J a))).real (A a) := by
  have hset : {ω | ω ∈ A (J.restrict ω)} =
      ⋃ a ∈ (Finset.univ : Finset (J → Bool)), (pattern J (ProductCylinder.extend J a) ∩ A a) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Finset.mem_univ, true_and,
      hc_mem_pattern_extend]
    constructor
    · intro h; exact ⟨_, trivial, rfl, h⟩
    · rintro ⟨a, _, rfl, h⟩; exact h
  have hle : ∀ S : Set E, (⨆ e ∈ S, bitSigma e) ≤ (inferInstance : MeasurableSpace (E → Bool)) :=
    fun S => iSup₂_le (fun e _ => (measurable_pi_apply e).comap_le)
  have hpm : ∀ a, MeasurableSet (pattern J (ProductCylinder.extend J a)) := fun a =>
    hle _ _ (hc_pattern_meas J _)
  rw [hset, measureReal_biUnion_finset]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [measureReal_def, hc_pattern_inter p J _ (A a) (hA a), ENNReal.toReal_mul]
    rfl
  · intro a _ b _ hab
    refine Set.disjoint_left.mpr ?_
    rintro ω ⟨h1, _⟩ ⟨h2, _⟩
    rw [hc_mem_pattern_extend] at h1 h2
    exact hab (h1.symm.trans h2)
  · exact fun a _ => (hpm a).inter (hA a)

theorem hc_select_lower {E : Type} (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (P : (J → Bool) → Prop) (A : (J → Bool) → Set (E → Bool))
    (hA : ∀ a, MeasurableSet (A a)) {b : ℝ}
    (hb : ∀ a, P a → b ≤
      (ProductCylinder.law (fixedParameter p J (ProductCylinder.extend J a))).real (A a)) :
    b * (ProductCylinder.law p).real {ω | P (J.restrict ω)} ≤
      (ProductCylinder.law p).real {ω | P (J.restrict ω) ∧ ω ∈ A (J.restrict ω)} := by
  have h1 := hc_measure_select p J (fun a => if P a then Set.univ else ∅)
    (fun a => by split_ifs <;> simp)
  have h2 := hc_measure_select p J (fun a => if P a then A a else ∅)
    (fun a => by split_ifs; exact hA a; simp)
  have e1 : {ω : E → Bool | P (J.restrict ω)} =
      {ω | ω ∈ (fun a => if P a then Set.univ else ∅) (J.restrict ω)} := by
    ext ω; by_cases h : P (J.restrict ω) <;> simp [h]
  have e2 : {ω : E → Bool | P (J.restrict ω) ∧ ω ∈ A (J.restrict ω)} =
      {ω | ω ∈ (fun a => if P a then A a else ∅) (J.restrict ω)} := by
    ext ω; by_cases h : P (J.restrict ω) <;> simp [h]
  rw [e1, e2, h1, h2, Finset.mul_sum]
  refine Finset.sum_le_sum (fun a _ => ?_)
  by_cases h : P a
  · simp only [h, if_true, probReal_univ, mul_one]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hb a h) measureReal_nonneg
  · simp [h]

theorem hc_cyl_meas {E : Type} (K : Finset E) (S : Set E) (hKS : (K : Set E) ⊆ S)
    (B : Set (E → Bool)) (hB : ∀ ω ω', (∀ e ∈ K, ω' e = ω e) → (ω' ∈ B ↔ ω ∈ B)) :
    MeasurableSet[⨆ e ∈ S, bitSigma e] B := by
  have hBe : B = K.restrict ⁻¹' {ξ | ProductCylinder.extend K ξ ∈ B} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    exact (hB ω _ (fun e he => by simp [ProductCylinder.extend, he])).symm
  have hm : Measurable[⨆ e ∈ S, bitSigma e] (K.restrict : (E → Bool) → (K → Bool)) := by
    rw [@measurable_pi_iff]
    intro e
    exact (comap_measurable (fun ω : E → Bool => ω e)).mono
      (le_iSup₂ (f := fun e (_ : e ∈ S) => bitSigma e) (e : E) (hKS e.2)) le_rfl
  rw [hBe]
  exact hm MeasurableSet.of_discrete

theorem hc_disjoint_blocks {E I : Type} (p : E → Set.Icc (0 : ℝ) 1)
    (J : I → Finset E) (hJ : Pairwise (fun i j => Disjoint (J i) (J j)))
    (A : I → Set (E → Bool))
    (hA : ∀ i, ProductCylinder.DeterminedBy (F := Prop) (J i) (fun ω => ω ∈ A i))
    (s : Finset I) :
    (ProductCylinder.law p).real {ω | ∀ i ∈ s, ω ∈ A i} =
      ∏ i ∈ s, (ProductCylinder.law p).real (A i) := by
  have hA' : ∀ i ω ω', (∀ e ∈ J i, ω' e = ω e) → (ω' ∈ A i ↔ ω ∈ A i) := fun i ω ω' h =>
    (hA i ω ω' h).to_iff
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, ← ih]
    have hset : {ω | ∀ i ∈ insert j s, ω ∈ A i} = A j ∩ {ω | ∀ i ∈ s, ω ∈ A i} := by
      ext ω; simp [Finset.forall_mem_insert]
    have hdisj : Disjoint ((J j : Set E)) (⋃ i ∈ s, (J i : Set E)) := by
      refine Set.disjoint_left.mpr ?_
      intro e he he'
      simp only [Set.mem_iUnion] at he'
      obtain ⟨i, hi, hei⟩ := he'
      have hij : j ≠ i := fun h => hj (h ▸ hi)
      exact Finset.disjoint_left.mp (hJ hij) he hei
    have hm1 := hc_cyl_meas (J j) _ le_rfl (A j) (hA' j)
    have hm2 : MeasurableSet[⨆ e ∈ (⋃ i ∈ s, (J i : Set E)), bitSigma e] {ω | ∀ i ∈ s, ω ∈ A i} := by
      have : {ω : E → Bool | ∀ i ∈ s, ω ∈ A i} = ⋂ i ∈ s, A i := by ext ω; simp
      rw [this]
      exact MeasurableSet.biInter s.countable_toSet (fun i hi =>
        hc_cyl_meas (J i) _ (Set.subset_biUnion_of_mem (u := fun i => (J i : Set E)) hi) (A i) (hA' i))
    rw [hset, measureReal_def, hc_indep_split p hdisj hm1 hm2, ENNReal.toReal_mul]
    rfl

theorem hc_cond_failure {E : Type} (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (H C : Set (E → Bool))
    (hH : ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ H))
    (hC : MeasurableSet C) {δ : ℝ} :
    δ * (ProductCylinder.law p).real
      {ω | ω ∈ H ∧ conditionalProbability p J C ω ≤ 1-δ} ≤
    (ProductCylinder.law p).real (H ∩ Cᶜ) := by
  have hfix : ∀ ω : E → Bool, fixedParameter p J (ProductCylinder.extend J (J.restrict ω)) =
      fixedParameter p J ω := by
    intro ω; funext e
    by_cases he : e ∈ J <;> simp [fixedParameter, ProductCylinder.extend, he]
  have hcp : ∀ ω : E → Bool, conditionalProbability p J C (ProductCylinder.extend J (J.restrict ω)) =
      conditionalProbability p J C ω := by
    intro ω; unfold conditionalProbability; rw [hfix]
  have hHe : ∀ ω : E → Bool, (ProductCylinder.extend J (J.restrict ω) ∈ H) ↔ ω ∈ H := fun ω =>
    (hH ω _ (fun e he => by simp [ProductCylinder.extend, he])).to_iff
  let P : (J → Bool) → Prop := fun a =>
    ProductCylinder.extend J a ∈ H ∧ conditionalProbability p J C (ProductCylinder.extend J a) ≤ 1-δ
  have e1 : {ω | ω ∈ H ∧ conditionalProbability p J C ω ≤ 1-δ} = {ω | P (J.restrict ω)} := by
    ext ω; simp only [Set.mem_setOf_eq, P, hcp, hHe]
  have key := hc_select_lower p J P (fun _ => Cᶜ) (fun _ => hC.compl) (b := δ) (fun a ha => by
    have := ha.2
    unfold conditionalProbability at this
    rw [measureReal_compl hC, probReal_univ]
    linarith)
  rw [e1]
  refine key.trans (measureReal_mono ?_)
  rintro ω ⟨h1, h2⟩
  exact ⟨(hHe ω).mp h1.1, h2⟩

theorem solution (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (H C : Set (E → Bool))
    (hH : ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ H))
    (hC : MeasurableSet C) {δ : ℝ} (_hδ : 0 ≤ δ) :
    δ * (ProductCylinder.law p).real
      {ω | ω ∈ H ∧ conditionalProbability p J C ω ≤ 1-δ} ≤
    (ProductCylinder.law p).real (H ∩ Cᶜ) := by
  exact hc_cond_failure p J H C hH hC

