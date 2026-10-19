-- Prove2me | solution 1 for OAI.AdaptiveReveals.Scheme.hit_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:08:55.777923+00:00
-- url     : https://prove2.me/submissions/32d99c65-1123-4754-a3fb-d4693b0aaa70

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
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary
import Definitions.Def_OAI_Probability_CriticalZ3_Matching
import Definitions.Def_OAI_Probability_CriticalZ3_Peierls
import Definitions.Def_OAI_Probability_CriticalZ3_Coarse
import Definitions.Def_OAI_Probability_CriticalZ3_AdaptiveReveals

open OAI OAI.AdaptiveReveals OAI.AdaptiveReveals.Scheme
universe uF
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory ProbabilityTheory Classical
open InfiniteConditioning
variable {E V S : Type} [Countable E] [DecidableEq V]
variable (P : Scheme E V S)
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

theorem ar_union {E : Type} (J : Finset E) (A : (J → Bool) → Set (E → Bool)) :
    {ω | ω ∈ A (J.restrict ω)} = ⋃ a ∈ (Finset.univ : Finset (J → Bool)),
      (pattern J (ProductCylinder.extend J a) ∩ A a) := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Finset.mem_univ, true_and,
    hc_mem_pattern_extend]
  constructor
  · intro h; exact ⟨_, trivial, rfl, h⟩
  · rintro ⟨a, _, rfl, h⟩; exact h

theorem ar_hit_meas (n : ℕ) : ∀ (s : S) (U : Finset V), MeasurableSet (P.hit n s U) := by
  induction n with
  | zero =>
    intro s U
    simp only [Scheme.hit]
    split_ifs <;> simp
  | succ n ih =>
    intro s U
    simp only [Scheme.hit]
    rcases P.vertex s with _ | v
    · split_ifs <;> simp
    · change MeasurableSet {ω | ω ∈ (fun a : P.reveal s → Bool =>
          {ω | (v ∈ U → P.bad s a = true) ∧ ω ∈ P.hit n (P.child s a) (U.erase v)})
          ((P.reveal s).restrict ω)}
      rw [ar_union (P.reveal s) (fun a : P.reveal s → Bool =>
          {ω | (v ∈ U → P.bad s a = true) ∧ ω ∈ P.hit n (P.child s a) (U.erase v)})]
      refine Finset.measurableSet_biUnion _ (fun a _ => ?_)
      have hle : ∀ S' : Set E, (⨆ e ∈ S', bitSigma e) ≤ (inferInstance : MeasurableSpace (E → Bool)) :=
        fun S' => iSup₂_le (fun e _ => (measurable_pi_apply e).comap_le)
      refine (hle _ _ (hc_pattern_meas _ _)).inter ?_
      have : {ω : E → Bool | (v ∈ U → P.bad s a = true) ∧ ω ∈ P.hit n (P.child s a) (U.erase v)} =
          {_ω | (v ∈ U → P.bad s a = true)} ∩ P.hit n (P.child s a) (U.erase v) := rfl
      rw [this]
      exact (MeasurableSet.const _).inter (ih _ _)

theorem solution (I : S → Prop) (f : ℝ) (hf : 0 ≤ f)
    (hbad : ∀ s, I s → P.badMass s ≤ f)
    (hchild : ∀ s, I s → ∀ a, 0 < P.weight s a → I (P.child s a))
    (n : ℕ) (s : S) (hs : I s) (U : Finset V) :
    (ProductCylinder.law (P.parameter s)).real (P.hit n s U) ≤ f^U.card := by
  classical
  have hle : ∀ S' : Set E, (⨆ e ∈ S', bitSigma e) ≤ (inferInstance : MeasurableSpace (E → Bool)) :=
    fun S' => iSup₂_le (fun e _ => (measurable_pi_apply e).comap_le)
  have htot : ∀ s, ∑ a : P.reveal s → Bool, P.weight s a = 1 := by
    intro s
    have := hc_measure_select (P.parameter s) (P.reveal s) (fun _ => Set.univ) (fun _ => MeasurableSet.univ)
    simp only [Set.mem_univ, Set.setOf_true, probReal_univ, mul_one] at this
    simpa [Scheme.weight] using this.symm
  have hw0 : ∀ s a, 0 ≤ P.weight s a := fun s a => measureReal_nonneg
  induction n generalizing s U with
  | zero =>
    simp only [Scheme.hit]
    split_ifs with hU
    · subst hU; simp
    · simp only [measureReal_empty]; exact pow_nonneg hf _
  | succ n ih =>
    simp only [Scheme.hit]
    rcases hv : P.vertex s with _ | v
    · simp only
      split_ifs with hU
      · subst hU; simp
      · simp only [measureReal_empty]; exact pow_nonneg hf _
    · simp only
      change (ProductCylinder.law (P.parameter s)).real {ω | ω ∈ (fun a : P.reveal s → Bool =>
          {ω | (v ∈ U → P.bad s a = true) ∧ ω ∈ P.hit n (P.child s a) (U.erase v)})
          ((P.reveal s).restrict ω)} ≤ _
      rw [hc_measure_select (P.parameter s) (P.reveal s) (fun a : P.reveal s → Bool =>
          {ω | (v ∈ U → P.bad s a = true) ∧ ω ∈ P.hit n (P.child s a) (U.erase v)})]
      swap
      · intro a
        have : {ω : E → Bool | (v ∈ U → P.bad s a = true) ∧ ω ∈ P.hit n (P.child s a) (U.erase v)} =
            {_ω | (v ∈ U → P.bad s a = true)} ∩ P.hit n (P.child s a) (U.erase v) := rfl
        rw [this]
        exact (MeasurableSet.const _).inter (ar_hit_meas P n _ _)
      have hterm : ∀ a : P.reveal s → Bool,
          (ProductCylinder.law (P.parameter s)).real (pattern (P.reveal s) (ProductCylinder.extend (P.reveal s) a)) *
          (ProductCylinder.law (fixedParameter (P.parameter s) (P.reveal s) (ProductCylinder.extend (P.reveal s) a))).real
            {ω | (v ∈ U → P.bad s a = true) ∧ ω ∈ P.hit n (P.child s a) (U.erase v)} ≤
          P.weight s a * (if v ∈ U ∧ P.bad s a = false then 0 else f ^ (U.erase v).card) := by
        intro a
        rw [← P.parameter_child s a]
        change P.weight s a * _ ≤ _
        rcases (hw0 s a).lt_or_eq with hpos | hzero
        · apply mul_le_mul_of_nonneg_left _ (hw0 s a)
          split_ifs with hc
          · have : {ω : E → Bool | (v ∈ U → P.bad s a = true) ∧ ω ∈ P.hit n (P.child s a) (U.erase v)} = ∅ := by
              ext ω; simp [hc.1, hc.2]
            rw [this, measureReal_empty]
          · exact (measureReal_mono (fun ω hω => hω.2)).trans (ih _ (hchild s hs a hpos) _)
        · rw [← hzero]; simp
      refine (Finset.sum_le_sum (fun a _ => hterm a)).trans ?_
      by_cases hvU : v ∈ U
      · have hcard : U.card = (U.erase v).card + 1 := (Finset.card_erase_add_one hvU).symm
        have : ∑ a : P.reveal s → Bool, P.weight s a * (if v ∈ U ∧ P.bad s a = false then 0 else f ^ (U.erase v).card) =
            P.badMass s * f ^ (U.erase v).card := by
          unfold Scheme.badMass
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          cases hb : P.bad s a <;> simp [hvU, hb]
        rw [this, hcard, pow_succ]
        calc P.badMass s * f ^ (U.erase v).card ≤ f * f ^ (U.erase v).card :=
              mul_le_mul_of_nonneg_right (hbad s hs) (pow_nonneg hf _)
          _ = f ^ (U.erase v).card * f := mul_comm _ _
      · have : ∑ a : P.reveal s → Bool, P.weight s a * (if v ∈ U ∧ P.bad s a = false then 0 else f ^ (U.erase v).card) =
            f ^ U.card := by
          simp only [hvU, false_and, if_false, Finset.erase_eq_of_notMem hvU]
          rw [← Finset.sum_mul, htot, one_mul]
        rw [this]

