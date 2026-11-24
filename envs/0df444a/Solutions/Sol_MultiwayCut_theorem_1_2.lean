-- Prove2me | solution 1 for MultiwayCut.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T08:12:30.525077+00:00
-- url     : https://prove2.me/submissions/fa4cbeaa-2241-44e0-8906-8b169e7f2466

import Mathlib
import Definitions.Def_MultiwayCut_Instance
import Definitions.Def_MultiwayCut_ExpClocks
import Definitions.Def_MultiwayCut_CKR
import Definitions.Def_MultiwayCut_Algorithm3
import Definitions.Def_MultiwayCut_Transformation
import Definitions.Def_MultiwayCut_A53
import Theorems.Thm_MultiwayCut_observation_5_1
import Theorems.Thm_MultiwayCut_lemma_5_1
import Theorems.Thm_MultiwayCut_theorem_1_2_density
import Theorems.Thm_MultiwayCut_karger_reduction

open MeasureTheory
open MultiwayCut

namespace SolTheorem12

private lemma expClock_single {k : ℕ} [NeZero k] (Z : Fin k → ℝ) (i : Fin k) :
    expClock Z (Pi.single i 1) = i := by
  unfold expClock
  have hS : (Finset.univ.filter fun a : Fin k =>
      0 < (Pi.single i (1 : ℝ) : Fin k → ℝ) a ∧
        ∀ j : Fin k, 0 < (Pi.single i (1 : ℝ) : Fin k → ℝ) j →
          Z a * (Pi.single i (1 : ℝ) : Fin k → ℝ) j ≤
            Z j * (Pi.single i (1 : ℝ) : Fin k → ℝ) a) = {i} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨ha, _⟩
      by_contra hne
      rw [Pi.single_eq_of_ne hne] at ha
      exact lt_irrefl 0 ha
    · rintro rfl
      refine ⟨by simp, fun j hj => ?_⟩
      by_cases hja : j = a
      · subst hja; exact le_rfl
      · exfalso
        rw [Pi.single_eq_of_ne hja] at hj
        exact lt_irrefl 0 hj
  simp [hS]

private lemma clockLaw_terminals_eq_zero {k : ℕ} [NeZero k] {V : Type} [Fintype V]
    (I : Instance V k) (x : V → Fin k → ℝ) (hx : IsFeasibleEmbedding I x) :
    clockLaw k {Z | ∃ i : Fin k, expClock Z (x (I.t i)) ≠ i} = 0 := by
  have hempty : {Z : Fin k → ℝ | ∃ i : Fin k, expClock Z (x (I.t i)) ≠ i} = ∅ := by
    ext Z
    simp only [Set.mem_ofPred, Set.mem_empty_iff_false, iff_false, not_exists, not_not]
    intro i
    rw [hx.2 i, expClock_single]
  rw [hempty, measure_empty]

private lemma ckr_single {k : ℕ} [NeZero k] {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    ckr r σ (Pi.single i 1) = i := by
  unfold ckr
  set m₀ : Fin k := σ.symm i
  by_cases hm₀ : m₀.val < k - 1
  · have hS : (Finset.univ.filter fun m : Fin k =>
        m.val < k - 1 ∧ r ≤ (Pi.single i (1 : ℝ) : Fin k → ℝ) (σ m)) = {m₀} := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hrm⟩
        by_contra hne
        have hσ : σ m ≠ i := by
          intro h
          apply hne
          simpa [m₀] using congrArg σ.symm h
        rw [Pi.single_eq_of_ne hσ] at hrm
        linarith
      · rintro rfl
        refine ⟨hm₀, ?_⟩
        simp [m₀, hr1]
    simp [hS, m₀]
  · have hS : ¬ (Finset.univ.filter fun m : Fin k =>
        m.val < k - 1 ∧ r ≤ (Pi.single i (1 : ℝ) : Fin k → ℝ) (σ m)).Nonempty := by
      rintro ⟨m, hm⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      have hne : m ≠ m₀ := by
        intro h
        subst h
        exact hm₀ hm.1
      have hσ : σ m ≠ i := by
        intro h
        apply hne
        simpa [m₀] using congrArg σ.symm h
      have hrm := hm.2
      rw [Pi.single_eq_of_ne hσ] at hrm
      linarith
    simp only [hS, ↓reduceDIte]
    have hm₀_eq : (⟨k - 1, Nat.sub_one_lt (NeZero.ne k)⟩ : Fin k) = m₀ := by
      apply Fin.ext
      change k - 1 = m₀.val
      have hlt : m₀.val < k := m₀.isLt
      omega
    rw [hm₀_eq]
    simp [m₀]

private lemma ckrProb_terminals_eq_zero {k : ℕ} [NeZero k] {V : Type} [Fintype V]
    (I : Instance V k) (x : V → Fin k → ℝ) (hx : IsFeasibleEmbedding I x) :
    ckrProb (fun r σ => ∃ i : Fin k, ckr r σ (quadTransform (A53 k) (x (I.t i))) ≠ i) = 0 := by
  have hf : IsFeasibleTransform (quadTransform (A53 k)) :=
    lemma_5_1 (A53 k) observation_5_1.1.1 observation_5_1.1.2
  unfold ckrProb
  have hsum : ∑ σ : Equiv.Perm (Fin k),
      (volume {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧
        ∃ i : Fin k, ckr r σ (quadTransform (A53 k) (x (I.t i))) ≠ i}).toReal = 0 := by
    apply Finset.sum_eq_zero
    intro σ _
    have hnull : volume {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧
        ∃ i : Fin k, ckr r σ (quadTransform (A53 k) (x (I.t i))) ≠ i} = 0 := by
      refine measure_mono_null (fun r hr => ?_) (measure_singleton (0 : ℝ))
      rcases hr with ⟨⟨hr0, hr1⟩, i, hi⟩
      rw [hx.2 i, hf.2.1 i] at hi
      simp only [Set.mem_singleton_iff]
      by_contra hne0
      have hpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hne0)
      exact hi (ckr_single hpos hr1 σ i)
    rw [hnull]
    simp
  rw [hsum, zero_div]

private lemma isProbabilityMeasure_clockLaw (k : ℕ) : IsProbabilityMeasure (clockLaw k) := by
  unfold clockLaw
  have : ∀ _ : Fin k, IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    fun _ => ProbabilityTheory.isProbabilityMeasure_expMeasure zero_lt_one
  infer_instance

private lemma sepExp_self {k : ℕ} [NeZero k] (u : Fin k → ℝ) : sepExp u u = 0 := by
  unfold sepExp
  simp

private lemma sepExp_comm {k : ℕ} [NeZero k] (u v : Fin k → ℝ) : sepExp u v = sepExp v u := by
  unfold sepExp
  congr 2
  ext Z
  exact ne_comm

private lemma sepExp_triangle {k : ℕ} [NeZero k] (u v w : Fin k → ℝ) :
    sepExp u w ≤ sepExp u v + sepExp v w := by
  have := isProbabilityMeasure_clockLaw k
  unfold sepExp
  have hsub : {Z : Fin k → ℝ | expClock Z u ≠ expClock Z w} ⊆
      {Z : Fin k → ℝ | expClock Z u ≠ expClock Z v} ∪
      {Z : Fin k → ℝ | expClock Z v ≠ expClock Z w} := by
    intro Z hZ
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred, not_or, not_not] at h
    exact hZ (h.1.trans h.2)
  have hle : clockLaw k {Z | expClock Z u ≠ expClock Z w} ≤
      clockLaw k {Z | expClock Z u ≠ expClock Z v} +
      clockLaw k {Z | expClock Z v ≠ expClock Z w} :=
    (measure_mono hsub).trans (measure_union_le _ _)
  have hfin1 : clockLaw k {Z | expClock Z u ≠ expClock Z v} ≠ ⊤ := measure_ne_top _ _
  have hfin2 : clockLaw k {Z | expClock Z v ≠ expClock Z w} ≠ ⊤ := measure_ne_top _ _
  calc (clockLaw k {Z | expClock Z u ≠ expClock Z w}).toReal
      ≤ (clockLaw k {Z | expClock Z u ≠ expClock Z v} +
          clockLaw k {Z | expClock Z v ≠ expClock Z w}).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin1, hfin2⟩) hle
    _ = (clockLaw k {Z | expClock Z u ≠ expClock Z v}).toReal +
          (clockLaw k {Z | expClock Z v ≠ expClock Z w}).toReal :=
        ENNReal.toReal_add hfin1 hfin2

private lemma sepCKR_self {k : ℕ} [NeZero k] (u : Fin k → ℝ) : sepCKR u u = 0 := by
  unfold sepCKR ckrProb
  simp

private lemma sepCKR_comm {k : ℕ} [NeZero k] (u v : Fin k → ℝ) : sepCKR u v = sepCKR v u := by
  unfold sepCKR ckrProb
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  congr 2
  ext r
  simp [ne_comm]

private lemma volume_Icc_subset_ne_top {S : Set ℝ} (hS : S ⊆ Set.Icc (0 : ℝ) 1) :
    volume S ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono hS)
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

private lemma sepCKR_triangle {k : ℕ} [NeZero k] (u v w : Fin k → ℝ) :
    sepCKR u w ≤ sepCKR u v + sepCKR v w := by
  unfold sepCKR ckrProb
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro σ _
  set Suw : Set ℝ := {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧ ckr r σ u ≠ ckr r σ w}
  set Suv : Set ℝ := {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧ ckr r σ u ≠ ckr r σ v}
  set Svw : Set ℝ := {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧ ckr r σ v ≠ ckr r σ w}
  have hsub : Suw ⊆ Suv ∪ Svw := by
    rintro r ⟨hr, huw⟩
    by_contra h
    simp only [Suv, Svw, Set.mem_union, Set.mem_ofPred, not_or, not_and, not_not] at h
    exact huw ((h.1 hr).trans (h.2 hr))
  have hle : volume Suw ≤ volume Suv + volume Svw :=
    (measure_mono hsub).trans (measure_union_le _ _)
  have hfin1 : volume Suv ≠ ⊤ := volume_Icc_subset_ne_top (fun _ hr => hr.1)
  have hfin2 : volume Svw ≠ ⊤ := volume_Icc_subset_ne_top (fun _ hr => hr.1)
  calc (volume Suw).toReal
      ≤ (volume Suv + volume Svw).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin1, hfin2⟩) hle
    _ = (volume Suv).toReal + (volume Svw).toReal :=
        ENNReal.toReal_add hfin1 hfin2

private lemma alg3Sep_self {k : ℕ} [NeZero k] (p : ℝ) (f : (Fin k → ℝ) → Fin k → ℝ)
    (u : Fin k → ℝ) : alg3Sep p f u u = 0 := by
  unfold alg3Sep
  simp [sepExp_self, sepCKR_self]

private lemma alg3Sep_comm {k : ℕ} [NeZero k] (p : ℝ) (f : (Fin k → ℝ) → Fin k → ℝ)
    (u v : Fin k → ℝ) : alg3Sep p f u v = alg3Sep p f v u := by
  unfold alg3Sep
  rw [sepExp_comm, sepCKR_comm]

private lemma alg3Sep_triangle {k : ℕ} [NeZero k] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (Fin k → ℝ) → Fin k → ℝ) (u v w : Fin k → ℝ) :
    alg3Sep p f u w ≤ alg3Sep p f u v + alg3Sep p f v w := by
  unfold alg3Sep
  have h1 : sepExp u w ≤ sepExp u v + sepExp v w := sepExp_triangle u v w
  have h2 : sepCKR (f u) (f w) ≤ sepCKR (f u) (f v) + sepCKR (f v) (f w) :=
    sepCKR_triangle (f u) (f v) (f w)
  have h1p : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  nlinarith

private lemma halfL1_single {k : ℕ} (a b : Fin k) :
    halfL1 (Pi.single a 1) (Pi.single b 1) = if a ≠ b then 1 else 0 := by
  unfold halfL1
  by_cases hab : a = b
  · subst hab
    simp
  · simp only [ne_eq, hab, not_false_eq_true, ↓reduceIte]
    let term : Fin k → ℝ := fun ℓ =>
      |(Pi.single a (1 : ℝ) : Fin k → ℝ) ℓ - (Pi.single b (1 : ℝ) : Fin k → ℝ) ℓ|
    have hsum : ∑ ℓ : Fin k, term ℓ = 2 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
      have hb_mem : b ∈ (Finset.univ : Finset (Fin k)).erase a :=
        Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩
      rw [← Finset.add_sum_erase _ _ hb_mem]
      have ha_val : term a = 1 := by
        dsimp [term]
        rw [Pi.single_eq_same, Pi.single_eq_of_ne hab]
        norm_num
      have hb_val : term b = 1 := by
        dsimp [term]
        rw [Pi.single_eq_of_ne (Ne.symm hab), Pi.single_eq_same]
        norm_num
      have hrest : ∑ ℓ ∈ ((Finset.univ : Finset (Fin k)).erase a).erase b, term ℓ = 0 := by
        apply Finset.sum_eq_zero
        intro ℓ hℓ
        have hℓb : ℓ ≠ b := (Finset.mem_erase.mp hℓ).1
        have hℓa : ℓ ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hℓ).2).1
        dsimp [term]
        rw [Pi.single_eq_of_ne hℓa, Pi.single_eq_of_ne hℓb]
        norm_num
      rw [ha_val, hb_val, hrest]
      norm_num
    change 1 / 2 * ∑ ℓ : Fin k, term ℓ = 1
    rw [hsum]
    norm_num

private lemma single_mem_simplex {k : ℕ} (j : Fin k) :
    (Pi.single j (1 : ℝ) : Fin k → ℝ) ∈ stdSimplex ℝ (Fin k) := by
  refine ⟨fun i => ?_, ?_⟩
  · by_cases hij : i = j
    · subst hij; simp
    · simp [Pi.single_eq_of_ne hij]
  · simp

private lemma relaxValue_single_eq_cutWeight {k : ℕ} {V : Type} (I : Instance V k)
    (g : V → Fin k) :
    relaxValue I (fun v => Pi.single (g v) 1) = cutWeight I g := by
  unfold relaxValue cutWeight
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  rw [halfL1_single]
  split_ifs <;> ring

end SolTheorem12

theorem solution {k : ℕ} [NeZero k] {V : Type} [Fintype V] (I : Instance V k)
    (x : V → Fin k → ℝ) (hx : IsFeasibleEmbedding I x) :
    (clockLaw k {Z | ∃ i : Fin k, expClock Z (x (I.t i)) ≠ i} = 0 ∧
      ckrProb (fun r σ => ∃ i : Fin k, ckr r σ (quadTransform (A53 k) (x (I.t i))) ≠ i) = 0) ∧
    alg3Cost I (121 / 229) (quadTransform (A53 k)) x ≤ 297 / 229 * relaxValue I x ∧
    (IsRelaxOptimal I x → ∀ g : V → Fin k, IsFeasibleLabeling I g →
      alg3Cost I (121 / 229) (quadTransform (A53 k)) x ≤ 297 / 229 * cutWeight I g) := by
  have h1a := SolTheorem12.clockLaw_terminals_eq_zero I x hx
  have h1b := SolTheorem12.ckrProb_terminals_eq_zero I x hx
  have hkarger := karger_reduction
    (alg3Sep (121 / 229) (quadTransform (A53 k))) (297 / 229)
    (fun u _ => SolTheorem12.alg3Sep_self _ _ u)
    (fun u _ v _ => SolTheorem12.alg3Sep_comm _ _ u v)
    (fun u _ v _ w _ =>
      SolTheorem12.alg3Sep_triangle (by norm_num) (by norm_num) _ u v w)
    theorem_1_2_density
  have hcost : alg3Cost I (121 / 229) (quadTransform (A53 k)) x ≤
      297 / 229 * relaxValue I x := hkarger.2 I x hx
  refine ⟨⟨h1a, h1b⟩, hcost, ?_⟩
  intro hopt g hg
  let y : V → Fin k → ℝ := fun v => Pi.single (g v) 1
  have hy : IsFeasibleEmbedding I y := by
    refine ⟨fun v => SolTheorem12.single_mem_simplex (g v), fun i => ?_⟩
    simp [y, hg i]
  have hrel : relaxValue I x ≤ cutWeight I g := by
    calc relaxValue I x
        ≤ relaxValue I y := hopt.2 y hy
      _ = cutWeight I g := SolTheorem12.relaxValue_single_eq_cutWeight I g
  linarith
