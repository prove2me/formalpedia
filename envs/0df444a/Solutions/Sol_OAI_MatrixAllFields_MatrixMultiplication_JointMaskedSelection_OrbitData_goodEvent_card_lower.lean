-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.JointMaskedSelection.OrbitData.goodEvent_card_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:26:16.682737+00:00
-- url     : https://prove2.me/submissions/5f6c3b14-d6e4-4f2b-895c-291bd5856370

import Mathlib
import Definitions.Def_OAIQ254M003

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointLossCounts
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.JointLossCounts

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {Ω V I : Type*}

theorem card_filter_exists_le (samples : Finset Ω) (indices : Finset I)
    (event : I → Ω → Prop) :
    (samples.filter (fun ω => ∃ i ∈ indices, event i ω)).card ≤
      ∑ i ∈ indices, (samples.filter (event i)).card := by
  classical
  have heq : samples.filter (fun ω => ∃ i ∈ indices, event i ω) =
      indices.biUnion (fun i => samples.filter (event i)) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hω, i, hi, he⟩
      exact ⟨i, hi, hω, he⟩
    · rintro ⟨i, hi, hω, he⟩
      exact ⟨hω, i, hi, he⟩
  rw [heq]
  exact Finset.card_biUnion_le

theorem competitor_union_card_mul_le (ownSurvival : Finset Ω)
    (competitors : Finset I) (collision : I → Ω → Prop) (M : ℕ)
    (hcollision : ∀ i ∈ competitors,
      M * (ownSurvival.filter (collision i)).card ≤ ownSurvival.card) :
    M * (ownSurvival.filter (fun ω => ∃ i ∈ competitors, collision i ω)).card ≤
      competitors.card * ownSurvival.card := by
  classical
  calc
    _ ≤ M * ∑ i ∈ competitors, (ownSurvival.filter (collision i)).card :=
      Nat.mul_le_mul_left M (card_filter_exists_le ownSurvival competitors collision)
    _ = ∑ i ∈ competitors, M * (ownSurvival.filter (collision i)).card :=
      by rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ competitors, ownSurvival.card :=
      Finset.sum_le_sum hcollision
    _ = _ := by simp

theorem randomLossFraction_nonneg (full passing : Finset V)
    (bad : V → Ω → Prop) (ω : Ω) : 0 ≤ randomLossFraction full passing bad ω :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem sum_randomLossCount (ownSurvival : Finset Ω) (passing : Finset V)
    (bad : V → Ω → Prop) :
    (∑ ω ∈ ownSurvival, randomLossCount passing bad ω) =
      ∑ v ∈ passing, (ownSurvival.filter (bad v)).card := by
  classical
  simp only [randomLossCount, Finset.card_filter]
  exact Finset.sum_comm

theorem sum_randomLossCount_le (ownSurvival : Finset Ω) (full passing : Finset V)
    (bad : V → Ω → Prop) (ε : ℝ) (hε : 0 ≤ ε) (hpassing : passing ⊆ full)
    (hbad : ∀ v ∈ passing,
      ((ownSurvival.filter (bad v)).card : ℝ) ≤ ε * (ownSurvival.card : ℝ)) :
    (∑ ω ∈ ownSurvival, (randomLossCount passing bad ω : ℝ)) ≤
      (full.card : ℝ) * (ε * (ownSurvival.card : ℝ)) := by
  classical
  have hdouble : (∑ ω ∈ ownSurvival, (randomLossCount passing bad ω : ℝ)) =
      ∑ v ∈ passing, ((ownSurvival.filter (bad v)).card : ℝ) := by
    exact_mod_cast sum_randomLossCount ownSurvival passing bad
  rw [hdouble]
  calc
    _ ≤ ∑ _v ∈ passing, ε * (ownSurvival.card : ℝ) := Finset.sum_le_sum hbad
    _ = (passing.card : ℝ) * (ε * (ownSurvival.card : ℝ)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast Finset.card_le_card hpassing)
      (mul_nonneg hε (Nat.cast_nonneg _))

theorem sum_randomLossFraction_le (ownSurvival : Finset Ω) (full passing : Finset V)
    (bad : V → Ω → Prop) (ε : ℝ) (hε : 0 ≤ ε) (hfull : 0 < full.card)
    (hpassing : passing ⊆ full)
    (hbad : ∀ v ∈ passing,
      ((ownSurvival.filter (bad v)).card : ℝ) ≤ ε * (ownSurvival.card : ℝ)) :
    (∑ ω ∈ ownSurvival, randomLossFraction full passing bad ω) ≤
      ε * (ownSurvival.card : ℝ) := by
  have hcard : (0 : ℝ) < full.card := by exact_mod_cast hfull
  simp only [randomLossFraction, ← Finset.sum_div]
  apply (div_le_iff₀ hcard).2
  simpa only [mul_comm] using
    sum_randomLossCount_le ownSurvival full passing bad ε hε hpassing hbad

theorem card_filter_mul_le_sum (samples : Finset Ω) (f : Ω → ℝ) (t : ℝ)
    (hf : ∀ ω ∈ samples, 0 ≤ f ω) :
    ((samples.filter (fun ω => t < f ω)).card : ℝ) * t ≤
      ∑ ω ∈ samples, f ω := by
  classical
  calc
    _ = ∑ _ω ∈ samples.filter (fun ω => t < f ω), t := by simp
    _ ≤ ∑ ω ∈ samples.filter (fun ω => t < f ω), f ω := by
      apply Finset.sum_le_sum
      intro ω hω
      exact (Finset.mem_filter.mp hω).2.le
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun ω hω _ => hf ω hω)

theorem bad_orbit_card_le (ownSurvival : Finset Ω) (full passing : Finset V)
    (bad : V → Ω → Prop) (ε N : ℝ) (hε : 0 ≤ ε) (hN : 0 < N)
    (hfull : 0 < full.card) (hpassing : passing ⊆ full)
    (hbad : ∀ v ∈ passing,
      ((ownSurvival.filter (bad v)).card : ℝ) ≤ ε * (ownSurvival.card : ℝ)) :
    ((ownSurvival.filter (fun ω => 1 / N < randomLossFraction full passing bad ω)).card : ℝ)
      ≤ N * ε * (ownSurvival.card : ℝ) := by
  classical
  have hm := card_filter_mul_le_sum ownSurvival
    (randomLossFraction full passing bad) (1 / N)
    (fun ω _ => randomLossFraction_nonneg full passing bad ω)
  have he := sum_randomLossFraction_le ownSurvival full passing bad ε hε hfull hpassing hbad
  have hdiv :
      ((ownSurvival.filter (fun ω => 1 / N < randomLossFraction full passing bad ω)).card : ℝ) / N
        ≤ ε * (ownSurvival.card : ℝ) := by
    simpa only [one_div, ← div_eq_mul_inv] using hm.trans he
  have hmul := (div_le_iff₀ hN).1 hdiv
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul

theorem targetBad_card_le (ownSurvival : Finset Ω) (orbits : Finset I)
    (full passing : I → Finset V) (bad : I → V → Ω → Prop)
    (eligible : Ω → Prop) (ε eligibilityError N : ℝ)
    (hε : 0 ≤ ε) (hN : 0 < N)
    (hfull : ∀ i ∈ orbits, 0 < (full i).card)
    (hpassing : ∀ i ∈ orbits, passing i ⊆ full i)
    (hbad : ∀ i ∈ orbits, ∀ v ∈ passing i,
      ((ownSurvival.filter (bad i v)).card : ℝ) ≤ ε * (ownSurvival.card : ℝ))
    (heligible : ((ownSurvival.filter (fun ω => ¬ eligible ω)).card : ℝ) ≤
      eligibilityError * (ownSurvival.card : ℝ)) :
    ((ownSurvival.filter (targetBad orbits full passing bad eligible N)).card : ℝ) ≤
      (eligibilityError + (orbits.card : ℝ) * N * ε) * (ownSurvival.card : ℝ) := by
  classical
  let excess := fun i ω => 1 / N < randomLossFraction (full i) (passing i) (bad i) ω
  have hunion : ownSurvival.filter (targetBad orbits full passing bad eligible N) =
      (ownSurvival.filter (fun ω => ¬ eligible ω)) ∪
        (ownSurvival.filter (fun ω => ∃ i ∈ orbits, excess i ω)) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_union, targetBad, excess]
    constructor
    · rintro ⟨hω, he | ho⟩
      · exact Or.inl ⟨hω, he⟩
      · exact Or.inr ⟨hω, ho⟩
    · rintro (⟨hω, he⟩ | ⟨hω, ho⟩)
      · exact ⟨hω, Or.inl he⟩
      · exact ⟨hω, Or.inr ho⟩
  have hu : ((ownSurvival.filter (targetBad orbits full passing bad eligible N)).card : ℝ) ≤
      ((ownSurvival.filter (fun ω => ¬ eligible ω)).card : ℝ) +
        ((ownSurvival.filter (fun ω => ∃ i ∈ orbits, excess i ω)).card : ℝ) := by
    rw [hunion]
    exact_mod_cast Finset.card_union_le
      (ownSurvival.filter (fun ω => ¬ eligible ω))
      (ownSurvival.filter (fun ω => ∃ i ∈ orbits, excess i ω))
  have horbits : ((ownSurvival.filter (fun ω => ∃ i ∈ orbits, excess i ω)).card : ℝ) ≤
      ∑ i ∈ orbits, ((ownSurvival.filter (excess i)).card : ℝ) := by
    exact_mod_cast card_filter_exists_le ownSurvival orbits excess
  have hsum : (∑ i ∈ orbits, ((ownSurvival.filter (excess i)).card : ℝ)) ≤
      (orbits.card : ℝ) * (N * ε * (ownSurvival.card : ℝ)) := by
    calc
      _ ≤ ∑ _i ∈ orbits, N * ε * (ownSurvival.card : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact bad_orbit_card_le ownSurvival (full i) (passing i) (bad i)
          ε N hε hN (hfull i hi) (hpassing i hi) (hbad i hi)
      _ = _ := by simp
  calc
    _ ≤ eligibilityError * (ownSurvival.card : ℝ) +
        (orbits.card : ℝ) * (N * ε * (ownSurvival.card : ℝ)) :=
      hu.trans (add_le_add heligible (horbits.trans hsum))
    _ = _ := by ring

theorem good_card_lower (ownSurvival : Finset Ω) (failure : Ω → Prop) (error : ℝ)
    (hbad : ((ownSurvival.filter failure).card : ℝ) ≤ error * (ownSurvival.card : ℝ)) :
    (1 - error) * (ownSurvival.card : ℝ) ≤
      ((ownSurvival.filter (fun ω => ¬ failure ω)).card : ℝ) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := ownSurvival) failure
  have hsplitR : ((ownSurvival.filter failure).card : ℝ) +
      ((ownSurvival.filter (fun ω => ¬ failure ω)).card : ℝ) =
      (ownSurvival.card : ℝ) := by exact_mod_cast hsplit
  nlinarith

end MatrixMultiplication.JointLossCounts

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_JointMaskedSelection
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.tripleSide_reorder _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialExact.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.JointCoarseReorder.tripleSide_reorder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.JointHashing

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {P R : Type*} [Fintype P] [CommRing R]

theorem survival_card [Fintype R] (U : Finset R) (I J : P → R) :
    Fintype.card {s : Sample P R // Survives (U : Set R) I J s} =
      Fintype.card R ^ Fintype.card P * U.card := by
  classical
  rw [Fintype.card_congr (survivalEquiv (U : Set R) I J)]
  simp

theorem shared_x_collision_iff (U : Set R) (I J J' : P → R)
    (s : Sample P R) (hs : Survives U I J s) :
    Survives U I J' s ↔ dot s.1 (J' - J) = 0 := by
  rcases hs with ⟨heq, hU⟩
  simp only [Survives, dot_sub_right]
  constructor
  · intro h
    dsimp [xHash, yHash] at heq h
    linear_combination heq - h.1
  · intro h
    refine ⟨?_, hU⟩
    dsimp [xHash, yHash] at heq ⊢
    linear_combination heq - h

theorem shared_y_collision_iff (U : Set R) (I I' J : P → R)
    (s : Sample P R) (hs : Survives U I J s) :
    Survives U I' J s ↔ dot s.1 (I' - I) = 0 := by
  rcases hs with ⟨heq, hU⟩
  simp only [Survives, dot_sub_right]
  constructor
  · intro h
    dsimp [xHash, yHash] at heq h
    linear_combination h.1 - heq
  · intro h
    have hx : xHash s I' = xHash s I := by
      dsimp [xHash]
      linear_combination h
    exact ⟨hx.trans heq, hx ▸ hU⟩

theorem linear_zero_fiber_card [Fintype R]
    (d : P → R) (i : P) (u : Rˣ) (hu : d i = u) :
    Fintype.card R * Fintype.card {v : P → R // dot v d = 0} =
      Fintype.card R ^ Fintype.card P := by
  classical
  have h := Fintype.card_congr (linearSplitEquiv d i u hu)
  simpa only [Fintype.card_prod, Fintype.card_fun] using h.symm

theorem collision_card_mul [Fintype R]
    (U : Finset R) (I J d : P → R) (i : P) (u : Rˣ) (hu : d i = u) :
    Fintype.card R *
      Fintype.card {s : Sample P R // Survives (U : Set R) I J s ∧ dot s.1 d = 0} =
      Fintype.card {s : Sample P R // Survives (U : Set R) I J s} := by
  classical
  have hcard : Fintype.card {s : Sample P R //
      Survives (U : Set R) I J s ∧ dot s.1 d = 0} =
      Fintype.card {v : P → R // dot v d = 0} * U.card := by
    simpa using Fintype.card_congr (collisionEquiv (U : Set R) I J d)
  calc
    _ = Fintype.card R * (Fintype.card {v : P → R // dot v d = 0} * U.card) :=
      congrArg (fun n : ℕ => Fintype.card R * n) hcard
    _ = (Fintype.card R * Fintype.card {v : P → R // dot v d = 0}) * U.card :=
      (mul_assoc _ _ _).symm
    _ = (Fintype.card R ^ Fintype.card P) * U.card :=
      congrArg (fun n : ℕ => n * U.card) (linear_zero_fiber_card d i u hu)
    _ = _ := (survival_card U I J).symm

theorem shared_x_collision_card_mul [Fintype R]
    (U : Finset R) (I J J' : P → R) (i : P) (u : Rˣ)
    (hu : J' i - J i = u) :
    Fintype.card R * Fintype.card {s : Sample P R //
      Survives (U : Set R) I J s ∧ Survives (U : Set R) I J' s} =
      Fintype.card {s : Sample P R // Survives (U : Set R) I J s} := by
  classical
  let e : {s : Sample P R // Survives (U : Set R) I J s ∧
      Survives (U : Set R) I J' s} ≃
      {s : Sample P R // Survives (U : Set R) I J s ∧ dot s.1 (J' - J) = 0} :=
    Equiv.subtypeEquivRight (fun s => and_congr_right (fun hs =>
      shared_x_collision_iff (U : Set R) I J J' s hs))
  rw [Fintype.card_congr e]
  exact collision_card_mul U I J (J' - J) i u hu

theorem shared_y_collision_card_mul [Fintype R]
    (U : Finset R) (I I' J : P → R) (i : P) (u : Rˣ)
    (hu : I' i - I i = u) :
    Fintype.card R * Fintype.card {s : Sample P R //
      Survives (U : Set R) I J s ∧ Survives (U : Set R) I' J s} =
      Fintype.card {s : Sample P R // Survives (U : Set R) I J s} := by
  classical
  let e : {s : Sample P R // Survives (U : Set R) I J s ∧
      Survives (U : Set R) I' J s} ≃
      {s : Sample P R // Survives (U : Set R) I J s ∧ dot s.1 (I' - I) = 0} :=
    Equiv.subtypeEquivRight (fun s => and_congr_right (fun hs =>
      shared_y_collision_iff (U : Set R) I I' J s hs))
  rw [Fintype.card_congr e]
  exact collision_card_mul U I J (I' - I) i u hu

theorem coarse_difference_isUnit (k : ℕ) (a b : Fin 17) (hab : a ≠ b) :
    IsUnit ((a.val : ZMod (37 ^ k)) - (b.val : ZMod (37 ^ k))) := by
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · have hu := small_nat_isUnit k (b.val - a.val) (Nat.sub_pos_of_lt h) (by omega)
    rw [Nat.cast_sub h.le] at hu
    simpa only [neg_sub] using hu.neg
  · have hu := small_nat_isUnit k (a.val - b.val) (Nat.sub_pos_of_lt h) (by omega)
    rwa [Nat.cast_sub h.le] at hu

theorem coarse_words_unit_coordinate (k : ℕ) (I J : P → Fin 17) (hIJ : I ≠ J) :
    ∃ i : P, IsUnit (((I i : ℕ) : ZMod (37 ^ k)) - ((J i : ℕ) : ZMod (37 ^ k))) := by
  classical
  have hi : ∃ i, I i ≠ J i := by
    by_contra h
    push Not at h
    exact hIJ (funext h)
  obtain ⟨i, hi⟩ := hi
  exact ⟨i, coarse_difference_isUnit k (I i) (J i) hi⟩

theorem shared_z_collision_iff (two : Rˣ) (htwo : (two : R) = 2)
    (U : Set R) (I I' J J' : P → R) (hIJ : I' + J' = I + J)
    (s : Sample P R) (hs : Survives U I J s) :
    Survives U I' J' s ↔ dot s.1 (I' - I) = 0 := by
  have hsum : dot s.1 I' + dot s.1 J' = dot s.1 I + dot s.1 J := by
    simpa using congrArg (dot s.1) hIJ
  rcases hs with ⟨heq, hU⟩
  rw [dot_sub_right]
  constructor
  · rintro ⟨heq', _⟩
    dsimp [xHash, yHash] at heq heq'
    have hz : (two : R) * (dot s.1 I' - dot s.1 I) = (two : R) * 0 := by
      rw [htwo]
      linear_combination heq' - heq + hsum
    exact two.isUnit.mul_left_cancel hz
  · intro hd
    have hx : xHash s I' = xHash s I := by
      dsimp [xHash]
      linear_combination hd
    have hy : yHash s J' = yHash s J := by
      dsimp [yHash]
      linear_combination hsum - hd
    exact ⟨hx.trans (heq.trans hy.symm), hx ▸ hU⟩

theorem shared_z_collision_card_mul [Fintype R]
    (two : Rˣ) (htwo : (two : R) = 2)
    (U : Finset R) (I I' J J' : P → R) (hIJ : I' + J' = I + J)
    (i : P) (u : Rˣ) (hu : I' i - I i = u) :
    Fintype.card R * Fintype.card {s : Sample P R //
      Survives (U : Set R) I J s ∧ Survives (U : Set R) I' J' s} =
      Fintype.card {s : Sample P R // Survives (U : Set R) I J s} := by
  classical
  let e : {s : Sample P R // Survives (U : Set R) I J s ∧
      Survives (U : Set R) I' J' s} ≃
      {s : Sample P R // Survives (U : Set R) I J s ∧ dot s.1 (I' - I) = 0} :=
    Equiv.subtypeEquivRight (fun s => and_congr_right (fun hs =>
      shared_z_collision_iff two htwo (U : Set R) I I' J J' hIJ s hs))
  rw [Fintype.card_congr e]
  exact collision_card_mul U I J (I' - I) i u hu

end MatrixMultiplication.JointHashing





noncomputable section

namespace MatrixMultiplication.JointCoarseHashing

attribute [local instance] Classical.propDecidable

variable {P : Type*}

theorem eq_of_shared_xy (S : P → ℕ) (e f : Triple P)
    (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hx : e.1 = f.1) (hy : e.2.1 = f.2.1) : e = f := by
  have hz : e.2.2 = f.2.2 := by
    funext p
    apply Fin.ext
    have he' := he p
    have hf' := hf p
    rw [hx, hy] at he'
    omega
  exact Prod.ext hx (Prod.ext hy hz)

theorem eq_of_shared_xz (S : P → ℕ) (e f : Triple P)
    (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hx : e.1 = f.1) (hz : e.2.2 = f.2.2) : e = f := by
  have hy : e.2.1 = f.2.1 := by
    funext p
    apply Fin.ext
    have he' := he p
    have hf' := hf p
    rw [hx, hz] at he'
    omega
  exact Prod.ext hx (Prod.ext hy hz)

theorem shared_z_cast_sum (k : ℕ) (S : P → ℕ) (e f : Triple P)
    (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hz : f.2.2 = e.2.2) :
    castWord k f.1 + castWord k f.2.1 = castWord k e.1 + castWord k e.2.1 := by
  have h := (supportSum_cast k S f hf).trans (supportSum_cast k S e he).symm
  rw [hz] at h
  exact add_right_cancel h

section FiniteHashing

variable [Fintype P]

theorem survival_card (k : ℕ) (U : Finset (ZMod (37 ^ k))) (e : Triple P) :
    Fintype.card {s : Sample P k // Survives k U e s} =
      (37 ^ k) ^ Fintype.card P * U.card := by
  have hcard := JointHashing.survival_card U (castWord k e.1) (castWord k e.2.1)
  simp only [ZMod.card] at hcard
  simp only [Fintype.card_eq_nat_card] at hcard ⊢
  exact hcard

theorem shared_x_card_mul (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e f : Triple P) (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hne : f ≠ e) (hx : f.1 = e.1) :
    (37 ^ k) * Fintype.card {s : Sample P k // Survives k U e s ∧ Survives k U f s} =
      Fintype.card {s : Sample P k // Survives k U e s} := by
  classical
  have hy : f.2.1 ≠ e.2.1 := fun hy => hne (eq_of_shared_xy S f e hf he hx hy)
  obtain ⟨i, hi⟩ := JointHashing.coarse_words_unit_coordinate k f.2.1 e.2.1 hy
  have h := JointHashing.shared_x_collision_card_mul U (castWord k e.1)
    (castWord k e.2.1) (castWord k f.2.1) i hi.unit hi.unit_spec.symm
  simp only [ZMod.card] at h
  simp only [Fintype.card_eq_nat_card] at h ⊢
  simpa only [Survives, hx] using h

theorem shared_y_card_mul (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e f : Triple P) (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hne : f ≠ e) (hy : f.2.1 = e.2.1) :
    (37 ^ k) * Fintype.card {s : Sample P k // Survives k U e s ∧ Survives k U f s} =
      Fintype.card {s : Sample P k // Survives k U e s} := by
  classical
  have hx : f.1 ≠ e.1 := fun hx => hne (eq_of_shared_xy S f e hf he hx hy)
  obtain ⟨i, hi⟩ := JointHashing.coarse_words_unit_coordinate k f.1 e.1 hx
  have h := JointHashing.shared_y_collision_card_mul U (castWord k e.1)
    (castWord k f.1) (castWord k e.2.1) i hi.unit hi.unit_spec.symm
  simp only [ZMod.card] at h
  simp only [Fintype.card_eq_nat_card] at h ⊢
  simpa only [Survives, hy] using h

theorem shared_z_card_mul (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e f : Triple P) (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hne : f ≠ e) (hz : f.2.2 = e.2.2) :
    (37 ^ k) * Fintype.card {s : Sample P k // Survives k U e s ∧ Survives k U f s} =
      Fintype.card {s : Sample P k // Survives k U e s} := by
  classical
  have hx : f.1 ≠ e.1 := fun hx => hne (eq_of_shared_xz S f e hf he hx hz)
  obtain ⟨i, hi⟩ := JointHashing.coarse_words_unit_coordinate k f.1 e.1 hx
  have h := JointHashing.shared_z_collision_card_mul (twoUnit k) (twoUnit_coe k)
    U (castWord k e.1) (castWord k f.1) (castWord k e.2.1) (castWord k f.2.1)
    (shared_z_cast_sum k S e f he hf hz) i hi.unit hi.unit_spec.symm
  simp only [ZMod.card] at h
  simp only [Fintype.card_eq_nat_card] at h ⊢
  exact h

theorem pair_survival_card_mul (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e f : Triple P) (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hne : f ≠ e) (hshare : SharesSide e f) :
    (37 ^ k) * Fintype.card {s : Sample P k // Survives k U e s ∧ Survives k U f s} =
      Fintype.card {s : Sample P k // Survives k U e s} := by
  rcases hshare with hx | hy | hz
  · exact shared_x_card_mul k U S e f he hf hne hx
  · exact shared_y_card_mul k U S e f he hf hne hy
  · exact shared_z_card_mul k U S e f he hf hne hz

theorem ownEvent_card (k : ℕ) (U : Finset (ZMod (37 ^ k))) (e : Triple P) :
    (ownEvent k U e).card = (37 ^ k) ^ Fintype.card P * U.card := by
  simpa only [ownEvent, Fintype.card_subtype] using survival_card k U e

theorem pair_event_card_mul (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e f : Triple P) (he : HasSupportSum S e) (hf : HasSupportSum S f)
    (hne : f ≠ e) (hshare : SharesSide e f) :
    (37 ^ k) * ((ownEvent k U e).filter (Survives k U f)).card = (ownEvent k U e).card := by
  simpa only [ownEvent, Finset.filter_filter, Fintype.card_subtype] using
    pair_survival_card_mul k U S e f he hf hne hshare

theorem competitor_union_card_mul_le (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e : Triple P) (he : HasSupportSum S e) (competitors : Finset (Triple P))
    (hf : ∀ f ∈ competitors, HasSupportSum S f)
    (hne : ∀ f ∈ competitors, f ≠ e)
    (hshare : ∀ f ∈ competitors, SharesSide e f) :
    (37 ^ k) * ((ownEvent k U e).filter
      (fun s => ∃ f ∈ competitors, Survives k U f s)).card ≤
        competitors.card * (ownEvent k U e).card := by
  apply JointLossCounts.competitor_union_card_mul_le
  intro f hf'
  exact (pair_event_card_mul k U S e f he (hf f hf') (hne f hf') (hshare f hf')).le

theorem competitor_union_card_le (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (S : P → ℕ) (e : Triple P) (he : HasSupportSum S e) (competitors : Finset (Triple P))
    (hf : ∀ f ∈ competitors, HasSupportSum S f)
    (hne : ∀ f ∈ competitors, f ≠ e)
    (hshare : ∀ f ∈ competitors, SharesSide e f) :
    (((ownEvent k U e).filter (fun s => ∃ f ∈ competitors, Survives k U f s)).card : ℝ) ≤
      ((competitors.card : ℝ) / ((37 ^ k : ℕ) : ℝ)) * ((ownEvent k U e).card : ℝ) := by
  have hM : (0 : ℝ) < ((37 ^ k : ℕ) : ℝ) := by
    exact_mod_cast (pow_pos (by decide : 0 < (37 : ℕ)) k)
  have h := competitor_union_card_mul_le k U S e he competitors hf hne hshare
  have hR : ((37 ^ k : ℕ) : ℝ) *
      (((ownEvent k U e).filter (fun s => ∃ f ∈ competitors, Survives k U f s)).card : ℝ) ≤
      (competitors.card : ℝ) * ((ownEvent k U e).card : ℝ) := by exact_mod_cast h
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hM).2 (by simpa only [mul_comm] using hR)

end FiniteHashing

end MatrixMultiplication.JointCoarseHashing






namespace MatrixMultiplication.JointOrdinarySelection

open JointCoarseHashing JointExtractionRates Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {P E : Type*}

section Finite

variable [Fintype P]

theorem ownEvent_card_real (k : ℕ) (U : Finset (ZMod (37 ^ k))) (e : Triple P) :
    ((ownEvent k U e).card : ℝ) =
      ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2) * (Fintype.card (Sample P k) : ℝ) := by
  rw [ownEvent_card, JointHashing.sample_card, ZMod.card]
  push_cast
  field_simp

end Finite

end MatrixMultiplication.JointOrdinarySelection






namespace MatrixMultiplication.JointMaskedSelection

open JointCoarseHashing JointExtractionRates

attribute [local instance] Classical.propDecidable

variable {P E O V : Type*}

namespace OrbitData

section Finite

variable [Fintype P]

theorem variableBad_card_le (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (e : E) (o : O) (ho : o ∈ d.orbits e)
    (v : V) (hv : v ∈ d.passing e o) (D : ℕ)
    (hdegree : (d.competitors e o v).card ≤ D) :
    (((ownEvent k U (d.coarse e)).filter (d.variableBad k U e o v)).card : ℝ) ≤
      ((D : ℝ) / ((37 ^ k : ℕ) : ℝ)) * ((ownEvent k U (d.coarse e)).card : ℝ) := by
  have h := competitor_union_card_le k U d.support (d.coarse e)
    (d.support_ambient _ (d.target_mem e)) (d.competitors e o v)
    (fun f hf => d.support_ambient f (d.competitor_mem e o ho v hv f hf))
    (d.competitor_ne e o ho v hv) (d.competitor_shares e o ho v hv)
  have hdegreeR : ((d.competitors e o v).card : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast hdegree
  have hfilter : (ownEvent k U (d.coarse e)).filter (d.variableBad k U e o v) =
      (ownEvent k U (d.coarse e)).filter
        (fun s => ∃ f ∈ d.competitors e o v, Survives k U f s) := by
    ext s
    simp only [Finset.mem_filter, variableBad]
  rw [hfilter]
  exact h.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hdegreeR (Nat.cast_nonneg _))
    (Nat.cast_nonneg _))

theorem eligibilityFailure_card_le (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (e : E) :
    (((ownEvent k U (d.coarse e)).filter (fun s => ¬ d.eligibilityGood k U e s)).card : ℝ) ≤
      (((d.eligibilityCompetitors e).card : ℝ) / ((37 ^ k : ℕ) : ℝ)) *
        ((ownEvent k U (d.coarse e)).card : ℝ) := by
  have h := competitor_union_card_le k U d.support (d.coarse e)
    (d.support_ambient _ (d.target_mem e)) (d.eligibilityCompetitors e)
    (fun f hf => d.support_ambient f ((d.mem_eligibilityCompetitors e f).1 hf).1)
    (fun f hf => ((d.mem_eligibilityCompetitors e f).1 hf).2.1)
    (fun f hf => Or.inl ((d.mem_eligibilityCompetitors e f).1 hf).2.2)
  simpa only [eligibilityGood, not_not] using h

theorem failure_card_le (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (N : ℝ) (hN : 0 < N) (e : E) (D : ℕ)
    (hdegree : ∀ o ∈ d.orbits e, ∀ v ∈ d.passing e o, (d.competitors e o v).card ≤ D) :
    (((ownEvent k U (d.coarse e)).filter (d.Failure k U N e)).card : ℝ) ≤
      (((d.eligibilityCompetitors e).card : ℝ) / ((37 ^ k : ℕ) : ℝ) +
        ((d.orbits e).card : ℝ) * N * ((D : ℝ) / ((37 ^ k : ℕ) : ℝ))) *
          ((ownEvent k U (d.coarse e)).card : ℝ) := by
  exact JointLossCounts.targetBad_card_le (ownEvent k U (d.coarse e))
    (d.orbits e) (d.full e) (d.passing e) (d.variableBad k U e)
    (d.eligibilityGood k U e) ((D : ℝ) / ((37 ^ k : ℕ) : ℝ))
    (((d.eligibilityCompetitors e).card : ℝ) / ((37 ^ k : ℕ) : ℝ)) N
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hN (d.full_pos e)
    (d.passing_subset e)
    (fun o ho v hv => d.variableBad_card_le k U e o ho v hv D (hdegree o ho v hv))
    (d.eligibilityFailure_card_le k U e)

theorem ownEvent_card_real (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (e : E) :
    ((ownEvent k U (d.coarse e)).card : ℝ) =
      ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2) * (Fintype.card (Sample P k) : ℝ) := by
  exact JointOrdinarySelection.ownEvent_card_real k U (d.coarse e)

theorem goodEvent_card_lower_oai (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (N : ℝ) (hN : 0 < N) (e : E) (D : ℕ)
    (hdegree : ∀ o ∈ d.orbits e, ∀ v ∈ d.passing e o, (d.competitors e o v).card ≤ D)
    (hsmall : ((d.eligibilityCompetitors e).card : ℝ) / ((37 ^ k : ℕ) : ℝ) +
      ((d.orbits e).card : ℝ) * N * ((D : ℝ) / ((37 ^ k : ℕ) : ℝ)) ≤ 1 / 2) :
    ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2 / 2) *
      (Fintype.card (Sample P k) : ℝ) ≤ (d.goodEvent k U N e).card := by
  have hb : (((ownEvent k U (d.coarse e)).filter (d.Failure k U N e)).card : ℝ) ≤
      (1 / 2) * ((ownEvent k U (d.coarse e)).card : ℝ) :=
    (d.failure_card_le k U N hN e D hdegree).trans
      (mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg _))
  have hg := JointLossCounts.good_card_lower (ownEvent k U (d.coarse e))
    (d.Failure k U N e) (1 / 2) hb
  rw [d.ownEvent_card_real] at hg
  change _ ≤ ((d.goodEvent k U N e).card : ℝ) at hg
  convert hg using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Finite

end OrbitData

end MatrixMultiplication.JointMaskedSelection

end
end

end MatrixAllFields

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.MatrixAllFields.MatrixMultiplication.JointMaskedSelection.OrbitData.goodEvent_card_lower_oai.{u_1, u_2, u_3, u_4} := @OAI.MatrixAllFields.MatrixMultiplication.JointMaskedSelection.OrbitData.goodEvent_card_lower_oai.{u_1, u_2, u_3, u_4}
