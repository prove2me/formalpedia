-- Prove2me | solution 1 for KallenbergLP.OptTransient.extreme_optimal_yields_pure_policy
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:06:41.027545+00:00
-- url     : https://prove2.me/submissions/fbbfb3de-d803-48bf-bac8-375ca59a172c

import Mathlib
import Definitions.Def_KallenbergLP_OptTransient_LinearProgram

open Classical

namespace KallenbergLP.OptTransient

open Matrix

/-! ## Matrix lemmas -/

lemma kot_pow_nonneg {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : ∀ i j, 0 ≤ P i j) :
    ∀ t i j, 0 ≤ (P ^ t) i j := by
  intro t
  induction t with
  | zero => intro i j; simp only [pow_zero, one_apply]; split_ifs <;> norm_num
  | succ t ih =>
    intro i j
    rw [pow_succ, mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (ih i k) (hP k j)

lemma kot_inv_eq {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hs : ∀ i j, Summable (fun t : ℕ => (P ^ t) i j)) :
    (1 - P)⁻¹ = Matrix.of (fun i j => ∑' t : ℕ, (P ^ t) i j) ∧
      (1 - P)⁻¹ * (1 - P) = 1 ∧ (1 - P) * (1 - P)⁻¹ = 1 := by
  have hleft : Matrix.of (fun i j => ∑' t : ℕ, (P ^ t) i j) * (1 - P) = 1 := by
    ext i j
    rw [mul_sub, mul_one, Matrix.sub_apply, Matrix.mul_apply]
    simp only [Matrix.of_apply]
    have e1 : ∑ k, (∑' t : ℕ, (P ^ t) i k) * P k j = ∑' t : ℕ, (P ^ (t + 1)) i j := by
      have : ∀ k, (∑' t : ℕ, (P ^ t) i k) * P k j = ∑' t : ℕ, (P ^ t) i k * P k j :=
        fun k => ((hs i k).tsum_mul_right (P k j)).symm
      simp_rw [this]
      rw [← Summable.tsum_finsetSum (fun k _ => (hs i k).mul_right (P k j))]
      congr 1
    rw [e1, (hs i j).tsum_eq_zero_add, pow_zero]
    ring
  have hinv : (1 - P)⁻¹ = Matrix.of (fun i j => ∑' t : ℕ, (P ^ t) i j) := Matrix.inv_eq_left_inv hleft
  have hdet : IsUnit (1 - P).det := Matrix.isUnit_det_of_left_inverse hleft
  refine ⟨hinv, ?_, ?_⟩
  · rw [hinv]; exact hleft
  · exact Matrix.mul_nonsing_inv _ hdet

lemma kot_inv_apply {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hs : ∀ i j, Summable (fun t : ℕ => (P ^ t) i j)) (i j : Fin n) :
    ((1 - P)⁻¹) i j = ∑' t : ℕ, (P ^ t) i j := by
  rw [(kot_inv_eq P hs).1, Matrix.of_apply]

lemma kot_inv_ge {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hs : ∀ i j, Summable (fun t : ℕ => (P ^ t) i j)) (i j : Fin n) :
    0 ≤ ((1 - P)⁻¹) i j ∧ (1 : Matrix (Fin n) (Fin n) ℝ) i j ≤ ((1 - P)⁻¹) i j := by
  rw [kot_inv_apply P hs]
  refine ⟨tsum_nonneg fun t => kot_pow_nonneg P hP t i j, ?_⟩
  have := (hs i j).le_tsum 0 (fun t _ => kot_pow_nonneg P hP t i j)
  simpa using this

/-- If `y (1 - P) = β` with `y ≥ 0` and `β > 0`, then powers of `P` are summable. -/
lemma kot_summable_of_sol {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (y β : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i) (hβ : ∀ i, 0 < β i)
    (hsol : vecMul y (1 - P) = β) :
    ∀ i j, Summable (fun t : ℕ => (P ^ t) i j) := by
  have hy' : y = β + vecMul y P := by
    rw [← hsol, Matrix.vecMul_sub, Matrix.vecMul_one]; abel
  have key : ∀ T : ℕ, y = (∑ t ∈ Finset.range T, vecMul β (P ^ t)) + vecMul y (P ^ T) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [Finset.sum_range_succ]
      conv_lhs => rw [ih]
      conv_lhs => rw [hy']
      rw [Matrix.add_vecMul, Matrix.vecMul_vecMul, ← pow_succ']
      abel
  intro i j
  have hnn := kot_pow_nonneg P hP
  apply summable_of_sum_range_le (c := y j / β i) (fun t => hnn t i j)
  intro T
  have h1 := congrFun (key T) j
  have h2 : 0 ≤ vecMul y (P ^ T) j := by
    simp only [vecMul, dotProduct]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hy k) (hnn T k j)
  have h3 : ∀ t, β i * (P ^ t) i j ≤ vecMul β (P ^ t) j := by
    intro t
    simp only [vecMul, dotProduct]
    exact Finset.single_le_sum (f := fun k => β k * (P ^ t) k j)
      (fun k _ => mul_nonneg (hβ k).le (hnn t k j)) (Finset.mem_univ i)
  have h4 : β i * ∑ t ∈ Finset.range T, (P ^ t) i j ≤ y j := by
    rw [Finset.mul_sum]
    have : ∑ t ∈ Finset.range T, β i * (P ^ t) i j ≤
        ∑ t ∈ Finset.range T, vecMul β (P ^ t) j := Finset.sum_le_sum fun t _ => h3 t
    rw [h1, Pi.add_apply, Finset.sum_apply]
    linarith
  rw [le_div_iff₀ (hβ i)]
  linarith


/-! ## Stationary policies -/

section MDP
variable {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]

lemma kot_rowsum (m : FiniteSubstochasticMDP n α) (π : StationaryRule n α)
    (hπ : IsStationaryRule m π) (k : Fin n) (g : α → ℝ) :
    ∑ a, π k a * g a = ∑ a ∈ m.actions k, π k a * g a := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha
  rw [(hπ k).2.1 a ha, zero_mul]

lemma kot_hist_sum (m : FiniteSubstochasticMDP n α) (π : StationaryRule n α)
    (hπ : IsStationaryRule m π) (i : Fin n) :
    ∀ t j, ∑ h : Fin t → (Fin n × α), historyMass m (stationaryPolicy π) i (List.ofFn h) j
      = (transitionMatrix m π ^ t) i j := by
  intro t
  induction t with
  | zero => intro j; simp [historyMass, Matrix.one_apply, eq_comm]
  | succ t ih =>
    intro j
    rw [← (Fin.consEquiv (fun _ : Fin (t + 1) => Fin n × α)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
    simp only [historyMass, stationaryPolicy]
    have e : ∀ x : Fin n × α, ∑ h : Fin t → (Fin n × α),
        historyMass m (stationaryPolicy π) i (List.ofFn fun k => h k) x.1 * π x.1 x.2 *
          m.transition x.1 x.2 j = (transitionMatrix m π ^ t) i x.1 * (π x.1 x.2 *
          m.transition x.1 x.2 j) := by
      intro x
      rw [← Finset.sum_mul, ← Finset.sum_mul, mul_assoc]
      congr 1
      exact ih x.1
    rw [Fintype.sum_congr _ _ e, Fintype.sum_prod_type, pow_succ, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    show ∑ y : α, (transitionMatrix m π ^ t) i k * (π k y * m.transition k y j) = _
    rw [← Finset.mul_sum, kot_rowsum m π hπ k (fun y => m.transition k y j)]
    unfold transitionMatrix
    congr 1
    exact Finset.sum_congr rfl fun a _ => by ring

lemma kot_jointAt (m : FiniteSubstochasticMDP n α) (π : StationaryRule n α)
    (hπ : IsStationaryRule m π) (i : Fin n) (t : ℕ) (j : Fin n) (a : α) :
    jointAt m (stationaryPolicy π) i t j a = (transitionMatrix m π ^ t) i j * π j a := by
  unfold jointAt
  rw [← kot_hist_sum m π hπ i t j, Finset.sum_mul]
  rfl

lemma kot_stateAt (m : FiniteSubstochasticMDP n α) (π : StationaryRule n α)
    (hπ : IsStationaryRule m π) (i : Fin n) (t : ℕ) (j : Fin n) :
    stateAt m (stationaryPolicy π) i t j = (transitionMatrix m π ^ t) i j := by
  unfold stateAt
  simp_rw [kot_jointAt m π hπ]
  rw [← Finset.mul_sum, (hπ j).2.2, mul_one]

lemma kot_transient_iff (m : FiniteSubstochasticMDP n α) (π : StationaryRule n α)
    (hπ : IsStationaryRule m π) :
    IsTransient m (stationaryPolicy π) ↔
      ∀ i j, Summable (fun t : ℕ => (transitionMatrix m π ^ t) i j) := by
  unfold IsTransient
  simp_rw [kot_stateAt m π hπ]

lemma kot_P_nonneg (m : FiniteSubstochasticMDP n α) (π : StationaryRule n α)
    (hπ : IsStationaryRule m π) (i j : Fin n) : 0 ≤ transitionMatrix m π i j :=
  Finset.sum_nonneg fun a ha => mul_nonneg (m.transition_nonneg i a j ha) ((hπ i).1 a)

end MDP


/-! ## Occupations -/

section LP
variable {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]

/-- occupation from state masses and a rule -/
def kotOcc (m : FiniteSubstochasticMDP n α) (y : Fin n → ℝ) (π : StationaryRule n α) :
    StateAction m → ℝ := fun s => y s.1 * π s.1 s.2.1

lemma kot_flow (m : FiniteSubstochasticMDP n α) (π : StationaryRule n α)
    (hπ : IsStationaryRule m π) (y : Fin n → ℝ) (j : Fin n) :
    (∑ s : StateAction m, ((if s.1 = j then (1 : ℝ) else 0) - m.transition s.1 s.2.1 j) *
      kotOcc m y π s) = y j - vecMul y (transitionMatrix m π) j := by
  rw [Fintype.sum_sigma]
  have h : ∀ i, (∑ a : {a : α // a ∈ m.actions i},
      ((if i = j then (1 : ℝ) else 0) - m.transition i a.1 j) * (y i * π i a.1)) =
      (if i = j then y i else 0) - y i * transitionMatrix m π i j := by
    intro i
    rw [Finset.sum_coe_sort (m.actions i)
      (fun a => ((if i = j then (1 : ℝ) else 0) - m.transition i a j) * (y i * π i a))]
    unfold transitionMatrix
    have h1 : ∑ a ∈ m.actions i, π i a = 1 := (hπ i).2.2
    rw [Finset.sum_congr rfl (fun a _ => (show ((if i = j then (1 : ℝ) else 0) - m.transition i a j) *
      (y i * π i a) = (if i = j then (1 : ℝ) else 0) * y i * π i a - y i * (m.transition i a j * π i a)
      by ring)), Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1]
    split_ifs <;> ring
  refine (Finset.sum_congr rfl fun i _ => h i).trans ?_
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ j, if_pos (Finset.mem_univ _)]
  rfl

lemma kot_stateMass_occ (m : FiniteSubstochasticMDP n α) (π : StationaryRule n α)
    (hπ : IsStationaryRule m π) (y : Fin n → ℝ) (i : Fin n) :
    stateMass m (kotOcc m y π) i = y i := by
  unfold stateMass kotOcc
  rw [Finset.sum_coe_sort (m.actions i) (fun a => y i * π i a), ← Finset.mul_sum, (hπ i).2.2,
    mul_one]

lemma kot_occ_feasible (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ) (π : StationaryRule n α)
    (hπ : IsStationaryRule m π) (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hsol : vecMul y (1 - transitionMatrix m π) = β) : IsFeasible m β (kotOcc m y π) := by
  refine ⟨fun s => mul_nonneg (hy _) ((hπ _).1 _), fun j => ?_⟩
  rw [kot_flow m π hπ y j, ← hsol, Matrix.vecMul_sub, Matrix.vecMul_one]
  rfl

lemma kot_flow_split (m : FiniteSubstochasticMDP n α) (x : StateAction m → ℝ) (j : Fin n) :
    (∑ s : StateAction m, ((if s.1 = j then (1 : ℝ) else 0) - m.transition s.1 s.2.1 j) * x s) =
      stateMass m x j - ∑ s : StateAction m, m.transition s.1 s.2.1 j * x s := by
  simp only [sub_mul, Finset.sum_sub_distrib]
  congr 1
  rw [Fintype.sum_sigma]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single j]
  · simp only [if_true]; rfl
  · intro i _ hij; simp [hij]
  · intro h; exact absurd (Finset.mem_univ j) h


lemma kot_mass_ge (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ) (x : StateAction m → ℝ)
    (hx : IsFeasible m β x) (j : Fin n) : β j ≤ stateMass m x j := by
  have h := hx.2 j
  rw [kot_flow_split] at h
  have : 0 ≤ ∑ s : StateAction m, m.transition s.1 s.2.1 j * x s :=
    Finset.sum_nonneg fun s _ => mul_nonneg (m.transition_nonneg _ _ _ s.2.2) (hx.1 s)
  linarith

lemma kot_statOcc_eq (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ) (π : StationaryRule n α) :
    stationaryOccupation m β π = kotOcc m (vecMul β ((1 - transitionMatrix m π)⁻¹)) π := by
  funext s
  rfl

lemma kot_partA (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ) (hβ : ∀ i, 0 < β i)
    (π : StationaryRule n α) (hπ : IsStationaryRule m π)
    (ht : IsTransient m (stationaryPolicy π)) :
    IsFeasible m β (stationaryOccupation m β π) ∧
      ∀ i, β i ≤ vecMul β ((1 - transitionMatrix m π)⁻¹) i := by
  have hs := (kot_transient_iff m π hπ).1 ht
  have hP := kot_P_nonneg m π hπ
  have hge := kot_inv_ge _ hP hs
  have hy : ∀ i, β i ≤ vecMul β ((1 - transitionMatrix m π)⁻¹) i := by
    intro i
    simp only [vecMul, dotProduct]
    calc β i ≤ β i * ((1 - transitionMatrix m π)⁻¹) i i := by
          have := (hge i i).2; rw [Matrix.one_apply_eq] at this
          nlinarith [hβ i]
      _ ≤ _ := Finset.single_le_sum (f := fun k => β k * ((1 - transitionMatrix m π)⁻¹) k i)
          (fun k _ => mul_nonneg (hβ k).le (hge k i).1) (Finset.mem_univ i)
  refine ⟨?_, hy⟩
  rw [kot_statOcc_eq]
  apply kot_occ_feasible m β π hπ _ (fun i => le_trans (hβ i).le (hy i))
  rw [Matrix.vecMul_vecMul, (kot_inv_eq _ hs).2.1, Matrix.vecMul_one]

lemma kot_part2 (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ) (hβ : ∀ i, 0 < β i)
    (x : StateAction m → ℝ) (hx : IsFeasible m β x) :
    IsStationaryRule m (ruleOfOccupation m x) ∧
      IsTransient m (stationaryPolicy (ruleOfOccupation m x)) ∧
      stationaryOccupation m β (ruleOfOccupation m x) = x := by
  set y := stateMass m x with hydef
  have hypos : ∀ i, 0 < y i := fun i => lt_of_lt_of_le (hβ i) (kot_mass_ge m β x hx i)
  set π := ruleOfOccupation m x with hπdef
  have hπ : IsStationaryRule m π := by
    intro i
    refine ⟨fun a => ?_, fun a ha => ?_, ?_⟩
    · simp only [hπdef, ruleOfOccupation]
      split_ifs
      · exact div_nonneg (hx.1 _) (hypos i).le
      · exact le_rfl
    · simp only [hπdef, ruleOfOccupation, dif_neg ha]
    · rw [← Finset.sum_coe_sort]
      simp only [hπdef, ruleOfOccupation]
      rw [Finset.sum_congr rfl (fun (a : {a : α // a ∈ m.actions i}) _ =>
        dif_pos a.2), ← Finset.sum_div]
      exact div_self (hypos i).ne'
  have hxeq : x = kotOcc m y π := by
    funext s
    simp only [kotOcc, hπdef, ruleOfOccupation, dif_pos s.2.2]
    rw [mul_div_cancel₀ _ (hypos s.1).ne']
  have hsol : vecMul y (1 - transitionMatrix m π) = β := by
    funext j
    have h := hx.2 j
    rw [hxeq, kot_flow m π hπ y j] at h
    rw [Matrix.vecMul_sub, Matrix.vecMul_one]
    exact h
  have hs := kot_summable_of_sol _ (kot_P_nonneg m π hπ) y β (fun i => (hypos i).le) hβ hsol
  refine ⟨hπ, (kot_transient_iff m π hπ).2 hs, ?_⟩
  rw [kot_statOcc_eq, ← hsol, Matrix.vecMul_vecMul, (kot_inv_eq _ hs).2.2, Matrix.vecMul_one,
    ← hxeq]

lemma kot_part3 (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ) (hβ : ∀ i, 0 < β i)
    (π : StationaryRule n α) (hπ : IsStationaryRule m π)
    (ht : IsTransient m (stationaryPolicy π)) :
    ruleOfOccupation m (stationaryOccupation m β π) = π := by
  obtain ⟨_, hy⟩ := kot_partA m β hβ π hπ ht
  funext i a
  rw [kot_statOcc_eq]
  simp only [ruleOfOccupation]
  split_ifs with ha
  · rw [kot_stateMass_occ m π hπ]
    simp only [kotOcc]
    have := lt_of_lt_of_le (hβ i) (hy i)
    field_simp
  · exact ((hπ i).2.1 a ha).symm


/-- the constraint coefficients -/
def kotC (m : FiniteSubstochasticMDP n α) (s : StateAction m) (j : Fin n) : ℝ :=
  (if s.1 = j then (1 : ℝ) else 0) - m.transition s.1 s.2.1 j

noncomputable def kotExt (m : FiniteSubstochasticMDP n α) (x : StateAction m → ℝ)
    (d : {s : StateAction m // 0 < x s} → ℝ) : StateAction m → ℝ :=
  fun s => if h : 0 < x s then d ⟨s, h⟩ else 0

noncomputable def kotL (m : FiniteSubstochasticMDP n α) (x : StateAction m → ℝ) :
    ({s : StateAction m // 0 < x s} → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun d j := ∑ s : StateAction m, kotC m s j * kotExt m x d s
  map_add' d d' := by
    funext j
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [kotExt]; split_ifs <;> simp [mul_add]
  map_smul' c d := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [kotExt]; split_ifs <;> simp; ring

lemma kot_extreme_card (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ) (x : StateAction m → ℝ)
    (hx : x ∈ (feasibleSet m β).extremePoints ℝ) :
    Fintype.card {s : StateAction m // 0 < x s} ≤ n := by
  by_contra hcard
  push_neg at hcard
  obtain ⟨hxP, hext⟩ := mem_extremePoints.1 hx
  have hxP' : IsFeasible m β x := hxP
  have hker : LinearMap.ker (kotL m x) ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    exact hcard
  obtain ⟨d, hdk, hd0⟩ := (Submodule.ne_bot_iff _).1 hker
  set D := kotExt m x d with hD
  have hDz : ∀ s, ¬ 0 < x s → D s = 0 := by
    intro s h; simp only [hD, kotExt, dif_neg h]
  have hD0 : D ≠ 0 := by
    intro h
    apply hd0
    funext s
    have := congrFun h s.1
    simp only [hD, kotExt, dif_pos s.2, Pi.zero_apply] at this
    simpa using this
  have hND : ∀ j, ∑ s : StateAction m, kotC m s j * D s = 0 := by
    intro j
    have := congrFun (LinearMap.mem_ker.1 hdk) j
    simpa [kotL] using this
  set K := ∑ s, |D s| / x s with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun s _ => div_nonneg (abs_nonneg _) (hxP'.1 s)
  set ε := 1 / (1 + K) with hε
  have hεpos : 0 < ε := by positivity
  have hεle : ∀ s, ε * |D s| ≤ x s := by
    intro s
    by_cases hp : 0 < x s
    · have h1 : |D s| / x s ≤ K :=
        Finset.single_le_sum (f := fun s => |D s| / x s)
          (fun s _ => div_nonneg (abs_nonneg _) (hxP'.1 s)) (Finset.mem_univ s)
      have h2 : |D s| ≤ x s * K := by
        rw [div_le_iff₀ hp] at h1; linarith
      rw [hε, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      nlinarith
    · rw [hDz s hp, abs_zero, mul_zero]; exact hxP'.1 s
  have hmem : ∀ r : ℝ, |r| ≤ ε → x + r • D ∈ feasibleSet m β := by
    intro r hr
    refine ⟨fun s => ?_, fun j => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1 := hεle s
      have h2 : |r * D s| ≤ ε * |D s| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right hr (abs_nonneg _)
      have h3 := neg_abs_le (r * D s)
      linarith
    · have h := hxP'.2 j
      have h2 := hND j
      simp only [kotC] at h2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
      rw [h]
      have : ∑ s : StateAction m, ((if s.1 = j then (1 : ℝ) else 0) - m.transition s.1 s.2.1 j) *
          (r * D s) = r * ∑ s : StateAction m,
          ((if s.1 = j then (1 : ℝ) else 0) - m.transition s.1 s.2.1 j) * D s := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
      rw [this, h2, mul_zero, add_zero]
  have hplus := hmem ε (by rw [abs_of_pos hεpos])
  have hminus := hmem (-ε) (by rw [abs_neg, abs_of_pos hεpos])
  have hseg : x ∈ openSegment ℝ (x + ε • D) (x + (-ε) • D) :=
    ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by
      funext s; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring⟩
  have := (hext _ hplus _ hminus hseg).1
  have h2 : ε • D = 0 := by
    have := congrArg (fun z => z - x) this
    simpa using this
  rcases smul_eq_zero.1 h2 with h | h
  · exact hεpos.ne' h
  · exact hD0 h


lemma kot_part4 (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ) (hβ : ∀ i, 0 < β i)
    (π : StationaryRule n α) (hπ : IsStationaryRule m π)
    (ht : IsTransient m (stationaryPolicy π)) :
    stationaryOccupation m β π ∈ (feasibleSet m β).extremePoints ℝ ↔ IsPureRule m π := by
  obtain ⟨hfeas, hy⟩ := kot_partA m β hβ π hπ ht
  set y := vecMul β ((1 - transitionMatrix m π)⁻¹) with hydef
  have hypos : ∀ i, 0 < y i := fun i => lt_of_lt_of_le (hβ i) (hy i)
  have hxe : stationaryOccupation m β π = kotOcc m y π := kot_statOcc_eq m β π
  have hposiff : ∀ s : StateAction m, 0 < stationaryOccupation m β π s ↔ 0 < π s.1 s.2.1 := by
    intro s
    rw [hxe]; simp only [kotOcc]
    constructor
    · intro h; exact pos_of_mul_pos_right h (hypos _).le
    · intro h; exact mul_pos (hypos _) h
  constructor
  · intro hext
    have hcard := kot_extreme_card m β _ hext
    set x := stationaryOccupation m β π
    let g : {s : StateAction m // 0 < x s} → Fin n := fun s => s.1.1
    have hex1 : ∀ i, ∃ a : {a : α // a ∈ m.actions i}, 0 < π i a.1 := by
      intro i
      by_contra hc
      push_neg at hc
      have h1 := (hπ i).2.2
      have : ∑ a ∈ m.actions i, π i a ≤ 0 := Finset.sum_nonpos fun a ha => hc ⟨a, ha⟩
      linarith
    have hsurj : Function.Surjective g := by
      intro i
      obtain ⟨a, ha⟩ := hex1 i
      exact ⟨⟨⟨i, a⟩, (hposiff _).2 ha⟩, rfl⟩
    have hbij : Function.Bijective g := by
      rw [Fintype.bijective_iff_surjective_and_card]
      refine ⟨hsurj, ?_⟩
      rw [Fintype.card_fin]
      exact le_antisymm hcard (by simpa using Fintype.card_le_of_surjective g hsurj)
    let f : (i : Fin n) → {a : α // a ∈ m.actions i} := fun i => (hex1 i).choose
    have hf : ∀ i, 0 < π i (f i).1 := fun i => (hex1 i).choose_spec
    have huniq : ∀ i (a : α) (ha : a ∈ m.actions i), 0 < π i a → a = (f i).1 := by
      intro i a ha hpa
      have e := hbij.1 (a₁ := ⟨⟨i, ⟨a, ha⟩⟩, (hposiff _).2 hpa⟩)
        (a₂ := ⟨⟨i, f i⟩, (hposiff _).2 (hf i)⟩) rfl
      have := congrArg (fun s => s.1.2.1) e
      simpa using this
    refine ⟨f, fun i a => ?_⟩
    have hzero : ∀ b ∈ m.actions i, b ≠ (f i).1 → π i b = 0 := by
      intro b hb hne
      rcases ((hπ i).1 b).lt_or_eq with h | h
      · exact absurd (huniq i b hb h) hne
      · exact h.symm
    split_ifs with hab
    · subst hab
      have h1 := (hπ i).2.2
      rwa [Finset.sum_eq_single_of_mem _ (f i).2 hzero] at h1
    · by_cases ha : a ∈ m.actions i
      · exact hzero a ha hab
      · exact (hπ i).2.1 a ha
  · rintro ⟨f, hf⟩
    refine mem_extremePoints.2 ⟨hfeas, ?_⟩
    have key : ∀ z, IsFeasible m β z →
        (∀ s : StateAction m, stationaryOccupation m β π s = 0 → z s = 0) →
        z = stationaryOccupation m β π := by
      intro z hz hz0
      have hzero : ∀ (i : Fin n) (a : α) (ha : a ∈ m.actions i), a ≠ (f i).1 → z ⟨i, ⟨a, ha⟩⟩ = 0 := by
        intro i a ha hne
        apply hz0
        rw [hxe]; simp only [kotOcc, hf, if_neg hne, mul_zero]
      have hmass : ∀ i, stateMass m z i = z ⟨i, f i⟩ := by
        intro i
        unfold stateMass
        rw [Finset.sum_eq_single (f i)]
        · intro b _ hb
          exact hzero i b.1 b.2 (fun h => hb (Subtype.ext h))
        · intro h; exact absurd (Finset.mem_univ _) h
      have hrule : ruleOfOccupation m z = π := by
        funext i a
        have hmpos := lt_of_lt_of_le (hβ i) (kot_mass_ge m β z hz i)
        simp only [ruleOfOccupation, hf]
        split_ifs with ha hab hab
        · subst hab; rw [← hmass]; exact div_self hmpos.ne'
        · rw [hzero i a ha hab, zero_div]
        · exact absurd (hab ▸ (f i).2) ha
        · rfl
      have := (kot_part2 m β hβ z hz).2.2
      rw [hrule] at this
      exact this.symm
    intro z1 hz1 z2 hz2 hseg
    obtain ⟨a, b, ha, hb, hab, hxab⟩ := hseg
    have hz1' : IsFeasible m β z1 := hz1
    have hz2' : IsFeasible m β z2 := hz2
    have hvan : ∀ s, stationaryOccupation m β π s = 0 → z1 s = 0 ∧ z2 s = 0 := by
      intro s hs
      have e := congrFun hxab s
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e
      rw [hs] at e
      have h1 := hz1'.1 s
      have h2 := hz2'.1 s
      constructor <;> nlinarith [mul_nonneg ha.le h1, mul_nonneg hb.le h2]
    exact ⟨key z1 hz1' fun s hs => (hvan s hs).1, key z2 hz2' fun s hs => (hvan s hs).2⟩

theorem stationary_lp_correspondence_core {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ)
    (hex : ∃ R : Policy n α, IsPolicy m R ∧ IsTransient m R)
    (hβ : ∀ i, 0 < β i) :
    (∀ π : StationaryRule n α,
      IsStationaryRule m π → IsTransient m (stationaryPolicy π) →
      IsFeasible m β (stationaryOccupation m β π)) ∧
    (∀ x : StateAction m → ℝ, IsFeasible m β x →
      IsStationaryRule m (ruleOfOccupation m x) ∧
      IsTransient m (stationaryPolicy (ruleOfOccupation m x)) ∧
      stationaryOccupation m β (ruleOfOccupation m x) = x) ∧
    (∀ π : StationaryRule n α,
      IsStationaryRule m π → IsTransient m (stationaryPolicy π) →
      ruleOfOccupation m (stationaryOccupation m β π) = π) ∧
    (∀ π : StationaryRule n α,
      IsStationaryRule m π → IsTransient m (stationaryPolicy π) →
      (stationaryOccupation m β π ∈ (feasibleSet m β).extremePoints ℝ ↔
       IsPureRule m π)) :=
  ⟨fun π hπ ht => (kot_partA m β hβ π hπ ht).1, fun x hx => kot_part2 m β hβ x hx,
    fun π hπ ht => kot_part3 m β hβ π hπ ht, fun π hπ ht => kot_part4 m β hβ π hπ ht⟩

end LP


/-! ## General policies -/

section Gen
variable {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]

lemma kot_hm_nonneg (m : FiniteSubstochasticMDP n α) (S : Policy n α) (hS : IsPolicy m S)
    (i : Fin n) : ∀ (L : List (Fin n × α)) (j : Fin n), 0 ≤ historyMass m S i L j := by
  intro L
  induction L with
  | nil => intro j; simp only [historyMass]; split_ifs <;> norm_num
  | cons s h ih =>
    intro j
    simp only [historyMass]
    by_cases ha : s.2 ∈ m.actions s.1
    · exact mul_nonneg (mul_nonneg (ih _) ((hS _ _ _).1 _)) (m.transition_nonneg _ _ _ ha)
    · rw [(hS _ _ _).2.1 _ ha]; simp

lemma kot_joint_nonneg (m : FiniteSubstochasticMDP n α) (S : Policy n α) (hS : IsPolicy m S)
    (i : Fin n) (t : ℕ) (j : Fin n) (a : α) : 0 ≤ jointAt m S i t j a :=
  Finset.sum_nonneg fun h _ => mul_nonneg (kot_hm_nonneg m S hS i _ _) ((hS _ _ _).1 _)

lemma kot_joint_out (m : FiniteSubstochasticMDP n α) (S : Policy n α) (hS : IsPolicy m S)
    (i : Fin n) (t : ℕ) (j : Fin n) (a : α) (ha : a ∉ m.actions j) : jointAt m S i t j a = 0 :=
  Finset.sum_eq_zero fun h _ => by rw [(hS _ _ _).2.1 _ ha, mul_zero]

lemma kot_stateAt_zero (m : FiniteSubstochasticMDP n α) (S : Policy n α) (hS : IsPolicy m S)
    (i j : Fin n) : stateAt m S i 0 j = if j = i then 1 else 0 := by
  unfold stateAt jointAt
  simp only [Finset.univ_unique, Finset.sum_singleton, List.ofFn_zero, historyMass]
  rw [← Finset.mul_sum, (hS _ _ _).2.2, mul_one]

lemma kot_stateAt_sum (m : FiniteSubstochasticMDP n α) (S : Policy n α) (hS : IsPolicy m S)
    (i : Fin n) (t : ℕ) (j : Fin n) :
    stateAt m S i t j = ∑ h : Fin t → (Fin n × α), historyMass m S i (List.ofFn h) j := by
  unfold stateAt jointAt
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← Finset.mul_sum, (hS _ _ _).2.2, mul_one]

lemma kot_sum_sa (m : FiniteSubstochasticMDP n α) (g : Fin n → α → ℝ)
    (hg : ∀ k a, a ∉ m.actions k → g k a = 0) :
    ∑ x : Fin n × α, g x.1 x.2 = ∑ s : StateAction m, g s.1 s.2.1 := by
  rw [Fintype.sum_prod_type, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_coe_sort (m.actions k) (fun a => g k a)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha; exact hg k a ha

lemma kot_stateAt_succ (m : FiniteSubstochasticMDP n α) (S : Policy n α) (hS : IsPolicy m S)
    (i : Fin n) (t : ℕ) (j : Fin n) :
    stateAt m S i (t + 1) j =
      ∑ s : StateAction m, jointAt m S i t s.1 s.2.1 * m.transition s.1 s.2.1 j := by
  rw [kot_stateAt_sum m S hS]
  rw [← (Fin.consEquiv (fun _ : Fin (t + 1) => Fin n × α)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
  simp only [historyMass, List.length_ofFn]
  rw [← kot_sum_sa m (fun k a => jointAt m S i t k a * m.transition k a j)
    (fun k a ha => by rw [kot_joint_out m S hS i t k a ha, zero_mul])]
  refine Fintype.sum_congr _ _ fun x => ?_
  unfold jointAt
  rw [Finset.sum_mul]


noncomputable def kotRho (m : FiniteSubstochasticMDP n α) (S : Policy n α) (i : Fin n) (t : ℕ) : ℝ :=
  ∑ s : StateAction m, jointAt m S i t s.1 s.2.1 * m.reward s.1 s.2.1

def kotGap (m : FiniteSubstochasticMDP n α) (u : Fin n → ℝ) (s : StateAction m) : ℝ :=
  m.reward s.1 s.2.1 + ∑ j, m.transition s.1 s.2.1 j * u j - u s.1

lemma kot_mass_u (m : FiniteSubstochasticMDP n α) (S : Policy n α) (i : Fin n) (t : ℕ)
    (u : Fin n → ℝ) :
    ∑ s : StateAction m, jointAt m S i t s.1 s.2.1 * u s.1 = ∑ k, stateAt m S i t k * u k := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold stateAt
  rw [Finset.sum_mul, ← Finset.sum_coe_sort (m.actions k)]

lemma kot_step (m : FiniteSubstochasticMDP n α) (S : Policy n α) (hS : IsPolicy m S)
    (i : Fin n) (t : ℕ) (u : Fin n → ℝ) :
    kotRho m S i t = ∑ s : StateAction m, jointAt m S i t s.1 s.2.1 * kotGap m u s +
      (∑ k, stateAt m S i t k * u k - ∑ k, stateAt m S i (t + 1) k * u k) := by
  have h1 : ∑ s : StateAction m, jointAt m S i t s.1 s.2.1 * kotGap m u s =
      kotRho m S i t + ∑ s : StateAction m, jointAt m S i t s.1 s.2.1 *
        (∑ j, m.transition s.1 s.2.1 j * u j) -
      ∑ s : StateAction m, jointAt m S i t s.1 s.2.1 * u s.1 := by
    unfold kotRho kotGap
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  have h2 : ∑ s : StateAction m, jointAt m S i t s.1 s.2.1 *
      (∑ j, m.transition s.1 s.2.1 j * u j) = ∑ k, stateAt m S i (t + 1) k * u k := by
    simp_rw [kot_stateAt_succ m S hS, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h1, h2, kot_mass_u]
  ring

lemma kot_partial (m : FiniteSubstochasticMDP n α) (S : Policy n α) (hS : IsPolicy m S)
    (i : Fin n) (u : Fin n → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, kotRho m S i t =
      ∑ t ∈ Finset.range T, ∑ s : StateAction m, jointAt m S i t s.1 s.2.1 * kotGap m u s +
      (u i - ∑ k, stateAt m S i T k * u k) := by
  simp_rw [kot_step m S hS i _ u]
  rw [Finset.sum_add_distrib, Finset.sum_range_sub' (fun t => ∑ k, stateAt m S i t k * u k)]
  congr 2
  simp_rw [kot_stateAt_zero m S hS]
  simp

lemma kot_rho_summable (m : FiniteSubstochasticMDP n α) (S : Policy n α) (hS : IsPolicy m S)
    (hT : IsTransient m S) (i : Fin n) : Summable (kotRho m S i) := by
  set C := ∑ s : StateAction m, |m.reward s.1 s.2.1| with hC
  have hb : ∀ t, ‖kotRho m S i t‖ ≤ C * ∑ k, stateAt m S i t k := by
    intro t
    rw [Real.norm_eq_abs]
    unfold kotRho
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hq : ∀ s : StateAction m, jointAt m S i t s.1 s.2.1 ≤ ∑ k, stateAt m S i t k := by
      intro s
      have e1 : jointAt m S i t s.1 s.2.1 ≤ stateAt m S i t s.1 := by
        unfold stateAt
        exact Finset.single_le_sum (f := fun a => jointAt m S i t s.1 a)
          (fun a _ => kot_joint_nonneg m S hS i t _ a) s.2.2
      refine e1.trans ?_
      exact Finset.single_le_sum (f := fun k => stateAt m S i t k)
        (fun k _ => Finset.sum_nonneg fun a _ => kot_joint_nonneg m S hS i t k a)
        (Finset.mem_univ _)
    rw [hC, Finset.sum_mul]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [abs_mul, abs_of_nonneg (kot_joint_nonneg m S hS i t _ _), mul_comm]
    exact mul_le_mul_of_nonneg_left (hq s) (abs_nonneg _)
  refine Summable.of_norm_bounded ?_ hb
  exact (summable_sum fun k _ => hT i k).mul_left C

lemma kot_tail (m : FiniteSubstochasticMDP n α) (S : Policy n α)
    (hT : IsTransient m S) (i : Fin n) (u : Fin n → ℝ) :
    Filter.Tendsto (fun T => ∑ k, stateAt m S i T k * u k) Filter.atTop (nhds 0) := by
  have : ∀ k, Filter.Tendsto (fun T => stateAt m S i T k * u k) Filter.atTop (nhds 0) := by
    intro k
    have := (hT i k).tendsto_atTop_zero.mul_const (u k)
    simpa using this
  simpa using tendsto_finset_sum Finset.univ fun k _ => this k

lemma kot_total_tendsto (m : FiniteSubstochasticMDP n α) (S : Policy n α) (hS : IsPolicy m S)
    (hT : IsTransient m S) (i : Fin n) :
    Filter.Tendsto (fun T => ∑ t ∈ Finset.range T, kotRho m S i t) Filter.atTop
      (nhds (totalReward m S i)) :=
  (kot_rho_summable m S hS hT i).hasSum.tendsto_sum_nat

lemma kot_le_superharmonic (m : FiniteSubstochasticMDP n α) (S : Policy n α) (hS : IsPolicy m S)
    (hT : IsTransient m S) (u : Fin n → ℝ) (hu : IsSuperharmonic m u) (i : Fin n) :
    totalReward m S i ≤ u i := by
  have hlim : Filter.Tendsto (fun T => u i - ∑ k, stateAt m S i T k * u k) Filter.atTop
      (nhds (u i - 0)) := tendsto_const_nhds.sub (kot_tail m S hT i u)
  rw [sub_zero] at hlim
  refine le_of_tendsto_of_tendsto' (kot_total_tendsto m S hS hT i) hlim fun T => ?_
  rw [kot_partial m S hS i u T]
  have : ∑ t ∈ Finset.range T, ∑ s : StateAction m, jointAt m S i t s.1 s.2.1 * kotGap m u s ≤ 0 :=
    Finset.sum_nonpos fun t _ => Finset.sum_nonpos fun s _ =>
      mul_nonpos_of_nonneg_of_nonpos (kot_joint_nonneg m S hS i t _ _)
        (by have := hu s.1 s.2; unfold kotGap; linarith)
  linarith

lemma kot_eq_of_gap (m : FiniteSubstochasticMDP n α) (S : Policy n α) (hS : IsPolicy m S)
    (hT : IsTransient m S) (u : Fin n → ℝ) (i : Fin n)
    (hg : ∀ t (s : StateAction m), jointAt m S i t s.1 s.2.1 * kotGap m u s = 0) :
    totalReward m S i = u i := by
  have hlim : Filter.Tendsto (fun T => u i - ∑ k, stateAt m S i T k * u k) Filter.atTop
      (nhds (u i - 0)) := tendsto_const_nhds.sub (kot_tail m S hT i u)
  rw [sub_zero] at hlim
  refine tendsto_nhds_unique (kot_total_tendsto m S hS hT i) ?_
  refine hlim.congr fun T => ?_
  rw [kot_partial m S hS i u T]
  simp [hg]

end Gen


/-! ## Pure rules and the LP perturbation -/

section Pure
variable {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]

/-- the pure stationary rule of a selector -/
def kotPR (m : FiniteSubstochasticMDP n α) (f : (i : Fin n) → {a : α // a ∈ m.actions i}) :
    StationaryRule n α := fun i a => if a = (f i).1 then 1 else 0

lemma kot_PR_rule (m : FiniteSubstochasticMDP n α) (f : (i : Fin n) → {a : α // a ∈ m.actions i}) :
    IsStationaryRule m (kotPR m f) := by
  intro i
  refine ⟨fun a => ?_, fun a ha => ?_, ?_⟩
  · unfold kotPR; split_ifs <;> norm_num
  · unfold kotPR; rw [if_neg]; intro h; exact ha (h ▸ (f i).2)
  · unfold kotPR; rw [Finset.sum_ite_eq' (m.actions i) (f i).1, if_pos (f i).2]

lemma kot_PR_P (m : FiniteSubstochasticMDP n α) (f : (i : Fin n) → {a : α // a ∈ m.actions i})
    (i j : Fin n) : transitionMatrix m (kotPR m f) i j = m.transition i (f i).1 j := by
  unfold transitionMatrix kotPR
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' (m.actions i) (f i).1, if_pos (f i).2]

lemma kot_sum_fpair (m : FiniteSubstochasticMDP n α) (f : (i : Fin n) → {a : α // a ∈ m.actions i})
    (g : StateAction m → ℝ) (z : Fin n → ℝ) :
    ∑ s : StateAction m, g s * (if s.2.1 = (f s.1).1 then z s.1 else 0) =
      ∑ i, g ⟨i, f i⟩ * z i := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (f i)]
  · simp
  · intro b _ hb
    rw [if_neg (fun h => hb (Subtype.ext h)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma kot_super (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ) (x : StateAction m → ℝ)
    (hopt : IsOptimalLP m β x) (f : (i : Fin n) → {a : α // a ∈ m.actions i})
    (hpos : ∀ i, 0 < x ⟨i, f i⟩)
    (hs : ∀ i j, Summable (fun t : ℕ => (transitionMatrix m (kotPR m f) ^ t) i j))
    (v : Fin n → ℝ) (hv : ∀ k, v k = m.reward k (f k).1 + ∑ j, m.transition k (f k).1 j * v j) :
    IsSuperharmonic m v := by
  intro k b
  by_contra hlt
  push_neg at hlt
  set P := transitionMatrix m (kotPR m f) with hP
  set inv := (1 - P)⁻¹ with hinvdef
  have hinv : inv * (1 - P) = 1 := (kot_inv_eq P hs).2.1
  have hbf : b ≠ f k := by
    intro h; rw [h, ← hv k] at hlt; exact lt_irrefl _ hlt
  set w : Fin n → ℝ := fun j => m.transition k (f k).1 j - m.transition k b.1 j with hw
  set z : Fin n → ℝ := -(vecMul w inv) with hz
  set rf : Fin n → ℝ := fun i => m.reward i (f i).1 with hrf
  -- v = inv * rf
  have hvP : v = rf + P *ᵥ v := by
    funext k'
    rw [hv k']
    simp only [Pi.add_apply, hrf, mulVec, dotProduct, hP, kot_PR_P]
  have hvinv : inv *ᵥ rf = v := by
    have : rf = (1 - P) *ᵥ v := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      nth_rewrite 1 [hvP]
      abel
    rw [this, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  let d : StateAction m → ℝ := fun s =>
    (if s = ⟨k, b⟩ then 1 else 0) - (if s = ⟨k, f k⟩ then 1 else 0) +
      (if s.2.1 = (f s.1).1 then z s.1 else 0)
  -- constraints
  have hcon : ∀ j, ∑ s : StateAction m, kotC m s j * d s = 0 := by
    intro j
    have e1 : ∑ s : StateAction m, kotC m s j * d s =
        kotC m ⟨k, b⟩ j - kotC m ⟨k, f k⟩ j + ∑ i, kotC m ⟨i, f i⟩ j * z i := by
      rw [← kot_sum_fpair m f (fun s => kotC m s j) z]
      simp only [d, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have e2 : ∑ i, kotC m ⟨i, f i⟩ j * z i = (vecMul z (1 - P)) j := by
      rw [Matrix.vecMul_sub, Matrix.vecMul_one]
      simp only [kotC, Pi.sub_apply, vecMul, dotProduct, hP, kot_PR_P, sub_mul,
        Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        if_true]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    have e3 : vecMul z (1 - P) = -w := by
      rw [hz, Matrix.neg_vecMul, Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]
    rw [e1, e2, e3]
    simp only [kotC, Pi.neg_apply, hw]
    ring
  -- objective
  have hobj : 0 < ∑ s : StateAction m, m.reward s.1 s.2.1 * d s := by
    have e1 : ∑ s : StateAction m, m.reward s.1 s.2.1 * d s =
        m.reward k b.1 - m.reward k (f k).1 + ∑ i, m.reward i (f i).1 * z i := by
      rw [← kot_sum_fpair m f (fun s => m.reward s.1 s.2.1)]
      simp only [d, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have e2 : ∑ i, m.reward i (f i).1 * z i = -(w ⬝ᵥ v) := by
      rw [← hvinv, Matrix.dotProduct_mulVec, hz]
      simp only [dotProduct, Pi.neg_apply, hrf]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2]
    simp only [dotProduct, hw, sub_mul, Finset.sum_sub_distrib]
    have := hv k
    linarith
  -- small step
  have hfeas : IsFeasible m β x := hopt.1
  have hdpos : ∀ s, x s = 0 → 0 ≤ d s := by
    intro s hxs
    have hnf : s.2.1 ≠ (f s.1).1 := by
      intro h
      have hs' : s = ⟨s.1, f s.1⟩ := Sigma.ext rfl (heq_of_eq (Subtype.ext h))
      have := hpos s.1
      rw [← hs'] at this
      linarith
    have hne : s ≠ ⟨k, f k⟩ := by
      intro h; apply hnf; rw [h]
    simp only [d, if_neg hnf, if_neg hne, sub_zero, add_zero]
    split_ifs <;> norm_num
  set K := ∑ s, |d s| / x s with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun s _ => div_nonneg (abs_nonneg _) (hfeas.1 s)
  set ε := 1 / (1 + K) with hε
  have hεpos : 0 < ε := by positivity
  have hnew : IsFeasible m β (x + ε • d) := by
    refine ⟨fun s => ?_, fun j => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases (hfeas.1 s).lt_or_eq with hp | hp
      · have h1 : |d s| / x s ≤ K :=
          Finset.single_le_sum (f := fun s => |d s| / x s)
            (fun s _ => div_nonneg (abs_nonneg _) (hfeas.1 s)) (Finset.mem_univ s)
        have h2 : |d s| ≤ x s * K := by
          rw [div_le_iff₀ hp] at h1; linarith
        have h3 : ε * |d s| ≤ x s := by
          rw [hε, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
          nlinarith
        have h4 := neg_abs_le (d s)
        nlinarith
      · rw [← hp]; have := hdpos s hp.symm; positivity
    · have h := hfeas.2 j
      have h2 := hcon j
      simp only [kotC] at h2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
      rw [h]
      have : ∑ s : StateAction m, ((if s.1 = j then (1 : ℝ) else 0) - m.transition s.1 s.2.1 j) *
          (ε * d s) = ε * ∑ s : StateAction m,
          ((if s.1 = j then (1 : ℝ) else 0) - m.transition s.1 s.2.1 j) * d s := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
      rw [this, h2, mul_zero, add_zero]
  have hle := hopt.2 _ hnew
  unfold objective at hle
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib] at hle
  have : ∑ s : StateAction m, m.reward s.1 s.2.1 * (ε * d s) =
      ε * ∑ s : StateAction m, m.reward s.1 s.2.1 * d s := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
  rw [this] at hle
  have := mul_pos hεpos hobj
  linarith

end Pure


theorem extreme_optimal_core {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ)
    (hβ : ∀ i, 0 < β i)
    (x : StateAction m → ℝ)
    (hopt : IsOptimalLP m β x)
    (hext : x ∈ (feasibleSet m β).extremePoints ℝ)
    (f : (i : Fin n) → {a : α // a ∈ m.actions i})
    (hpositive : ∀ i, 0 < x ⟨i, f i⟩) :
    IsOptimalTransient m (purePolicy (fun i => (f i).1)) := by
  obtain ⟨hπ, htr, hocc⟩ := kot_part2 m β hβ x hopt.1
  set π := ruleOfOccupation m x with hπdef
  have hpure : IsPureRule m π := by
    rw [← kot_part4 m β hβ π hπ htr, hocc]; exact hext
  obtain ⟨g, hg⟩ := hpure
  have hfg : ∀ i, (f i).1 = (g i).1 := by
    intro i
    have hm : 0 < stateMass m x i := lt_of_lt_of_le (hβ i) (kot_mass_ge m β x hopt.1 i)
    have h1 : 0 < π i (f i).1 := by
      simp only [hπdef, ruleOfOccupation, dif_pos (f i).2]
      exact div_pos (hpositive i) hm
    rw [hg] at h1
    by_contra hne
    rw [if_neg hne] at h1
    exact lt_irrefl _ h1
  have hπf : π = kotPR m f := by
    funext i a
    rw [hg]; unfold kotPR; rw [hfg]
  have hpp : purePolicy (fun i => (f i).1) = stationaryPolicy (kotPR m f) := rfl
  have hR := kot_PR_rule m f
  have htrf : IsTransient m (stationaryPolicy (kotPR m f)) := by rw [← hπf]; exact htr
  have hs := (kot_transient_iff m _ hR).1 htrf
  set P := transitionMatrix m (kotPR m f) with hP
  set rf : Fin n → ℝ := fun i => m.reward i (f i).1 with hrf
  set v := (1 - P)⁻¹ *ᵥ rf with hvdef
  have hv1 : (1 - P) *ᵥ v = rf := by
    rw [hvdef, Matrix.mulVec_mulVec, (kot_inv_eq P hs).2.2, Matrix.one_mulVec]
  have hv : ∀ k, v k = m.reward k (f k).1 + ∑ j, m.transition k (f k).1 j * v j := by
    intro k
    have := congrFun hv1 k
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply] at this
    simp only [mulVec, dotProduct, hP, kot_PR_P, hrf] at this
    linarith
  have hsup := kot_super m β x hopt f hpositive hs v hv
  have hpol : IsPolicy m (stationaryPolicy (kotPR m f)) := fun t h i => hR i
  have hval : ∀ i, totalReward m (stationaryPolicy (kotPR m f)) i = v i := by
    intro i
    apply kot_eq_of_gap m _ hpol htrf v i
    intro t s
    rw [kot_jointAt m _ hR]
    unfold kotPR
    split_ifs with h
    · have hs' : s = ⟨s.1, f s.1⟩ := Sigma.ext rfl (heq_of_eq (Subtype.ext h))
      have : kotGap m v s = 0 := by
        rw [hs']; unfold kotGap; rw [← hv]; ring
      rw [this, mul_zero]
    · rw [mul_zero, zero_mul]
  rw [hpp]
  refine ⟨hpol, htrf, fun S hS hST i => ?_⟩
  rw [hval i]
  exact kot_le_superharmonic m S hS hST v hsup i

end KallenbergLP.OptTransient

open KallenbergLP.OptTransient


theorem solution {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (m : FiniteSubstochasticMDP n α) (β : Fin n → ℝ)
    (hβ : ∀ i, 0 < β i)
    (x : StateAction m → ℝ)
    (hopt : IsOptimalLP m β x)
    (hext : x ∈ (feasibleSet m β).extremePoints ℝ)
    (f : (i : Fin n) → {a : α // a ∈ m.actions i})
    (hpositive : ∀ i, 0 < x ⟨i, f i⟩) :
    IsOptimalTransient m (purePolicy (fun i => (f i).1)) := by
  exact extreme_optimal_core m β hβ x hopt hext f hpositive
