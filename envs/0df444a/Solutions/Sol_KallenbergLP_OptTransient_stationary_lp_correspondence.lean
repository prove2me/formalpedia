-- Prove2me | solution 1 for KallenbergLP.OptTransient.stationary_lp_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:00:00.4878+00:00
-- url     : https://prove2.me/submissions/7358af21-c199-4d75-8025-b21fa430cb9e

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

end KallenbergLP.OptTransient

open KallenbergLP.OptTransient


theorem solution {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
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
       IsPureRule m π)) := by
  exact stationary_lp_correspondence_core m β hex hβ
