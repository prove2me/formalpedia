-- Prove2me | solution 1 for KallenbergLP.Contracting.lp_optimal_pure_policy
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:38:52.82788+00:00
-- url     : https://prove2.me/submissions/e471e522-84e1-4980-9bd5-4751d40afe3e

import Mathlib
import Definitions.Def_KallenbergLP_Contracting_Occupation



namespace KallenbergLP.Contracting

open scoped BigOperators
open Finset Classical

variable {E : Type} [Fintype E] {A : E → Type} [∀ i, Fintype (A i)]

namespace FiniteMDP

lemma kc_hp_nonneg (M : FiniteMDP E A) (π : Policy E A) (hπ : IsPolicy π) (i : E) :
    ∀ n (h : History E A n), 0 ≤ M.historyProbability π i n h := by
  intro n
  induction n with
  | zero => intro h; simp only [historyProbability]; split_ifs <;> norm_num
  | succ n ih =>
    intro h
    simp only [historyProbability]
    exact mul_nonneg (mul_nonneg (ih _) (hπ.1 _ _ _)) (M.transition_nonneg _ _ _)

lemma kc_sap_nonneg (M : FiniteMDP E A) (π : Policy E A) (hπ : IsPolicy π) (i j : E) (a : A j) (n : ℕ) :
    0 ≤ M.stateActionProbability π i j a n := by
  unfold stateActionProbability
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (M.kc_hp_nonneg π hπ i _ _) (hπ.1 _ _ _)

lemma kc_sap_zero (M : FiniteMDP E A) (π : Policy E A) (hπ : IsPolicy π) (i j : E) :
    ∑ a, M.stateActionProbability π i j a 0 = if j = i then 1 else 0 := by
  unfold stateActionProbability
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun x _ => by rw [hπ.2 0 (x, j), mul_one]]
  rw [Fintype.sum_unique]
  simp [historyProbability]

lemma kc_sap_succ (M : FiniteMDP E A) (π : Policy E A) (hπ : IsPolicy π) (i j : E) (n : ℕ) :
    ∑ a, M.stateActionProbability π i j a (n+1) =
      ∑ k, ∑ b : A k, M.transition k b j * M.stateActionProbability π i k b n := by
  unfold stateActionProbability
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun x _ => by rw [hπ.2 (n+1) (x, j), mul_one]]
  set G : (Fin n → Σ k : E, A k) → (Σ k : E, A k) → ℝ := fun acts x =>
    M.historyProbability π i n (acts, x.1) * π n (acts, x.1) x.2 * M.transition x.1 x.2 j with hG
  have hF : ∀ y : Fin (n+1) → Σ k : E, A k,
      M.historyProbability π i (n+1) (y, j) = G (Fin.init y) (y (Fin.last n)) := fun y => rfl
  simp only [hF]
  rw [← (Fin.snocEquiv (fun _ : Fin (n+1) => Σ k : E, A k)).sum_comp]
  simp only [Fin.snocEquiv_apply, Fin.init_snoc, Fin.snoc_last]
  rw [Fintype.sum_prod_type, Fintype.sum_sigma]
  simp only [Finset.mul_sum, hG]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun acts _ => ?_
  have e : Fin.init ((Fin.snocEquiv fun _ : Fin (n+1) => (Σ k : E, A k)) (⟨k, b⟩, acts)) = acts := by
    funext t; simp [Fin.init]
  rw [e]
  ring


/-- the per-stage state–action vector weighted by `β`. -/
noncomputable def kcY (M : FiniteMDP E A) (β : E → ℝ) (π : Policy E A) (n : ℕ) (j : E) (a : A j) : ℝ :=
  ∑ i, β i * M.stateActionProbability π i j a n

lemma kcY_nonneg (M : FiniteMDP E A) (β : E → ℝ) (hβ : ∀ i, 0 ≤ β i) (π : Policy E A) (hπ : IsPolicy π)
    (n : ℕ) (j : E) (a : A j) : 0 ≤ M.kcY β π n j a :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hβ i) (M.kc_sap_nonneg π hπ _ _ _ _)

lemma kcY_zero (M : FiniteMDP E A) (β : E → ℝ) (π : Policy E A) (hπ : IsPolicy π) (j : E) :
    ∑ a, M.kcY β π 0 j a = β j := by
  unfold kcY
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, M.kc_sap_zero π hπ]
  simp

lemma kcY_succ (M : FiniteMDP E A) (β : E → ℝ) (π : Policy E A) (hπ : IsPolicy π) (n : ℕ) (j : E) :
    ∑ a, M.kcY β π (n+1) j a = ∑ k, ∑ b : A k, M.transition k b j * M.kcY β π n k b := by
  unfold kcY
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, M.kc_sap_succ π hπ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma kcY_weight (M : FiniteMDP E A) (C : Contraction M) (β : E → ℝ) (hβ : ∀ i, 0 ≤ β i)
    (π : Policy E A) (hπ : IsPolicy π) (n : ℕ) :
    ∑ j, ∑ a : A j, C.weight j * M.kcY β π (n+1) j a ≤
      C.factor * ∑ j, ∑ a : A j, C.weight j * M.kcY β π n j a := by
  have h1 : ∑ j, ∑ a : A j, C.weight j * M.kcY β π (n+1) j a =
      ∑ k, ∑ b : A k, M.kcY β π n k b * ∑ j, M.transition k b j * C.weight j := by
    calc _ = ∑ j, C.weight j * ∑ a : A j, M.kcY β π (n+1) j a := by simp only [Finset.mul_sum]
      _ = ∑ j, C.weight j * ∑ k, ∑ b : A k, M.transition k b j * M.kcY β π n k b := by
          simp only [M.kcY_succ β π hπ]
      _ = _ := ?_
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h1, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  have := C.bound k b
  have hy := M.kcY_nonneg β hβ π hπ n k b
  nlinarith

lemma kcY_geom (M : FiniteMDP E A) (C : Contraction M) (β : E → ℝ) (hβ : ∀ i, 0 ≤ β i)
    (π : Policy E A) (hπ : IsPolicy π) (n : ℕ) :
    ∑ j, ∑ a : A j, C.weight j * M.kcY β π n j a ≤
      C.factor ^ n * ∑ j, ∑ a : A j, C.weight j * M.kcY β π 0 j a := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc _ ≤ C.factor * ∑ j, ∑ a : A j, C.weight j * M.kcY β π n j a := M.kcY_weight C β hβ π hπ n
      _ ≤ C.factor * (C.factor ^ n * ∑ j, ∑ a : A j, C.weight j * M.kcY β π 0 j a) :=
          mul_le_mul_of_nonneg_left ih C.factor_nonneg
      _ = _ := by ring

lemma kcY_le (M : FiniteMDP E A) (C : Contraction M) (β : E → ℝ) (hβ : ∀ i, 0 ≤ β i)
    (π : Policy E A) (hπ : IsPolicy π) (n : ℕ) (j : E) (a : A j) :
    M.kcY β π n j a ≤
      C.factor ^ n * ((∑ j, ∑ a : A j, C.weight j * M.kcY β π 0 j a) / C.weight j) := by
  have hw := C.weight_pos j
  have h1 : C.weight j * M.kcY β π n j a ≤ ∑ j, ∑ a : A j, C.weight j * M.kcY β π n j a := by
    have hn : ∀ j' (a' : A j'), 0 ≤ C.weight j' * M.kcY β π n j' a' := fun j' a' =>
      mul_nonneg (C.weight_pos j').le (M.kcY_nonneg β hβ π hπ n j' a')
    calc C.weight j * M.kcY β π n j a ≤ ∑ a : A j, C.weight j * M.kcY β π n j a :=
          Finset.single_le_sum (f := fun a => C.weight j * M.kcY β π n j a) (fun a' _ => hn j a') (Finset.mem_univ a)
      _ ≤ _ := Finset.single_le_sum (f := fun j => ∑ a : A j, C.weight j * M.kcY β π n j a)
          (fun j' _ => Finset.sum_nonneg fun a' _ => hn j' a') (Finset.mem_univ j)
  have h2 := M.kcY_geom C β hβ π hπ n
  rw [mul_div_assoc', le_div_iff₀ hw]
  nlinarith

lemma kcY_summable (M : FiniteMDP E A) (C : Contraction M) (β : E → ℝ) (hβ : ∀ i, 0 ≤ β i)
    (π : Policy E A) (hπ : IsPolicy π) (j : E) (a : A j) :
    Summable (fun n => M.kcY β π n j a) := by
  refine Summable.of_nonneg_of_le (fun n => M.kcY_nonneg β hβ π hπ n j a)
    (fun n => M.kcY_le C β hβ π hπ n j a) ?_
  exact (summable_geometric_of_lt_one C.factor_nonneg C.factor_lt_one).mul_right _

lemma kc_frequency_eq (M : FiniteMDP E A) (β : E → ℝ) (π : Policy E A) (j : E) (a : A j) :
    M.frequency β π j a = ∑' n, M.kcY β π n j a := rfl

lemma kc_frequency_mem (M : FiniteMDP E A) (C : Contraction M) (β : E → ℝ) (hβ : ∀ i, 0 ≤ β i)
    (π : Policy E A) (hπ : IsPolicy π) : M.frequency β π ∈ M.feasibleFrequency β := by
  refine ⟨fun i a => ?_, fun j => ?_⟩
  · rw [kc_frequency_eq]; exact tsum_nonneg fun n => M.kcY_nonneg β hβ π hπ n i a
  · simp only [kc_frequency_eq]
    have hs := M.kcY_summable C β hβ π hπ
    rw [← Summable.tsum_finsetSum (fun a _ => hs j a)]
    rw [(summable_sum fun a _ => hs j a).tsum_eq_zero_add]
    simp only [M.kcY_zero β π hπ, M.kcY_succ β π hπ]
    have : ∑ i, ∑ a : A i, M.transition i a j * ∑' n, M.kcY β π n i a =
        ∑' n, ∑ k, ∑ b : A k, M.transition k b j * M.kcY β π n k b := by
      rw [Summable.tsum_finsetSum (fun i _ => summable_sum fun b _ => (hs i b).mul_left _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Summable.tsum_finsetSum (fun b _ => (hs i b).mul_left _)]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [tsum_mul_left]
    rw [this]; ring


lemma kc_unique (M : FiniteMDP E A) (C : Contraction M) (q : StationaryRule E A) (hq : IsStationaryRule q)
    (d : E → ℝ) (hd : ∀ j, d j = ∑ i, ∑ a : A i, M.transition i a j * (d i * q i a)) :
    ∀ j, d j = 0 := by
  have habs : ∀ j, |d j| ≤ ∑ i, ∑ a : A i, M.transition i a j * (|d i| * q i a) := by
    intro j
    rw [hd j]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg (M.transition_nonneg _ _ _), abs_of_nonneg (hq.1 i a)]
  set S := ∑ j, C.weight j * |d j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => mul_nonneg (C.weight_pos j).le (abs_nonneg _)
  have hle : S ≤ C.factor * S := by
    calc S ≤ ∑ j, C.weight j * ∑ i, ∑ a : A i, M.transition i a j * (|d i| * q i a) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (habs j) (C.weight_pos j).le
      _ = ∑ i, ∑ a : A i, (|d i| * q i a) * ∑ j, M.transition i a j * C.weight j := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ ≤ ∑ i, ∑ a : A i, (|d i| * q i a) * (C.factor * C.weight i) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ => ?_
          exact mul_le_mul_of_nonneg_left (C.bound i a) (mul_nonneg (abs_nonneg _) (hq.1 i a))
      _ = C.factor * S := by
          rw [hS, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          have : ∑ a : A i, (|d i| * q i a) * (C.factor * C.weight i) =
              (|d i| * (C.factor * C.weight i)) * ∑ a : A i, q i a := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_; ring
          rw [this, hq.2 i]; ring
  have hS' : S = 0 := by
    have := C.factor_lt_one
    nlinarith
  intro j
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => mul_nonneg (C.weight_pos j).le (abs_nonneg (d j)))).1 hS' j (Finset.mem_univ j)
  rcases mul_eq_zero.1 hterm with h | h
  · exact absurd h (C.weight_pos j).ne'
  · exact abs_eq_zero.1 h

lemma kc_rep_eq (M : FiniteMDP E A) (C : Contraction M) (β : E → ℝ) (q : StationaryRule E A)
    (hq : IsStationaryRule q) (x z : StationaryRule E A)
    (hx : x ∈ M.feasibleFrequency β) (hz : z ∈ M.feasibleFrequency β)
    (hxr : ∀ j a, x j a = (∑ b, x j b) * q j a) (hzr : ∀ j a, z j a = (∑ b, z j b) * q j a) :
    x = z := by
  set d : E → ℝ := fun j => (∑ b, x j b) - ∑ b, z j b with hd
  have hd' : ∀ j, d j = ∑ i, ∑ a : A i, M.transition i a j * (d i * q i a) := by
    intro j
    have h1 := hx.2 j
    have h2 := hz.2 j
    have e : ∑ i, ∑ a : A i, M.transition i a j * (d i * q i a) =
        (∑ i, ∑ a : A i, M.transition i a j * x i a) - ∑ i, ∑ a : A i, M.transition i a j * z i a := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hxr i a, hzr i a, hd]; ring
    rw [e, hd]; simp only; linarith
  have h0 := M.kc_unique C q hq d hd'
  funext j a
  rw [hxr j a, hzr j a]
  have := h0 j
  simp only [hd] at this
  rw [sub_eq_zero.1 this]

lemma kc_P_rep [∀ i, Nonempty (A i)] (M : FiniteMDP E A) (β : E → ℝ) (x : StationaryRule E A)
    (hx : x ∈ M.feasibleFrequency β) : ∀ j a, x j a = (∑ b, x j b) * ruleOfFrequency x j a := by
  intro j a
  unfold ruleOfFrequency
  by_cases h : (∑ b, x j b) ≠ 0
  · rw [dif_pos h]; field_simp
  · rw [dif_neg h]
    push_neg at h
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hx.1 j b)).1 h a (Finset.mem_univ a)
    rw [this, h]; ring

lemma kc_rule_stat [∀ i, Nonempty (A i)] (M : FiniteMDP E A) (β : E → ℝ) (x : StationaryRule E A)
    (hx : x ∈ M.feasibleFrequency β) : IsStationaryRule (ruleOfFrequency x) := by
  refine ⟨fun i a => ?_, fun i => ?_⟩
  · unfold ruleOfFrequency
    split_ifs with h
    · exact div_nonneg (hx.1 i a) (Finset.sum_nonneg fun b _ => hx.1 i b)
    · norm_num
    · norm_num
  · unfold ruleOfFrequency
    by_cases h : (∑ b, x i b) ≠ 0
    · simp only [dif_pos h]; rw [← Finset.sum_div]; exact div_self h
    · simp only [dif_neg h]; simp

lemma kc_stat_rep (M : FiniteMDP E A) (β : E → ℝ) (q : StationaryRule E A) (hq : IsStationaryRule q) :
    ∀ j a, M.frequency β (stationaryPolicy q) j a =
      (∑ b, M.frequency β (stationaryPolicy q) j b) * q j a := by
  have key : ∀ j a, M.frequency β (stationaryPolicy q) j a =
      (∑' n, ∑ i, β i * ∑ acts : Fin n → Σ k : E, A k, M.historyProbability (stationaryPolicy q) i n (acts, j)) * q j a := by
    intro j a
    unfold frequency stateActionProbability
    rw [← tsum_mul_right]
    refine tsum_congr fun n => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, Finset.sum_mul]
    congr 1
  intro j a
  rw [key j a]
  congr 1
  simp only [key j, ← Finset.mul_sum, hq.2 j, mul_one]

lemma kc_stationary_isPolicy (q : StationaryRule E A) (hq : IsStationaryRule q) :
    IsPolicy (stationaryPolicy q) :=
  ⟨fun _ h a => hq.1 h.2 a, fun _ h => hq.2 h.2⟩

lemma kc_P_sub_KS [∀ i, Nonempty (A i)] (M : FiniteMDP E A) (C : Contraction M) (β : E → ℝ)
    (hβ : ∀ i, 0 ≤ β i) (x : StationaryRule E A) (hx : x ∈ M.feasibleFrequency β) :
    x = M.frequency β (stationaryPolicy (ruleOfFrequency x)) := by
  have hq := M.kc_rule_stat β x hx
  exact M.kc_rep_eq C β _ hq x _ hx
    (M.kc_frequency_mem C β hβ _ (kc_stationary_isPolicy _ hq))
    (M.kc_P_rep β x hx) (M.kc_stat_rep β _ hq)


/-- flow operator -/
def kcN (M : FiniteMDP E A) (D : StationaryRule E A) (j : E) : ℝ :=
  (∑ a : A j, D j a) - ∑ i : E, ∑ a : A i, M.transition i a j * D i a

lemma kcN_add (M : FiniteMDP E A) (D D' : StationaryRule E A) (j : E) :
    M.kcN (D + D') j = M.kcN D j + M.kcN D' j := by
  unfold kcN
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring

lemma kcN_smul (M : FiniteMDP E A) (c : ℝ) (D : StationaryRule E A) (j : E) :
    M.kcN (c • D) j = c * M.kcN D j := by
  unfold kcN
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

noncomputable def kcExt (x : StationaryRule E A) (d : {p : Σ i, A i // 0 < x p.1 p.2} → ℝ) :
    StationaryRule E A :=
  fun i a => if h : 0 < x i a then d ⟨⟨i, a⟩, h⟩ else 0

lemma kcExt_add (x : StationaryRule E A) (d d' : {p : Σ i, A i // 0 < x p.1 p.2} → ℝ) :
    kcExt x (d + d') = kcExt x d + kcExt x d' := by
  funext i a; simp only [kcExt, Pi.add_apply]; split_ifs <;> simp

lemma kcExt_smul (x : StationaryRule E A) (c : ℝ) (d : {p : Σ i, A i // 0 < x p.1 p.2} → ℝ) :
    kcExt x (c • d) = c • kcExt x d := by
  funext i a; simp only [kcExt, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp

noncomputable def kcL (M : FiniteMDP E A) (x : StationaryRule E A) :
    ({p : Σ i, A i // 0 < x p.1 p.2} → ℝ) →ₗ[ℝ] ({j : E // 0 < ∑ c, x j c} → ℝ) where
  toFun d j := M.kcN (kcExt x d) j.1
  map_add' d d' := by funext j; simp only [kcExt_add, kcN_add, Pi.add_apply]
  map_smul' c d := by funext j; simp only [kcExt_smul, kcN_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

lemma kc_extreme_single (M : FiniteMDP E A) (β : E → ℝ) (hβ : ∀ i, 0 ≤ β i) (x : StationaryRule E A)
    (hx : x ∈ (M.feasibleFrequency β).extremePoints ℝ) (i : E) (a b : A i)
    (ha : 0 < x i a) (hb : 0 < x i b) : a = b := by
  by_contra hab
  obtain ⟨hxP, hext⟩ := mem_extremePoints.1 hx
  have hpos : ∀ j : {j : E // 0 < ∑ c, x j c}, ∃ c, 0 < x j.1 c := by
    intro j
    by_contra hc
    push_neg at hc
    have := j.2
    have : ∑ c, x j.1 c ≤ 0 := Finset.sum_nonpos fun c _ => hc c
    linarith
  let g : {j : E // 0 < ∑ c, x j c} → {p : Σ i, A i // 0 < x p.1 p.2} :=
    fun j => ⟨⟨j.1, (hpos j).choose⟩, (hpos j).choose_spec⟩
  have ginj : Function.Injective g := by
    intro j1 j2 h
    exact Subtype.ext (congrArg (fun s => s.1.1) h)
  have gns : ¬ Function.Surjective g := by
    intro hs
    obtain ⟨j1, h1⟩ := hs ⟨⟨i, a⟩, ha⟩
    obtain ⟨j2, h2⟩ := hs ⟨⟨i, b⟩, hb⟩
    have e1 : j1.1 = i := congrArg (fun s => s.1.1) h1
    have e2 : j2.1 = i := congrArg (fun s => s.1.1) h2
    have e : j1 = j2 := Subtype.ext (e1.trans e2.symm)
    subst e
    rw [h1] at h2
    have := congrArg (fun s => s.1) h2
    simp only [Subtype.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at this
    exact hab this
  have hcard := Fintype.card_lt_of_injective_not_surjective g ginj gns
  have hker : LinearMap.ker (M.kcL x) ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp only [Module.finrank_fintype_fun_eq_card]
    exact hcard
  obtain ⟨d, hdk, hd0⟩ := (Submodule.ne_bot_iff _).1 hker
  set D := kcExt x d with hD
  -- D vanishes where x vanishes
  have hDz : ∀ i a, ¬ 0 < x i a → D i a = 0 := by
    intro i a h; simp only [hD, kcExt, dif_neg h]
  have hD0 : D ≠ 0 := by
    intro h
    apply hd0
    funext s
    have := congrFun (congrFun h s.1.1) s.1.2
    simp only [hD, kcExt, dif_pos s.2, Pi.zero_apply] at this
    simpa using this
  have hND : ∀ j, M.kcN D j = 0 := by
    intro j
    by_cases hj : 0 < ∑ c, x j c
    · have := congrFun (LinearMap.mem_ker.1 hdk) ⟨j, hj⟩
      simpa [kcL] using this
    · have hu : ∑ c, x j c = 0 :=
        le_antisymm (not_lt.1 hj) (Finset.sum_nonneg fun c _ => hxP.1 j c)
      have hxj : ∀ c, x j c = 0 := fun c =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => hxP.1 j c)).1 hu c (Finset.mem_univ c)
      have hflow := hxP.2 j
      rw [hu] at hflow
      have hin : ∑ i : E, ∑ a : A i, M.transition i a j * x i a = 0 := by
        have h0 : 0 ≤ ∑ i : E, ∑ a : A i, M.transition i a j * x i a :=
          Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ =>
            mul_nonneg (M.transition_nonneg _ _ _) (hxP.1 i a)
        have := hβ j
        linarith
      have hterm : ∀ i (a : A i), M.transition i a j * x i a = 0 := by
        intro i a
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun a _ =>
            mul_nonneg (M.transition_nonneg _ _ _) (hxP.1 i a))).1 hin i (Finset.mem_univ i)
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
            mul_nonneg (M.transition_nonneg _ _ _) (hxP.1 i a))).1 h1 a (Finset.mem_univ a)
      unfold kcN
      have e1 : ∑ a : A j, D j a = 0 :=
        Finset.sum_eq_zero fun c _ => hDz j c (by rw [hxj c]; exact lt_irrefl 0)
      have e2 : ∑ i : E, ∑ a : A i, M.transition i a j * D i a = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun a _ => ?_
        by_cases hp : 0 < x i a
        · have := hterm i a
          rcases mul_eq_zero.1 this with h | h
          · rw [h, zero_mul]
          · exact absurd h hp.ne'
        · rw [hDz i a hp, mul_zero]
      rw [e1, e2, sub_zero]
  -- choose ε
  set K := ∑ i, ∑ a : A i, |D i a| / x i a with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ =>
    div_nonneg (abs_nonneg _) (hxP.1 i a)
  set ε := 1 / (1 + K) with hε
  have hεpos : 0 < ε := by positivity
  have hεle : ∀ i a, ε * |D i a| ≤ x i a := by
    intro i a
    by_cases hp : 0 < x i a
    · have h1 : |D i a| / x i a ≤ K := by
        have hn : ∀ i' (a' : A i'), 0 ≤ |D i' a'| / x i' a' := fun i' a' =>
          div_nonneg (abs_nonneg _) (hxP.1 i' a')
        calc |D i a| / x i a ≤ ∑ a' : A i, |D i a'| / x i a' :=
              Finset.single_le_sum (f := fun a' => |D i a'| / x i a') (fun a' _ => hn i a') (Finset.mem_univ a)
          _ ≤ K := Finset.single_le_sum (f := fun i => ∑ a' : A i, |D i a'| / x i a')
              (fun i' _ => Finset.sum_nonneg fun a' _ => hn i' a') (Finset.mem_univ i)
      have h2 : |D i a| ≤ x i a * K := by
        rw [div_le_iff₀ hp] at h1; linarith
      rw [hε, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      nlinarith
    · rw [hDz i a hp, abs_zero, mul_zero]; exact hxP.1 i a
  have hmem : ∀ s : ℝ, |s| ≤ ε → x + s • D ∈ M.feasibleFrequency β := by
    intro s hs
    refine ⟨fun i a => ?_, fun j => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1 := hεle i a
      have h2 : |s * D i a| ≤ ε * |D i a| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)
      have h3 := neg_abs_le (s * D i a)
      linarith
    · have := M.kcN_add x (s • D) j
      rw [M.kcN_smul, hND j, mul_zero, add_zero] at this
      unfold kcN at this
      rw [this]; exact hxP.2 j
  have hplus := hmem ε (by rw [abs_of_pos hεpos])
  have hminus := hmem (-ε) (by rw [abs_neg, abs_of_pos hεpos])
  have hseg : x ∈ openSegment ℝ (x + ε • D) (x + (-ε) • D) :=
    ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by
      funext i a; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring⟩
  have := (hext _ hplus _ hminus hseg).1
  have h2 : ε • D = 0 := by
    have := congrArg (fun z => z - x) this
    simpa using this
  rcases smul_eq_zero.1 h2 with h | h
  · exact hεpos.ne' h
  · exact hD0 h


lemma kc_extreme_mem_KD [∀ i, Nonempty (A i)] (M : FiniteMDP E A) (C : Contraction M) (β : E → ℝ)
    (hβ : ∀ i, 0 ≤ β i) (x : StationaryRule E A)
    (hx : x ∈ (M.feasibleFrequency β).extremePoints ℝ) : x ∈ M.KD β := by
  have hxP : x ∈ M.feasibleFrequency β := hx.1
  let f : PureRule E A := fun j =>
    if h : ∃ c, 0 < x j c then h.choose else Classical.choice (inferInstance : Nonempty (A j))
  refine ⟨f, ?_⟩
  have hrule : ruleOfFrequency x = pureRule f := by
    funext j a
    unfold ruleOfFrequency pureRule
    by_cases hu : (∑ b, x j b) ≠ 0
    · have hex : ∃ c, 0 < x j c := by
        by_contra hc; push_neg at hc
        exact hu (le_antisymm (Finset.sum_nonpos fun c _ => hc c)
          (Finset.sum_nonneg fun c _ => hxP.1 j c))
      have hf : f j = hex.choose := by simp only [f, dif_pos hex]
      set c0 := hex.choose with hc0
      have hc0pos : 0 < x j c0 := hex.choose_spec
      have hzero : ∀ c, c ≠ c0 → x j c = 0 := by
        intro c hc
        by_contra hne
        have hpos : 0 < x j c := lt_of_le_of_ne (hxP.1 j c) (Ne.symm hne)
        exact hc (M.kc_extreme_single β hβ x hx j c c0 hpos hc0pos)
      have hsum : ∑ b, x j b = x j c0 :=
        Finset.sum_eq_single c0 (fun c _ hc => hzero c hc) (fun h => absurd (Finset.mem_univ _) h)
      rw [dif_pos hu, hf, hsum]
      by_cases hac : a = c0
      · subst hac; rw [if_pos rfl]; exact div_self hc0pos.ne'
      · rw [if_neg hac, hzero a hac, zero_div]
    · have hex : ¬ ∃ c, 0 < x j c := by
        push_neg at hu
        rintro ⟨c, hc⟩
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => hxP.1 j c)).1 hu c (Finset.mem_univ c)
        linarith
      have hf : f j = Classical.choice (inferInstance : Nonempty (A j)) := by simp only [f, dif_neg hex]
      rw [dif_neg hu, hf]
  have := M.kc_P_sub_KS C β hβ x hxP
  rw [hrule] at this
  exact this

lemma kc_P_convex (M : FiniteMDP E A) (β : E → ℝ) : Convex ℝ (M.feasibleFrequency β) := by
  intro x hx y hy s t hs ht hst
  refine ⟨fun i a => ?_, fun j => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hs (hx.1 i a)) (mul_nonneg ht (hy.1 i a))
  · have h1 := hx.2 j
    have h2 := hy.2 j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e1 : ∑ a : A j, (s * x j a + t * y j a) = s * ∑ a : A j, x j a + t * ∑ a : A j, y j a := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    have e2 : ∑ i : E, ∑ a : A i, M.transition i a j * (s * x i a + t * y i a) =
        s * ∑ i : E, ∑ a : A i, M.transition i a j * x i a +
        t * ∑ i : E, ∑ a : A i, M.transition i a j * y i a := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [e1, e2]
    calc _ = s * ((∑ a : A j, x j a) - ∑ i : E, ∑ a : A i, M.transition i a j * x i a) +
          t * ((∑ a : A j, y j a) - ∑ i : E, ∑ a : A i, M.transition i a j * y i a) := by ring
      _ = _ := by rw [h1, h2, ← add_mul, hst, one_mul]

lemma kc_P_bound (M : FiniteMDP E A) (C : Contraction M) (β : E → ℝ) (hβ : ∀ i, 0 ≤ β i)
    (x : StationaryRule E A) (hx : x ∈ M.feasibleFrequency β) (i : E) (a : A i) :
    x i a ≤ (∑ j, β j * C.weight j) / (1 - C.factor) / C.weight i := by
  set T := ∑ j, ∑ a : A j, C.weight j * x j a with hT
  have hT1 : T ≤ (∑ j, β j * C.weight j) + C.factor * T := by
    have e : T = ∑ j, C.weight j * (β j + ∑ k, ∑ b : A k, M.transition k b j * x k b) := by
      rw [hT]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.mul_sum]
      congr 1
      have := hx.2 j
      linarith
    have e' : T = (∑ j, C.weight j * β j) +
        ∑ j, C.weight j * ∑ k, ∑ b : A k, M.transition k b j * x k b := by
      rw [e]; simp only [mul_add, Finset.sum_add_distrib]
    have : ∑ j, C.weight j * ∑ k, ∑ b : A k, M.transition k b j * x k b ≤ C.factor * T := by
      calc ∑ j, C.weight j * ∑ k, ∑ b : A k, M.transition k b j * x k b
            = ∑ k, ∑ b : A k, x k b * ∑ j, M.transition k b j * C.weight j := by
            simp only [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun b _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
        _ ≤ ∑ k, ∑ b : A k, x k b * (C.factor * C.weight k) :=
            Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun b _ =>
              mul_le_mul_of_nonneg_left (C.bound k b) (hx.1 k b)
        _ = C.factor * T := by
            rw [hT, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => ?_
            ring
    have e3 : ∑ j, C.weight j * β j = ∑ j, β j * C.weight j :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    linarith
  have hc := C.factor_lt_one
  have hT2 : T ≤ (∑ j, β j * C.weight j) / (1 - C.factor) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hn : ∀ j (b : A j), 0 ≤ C.weight j * x j b := fun j b =>
    mul_nonneg (C.weight_pos j).le (hx.1 j b)
  have h3 : C.weight i * x i a ≤ T :=
    calc C.weight i * x i a ≤ ∑ b : A i, C.weight i * x i b :=
          Finset.single_le_sum (f := fun b => C.weight i * x i b) (fun b _ => hn i b) (Finset.mem_univ a)
      _ ≤ T := Finset.single_le_sum (f := fun j => ∑ b : A j, C.weight j * x j b)
          (fun j _ => Finset.sum_nonneg fun b _ => hn j b) (Finset.mem_univ i)
  rw [le_div_iff₀ (C.weight_pos i)]
  linarith

lemma kc_P_compact (M : FiniteMDP E A) (C : Contraction M) (β : E → ℝ) (hβ : ∀ i, 0 ≤ β i) :
    IsCompact (M.feasibleFrequency β) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have e : M.feasibleFrequency β =
        (⋂ i, ⋂ a : A i, {x : StationaryRule E A | 0 ≤ x i a}) ∩
        ⋂ j, {x : StationaryRule E A | (∑ a : A j, x j a) -
          (∑ i : E, ∑ a : A i, M.transition i a j * x i a) = β j} := by
      ext x; simp [feasibleFrequency]
    rw [e]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun a => ?_)
      (isClosed_iInter fun j => ?_)
    · exact isClosed_le continuous_const (by fun_prop)
    · exact isClosed_eq (by fun_prop) continuous_const
  · set B := (∑ j, β j * C.weight j) / (1 - C.factor) with hB
    have hB0 : 0 ≤ B := by
      have := C.factor_lt_one
      exact div_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hβ j) (C.weight_pos j).le)
        (by linarith)
    rw [Metric.isBounded_iff_subset_closedBall (0 : StationaryRule E A)]
    refine ⟨∑ i, B / C.weight i, fun x hx => ?_⟩
    have hR : 0 ≤ ∑ i, B / C.weight i :=
      Finset.sum_nonneg fun i _ => div_nonneg hB0 (C.weight_pos i).le
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg hR).2 fun i => (pi_norm_le_iff_of_nonneg hR).2 fun a => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hx.1 i a)]
    refine (M.kc_P_bound C β hβ x hx i a).trans ?_
    exact Finset.single_le_sum (f := fun i => B / C.weight i)
      (fun i _ => div_nonneg hB0 (C.weight_pos i).le) (Finset.mem_univ i)

lemma kc_extreme_rule_pure [∀ i, Nonempty (A i)] (M : FiniteMDP E A) (C : Contraction M) (β : E → ℝ)
    (hβ : ∀ i, 0 ≤ β i) (x : StationaryRule E A)
    (hx : x ∈ (M.feasibleFrequency β).extremePoints ℝ) :
    ∃ f : PureRule E A, ruleOfFrequency x = pureRule f := by
  have hxP : x ∈ M.feasibleFrequency β := hx.1
  let f : PureRule E A := fun j =>
    if h : ∃ c, 0 < x j c then h.choose else Classical.choice (inferInstance : Nonempty (A j))
  have hrule : ruleOfFrequency x = pureRule f := by
    funext j a
    unfold ruleOfFrequency pureRule
    by_cases hu : (∑ b, x j b) ≠ 0
    · have hex : ∃ c, 0 < x j c := by
        by_contra hc; push_neg at hc
        exact hu (le_antisymm (Finset.sum_nonpos fun c _ => hc c)
          (Finset.sum_nonneg fun c _ => hxP.1 j c))
      have hf : f j = hex.choose := by simp only [f, dif_pos hex]
      set c0 := hex.choose with hc0
      have hc0pos : 0 < x j c0 := hex.choose_spec
      have hzero : ∀ c, c ≠ c0 → x j c = 0 := by
        intro c hc
        by_contra hne
        have hpos : 0 < x j c := lt_of_le_of_ne (hxP.1 j c) (Ne.symm hne)
        exact hc (M.kc_extreme_single β hβ x hx j c c0 hpos hc0pos)
      have hsum : ∑ b, x j b = x j c0 :=
        Finset.sum_eq_single c0 (fun c _ hc => hzero c hc) (fun h => absurd (Finset.mem_univ _) h)
      rw [dif_pos hu, hf, hsum]
      by_cases hac : a = c0
      · subst hac; rw [if_pos rfl]; exact div_self hc0pos.ne'
      · rw [if_neg hac, hzero a hac, zero_div]
    · have hex : ¬ ∃ c, 0 < x j c := by
        push_neg at hu
        rintro ⟨c, hc⟩
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => hxP.1 j c)).1 hu c (Finset.mem_univ c)
        linarith
      have hf : f j = Classical.choice (inferInstance : Nonempty (A j)) := by simp only [f, dif_neg hex]
      rw [dif_neg hu, hf]
  exact ⟨f, hrule⟩


lemma kc_occ_eq (M : FiniteMDP E A) (C : Contraction M) (β : E → ℝ) (hβ : ∀ i, 0 ≤ β i)
    (q : StationaryRule E A) (hq : IsStationaryRule q) (j : E) :
    (∑ a, M.frequency β (stationaryPolicy q) j a) -
      ∑ i, (∑ a, M.frequency β (stationaryPolicy q) i a) * M.stationaryTransition q i j = β j := by
  have h := (M.kc_frequency_mem C β hβ _ (kc_stationary_isPolicy q hq)).2 j
  rw [← h]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [stationaryTransition, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [M.kc_stat_rep β q hq i a]
  ring

open Matrix in
lemma kc_isUnit (M : FiniteMDP E A) (C : Contraction M) (q : StationaryRule E A) (hq : IsStationaryRule q) :
    IsUnit (1 - M.stationaryTransition q).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  apply hv0
  funext j
  refine M.kc_unique C q hq v (fun j => ?_) j
  have := congrFun hv j
  rw [Matrix.vecMul_sub, Matrix.vecMul_one] at this
  simp only [Pi.sub_apply, Pi.zero_apply, Matrix.vecMul, dotProduct, stationaryTransition,
    Matrix.of_apply] at this
  rw [sub_eq_zero.1 this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

open Matrix in
lemma kc_statFreq_eq (M : FiniteMDP E A) (C : Contraction M) (β : E → ℝ) (hβ : ∀ i, 0 ≤ β i)
    (q : StationaryRule E A) (hq : IsStationaryRule q) :
    M.stationaryFrequency β q = M.frequency β (stationaryPolicy q) := by
  set U : E → ℝ := fun j => ∑ a, M.frequency β (stationaryPolicy q) j a with hU
  have hvec : U ᵥ* (1 - M.stationaryTransition q) = β := by
    funext j
    rw [Matrix.vecMul_sub, Matrix.vecMul_one]
    simp only [Pi.sub_apply, Matrix.vecMul, dotProduct]
    exact M.kc_occ_eq C β hβ q hq j
  have hinv : β ᵥ* (1 - M.stationaryTransition q)⁻¹ = U := by
    rw [← hvec, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (M.kc_isUnit C q hq), Matrix.vecMul_one]
  funext i a
  unfold stationaryFrequency
  rw [M.kc_stat_rep β q hq i a]
  congr 1
  have := congrFun hinv i
  simp only [Matrix.vecMul, dotProduct] at this
  rw [this]


/-- advantage of action `a` at `j` relative to `v` -/
def kcAdv (M : FiniteMDP E A) (v : E → ℝ) (j : E) (a : A j) : ℝ :=
  M.reward j a + (∑ k, M.transition j a k * v k) - v j

lemma kc_reward_identity (M : FiniteMDP E A) (β : E → ℝ) (y : StationaryRule E A)
    (hy : y ∈ M.feasibleFrequency β) (v : E → ℝ) :
    M.frequencyReward y = (∑ j, β j * v j) + ∑ j, ∑ a : A j, y j a * M.kcAdv v j a := by
  have e1 : ∑ j, β j * v j = ∑ j, v j * (∑ a : A j, y j a) -
      ∑ k, ∑ b : A k, y k b * ∑ j, M.transition k b j * v j := by
    have : ∀ j, β j * v j = v j * (∑ a : A j, y j a) -
        v j * ∑ i : E, ∑ a : A i, M.transition i a j * y i a := by
      intro j; rw [← hy.2 j]; ring
    simp only [this, Finset.sum_sub_distrib]
    congr 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e1]
  unfold frequencyReward kcAdv
  have e2 : ∀ j, v j * ∑ a : A j, y j a = ∑ a : A j, y j a * v j := fun j => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  simp only [e2, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have e3 : ∑ j, ∑ a : A j, M.reward j a * y j a = ∑ j, ∑ a : A j, y j a * M.reward j a :=
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => mul_comm _ _
  rw [e3]; ring

lemma kc_occ_ge (M : FiniteMDP E A) (β : E → ℝ) (y : StationaryRule E A)
    (hy : y ∈ M.feasibleFrequency β) (j : E) : β j ≤ ∑ a, y j a := by
  have h := hy.2 j
  have h0 : 0 ≤ ∑ i : E, ∑ a : A i, M.transition i a j * y i a :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ =>
      mul_nonneg (M.transition_nonneg _ _ _) (hy.1 i a)
  linarith

/-- point mass initial distribution -/
noncomputable def kcDelta (i : E) : E → ℝ := fun k => if k = i then 1 else 0

lemma kcDelta_nonneg (i : E) : ∀ k, 0 ≤ kcDelta i k := by
  intro k; unfold kcDelta; split_ifs <;> norm_num

lemma kc_tr_eq (M : FiniteMDP E A) (C : Contraction M) (π : Policy E A) (hπ : IsPolicy π) (i : E) :
    M.totalReward π i = M.frequencyReward (M.frequency (kcDelta i) π) := by
  have hY : ∀ n j a, M.kcY (kcDelta i) π n j a = M.stateActionProbability π i j a n := by
    intro n j a; unfold kcY kcDelta; simp
  have hs := M.kcY_summable C (kcDelta i) (kcDelta_nonneg i) π hπ
  unfold totalReward frequencyReward
  simp only [kc_frequency_eq]
  simp only [← hY]
  rw [Summable.tsum_finsetSum (fun j _ => summable_sum fun a _ => (hs j a).mul_right _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Summable.tsum_finsetSum (fun a _ => (hs j a).mul_right _)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [tsum_mul_right, mul_comm]

lemma kc_tr_identity (M : FiniteMDP E A) (C : Contraction M) (π : Policy E A) (hπ : IsPolicy π)
    (i : E) (v : E → ℝ) :
    M.totalReward π i = v i + ∑ j, ∑ a : A j,
      M.frequency (kcDelta i) π j a * M.kcAdv v j a := by
  rw [M.kc_tr_eq C π hπ i, M.kc_reward_identity (kcDelta i) _
    (M.kc_frequency_mem C _ (kcDelta_nonneg i) π hπ) v]
  congr 1
  unfold kcDelta; simp

lemma kc_tr_le (M : FiniteMDP E A) (C : Contraction M) (w : E → ℝ) (hw : M.IsSuperharmonic w)
    (π : Policy E A) (hπ : IsPolicy π) (i : E) : M.totalReward π i ≤ w i := by
  rw [M.kc_tr_identity C π hπ i w]
  have hP := M.kc_frequency_mem C _ (kcDelta_nonneg i) π hπ
  have : ∑ j, ∑ a : A j, M.frequency (kcDelta i) π j a * M.kcAdv w j a ≤ 0 :=
    Finset.sum_nonpos fun j _ => Finset.sum_nonpos fun a _ =>
      mul_nonpos_of_nonneg_of_nonpos (hP.1 j a) (by unfold kcAdv; linarith [hw j a])
  linarith

lemma kc_pure_stat (f : PureRule E A) : IsStationaryRule (pureRule f) := by
  refine ⟨fun i a => ?_, fun i => ?_⟩
  · unfold pureRule; split_ifs <;> norm_num
  · unfold pureRule; simp

lemma kc_stat_sum_adv (M : FiniteMDP E A) (C : Contraction M) (β : E → ℝ) (hβ : ∀ i, 0 ≤ β i)
    (q : StationaryRule E A) (hq : IsStationaryRule q) (v : E → ℝ) :
    ∑ j, ∑ a : A j, M.frequency β (stationaryPolicy q) j a * M.kcAdv v j a =
      ∑ j, (∑ a, M.frequency β (stationaryPolicy q) j a) * ∑ a : A j, q j a * M.kcAdv v j a := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [M.kc_stat_rep β q hq j a]; ring

lemma kc_pure_sum (f : PureRule E A) (j : E) (g : A j → ℝ) :
    ∑ a : A j, pureRule f j a * g a = g (f j) := by
  unfold pureRule; simp

lemma kc_tr_pure (M : FiniteMDP E A) (C : Contraction M) (f : PureRule E A) (v : E → ℝ)
    (hv : ∀ j, M.kcAdv v j (f j) = 0) (i : E) : M.totalReward (purePolicy f) i = v i := by
  have hq := kc_pure_stat f
  show M.totalReward (stationaryPolicy (pureRule f)) i = v i
  rw [M.kc_tr_identity C _ (kc_stationary_isPolicy _ hq) i v]
  have := M.kc_stat_sum_adv C (kcDelta i) (kcDelta_nonneg i) _ hq v
  rw [this]
  simp [kc_pure_sum, hv]

open Matrix in
lemma kc_exists_solution (M : FiniteMDP E A) (C : Contraction M) (q : StationaryRule E A)
    (hq : IsStationaryRule q) : ∃ v : E → ℝ, ∀ j, ∑ a : A j, q j a * M.kcAdv v j a = 0 := by
  set T := 1 - M.stationaryTransition q
  refine ⟨T⁻¹ *ᵥ M.stationaryReward q, fun j => ?_⟩
  have h : T *ᵥ (T⁻¹ *ᵥ M.stationaryReward q) = M.stationaryReward q := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (M.kc_isUnit C q hq), Matrix.one_mulVec]
  set v := T⁻¹ *ᵥ M.stationaryReward q
  have hj := congrFun h j
  simp only [T, Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.one_apply, stationaryTransition,
    Matrix.of_apply, stationaryReward, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at hj
  unfold kcAdv
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hq.2 j, one_mul]
  have e : ∑ a : A j, q j a * ∑ k, M.transition j a k * v k = ∑ k, (∑ a : A j, q j a * M.transition j a k) * v k := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [e]
  have e2 : ∑ a : A j, q j a * M.reward j a = M.stationaryReward q j := rfl
  linarith

end FiniteMDP

open FiniteMDP in
theorem lop_core
    {E : Type} [Fintype E] [Nonempty E]
    {A : E → Type} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (M : FiniteMDP E A) (C : Contraction M)
    (β : E → ℝ) (hβ : ∀ i, 0 < β i) :
    (∃ x : StationaryRule E A, x ∈ M.feasibleFrequency β ∧
      ∀ y : StationaryRule E A, y ∈ M.feasibleFrequency β →
        M.frequencyReward y ≤ M.frequencyReward x) ∧
    (∀ x : StationaryRule E A, x ∈ M.feasibleFrequency β →
      (∀ y : StationaryRule E A, y ∈ M.feasibleFrequency β →
        M.frequencyReward y ≤ M.frequencyReward x) →
      ∀ f : PureRule E A, (∀ i, 0 < x i (f i)) →
        ∀ π : Policy E A, IsPolicy π →
          ∀ i, M.totalReward π i ≤ M.totalReward (purePolicy f) i) := by
  have hβ0 : ∀ i, 0 ≤ β i := fun i => (hβ i).le
  constructor
  · have hcomp := M.kc_P_compact C β hβ0
    let f0 : PureRule E A := fun j => Classical.choice inferInstance
    have hne : (M.feasibleFrequency β).Nonempty :=
      ⟨_, M.kc_frequency_mem C β hβ0 _ (kc_stationary_isPolicy _ (kc_pure_stat f0))⟩
    have hcont : Continuous (fun x : StationaryRule E A => M.frequencyReward x) := by
      unfold frequencyReward; fun_prop
    obtain ⟨x, hx, hmax⟩ := hcomp.exists_isMaxOn hne hcont.continuousOn
    exact ⟨x, hx, fun y hy => hmax hy⟩
  · intro x hx hopt f hf π hπ i
    set q := ruleOfFrequency x with hqdef
    have hq : IsStationaryRule q := M.kc_rule_stat β x hx
    obtain ⟨v, hv⟩ := M.kc_exists_solution C q hq
    have hxr := M.kc_P_rep β x hx
    have hRx : M.frequencyReward x = ∑ j, β j * v j := by
      rw [M.kc_reward_identity β x hx v]
      have : ∑ j, ∑ a : A j, x j a * M.kcAdv v j a = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        have e : ∑ a : A j, x j a * M.kcAdv v j a = (∑ b, x j b) * ∑ a : A j, q j a * M.kcAdv v j a := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_
          rw [hxr j a]; ring
        rw [e, hv j, mul_zero]
      rw [this, add_zero]
    have hadv : ∀ j (a : A j), M.kcAdv v j a ≤ 0 := by
      intro i0 a0
      by_contra hpos
      push_neg at hpos
      let δ : A i0 → ℝ := fun b => if b = a0 then 1 else 0
      let q' : StationaryRule E A := Function.update q i0 δ
      have hq' : IsStationaryRule q' := by
        refine ⟨fun j b => ?_, fun j => ?_⟩
        · by_cases hj : j = i0
          · subst hj; simp only [q', Function.update_self, δ]; split_ifs <;> norm_num
          · simp only [q', Function.update_of_ne hj]; exact hq.1 j b
        · by_cases hj : j = i0
          · subst hj; simp [q', Function.update_self, δ]
          · simp only [q', Function.update_of_ne hj]; exact hq.2 j
      have hyP := M.kc_frequency_mem C β hβ0 _ (kc_stationary_isPolicy _ hq')
      have hR := M.kc_reward_identity β _ hyP v
      rw [M.kc_stat_sum_adv C β hβ0 q' hq' v] at hR
      have hterm : ∀ j, (∑ a, M.frequency β (stationaryPolicy q') j a) *
          ∑ a : A j, q' j a * M.kcAdv v j a =
          if j = i0 then (∑ a, M.frequency β (stationaryPolicy q') j a) * (if h : j = i0 then
            M.kcAdv v i0 a0 else 0) else 0 := by
        intro j
        by_cases hj : j = i0
        · subst hj
          simp [q', Function.update_self, δ]
        · simp only [if_neg hj, q', Function.update_of_ne hj, hv j, mul_zero]
      rw [Finset.sum_congr rfl fun j _ => hterm j] at hR
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, dif_pos] at hR
      have hocc := M.kc_occ_ge β _ hyP i0
      have hpos2 : 0 < (∑ a, M.frequency β (stationaryPolicy q') i0 a) * M.kcAdv v i0 a0 :=
        mul_pos (by linarith [hβ i0]) hpos
      have := hopt _ hyP
      linarith
    have hsuper : M.IsSuperharmonic v := by
      intro j a; have := hadv j a; unfold kcAdv at this; linarith
    have hfadv : ∀ j, M.kcAdv v j (f j) = 0 := by
      intro j
      have hz := (Finset.sum_eq_zero_iff_of_nonpos (fun a _ =>
        mul_nonpos_of_nonneg_of_nonpos (hq.1 j a) (hadv j a))).1 (hv j) (f j) (Finset.mem_univ _)
      have hqpos : 0 < q j (f j) := by
        have hU : 0 < ∑ b, x j b := lt_of_lt_of_le (hf j)
          (Finset.single_le_sum (f := fun b => x j b) (fun b _ => hx.1 j b) (Finset.mem_univ (f j)))
        have := hxr j (f j)
        by_contra hle
        push_neg at hle
        have : x j (f j) ≤ 0 := by rw [this]; exact mul_nonpos_of_nonneg_of_nonpos hU.le hle
        linarith [hf j]
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h hqpos.ne'
      · exact h
    rw [M.kc_tr_pure C f v hfadv i]
    exact M.kc_tr_le C v hsuper π hπ i

end KallenbergLP.Contracting

open KallenbergLP.Contracting


theorem solution
    {E : Type} [Fintype E] [Nonempty E]
    {A : E → Type} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (M : FiniteMDP E A) (_C : Contraction M)
    (β : E → ℝ) (hβ : ∀ i, 0 < β i) :
    (∃ x : StationaryRule E A, x ∈ M.feasibleFrequency β ∧
      ∀ y : StationaryRule E A, y ∈ M.feasibleFrequency β →
        M.frequencyReward y ≤ M.frequencyReward x) ∧
    (∀ x : StationaryRule E A, x ∈ M.feasibleFrequency β →
      (∀ y : StationaryRule E A, y ∈ M.feasibleFrequency β →
        M.frequencyReward y ≤ M.frequencyReward x) →
      ∀ f : PureRule E A, (∀ i, 0 < x i (f i)) →
        ∀ π : Policy E A, IsPolicy π →
          ∀ i, M.totalReward π i ≤ M.totalReward (purePolicy f) i) := by
  exact lop_core M _C β hβ
