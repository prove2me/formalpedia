-- Prove2me | solution 1 for GeneralizedUniformServer.UnitWeights.step_movement
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T13:37:51.624537+00:00
-- url     : https://prove2.me/submissions/b4d5fde2-3003-4722-9ce7-7de2ab7ed1ea

import Definitions.Def_GeneralizedUniformServer_UnitWeights_Algorithm
import Mathlib
import Theorems.Thm_GeneralizedUniformServer_UnitWeights_configuration_law
section
open scoped NNReal

noncomputable section

namespace GeneralizedUniformServer.Dev.StepMovement

open GeneralizedUniformServer.UnitWeights

variable {k : ℕ} {M : Fin k → Type*}

lemma weights_append (a : Config M) (ρ : List (Config M)) (r : Config M) :
    weights a (ρ ++ [r]) = update r (weights a ρ) := by
  simp [weights, List.foldl_append]

lemma total_eq (ϕ : Config M →₀ ℝ≥0) : ϕ.sum (fun _ v => v) = ∑ x ∈ ϕ.support, ϕ x := rfl

open Classical in
lemma total_update_eq [NeZero k] (r : Config M) (ϕ : Config M →₀ ℝ≥0) :
    (update r ϕ).sum (fun _ v => v) =
      ∑ x ∈ ϕ.support.filter (fun x => Serves x r), ϕ x +
      (∑ x ∈ ϕ.support.filter (fun x => ¬ Serves x r), ϕ x) / 2 := by
  classical
  unfold update
  rw [Finsupp.sum_add_index' (by simp) (by simp), ← Finsupp.sum_finsetSum_index (by simp) (by simp)]
  have h1 : (ϕ.filter (fun y => Serves y r)).sum (fun _ v => v)
      = ∑ x ∈ ϕ.support.filter (fun x => Serves x r), ϕ x := by
    rw [total_eq, Finsupp.support_filter]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finsupp.filter_apply, if_pos (Finset.mem_filter.mp hx).2]
  have h2 : ∀ x ∈ ϕ.support.filter (fun x => ¬ Serves x r),
      (∑ i : Fin k, Finsupp.single (repair x r i) (ϕ x / (2 * (k : ℝ≥0)))).sum (fun _ v => v)
        = ϕ x / 2 := by
    intro x _
    rw [← Finsupp.sum_finsetSum_index (by simp) (by simp)]
    simp only [Finsupp.sum_single_index]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hk : (k : ℝ≥0) ≠ 0 := by exact_mod_cast NeZero.ne k
    field_simp
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_div]

open Classical in
lemma total_split (ϕ : Config M →₀ ℝ≥0) (r : Config M) :
    ϕ.sum (fun _ v => v) =
      ∑ x ∈ ϕ.support.filter (fun x => Serves x r), ϕ x +
      ∑ x ∈ ϕ.support.filter (fun x => ¬ Serves x r), ϕ x := by
  classical
  rw [total_eq, Finset.sum_filter_add_sum_filter_not]

lemma totalWeight_nil (a : Config M) : totalWeight a [] = 1 := by
  simp [totalWeight, weights, Finsupp.sum_single_index]

open Classical in
lemma totalWeight_pos [NeZero k] (a : Config M) (ρ : List (Config M)) :
    0 < totalWeight a ρ := by
  induction ρ using List.reverseRecOn with
  | nil => simp [totalWeight_nil]
  | append_singleton ρ r ih =>
    unfold totalWeight at *
    rw [weights_append, total_update_eq, total_split (weights a ρ) r] at *
    set S := ∑ x ∈ (weights a ρ).support.filter (fun x => Serves x r), (weights a ρ) x
    set N := ∑ x ∈ (weights a ρ).support.filter (fun x => ¬ Serves x r), (weights a ρ) x
    have : (S + N) / 2 ≤ S + N / 2 := by
      rw [add_div]; gcongr; exact div_le_self (zero_le) (by norm_num)
    exact lt_of_lt_of_le (by positivity) this

lemma traj_ne_nil [NeZero k] (A : OnlineAlg M) (a : Config M) (ρ : List (Config M)) (t : ℕ)
    (p : List (Config M)) (hp : p ∈ (trajLaw A a ρ t).support) : p ≠ [] := by
  induction t generalizing p with
  | zero => simp [trajLaw] at hp; simp [hp]
  | succ t ih =>
    rw [trajLaw, PMF.mem_support_bind_iff] at hp
    obtain ⟨q, hq, hp⟩ := hp
    split_ifs at hp with h
    · rw [PMF.mem_support_map_iff] at hp
      obtain ⟨y, -, rfl⟩ := hp
      simp
    · rw [PMF.support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ih _ hq

/-- Expectation of `g` under a PMF, in `ℝ≥0∞`. -/
def E {α : Type*} (μ : PMF α) (g : α → ENNReal) : ENNReal := ∑' p, μ p * g p

lemma E_bind {α β : Type*} (μ : PMF α) (f : α → PMF β) (g : β → ENNReal) :
    E (μ.bind f) g = E μ (fun a => E (f a) g) := by
  unfold E
  simp_rw [PMF.bind_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  congr 1
  ext a
  simp_rw [← ENNReal.tsum_mul_left, mul_assoc]

lemma E_pure {α : Type*} (b : α) (g : α → ENNReal) : E (PMF.pure b) g = g b := by
  classical
  simp [E, PMF.pure_apply]

lemma E_map {α β : Type*} (h : α → β) (μ : PMF α) (g : β → ENNReal) :
    E (μ.map h) g = E μ (fun a => g (h a)) := by
  have : μ.map h = μ.bind (PMF.pure ∘ h) := rfl
  rw [this, E_bind]
  simp [E_pure]

lemma E_const {α : Type*} (μ : PMF α) (c : ENNReal) : E μ (fun _ => c) = c := by
  unfold E
  rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

lemma E_mono {α : Type*} (μ : PMF α) {f g : α → ENNReal} (h : ∀ a, f a ≤ g a) :
    E μ f ≤ E μ g :=
  ENNReal.tsum_le_tsum fun a => by gcongr; exact h a

lemma traj_succ_E (A : OnlineAlg M) (a : Config M) (ρ : List (Config M)) (t : ℕ)
    (ht : t < ρ.length) (g : List (Config M) → ENNReal) :
    E (trajLaw A a ρ (t + 1)) g =
      E (trajLaw A a ρ t) (fun p => E (A (ρ.take t) (p.headD a) ρ[t]) (fun y => g (y :: p))) := by
  rw [trajLaw, E_bind]
  congr 1
  ext p
  rw [dif_pos ht, E_map]

lemma dist_le (x y : Config M) : UnitWeights.dist x y ≤ k := by
  classical
  unfold UnitWeights.dist
  calc _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_filter_le _ _
    _ = k := by simp

lemma dist_repair (x r : Config M) (i : Fin k) (h : x i ≠ r i) : UnitWeights.dist x (repair x r i) = 1 := by
  classical
  unfold UnitWeights.dist
  rw [Finset.card_eq_one]
  refine ⟨i, Finset.ext fun j => ?_⟩
  rw [Finset.mem_filter, Finset.mem_singleton]
  by_cases hj : j = i
  · subst hj; simp [repair, h]
  · simp [repair, hj, Function.update_of_ne]

open Classical in
lemma inner_le [NeZero k] (a : Config M) (hist : List (Config M)) (x r : Config M) :
    E (hwangAlg a hist x r) (fun y => (UnitWeights.dist x y : ENNReal)) ≤
      if Serves x r then 0 else (2⁻¹ : ENNReal) * (1 + (k : ENNReal)) := by
  classical
  by_cases hs : Serves x r
  · rw [if_pos hs]
    unfold hwangAlg
    rw [if_pos hs, E_pure]
    simp [UnitWeights.dist]
  · rw [if_neg hs]
    unfold hwangAlg
    rw [if_neg hs, E_bind]
    unfold E
    rw [tsum_fintype, Fintype.sum_bool]
    simp only [PMF.uniformOfFintype_apply, if_true, Bool.false_eq_true, if_false]
    have h1 : E ((PMF.uniformOfFintype (Fin k)).map (repair x r)) (fun y => (UnitWeights.dist x y : ENNReal))
        = 1 := by
      rw [E_map]
      have : ∀ i : Fin k, ((UnitWeights.dist x (repair x r i) : ℕ) : ENNReal) = 1 := by
        intro i
        rw [dist_repair x r i (fun h => hs ⟨i, h⟩)]; simp
      simp_rw [this]
      rw [E_const]
    have h2 : E (normalizedLaw a (hist ++ [r]) x) (fun y => (UnitWeights.dist x y : ENNReal)) ≤ k := by
      calc _ ≤ E (normalizedLaw a (hist ++ [r]) x) (fun _ => (k : ENNReal)) :=
            E_mono _ (fun y => by exact_mod_cast dist_le x y)
        _ = k := E_const _ _
    simp only [Fintype.card_bool]
    have : ((2 : ℕ) : ENNReal)⁻¹ = 2⁻¹ := by simp
    rw [this, ← mul_add]
    exact mul_le_mul_right (add_le_add h1.le h2) _

lemma take_succ' (ρ : List (Config M)) (s : ℕ) (hs : s < ρ.length) :
    ρ.take (s + 1) = ρ.take s ++ [ρ[s]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hs]
  rfl

lemma stepA [NeZero k] (a : Config M) (ρ : List (Config M)) (s : ℕ) (hs : s < ρ.length) :
    E (algTraj a ρ (s + 1)) (fun p => (lastStepCost p : ENNReal)) =
      E ((algTraj a ρ s).map fun p => p.headD a)
        (fun x => E (hwangAlg a (ρ.take s) x ρ[s]) (fun y => (UnitWeights.dist x y : ENNReal))) := by
  rw [algTraj, traj_succ_E _ _ _ _ hs, E_map]
  unfold E
  refine tsum_congr fun p => ?_
  by_cases hp : (algTraj a ρ s) p = 0
  · have hp' : (trajLaw (hwangAlg a) a ρ s) p = 0 := hp
    rw [hp']; simp; exact Or.inl hp
  · have hsupp : p ∈ (trajLaw (hwangAlg a) a ρ s).support := by
      rw [PMF.mem_support_iff]; exact hp
    obtain ⟨x, q, rfl⟩ := List.exists_cons_of_ne_nil (traj_ne_nil _ _ _ _ p hsupp)
    simp [lastStepCost]
    rfl

lemma real_ineq (S N K Φ' : ℝ) (hS : 0 ≤ S) (_hN : 0 ≤ N) (hK : 0 ≤ K)
    (hΦ : 0 < S + N) (hΦ' : Φ' = S + N / 2) :
    N / (S + N) * (K / 2) ≤ K * Real.log ((S + N) / Φ') := by
  have hp : 0 < Φ' := by rw [hΦ']; linarith
  have h1 : Real.log (Φ' / (S + N)) ≤ Φ' / (S + N) - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Φ' / (S + N) - 1 = -(N / 2 / (S + N)) := by
    rw [hΦ']; field_simp; ring
  have h3 : Real.log ((S + N) / Φ') = - Real.log (Φ' / (S + N)) := by
    rw [← Real.log_inv, inv_div]
  have h4 : N / 2 / (S + N) ≤ Real.log ((S + N) / Φ') := by linarith
  have h5 : N / (S + N) * (K / 2) = K * (N / 2 / (S + N)) := by field_simp
  rw [h5]
  exact mul_le_mul_of_nonneg_left h4 hK

open Classical in
lemma main [NeZero k] (a : Config M) (ρ : List (Config M)) (s : ℕ) (hs : s < ρ.length) :
    ∑' p : List (Config M), algTraj a ρ (s + 1) p * (lastStepCost p : ENNReal) ≤
      ENNReal.ofReal (((k : ℝ) + 1) *
        Real.log ((totalWeight a (ρ.take s) : ℝ) / (totalWeight a (ρ.take (s + 1)) : ℝ))) := by
  set r := ρ[s] with hr
  set ϕ := weights a (ρ.take s) with hϕ
  set S := ∑ x ∈ ϕ.support.filter (fun x => Serves x r), ϕ x with hSdef
  set N := ∑ x ∈ ϕ.support.filter (fun x => ¬ Serves x r), ϕ x with hNdef
  have hΦ : totalWeight a (ρ.take s) = S + N := total_split ϕ r
  have hΦ' : totalWeight a (ρ.take (s + 1)) = S + N / 2 := by
    unfold totalWeight
    rw [take_succ' ρ s hs, weights_append, total_update_eq]
  have hpos : 0 < S + N := hΦ ▸ totalWeight_pos a _
  have hne : ((S + N : ℝ≥0) : ENNReal) ≠ 0 := by exact_mod_cast hpos.ne'
  have hA := stepA a ρ s hs
  have hB : E (algTraj a ρ (s + 1)) (fun p => (lastStepCost p : ENNReal)) ≤
      ∑' x, (ϕ x : ENNReal) / ((S + N : ℝ≥0) : ENNReal) *
        (if Serves x r then 0 else (2⁻¹ : ENNReal) * (1 + (k : ENNReal))) := by
    rw [hA]
    unfold E
    refine ENNReal.tsum_le_tsum fun x => ?_
    rw [configuration_law a ρ s hs.le x, ← hΦ]
    gcongr
    exact inner_le a _ x r
  have hC : (∑' x, (ϕ x : ENNReal) / ((S + N : ℝ≥0) : ENNReal) *
        (if Serves x r then 0 else (2⁻¹ : ENNReal) * (1 + (k : ENNReal)))) =
      ((N / (S + N) * ((1 + k) / 2) : ℝ≥0) : ENNReal) := by
    rw [tsum_eq_sum (s := ϕ.support)]
    · rw [← Finset.sum_filter_add_sum_filter_not ϕ.support (fun x => Serves x r)]
      have e1 : ∀ x ∈ ϕ.support.filter (fun x => Serves x r),
          (ϕ x : ENNReal) / ((S + N : ℝ≥0) : ENNReal) *
            (if Serves x r then 0 else (2⁻¹ : ENNReal) * (1 + (k : ENNReal))) = 0 := by
        intro x hx
        rw [if_pos (Finset.mem_filter.mp hx).2, mul_zero]
      have e2 : ∀ x ∈ ϕ.support.filter (fun x => ¬ Serves x r),
          (ϕ x : ENNReal) / ((S + N : ℝ≥0) : ENNReal) *
            (if Serves x r then 0 else (2⁻¹ : ENNReal) * (1 + (k : ENNReal))) =
          (ϕ x : ENNReal) * (((S + N : ℝ≥0) : ENNReal)⁻¹ * ((2⁻¹ : ENNReal) * (1 + (k : ENNReal)))) := by
        intro x hx
        rw [if_neg (Finset.mem_filter.mp hx).2, div_eq_mul_inv, mul_assoc]
      rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_const_zero, zero_add,
        ← Finset.sum_mul, ← ENNReal.ofNNReal_finsetSum, ← hNdef]
      rw [ENNReal.coe_mul, ENNReal.coe_div (by simpa using hpos.ne'), ENNReal.coe_div (by norm_num),
        div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
      push_cast
      simp [mul_comm, mul_left_comm, mul_assoc]
    · intro x hx
      rw [Finsupp.notMem_support_iff.mp hx]; simp
  show E _ _ ≤ _
  refine hB.trans (hC.le.trans ?_)
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  rw [hΦ, hΦ']
  have := real_ineq (S : ℝ) (N : ℝ) ((k : ℝ) + 1) _ S.2 N.2 (by positivity) (by exact_mod_cast hpos)
    rfl
  push_cast
  convert this using 2
  ring

end GeneralizedUniformServer.Dev.StepMovement

namespace GeneralizedUniformServer

open GeneralizedUniformServer.UnitWeights

theorem chk_step_movement {k : ℕ} [NeZero k] {M : Fin k → Type*}
    (a : Config M) (ρ : List (Config M)) (t : ℕ) (ht₁ : 1 ≤ t) (ht : t ≤ ρ.length) :
    ∑' p : List (Config M), algTraj a ρ t p * (lastStepCost p : ENNReal) ≤
      ENNReal.ofReal (((k : ℝ) + 1) *
        Real.log ((totalWeight a (ρ.take (t - 1)) : ℝ) / (totalWeight a (ρ.take t) : ℝ))) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simpa using Dev.StepMovement.main a ρ s (by omega)

end GeneralizedUniformServer
end
end

theorem solution : type_of% @GeneralizedUniformServer.chk_step_movement := @GeneralizedUniformServer.chk_step_movement
