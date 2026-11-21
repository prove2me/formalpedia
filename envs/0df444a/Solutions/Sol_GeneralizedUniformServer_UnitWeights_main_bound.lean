-- Prove2me | solution 1 for GeneralizedUniformServer.UnitWeights.main_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T13:27:38.500416+00:00
-- url     : https://prove2.me/submissions/754ed37d-48a1-474a-99ab-075cc82780fc

import Definitions.Def_GeneralizedUniformServer_UnitWeights_Algorithm
import Mathlib
import Theorems.Thm_GeneralizedUniformServer_UnitWeights_step_movement
import Theorems.Thm_GeneralizedUniformServer_UnitWeights_lazy_conversion
import Theorems.Thm_GeneralizedUniformServer_UnitWeights_lazy_weight

section
open scoped NNReal

noncomputable section

namespace GeneralizedUniformServer.Dev.Main

open GeneralizedUniformServer.UnitWeights

variable {k : ℕ} {M : Fin k → Type*}

lemma weights_append (a : Config M) (ρ : List (Config M)) (r : Config M) :
    weights a (ρ ++ [r]) = update r (weights a ρ) := by
  simp [weights, List.foldl_append]

lemma update_support_serves (r : Config M) (ϕ : Config M →₀ ℝ≥0) (y : Config M)
    (hy : y ∈ (update r ϕ).support) : Serves y r := by
  classical
  by_contra hs
  rw [Finsupp.mem_support_iff] at hy
  apply hy
  unfold update
  rw [Finsupp.add_apply, Finsupp.filter_apply, if_neg hs, zero_add, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro x _
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [Finsupp.single_apply, if_neg]
  intro h
  apply hs
  exact ⟨i, by rw [← h]; simp [repair]⟩

lemma total_eq (ϕ : Config M →₀ ℝ≥0) : ϕ.sum (fun _ v => v) = ∑ x ∈ ϕ.support, ϕ x := rfl

lemma total_update_le [NeZero k] (r : Config M) (ϕ : Config M →₀ ℝ≥0) :
    (update r ϕ).sum (fun _ v => v) ≤ ϕ.sum (fun _ v => v) := by
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
        ≤ ϕ x := by
    intro x _
    rw [← Finsupp.sum_finsetSum_index (by simp) (by simp)]
    simp only [Finsupp.sum_single_index]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hk : (k : ℝ≥0) ≠ 0 := by exact_mod_cast NeZero.ne k
    calc (k : ℝ≥0) * (ϕ x / (2 * k)) = ϕ x / 2 := by
          field_simp
      _ ≤ ϕ x := by exact div_le_self (zero_le) (by norm_num)
  rw [h1, total_eq, ← Finset.sum_filter_add_sum_filter_not ϕ.support (fun x => Serves x r)]
  exact add_le_add le_rfl (Finset.sum_le_sum h2)

lemma totalWeight_append_le [NeZero k] (a : Config M) (ρ : List (Config M)) (r : Config M) :
    totalWeight a (ρ ++ [r]) ≤ totalWeight a ρ := by
  unfold totalWeight
  rw [weights_append]
  exact total_update_le _ _

lemma totalWeight_nil (a : Config M) : totalWeight a [] = 1 := by
  simp [totalWeight, weights, Finsupp.sum_single_index]

lemma exists_solution [NeZero k] (a : Config M) (ρ : List (Config M)) :
    ∃ o : Fin (ρ.length + 1) → Config M, IsOfflineSolution ρ o ∧ o 0 = a := by
  refine ⟨Fin.cases a (fun s => ρ[s]), ?_, by simp⟩
  intro s
  simp only [Fin.cases_succ]
  exact ⟨⟨0, NeZero.pos k⟩, rfl⟩

lemma totalWeight_pos [NeZero k] (a : Config M) (ρ : List (Config M)) :
    0 < totalWeight a ρ := by
  obtain ⟨o, ho, h0⟩ := exists_solution a ρ
  obtain ⟨o', h1, h2, h3, -⟩ := lazy_conversion ρ o ho a
  obtain ⟨-, h5⟩ := lazy_weight a ρ o' h1 h2 h3
  have : 0 < ((2 * (k : ℝ≥0)) ^ numMoves ρ o')⁻¹ := by
    have : (k : ℝ≥0) ≠ 0 := by exact_mod_cast NeZero.ne k
    positivity
  exact lt_of_lt_of_le this (h5.trans (by
    obtain ⟨h4, -⟩ := lazy_weight a ρ o' h1 h2 h3
    exact h4))

lemma normalizedLaw_support [NeZero k] (a : Config M) (ρ : List (Config M)) (fb y : Config M)
    (hy : y ∈ (normalizedLaw a ρ fb).support) : y ∈ (weights a ρ).support := by
  classical
  have h : totalWeight a ρ ≠ 0 := (totalWeight_pos a ρ).ne'
  unfold normalizedLaw at hy
  rw [dif_neg h, PMF.mem_support_iff, PMF.ofFinset_apply] at hy
  rw [Finsupp.mem_support_iff]
  intro h0
  apply hy
  simp [h0]

lemma hwang_support [NeZero k] (a : Config M) (hist : List (Config M)) (x r y : Config M)
    (hy : y ∈ (hwangAlg a hist x r).support) : Serves y r := by
  classical
  unfold hwangAlg at hy
  by_cases hs : Serves x r
  · rw [if_pos hs, PMF.support_pure, Set.mem_singleton_iff] at hy
    rw [hy]; exact hs
  · rw [if_neg hs, PMF.mem_support_bind_iff] at hy
    obtain ⟨b, -, hb⟩ := hy
    cases b
    · simp only [Bool.false_eq_true, if_false] at hb
      have := normalizedLaw_support a _ _ _ hb
      rw [weights_append] at this
      exact update_support_serves _ _ _ this
    · simp only [if_true] at hb
      rw [PMF.mem_support_map_iff] at hb
      obtain ⟨i, -, rfl⟩ := hb
      exact ⟨i, by simp [repair]⟩


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

lemma E_add {α : Type*} (μ : PMF α) (f g : α → ENNReal) :
    E μ (fun a => f a + g a) = E μ f + E μ g := by
  simp [E, mul_add, ENNReal.tsum_add]

lemma E_const {α : Type*} (μ : PMF α) (c : ENNReal) : E μ (fun _ => c) = c := by
  unfold E
  rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

lemma pathCost_cons (y : Config M) (p : List (Config M)) :
    pathCost (y :: p) = lastStepCost (y :: p) + pathCost p := by
  cases p <;> simp [pathCost, lastStepCost]

lemma traj_succ_E (A : OnlineAlg M) (a : Config M) (ρ : List (Config M)) (t : ℕ)
    (ht : t < ρ.length) (g : List (Config M) → ENNReal) :
    E (trajLaw A a ρ (t + 1)) g =
      E (trajLaw A a ρ t) (fun p => E (A (ρ.take t) (p.headD a) ρ[t]) (fun y => g (y :: p))) := by
  rw [trajLaw, E_bind]
  congr 1
  ext p
  rw [dif_pos ht, E_map]

lemma cost_eq_sum (A : OnlineAlg M) (a : Config M) (ρ : List (Config M)) (t : ℕ)
    (ht : t ≤ ρ.length) :
    E (trajLaw A a ρ t) (fun p => (pathCost p : ENNReal)) =
      ∑ s ∈ Finset.range t, E (trajLaw A a ρ (s + 1)) (fun p => (lastStepCost p : ENNReal)) := by
  induction t with
  | zero => simp [trajLaw, E_pure, pathCost]
  | succ t ih =>
    have ht' : t < ρ.length := ht
    rw [Finset.sum_range_succ, ← ih ht'.le, traj_succ_E _ _ _ _ ht',
      traj_succ_E _ _ _ _ ht', ← E_add]
    congr 1
    ext p
    simp_rw [pathCost_cons, Nat.cast_add]
    rw [E_add, E_const, add_comm]

lemma expectedCost_eq [NeZero k] (a : Config M) (ρ : List (Config M)) :
    expectedCost (hwangAlg a) a ρ =
      ∑ s ∈ Finset.range ρ.length,
        ∑' p : List (Config M), algTraj a ρ (s + 1) p * (lastStepCost p : ENNReal) :=
  cost_eq_sum (hwangAlg a) a ρ ρ.length le_rfl


lemma take_succ' (ρ : List (Config M)) (s : ℕ) (hs : s < ρ.length) :
    ρ.take (s + 1) = ρ.take s ++ [ρ[s]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hs]
  rfl

lemma Phi_anti [NeZero k] (a : Config M) (ρ : List (Config M)) (s : ℕ) (hs : s < ρ.length) :
    totalWeight a (ρ.take (s + 1)) ≤ totalWeight a (ρ.take s) := by
  rw [take_succ' ρ s hs]
  exact totalWeight_append_le _ _ _

lemma opt_attained [NeZero k] (a : Config M) (ρ : List (Config M)) :
    ∃ o : Fin (ρ.length + 1) → Config M,
      IsOfflineSolution ρ o ∧ o 0 = a ∧ offlineCost ρ o = optCost a ρ := by
  obtain ⟨o, ho, h0⟩ := exists_solution a ρ
  have hne : {C : ℕ | ∃ o : Fin (ρ.length + 1) → Config M,
      IsOfflineSolution ρ o ∧ o 0 = a ∧ offlineCost ρ o = C}.Nonempty :=
    ⟨_, o, ho, h0, rfl⟩
  exact Nat.sInf_mem hne

lemma log_bound [NeZero k] (a : Config M) (ρ : List (Config M)) :
    -Real.log (totalWeight a ρ : ℝ) ≤ Real.log (2 * (k : ℝ)) * (optCost a ρ : ℝ) := by
  obtain ⟨o, ho, h0, hc⟩ := opt_attained a ρ
  obtain ⟨o', h1, h2, h3, h4⟩ := lazy_conversion ρ o ho a
  obtain ⟨hA, hB⟩ := lazy_weight a ρ o' h1 h2 h3
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  have hm : numMoves ρ o' ≤ optCost a ρ := by
    have : UnitWeights.dist a (o 0) = 0 := by simp [h0, UnitWeights.dist]
    omega
  have hpow : (((2 * (k : ℝ)) ^ numMoves ρ o')⁻¹) ≤ (totalWeight a ρ : ℝ) := by
    have := (hB.trans hA)
    exact_mod_cast this
  have hpos : (0 : ℝ) < ((2 * (k : ℝ)) ^ numMoves ρ o')⁻¹ := by positivity
  have hl := Real.log_le_log hpos hpow
  rw [Real.log_inv, Real.log_pow] at hl
  have hlog : 0 ≤ Real.log (2 * (k : ℝ)) := Real.log_nonneg (by linarith)
  have : (numMoves ρ o' : ℝ) ≤ optCost a ρ := by exact_mod_cast hm
  nlinarith

lemma cost_bound [NeZero k] (a : Config M) (ρ : List (Config M)) :
    expectedCost (hwangAlg a) a ρ ≤
      ENNReal.ofReal (((k : ℝ) + 1) * Real.log (2 * (k : ℝ)) * (optCost a ρ : ℝ)) := by
  rw [expectedCost_eq]
  have hle : ∀ s ∈ Finset.range ρ.length,
      ∑' p : List (Config M), algTraj a ρ (s + 1) p * (lastStepCost p : ENNReal) ≤
        ENNReal.ofReal (((k : ℝ) + 1) * (Real.log (totalWeight a (ρ.take s) : ℝ) -
          Real.log (totalWeight a (ρ.take (s + 1)) : ℝ))) := by
    intro s hs
    have hs' := Finset.mem_range.mp hs
    have := step_movement a ρ (s + 1) (by omega) hs'
    simp only [Nat.add_sub_cancel] at this
    have h1 : (0 : ℝ) < totalWeight a (ρ.take s) := by exact_mod_cast totalWeight_pos a _
    have h2 : (0 : ℝ) < totalWeight a (ρ.take (s + 1)) := by exact_mod_cast totalWeight_pos a _
    rwa [Real.log_div h1.ne' h2.ne'] at this
  refine (Finset.sum_le_sum hle).trans ?_
  have hnn : ∀ s ∈ Finset.range ρ.length,
      0 ≤ ((k : ℝ) + 1) * (Real.log (totalWeight a (ρ.take s) : ℝ) -
          Real.log (totalWeight a (ρ.take (s + 1)) : ℝ)) := by
    intro s hs
    have hs' := Finset.mem_range.mp hs
    have h2 : (0 : ℝ) < totalWeight a (ρ.take (s + 1)) := by exact_mod_cast totalWeight_pos a _
    have h3 : (totalWeight a (ρ.take (s + 1)) : ℝ) ≤ totalWeight a (ρ.take s) := by
      exact_mod_cast Phi_anti a ρ s hs'
    have := Real.log_le_log h2 h3
    positivity
  rw [← ENNReal.ofReal_sum_of_nonneg hnn, ← Finset.mul_sum]
  rw [Finset.sum_range_sub' (fun s => Real.log (totalWeight a (ρ.take s) : ℝ))]
  apply ENNReal.ofReal_le_ofReal
  simp only [List.take_zero, totalWeight_nil, NNReal.coe_one, Real.log_one, zero_sub,
    List.take_length]
  have := log_bound a ρ
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  nlinarith

end GeneralizedUniformServer.Dev.Main

namespace GeneralizedUniformServer

open GeneralizedUniformServer.UnitWeights

theorem chk_main_bound {k : ℕ} [NeZero k] {M : Fin k → Type*} (a : Config M) :
    ∃ A : OnlineAlg M,
      (∀ (hist : List (Config M)) (x r y : Config M), y ∈ (A hist x r).support → Serves y r) ∧
      ∀ ρ : List (Config M),
        expectedCost A a ρ ≤
          ENNReal.ofReal (((k : ℝ) + 1) * Real.log (2 * (k : ℝ)) * (optCost a ρ : ℝ)) :=
  ⟨hwangAlg a, fun hist x r y hy => Dev.Main.hwang_support a hist x r y hy,
    fun ρ => Dev.Main.cost_bound a ρ⟩

end GeneralizedUniformServer
end
end

theorem solution : type_of% @GeneralizedUniformServer.chk_main_bound := @GeneralizedUniformServer.chk_main_bound
