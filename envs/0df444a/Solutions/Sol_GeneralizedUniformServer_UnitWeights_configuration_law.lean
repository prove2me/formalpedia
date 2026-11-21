-- Prove2me | solution 1 for GeneralizedUniformServer.UnitWeights.configuration_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T13:37:51.164621+00:00
-- url     : https://prove2.me/submissions/9261484a-e0c2-4680-9566-8b44a0794860

import Mathlib
import Definitions.Def_GeneralizedUniformServer_UnitWeights_Algorithm

section
open scoped NNReal Classical

noncomputable section

namespace GeneralizedUniformServer.Dev.ConfigLaw

open GeneralizedUniformServer.UnitWeights

variable {k : ℕ} {M : Fin k → Type*}

lemma weights_append (a : Config M) (ρ : List (Config M)) (r : Config M) :
    weights a (ρ ++ [r]) = update r (weights a ρ) := by
  simp [weights, List.foldl_append]

lemma head_rec (A : OnlineAlg M) (a : Config M) (ρ : List (Config M)) (t : ℕ)
    (h : t < ρ.length) (y : Config M) :
    ((trajLaw A a ρ (t + 1)).map fun p => p.headD a) y =
      (((trajLaw A a ρ t).map fun p => p.headD a).bind fun x => A (ρ.take t) x ρ[t]) y := by
  rw [PMF.bind_map]
  have : trajLaw A a ρ (t + 1) = (trajLaw A a ρ t).bind fun p =>
      (A (ρ.take t) (p.headD a) ρ[t]).map fun y => y :: p := by
    simp only [trajLaw, dif_pos h]
  rw [this, PMF.map_bind]
  refine congrArg (fun μ : PMF (Config M) => μ y)
    (congrArg (fun f => (trajLaw A a ρ t).bind f) (funext fun p => ?_))
  show _ = A (ρ.take t) (p.headD a) ρ[t]
  rw [PMF.map_comp]
  have : ((fun q : List (Config M) => q.headD a) ∘ fun y => y :: p) = id := by
    funext y; simp
  rw [this, PMF.map_id]

lemma total_eq (ϕ : Config M →₀ ℝ≥0) : ϕ.sum (fun _ v => v) = ∑ x ∈ ϕ.support, ϕ x := rfl

/-- The non-serving mass `N`. -/
def nmass (r : Config M) (ϕ : Config M →₀ ℝ≥0) : ℝ≥0 := by
  classical
  exact ∑ x ∈ ϕ.support.filter (fun x => ¬ Serves x r), ϕ x

lemma total_split [NeZero k] (r : Config M) (ϕ : Config M →₀ ℝ≥0) :
    ϕ.sum (fun _ v => v) = (update r ϕ).sum (fun _ v => v) + nmass r ϕ / 2 := by
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
  rw [h1, Finset.sum_congr rfl h2, total_eq, nmass, Finset.sum_div]
  conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not ϕ.support (fun x => Serves x r)]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intros
  exact (add_halves _).symm

lemma nmass_le (r : Config M) (ϕ : Config M →₀ ℝ≥0) : nmass r ϕ ≤ ϕ.sum (fun _ v => v) := by
  classical
  rw [total_eq, nmass]
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

lemma totalWeight_pos [NeZero k] (a : Config M) (ρ : List (Config M)) :
    0 < totalWeight a ρ := by
  induction ρ using List.reverseRecOn with
  | nil => simp [totalWeight, weights, Finsupp.sum_single_index]
  | append_singleton ρ r ih =>
    unfold totalWeight at ih ⊢
    rw [weights_append]
    have h1 := total_split r (weights a ρ)
    have h2 := nmass_le r (weights a ρ)
    by_contra h0
    have h0' : (update r (weights a ρ)).sum (fun _ v => v) = 0 := by
      simpa using h0
    rw [h0', zero_add] at h1
    rw [h1] at ih h2
    have h3 : nmass r (weights a ρ) / 2 = 0 := by
      have h4 : nmass r (weights a ρ) ≤ nmass r (weights a ρ) / 2 := h2
      have h5 : nmass r (weights a ρ) = 0 := by
        by_contra hne
        have hp : 0 < nmass r (weights a ρ) := pos_iff_ne_zero.mpr hne
        have : nmass r (weights a ρ) / 2 < nmass r (weights a ρ) := half_lt_self hp
        exact absurd h4 (not_le.mpr this)
      simp [h5]
    rw [h3] at ih
    exact lt_irrefl _ ih

lemma update_apply (r : Config M) (ϕ : Config M →₀ ℝ≥0) (y : Config M) :
    update r ϕ y = (if Serves y r then ϕ y else 0) +
      ∑ x ∈ ϕ.support.filter (fun x => ¬ Serves x r), ∑ i : Fin k,
        (if repair x r i = y then ϕ x / (2 * (k : ℝ≥0)) else 0) := by
  classical
  unfold update
  rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.finsetSum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finsupp.single_apply]

lemma hwang_serves [NeZero k] (a : Config M) (hist : List (Config M)) (x r y : Config M)
    (h : Serves x r) : hwangAlg a hist x r y = if y = x then 1 else 0 := by
  classical
  unfold hwangAlg
  rw [if_pos h, PMF.pure_apply]
  congr

lemma hwang_not [NeZero k] (a : Config M) (hist : List (Config M)) (x r y : Config M)
    (h : ¬ Serves x r) : hwangAlg a hist x r y =
      2⁻¹ * (∑ i : Fin k, if y = repair x r i then (k : ENNReal)⁻¹ else 0)
        + 2⁻¹ * normalizedLaw a (hist ++ [r]) x y := by
  classical
  unfold hwangAlg
  rw [if_neg h, PMF.bind_apply, tsum_bool]
  simp only [if_true, Bool.false_eq_true, if_false, PMF.uniformOfFintype_apply, Fintype.card_bool,
    PMF.map_apply]
  simp
  rw [add_comm]

lemma alg (p Φ' N : ℝ≥0) (h' : Φ' ≠ 0) (h : Φ' + N / 2 ≠ 0) :
    (p : ENNReal) / ((Φ' + N / 2 : ℝ≥0) : ENNReal) +
      (N : ENNReal) / ((Φ' + N / 2 : ℝ≥0) : ENNReal) * 2⁻¹ * ((p : ENNReal) / (Φ' : ENNReal))
      = (p : ENNReal) / (Φ' : ENNReal) := by
  have key : p / (Φ' + N / 2) + N / (Φ' + N / 2) / 2 * (p / Φ') = p / Φ' := by
    field_simp
  have := congrArg (fun z : ℝ≥0 => (z : ENNReal)) key
  simp only [ENNReal.coe_add, ENNReal.coe_mul] at this
  rw [ENNReal.coe_div h, ENNReal.coe_div h', ENNReal.coe_div (two_ne_zero), ENNReal.coe_div h]
    at this
  simp only [ENNReal.coe_add, ENNReal.coe_div (two_ne_zero)] at this ⊢
  simpa [div_eq_mul_inv] using this

lemma nl_apply [NeZero k] (a : Config M) (ρ : List (Config M)) (fb y : Config M) :
    normalizedLaw a ρ fb y = ((weights a ρ y : ℝ≥0) : ENNReal) / ((totalWeight a ρ : ℝ≥0) : ENNReal) := by
  have h : totalWeight a ρ ≠ 0 := (totalWeight_pos a ρ).ne'
  unfold normalizedLaw
  rw [dif_neg h, PMF.ofFinset_apply]

lemma step [NeZero k] (a : Config M) (ρ : List (Config M)) (r y : Config M) :
    ∑' x, ((weights a ρ x : ℝ≥0) : ENNReal) / ((totalWeight a ρ : ℝ≥0) : ENNReal) *
        hwangAlg a ρ x r y =
      ((weights a (ρ ++ [r]) y : ℝ≥0) : ENNReal) / ((totalWeight a (ρ ++ [r]) : ℝ≥0) : ENNReal) := by
  set ϕ := weights a ρ with hϕ
  have hΦ : totalWeight a ρ = totalWeight a (ρ ++ [r]) + nmass r ϕ / 2 := by
    unfold totalWeight
    rw [weights_append]
    exact total_split r ϕ
  have hpos' := totalWeight_pos a (ρ ++ [r])
  have hpos := totalWeight_pos a ρ
  rw [tsum_eq_sum (s := ϕ.support) (by
    intro x hx
    rw [Finsupp.notMem_support_iff.mp hx]; simp)]
  rw [← Finset.sum_filter_add_sum_filter_not ϕ.support (fun x => Serves x r)]
  have hS : ∑ x ∈ ϕ.support.filter (fun x => Serves x r),
      ((ϕ x : ℝ≥0) : ENNReal) / ((totalWeight a ρ : ℝ≥0) : ENNReal) * hwangAlg a ρ x r y
      = if Serves y r then ((ϕ y : ℝ≥0) : ENNReal) / ((totalWeight a ρ : ℝ≥0) : ENNReal) else 0 := by
    rw [Finset.sum_congr rfl (fun x hx => by
      rw [hwang_serves a ρ x r y (Finset.mem_filter.mp hx).2])]
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    by_cases hy : y ∈ ϕ.support.filter (fun x => Serves x r)
    · rw [if_pos hy, if_pos (Finset.mem_filter.mp hy).2]
    · rw [if_neg hy]
      by_cases hs : Serves y r
      · rw [if_pos hs]
        have : y ∉ ϕ.support := fun h => hy (Finset.mem_filter.mpr ⟨h, hs⟩)
        rw [Finsupp.notMem_support_iff.mp this]; simp
      · rw [if_neg hs]
  have hF : ∑ x ∈ ϕ.support.filter (fun x => ¬ Serves x r),
      ((ϕ x : ℝ≥0) : ENNReal) / ((totalWeight a ρ : ℝ≥0) : ENNReal) * hwangAlg a ρ x r y
      = ((∑ x ∈ ϕ.support.filter (fun x => ¬ Serves x r), ∑ i : Fin k,
          (if repair x r i = y then ϕ x / (2 * (k : ℝ≥0)) else 0) : ℝ≥0) : ENNReal)
          / ((totalWeight a ρ : ℝ≥0) : ENNReal)
        + (nmass r ϕ : ENNReal) / ((totalWeight a ρ : ℝ≥0) : ENNReal) * 2⁻¹ *
          (((update r ϕ y : ℝ≥0) : ENNReal) / ((totalWeight a (ρ ++ [r]) : ℝ≥0) : ENNReal)) := by
    have hk : (k : ℝ≥0) ≠ 0 := by exact_mod_cast NeZero.ne k
    have hk2 : (2 * (k : ℝ≥0)) ≠ 0 := by positivity
    rw [Finset.sum_congr rfl (fun x hx => by
      rw [hwang_not a ρ x r y (Finset.mem_filter.mp hx).2, nl_apply, weights_append]),
      Finset.sum_congr rfl (fun x _ => mul_add _ _ _), Finset.sum_add_distrib]
    congr 1
    · rw [ENNReal.ofNNReal_finsetSum]
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [ENNReal.ofNNReal_finsetSum]
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : repair x r i = y
      · subst h
        simp only [if_true]
        rw [ENNReal.coe_mul, ENNReal.coe_inv hk2]
        simp only [ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_natCast]
        rw [ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inr (by simpa using NeZero.ne k))]
        ring
      · have h' : ¬ y = repair x r i := fun e => h e.symm
        simp [h, h']
    · rw [← Finset.sum_mul]
      have : ∑ x ∈ ϕ.support.filter (fun x => ¬ Serves x r),
          ((ϕ x : ℝ≥0) : ENNReal) / ((totalWeight a ρ : ℝ≥0) : ENNReal)
          = (nmass r ϕ : ENNReal) / ((totalWeight a ρ : ℝ≥0) : ENNReal) := by
        simp only [nmass, ENNReal.ofNNReal_finsetSum, div_eq_mul_inv, Finset.sum_mul]
      rw [this, mul_assoc]

  rw [hS, hF, weights_append]
  have hp : ((update r ϕ y : ℝ≥0) : ENNReal) = ((if Serves y r then ϕ y else 0 : ℝ≥0) : ENNReal) +
      ((∑ x ∈ ϕ.support.filter (fun x => ¬ Serves x r), ∑ i : Fin k,
          (if repair x r i = y then ϕ x / (2 * (k : ℝ≥0)) else 0) : ℝ≥0) : ENNReal) := by
    rw [update_apply, ENNReal.coe_add]
  have h1 : (if Serves y r then ((ϕ y : ℝ≥0) : ENNReal) / ((totalWeight a ρ : ℝ≥0) : ENNReal) else 0)
      = ((if Serves y r then ϕ y else 0 : ℝ≥0) : ENNReal) / ((totalWeight a ρ : ℝ≥0) : ENNReal) := by
    split_ifs <;> simp
  rw [h1, ← add_assoc, ← ENNReal.add_div, ← hp]
  have hne : totalWeight a ρ ≠ 0 := hpos.ne'
  rw [hΦ] at hne ⊢
  exact alg _ _ _ hpos'.ne' hne

end GeneralizedUniformServer.Dev.ConfigLaw

namespace GeneralizedUniformServer.UnitWeights

open GeneralizedUniformServer.Dev.ConfigLaw

/-- Lemma 3.1 (source p. 9): for every fixed request sequence and every `t ≥ 0`, the
configuration `X_t` of the algorithm has distribution `μ_t = ϕ_t / Φ_t`. Here `X_t` is the
head of the reversed trajectory, and `t` ranges over the times `0 ≤ t ≤ T` of the finite
sequence `ρ = (r₁, …, r_T)`. -/
theorem _root_.GeneralizedUniformServer.chk_configuration_law {k : ℕ} [NeZero k] {M : Fin k → Type*}
    (a : Config M) (ρ : List (Config M)) (t : ℕ) (ht : t ≤ ρ.length) (y : Config M) :
    ((algTraj a ρ t).map fun p => p.headD a) y =
      ((weights a (ρ.take t) y : ℝ≥0) : ENNReal) / ((totalWeight a (ρ.take t) : ℝ≥0) : ENNReal) := by
  induction t generalizing y with
  | zero =>
    classical
    simp [algTraj, trajLaw, weights, totalWeight, PMF.pure_map, PMF.pure_apply,
      Finsupp.single_apply, Finsupp.sum_single_index, eq_comm]
    split_ifs <;> simp
  | succ t ih =>
    have h : t < ρ.length := ht
    unfold algTraj at *
    rw [head_rec _ a ρ t h y, PMF.bind_apply]
    simp_rw [ih (Nat.le_of_lt h)]
    have := step a (ρ.take t) ρ[t] y
    rw [← List.take_succ_eq_append_getElem h] at this
    exact this

end GeneralizedUniformServer.UnitWeights
end
end

theorem solution : type_of% @GeneralizedUniformServer.chk_configuration_law := @GeneralizedUniformServer.chk_configuration_law
