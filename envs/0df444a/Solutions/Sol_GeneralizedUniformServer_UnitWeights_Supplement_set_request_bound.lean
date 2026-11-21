-- Prove2me | solution 1 for GeneralizedUniformServer.UnitWeights.Supplement.set_request_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T13:48:07.743748+00:00
-- url     : https://prove2.me/submissions/9de32b75-0c4b-49de-85cc-12057cc2dd79

import Mathlib
import Definitions.Def_GeneralizedUniformServer_UnitWeights_Supplement_SetRequests

section
open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement

namespace GeneralizedUniformServer.Dev.SetDefs

variable {k : ℕ} {M : Fin k → Type*}

/-- lazy offline solution for set requests -/
def IsSetLazy (ρ : List (SetRequest M)) (o : Fin (ρ.length + 1) → Config M) : Prop :=
  ∀ s : Fin ρ.length,
    (ServesSet (o s.castSucc) ρ[s] → o s.succ = o s.castSucc) ∧
    (¬ ServesSet (o s.castSucc) ρ[s] → ∃ q ∈ repairPairs ρ[s], o s.succ = setRepair (o s.castSucc) q)

open Classical in
/-- number of moves -/
noncomputable def setNumMoves (ρ : List (SetRequest M)) (o : Fin (ρ.length + 1) → Config M) : ℕ :=
  (Finset.univ.filter fun s : Fin ρ.length => o s.succ ≠ o s.castSucc).card

end GeneralizedUniformServer.Dev.SetDefs
end

section
open scoped NNReal Classical

noncomputable section

namespace GeneralizedUniformServer.Dev.SetCore

open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement

variable {k : ℕ} {M : Fin k → Type*}

lemma setWeights_append (a : Config M) (ρ : List (SetRequest M)) (P : SetRequest M) :
    setWeights a (ρ ++ [P]) = setUpdate P (setWeights a ρ) := by
  simp [setWeights, List.foldl_append]

lemma total_eq (ϕ : Config M →₀ ℝ≥0) : ϕ.sum (fun _ v => v) = ∑ x ∈ ϕ.support, ϕ x := rfl

lemma card_repairPairs (P : SetRequest M) : (repairPairs P).card = reqSize P := by
  simp [repairPairs, reqSize, Finset.card_sigma]

lemma repair_total (P : SetRequest M) (ϕ : Config M →₀ ℝ≥0) (x : Config M) :
    (∑ s ∈ repairPairs P, Finsupp.single (setRepair x s) (ϕ x / (2 * (reqSize P : ℝ≥0)))).sum
        (fun _ v => v) ≤ ϕ x / 2 ∧
      (1 ≤ reqSize P → (∑ s ∈ repairPairs P,
        Finsupp.single (setRepair x s) (ϕ x / (2 * (reqSize P : ℝ≥0)))).sum (fun _ v => v)
          = ϕ x / 2) := by
  rw [← Finsupp.sum_finsetSum_index (by simp) (by simp)]
  simp only [Finsupp.sum_single_index]
  rw [Finset.sum_const, card_repairPairs, nsmul_eq_mul]
  constructor
  · by_cases h : reqSize P = 0
    · simp [h]
    · have hk : (reqSize P : ℝ≥0) ≠ 0 := by exact_mod_cast h
      apply le_of_eq
      field_simp
  · intro h
    have hk : (reqSize P : ℝ≥0) ≠ 0 := by
      exact_mod_cast (by omega : reqSize P ≠ 0)
    field_simp

lemma total_update_eq (P : SetRequest M) (ϕ : Config M →₀ ℝ≥0) (hP : 1 ≤ reqSize P) :
    (setUpdate P ϕ).sum (fun _ v => v) =
      ∑ x ∈ ϕ.support.filter (fun x => ServesSet x P), ϕ x +
      (∑ x ∈ ϕ.support.filter (fun x => ¬ ServesSet x P), ϕ x) / 2 := by
  unfold setUpdate
  rw [Finsupp.sum_add_index' (by simp) (by simp), ← Finsupp.sum_finsetSum_index (by simp) (by simp)]
  have h1 : (ϕ.filter (fun y => ServesSet y P)).sum (fun _ v => v)
      = ∑ x ∈ ϕ.support.filter (fun x => ServesSet x P), ϕ x := by
    rw [total_eq, Finsupp.support_filter]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finsupp.filter_apply, if_pos (Finset.mem_filter.mp hx).2]
  have h2 : ∀ x ∈ ϕ.support.filter (fun x => ¬ ServesSet x P),
      (∑ s ∈ repairPairs P, Finsupp.single (setRepair x s) (ϕ x / (2 * (reqSize P : ℝ≥0)))).sum
        (fun _ v => v) = ϕ x / 2 := fun x _ => (repair_total P ϕ x).2 hP
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_div]

lemma total_update_le (P : SetRequest M) (ϕ : Config M →₀ ℝ≥0) :
    (setUpdate P ϕ).sum (fun _ v => v) ≤ ϕ.sum (fun _ v => v) := by
  unfold setUpdate
  rw [Finsupp.sum_add_index' (by simp) (by simp), ← Finsupp.sum_finsetSum_index (by simp) (by simp)]
  have h1 : (ϕ.filter (fun y => ServesSet y P)).sum (fun _ v => v)
      = ∑ x ∈ ϕ.support.filter (fun x => ServesSet x P), ϕ x := by
    rw [total_eq, Finsupp.support_filter]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finsupp.filter_apply, if_pos (Finset.mem_filter.mp hx).2]
  have h2 : ∀ x ∈ ϕ.support.filter (fun x => ¬ ServesSet x P),
      (∑ s ∈ repairPairs P, Finsupp.single (setRepair x s) (ϕ x / (2 * (reqSize P : ℝ≥0)))).sum
        (fun _ v => v) ≤ ϕ x := fun x _ =>
    (repair_total P ϕ x).1.trans (div_le_self zero_le (by norm_num))
  rw [h1, total_eq, ← Finset.sum_filter_add_sum_filter_not ϕ.support (fun x => ServesSet x P)]
  exact add_le_add le_rfl (Finset.sum_le_sum h2)

lemma set_totalWeight_nil (a : Config M) : setTotalWeight a [] = 1 := by
  simp [setTotalWeight, setWeights, Finsupp.sum_single_index]

lemma set_totalWeight_pos {ρ : List (SetRequest M)} (hρ : ∀ P ∈ ρ, 1 ≤ reqSize P)
    (a : Config M) : 0 < (setTotalWeight a ρ : ℝ) := by
  have : 0 < setTotalWeight a ρ := by
    induction ρ using List.reverseRecOn with
    | nil => simp [set_totalWeight_nil]
    | append_singleton ρ r ih =>
      have ih := ih (fun P hP => hρ P (by simp [hP]))
      have hr := hρ r (by simp)
      unfold setTotalWeight at ih ⊢
      rw [setWeights_append, total_update_eq _ _ hr]
      rw [total_eq, ← Finset.sum_filter_add_sum_filter_not _ (fun x => ServesSet x r)] at ih
      set S := ∑ x ∈ (setWeights a ρ).support.filter (fun x => ServesSet x r), (setWeights a ρ) x
      set N := ∑ x ∈ (setWeights a ρ).support.filter (fun x => ¬ ServesSet x r), (setWeights a ρ) x
      have : (S + N) / 2 ≤ S + N / 2 := by
        rw [add_div]; gcongr; exact div_le_self (zero_le) (by norm_num)
      exact lt_of_lt_of_le (by positivity) this
  exact_mod_cast this

lemma set_totalWeight_mono (a : Config M) (ρ : List (SetRequest M)) (P : SetRequest M) :
    setTotalWeight a (ρ ++ [P]) ≤ setTotalWeight a ρ := by
  unfold setTotalWeight
  rw [setWeights_append]
  exact total_update_le _ _

lemma update_apply (P : SetRequest M) (ϕ : Config M →₀ ℝ≥0) (y : Config M) :
    setUpdate P ϕ y = (if ServesSet y P then ϕ y else 0) +
      ∑ x ∈ ϕ.support.filter (fun x => ¬ ServesSet x P), ∑ s ∈ repairPairs P,
        (if setRepair x s = y then ϕ x / (2 * (reqSize P : ℝ≥0)) else 0) := by
  unfold setUpdate
  rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.finsetSum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finsupp.single_apply]

lemma head_rec (a : Config M) (ρ : List (SetRequest M))
    (t : ℕ) (h : t < ρ.length) (y : Config M) :
    ((genTrajLaw (setAlg a) a ρ (t + 1)).map fun p => p.headD a) y =
      (((genTrajLaw (setAlg a) a ρ t).map fun p => p.headD a).bind fun x =>
        setAlg a (ρ.take t) [x] ρ[t]) y := by
  rw [PMF.bind_map]
  have : genTrajLaw (setAlg a) a ρ (t + 1) = (genTrajLaw (setAlg a) a ρ t).bind fun p =>
      (setAlg a (ρ.take t) p ρ[t]).map fun y => y :: p := by
    simp only [genTrajLaw, dif_pos h]
  rw [this, PMF.map_bind]
  refine congrArg (fun μ : PMF (Config M) => μ y)
    (congrArg (fun f => (genTrajLaw (setAlg a) a ρ t).bind f) (funext fun p => ?_))
  show _ = setAlg a (ρ.take t) p ρ[t]
  rw [PMF.map_comp]
  have : ((fun q : List (Config M) => q.headD a) ∘ fun y => y :: p) = id := by
    funext y; simp
  rw [this, PMF.map_id]

lemma setAlg_serves (a : Config M) (hist : List (SetRequest M)) (x : Config M) (P : SetRequest M)
    (y : Config M) (h : ServesSet x P) :
    setAlg a hist [x] P y = if y = x then 1 else 0 := by
  unfold setAlg
  dsimp only [List.headD_cons]
  rw [if_pos h, PMF.pure_apply]
  congr

lemma setAlg_not (a : Config M) (hist : List (SetRequest M)) (x : Config M) (P : SetRequest M)
    (hP : 1 ≤ reqSize P) (y : Config M) (h : ¬ ServesSet x P) :
    setAlg a hist [x] P y =
      2⁻¹ * (∑ s ∈ repairPairs P, if y = setRepair x s then ((reqSize P : ℕ) : ENNReal)⁻¹ else 0)
        + 2⁻¹ * setNormalizedLaw a (hist ++ [P]) x y := by
  have hne : (repairPairs P).Nonempty := by
    rw [← Finset.card_pos, card_repairPairs]; omega
  unfold setAlg
  dsimp only [List.headD_cons]
  rw [if_neg h, PMF.bind_apply, tsum_bool]
  simp only [if_true, Bool.false_eq_true, if_false, PMF.uniformOfFintype_apply, Fintype.card_bool,
    dif_pos hne, PMF.map_apply, PMF.uniformOfFinset_apply]
  have h2 : ((2 : ℕ) : ENNReal)⁻¹ = 2⁻¹ := by simp
  rw [h2, add_comm, card_repairPairs]
  congr 2
  rw [tsum_eq_sum (s := repairPairs P)]
  · apply Finset.sum_congr rfl
    intro s hs
    rw [if_pos hs]
    congr
  · intro s hs
    rw [if_neg hs]
    simp

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

lemma nl_apply (a : Config M) (ρ : List (SetRequest M)) (hρ : ∀ P ∈ ρ, 1 ≤ reqSize P)
    (fb y : Config M) :
    setNormalizedLaw a ρ fb y =
      ((setWeights a ρ y : ℝ≥0) : ENNReal) / ((setTotalWeight a ρ : ℝ≥0) : ENNReal) := by
  have h : setTotalWeight a ρ ≠ 0 := by
    have := set_totalWeight_pos hρ a
    exact_mod_cast this.ne'
  unfold setNormalizedLaw
  rw [dif_neg h, PMF.ofFinset_apply]

lemma step (a : Config M) (ρ : List (SetRequest M)) (r : SetRequest M)
    (hρ : ∀ P ∈ ρ, 1 ≤ reqSize P) (hr : 1 ≤ reqSize r) (y : Config M) :
    ∑' x, ((setWeights a ρ x : ℝ≥0) : ENNReal) / ((setTotalWeight a ρ : ℝ≥0) : ENNReal) *
        setAlg a ρ [x] r y =
      ((setWeights a (ρ ++ [r]) y : ℝ≥0) : ENNReal) /
        ((setTotalWeight a (ρ ++ [r]) : ℝ≥0) : ENNReal) := by
  have hρ' : ∀ P ∈ ρ ++ [r], 1 ≤ reqSize P := by
    intro P hP
    rcases List.mem_append.mp hP with h | h
    · exact hρ P h
    · rw [List.mem_singleton.mp h]; exact hr
  set ϕ := setWeights a ρ with hϕ
  have hΦ : setTotalWeight a ρ = setTotalWeight a (ρ ++ [r]) +
      (∑ x ∈ ϕ.support.filter (fun x => ¬ ServesSet x r), ϕ x) / 2 := by
    unfold setTotalWeight
    rw [setWeights_append, total_update_eq _ _ hr, total_eq, ← Finset.sum_filter_add_sum_filter_not
      ϕ.support (fun x => ServesSet x r)]
    rw [add_assoc, add_halves]
  have hpos' : 0 < setTotalWeight a (ρ ++ [r]) := by exact_mod_cast set_totalWeight_pos hρ' a
  have hpos : 0 < setTotalWeight a ρ := by exact_mod_cast set_totalWeight_pos hρ a
  set N := ∑ x ∈ ϕ.support.filter (fun x => ¬ ServesSet x r), ϕ x with hN
  have hn : (reqSize r : ℝ≥0) ≠ 0 := by exact_mod_cast (by omega : reqSize r ≠ 0)
  have hn2 : (2 * (reqSize r : ℝ≥0)) ≠ 0 := by positivity
  rw [tsum_eq_sum (s := ϕ.support) (by
    intro x hx
    rw [Finsupp.notMem_support_iff.mp hx]; simp)]
  rw [← Finset.sum_filter_add_sum_filter_not ϕ.support (fun x => ServesSet x r)]
  have hS : ∑ x ∈ ϕ.support.filter (fun x => ServesSet x r),
      ((ϕ x : ℝ≥0) : ENNReal) / ((setTotalWeight a ρ : ℝ≥0) : ENNReal) * setAlg a ρ [x] r y
      = if ServesSet y r then ((ϕ y : ℝ≥0) : ENNReal) / ((setTotalWeight a ρ : ℝ≥0) : ENNReal)
        else 0 := by
    rw [Finset.sum_congr rfl (fun x hx => by
      rw [setAlg_serves a ρ x r y (Finset.mem_filter.mp hx).2])]
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    by_cases hy : y ∈ ϕ.support.filter (fun x => ServesSet x r)
    · rw [if_pos hy, if_pos (Finset.mem_filter.mp hy).2]
    · rw [if_neg hy]
      by_cases hs : ServesSet y r
      · rw [if_pos hs]
        have : y ∉ ϕ.support := fun h => hy (Finset.mem_filter.mpr ⟨h, hs⟩)
        rw [Finsupp.notMem_support_iff.mp this]; simp
      · rw [if_neg hs]
  have hF : ∑ x ∈ ϕ.support.filter (fun x => ¬ ServesSet x r),
      ((ϕ x : ℝ≥0) : ENNReal) / ((setTotalWeight a ρ : ℝ≥0) : ENNReal) * setAlg a ρ [x] r y
      = ((∑ x ∈ ϕ.support.filter (fun x => ¬ ServesSet x r), ∑ s ∈ repairPairs r,
          (if setRepair x s = y then ϕ x / (2 * (reqSize r : ℝ≥0)) else 0) : ℝ≥0) : ENNReal)
          / ((setTotalWeight a ρ : ℝ≥0) : ENNReal)
        + (N : ENNReal) / ((setTotalWeight a ρ : ℝ≥0) : ENNReal) * 2⁻¹ *
          (((setUpdate r ϕ y : ℝ≥0) : ENNReal) /
            ((setTotalWeight a (ρ ++ [r]) : ℝ≥0) : ENNReal)) := by
    rw [Finset.sum_congr rfl (fun x hx => by
      rw [setAlg_not a ρ x r hr y (Finset.mem_filter.mp hx).2, nl_apply a (ρ ++ [r]) hρ',
        setWeights_append]),
      Finset.sum_congr rfl (fun x _ => mul_add _ _ _), Finset.sum_add_distrib]
    congr 1
    · rw [ENNReal.ofNNReal_finsetSum]
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [ENNReal.ofNNReal_finsetSum]
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      by_cases h : setRepair x s = y
      · subst h
        simp only [if_true]
        rw [ENNReal.coe_mul, ENNReal.coe_inv hn2]
        simp only [ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_natCast]
        rw [ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inr (by simpa using hn))]
        ring
      · have h' : ¬ y = setRepair x s := fun e => h e.symm
        simp [h, h']
    · rw [← Finset.sum_mul]
      have : ∑ x ∈ ϕ.support.filter (fun x => ¬ ServesSet x r),
          ((ϕ x : ℝ≥0) : ENNReal) / ((setTotalWeight a ρ : ℝ≥0) : ENNReal)
          = (N : ENNReal) / ((setTotalWeight a ρ : ℝ≥0) : ENNReal) := by
        simp only [hN, ENNReal.ofNNReal_finsetSum, div_eq_mul_inv, Finset.sum_mul]
      rw [this, mul_assoc]
  rw [hS, hF, setWeights_append]
  have hp : ((setUpdate r ϕ y : ℝ≥0) : ENNReal) =
      ((if ServesSet y r then ϕ y else 0 : ℝ≥0) : ENNReal) +
      ((∑ x ∈ ϕ.support.filter (fun x => ¬ ServesSet x r), ∑ s ∈ repairPairs r,
          (if setRepair x s = y then ϕ x / (2 * (reqSize r : ℝ≥0)) else 0) : ℝ≥0) : ENNReal) := by
    rw [update_apply, ENNReal.coe_add]
  have h1 : (if ServesSet y r then ((ϕ y : ℝ≥0) : ENNReal) /
        ((setTotalWeight a ρ : ℝ≥0) : ENNReal) else 0)
      = ((if ServesSet y r then ϕ y else 0 : ℝ≥0) : ENNReal) /
        ((setTotalWeight a ρ : ℝ≥0) : ENNReal) := by
    split_ifs <;> simp
  rw [h1, ← add_assoc, ← ENNReal.add_div, ← hp]
  have hne : setTotalWeight a ρ ≠ 0 := hpos.ne'
  rw [hΦ] at hne ⊢
  exact alg _ _ _ hpos'.ne' hne

lemma take_succ' (ρ : List (SetRequest M)) (s : ℕ) (hs : s < ρ.length) :
    ρ.take (s + 1) = ρ.take s ++ [ρ[s]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hs]
  rfl

lemma hρ_take {ρ : List (SetRequest M)} (hρ : ∀ P ∈ ρ, 1 ≤ reqSize P) (t : ℕ) :
    ∀ P ∈ ρ.take t, 1 ≤ reqSize P := fun P hP => hρ P (List.mem_of_mem_take hP)

theorem set_configuration_law {k : ℕ} {M : Fin k → Type*} (a : Config M)
    (ρ : List (SetRequest M)) (hρ : ∀ P ∈ ρ, 1 ≤ reqSize P) (t : ℕ) (ht : t ≤ ρ.length)
    (y : Config M) :
    ((genTrajLaw (setAlg a) a ρ t).map fun p => p.headD a) y =
      ((setWeights a (ρ.take t) y : ℝ≥0) : ENNReal) /
        ((setTotalWeight a (ρ.take t) : ℝ≥0) : ENNReal) := by
  induction t generalizing y with
  | zero =>
    simp [genTrajLaw, setWeights, setTotalWeight, PMF.pure_map, PMF.pure_apply,
      Finsupp.single_apply, Finsupp.sum_single_index, eq_comm]
    split_ifs <;> simp
  | succ t ih =>
    have h : t < ρ.length := ht
    rw [head_rec a ρ t h y, PMF.bind_apply]
    simp_rw [ih (Nat.le_of_lt h)]
    have := step a (ρ.take t) ρ[t] (hρ_take hρ t) (hρ _ (List.getElem_mem h)) y
    rw [← take_succ' ρ t h] at this
    exact this

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

lemma traj_succ_E (a : Config M) (ρ : List (SetRequest M)) (t : ℕ)
    (ht : t < ρ.length) (g : List (Config M) → ENNReal) :
    E (genTrajLaw (setAlg a) a ρ (t + 1)) g =
      E (genTrajLaw (setAlg a) a ρ t) (fun p =>
        E (setAlg a (ρ.take t) [p.headD a] ρ[t]) (fun y => g (y :: p))) := by
  rw [genTrajLaw, E_bind]
  congr 1
  ext p
  rw [dif_pos ht, E_map]
  rfl

lemma traj_ne_nil (A : GenOnlineAlg M (SetRequest M)) (a : Config M) (ρ : List (SetRequest M))
    (t : ℕ) (p : List (Config M)) (hp : p ∈ (genTrajLaw A a ρ t).support) : p ≠ [] := by
  induction t generalizing p with
  | zero => simp [genTrajLaw] at hp; simp [hp]
  | succ t ih =>
    rw [genTrajLaw, PMF.mem_support_bind_iff] at hp
    obtain ⟨q, hq, hp⟩ := hp
    split_ifs at hp with h
    · rw [PMF.mem_support_map_iff] at hp
      obtain ⟨y, -, rfl⟩ := hp
      simp
    · rw [PMF.support_pure, Set.mem_singleton_iff] at hp
      subst hp; exact ih _ hq

lemma dist_le (x y : Config M) : UnitWeights.dist x y ≤ k := by
  unfold UnitWeights.dist
  calc _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_filter_le _ _
    _ = k := by simp

lemma dist_setRepair_le (x : Config M) (s : Σ i : Fin k, M i) :
    UnitWeights.dist x (setRepair x s) ≤ 1 := by
  unfold UnitWeights.dist
  calc _ ≤ ({s.1} : Finset (Fin k)).card := by
        apply Finset.card_le_card
        intro j hj
        rw [Finset.mem_filter] at hj
        rw [Finset.mem_singleton]
        by_contra hne
        exact hj.2 (by simp [setRepair, Function.update_of_ne hne])
    _ = 1 := by simp

lemma inner_le (a : Config M) (hist : List (SetRequest M)) (x : Config M) (r : SetRequest M)
    (hr : 1 ≤ reqSize r) :
    E (setAlg a hist [x] r) (fun y => (UnitWeights.dist x y : ENNReal)) ≤
      if ServesSet x r then 0 else (2⁻¹ : ENNReal) * (1 + (k : ENNReal)) := by
  by_cases hs : ServesSet x r
  · rw [if_pos hs]
    unfold setAlg
    dsimp only [List.headD_cons]
    rw [if_pos hs, E_pure]
    simp [UnitWeights.dist]
  · rw [if_neg hs]
    have hne : (repairPairs r).Nonempty := by
      rw [← Finset.card_pos, card_repairPairs]; omega
    unfold setAlg
    dsimp only [List.headD_cons]
    rw [if_neg hs, E_bind]
    unfold E
    rw [tsum_fintype, Fintype.sum_bool]
    simp only [PMF.uniformOfFintype_apply, if_true, Bool.false_eq_true, if_false, dif_pos hne]
    have h1 : E ((PMF.uniformOfFinset (repairPairs r) hne).map (setRepair x))
        (fun y => (UnitWeights.dist x y : ENNReal)) ≤ 1 := by
      rw [E_map]
      calc _ ≤ E (PMF.uniformOfFinset (repairPairs r) hne) (fun _ => (1 : ENNReal)) :=
            E_mono _ (fun s => by exact_mod_cast dist_setRepair_le x s)
        _ = 1 := E_const _ _
    have h2 : E (setNormalizedLaw a (hist ++ [r]) x) (fun y => (UnitWeights.dist x y : ENNReal))
        ≤ k := by
      calc _ ≤ E (setNormalizedLaw a (hist ++ [r]) x) (fun _ => (k : ENNReal)) :=
            E_mono _ (fun y => by exact_mod_cast dist_le x y)
        _ = k := E_const _ _
    simp only [Fintype.card_bool]
    have : ((2 : ℕ) : ENNReal)⁻¹ = 2⁻¹ := by simp
    rw [this, ← mul_add]
    exact mul_le_mul_right (add_le_add h1 h2) _

lemma stepA (a : Config M) (ρ : List (SetRequest M)) (s : ℕ) (hs : s < ρ.length) :
    E (genTrajLaw (setAlg a) a ρ (s + 1)) (fun p => (lastStepCost p : ENNReal)) =
      E ((genTrajLaw (setAlg a) a ρ s).map fun p => p.headD a)
        (fun x => E (setAlg a (ρ.take s) [x] ρ[s]) (fun y => (UnitWeights.dist x y : ENNReal))) := by
  rw [traj_succ_E a ρ s hs, E_map]
  unfold E
  refine tsum_congr fun p => ?_
  by_cases hp : (genTrajLaw (setAlg a) a ρ s) p = 0
  · rw [hp]; simp
  · have hsupp : p ∈ (genTrajLaw (setAlg a) a ρ s).support := by
      rw [PMF.mem_support_iff]; exact hp
    obtain ⟨x, q, rfl⟩ := List.exists_cons_of_ne_nil (traj_ne_nil _ _ _ _ p hsupp)
    simp [lastStepCost]

lemma real_ineq (S N K Φ' : ℝ) (hS : 0 ≤ S) (_hN : 0 ≤ N) (hK : 0 ≤ K)
    (hΦ : 0 < S + N) (hΦ' : Φ' = S + N / 2) :
    N / (S + N) * (K / 2) ≤ K * Real.log ((S + N) / Φ') := by
  have hp : 0 < Φ' := by rw [hΦ']; linarith
  have h1 : Real.log (Φ' / (S + N)) ≤ Φ' / (S + N) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Φ' / (S + N) - 1 = -(N / 2 / (S + N)) := by
    rw [hΦ']; field_simp; ring
  have h3 : Real.log ((S + N) / Φ') = - Real.log (Φ' / (S + N)) := by
    rw [← Real.log_inv, inv_div]
  have h4 : N / 2 / (S + N) ≤ Real.log ((S + N) / Φ') := by linarith
  have h5 : N / (S + N) * (K / 2) = K * (N / 2 / (S + N)) := by field_simp
  rw [h5]
  exact mul_le_mul_of_nonneg_left h4 hK

lemma main (a : Config M) (ρ : List (SetRequest M)) (hρ : ∀ P ∈ ρ, 1 ≤ reqSize P) (s : ℕ)
    (hs : s < ρ.length) :
    ∑' p : List (Config M), genTrajLaw (setAlg a) a ρ (s + 1) p * (lastStepCost p : ENNReal) ≤
      ENNReal.ofReal (((k : ℝ) + 1) *
        Real.log ((setTotalWeight a (ρ.take s) : ℝ) / (setTotalWeight a (ρ.take (s + 1)) : ℝ))) := by
  set r := ρ[s] with hr
  have hr1 : 1 ≤ reqSize r := hρ _ (List.getElem_mem hs)
  set ϕ := setWeights a (ρ.take s) with hϕ
  set S := ∑ x ∈ ϕ.support.filter (fun x => ServesSet x r), ϕ x with hSdef
  set N := ∑ x ∈ ϕ.support.filter (fun x => ¬ ServesSet x r), ϕ x with hNdef
  have hΦ : setTotalWeight a (ρ.take s) = S + N := by
    rw [setTotalWeight, total_eq, ← Finset.sum_filter_add_sum_filter_not ϕ.support
      (fun x => ServesSet x r)]
  have hΦ' : setTotalWeight a (ρ.take (s + 1)) = S + N / 2 := by
    unfold setTotalWeight
    rw [take_succ' ρ s hs, setWeights_append, total_update_eq _ _ hr1]
  have hpos : 0 < S + N := by
    rw [← hΦ]; exact_mod_cast set_totalWeight_pos (hρ_take hρ s) a
  have hne : ((S + N : ℝ≥0) : ENNReal) ≠ 0 := by exact_mod_cast hpos.ne'
  have hA := stepA a ρ s hs
  have hB : E (genTrajLaw (setAlg a) a ρ (s + 1)) (fun p => (lastStepCost p : ENNReal)) ≤
      ∑' x, (ϕ x : ENNReal) / ((S + N : ℝ≥0) : ENNReal) *
        (if ServesSet x r then 0 else (2⁻¹ : ENNReal) * (1 + (k : ENNReal))) := by
    rw [hA]
    unfold E
    refine ENNReal.tsum_le_tsum fun x => ?_
    rw [set_configuration_law a ρ hρ s hs.le x, ← hΦ]
    gcongr
    exact inner_le a _ x r hr1
  have hC : (∑' x, (ϕ x : ENNReal) / ((S + N : ℝ≥0) : ENNReal) *
        (if ServesSet x r then 0 else (2⁻¹ : ENNReal) * (1 + (k : ENNReal)))) =
      ((N / (S + N) * ((1 + k) / 2) : ℝ≥0) : ENNReal) := by
    rw [tsum_eq_sum (s := ϕ.support)]
    · rw [← Finset.sum_filter_add_sum_filter_not ϕ.support (fun x => ServesSet x r)]
      have e1 : ∀ x ∈ ϕ.support.filter (fun x => ServesSet x r),
          (ϕ x : ENNReal) / ((S + N : ℝ≥0) : ENNReal) *
            (if ServesSet x r then 0 else (2⁻¹ : ENNReal) * (1 + (k : ENNReal))) = 0 := by
        intro x hx
        rw [if_pos (Finset.mem_filter.mp hx).2, mul_zero]
      have e2 : ∀ x ∈ ϕ.support.filter (fun x => ¬ ServesSet x r),
          (ϕ x : ENNReal) / ((S + N : ℝ≥0) : ENNReal) *
            (if ServesSet x r then 0 else (2⁻¹ : ENNReal) * (1 + (k : ENNReal))) =
          (ϕ x : ENNReal) *
            (((S + N : ℝ≥0) : ENNReal)⁻¹ * ((2⁻¹ : ENNReal) * (1 + (k : ENNReal)))) := by
        intro x hx
        rw [if_neg (Finset.mem_filter.mp hx).2, div_eq_mul_inv, mul_assoc]
      rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_const_zero, zero_add,
        ← Finset.sum_mul, ← ENNReal.ofNNReal_finsetSum, ← hNdef]
      rw [ENNReal.coe_mul, ENNReal.coe_div (by simpa using hpos.ne'),
        ENNReal.coe_div (by norm_num), div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
      push_cast
      simp [mul_comm, mul_left_comm, mul_assoc]
    · intro x hx
      rw [Finsupp.notMem_support_iff.mp hx]; simp
  show E _ _ ≤ _
  refine hB.trans (hC.le.trans ?_)
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  rw [hΦ, hΦ']
  have := real_ineq (S : ℝ) (N : ℝ) ((k : ℝ) + 1) _ S.2 N.2 (by positivity)
    (by exact_mod_cast hpos) rfl
  push_cast
  convert this using 2
  ring

theorem set_step_movement {k : ℕ} {M : Fin k → Type*} (a : Config M)
    (ρ : List (SetRequest M)) (hρ : ∀ P ∈ ρ, 1 ≤ reqSize P) (t : ℕ) (ht₁ : 1 ≤ t)
    (ht : t ≤ ρ.length) :
    ∑' p : List (Config M), genTrajLaw (setAlg a) a ρ t p * (lastStepCost p : ENNReal) ≤
      ENNReal.ofReal (((k : ℝ) + 1) *
        Real.log ((setTotalWeight a (ρ.take (t - 1)) : ℝ) /
          (setTotalWeight a (ρ.take t) : ℝ))) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simpa using main a ρ hρ s (by omega)


end GeneralizedUniformServer.Dev.SetCore
end
end

section
open scoped NNReal

noncomputable section

namespace GeneralizedUniformServer.Dev.SetLazy

open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
  GeneralizedUniformServer.Dev.SetDefs

variable {k : ℕ} {M : Fin k → Type*}

theorem weights_take_succ (a : Config M) (ρ : List (SetRequest M)) (t : ℕ) (h : t < ρ.length) :
    setWeights a (ρ.take (t+1)) = setUpdate ρ[t] (setWeights a (ρ.take t)) := by
  unfold setWeights
  rw [List.take_succ_eq_append_getElem h, List.foldl_append]
  rfl

theorem update_ge_serves (r : SetRequest M) (ϕ : Config M →₀ ℝ≥0) (y : Config M)
    (hy : ServesSet y r) : ϕ y ≤ setUpdate r ϕ y := by
  classical
  unfold setUpdate
  rw [Finsupp.add_apply, Finsupp.filter_apply, if_pos hy]
  exact le_self_add

theorem update_ge_repair (r : SetRequest M) (x : Config M) (ϕ : Config M →₀ ℝ≥0)
    (hx : ¬ ServesSet x r) (q : Σ i : Fin k, M i) (hq : q ∈ repairPairs r) :
    ϕ x / (2 * (reqSize r : ℝ≥0)) ≤ setUpdate r ϕ (setRepair x q) := by
  classical
  by_cases hs : x ∈ ϕ.support
  · unfold setUpdate
    rw [Finsupp.add_apply]
    refine le_trans ?_ le_add_self
    rw [Finsupp.finsetSum_apply]
    have hx' : x ∈ ϕ.support.filter (fun x => ¬ ServesSet x r) := Finset.mem_filter.2 ⟨hs, hx⟩
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun x' => (∑ s ∈ repairPairs r,
        Finsupp.single (setRepair x' s) (ϕ x' / (2 * (reqSize r : ℝ≥0)))) (setRepair x q))
      (fun _ _ => zero_le) hx')
    simp only [Finsupp.finsetSum_apply]
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun s => (Finsupp.single (setRepair x s) (ϕ x / (2 * (reqSize r : ℝ≥0))))
        (setRepair x q)) (fun _ _ => zero_le) hq)
    simp
  · rw [Finsupp.notMem_support_iff.1 hs]; simp

def ext (ρ : List (SetRequest M)) (o : Fin (ρ.length + 1) → Config M) (t : ℕ) : Config M :=
  if h : t < ρ.length + 1 then o ⟨t, h⟩ else o 0

open scoped Classical in
def mv (ρ : List (SetRequest M)) (o : Fin (ρ.length + 1) → Config M) (t : ℕ) : ℕ :=
  ∑ s ∈ Finset.range t, if ext ρ o (s+1) ≠ ext ρ o s then 1 else 0

theorem ext_castSucc (ρ : List (SetRequest M)) (o : Fin (ρ.length + 1) → Config M)
    (s : Fin ρ.length) : ext ρ o s.val = o s.castSucc := by
  unfold ext; rw [dif_pos (by omega)]; rfl

theorem ext_succ (ρ : List (SetRequest M)) (o : Fin (ρ.length + 1) → Config M)
    (s : Fin ρ.length) : ext ρ o (s.val + 1) = o s.succ := by
  unfold ext; rw [dif_pos (by omega)]; rfl

theorem numMoves_eq (ρ : List (SetRequest M)) (o : Fin (ρ.length + 1) → Config M) :
    setNumMoves ρ o = mv ρ o ρ.length := by
  classical
  unfold setNumMoves mv
  rw [Finset.card_filter, ← Fin.sum_univ_eq_sum_range
    (fun s => if ext ρ o (s+1) ≠ ext ρ o s then 1 else 0) ρ.length]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [ext_castSucc, ext_succ]

theorem main (a : Config M) (B : ℕ) (ρ : List (SetRequest M))
    (hρ : ∀ P ∈ ρ, 1 ≤ reqSize P ∧ reqSize P ≤ B)
    (o : Fin (ρ.length + 1) → Config M) (hlazy : IsSetLazy ρ o) (h₀ : o 0 = a) :
    ∀ t, t ≤ ρ.length →
      ((2 * (B : ℝ≥0)) ^ mv ρ o t)⁻¹ ≤ setWeights a (ρ.take t) (ext ρ o t) := by
  classical
  intro t
  induction t with
  | zero =>
    intro _
    have : ext ρ o 0 = a := by unfold ext; rw [dif_pos (by omega)]; exact h₀
    simp [mv, this, setWeights]
  | succ t ih =>
    intro hle
    have ht : t < ρ.length := hle
    have ih := ih ht.le
    rw [weights_take_succ a ρ t ht]
    have hmv : mv ρ o (t+1) = mv ρ o t + (if ext ρ o (t+1) ≠ ext ρ o t then 1 else 0) := by
      unfold mv; rw [Finset.sum_range_succ]
    have hl := hlazy ⟨t, ht⟩
    have e1 : ext ρ o t = o (⟨t, ht⟩ : Fin ρ.length).castSucc := ext_castSucc ρ o ⟨t, ht⟩
    have e2 : ext ρ o (t+1) = o (⟨t, ht⟩ : Fin ρ.length).succ := ext_succ ρ o ⟨t, ht⟩
    rw [← e1, ← e2] at hl
    have hP : 1 ≤ reqSize ρ[t] ∧ reqSize ρ[t] ≤ B := hρ _ (List.getElem_mem ht)
    by_cases hs : ServesSet (ext ρ o t) ρ[t]
    · have hz := hl.1 hs
      rw [hmv, hz]
      simp only [ne_eq, not_true_eq_false, if_false, add_zero]
      exact le_trans ih (update_ge_serves _ _ _ hs)
    · obtain ⟨q, hq, hi⟩ := hl.2 hs
      have hne : ext ρ o (t+1) ≠ ext ρ o t := by
        intro h
        apply hs
        rw [← h, hi]
        have := Finset.mem_sigma.1 hq
        exact ⟨q.1, by simpa [setRepair] using this.2⟩
      rw [hmv, if_pos hne, hi, pow_succ, mul_inv, ← div_eq_mul_inv]
      refine le_trans ?_ (update_ge_repair _ _ _ hs q hq)
      have hB : (reqSize ρ[t] : ℝ≥0) ≤ B := by exact_mod_cast hP.2
      have h1 : (0 : ℝ≥0) < reqSize ρ[t] := by exact_mod_cast hP.1
      have : (2 * (reqSize ρ[t] : ℝ≥0))⁻¹ ≥ (2 * (B : ℝ≥0))⁻¹ := by
        apply inv_anti₀ (by positivity)
        gcongr
      calc ((2 * (B : ℝ≥0)) ^ mv ρ o t)⁻¹ * (2 * (B : ℝ≥0))⁻¹
          ≤ setWeights a (ρ.take t) (ext ρ o t) * (2 * (B : ℝ≥0))⁻¹ := by gcongr
        _ ≤ setWeights a (ρ.take t) (ext ρ o t) * (2 * (reqSize ρ[t] : ℝ≥0))⁻¹ := by gcongr
        _ = _ := by rw [div_eq_mul_inv]

open scoped Classical in
theorem dist_eq (x y : Config M) :
    UnitWeights.dist x y = (Finset.univ.filter fun i : Fin k => x i ≠ y i).card := by
  classical
  unfold UnitWeights.dist
  rfl

theorem dist_triangle (x y z : Config M) :
    UnitWeights.dist x z ≤ UnitWeights.dist x y + UnitWeights.dist y z := by
  classical
  rw [dist_eq, dist_eq, dist_eq]
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
  by_contra h
  push Not at h
  exact hi (h.1.trans h.2)

theorem dist_repair_lt (x z : Config M) (q : Σ i : Fin k, M i) (hxi : x q.1 ≠ z q.1)
    (hz : z q.1 = q.2) :
    UnitWeights.dist (setRepair x q) z < UnitWeights.dist x z := by
  classical
  rw [dist_eq, dist_eq]
  have hsub : (Finset.univ.filter fun j : Fin k => setRepair x q j ≠ z j) ⊆
      (Finset.univ.filter fun j : Fin k => x j ≠ z j) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    by_cases h : j = q.1
    · subst h; simp [setRepair, hz] at hj
    · simpa [setRepair, h] using hj
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨q.1, ?_, ?_⟩)
  · simpa using hxi
  · simp [setRepair, ← hz]

open scoped Classical in
def req (ρ : List (SetRequest M)) (t : ℕ) : SetRequest M :=
  if h : t < ρ.length then ρ[t] else fun _ => ∅

open scoped Classical in
def seq (a : Config M) (rq : ℕ → SetRequest M) (oo : ℕ → Config M) : ℕ → Config M
  | 0 => a
  | t+1 => if ServesSet (seq a rq oo t) (rq t) then seq a rq oo t
      else if h : ∃ q ∈ repairPairs (rq t), oo (t+1) q.1 = q.2 then
        setRepair (seq a rq oo t) (Classical.choose h)
      else seq a rq oo t

section
variable (a : Config M) (rq : ℕ → SetRequest M) (oo : ℕ → Config M)

theorem seq_succ_of_serves (t : ℕ) (h : ServesSet (seq a rq oo t) (rq t)) :
    seq a rq oo (t+1) = seq a rq oo t := by
  rw [seq, if_pos h]

theorem seq_succ_of_not (t : ℕ) (h : ¬ ServesSet (seq a rq oo t) (rq t))
    (hy : ServesSet (oo (t+1)) (rq t)) :
    ∃ q ∈ repairPairs (rq t), seq a rq oo (t+1) = setRepair (seq a rq oo t) q ∧
      oo (t+1) q.1 = q.2 := by
  classical
  have hex : ∃ q ∈ repairPairs (rq t), oo (t+1) q.1 = q.2 := by
    obtain ⟨i, hi⟩ := hy
    exact ⟨⟨i, oo (t+1) i⟩, Finset.mem_sigma.2 ⟨Finset.mem_univ _, hi⟩, rfl⟩
  refine ⟨Classical.choose hex, (Classical.choose_spec hex).1, ?_, (Classical.choose_spec hex).2⟩
  rw [seq, if_neg h, dif_pos hex]

theorem seq_succ_serves (t : ℕ) (hy : ServesSet (oo (t+1)) (rq t)) :
    ServesSet (seq a rq oo (t+1)) (rq t) := by
  by_cases h : ServesSet (seq a rq oo t) (rq t)
  · rw [seq_succ_of_serves a rq oo t h]; exact h
  · obtain ⟨q, hq, he, _⟩ := seq_succ_of_not a rq oo t h hy
    rw [he]
    exact ⟨q.1, by simpa [setRepair] using (Finset.mem_sigma.1 hq).2⟩

theorem step (t : ℕ) (hy : ServesSet (oo (t+1)) (rq t)) :
    (by classical exact if seq a rq oo (t+1) ≠ seq a rq oo t then 1 else 0 : ℕ) +
        UnitWeights.dist (seq a rq oo (t+1)) (oo (t+1)) ≤
      UnitWeights.dist (oo t) (oo (t+1)) + UnitWeights.dist (seq a rq oo t) (oo t) := by
  classical
  by_cases hs : ServesSet (seq a rq oo t) (rq t)
  · rw [seq_succ_of_serves a rq oo t hs]
    have := dist_triangle (seq a rq oo t) (oo t) (oo (t+1))
    simp only [ne_eq, not_true_eq_false, if_false]
    omega
  · obtain ⟨q, hq, he, hqo⟩ := seq_succ_of_not a rq oo t hs hy
    rw [he]
    have hqm := (Finset.mem_sigma.1 hq).2
    have hne : setRepair (seq a rq oo t) q ≠ seq a rq oo t := by
      intro h; apply hs; rw [← h]; exact ⟨q.1, by simpa [setRepair] using hqm⟩
    have hxi : seq a rq oo t q.1 ≠ oo (t+1) q.1 := by
      rw [hqo]; intro h; exact hs ⟨q.1, by rw [h]; exact hqm⟩
    have h1 := dist_repair_lt (seq a rq oo t) (oo (t+1)) q hxi hqo
    have h2 := dist_triangle (seq a rq oo t) (oo t) (oo (t+1))
    simp only [ne_eq, hne, not_false_eq_true, if_true]
    omega

theorem sum_bound (n : ℕ) (hy : ∀ t < n, ServesSet (oo (t+1)) (rq t)) :
    ∀ m ≤ n,
      (by classical exact ∑ s ∈ Finset.range m,
        (if seq a rq oo (s+1) ≠ seq a rq oo s then 1 else 0) : ℕ) +
        UnitWeights.dist (seq a rq oo m) (oo m) ≤
      ∑ s ∈ Finset.range m, UnitWeights.dist (oo s) (oo (s+1)) +
        UnitWeights.dist a (oo 0) := by
  intro m
  induction m with
  | zero => intro _; simp [seq]
  | succ m ih =>
    intro hm
    have := ih (by omega)
    have h2 := step a rq oo m (hy m (by omega))
    classical
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    omega
end

theorem exists_serving (P : SetRequest M) (h : 1 ≤ reqSize P) :
    ∃ q ∈ repairPairs P, True := by
  have : ∃ i, 0 < (P i).card := by
    by_contra hc
    push Not at hc
    have : reqSize P = 0 := Finset.sum_eq_zero fun i _ => by have := hc i; omega
    omega
  obtain ⟨i, hi⟩ := this
  obtain ⟨p, hp⟩ := Finset.card_pos.1 hi
  exact ⟨⟨i, p⟩, Finset.mem_sigma.2 ⟨Finset.mem_univ _, hp⟩, trivial⟩

end GeneralizedUniformServer.Dev.SetLazy

namespace GeneralizedUniformServer.Dev.SetLazy

open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
  GeneralizedUniformServer.Dev.SetDefs

theorem set_lazy_weight {k : ℕ} {M : Fin k → Type*} (a : Config M) (B : ℕ)
    (ρ : List (SetRequest M)) (hρ : ∀ P ∈ ρ, 1 ≤ reqSize P ∧ reqSize P ≤ B)
    (o : Fin (ρ.length + 1) → Config M) (hsol : IsSetOfflineSolution ρ o)
    (hlazy : IsSetLazy ρ o) (h₀ : o 0 = a) :
    setWeights a ρ (o (Fin.last ρ.length)) ≤ setTotalWeight a ρ ∧
      ((2 * (B : ℝ≥0)) ^ setNumMoves ρ o)⁻¹ ≤ setWeights a ρ (o (Fin.last ρ.length)) := by
  classical
  have hlast : ext ρ o ρ.length = o (Fin.last ρ.length) := by
    unfold ext; rw [dif_pos (by omega)]; rfl
  refine ⟨?_, ?_⟩
  · by_cases hm : o (Fin.last ρ.length) ∈ (setWeights a ρ).support
    · unfold setTotalWeight Finsupp.sum
      exact Finset.single_le_sum (f := fun x => setWeights a ρ x) (fun _ _ => zero_le) hm
    · rw [Finsupp.notMem_support_iff.1 hm]; exact zero_le
  · have := main a B ρ hρ o hlazy h₀ ρ.length le_rfl
    rw [List.take_length, hlast] at this
    rw [numMoves_eq]
    exact this

theorem set_lazy_conversion {k : ℕ} {M : Fin k → Type*} (ρ : List (SetRequest M))
    (hρ : ∀ P ∈ ρ, 1 ≤ reqSize P) (o : Fin (ρ.length + 1) → Config M)
    (ho : IsSetOfflineSolution ρ o) (a : Config M) :
    ∃ o' : Fin (ρ.length + 1) → Config M, IsSetOfflineSolution ρ o' ∧ IsSetLazy ρ o' ∧
      o' 0 = a ∧ setNumMoves ρ o' ≤ setOfflineCost ρ o + UnitWeights.dist a (o 0) := by
  classical
  have hreq : ∀ s : Fin ρ.length, req ρ s.val = ρ[s] := by
    intro s; unfold req; rw [dif_pos s.2]; simp
  have hy : ∀ t < ρ.length, ServesSet (ext ρ o (t+1)) (req ρ t) := by
    intro t ht
    have := ho ⟨t, ht⟩
    rw [← ext_succ ρ o ⟨t, ht⟩] at this
    rw [show req ρ t = ρ[t] from hreq ⟨t, ht⟩]
    exact this
  refine ⟨fun s => seq a (req ρ) (ext ρ o) s.val, ?_, ?_, ?_, ?_⟩
  · intro s
    have := seq_succ_serves a (req ρ) (ext ρ o) s.val (hy s.val s.2)
    rw [hreq] at this
    exact this
  · intro s
    have e : (fun s : Fin (ρ.length + 1) => seq a (req ρ) (ext ρ o) s.val) s.succ =
      seq a (req ρ) (ext ρ o) (s.val + 1) := rfl
    have e' : (fun s : Fin (ρ.length + 1) => seq a (req ρ) (ext ρ o) s.val) s.castSucc =
      seq a (req ρ) (ext ρ o) s.val := rfl
    simp only [e, e']
    rw [← hreq s]
    constructor
    · intro h; exact seq_succ_of_serves _ _ _ _ h
    · intro h
      obtain ⟨q, hq, he, _⟩ := seq_succ_of_not a (req ρ) (ext ρ o) s.val h (hy s.val s.2)
      exact ⟨q, hq, he⟩
  · simp [seq]
  · have key := sum_bound a (req ρ) (ext ρ o) ρ.length hy ρ.length le_rfl
    have h0 : ext ρ o 0 = o 0 := by unfold ext; rw [dif_pos (by omega)]; rfl
    have hm : setNumMoves ρ (fun s : Fin (ρ.length + 1) => seq a (req ρ) (ext ρ o) s.val) =
        ∑ s ∈ Finset.range ρ.length,
          (if seq a (req ρ) (ext ρ o) (s+1) ≠ seq a (req ρ) (ext ρ o) s then 1 else 0) := by
      unfold setNumMoves
      rw [Finset.card_filter, ← Fin.sum_univ_eq_sum_range
        (fun s => if seq a (req ρ) (ext ρ o) (s+1) ≠ seq a (req ρ) (ext ρ o) s
          then 1 else 0) ρ.length]
      rfl
    have hc : setOfflineCost ρ o = ∑ s ∈ Finset.range ρ.length,
        UnitWeights.dist (ext ρ o s) (ext ρ o (s+1)) := by
      unfold setOfflineCost
      rw [← Fin.sum_univ_eq_sum_range
        (fun s => UnitWeights.dist (ext ρ o s) (ext ρ o (s+1))) ρ.length]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [ext_castSucc, ext_succ]
    rw [hm, hc, ← h0]
    omega

theorem set_exists_offline_solution {k : ℕ} {M : Fin k → Type*} {ρ : List (SetRequest M)}
    (hρ : ∀ P ∈ ρ, 1 ≤ reqSize P) (a : Config M) :
    ∃ o : Fin (ρ.length + 1) → Config M, IsSetOfflineSolution ρ o ∧ o 0 = a := by
  classical
  have h : ∀ P : SetRequest M, ∃ c : Config M, 1 ≤ reqSize P → ServesSet c P := by
    intro P
    by_cases hP : 1 ≤ reqSize P
    · obtain ⟨q, hq, _⟩ := exists_serving P hP
      exact ⟨setRepair a q, fun _ =>
        ⟨q.1, by simpa [setRepair] using (Finset.mem_sigma.1 hq).2⟩⟩
    · exact ⟨a, fun h => absurd h hP⟩
  choose c hc using h
  refine ⟨Fin.cases a (fun s => c ρ[s]), fun s => ?_, rfl⟩
  simp only [Fin.cases_succ]
  exact hc _ (hρ _ (List.getElem_mem s.2))

theorem set_opt_attained {k : ℕ} {M : Fin k → Type*} {ρ : List (SetRequest M)}
    (hρ : ∀ P ∈ ρ, 1 ≤ reqSize P) (a : Config M) :
    ∃ o : Fin (ρ.length + 1) → Config M, IsSetOfflineSolution ρ o ∧ o 0 = a ∧
      setOfflineCost ρ o = setOptCost a ρ := by
  obtain ⟨o, ho, h0⟩ := set_exists_offline_solution hρ a
  have hne : {C : ℕ | ∃ o : Fin (ρ.length + 1) → Config M,
      IsSetOfflineSolution ρ o ∧ o 0 = a ∧ setOfflineCost ρ o = C}.Nonempty :=
    ⟨_, o, ho, h0, rfl⟩
  obtain ⟨o', ho', h0', hc⟩ := Nat.sInf_mem hne
  exact ⟨o', ho', h0', hc⟩

end GeneralizedUniformServer.Dev.SetLazy
end
end

section
open scoped NNReal

noncomputable section

namespace GeneralizedUniformServer.Dev.SetBound

open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement
  GeneralizedUniformServer.Dev.SetCore GeneralizedUniformServer.Dev.SetDefs
  GeneralizedUniformServer.Dev.SetLazy

variable {k : ℕ} {M : Fin k → Type*}

lemma E_add' {α : Type*} (μ : PMF α) (f g : α → ENNReal) :
    E μ (fun a => f a + g a) = E μ f + E μ g := by
  simp [E, mul_add, ENNReal.tsum_add]

lemma pathCost_cons (y : Config M) (p : List (Config M)) :
    pathCost (y :: p) = lastStepCost (y :: p) + pathCost p := by
  cases p <;> simp [pathCost, lastStepCost]

lemma cost_eq_sum (a : Config M) (ρ : List (SetRequest M)) (t : ℕ) (ht : t ≤ ρ.length) :
    E (genTrajLaw (setAlg a) a ρ t) (fun p => (pathCost p : ENNReal)) =
      ∑ s ∈ Finset.range t,
        E (genTrajLaw (setAlg a) a ρ (s + 1)) (fun p => (lastStepCost p : ENNReal)) := by
  induction t with
  | zero => simp [genTrajLaw, E_pure, pathCost]
  | succ t ih =>
    have ht' : t < ρ.length := ht
    rw [Finset.sum_range_succ, ← ih ht'.le, traj_succ_E _ _ _ ht',
      traj_succ_E _ _ _ ht', ← E_add']
    congr 1
    ext p
    simp_rw [pathCost_cons, Nat.cast_add]
    rw [E_add', E_const, add_comm]

lemma Phi_anti (a : Config M) (ρ : List (SetRequest M)) (s : ℕ) (hs : s < ρ.length) :
    setTotalWeight a (ρ.take (s + 1)) ≤ setTotalWeight a (ρ.take s) := by
  rw [take_succ' ρ s hs]
  exact set_totalWeight_mono _ _ _

lemma log_bound (a : Config M) (B : ℕ) (ρ : List (SetRequest M))
    (hρ : ∀ P ∈ ρ, 1 ≤ reqSize P ∧ reqSize P ≤ B) (hne : ρ ≠ []) :
    -Real.log (setTotalWeight a ρ : ℝ) ≤ Real.log (2 * (B : ℝ)) * (setOptCost a ρ : ℝ) := by
  have hρ1 : ∀ P ∈ ρ, 1 ≤ reqSize P := fun P hP => (hρ P hP).1
  obtain ⟨o, ho, h0, hc⟩ := set_opt_attained hρ1 a
  obtain ⟨o', h1, h2, h3, h4⟩ := set_lazy_conversion ρ hρ1 o ho a
  obtain ⟨hA, hB⟩ := set_lazy_weight a B ρ hρ o' h1 h2 h3
  have hB1 : 1 ≤ B := by
    obtain ⟨P, hP⟩ := List.exists_mem_of_ne_nil _ hne
    exact (hρ P hP).1.trans (hρ P hP).2
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hm : setNumMoves ρ o' ≤ setOptCost a ρ := by
    have : UnitWeights.dist a (o 0) = 0 := by simp [h0, UnitWeights.dist]
    omega
  have hpow : (((2 * (B : ℝ)) ^ setNumMoves ρ o')⁻¹) ≤ (setTotalWeight a ρ : ℝ) := by
    have := (hB.trans hA)
    exact_mod_cast this
  have hpos : (0 : ℝ) < ((2 * (B : ℝ)) ^ setNumMoves ρ o')⁻¹ := by positivity
  have hl := Real.log_le_log hpos hpow
  rw [Real.log_inv, Real.log_pow] at hl
  have hlog : 0 ≤ Real.log (2 * (B : ℝ)) := Real.log_nonneg (by linarith)
  have : (setNumMoves ρ o' : ℝ) ≤ setOptCost a ρ := by exact_mod_cast hm
  nlinarith

lemma cost_bound (a : Config M) (B : ℕ) (ρ : List (SetRequest M))
    (hρ : ∀ P ∈ ρ, 1 ≤ reqSize P ∧ reqSize P ≤ B) :
    genExpectedCost (setAlg a) a ρ ≤
      ENNReal.ofReal (((k : ℝ) + 1) * Real.log (2 * (B : ℝ)) * (setOptCost a ρ : ℝ)) := by
  have hρ1 : ∀ P ∈ ρ, 1 ≤ reqSize P := fun P hP => (hρ P hP).1
  rcases eq_or_ne ρ [] with rfl | hne
  · simp [genExpectedCost, genTrajLaw, pathCost]
  have hc := cost_eq_sum a ρ ρ.length le_rfl
  have hE : genExpectedCost (setAlg a) a ρ = ∑ s ∈ Finset.range ρ.length,
      ∑' p : List (Config M), genTrajLaw (setAlg a) a ρ (s + 1) p * (lastStepCost p : ENNReal) :=
    hc
  rw [hE]
  have hle : ∀ s ∈ Finset.range ρ.length,
      ∑' p : List (Config M), genTrajLaw (setAlg a) a ρ (s + 1) p * (lastStepCost p : ENNReal) ≤
        ENNReal.ofReal (((k : ℝ) + 1) * (Real.log (setTotalWeight a (ρ.take s) : ℝ) -
          Real.log (setTotalWeight a (ρ.take (s + 1)) : ℝ))) := by
    intro s hs
    have hs' := Finset.mem_range.mp hs
    have := set_step_movement a ρ hρ1 (s + 1) (by omega) hs'
    simp only [Nat.add_sub_cancel] at this
    have h1 := set_totalWeight_pos (hρ_take hρ1 s) a
    have h2 := set_totalWeight_pos (hρ_take hρ1 (s + 1)) a
    rwa [Real.log_div h1.ne' h2.ne'] at this
  refine (Finset.sum_le_sum hle).trans ?_
  have hnn : ∀ s ∈ Finset.range ρ.length,
      0 ≤ ((k : ℝ) + 1) * (Real.log (setTotalWeight a (ρ.take s) : ℝ) -
          Real.log (setTotalWeight a (ρ.take (s + 1)) : ℝ)) := by
    intro s hs
    have hs' := Finset.mem_range.mp hs
    have h2 := set_totalWeight_pos (hρ_take hρ1 (s + 1)) a
    have h3 : (setTotalWeight a (ρ.take (s + 1)) : ℝ) ≤ setTotalWeight a (ρ.take s) := by
      exact_mod_cast Phi_anti a ρ s hs'
    have := Real.log_le_log h2 h3
    positivity
  rw [← ENNReal.ofReal_sum_of_nonneg hnn, ← Finset.mul_sum]
  rw [Finset.sum_range_sub' (fun s => Real.log (setTotalWeight a (ρ.take s) : ℝ))]
  apply ENNReal.ofReal_le_ofReal
  simp only [List.take_zero, set_totalWeight_nil, NNReal.coe_one, Real.log_one, zero_sub,
    List.take_length]
  have := log_bound a B ρ hρ hne
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  nlinarith

end GeneralizedUniformServer.Dev.SetBound

namespace GeneralizedUniformServer

open GeneralizedUniformServer.UnitWeights GeneralizedUniformServer.UnitWeights.Supplement

theorem chk_set_request_bound {k : ℕ} {M : Fin k → Type*} (a : Config M) (B : ℕ)
    (ρ : List (SetRequest M)) (hρ : ∀ P ∈ ρ, 1 ≤ reqSize P ∧ reqSize P ≤ B) :
    genExpectedCost (setAlg a) a ρ ≤
      ENNReal.ofReal (((k : ℝ) + 1) * Real.log (2 * (B : ℝ)) * (setOptCost a ρ : ℝ)) :=
  Dev.SetBound.cost_bound a B ρ hρ

end GeneralizedUniformServer
end
end

theorem solution : type_of% @GeneralizedUniformServer.chk_set_request_bound := @GeneralizedUniformServer.chk_set_request_bound
