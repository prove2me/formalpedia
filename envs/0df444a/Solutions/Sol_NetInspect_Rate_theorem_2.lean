-- Prove2me | solution 1 for NetInspect.Rate.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-28T06:17:10.272984+00:00
-- url     : https://prove2.me/submissions/b03be2a2-07e1-483d-bac1-9b09dfc34a70

import Definitions.Def_BlottoLP_Flow_ZeroSum
import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_NetInspect_Rate_Model
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Theorems.Thm_NetInspect_Rate_theorem_2_step_ia
import Mathlib.Algebra.BigOperators.Ring.Finset
import Theorems.Thm_NetInspect_Rate_lemma_EC_4
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp


namespace BlottoLP.Flow
open Finset
variable {α β : Type*} [Fintype α] [Fintype β]

lemma nr20261028_expPay_affine_left (M : α → β → ℝ) (σ σ' : α → ℝ) (τ : β → ℝ) (a b : ℝ) :
    expPay M (a • σ + b • σ') τ = a * expPay M σ τ + b * expPay M σ' τ := by
  simp only [expPay, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

lemma nr20261028_expPay_affine_right (M : α → β → ℝ) (σ : α → ℝ) (τ τ' : β → ℝ) (a b : ℝ) :
    expPay M σ (a • τ + b • τ') = a * expPay M σ τ + b * expPay M σ τ' := by
  simp only [expPay, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

/-- Every finite nonempty real zero-sum game has a mixed Nash equilibrium. -/
theorem nr20261028_exists_isNashEq [Nonempty α] [Nonempty β] (M : α → β → ℝ) :
    ∃ σ τ, IsNashEq M σ τ := by
  classical
  have hcontσ (τ : β → ℝ) : Continuous (fun σ => expPay M σ τ) := by
    unfold expPay
    fun_prop
  have hcontτ (σ : α → ℝ) : Continuous (fun τ => expPay M σ τ) := by
    unfold expPay
    fun_prop
  have hconv (σ : α → ℝ) : ConvexOn ℝ (stdSimplex ℝ β) (fun τ => expPay M σ τ) := by
    refine ⟨convex_stdSimplex _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    exact (nr20261028_expPay_affine_right M σ x y a b).le
  have hconc (τ : β → ℝ) : ConcaveOn ℝ (stdSimplex ℝ α) (fun σ => expPay M σ τ) := by
    refine ⟨convex_stdSimplex _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    exact (nr20261028_expPay_affine_left M x y τ a b).ge
  obtain ⟨τ, hτ, σ, hσ, hs⟩ := Sion.exists_isSaddlePointOn
    (f := fun τ σ => expPay M σ τ)
    ⟨_, single_mem_stdSimplex ℝ (Classical.choice inferInstance : β)⟩
    (convex_stdSimplex ℝ β) (isCompact_stdSimplex ℝ β)
    (fun σ _ => (hcontτ σ).lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun σ _ => (hconv σ).quasiconvexOn)
    (convex_stdSimplex ℝ α)
    ⟨_, single_mem_stdSimplex ℝ (Classical.choice inferInstance : α)⟩
    (isCompact_stdSimplex ℝ α)
    (fun τ _ => (hcontσ τ).upperSemicontinuous.upperSemicontinuousOn _)
    (fun τ _ => (hconc τ).quasiconcaveOn)
  refine ⟨σ, τ, hσ, hτ, ?_, ?_⟩
  · intro σ' hσ'
    exact hs τ hτ σ' hσ'
  · intro τ' hτ'
    exact hs τ' hτ' σ hσ

 theorem IsNashEq.nr20261028_expPay_eq {M : α → β → ℝ} {σ σ' : α → ℝ} {τ τ' : β → ℝ}
    (h : IsNashEq M σ τ) (h' : IsNashEq M σ' τ') :
    expPay M σ τ = expPay M σ' τ' := by
  apply le_antisymm
  · exact (h.2.2.2 τ' h'.2.1).trans (h'.2.2.1 σ h.1)
  · exact (h'.2.2.2 τ h.2.1).trans (h.2.2.1 σ' h'.1)

 theorem IsNashEq.nr20261028_cross {M : α → β → ℝ} {σ σ' : α → ℝ} {τ τ' : β → ℝ}
    (h : IsNashEq M σ τ) (h' : IsNashEq M σ' τ') : IsNashEq M σ τ' := by
  have hv := h.nr20261028_expPay_eq h'
  have hx : expPay M σ τ' = expPay M σ τ := by
    apply le_antisymm
    · exact (h'.2.2.1 σ h.1).trans hv.ge
    · exact h.2.2.2 τ' h'.2.1
  refine ⟨h.1, h'.2.1, ?_, ?_⟩
  · intro ρ hρ
    rw [hx, hv]
    exact h'.2.2.1 ρ hρ
  · intro ρ hρ
    rw [hx]
    exact h.2.2.2 ρ hρ

lemma nr20261028_expPay_eq_sum_pure_left [DecidableEq α] (M : α → β → ℝ) (σ : α → ℝ) (τ : β → ℝ) :
    expPay M σ τ = ∑ a, σ a * expPay M (pureMixed a) τ := by
  simp only [expPay, pureMixed]
  simp [Finset.mul_sum, mul_assoc]

lemma nr20261028_expPay_eq_sum_pure_right [DecidableEq β] (M : α → β → ℝ) (σ : α → ℝ) (τ : β → ℝ) :
    expPay M σ τ = ∑ b, τ b * expPay M σ (pureMixed b) := by
  simp only [expPay, pureMixed]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma nr20261028_expPay_le_of_pure_left [DecidableEq α] (M : α → β → ℝ) {σ : α → ℝ}
    (hσ : IsMixed σ) (τ : β → ℝ) (v : ℝ)
    (h : ∀ a, expPay M (pureMixed a) τ ≤ v) : expPay M σ τ ≤ v := by
  rw [nr20261028_expPay_eq_sum_pure_left]
  calc
    _ ≤ ∑ a, σ a * v := Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (hσ.1 a)
    _ = v := by rw [← Finset.sum_mul, hσ.2, one_mul]

lemma nr20261028_le_expPay_of_pure_right [DecidableEq β] (M : α → β → ℝ) (σ : α → ℝ)
    {τ : β → ℝ} (hτ : IsMixed τ) (v : ℝ)
    (h : ∀ b, v ≤ expPay M σ (pureMixed b)) : v ≤ expPay M σ τ := by
  rw [nr20261028_expPay_eq_sum_pure_right]
  calc
    v = ∑ b, τ b * v := by rw [← Finset.sum_mul, hτ.2, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (h b) (hτ.1 b)

end BlottoLP.Flow




namespace NetInspect.Rate
open Finset DetectionModel
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem nr20261028_packing_sizes_nonempty (G : DetectionModel V E) :
    {k : ℕ | ∃ T : Finset E, T.card = k ∧ G.IsSetPacking T}.Nonempty := by
  refine ⟨0, ∅, rfl, ?_⟩
  intro i
  simp [F]

theorem nr20261028_packing_sizes_bddAbove (G : DetectionModel V E) :
    BddAbove {k : ℕ | ∃ T : Finset E, T.card = k ∧ G.IsSetPacking T} := by
  refine ⟨Fintype.card E, ?_⟩
  rintro k ⟨T, rfl, _⟩
  exact card_le_univ T

theorem nr20261028_exists_max_packing (G : DetectionModel V E) :
    ∃ T : Finset E, T.card = G.mStar ∧ G.IsSetPacking T :=
  Nat.sSup_mem (nr20261028_packing_sizes_nonempty G) (nr20261028_packing_sizes_bddAbove G)

theorem nr20261028_mStar_le_card_packing (G : DetectionModel V E) : G.mStar ≤ Fintype.card E := by
  obtain ⟨T, ht, _⟩ := nr20261028_exists_max_packing G
  rw [← ht]
  exact card_le_univ T

theorem nr20261028_one_le_mStar_of_nonempty (G : DetectionModel V E) [Nonempty E] : 1 ≤ G.mStar := by
  classical
  obtain ⟨e⟩ := ‹Nonempty E›
  apply le_csSup (nr20261028_packing_sizes_bddAbove G)
  refine ⟨{e}, by simp, ?_⟩
  intro i
  unfold F
  exact (card_le_card inter_subset_right).trans (by simp)

theorem nr20261028_F_le_card_of_packing (G : DetectionModel V E) (S : Finset V) (T : Finset E)
    (hT : G.IsSetPacking T) : G.F S T ≤ S.card := by
  classical
  have heq : G.CS S ∩ T = S.biUnion (fun i => G.C i ∩ T) := by
    ext e
    simp only [CS, mem_inter, mem_biUnion]
    constructor
    · rintro ⟨⟨i, hi, hie⟩, he⟩
      exact ⟨i, hi, hie, he⟩
    · rintro ⟨i, hi, hie, he⟩
      exact ⟨⟨i, hi, hie⟩, he⟩
  unfold F
  rw [heq]
  calc
    _ ≤ ∑ i ∈ S, (G.C i ∩ T).card := card_biUnion_le
    _ ≤ ∑ _i ∈ S, 1 := by
      apply sum_le_sum
      intro i _
      simpa [F, CS] using hT i
    _ = S.card := by simp

end NetInspect.Rate



namespace NetInspect.Rate
open Finset DetectionModel BlottoLP.Flow
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

 def nr20261028_coverage (G : DetectionModel V E) (p : E → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ G.CS S, p e

 theorem nr20261028_coverage_minimax [Nonempty E] (G : DetectionModel V E) (b : ℕ) :
    ∃ (p : E → ℝ) (v : ℝ), IsMixed p ∧
      (∀ S : Finset V, S.card ≤ b → nr20261028_coverage G p S ≤ v) ∧
      (∀ q : E → ℝ, IsMixed q → ∃ S : Finset V, S.card ≤ b ∧ v ≤ nr20261028_coverage G q S) := by
  classical
  letI : Nonempty (Act V b) := ⟨⟨∅, by simp⟩⟩
  let M : Act V b → E → ℝ := fun S e => if e ∈ G.CS S.1 then 1 else 0
  have hpure (S : Act V b) (p : E → ℝ) : expPay M (pureMixed S) p = nr20261028_coverage G p S.1 := by
    simp [expPay, pureMixed, M, nr20261028_coverage, mul_ite, sum_ite]
  obtain ⟨σ, p, hne⟩ := nr20261028_exists_isNashEq M
  let v := expPay M σ p
  refine ⟨p, v, hne.2.1, ?_, ?_⟩
  · intro S hS
    let s : Act V b := ⟨S, hS⟩
    have hs : IsMixed (pureMixed s) := by
      constructor
      · intro a; simp only [pureMixed]; split_ifs <;> norm_num
      · simp [pureMixed]
    simpa [hpure] using hne.2.2.1 (pureMixed s) hs
  · intro q hq
    obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image (univ : Finset (Act V b))
      (fun S => nr20261028_coverage G q S.1) (by simp)
    refine ⟨S.1, S.2, ?_⟩
    calc
      v ≤ expPay M σ q := hne.2.2.2 q hq
      _ ≤ nr20261028_coverage G q S.1 := nr20261028_expPay_le_of_pure_left M hne.1 q _ (by
        intro T
        rw [hpure]
        exact hmax T (mem_univ _))

 theorem nr20261028_uniform_packing_coverage [Nonempty E] (G : DetectionModel V E) (b : ℕ) :
    ∃ q : E → ℝ, IsMixed q ∧ (∀ e, q e ≤ 1 / (G.mStar : ℝ)) ∧
      ∀ S : Finset V, S.card ≤ b → nr20261028_coverage G q S ≤ (b : ℝ) / G.mStar := by
  classical
  obtain ⟨T, hTc, hT⟩ := nr20261028_exists_max_packing G
  have hmN : 0 < G.mStar := lt_of_lt_of_le Nat.zero_lt_one (nr20261028_one_le_mStar_of_nonempty G)
  have hm : (0 : ℝ) < G.mStar := by exact_mod_cast hmN
  let q : E → ℝ := fun e => if e ∈ T then (G.mStar : ℝ)⁻¹ else 0
  refine ⟨q, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro e
    dsimp [q]
    split_ifs <;> positivity
  · simp [q, sum_ite, hTc, hm.ne']
  · intro e
    dsimp [q]
    split_ifs <;> simp [one_div, hm.le]
  · intro S hS
    have heq : nr20261028_coverage G q S = (G.F S T : ℝ) / G.mStar := by
      simp [nr20261028_coverage, q, sum_ite, filter_mem_eq_inter, F, div_eq_mul_inv]
    rw [heq]
    apply div_le_div_of_nonneg_right _ hm.le
    exact_mod_cast (nr20261028_F_le_card_of_packing G S T hT).trans hS

 theorem nr20261028_exists_coverage_minimax [Nonempty E] (G : DetectionModel V E) (b : ℕ) :
    ∃ (p : E → ℝ) (v : ℝ), IsMixed p ∧ v ≤ (b : ℝ) / G.mStar ∧
      (∀ S : Finset V, S.card ≤ b → ∑ e ∈ G.CS S, p e ≤ v) ∧
      (∀ q : E → ℝ, IsMixed q → ∃ S : Finset V, S.card ≤ b ∧ v ≤ ∑ e ∈ G.CS S, q e) := by
  obtain ⟨p, v, hp, hupper, hlower⟩ := nr20261028_coverage_minimax G b
  obtain ⟨q, hq, hcap, hbound⟩ := nr20261028_uniform_packing_coverage G b
  obtain ⟨S, hS, hv⟩ := hlower q hq
  exact ⟨p, v, hp, hv.trans (hbound S hS), hupper, hlower⟩

end NetInspect.Rate





namespace NetInspect.Rate
open Finset DetectionModel

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem nr20261028_undet_eq_sum (G : DetectionModel V E) (S : Finset V) (T : Finset E) :
    G.undet S T = ∑ e ∈ T, if e ∈ G.CS S then (0 : ℝ) else 1 := by
  classical
  have hc : ∑ e ∈ T, (if e ∈ G.CS S then (1 : ℝ) else 0) = (G.F S T : ℝ) := by
    simp [F, sum_ite, filter_mem_eq_inter, inter_comm]
  calc
    G.undet S T = (∑ _e ∈ T, (1 : ℝ)) -
        ∑ e ∈ T, (if e ∈ G.CS S then (1 : ℝ) else 0) := by simp [undet, hc]
    _ = ∑ e ∈ T, (1 - if e ∈ G.CS S then (1 : ℝ) else 0) := by rw [sum_sub_distrib]
    _ = _ := by apply sum_congr rfl; intro e _; split_ifs <;> norm_num

namespace DetectionModel
/-- Weighted probability that a component escapes inspection. No normalization assumption needed. -/
def nr20261028_missProb {b1 : ℕ} (G : DetectionModel V E) (σ1 : Act V b1 → ℝ) (e : E) : ℝ :=
  ∑ S, σ1 S * (if e ∈ G.CS S.1 then 0 else 1)
end DetectionModel

theorem nr20261028_U_eq_sum_marg {b1 b2 : ℕ} (G : DetectionModel V E)
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ) :
    G.U σ1 σ2 = ∑ e, marg σ2 e * G.nr20261028_missProb σ1 e := by
  classical
  have hu (S : Finset V) (T : Finset E) : G.undet S T =
      ∑ e, if e ∈ T then (if e ∈ G.CS S then (0 : ℝ) else 1) else 0 := by
    rw [nr20261028_undet_eq_sum]
    simp
  unfold U BlottoLP.Flow.expPay payoff
  simp_rw [hu, mul_sum]
  calc
    _ = ∑ T : Act E b2, ∑ e : E, ∑ S : Act V b1,
        σ2 T * σ1 S * (if e ∈ T.1 then (if e ∈ G.CS S.1 then (0 : ℝ) else 1) else 0) := by
      apply sum_congr rfl
      intro T _
      rw [sum_comm]
    _ = ∑ e : E, ∑ T : Act E b2, ∑ S : Act V b1,
        σ2 T * σ1 S * (if e ∈ T.1 then (if e ∈ G.CS S.1 then (0 : ℝ) else 1) else 0) := sum_comm
    _ = _ := by
      unfold marg nr20261028_missProb
      simp_rw [sum_mul, mul_sum]
      apply sum_congr rfl
      intro e _
      apply sum_congr rfl
      intro T _
      apply sum_congr rfl
      intro S _
      by_cases he : e ∈ T.1 <;> simp [he, mul_assoc]

theorem nr20261028_U_eq_of_marg_eq {b1 b2 b2' : ℕ} (G : DetectionModel V E)
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ) (τ2 : Act E b2' → ℝ)
    (h : ∀ e, marg σ2 e = marg τ2 e) : G.U σ1 σ2 = G.U σ1 τ2 := by
  simp only [nr20261028_U_eq_sum_marg, h]

theorem nr20261028_U_eq_mul_of_marg_eq_mul {b1 b2 b2' : ℕ} (G : DetectionModel V E)
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ) (τ2 : Act E b2' → ℝ) (c : ℝ)
    (h : ∀ e, marg σ2 e = c * marg τ2 e) : G.U σ1 σ2 = c * G.U σ1 τ2 := by
  simp only [nr20261028_U_eq_sum_marg, h, mul_sum, mul_assoc]

theorem nr20261028_missProb_nonneg {b1 : ℕ} (G : DetectionModel V E)
    (σ1 : Act V b1 → ℝ) (hσ : BlottoLP.Flow.IsMixed σ1) (e : E) :
    0 ≤ G.nr20261028_missProb σ1 e := by
  unfold DetectionModel.nr20261028_missProb
  apply sum_nonneg
  intro S _
  exact mul_nonneg (hσ.1 S) (by split_ifs <;> norm_num)

theorem nr20261028_missProb_le_one {b1 : ℕ} (G : DetectionModel V E)
    (σ1 : Act V b1 → ℝ) (hσ : BlottoLP.Flow.IsMixed σ1) (e : E) :
    G.nr20261028_missProb σ1 e ≤ 1 := by
  unfold DetectionModel.nr20261028_missProb
  calc
    _ ≤ ∑ S, σ1 S := by
      apply sum_le_sum
      intro S _
      split_ifs <;> simp [hσ.1 S]
    _ = 1 := hσ.2

end NetInspect.Rate




namespace NetInspect.Rate
open Finset DetectionModel BlottoLP.Flow
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

noncomputable def nr20261028_singletonExEquiv (E : Type*) [Fintype E] [DecidableEq E] : E ≃ ActEx E 1 :=
  Equiv.ofBijective (fun e => (⟨{e}, by simp⟩ : ActEx E 1)) (by
    constructor
    · intro e f h
      have hh := congrArg Subtype.val h
      simpa using hh
    · intro T
      obtain ⟨e, he⟩ := card_eq_one.mp T.2
      exact ⟨e, Subtype.ext he.symm⟩)

@[simp] theorem nr20261028_singletonExEquiv_apply (e : E) :
    (nr20261028_singletonExEquiv E e).1 = {e} := rfl

noncomputable def nr20261028_singletonExStrat (p : E → ℝ) : ActEx E 1 → ℝ :=
  fun T => p ((nr20261028_singletonExEquiv E).symm T)

@[simp] theorem nr20261028_singletonExStrat_apply (p : E → ℝ) (e : E) :
    nr20261028_singletonExStrat p (nr20261028_singletonExEquiv E e) = p e := by simp [nr20261028_singletonExStrat]

theorem nr20261028_singletonExStrat_mixed (p : E → ℝ) (hp : IsMixed p) : IsMixed (nr20261028_singletonExStrat p) := by
  refine ⟨fun T => hp.1 _, ?_⟩
  rw [← (nr20261028_singletonExEquiv E).sum_comp]
  simpa using hp.2

theorem nr20261028_singletonExStrat_marg (p : E → ℝ) (e : E) : marg (nr20261028_singletonExStrat p) e = p e := by
  classical
  unfold marg
  rw [← (nr20261028_singletonExEquiv E).sum_comp]
  simp

theorem nr20261028_payoffEx_singleton (G : DetectionModel V E) {b1 : ℕ} (p : E → ℝ)
    (hp : IsMixed p) (S : ActEx V b1) :
    expPay (G.payoffEx b1 1) (nr20261028_singletonExStrat p) (pureMixed S) =
      1 - ∑ e ∈ G.CS S.1, p e := by
  classical
  simp only [expPay, pureMixed, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    sum_ite_eq', sum_ite_eq, mem_univ, ↓reduceIte]
  rw [← (nr20261028_singletonExEquiv E).sum_comp]
  simp only [nr20261028_singletonExStrat_apply, payoffEx, nr20261028_singletonExEquiv_apply]
  simp_rw [nr20261028_undet_eq_sum]
  simp only [sum_singleton]
  have he (e : E) : p e * (if e ∈ G.CS S.1 then (0 : ℝ) else 1) =
      p e - if e ∈ G.CS S.1 then p e else 0 := by split_ifs <;> simp
  simp_rw [he]
  rw [sum_sub_distrib, hp.2]
  simp

theorem nr20261028_singletonExStrat_optLP2bar (G : DetectionModel V E) (b : ℕ)
    (hb : b ≤ Fintype.card V) (p : E → ℝ) (hp : IsMixed p) (v : ℝ)
    (hupper : ∀ S : Finset V, S.card ≤ b → ∑ e ∈ G.CS S, p e ≤ v)
    (hopt : ∀ q : E → ℝ, IsMixed q →
      ∃ S : Finset V, S.card ≤ b ∧ v ≤ ∑ e ∈ G.CS S, q e) :
    G.IsOptLP2bar b 1 (nr20261028_singletonExStrat p) := by
  classical
  obtain ⟨B, _, hB⟩ := exists_subset_card_eq (s := (univ : Finset V)) (by simpa using hb)
  letI : Nonempty (ActEx V b) := ⟨⟨B, hB⟩⟩
  refine ⟨nr20261028_singletonExStrat_mixed p hp, ?_⟩
  intro τ hτ
  let q : E → ℝ := fun e => τ (nr20261028_singletonExEquiv E e)
  have hq : IsMixed q := by
    refine ⟨fun e => hτ.1 _, ?_⟩
    simpa [q] using ((nr20261028_singletonExEquiv E).sum_comp τ).trans hτ.2
  have hτq : τ = nr20261028_singletonExStrat q := by
    funext T
    simp [nr20261028_singletonExStrat, q]
  obtain ⟨S, hS, hvS⟩ := hopt q hq
  obtain ⟨S', hSS', _, hS'⟩ := exists_subsuperset_card_eq (subset_univ S) hS
    (by simpa using hb)
  have hCS : G.CS S ⊆ G.CS S' := by
    intro e he
    obtain ⟨i, hi, hie⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨i, hSS' hi, hie⟩
  have hvS' : v ≤ ∑ e ∈ G.CS S', q e := hvS.trans
    (sum_le_sum_of_subset_of_nonneg hCS (fun e _ _ => hq.1 e))
  have hlow : 1 - v ≤ G.best2Ex b (nr20261028_singletonExStrat p) := by
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨X, rfl⟩
    change 1 - v ≤ expPay (G.payoffEx b 1) (nr20261028_singletonExStrat p) (pureMixed X)
    rw [nr20261028_payoffEx_singleton G p hp X]
    linarith [hupper X.1 X.2.le]
  have hup : G.best2Ex b τ ≤ 1 - v := by
    change sInf (Set.range (fun X : ActEx V b => expPay (G.payoffEx b 1) τ (pureMixed X))) ≤ 1 - v
    calc
      _ ≤ expPay (G.payoffEx b 1) τ (pureMixed (⟨S', hS'⟩ : ActEx V b)) :=
        csInf_le (Set.finite_range (fun X : ActEx V b =>
          expPay (G.payoffEx b 1) τ (pureMixed X))).bddBelow
          (Set.mem_range_self (⟨S', hS'⟩ : ActEx V b))
      _ = 1 - ∑ e ∈ G.CS S', q e := by rw [hτq, nr20261028_payoffEx_singleton G q hq]
      _ ≤ 1 - v := by linarith
  exact hup.trans hlow

end NetInspect.Rate




namespace NetInspect.Rate
open Finset DetectionModel BlottoLP.Flow
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

noncomputable def nr20261028_singletonExWeights (σ : ActEx E 1 → ℝ) : E → ℝ :=
  fun e => σ (nr20261028_singletonExEquiv E e)

 theorem nr20261028_singletonExWeights_mixed (σ : ActEx E 1 → ℝ) (hσ : IsMixed σ) :
    IsMixed (nr20261028_singletonExWeights σ) := by
  refine ⟨fun e => hσ.1 _, ?_⟩
  exact ((nr20261028_singletonExEquiv E).sum_comp σ).trans hσ.2

 theorem nr20261028_singletonExWeights_reconstruct (σ : ActEx E 1 → ℝ) :
    σ = nr20261028_singletonExStrat (nr20261028_singletonExWeights σ) := by
  funext T
  simp [nr20261028_singletonExStrat, nr20261028_singletonExWeights]

 theorem nr20261028_singletonExWeights_marg (σ : ActEx E 1 → ℝ) (e : E) :
    marg σ e = nr20261028_singletonExWeights σ e := by
  conv_lhs => rw [nr20261028_singletonExWeights_reconstruct σ]
  exact nr20261028_singletonExStrat_marg _ _

 theorem nr20261028_optimal_singleton_coverage_upper (G : DetectionModel V E) (b : ℕ)
    (hb : b ≤ Fintype.card V) (σex : ActEx E 1 → ℝ)
    (hopt : G.IsOptLP2bar b 1 σex) (p0 : E → ℝ) (hp0 : IsMixed p0) (v : ℝ)
    (hupper0 : ∀ S : Finset V, S.card ≤ b → ∑ e ∈ G.CS S, p0 e ≤ v) :
    ∀ S : Finset V, S.card ≤ b → ∑ e ∈ G.CS S, nr20261028_singletonExWeights σex e ≤ v := by
  classical
  obtain ⟨B, _, hB⟩ := exists_subset_card_eq (s := (univ : Finset V)) (by simpa using hb)
  letI : Nonempty (ActEx V b) := ⟨⟨B, hB⟩⟩
  have hp := nr20261028_singletonExWeights_mixed σex hopt.1
  have hlow : 1 - v ≤ G.best2Ex b (nr20261028_singletonExStrat p0) := by
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨X, rfl⟩
    change 1 - v ≤ expPay (G.payoffEx b 1) (nr20261028_singletonExStrat p0) (pureMixed X)
    rw [nr20261028_payoffEx_singleton G p0 hp0 X]
    linarith [hupper0 X.1 X.2.le]
  have hbest : 1 - v ≤ G.best2Ex b σex :=
    hlow.trans (hopt.2 (nr20261028_singletonExStrat p0) (nr20261028_singletonExStrat_mixed p0 hp0))
  have hexact (S : ActEx V b) : ∑ e ∈ G.CS S.1, nr20261028_singletonExWeights σex e ≤ v := by
    have hup : G.best2Ex b σex ≤
        expPay (G.payoffEx b 1) σex (pureMixed S) :=
      csInf_le (Set.finite_range (fun X : ActEx V b =>
        expPay (G.payoffEx b 1) σex (pureMixed X))).bddBelow (Set.mem_range_self S)
    rw [nr20261028_singletonExWeights_reconstruct σex, nr20261028_payoffEx_singleton G _ hp S] at hup
    have hbest' := hbest
    rw [nr20261028_singletonExWeights_reconstruct σex] at hbest'
    linarith
  intro S hS
  obtain ⟨S', hSS', _, hS'⟩ := exists_subsuperset_card_eq (subset_univ S) hS (by simpa using hb)
  have hCS : G.CS S ⊆ G.CS S' := by
    intro e he
    obtain ⟨i, hi, hie⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨i, hSS' hi, hie⟩
  exact (sum_le_sum_of_subset_of_nonneg hCS (fun e _ _ => hp.1 e)).trans
    (hexact ⟨S', hS'⟩)

end NetInspect.Rate




namespace NetInspect.Rate
open Finset

/-- The sum of attack marginals is the expected number of attacked components. -/
theorem nr20261028_sum_marg_eq_expected_card {E : Type*} [Fintype E] [DecidableEq E]
    {b : ℕ} (σ : Act E b → ℝ) :
    ∑ e, marg σ e = ∑ T, σ T * (T.1.card : ℝ) := by
  unfold marg
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  simp [Finset.sum_ite_mem, mul_comm]

/-- Every mixed strategy over plans of size at most b has total marginal mass at most b. -/
theorem nr20261028_sum_marg_le_budget {E : Type*} [Fintype E] [DecidableEq E]
    {b : ℕ} (σ : Act E b → ℝ) (hσ : BlottoLP.Flow.IsMixed σ) :
    ∑ e, marg σ e ≤ (b : ℝ) := by
  rw [nr20261028_sum_marg_eq_expected_card]
  calc
    _ ≤ ∑ T : Act E b, σ T * (b : ℝ) := by
      apply Finset.sum_le_sum
      intro T _
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast T.2) (hσ.1 T)
    _ = (b : ℝ) := by rw [← Finset.sum_mul, hσ.2, one_mul]

end NetInspect.Rate



namespace NetInspect.Rate
open Finset DetectionModel BlottoLP.Flow
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The exact conclusion of the network detection-rate theorem. -/
def nr20261028_DetectionRateConclusion (G : DetectionModel V E) (b1 : ℕ) : Prop :=
    (∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧
      ∀ b2 : ℕ, 1 ≤ b2 → b2 < G.mStar →
        ∀ (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ), G.IsNE b1 b2 σ1 σ2 → G.rate σ1 σ2 = r) ∧
    (∀ (σ1 : Act V b1 → ℝ) (σ2 : Act E 1 → ℝ), G.IsNE b1 1 σ1 σ2 →
      ∀ b2 : ℕ, 1 ≤ b2 → b2 < G.mStar →
        ∃ σ2' : Act E b2 → ℝ, G.IsNE b1 b2 σ1 σ2')

 theorem nr20261028_theorem_2_vacuous (G : DetectionModel V E) (b1 : ℕ) (hm : G.mStar ≤ 1) :
    nr20261028_DetectionRateConclusion G b1 := by
  refine ⟨⟨0, le_rfl, zero_le_one, ?_⟩, ?_⟩
  · intro b2 hb hm'
    omega
  · intro σ1 σ2 hne b2 hb hm'
    omega

 lemma nr20261028_mStar_le_card (G : DetectionModel V E) : G.mStar ≤ Fintype.card E := by
  apply csSup_le
  · exact ⟨0, ∅, by simp, by simp [IsSetPacking, F]⟩
  · rintro k ⟨T, rfl, hT⟩
    exact Finset.card_le_univ T

 lemma nr20261028_act_zero_eq_empty (S : Act V 0) : S.1 = ∅ :=
    Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero S.2)

 lemma nr20261028_mixed_zero_unique {σ τ : Act V 0 → ℝ} (hσ : IsMixed σ) (hτ : IsMixed τ) : σ = τ := by
  classical
  letI : Subsingleton (Act V 0) := ⟨fun S T => Subtype.ext ((nr20261028_act_zero_eq_empty S).trans (nr20261028_act_zero_eq_empty T).symm)⟩
  letI : Nonempty (Act V 0) := ⟨⟨∅, by simp⟩⟩
  funext S
  have hs : σ S = 1 := by
    have he : ∑ a, σ a = σ S := Finset.sum_eq_single S
      (fun a _ ha => False.elim (ha (Subsingleton.elim a S))) (by simp)
    exact he.symm.trans hσ.2
  have ht : τ S = 1 := by
    have he : ∑ a, τ a = τ S := Finset.sum_eq_single S
      (fun a _ ha => False.elim (ha (Subsingleton.elim a S))) (by simp)
    exact he.symm.trans hτ.2
  exact hs.trans ht.symm

 lemma nr20261028_zero_budget_payoff (G : DetectionModel V E) {b2 : ℕ}
    (T : Act E b2) (S : Act V 0) : G.payoff 0 b2 T S = T.1.card := by
  simp [payoff, undet, F, CS, nr20261028_act_zero_eq_empty S]

 theorem nr20261028_zero_budget_rate (G : DetectionModel V E) {b2 : ℕ} (hb : 1 ≤ b2)
    (hcard : b2 ≤ Fintype.card E) (σ1 : Act V 0 → ℝ) (σ2 : Act E b2 → ℝ)
    (hne : G.IsNE 0 b2 σ1 σ2) : G.rate σ1 σ2 = 0 := by
  classical
  have hp (τ : Act E b2 → ℝ) : expPay (G.payoff 0 b2) τ σ1 = ∑ T, τ T * (T.1.card : ℝ) := by
    unfold expPay
    apply sum_congr rfl
    intro T _
    simp_rw [nr20261028_zero_budget_payoff]
    calc
      _ = (τ T * (T.1.card : ℝ)) * ∑ S, σ1 S := by
        rw [mul_sum]
        apply sum_congr rfl
        intro S _
        ring
      _ = _ := by rw [hne.2.1.2, mul_one]
  obtain ⟨T, hTu, hTc⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset E)) hcard
  let t : Act E b2 := ⟨T, hTc.le⟩
  have ht : IsMixed (pureMixed t) := by
    constructor
    · intro a
      simp only [pureMixed]
      split_ifs <;> norm_num
    · simp [pureMixed]
  have hlo := hne.2.2.1 (pureMixed t) ht
  rw [hp, hp] at hlo
  have hpure : (∑ T : Act E b2, pureMixed t T * (T.1.card : ℝ)) = b2 := by
    simp [pureMixed, t, hTc]
  rw [hpure] at hlo
  have hsum : ∑ T : Act E b2, σ2 T * ((b2 : ℝ) - T.1.card) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hne.1.2, one_mul]
    have hhi : (∑ T : Act E b2, σ2 T * (T.1.card : ℝ)) ≤ b2 := by
      calc
        _ ≤ ∑ T : Act E b2, σ2 T * b2 := Finset.sum_le_sum fun T _ =>
          mul_le_mul_of_nonneg_left (by exact_mod_cast T.2) (hne.1.1 T)
        _ = b2 := by rw [← Finset.sum_mul, hne.1.2, one_mul]
    linarith
  have hnneg (T : Act E b2) : 0 ≤ σ2 T * ((b2 : ℝ) - T.1.card) :=
    mul_nonneg (hne.1.1 T) (sub_nonneg.mpr (by exact_mod_cast T.2))
  let emptyAct : Act E b2 := ⟨∅, by simp⟩
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun T _ => hnneg T).mp hsum emptyAct (mem_univ _)
  have he : σ2 emptyAct = 0 := by
    have hbR : (0 : ℝ) < b2 := by exact_mod_cast (show 0 < b2 by omega)
    simp only [emptyAct, card_empty, Nat.cast_zero, sub_zero] at hz
    exact (mul_eq_zero.mp hz).resolve_right hbR.ne'
  have hratio (S : Act V 0) (T : Act E b2) : G.ratio S.1 T.1 = if T = emptyAct then 1 else 0 := by
    by_cases h : T = emptyAct
    · subst T
      simp [ratio, emptyAct]
    · have hv : T.1 ≠ ∅ := fun hv => h (Subtype.ext hv)
      simp [ratio, hv, F, CS, nr20261028_act_zero_eq_empty S, h]
  unfold rate expPay
  simp_rw [hratio]
  simp [mul_ite, he]

 theorem nr20261028_theorem_2_zero (G : DetectionModel V E) : nr20261028_DetectionRateConclusion G 0 := by
  classical
  refine ⟨⟨0, le_rfl, zero_le_one, ?_⟩, ?_⟩
  · intro b2 hb hm σ1 σ2 hne
    exact nr20261028_zero_budget_rate G hb (le_trans hm.le (nr20261028_mStar_le_card G)) σ1 σ2 hne
  · intro σ1 σ2 hne b2 hb hm
    letI : Nonempty (Act E b2) := ⟨⟨∅, by simp⟩⟩
    letI : Nonempty (Act V 0) := ⟨⟨∅, by simp⟩⟩
    obtain ⟨τ2, τ1, hτ⟩ := nr20261028_exists_isNashEq (G.payoff 0 b2)
    have heq : τ1 = σ1 := nr20261028_mixed_zero_unique hτ.2.1 hne.2.1
    exact ⟨τ2, heq ▸ hτ⟩

lemma nr20261028_undet_nonneg (G : DetectionModel V E) (S : Finset V) (T : Finset E) :
    0 ≤ G.undet S T := by
  unfold undet
  exact sub_nonneg.mpr (by exact_mod_cast (card_le_card (inter_subset_right : G.CS S ∩ T ⊆ T)))

lemma nr20261028_U_nonneg (G : DetectionModel V E) {b1 b2 : ℕ}
    {σ1 : Act V b1 → ℝ} {σ2 : Act E b2 → ℝ}
    (h1 : IsMixed σ1) (h2 : IsMixed σ2) : 0 ≤ G.U σ1 σ2 := by
  exact sum_nonneg fun T _ => sum_nonneg fun S _ =>
    mul_nonneg (mul_nonneg (h2.1 T) (h1.1 S)) (nr20261028_undet_nonneg G S.1 T.1)

lemma nr20261028_ratio_eq_one_of_undet_eq_zero (G : DetectionModel V E) (S : Finset V) (T : Finset E)
    (h : G.undet S T = 0) : G.ratio S T = 1 := by
  unfold ratio
  split_ifs with ht
  · rfl
  · have hc : (T.card : ℝ) ≠ 0 := by exact_mod_cast (card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr ht))
    have hf : (G.F S T : ℝ) = T.card := by unfold undet at h; linarith
    rw [hf, div_self hc]

 theorem nr20261028_rate_eq_one_of_U_eq_zero (G : DetectionModel V E) {b1 b2 : ℕ}
    {σ1 : Act V b1 → ℝ} {σ2 : Act E b2 → ℝ}
    (h1 : IsMixed σ1) (h2 : IsMixed σ2) (hu : G.U σ1 σ2 = 0) : G.rate σ1 σ2 = 1 := by
  classical
  have hn (T : Act E b2) (S : Act V b1) :
      0 ≤ σ2 T * σ1 S * G.undet S.1 T.1 :=
    mul_nonneg (mul_nonneg (h2.1 T) (h1.1 S)) (nr20261028_undet_nonneg G S.1 T.1)
  have hz (T : Act E b2) (S : Act V b1) : σ2 T * σ1 S * G.undet S.1 T.1 = 0 := by
    have hrow := (sum_eq_zero_iff_of_nonneg fun T _ => sum_nonneg fun S _ => hn T S).mp hu T (mem_univ _)
    exact (sum_eq_zero_iff_of_nonneg fun S _ => hn T S).mp hrow S (mem_univ _)
  have ht (T : Act E b2) (S : Act V b1) : σ2 T * σ1 S * G.ratio S.1 T.1 = σ2 T * σ1 S := by
    by_cases hw : σ2 T * σ1 S = 0
    · rw [hw, zero_mul]
    · have hu' : G.undet S.1 T.1 = 0 := (mul_eq_zero.mp (hz T S)).resolve_left hw
      rw [nr20261028_ratio_eq_one_of_undet_eq_zero G S.1 T.1 hu', mul_one]
  unfold rate expPay
  simp_rw [ht, ← mul_sum, h1.2, mul_one, h2.2]

lemma nr20261028_exists_cover_le (G : DetectionModel V E) {b1 : ℕ} (hb : G.nStar ≤ b1) :
    ∃ S : Act V b1, G.IsSetCover S.1 := by
  have huniv : G.IsSetCover univ := by
    intro e
    obtain ⟨i, hi⟩ := G.coverable e
    have he : e ∈ G.CS univ := mem_biUnion.mpr ⟨i, mem_univ _, hi⟩
    simp [F, he]
  have hne : {k | ∃ S : Finset V, S.card = k ∧ G.IsSetCover S}.Nonempty :=
    ⟨_, univ, rfl, huniv⟩
  obtain ⟨S, hS, hc⟩ := Nat.sInf_mem hne
  exact ⟨⟨S, hS ▸ hb⟩, hc⟩

lemma nr20261028_cover_undet (G : DetectionModel V E) (S : Finset V) (hc : G.IsSetCover S)
    (T : Finset E) : G.undet S T = 0 := by
  have hmem e : e ∈ G.CS S := by
    have h := hc e
    by_contra hn
    simp [F, hn] at h
  have hsub : T ⊆ G.CS S := fun e _ => hmem e
  simp [undet, F, inter_eq_right.mpr hsub]

 theorem nr20261028_equilibrium_U_zero_of_cover (G : DetectionModel V E) {b1 b2 : ℕ}
    (hb : G.nStar ≤ b1) {σ1 : Act V b1 → ℝ} {σ2 : Act E b2 → ℝ}
    (hne : G.IsNE b1 b2 σ1 σ2) : G.U σ1 σ2 = 0 := by
  classical
  obtain ⟨S, hc⟩ := nr20261028_exists_cover_le G hb
  have hp : IsMixed (pureMixed S) := by
    constructor
    · intro a; simp only [pureMixed]; split_ifs <;> norm_num
    · simp [pureMixed]
  have h := hne.2.2.2 (pureMixed S) hp
  have hz : expPay (G.payoff b1 b2) σ2 (pureMixed S) = 0 := by
    simp [expPay, pureMixed, payoff, nr20261028_cover_undet G S.1 hc]
  rw [hz] at h
  exact le_antisymm h (nr20261028_U_nonneg G hne.2.1 hne.1)

lemma nr20261028_U_pure_singleton (G : DetectionModel V E) {b1 : ℕ}
    (σ1 : Act V b1 → ℝ) (e : E) :
    G.U σ1 (pureMixed (⟨{e}, by simp⟩ : Act E 1)) = G.nr20261028_missProb σ1 e := by
  classical
  simp [U, expPay, pureMixed, payoff, nr20261028_undet_eq_sum, DetectionModel.nr20261028_missProb]

 theorem nr20261028_theorem_2_cover (G : DetectionModel V E) {b1 : ℕ} (hb : G.nStar ≤ b1) :
    nr20261028_DetectionRateConclusion G b1 := by
  classical
  refine ⟨⟨1, zero_le_one, le_rfl, ?_⟩, ?_⟩
  · intro b2 hb2 hm σ1 σ2 hne
    exact nr20261028_rate_eq_one_of_U_eq_zero G hne.2.1 hne.1 (nr20261028_equilibrium_U_zero_of_cover G hb hne)
  · intro σ1 σ2 hne b2 hb2 hm
    have hu : G.U σ1 σ2 = 0 := nr20261028_equilibrium_U_zero_of_cover G hb hne
    have hmiss (e : E) : G.nr20261028_missProb σ1 e = 0 := by
      let t : Act E 1 := ⟨{e}, by simp⟩
      have ht : IsMixed (pureMixed t) := by
        constructor
        · intro a; simp only [pureMixed]; split_ifs <;> norm_num
        · simp [pureMixed]
      have h := hne.2.2.1 (pureMixed t) ht
      change G.U σ1 (pureMixed t) ≤ G.U σ1 σ2 at h
      rw [hu] at h
      have hh : G.U σ1 (pureMixed t) = G.nr20261028_missProb σ1 e := nr20261028_U_pure_singleton G σ1 e
      rw [hh] at h
      exact le_antisymm h (nr20261028_missProb_nonneg G σ1 hne.2.1 e)
    have hzero (τ : Act E b2 → ℝ) : G.U σ1 τ = 0 := by
      rw [nr20261028_U_eq_sum_marg]
      simp [hmiss]
    let emptyAct : Act E b2 := ⟨∅, by simp⟩
    have he : IsMixed (pureMixed emptyAct) := by
      constructor
      · intro a; simp only [pureMixed]; split_ifs <;> norm_num
      · simp [pureMixed]
    refine ⟨pureMixed emptyAct, he, hne.2.1, ?_, ?_⟩
    · intro τ hτ
      change G.U σ1 τ ≤ G.U σ1 (pureMixed emptyAct)
      rw [hzero, hzero]
    · intro τ hτ
      change G.U σ1 (pureMixed emptyAct) ≤ G.U τ (pureMixed emptyAct)
      rw [hzero]
      exact nr20261028_U_nonneg G hτ he

end NetInspect.Rate








namespace NetInspect.Rate
open Finset DetectionModel BlottoLP.Flow
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem nr20261028_marg_nonneg_of_mixed {b : ℕ} (σ : Act E b → ℝ) (hσ : IsMixed σ) (e : E) :
    0 ≤ marg σ e := by
  classical
  unfold marg
  apply sum_nonneg
  intro T _
  split_ifs
  · exact hσ.1 T
  · exact le_rfl

theorem nr20261028_complete_single_marginals [Nonempty E] (σ : Act E 1 → ℝ) (hσ : IsMixed σ) :
    ∃ q : E → ℝ, IsMixed q ∧ ∀ e, marg σ e ≤ q e := by
  classical
  let e0 : E := Classical.choice inferInstance
  let M := ∑ e, marg σ e
  have hM : M ≤ 1 := by simpa [M] using nr20261028_sum_marg_le_budget σ hσ
  let q : E → ℝ := fun e => marg σ e + if e = e0 then 1 - M else 0
  refine ⟨q, ⟨?_, ?_⟩, ?_⟩
  · intro e
    exact add_nonneg (nr20261028_marg_nonneg_of_mixed σ hσ e) (by split_ifs <;> linarith)
  · dsimp [q]
    rw [sum_add_distrib]
    simp [M]
    <;> ring
  · intro e
    dsimp [q]
    have : 0 ≤ if e = e0 then 1 - M else 0 := by split_ifs <;> linarith
    linarith

theorem nr20261028_U_pure_eq_marg_sum {b1 b2 : ℕ} (G : DetectionModel V E)
    (S : Act V b1) (σ2 : Act E b2 → ℝ) :
    G.U (pureMixed S) σ2 = ∑ e, marg σ2 e * (if e ∈ G.CS S.1 then (0 : ℝ) else 1) := by
  classical
  rw [nr20261028_U_eq_sum_marg]
  simp only [DetectionModel.nr20261028_missProb, pureMixed, ite_mul, one_mul, zero_mul,
    sum_ite_eq', sum_ite_eq, mem_univ, ↓reduceIte]

theorem nr20261028_sum_miss_eq_one_sub_coverage (G : DetectionModel V E)
    (q : E → ℝ) (hq : IsMixed q) (S : Finset V) :
    (∑ e, q e * (if e ∈ G.CS S then (0 : ℝ) else 1)) = 1 - ∑ e ∈ G.CS S, q e := by
  classical
  have he (e : E) : q e * (if e ∈ G.CS S then (0 : ℝ) else 1) =
      q e - if e ∈ G.CS S then q e else 0 := by split_ifs <;> simp
  simp_rw [he]
  rw [sum_sub_distrib, hq.2]
  simp

theorem nr20261028_single_equilibrium_of_capped_coverage [Nonempty E] (G : DetectionModel V E)
    (b : ℕ) (hm : 1 < G.mStar) (p : E → ℝ) (hp : IsMixed p)
    (hcap : ∀ e, p e ≤ 1 / (G.mStar : ℝ)) (v : ℝ)
    (hupper : ∀ S : Finset V, S.card ≤ b → ∑ e ∈ G.CS S, p e ≤ v)
    (hopt : ∀ q : E → ℝ, IsMixed q →
      ∃ S : Finset V, S.card ≤ b ∧ v ≤ ∑ e ∈ G.CS S, q e)
    (σ1 : Act V b → ℝ) (σ2 : Act E 1 → ℝ) (hne : G.IsNE b 1 σ1 σ2) :
    ∃ τ2 : Act E 1 → ℝ, G.IsNE b 1 σ1 τ2 ∧ (∀ e, marg τ2 e = p e) ∧
      G.U σ1 τ2 = 1 - v := by
  classical
  have hmR : (1 : ℝ) < G.mStar := by exact_mod_cast hm
  have hp1 : ∀ e, 0 ≤ p e ∧ p e ≤ 1 := by
    intro e
    exact ⟨hp.1 e, (hcap e).trans (by apply (div_le_one (by positivity)).2; linarith)⟩
  obtain ⟨τ2, hτ2, hmarg⟩ := lemma_EC_4 G hm p hp1 (by simpa using hp.2)
  obtain ⟨q, hq, hqge⟩ := nr20261028_complete_single_marginals σ2 hne.1
  obtain ⟨S, hS, hvS⟩ := hopt q hq
  let s : Act V b := ⟨S, hS⟩
  have hs : IsMixed (pureMixed s) := by
    constructor
    · intro X; simp only [pureMixed]; split_ifs <;> norm_num
    · simp [pureMixed]
  have huv : G.U σ1 σ2 ≤ 1 - v := by
    calc
      _ ≤ G.U (pureMixed s) σ2 := hne.2.2.2 (pureMixed s) hs
      _ ≤ ∑ e, q e * (if e ∈ G.CS S then (0 : ℝ) else 1) := by
        rw [nr20261028_U_pure_eq_marg_sum]
        exact sum_le_sum fun e _ => mul_le_mul_of_nonneg_right (hqge e) (by split_ifs <;> norm_num)
      _ = 1 - ∑ e ∈ G.CS S, q e := nr20261028_sum_miss_eq_one_sub_coverage G q hq S
      _ ≤ 1 - v := by linarith
  have hsecure (ρ : Act V b → ℝ) (hρ : IsMixed ρ) : 1 - v ≤ G.U ρ τ2 := by
    apply nr20261028_le_expPay_of_pure_right (G.payoff b 1) τ2 hρ (1 - v)
    intro X
    change 1 - v ≤ G.U (pureMixed X) τ2
    rw [nr20261028_U_pure_eq_marg_sum]
    simp_rw [hmarg]
    rw [nr20261028_sum_miss_eq_one_sub_coverage G p hp]
    linarith [hupper X.1 X.2]
  have ht : G.U σ1 τ2 = 1 - v := le_antisymm
    ((hne.2.2.1 τ2 hτ2).trans huv) (hsecure σ1 hne.2.1)
  have horig : G.U σ1 σ2 = 1 - v := le_antisymm huv
    ((hsecure σ1 hne.2.1).trans (hne.2.2.1 τ2 hτ2))
  refine ⟨τ2, ⟨hτ2, hne.2.1, ?_, ?_⟩, hmarg, ht⟩
  · intro ρ hρ
    change G.U σ1 ρ ≤ G.U σ1 τ2
    rw [ht, ← horig]
    exact hne.2.2.1 ρ hρ
  · intro ρ hρ
    change G.U σ1 τ2 ≤ G.U ρ τ2
    rw [ht]
    exact hsecure ρ hρ

theorem nr20261028_scale_capped_equilibrium (G : DetectionModel V E) {b1 b2 : ℕ}
    (σ1 : Act V b1 → ℝ) (τ1 : Act E 1 → ℝ) (hne : G.IsNE b1 1 σ1 τ1)
    (p : E → ℝ) (hp : IsMixed p) (hmarg : ∀ e, marg τ1 e = p e)
    (hcap : ∀ e, p e ≤ 1 / (G.mStar : ℝ)) (hb2 : 1 ≤ b2) (hbm : b2 < G.mStar) :
    ∃ τ2 : Act E b2 → ℝ, G.IsNE b1 b2 σ1 τ2 ∧
      G.U σ1 τ2 = (b2 : ℝ) * G.U σ1 τ1 ∧
      ∀ e, G.nr20261028_missProb σ1 e ≤ G.U σ1 τ1 := by
  classical
  have hmN : 0 < G.mStar := by omega
  have hmR : (0 : ℝ) < G.mStar := by exact_mod_cast hmN
  have hbR : (b2 : ℝ) < G.mStar := by exact_mod_cast hbm
  let ρ : E → ℝ := fun e => (b2 : ℝ) * p e
  have hρ : ∀ e, 0 ≤ ρ e ∧ ρ e ≤ 1 := by
    intro e
    refine ⟨mul_nonneg (Nat.cast_nonneg _) (hp.1 e), ?_⟩
    calc
      ρ e ≤ (b2 : ℝ) * (1 / (G.mStar : ℝ)) :=
        mul_le_mul_of_nonneg_left (hcap e) (Nat.cast_nonneg _)
      _ = (b2 : ℝ) / G.mStar := by ring
      _ ≤ 1 := (div_le_one hmR).2 hbR.le
  have hsum : ∑ e, ρ e = (b2 : ℝ) := by simp [ρ, ← mul_sum, hp.2]
  obtain ⟨τ2, hτ2, hτmarg⟩ := lemma_EC_4 G hbm ρ hρ hsum
  have hscale (σ : Act V b1 → ℝ) : G.U σ τ2 = (b2 : ℝ) * G.U σ τ1 := by
    apply nr20261028_U_eq_mul_of_marg_eq_mul
    intro e
    rw [hτmarg, hmarg]
  have hmiss (e : E) : G.nr20261028_missProb σ1 e ≤ G.U σ1 τ1 := by
    let t : Act E 1 := ⟨{e}, by simp⟩
    have ht : IsMixed (pureMixed t) := by
      constructor
      · intro X; simp only [pureMixed]; split_ifs <;> norm_num
      · simp [pureMixed]
    have hh := hne.2.2.1 (pureMixed t) ht
    change G.U σ1 (pureMixed t) ≤ G.U σ1 τ1 at hh
    simpa only [t, nr20261028_U_pure_singleton] using hh
  have hu : 0 ≤ G.U σ1 τ1 := by
    rw [nr20261028_U_eq_sum_marg]
    exact sum_nonneg fun e _ => mul_nonneg (nr20261028_marg_nonneg_of_mixed τ1 hne.1 e)
      (nr20261028_missProb_nonneg G σ1 hne.2.1 e)
  refine ⟨τ2, ⟨hτ2, hne.2.1, ?_, ?_⟩, hscale σ1, hmiss⟩
  · intro σ hσ
    change G.U σ1 σ ≤ G.U σ1 τ2
    rw [hscale σ1, nr20261028_U_eq_sum_marg]
    calc
      _ ≤ ∑ e, marg σ e * G.U σ1 τ1 := sum_le_sum fun e _ =>
        mul_le_mul_of_nonneg_left (hmiss e) (nr20261028_marg_nonneg_of_mixed σ hσ e)
      _ = (∑ e, marg σ e) * G.U σ1 τ1 := (sum_mul _ _ _).symm
      _ ≤ (b2 : ℝ) * G.U σ1 τ1 := mul_le_mul_of_nonneg_right (nr20261028_sum_marg_le_budget σ hσ) hu
  · intro σ hσ
    change G.U σ1 τ2 ≤ G.U σ τ2
    rw [hscale σ1, hscale σ]
    exact mul_le_mul_of_nonneg_left (hne.2.2.2 σ hσ) (Nat.cast_nonneg _)

end NetInspect.Rate




namespace NetInspect.Rate
open Finset DetectionModel BlottoLP.Flow
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

 theorem nr20261028_support_card_eq_of_sum_marg_eq {b : ℕ} (σ : Act E b → ℝ)
    (hσ : IsMixed σ) (hsum : ∑ e, marg σ e = (b : ℝ)) :
    ∀ T, 0 < σ T → T.1.card = b := by
  classical
  have hz : ∑ T : Act E b, σ T * ((b : ℝ) - T.1.card) = 0 := by
    simp_rw [mul_sub]
    rw [sum_sub_distrib, ← sum_mul, hσ.2, one_mul,
      ← nr20261028_sum_marg_eq_expected_card, hsum, sub_self]
  have hn T : 0 ≤ σ T * ((b : ℝ) - T.1.card) :=
    mul_nonneg (hσ.1 T) (sub_nonneg.mpr (by exact_mod_cast T.2))
  intro T hT
  have ht := (sum_eq_zero_iff_of_nonneg fun T _ => hn T).mp hz T (mem_univ _)
  have he := (mul_eq_zero.mp ht).resolve_left hT.ne'
  have hc : (T.1.card : ℝ) = b := by linarith
  exact_mod_cast hc

 theorem nr20261028_support_card_eq_of_payoff_eq (G : DetectionModel V E) {b1 b2 : ℕ}
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ) (h2 : IsMixed σ2)
    (v : ℝ) (hv : 0 < v) (hmiss : ∀ e, G.nr20261028_missProb σ1 e ≤ v)
    (hu : G.U σ1 σ2 = (b2 : ℝ) * v) :
    ∀ T, 0 < σ2 T → T.1.card = b2 := by
  have hm (e : E) : 0 ≤ marg σ2 e := by
    unfold marg
    apply sum_nonneg
    intro T _
    split_ifs <;> simp [h2.1 T]
  have hupper : G.U σ1 σ2 ≤ (∑ e, marg σ2 e) * v := by
    rw [nr20261028_U_eq_sum_marg, sum_mul]
    exact sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hmiss e) (hm e)
  have hmass : ∑ e, marg σ2 e = (b2 : ℝ) := by
    have hle := nr20261028_sum_marg_le_budget σ2 h2
    rw [hu] at hupper
    nlinarith
  exact nr20261028_support_card_eq_of_sum_marg_eq σ2 h2 hmass

 theorem nr20261028_ratio_eq_one_sub_undet_div (G : DetectionModel V E) (S : Finset V) (T : Finset E)
    {b : ℕ} (hb : 0 < b) (hT : T.card = b) :
    G.ratio S T = 1 - G.undet S T / (b : ℝ) := by
  have ht : T ≠ ∅ := by intro h; simp [h] at hT; omega
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  unfold ratio undet
  rw [if_neg ht, hT]
  field_simp
  ring

 theorem nr20261028_rate_eq_one_sub_U_div (G : DetectionModel V E) {b1 b2 : ℕ}
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ)
    (h1 : IsMixed σ1) (h2 : IsMixed σ2) (hb : 0 < b2)
    (hsupport : ∀ T, 0 < σ2 T → T.1.card = b2) :
    G.rate σ1 σ2 = 1 - G.U σ1 σ2 / (b2 : ℝ) := by
  have ht (T : Act E b2) (S : Act V b1) :
      σ2 T * σ1 S * G.ratio S.1 T.1 =
        σ2 T * σ1 S - σ2 T * σ1 S * G.undet S.1 T.1 / (b2 : ℝ) := by
    by_cases hz : σ2 T = 0
    · simp [hz]
    · have hpos : 0 < σ2 T := lt_of_le_of_ne (h2.1 T) (Ne.symm hz)
      rw [nr20261028_ratio_eq_one_sub_undet_div G S.1 T.1 hb (hsupport T hpos)]
      ring
  unfold rate U expPay payoff
  simp_rw [ht, sum_sub_distrib, ← sum_div]
  simp_rw [← mul_sum, h1.2, mul_one, h2.2]

 theorem nr20261028_rate_eq_one_sub_value (G : DetectionModel V E) {b1 b2 : ℕ}
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ)
    (h1 : IsMixed σ1) (h2 : IsMixed σ2) (hb : 0 < b2)
    (v : ℝ) (hv : 0 < v) (hmiss : ∀ e, G.nr20261028_missProb σ1 e ≤ v)
    (hu : G.U σ1 σ2 = (b2 : ℝ) * v) : G.rate σ1 σ2 = 1 - v := by
  rw [nr20261028_rate_eq_one_sub_U_div G σ1 σ2 h1 h2 hb
    (nr20261028_support_card_eq_of_payoff_eq G σ1 σ2 h2 v hv hmiss hu), hu]
  have hbR : (b2 : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [mul_div_cancel_left₀ v hbR]

 theorem nr20261028_equilibrium_U_pos_of_lt_nStar (G : DetectionModel V E) {b1 : ℕ}
    (hb : b1 < G.nStar) (σ1 : Act V b1 → ℝ) (σ2 : Act E 1 → ℝ)
    (hne : G.IsNE b1 1 σ1 σ2) : 0 < G.U σ1 σ2 := by
  classical
  have hn := nr20261028_U_nonneg G hne.2.1 hne.1
  by_contra hpos
  have hu : G.U σ1 σ2 = 0 := le_antisymm (le_of_not_gt hpos) hn
  have hmiss (e : E) : G.nr20261028_missProb σ1 e = 0 := by
    let t : Act E 1 := ⟨{e}, by simp⟩
    have ht : IsMixed (pureMixed t) := by
      constructor
      · intro a; simp only [pureMixed]; split_ifs <;> norm_num
      · simp [pureMixed]
    have h := hne.2.2.1 (pureMixed t) ht
    change G.U σ1 (pureMixed t) ≤ G.U σ1 σ2 at h
    rw [hu] at h
    have he : G.U σ1 (pureMixed t) = G.nr20261028_missProb σ1 e := nr20261028_U_pure_singleton G σ1 e
    rw [he] at h
    exact le_antisymm h (nr20261028_missProb_nonneg G σ1 hne.2.1 e)
  have hex : ∃ S, 0 < σ1 S := by
    by_contra hh
    have hh' (S : Act V b1) : σ1 S ≤ 0 := le_of_not_gt (fun h => hh ⟨S, h⟩)
    have hs := sum_nonpos fun S (_ : S ∈ (univ : Finset (Act V b1))) => hh' S
    rw [hne.2.1.2] at hs
    norm_num at hs
  obtain ⟨S, hS⟩ := hex
  have hcover : G.IsSetCover S.1 := by
    intro e
    have hzero := hmiss e
    unfold DetectionModel.nr20261028_missProb at hzero
    have hnon (T : Act V b1) :
        0 ≤ σ1 T * (if e ∈ G.CS T.1 then (0 : ℝ) else 1) := by
      exact mul_nonneg (hne.2.1.1 T) (by split_ifs <;> norm_num)
    have ht := (sum_eq_zero_iff_of_nonneg fun T _ => hnon T).mp hzero S (mem_univ _)
    have he : e ∈ G.CS S.1 := by
      by_contra hh
      simp [hh] at ht
      exact hS.ne' ht
    simp [F, he]
  have hns : G.nStar ≤ S.1.card := Nat.sInf_le ⟨S.1, rfl, hcover⟩
  omega

 theorem nr20261028_equilibrium_rate_eq_of_reference (G : DetectionModel V E) {b1 b2 : ℕ}
    (σref : Act V b1 → ℝ) (τref : Act E b2 → ℝ)
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ)
    (href : G.IsNE b1 b2 σref τref) (hne : G.IsNE b1 b2 σ1 σ2)
    (hb : 0 < b2) (v : ℝ) (hv : 0 < v)
    (hmiss : ∀ e, G.nr20261028_missProb σref e ≤ v)
    (huref : G.U σref τref = (b2 : ℝ) * v) : G.rate σ1 σ2 = 1 - v := by
  have hcross : G.IsNE b1 b2 σref σ2 := hne.nr20261028_cross href
  have hucross : G.U σref σ2 = (b2 : ℝ) * v := (hcross.nr20261028_expPay_eq href).trans huref
  have hu : G.U σ1 σ2 = (b2 : ℝ) * v := (hne.nr20261028_expPay_eq href).trans huref
  have hsupport := nr20261028_support_card_eq_of_payoff_eq G σref σ2 hne.1 v hv hmiss hucross
  rw [nr20261028_rate_eq_one_sub_U_div G σ1 σ2 hne.2.1 hne.1 hb hsupport, hu]
  have hbR : (b2 : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [mul_div_cancel_left₀ v hbR]

end NetInspect.Rate





namespace NetInspect.Rate
open Finset DetectionModel BlottoLP.Flow
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem nr20261028_gameValue_eq_U_of_NE (G : DetectionModel V E) {b1 b2 : ℕ}
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ) (hne : G.IsNE b1 b2 σ1 σ2) :
    G.gameValue b1 b2 = G.U σ1 σ2 := by
  classical
  letI : Nonempty (Act E b2) := ⟨⟨∅, by simp⟩⟩
  change IsNashEq (G.payoff b1 b2) σ2 σ1 at hne
  have hpure (T : Act E b2) : IsMixed (pureMixed T) := by
    refine ⟨fun X => ?_, ?_⟩
    · unfold pureMixed; split_ifs <;> norm_num
    · simp [pureMixed]
  have hupper (τ1 : Act V b1 → ℝ) : G.U τ1 σ2 ≤ G.worst1 b2 τ1 := by
    apply nr20261028_expPay_le_of_pure_left (G.payoff b1 b2) hne.1 τ1
    intro T
    exact le_csSup (Set.finite_range (fun X : Act E b2 => G.U τ1 (pureMixed X))).bddAbove
      (Set.mem_range_self T)
  have hvalue : G.worst1 b2 σ1 = G.U σ1 σ2 := by
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty _)
      rintro x ⟨T, rfl⟩
      exact hne.2.2.1 _ (hpure T)
    · exact hupper σ1
  have hlower (τ1 : Act V b1 → ℝ) (hτ1 : IsMixed τ1) :
      G.U σ1 σ2 ≤ G.worst1 b2 τ1 :=
    (hne.2.2.2 τ1 hτ1).trans (hupper τ1)
  have hneSet : ((G.worst1 b2) '' {τ1 : Act V b1 → ℝ | IsMixed τ1}).Nonempty :=
    ⟨G.worst1 b2 σ1, σ1, hne.2.1, rfl⟩
  have hbounded : BddBelow ((G.worst1 b2) '' {τ1 : Act V b1 → ℝ | IsMixed τ1}) := by
    refine ⟨G.U σ1 σ2, ?_⟩
    rintro x ⟨τ1, hτ1, rfl⟩
    exact hlower τ1 hτ1
  apply le_antisymm
  · exact (csInf_le hbounded ⟨σ1, hne.2.1, rfl⟩).trans hvalue.le
  · apply le_csInf hneSet
    rintro x ⟨τ1, hτ1, rfl⟩
    exact hlower τ1 hτ1

end NetInspect.Rate



namespace NetInspect.Rate
open Finset DetectionModel BlottoLP.Flow
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem nr20261028_capped_equilibrium_for_defender [Nonempty E] (G : DetectionModel V E)
    {b : ℕ} (hb : b < G.nStar) (hm : 1 < G.mStar)
    (σ1 : Act V b → ℝ) (σ2 : Act E 1 → ℝ) (hne : G.IsNE b 1 σ1 σ2) :
    ∃ (p : E → ℝ) (τ1 : Act E 1 → ℝ), IsMixed p ∧
      (∀ e, p e ≤ 1 / (G.mStar : ℝ)) ∧ G.IsNE b 1 σ1 τ1 ∧
      ∀ e, marg τ1 e = p e := by
  classical
  have hncard : G.nStar ≤ Fintype.card V := by
    apply Nat.sInf_le
    refine ⟨univ, by simp, ?_⟩
    intro e
    obtain ⟨i, hi⟩ := G.coverable e
    have he : e ∈ G.CS univ := mem_biUnion.mpr ⟨i, mem_univ _, hi⟩
    simp [F, he]
  have hbcard := hb.le.trans hncard
  obtain ⟨p0, v, hp0, hv, hupper0, hopt⟩ := nr20261028_exists_coverage_minimax G b
  obtain ⟨σex, hσopt, hσcap⟩ := theorem_2_step_ia G hb hm
  let p := nr20261028_singletonExWeights σex
  have hp : IsMixed p := nr20261028_singletonExWeights_mixed σex hσopt.1
  have hcap : ∀ e, p e ≤ 1 / (G.mStar : ℝ) := by
    intro e
    simpa only [p, nr20261028_singletonExWeights_marg] using hσcap e
  have hupper : ∀ S : Finset V, S.card ≤ b → ∑ e ∈ G.CS S, p e ≤ v :=
    nr20261028_optimal_singleton_coverage_upper G b hbcard σex hσopt p0 hp0 v hupper0
  obtain ⟨τ1, hτ, hτmarg, hval⟩ := nr20261028_single_equilibrium_of_capped_coverage
    G b hm p hp hcap v hupper hopt σ1 σ2 hne
  exact ⟨p, τ1, hp, hcap, hτ, hτmarg⟩

theorem nr20261028_theorem_2_intermediate (G : DetectionModel V E) {b : ℕ}
    (hb : b < G.nStar) (hm : 1 < G.mStar) : nr20261028_DetectionRateConclusion G b := by
  classical
  have hcardE : 0 < Fintype.card E := lt_of_lt_of_le (by omega) (nr20261028_mStar_le_card G)
  letI : Nonempty E := Fintype.card_pos_iff.mp hcardE
  letI : Nonempty (Act V b) := ⟨⟨∅, by simp⟩⟩
  letI : Nonempty (Act E 1) := ⟨⟨∅, by simp⟩⟩
  obtain ⟨σ2, σ1, hbase⟩ := nr20261028_exists_isNashEq (G.payoff b 1)
  change G.IsNE b 1 σ1 σ2 at hbase
  obtain ⟨p, τ1, hp, hcap, href, hmarg⟩ := nr20261028_capped_equilibrium_for_defender G hb hm σ1 σ2 hbase
  let u := G.U σ1 τ1
  have hu : 0 < u := nr20261028_equilibrium_U_pos_of_lt_nStar G hb σ1 τ1 href
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [nr20261028_U_eq_sum_marg]
    simp_rw [hmarg]
    calc
      _ ≤ ∑ e, p e := sum_le_sum fun e _ => by
        simpa using mul_le_mul_of_nonneg_left (nr20261028_missProb_le_one G σ1 href.2.1 e) (hp.1 e)
      _ = 1 := hp.2
  refine ⟨⟨1-u, by linarith, by linarith, ?_⟩, ?_⟩
  · intro b2 hb2 hbm ρ1 ρ2 hne
    obtain ⟨τ2, hscaled, hval, hmiss⟩ := nr20261028_scale_capped_equilibrium G σ1 τ1 href p hp hmarg hcap hb2 hbm
    exact nr20261028_equilibrium_rate_eq_of_reference G σ1 τ2 ρ1 ρ2 hscaled hne
      (by omega) u hu hmiss hval
  · intro ρ1 ρ2 hne b2 hb2 hbm
    obtain ⟨p', τ', hp', hcap', href', hmarg'⟩ := nr20261028_capped_equilibrium_for_defender G hb hm ρ1 ρ2 hne
    obtain ⟨τ2, hscaled, _, _⟩ := nr20261028_scale_capped_equilibrium G ρ1 τ' href' p' hp' hmarg' hcap' hb2 hbm
    exact ⟨τ2, hscaled⟩

theorem nr20261028_eq_18 (G : DetectionModel V E)
    {b1 b2 : ℕ} (hb1 : b1 < G.nStar) (hb2 : 1 ≤ b2) (hb2m : b2 < G.mStar) :
    G.gameValue b1 b2 = (b2 : ℝ) * G.gameValue b1 1 := by
  classical
  have hm : 1 < G.mStar := hb2.trans_lt hb2m
  have hcardE : 0 < Fintype.card E := lt_of_lt_of_le (by omega) (nr20261028_mStar_le_card G)
  letI : Nonempty E := Fintype.card_pos_iff.mp hcardE
  letI : Nonempty (Act V b1) := ⟨⟨∅, by simp⟩⟩
  letI : Nonempty (Act E 1) := ⟨⟨∅, by simp⟩⟩
  obtain ⟨σ2, σ1, hbase⟩ := nr20261028_exists_isNashEq (G.payoff b1 1)
  change G.IsNE b1 1 σ1 σ2 at hbase
  obtain ⟨p, τ1, hp, hcap, href, hmarg⟩ := nr20261028_capped_equilibrium_for_defender G hb1 hm σ1 σ2 hbase
  obtain ⟨τ2, hscaled, hval, _⟩ := nr20261028_scale_capped_equilibrium G σ1 τ1 href p hp hmarg hcap hb2 hb2m
  rw [nr20261028_gameValue_eq_U_of_NE G σ1 τ2 hscaled, nr20261028_gameValue_eq_U_of_NE G σ1 τ1 href]
  exact hval

theorem nr20261028_theorem_2 (G : DetectionModel V E) (b1 : ℕ) :
    (∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧
      ∀ b2 : ℕ, 1 ≤ b2 → b2 < G.mStar →
        ∀ (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ), G.IsNE b1 b2 σ1 σ2 → G.rate σ1 σ2 = r) ∧
    (∀ (σ1 : Act V b1 → ℝ) (σ2 : Act E 1 → ℝ), G.IsNE b1 1 σ1 σ2 →
      ∀ b2 : ℕ, 1 ≤ b2 → b2 < G.mStar →
        ∃ σ2' : Act E b2 → ℝ, G.IsNE b1 b2 σ1 σ2') := by
  change nr20261028_DetectionRateConclusion G b1
  by_cases hm : G.mStar ≤ 1
  · exact nr20261028_theorem_2_vacuous G b1 hm
  by_cases hz : b1 = 0
  · subst b1
    exact nr20261028_theorem_2_zero G
  by_cases hc : G.nStar ≤ b1
  · exact nr20261028_theorem_2_cover G hc
  exact nr20261028_theorem_2_intermediate G (by omega) (by omega)

end NetInspect.Rate


open NetInspect.Rate NetInspect.Rate.DetectionModel Finset

theorem solution {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DetectionModel V E) (b1 : ℕ) :
    (∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧
      ∀ b2 : ℕ, 1 ≤ b2 → b2 < G.mStar →
        ∀ (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ), G.IsNE b1 b2 σ1 σ2 → G.rate σ1 σ2 = r) ∧
    (∀ (σ1 : Act V b1 → ℝ) (σ2 : Act E 1 → ℝ), G.IsNE b1 1 σ1 σ2 →
      ∀ b2 : ℕ, 1 ≤ b2 → b2 < G.mStar →
        ∃ σ2' : Act E b2 → ℝ, G.IsNE b1 b2 σ1 σ2') := by
  exact NetInspect.Rate.nr20261028_theorem_2 G b1

#print axioms solution
