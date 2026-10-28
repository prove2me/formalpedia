-- Prove2me | solution 1 for NetInspect.Rate.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-28T06:19:49.605387+00:00
-- url     : https://prove2.me/submissions/c4a807d7-5e3f-470e-aefc-e11a59c73497

import Definitions.Def_NetInspect_Rate_Model
import Definitions.Def_BlottoLP_Flow_ZeroSum
import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Ring.Finset
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp


namespace BlottoLP.Flow
open Finset
variable {α β : Type*} [Fintype α] [Fintype β]

lemma expPay_affine_left (M : α → β → ℝ) (σ σ' : α → ℝ) (τ : β → ℝ) (a b : ℝ) :
    expPay M (a • σ + b • σ') τ = a * expPay M σ τ + b * expPay M σ' τ := by
  simp only [expPay, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

lemma expPay_affine_right (M : α → β → ℝ) (σ : α → ℝ) (τ τ' : β → ℝ) (a b : ℝ) :
    expPay M σ (a • τ + b • τ') = a * expPay M σ τ + b * expPay M σ τ' := by
  simp only [expPay, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

/-- Every finite nonempty real zero-sum game has a mixed Nash equilibrium. -/
theorem exists_isNashEq [Nonempty α] [Nonempty β] (M : α → β → ℝ) :
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
    exact (expPay_affine_right M σ x y a b).le
  have hconc (τ : β → ℝ) : ConcaveOn ℝ (stdSimplex ℝ α) (fun σ => expPay M σ τ) := by
    refine ⟨convex_stdSimplex _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    exact (expPay_affine_left M x y τ a b).ge
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

 theorem IsNashEq.expPay_eq {M : α → β → ℝ} {σ σ' : α → ℝ} {τ τ' : β → ℝ}
    (h : IsNashEq M σ τ) (h' : IsNashEq M σ' τ') :
    expPay M σ τ = expPay M σ' τ' := by
  apply le_antisymm
  · exact (h.2.2.2 τ' h'.2.1).trans (h'.2.2.1 σ h.1)
  · exact (h'.2.2.2 τ h.2.1).trans (h.2.2.1 σ' h'.1)

 theorem IsNashEq.cross {M : α → β → ℝ} {σ σ' : α → ℝ} {τ τ' : β → ℝ}
    (h : IsNashEq M σ τ) (h' : IsNashEq M σ' τ') : IsNashEq M σ τ' := by
  have hv := h.expPay_eq h'
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

lemma expPay_eq_sum_pure_left [DecidableEq α] (M : α → β → ℝ) (σ : α → ℝ) (τ : β → ℝ) :
    expPay M σ τ = ∑ a, σ a * expPay M (pureMixed a) τ := by
  simp only [expPay, pureMixed]
  simp [Finset.mul_sum, mul_assoc]

lemma expPay_eq_sum_pure_right [DecidableEq β] (M : α → β → ℝ) (σ : α → ℝ) (τ : β → ℝ) :
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

lemma expPay_le_of_pure_left [DecidableEq α] (M : α → β → ℝ) {σ : α → ℝ}
    (hσ : IsMixed σ) (τ : β → ℝ) (v : ℝ)
    (h : ∀ a, expPay M (pureMixed a) τ ≤ v) : expPay M σ τ ≤ v := by
  rw [expPay_eq_sum_pure_left]
  calc
    _ ≤ ∑ a, σ a * v := Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (hσ.1 a)
    _ = v := by rw [← Finset.sum_mul, hσ.2, one_mul]

lemma le_expPay_of_pure_right [DecidableEq β] (M : α → β → ℝ) (σ : α → ℝ)
    {τ : β → ℝ} (hτ : IsMixed τ) (v : ℝ)
    (h : ∀ b, v ≤ expPay M σ (pureMixed b)) : v ≤ expPay M σ τ := by
  rw [expPay_eq_sum_pure_right]
  calc
    v = ∑ b, τ b * v := by rw [← Finset.sum_mul, hτ.2, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (h b) (hτ.1 b)

end BlottoLP.Flow




namespace NetInspect.Rate
open Finset DetectionModel
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem packing_sizes_nonempty (G : DetectionModel V E) :
    {k : ℕ | ∃ T : Finset E, T.card = k ∧ G.IsSetPacking T}.Nonempty := by
  refine ⟨0, ∅, rfl, ?_⟩
  intro i
  simp [F]

theorem packing_sizes_bddAbove (G : DetectionModel V E) :
    BddAbove {k : ℕ | ∃ T : Finset E, T.card = k ∧ G.IsSetPacking T} := by
  refine ⟨Fintype.card E, ?_⟩
  rintro k ⟨T, rfl, _⟩
  exact card_le_univ T

theorem exists_max_packing (G : DetectionModel V E) :
    ∃ T : Finset E, T.card = G.mStar ∧ G.IsSetPacking T :=
  Nat.sSup_mem (packing_sizes_nonempty G) (packing_sizes_bddAbove G)

theorem mStar_le_card_packing (G : DetectionModel V E) : G.mStar ≤ Fintype.card E := by
  obtain ⟨T, ht, _⟩ := exists_max_packing G
  rw [← ht]
  exact card_le_univ T

theorem one_le_mStar_of_nonempty (G : DetectionModel V E) [Nonempty E] : 1 ≤ G.mStar := by
  classical
  obtain ⟨e⟩ := ‹Nonempty E›
  apply le_csSup (packing_sizes_bddAbove G)
  refine ⟨{e}, by simp, ?_⟩
  intro i
  unfold F
  exact (card_le_card inter_subset_right).trans (by simp)

theorem F_le_card_of_packing (G : DetectionModel V E) (S : Finset V) (T : Finset E)
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

 def coverage (G : DetectionModel V E) (p : E → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ G.CS S, p e

 theorem coverage_minimax [Nonempty E] (G : DetectionModel V E) (b : ℕ) :
    ∃ (p : E → ℝ) (v : ℝ), IsMixed p ∧
      (∀ S : Finset V, S.card ≤ b → coverage G p S ≤ v) ∧
      (∀ q : E → ℝ, IsMixed q → ∃ S : Finset V, S.card ≤ b ∧ v ≤ coverage G q S) := by
  classical
  letI : Nonempty (Act V b) := ⟨⟨∅, by simp⟩⟩
  let M : Act V b → E → ℝ := fun S e => if e ∈ G.CS S.1 then 1 else 0
  have hpure (S : Act V b) (p : E → ℝ) : expPay M (pureMixed S) p = coverage G p S.1 := by
    simp [expPay, pureMixed, M, coverage, mul_ite, sum_ite]
  obtain ⟨σ, p, hne⟩ := exists_isNashEq M
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
      (fun S => coverage G q S.1) (by simp)
    refine ⟨S.1, S.2, ?_⟩
    calc
      v ≤ expPay M σ q := hne.2.2.2 q hq
      _ ≤ coverage G q S.1 := expPay_le_of_pure_left M hne.1 q _ (by
        intro T
        rw [hpure]
        exact hmax T (mem_univ _))

 theorem uniform_packing_coverage [Nonempty E] (G : DetectionModel V E) (b : ℕ) :
    ∃ q : E → ℝ, IsMixed q ∧ (∀ e, q e ≤ 1 / (G.mStar : ℝ)) ∧
      ∀ S : Finset V, S.card ≤ b → coverage G q S ≤ (b : ℝ) / G.mStar := by
  classical
  obtain ⟨T, hTc, hT⟩ := exists_max_packing G
  have hmN : 0 < G.mStar := lt_of_lt_of_le Nat.zero_lt_one (one_le_mStar_of_nonempty G)
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
    have heq : coverage G q S = (G.F S T : ℝ) / G.mStar := by
      simp [coverage, q, sum_ite, filter_mem_eq_inter, F, div_eq_mul_inv]
    rw [heq]
    apply div_le_div_of_nonneg_right _ hm.le
    exact_mod_cast (F_le_card_of_packing G S T hT).trans hS

 theorem exists_coverage_minimax [Nonempty E] (G : DetectionModel V E) (b : ℕ) :
    ∃ (p : E → ℝ) (v : ℝ), IsMixed p ∧ v ≤ (b : ℝ) / G.mStar ∧
      (∀ S : Finset V, S.card ≤ b → ∑ e ∈ G.CS S, p e ≤ v) ∧
      (∀ q : E → ℝ, IsMixed q → ∃ S : Finset V, S.card ≤ b ∧ v ≤ ∑ e ∈ G.CS S, q e) := by
  obtain ⟨p, v, hp, hupper, hlower⟩ := coverage_minimax G b
  obtain ⟨q, hq, hcap, hbound⟩ := uniform_packing_coverage G b
  obtain ⟨S, hS, hv⟩ := hlower q hq
  exact ⟨p, v, hp, hv.trans (hbound S hS), hupper, hlower⟩

end NetInspect.Rate





namespace NetInspect.Rate
open Finset DetectionModel

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem undet_eq_sum (G : DetectionModel V E) (S : Finset V) (T : Finset E) :
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
def missProb {b1 : ℕ} (G : DetectionModel V E) (σ1 : Act V b1 → ℝ) (e : E) : ℝ :=
  ∑ S, σ1 S * (if e ∈ G.CS S.1 then 0 else 1)
end DetectionModel

theorem U_eq_sum_marg {b1 b2 : ℕ} (G : DetectionModel V E)
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ) :
    G.U σ1 σ2 = ∑ e, marg σ2 e * G.missProb σ1 e := by
  classical
  have hu (S : Finset V) (T : Finset E) : G.undet S T =
      ∑ e, if e ∈ T then (if e ∈ G.CS S then (0 : ℝ) else 1) else 0 := by
    rw [undet_eq_sum]
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
      unfold marg missProb
      simp_rw [sum_mul, mul_sum]
      apply sum_congr rfl
      intro e _
      apply sum_congr rfl
      intro T _
      apply sum_congr rfl
      intro S _
      by_cases he : e ∈ T.1 <;> simp [he, mul_assoc]

theorem U_eq_of_marg_eq {b1 b2 b2' : ℕ} (G : DetectionModel V E)
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ) (τ2 : Act E b2' → ℝ)
    (h : ∀ e, marg σ2 e = marg τ2 e) : G.U σ1 σ2 = G.U σ1 τ2 := by
  simp only [U_eq_sum_marg, h]

theorem U_eq_mul_of_marg_eq_mul {b1 b2 b2' : ℕ} (G : DetectionModel V E)
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ) (τ2 : Act E b2' → ℝ) (c : ℝ)
    (h : ∀ e, marg σ2 e = c * marg τ2 e) : G.U σ1 σ2 = c * G.U σ1 τ2 := by
  simp only [U_eq_sum_marg, h, mul_sum, mul_assoc]

theorem missProb_nonneg {b1 : ℕ} (G : DetectionModel V E)
    (σ1 : Act V b1 → ℝ) (hσ : BlottoLP.Flow.IsMixed σ1) (e : E) :
    0 ≤ G.missProb σ1 e := by
  unfold DetectionModel.missProb
  apply sum_nonneg
  intro S _
  exact mul_nonneg (hσ.1 S) (by split_ifs <;> norm_num)

theorem missProb_le_one {b1 : ℕ} (G : DetectionModel V E)
    (σ1 : Act V b1 → ℝ) (hσ : BlottoLP.Flow.IsMixed σ1) (e : E) :
    G.missProb σ1 e ≤ 1 := by
  unfold DetectionModel.missProb
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

noncomputable def singletonExEquiv (E : Type*) [Fintype E] [DecidableEq E] : E ≃ ActEx E 1 :=
  Equiv.ofBijective (fun e => (⟨{e}, by simp⟩ : ActEx E 1)) (by
    constructor
    · intro e f h
      have hh := congrArg Subtype.val h
      simpa using hh
    · intro T
      obtain ⟨e, he⟩ := card_eq_one.mp T.2
      exact ⟨e, Subtype.ext he.symm⟩)

@[simp] theorem singletonExEquiv_apply (e : E) :
    (singletonExEquiv E e).1 = {e} := rfl

noncomputable def singletonExStrat (p : E → ℝ) : ActEx E 1 → ℝ :=
  fun T => p ((singletonExEquiv E).symm T)

@[simp] theorem singletonExStrat_apply (p : E → ℝ) (e : E) :
    singletonExStrat p (singletonExEquiv E e) = p e := by simp [singletonExStrat]

theorem singletonExStrat_mixed (p : E → ℝ) (hp : IsMixed p) : IsMixed (singletonExStrat p) := by
  refine ⟨fun T => hp.1 _, ?_⟩
  rw [← (singletonExEquiv E).sum_comp]
  simpa using hp.2

theorem singletonExStrat_marg (p : E → ℝ) (e : E) : marg (singletonExStrat p) e = p e := by
  classical
  unfold marg
  rw [← (singletonExEquiv E).sum_comp]
  simp

theorem payoffEx_singleton (G : DetectionModel V E) {b1 : ℕ} (p : E → ℝ)
    (hp : IsMixed p) (S : ActEx V b1) :
    expPay (G.payoffEx b1 1) (singletonExStrat p) (pureMixed S) =
      1 - ∑ e ∈ G.CS S.1, p e := by
  classical
  simp only [expPay, pureMixed, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    sum_ite_eq', sum_ite_eq, mem_univ, ↓reduceIte]
  rw [← (singletonExEquiv E).sum_comp]
  simp only [singletonExStrat_apply, payoffEx, singletonExEquiv_apply]
  simp_rw [undet_eq_sum]
  simp only [sum_singleton]
  have he (e : E) : p e * (if e ∈ G.CS S.1 then (0 : ℝ) else 1) =
      p e - if e ∈ G.CS S.1 then p e else 0 := by split_ifs <;> simp
  simp_rw [he]
  rw [sum_sub_distrib, hp.2]
  simp

theorem singletonExStrat_optLP2bar (G : DetectionModel V E) (b : ℕ)
    (hb : b ≤ Fintype.card V) (p : E → ℝ) (hp : IsMixed p) (v : ℝ)
    (hupper : ∀ S : Finset V, S.card ≤ b → ∑ e ∈ G.CS S, p e ≤ v)
    (hopt : ∀ q : E → ℝ, IsMixed q →
      ∃ S : Finset V, S.card ≤ b ∧ v ≤ ∑ e ∈ G.CS S, q e) :
    G.IsOptLP2bar b 1 (singletonExStrat p) := by
  classical
  obtain ⟨B, _, hB⟩ := exists_subset_card_eq (s := (univ : Finset V)) (by simpa using hb)
  letI : Nonempty (ActEx V b) := ⟨⟨B, hB⟩⟩
  refine ⟨singletonExStrat_mixed p hp, ?_⟩
  intro τ hτ
  let q : E → ℝ := fun e => τ (singletonExEquiv E e)
  have hq : IsMixed q := by
    refine ⟨fun e => hτ.1 _, ?_⟩
    simpa [q] using ((singletonExEquiv E).sum_comp τ).trans hτ.2
  have hτq : τ = singletonExStrat q := by
    funext T
    simp [singletonExStrat, q]
  obtain ⟨S, hS, hvS⟩ := hopt q hq
  obtain ⟨S', hSS', _, hS'⟩ := exists_subsuperset_card_eq (subset_univ S) hS
    (by simpa using hb)
  have hCS : G.CS S ⊆ G.CS S' := by
    intro e he
    obtain ⟨i, hi, hie⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨i, hSS' hi, hie⟩
  have hvS' : v ≤ ∑ e ∈ G.CS S', q e := hvS.trans
    (sum_le_sum_of_subset_of_nonneg hCS (fun e _ _ => hq.1 e))
  have hlow : 1 - v ≤ G.best2Ex b (singletonExStrat p) := by
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨X, rfl⟩
    change 1 - v ≤ expPay (G.payoffEx b 1) (singletonExStrat p) (pureMixed X)
    rw [payoffEx_singleton G p hp X]
    linarith [hupper X.1 X.2.le]
  have hup : G.best2Ex b τ ≤ 1 - v := by
    change sInf (Set.range (fun X : ActEx V b => expPay (G.payoffEx b 1) τ (pureMixed X))) ≤ 1 - v
    calc
      _ ≤ expPay (G.payoffEx b 1) τ (pureMixed (⟨S', hS'⟩ : ActEx V b)) :=
        csInf_le (Set.finite_range (fun X : ActEx V b =>
          expPay (G.payoffEx b 1) τ (pureMixed X))).bddBelow
          (Set.mem_range_self (⟨S', hS'⟩ : ActEx V b))
      _ = 1 - ∑ e ∈ G.CS S', q e := by rw [hτq, payoffEx_singleton G q hq]
      _ ≤ 1 - v := by linarith
  exact hup.trans hlow

end NetInspect.Rate




namespace NetInspect.Rate
open Finset DetectionModel


/-- Cap one overweight coordinate by redistributing only into available global capacity. -/
theorem redistribute_coordinate {E : Type*} [Fintype E] [DecidableEq E]
    (p : E → ℝ) (hp : BlottoLP.Flow.IsMixed p) (c : ℝ) (hc : 0 ≤ c)
    (hcapacity : 1 ≤ (Fintype.card E : ℝ) * c) (e : E) (he : c < p e) :
    ∃ q : E → ℝ, BlottoLP.Flow.IsMixed q ∧ q e = c ∧
      (∀ f, p f ≤ c → q f ≤ c) ∧
      (∀ A : Finset E, ∑ f ∈ A, q f ≤
        (∑ f ∈ A, p f) + (p e - c) - if e ∈ A then p e - c else 0) := by
  classical
  let ε := p e - c
  let d : E → ℝ := fun f => max (c - p f) 0
  let D : ℝ := ∑ f, d f
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hd (f) : 0 ≤ d f := le_max_right _ _
  have hde : d e = 0 := max_eq_right (by linarith)
  have hD : ε ≤ D := by
    have hpoint (f : E) : c - p f ≤ d f - if f = e then ε else 0 := by
      by_cases h : f = e
      · subst f; simp only [hde, ↓reduceIte]; dsimp [ε]; linarith
      · rw [if_neg h, sub_zero]
        exact le_max_left _ _
    have hh := sum_le_sum (s := (univ : Finset E)) (fun f _ => hpoint f)
    have hs : (∑ f, (c - p f)) = (Fintype.card E : ℝ) * c - 1 := by
      rw [sum_sub_distrib, hp.2]; simp [nsmul_eq_mul]
    rw [hs, sum_sub_distrib] at hh
    have hs' : (∑ f : E, if f = e then ε else 0) = ε := by simp
    rw [hs'] at hh
    change (Fintype.card E : ℝ) * c - 1 ≤ D - ε at hh
    linarith
  have hDpos : 0 < D := hε.trans_le hD
  let k : ℝ := ε / D
  have hk0 : 0 ≤ k := div_nonneg hε.le hDpos.le
  have hk1 : k ≤ 1 := (div_le_one hDpos).mpr hD
  have hkD : k * D = ε := by dsimp [k]; field_simp
  let q : E → ℝ := fun f => p f + k * d f - if f = e then ε else 0
  have hqe : q e = c := by simp [q, hde, ε]
  have hqnorm : ∑ f, q f = 1 := by
    simp only [q, sum_sub_distrib, sum_add_distrib, ← mul_sum]
    rw [hp.2]
    change 1 + k * D - (∑ f : E, if f = e then ε else 0) = 1
    simp [hkD]
  have hqnon (f) : 0 ≤ q f := by
    by_cases h : f = e
    · subst f; rw [hqe]; exact hc
    · dsimp [q]; simp only [h, ↓reduceIte, sub_zero]
      exact add_nonneg (hp.1 f) (mul_nonneg hk0 (hd f))
  refine ⟨q, ⟨hqnon, hqnorm⟩, hqe, ?_, ?_⟩
  · intro f hfc
    have hdf : d f = c - p f := max_eq_left (by linarith)
    have hh := mul_le_mul_of_nonneg_right hk1 (hd f)
    dsimp [q]
    rw [hdf] at hh ⊢
    split_ifs <;> dsimp [ε] at * <;> linarith
  · intro A
    have hsub : ∑ f ∈ A, d f ≤ D := by
      exact sum_le_univ_sum_of_nonneg hd
    have hh := mul_le_mul_of_nonneg_left hsub hk0
    have hi : (∑ f ∈ A, if f = e then ε else 0) = if e ∈ A then ε else 0 := by simp
    dsimp [q]
    simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum]
    rw [hi]
    change (∑ f ∈ A, p f) + k * (∑ f ∈ A, d f) -
      (if e ∈ A then ε else 0) ≤ (∑ f ∈ A, p f) + ε - (if e ∈ A then ε else 0)
    linarith

section Coverage
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem coverage_mono (G : DetectionModel V E) (p : E → ℝ) (hp : ∀ e, 0 ≤ p e)
    {S T : Finset V} (h : S ⊆ T) : coverage G p S ≤ coverage G p T := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro e he
    obtain ⟨i, hi, hie⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨i, h hi, hie⟩
  · intro e _ _; exact hp e

theorem coverage_insert_component (G : DetectionModel V E) (p : E → ℝ)
    (hp : ∀ e, 0 ≤ p e) (S : Finset V) (e : E) (he : e ∉ G.CS S)
    (j : V) (hj : e ∈ G.C j) :
    coverage G p S + p e ≤ coverage G p (insert j S) := by
  have hsub : insert e (G.CS S) ⊆ G.CS (insert j S) := by
    intro f hf
    rcases mem_insert.mp hf with rfl | hf
    · exact mem_biUnion.mpr ⟨j, mem_insert_self _ _, hj⟩
    · obtain ⟨i, hi, hif⟩ := mem_biUnion.mp hf
      exact mem_biUnion.mpr ⟨i, mem_insert_of_mem hi, hif⟩
  calc
    coverage G p S + p e = ∑ f ∈ insert e (G.CS S), p f := by
      rw [sum_insert he]; dsimp [coverage]; ring
    _ ≤ coverage G p (insert j S) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun f _ _ => hp f)

/-- Every covered component survives deletion of all but at most one detector. -/
theorem sum_coverage_erase (G : DetectionModel V E) (p : E → ℝ)
    (hp : ∀ e, 0 ≤ p e) (S : Finset V) :
    ((S.card : ℝ) - 1) * coverage G p S ≤ ∑ i ∈ S, coverage G p (S.erase i) := by
  classical
  have hpoint (e : E) : ((S.card : ℝ) - 1) * (if e ∈ G.CS S then p e else 0) ≤
      ∑ i ∈ S, if e ∈ G.CS (S.erase i) then p e else 0 := by
    by_cases he : e ∈ G.CS S
    · obtain ⟨j, hj, hje⟩ := mem_biUnion.mp he
      have hsurv (i : V) (hi : i ∈ S.erase j) : e ∈ G.CS (S.erase i) := by
        have hne : j ≠ i := Ne.symm (mem_erase.mp hi).1
        exact mem_biUnion.mpr ⟨j, mem_erase.mpr ⟨hne, hj⟩, hje⟩
      have hc : 1 ≤ S.card := card_pos.mpr ⟨j, hj⟩
      calc
        _ = ∑ _i ∈ S.erase j, p e := by
          simp only [if_pos he, sum_const, card_erase_of_mem hj, nsmul_eq_mul]
          rw [Nat.cast_sub hc]; norm_num
        _ = ∑ i ∈ S.erase j, if e ∈ G.CS (S.erase i) then p e else 0 := by
          apply sum_congr rfl; intro i hi; simp [hsurv i hi]
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (erase_subset j S)
          (fun i _ _ => by split_ifs <;> simp [hp e])
    · simp only [if_neg he, mul_zero]
      exact sum_nonneg fun i _ => by split_ifs <;> simp [hp e]
  calc
    _ = ∑ e : E, ((S.card : ℝ) - 1) * (if e ∈ G.CS S then p e else 0) := by
      rw [← mul_sum]; simp [coverage]
    _ ≤ ∑ e : E, ∑ i ∈ S, if e ∈ G.CS (S.erase i) then p e else 0 :=
      sum_le_sum fun e _ => hpoint e
    _ = _ := by rw [sum_comm]; simp [coverage]

theorem heavy_avoidance_margin (G : DetectionModel V E) (p : E → ℝ)
    (hp : ∀ e, 0 ≤ p e) (b : ℕ) (hb : 2 ≤ b) (c v : ℝ)
    (hc : 0 ≤ c) (hv : v ≤ (b : ℝ) * c)
    (hfeas : ∀ S : Finset V, S.card ≤ b → coverage G p S ≤ v)
    (e : E) (he : c < p e) (S : Finset V) (hS : S.card ≤ b)
    (heS : e ∉ G.CS S) : coverage G p S + (p e - c) ≤ v := by
  classical
  obtain ⟨j, hj⟩ := G.coverable e
  by_cases hlt : S.card < b
  · have hins : (insert j S).card ≤ b :=
      (card_insert_le j S).trans (by omega)
    have hh := (coverage_insert_component G p hp S e heS j hj).trans (hfeas _ hins)
    linarith
  · have hcard : S.card = b := by omega
    have hjS : j ∉ S := by
      intro h; exact heS (mem_biUnion.mpr ⟨j, h, hj⟩)
    have hdel (i : V) (hi : i ∈ S) : coverage G p (S.erase i) ≤ v - p e := by
      have heDel : e ∉ G.CS (S.erase i) := by
        intro h; exact heS (mem_biUnion.mpr (by
          obtain ⟨k, hk, hke⟩ := mem_biUnion.mp h
          exact ⟨k, (mem_erase.mp hk).2, hke⟩))
      have hjDel : j ∉ S.erase i := fun h => hjS (mem_erase.mp h).2
      have hbudget : (insert j (S.erase i)).card ≤ b := by
        rw [card_insert_of_notMem hjDel, card_erase_of_mem hi, hcard]
        omega
      have hh := (coverage_insert_component G p hp (S.erase i) e heDel j hj).trans
        (hfeas _ hbudget)
      linarith
    have hsum := (sum_coverage_erase G p hp S).trans
      (sum_le_sum fun i hi => hdel i hi)
    rw [sum_const, nsmul_eq_mul, hcard] at hsum
    have hbR : (0 : ℝ) < (b : ℝ) - 1 := by
      have : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
      linarith
    apply le_of_mul_le_mul_left (a := (b : ℝ) - 1) ?_ hbR
    nlinarith

 /-- Repeatedly repair overweight coordinates without raising any feasible coverage bound. -/
theorem exists_capped_feasible (G : DetectionModel V E) (b : ℕ) (hb : 2 ≤ b)
    (c v : ℝ) (hc : 0 ≤ c) (hcapacity : 1 ≤ (Fintype.card E : ℝ) * c)
    (hv : v ≤ (b : ℝ) * c) (p : E → ℝ) (hp : BlottoLP.Flow.IsMixed p)
    (hfeas : ∀ S : Finset V, S.card ≤ b → coverage G p S ≤ v) :
    ∃ q : E → ℝ, BlottoLP.Flow.IsMixed q ∧
      (∀ S : Finset V, S.card ≤ b → coverage G q S ≤ v) ∧ ∀ e, q e ≤ c := by
  classical
  have hprocessed (s : Finset E) : ∃ q : E → ℝ, BlottoLP.Flow.IsMixed q ∧
      (∀ S : Finset V, S.card ≤ b → coverage G q S ≤ v) ∧ ∀ e ∈ s, q e ≤ c := by
    induction s using Finset.induction_on with
    | empty => exact ⟨p, hp, hfeas, by simp⟩
    | @insert e s hes ih =>
      obtain ⟨r, hr, hrf, hrs⟩ := ih
      by_cases he : r e ≤ c
      · refine ⟨r, hr, hrf, ?_⟩
        intro f hf
        rcases mem_insert.mp hf with rfl | hf
        · exact he
        · exact hrs f hf
      · have he' : c < r e := lt_of_not_ge he
        obtain ⟨q, hq, hqe, hpreserve, hsubset⟩ :=
          redistribute_coordinate r hr c hc hcapacity e he'
        refine ⟨q, hq, ?_, ?_⟩
        · intro S hS
          have hh := hsubset (G.CS S)
          change coverage G q S ≤ coverage G r S + (r e - c) -
            if e ∈ G.CS S then r e - c else 0 at hh
          by_cases heS : e ∈ G.CS S
          · rw [if_pos heS] at hh
            exact hh.trans (by linarith [hrf S hS])
          · rw [if_neg heS, sub_zero] at hh
            exact hh.trans (heavy_avoidance_margin G r hr.1 b hb c v hc hv hrf e he' S hS heS)
        · intro f hf
          rcases mem_insert.mp hf with rfl | hf
          · exact hqe.le
          · exact hpreserve f (hrs f hf)
  obtain ⟨q, hq, hqf, hqu⟩ := hprocessed univ
  exact ⟨q, hq, hqf, fun e => hqu e (mem_univ e)⟩

end Coverage


/-- A capped optimal component distribution, retaining its coverage minimax certificate. -/
theorem exists_capped_coverage_optimal {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : DetectionModel V E) (b1 : ℕ) (hm : 1 < G.mStar) :
    ∃ (p : E → ℝ) (v : ℝ), BlottoLP.Flow.IsMixed p ∧ v ≤ (b1 : ℝ) / G.mStar ∧
      (∀ S : Finset V, S.card ≤ b1 → ∑ e ∈ G.CS S, p e ≤ v) ∧
      (∀ q : E → ℝ, BlottoLP.Flow.IsMixed q →
        ∃ S : Finset V, S.card ≤ b1 ∧ v ≤ ∑ e ∈ G.CS S, q e) ∧
      ∀ e, p e ≤ 1 / (G.mStar : ℝ) := by
  classical
  have hmc : G.mStar ≤ Fintype.card E := mStar_le_card_packing G
  have hE : 0 < Fintype.card E := lt_of_lt_of_le (by omega : 0 < G.mStar) hmc
  letI : Nonempty E := Fintype.card_pos_iff.mp hE
  have hmR : (0 : ℝ) < G.mStar := by exact_mod_cast (by omega : 0 < G.mStar)
  obtain ⟨p, v, hp, hv, hupper, hlower⟩ := exists_coverage_minimax G b1
  have hcap : ∃ q : E → ℝ, BlottoLP.Flow.IsMixed q ∧
      (∀ S : Finset V, S.card ≤ b1 → ∑ e ∈ G.CS S, q e ≤ v) ∧
      ∀ e, q e ≤ 1 / (G.mStar : ℝ) := by
    by_cases hb0 : b1 = 0
    · obtain ⟨q, hq, hqc, hqb⟩ := uniform_packing_coverage G b1
      have h0v : 0 ≤ v := by
        simpa [DetectionModel.CS] using hupper ∅ (by simp)
      refine ⟨q, hq, ?_, hqc⟩
      intro S hS
      exact (hqb S hS).trans (by simpa [hb0] using h0v)
    · by_cases hbOne : b1 = 1
      · refine ⟨p, hp, hupper, ?_⟩
        intro e
        obtain ⟨j, hj⟩ := G.coverable e
        have he : e ∈ G.CS {j} := mem_biUnion.mpr ⟨j, mem_singleton_self j, hj⟩
        have hsingle : p e ≤ ∑ f ∈ G.CS {j}, p f :=
          single_le_sum (fun f _ => hp.1 f) he
        have hh := hupper {j} (by simp [hbOne])
        exact hsingle.trans (hh.trans (by simpa [hbOne] using hv))
      · have hb : 2 ≤ b1 := by omega
        have hcapacity : 1 ≤ (Fintype.card E : ℝ) * (1 / (G.mStar : ℝ)) := by
          have hh : (G.mStar : ℝ) ≤ Fintype.card E := by exact_mod_cast hmc
          simpa [div_eq_mul_inv] using (one_le_div₀ hmR).mpr hh
        have hv' : v ≤ (b1 : ℝ) * (1 / (G.mStar : ℝ)) := by
          simpa only [div_eq_mul_inv, one_mul] using hv
        obtain ⟨q, hq, hqf, hqc⟩ := exists_capped_feasible G b1 hb
          (1 / (G.mStar : ℝ)) v (by positivity) hcapacity hv' p hp hupper
        exact ⟨q, hq, hqf, hqc⟩
  obtain ⟨q, hq, hqf, hqc⟩ := hcap
  exact ⟨q, v, hq, hv, hqf, hlower, hqc⟩


/-- Single-attack optimal strategies can satisfy the maximum-packing marginal cap. -/
theorem theorem_2_step_ia {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DetectionModel V E) {b1 : ℕ} (hb1 : b1 < G.nStar) (hm : 1 < G.mStar) :
    ∃ σ2 : ActEx E 1 → ℝ, G.IsOptLP2bar b1 1 σ2 ∧
      ∀ e : E, marg σ2 e ≤ 1 / (G.mStar : ℝ) := by
  classical
  have hncard : G.nStar ≤ Fintype.card V := by
    apply Nat.sInf_le
    refine ⟨univ, by simp, ?_⟩
    intro e
    obtain ⟨i, hi⟩ := G.coverable e
    have he : e ∈ G.CS univ := mem_biUnion.mpr ⟨i, mem_univ _, hi⟩
    simp [F, he]
  have hbcard : b1 ≤ Fintype.card V := hb1.le.trans hncard
  obtain ⟨q, v, hq, _, hqf, hlower, hqc⟩ := exists_capped_coverage_optimal G b1 hm
  refine ⟨singletonExStrat q, singletonExStrat_optLP2bar G b1 hbcard q hq v hqf hlower, ?_⟩
  intro e
  simpa only [singletonExStrat_marg] using hqc e

end NetInspect.Rate



namespace NetInspect.Rate
open Finset DetectionModel BlottoLP.Flow
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

noncomputable def singletonExWeights (σ : ActEx E 1 → ℝ) : E → ℝ :=
  fun e => σ (singletonExEquiv E e)

 theorem singletonExWeights_mixed (σ : ActEx E 1 → ℝ) (hσ : IsMixed σ) :
    IsMixed (singletonExWeights σ) := by
  refine ⟨fun e => hσ.1 _, ?_⟩
  exact ((singletonExEquiv E).sum_comp σ).trans hσ.2

 theorem singletonExWeights_reconstruct (σ : ActEx E 1 → ℝ) :
    σ = singletonExStrat (singletonExWeights σ) := by
  funext T
  simp [singletonExStrat, singletonExWeights]

 theorem singletonExWeights_marg (σ : ActEx E 1 → ℝ) (e : E) :
    marg σ e = singletonExWeights σ e := by
  conv_lhs => rw [singletonExWeights_reconstruct σ]
  exact singletonExStrat_marg _ _

 theorem optimal_singleton_coverage_upper (G : DetectionModel V E) (b : ℕ)
    (hb : b ≤ Fintype.card V) (σex : ActEx E 1 → ℝ)
    (hopt : G.IsOptLP2bar b 1 σex) (p0 : E → ℝ) (hp0 : IsMixed p0) (v : ℝ)
    (hupper0 : ∀ S : Finset V, S.card ≤ b → ∑ e ∈ G.CS S, p0 e ≤ v) :
    ∀ S : Finset V, S.card ≤ b → ∑ e ∈ G.CS S, singletonExWeights σex e ≤ v := by
  classical
  obtain ⟨B, _, hB⟩ := exists_subset_card_eq (s := (univ : Finset V)) (by simpa using hb)
  letI : Nonempty (ActEx V b) := ⟨⟨B, hB⟩⟩
  have hp := singletonExWeights_mixed σex hopt.1
  have hlow : 1 - v ≤ G.best2Ex b (singletonExStrat p0) := by
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨X, rfl⟩
    change 1 - v ≤ expPay (G.payoffEx b 1) (singletonExStrat p0) (pureMixed X)
    rw [payoffEx_singleton G p0 hp0 X]
    linarith [hupper0 X.1 X.2.le]
  have hbest : 1 - v ≤ G.best2Ex b σex :=
    hlow.trans (hopt.2 (singletonExStrat p0) (singletonExStrat_mixed p0 hp0))
  have hexact (S : ActEx V b) : ∑ e ∈ G.CS S.1, singletonExWeights σex e ≤ v := by
    have hup : G.best2Ex b σex ≤
        expPay (G.payoffEx b 1) σex (pureMixed S) :=
      csInf_le (Set.finite_range (fun X : ActEx V b =>
        expPay (G.payoffEx b 1) σex (pureMixed X))).bddBelow (Set.mem_range_self S)
    rw [singletonExWeights_reconstruct σex, payoffEx_singleton G _ hp S] at hup
    have hbest' := hbest
    rw [singletonExWeights_reconstruct σex] at hbest'
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
theorem sum_marg_eq_expected_card {E : Type*} [Fintype E] [DecidableEq E]
    {b : ℕ} (σ : Act E b → ℝ) :
    ∑ e, marg σ e = ∑ T, σ T * (T.1.card : ℝ) := by
  unfold marg
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  simp [Finset.sum_ite_mem, mul_comm]

/-- Every mixed strategy over plans of size at most b has total marginal mass at most b. -/
theorem sum_marg_le_budget {E : Type*} [Fintype E] [DecidableEq E]
    {b : ℕ} (σ : Act E b → ℝ) (hσ : BlottoLP.Flow.IsMixed σ) :
    ∑ e, marg σ e ≤ (b : ℝ) := by
  rw [sum_marg_eq_expected_card]
  calc
    _ ≤ ∑ T : Act E b, σ T * (b : ℝ) := by
      apply Finset.sum_le_sum
      intro T _
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast T.2) (hσ.1 T)
    _ = (b : ℝ) := by rw [← Finset.sum_mul, hσ.2, one_mul]

end NetInspect.Rate



namespace NetInspect.Rate
open Finset Matrix

set_option backward.isDefEq.respectTransparency.types false in
theorem marginals_doubly_stochastic {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : E → ℝ) (B : Finset E) (hB : B.Nonempty) (hBc : Bᶜ.Nonempty)
    (hρ : ∀ e, 0 ≤ ρ e ∧ ρ e ≤ 1) (hs : ∑ e, ρ e = (B.card : ℝ)) :
    ((fun i j => if i ∈ B then ρ j / B.card else (1 - ρ j) / Bᶜ.card) : Matrix E E ℝ) ∈
      doublyStochastic ℝ E := by
  have hb : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  have hc : (Bᶜ.card : ℝ) ≠ 0 := by exact_mod_cast hBc.card_pos.ne'
  refine (mem_doublyStochastic_iff_sum (M :=
    (fun i j => if i ∈ B then ρ j / B.card else (1 - ρ j) / Bᶜ.card : Matrix E E ℝ))).2 ?_
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    split_ifs <;> exact div_nonneg (by linarith [(hρ j).1, (hρ j).2]) (Nat.cast_nonneg _)
  · intro i
    by_cases hi : i ∈ B
    · simp [hi, ← sum_div, hs, hb]
    · simp only [hi, ↓reduceIte, ← sum_div, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, hs]
      have hcard : (Fintype.card E : ℝ) - B.card = (Bᶜ.card : ℝ) := by
        have hh : (B.card : ℝ) + Bᶜ.card = Fintype.card E := by
          exact_mod_cast Finset.card_add_card_compl B
        linarith
      rw [hcard, div_self hc]
  · intro j
    rw [sum_ite]
    simp only [filter_mem_eq_inter, univ_inter]
    have hfilter : (univ.filter fun i => i ∉ B) = Bᶜ := by ext i; simp
    rw [hfilter]
    simp only [sum_const, nsmul_eq_mul]
    field_simp [hb, hc]
    <;> ring
theorem realize_from_finite_family {E K : Type*} [Fintype E] [DecidableEq E]
    [Fintype K] {b : ℕ} (A : K → Act E b) (w : K → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) :
    ∃ σ : Act E b → ℝ, BlottoLP.Flow.IsMixed σ ∧
      ∀ e, marg σ e = ∑ k, if e ∈ (A k).1 then w k else 0 := by
  classical
  let σ : Act E b → ℝ := fun T => ∑ k, if A k = T then w k else 0
  refine ⟨σ, ⟨?_, ?_⟩, ?_⟩
  · intro T
    exact sum_nonneg fun k _ => by split_ifs <;> simp_all
  · dsimp [σ]
    rw [sum_comm]
    simpa using hs
  · intro e
    unfold marg
    dsimp [σ]
    simp_rw [Finset.ite_sum_zero]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    by_cases he : e ∈ (A k).1
    · simp only [he, ↓reduceIte]
      rw [sum_eq_single (A k)]
      · simp [he]
      · intro T _ hT
        by_cases ht : e ∈ T.1 <;> simp [ht, Ne.symm hT]
      · simp
    · simp only [he, ↓reduceIte]
      apply sum_eq_zero
      intro T _
      by_cases ht : e ∈ T.1
      · have hn : A k ≠ T := by intro h; exact he (h ▸ ht)
        simp [ht, hn]
      · simp [ht]

theorem sum_permMatrix_subset {E : Type*} [Fintype E] [DecidableEq E]
    (B : Finset E) (π : Equiv.Perm E) (e : E) :
    ∑ i ∈ B, π.permMatrix ℝ i e = if e ∈ B.image π then 1 else 0 := by
  classical
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq]
  by_cases he : π.symm e ∈ B
  · rw [sum_eq_single (π.symm e)]
    · simp [mem_image, he, Equiv.apply_eq_iff_eq_symm_apply]
    · intro i hi hn
      simp [show π i ≠ e by intro h; exact hn (π.injective (by simpa using h))]
    · simp [he]
  · have he' : e ∉ B.image π := by
      rintro he'
      obtain ⟨i, hi, hie⟩ := mem_image.mp he'
      exact he (by simpa [← hie] using hi)
    rw [if_neg he']
    apply sum_eq_zero
    intro i hi
    have hn : π i ≠ e := by intro h; exact he (by simpa [← h] using hi)
    simp [hn]
theorem realize_marginals_of_subset {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : E → ℝ) (B : Finset E) (hB : B.Nonempty) (hBc : Bᶜ.Nonempty)
    (hρ : ∀ e, 0 ≤ ρ e ∧ ρ e ≤ 1) (hs : ∑ e, ρ e = (B.card : ℝ)) :
    ∃ σ : Act E B.card → ℝ, BlottoLP.Flow.IsMixed σ ∧ ∀ e, marg σ e = ρ e := by
  classical
  let M : Matrix E E ℝ := fun i j =>
    if i ∈ B then ρ j / B.card else (1 - ρ j) / Bᶜ.card
  obtain ⟨w, hw, hw1, hM⟩ := exists_eq_sum_perm_of_mem_doublyStochastic
    (marginals_doubly_stochastic ρ B hB hBc hρ hs)
  let A : Equiv.Perm E → Act E B.card := fun π =>
    ⟨B.image π, by rw [card_image_of_injective _ π.injective]⟩
  obtain ⟨σ, hσ, hm⟩ := realize_from_finite_family A w hw hw1
  refine ⟨σ, hσ, fun e => ?_⟩
  rw [hm]
  change (∑ π : Equiv.Perm E, if e ∈ B.image π then w π else 0) = ρ e
  calc
    _ = ∑ π : Equiv.Perm E, w π * ∑ i ∈ B, π.permMatrix ℝ i e := by
      apply sum_congr rfl
      intro π _
      rw [sum_permMatrix_subset]
      split_ifs <;> simp
    _ = ∑ i ∈ B, M i e := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      have hij := congrArg (fun X : Matrix E E ℝ => X i e) hM
      simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, M] using hij
    _ = ρ e := by
      have hb : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
      calc
        _ = ∑ _i ∈ B, ρ e / (B.card : ℝ) := by
          apply sum_congr rfl
          intro i hi
          simp [M, hi]
        _ = ρ e := by simp only [sum_const, nsmul_eq_mul]; field_simp
theorem realize_marginals {E : Type*} [Fintype E] [DecidableEq E]
    (b : ℕ) (ρ : E → ℝ) (hρ : ∀ e, 0 ≤ ρ e ∧ ρ e ≤ 1)
    (hs : ∑ e, ρ e = (b : ℝ)) :
    ∃ σ : Act E b → ℝ, BlottoLP.Flow.IsMixed σ ∧ ∀ e, marg σ e = ρ e := by
  classical
  have hb : b ≤ Fintype.card E := by
    have hh : (b : ℝ) ≤ Fintype.card E := by
      rw [← hs]
      calc
        _ ≤ ∑ _ : E, (1 : ℝ) := sum_le_sum fun e _ => (hρ e).2
        _ = _ := by simp
    exact_mod_cast hh
  by_cases hz : b = 0
  · subst b
    have hr : ∀ e, ρ e = 0 := by
      have hs0 : ∑ e, ρ e = 0 := by simpa using hs
      have hh := (sum_eq_zero_iff_of_nonneg (s := univ) (fun e _ => (hρ e).1)).1 hs0
      exact fun e => hh e (mem_univ e)
    obtain ⟨σ, hσ, hm⟩ := realize_from_finite_family
      (fun _ : Unit => (⟨∅, by simp⟩ : Act E 0)) (fun _ => (1 : ℝ)) (by simp) (by simp)
    refine ⟨σ, hσ, fun e => ?_⟩
    simpa [hr e] using hm e
  by_cases hn : b = Fintype.card E
  · have hr : ∀ e, ρ e = 1 := by
      have hh : ∑ e, (1 - ρ e) = 0 := by simp [sum_sub_distrib, hs, hn]
      have hh' := (sum_eq_zero_iff_of_nonneg
        (fun e _ => sub_nonneg.mpr (hρ e).2)).1 hh
      intro e
      have := hh' e (mem_univ e)
      linarith
    obtain ⟨σ, hσ, hm⟩ := realize_from_finite_family
      (fun _ : Unit => (⟨univ, by simp [hn]⟩ : Act E b))
      (fun _ => (1 : ℝ)) (by simp) (by simp)
    refine ⟨σ, hσ, fun e => ?_⟩
    simpa [hr e] using hm e
  obtain ⟨B, _, hB⟩ := exists_subset_card_eq (s := (univ : Finset E)) (by simpa using hb)
  have hne : B.Nonempty := card_pos.mp (by omega)
  have hcne : Bᶜ.Nonempty := card_pos.mp (by rw [card_compl, hB]; omega)
  subst b
  exact realize_marginals_of_subset ρ B hne hcne hρ hs

theorem lemma_EC_4 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DetectionModel V E)
    {b2 : ℕ} (hb2 : b2 < G.mStar) (ρ : E → ℝ) (hρ : ∀ e : E, 0 ≤ ρ e ∧ ρ e ≤ 1)
    (hsum : ∑ e : E, ρ e = (b2 : ℝ)) :
    ∃ σ2 : Act E b2 → ℝ, BlottoLP.Flow.IsMixed σ2 ∧ ∀ e : E, marg σ2 e = ρ e :=
  realize_marginals b2 ρ hρ hsum

end NetInspect.Rate




namespace NetInspect.Rate
open Finset DetectionModel BlottoLP.Flow
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The exact conclusion of the network detection-rate theorem. -/
def DetectionRateConclusion (G : DetectionModel V E) (b1 : ℕ) : Prop :=
    (∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧
      ∀ b2 : ℕ, 1 ≤ b2 → b2 < G.mStar →
        ∀ (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ), G.IsNE b1 b2 σ1 σ2 → G.rate σ1 σ2 = r) ∧
    (∀ (σ1 : Act V b1 → ℝ) (σ2 : Act E 1 → ℝ), G.IsNE b1 1 σ1 σ2 →
      ∀ b2 : ℕ, 1 ≤ b2 → b2 < G.mStar →
        ∃ σ2' : Act E b2 → ℝ, G.IsNE b1 b2 σ1 σ2')

 theorem theorem_2_vacuous (G : DetectionModel V E) (b1 : ℕ) (hm : G.mStar ≤ 1) :
    DetectionRateConclusion G b1 := by
  refine ⟨⟨0, le_rfl, zero_le_one, ?_⟩, ?_⟩
  · intro b2 hb hm'
    omega
  · intro σ1 σ2 hne b2 hb hm'
    omega

 lemma mStar_le_card (G : DetectionModel V E) : G.mStar ≤ Fintype.card E := by
  apply csSup_le
  · exact ⟨0, ∅, by simp, by simp [IsSetPacking, F]⟩
  · rintro k ⟨T, rfl, hT⟩
    exact Finset.card_le_univ T

 lemma act_zero_eq_empty (S : Act V 0) : S.1 = ∅ :=
    Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero S.2)

 lemma mixed_zero_unique {σ τ : Act V 0 → ℝ} (hσ : IsMixed σ) (hτ : IsMixed τ) : σ = τ := by
  classical
  letI : Subsingleton (Act V 0) := ⟨fun S T => Subtype.ext ((act_zero_eq_empty S).trans (act_zero_eq_empty T).symm)⟩
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

 lemma zero_budget_payoff (G : DetectionModel V E) {b2 : ℕ}
    (T : Act E b2) (S : Act V 0) : G.payoff 0 b2 T S = T.1.card := by
  simp [payoff, undet, F, CS, act_zero_eq_empty S]

 theorem zero_budget_rate (G : DetectionModel V E) {b2 : ℕ} (hb : 1 ≤ b2)
    (hcard : b2 ≤ Fintype.card E) (σ1 : Act V 0 → ℝ) (σ2 : Act E b2 → ℝ)
    (hne : G.IsNE 0 b2 σ1 σ2) : G.rate σ1 σ2 = 0 := by
  classical
  have hp (τ : Act E b2 → ℝ) : expPay (G.payoff 0 b2) τ σ1 = ∑ T, τ T * (T.1.card : ℝ) := by
    unfold expPay
    apply sum_congr rfl
    intro T _
    simp_rw [zero_budget_payoff]
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
      simp [ratio, hv, F, CS, act_zero_eq_empty S, h]
  unfold rate expPay
  simp_rw [hratio]
  simp [mul_ite, he]

 theorem theorem_2_zero (G : DetectionModel V E) : DetectionRateConclusion G 0 := by
  classical
  refine ⟨⟨0, le_rfl, zero_le_one, ?_⟩, ?_⟩
  · intro b2 hb hm σ1 σ2 hne
    exact zero_budget_rate G hb (le_trans hm.le (mStar_le_card G)) σ1 σ2 hne
  · intro σ1 σ2 hne b2 hb hm
    letI : Nonempty (Act E b2) := ⟨⟨∅, by simp⟩⟩
    letI : Nonempty (Act V 0) := ⟨⟨∅, by simp⟩⟩
    obtain ⟨τ2, τ1, hτ⟩ := exists_isNashEq (G.payoff 0 b2)
    have heq : τ1 = σ1 := mixed_zero_unique hτ.2.1 hne.2.1
    exact ⟨τ2, heq ▸ hτ⟩

lemma undet_nonneg (G : DetectionModel V E) (S : Finset V) (T : Finset E) :
    0 ≤ G.undet S T := by
  unfold undet
  exact sub_nonneg.mpr (by exact_mod_cast (card_le_card (inter_subset_right : G.CS S ∩ T ⊆ T)))

lemma U_nonneg (G : DetectionModel V E) {b1 b2 : ℕ}
    {σ1 : Act V b1 → ℝ} {σ2 : Act E b2 → ℝ}
    (h1 : IsMixed σ1) (h2 : IsMixed σ2) : 0 ≤ G.U σ1 σ2 := by
  exact sum_nonneg fun T _ => sum_nonneg fun S _ =>
    mul_nonneg (mul_nonneg (h2.1 T) (h1.1 S)) (undet_nonneg G S.1 T.1)

lemma ratio_eq_one_of_undet_eq_zero (G : DetectionModel V E) (S : Finset V) (T : Finset E)
    (h : G.undet S T = 0) : G.ratio S T = 1 := by
  unfold ratio
  split_ifs with ht
  · rfl
  · have hc : (T.card : ℝ) ≠ 0 := by exact_mod_cast (card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr ht))
    have hf : (G.F S T : ℝ) = T.card := by unfold undet at h; linarith
    rw [hf, div_self hc]

 theorem rate_eq_one_of_U_eq_zero (G : DetectionModel V E) {b1 b2 : ℕ}
    {σ1 : Act V b1 → ℝ} {σ2 : Act E b2 → ℝ}
    (h1 : IsMixed σ1) (h2 : IsMixed σ2) (hu : G.U σ1 σ2 = 0) : G.rate σ1 σ2 = 1 := by
  classical
  have hn (T : Act E b2) (S : Act V b1) :
      0 ≤ σ2 T * σ1 S * G.undet S.1 T.1 :=
    mul_nonneg (mul_nonneg (h2.1 T) (h1.1 S)) (undet_nonneg G S.1 T.1)
  have hz (T : Act E b2) (S : Act V b1) : σ2 T * σ1 S * G.undet S.1 T.1 = 0 := by
    have hrow := (sum_eq_zero_iff_of_nonneg fun T _ => sum_nonneg fun S _ => hn T S).mp hu T (mem_univ _)
    exact (sum_eq_zero_iff_of_nonneg fun S _ => hn T S).mp hrow S (mem_univ _)
  have ht (T : Act E b2) (S : Act V b1) : σ2 T * σ1 S * G.ratio S.1 T.1 = σ2 T * σ1 S := by
    by_cases hw : σ2 T * σ1 S = 0
    · rw [hw, zero_mul]
    · have hu' : G.undet S.1 T.1 = 0 := (mul_eq_zero.mp (hz T S)).resolve_left hw
      rw [ratio_eq_one_of_undet_eq_zero G S.1 T.1 hu', mul_one]
  unfold rate expPay
  simp_rw [ht, ← mul_sum, h1.2, mul_one, h2.2]

lemma exists_cover_le (G : DetectionModel V E) {b1 : ℕ} (hb : G.nStar ≤ b1) :
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

lemma cover_undet (G : DetectionModel V E) (S : Finset V) (hc : G.IsSetCover S)
    (T : Finset E) : G.undet S T = 0 := by
  have hmem e : e ∈ G.CS S := by
    have h := hc e
    by_contra hn
    simp [F, hn] at h
  have hsub : T ⊆ G.CS S := fun e _ => hmem e
  simp [undet, F, inter_eq_right.mpr hsub]

 theorem equilibrium_U_zero_of_cover (G : DetectionModel V E) {b1 b2 : ℕ}
    (hb : G.nStar ≤ b1) {σ1 : Act V b1 → ℝ} {σ2 : Act E b2 → ℝ}
    (hne : G.IsNE b1 b2 σ1 σ2) : G.U σ1 σ2 = 0 := by
  classical
  obtain ⟨S, hc⟩ := exists_cover_le G hb
  have hp : IsMixed (pureMixed S) := by
    constructor
    · intro a; simp only [pureMixed]; split_ifs <;> norm_num
    · simp [pureMixed]
  have h := hne.2.2.2 (pureMixed S) hp
  have hz : expPay (G.payoff b1 b2) σ2 (pureMixed S) = 0 := by
    simp [expPay, pureMixed, payoff, cover_undet G S.1 hc]
  rw [hz] at h
  exact le_antisymm h (U_nonneg G hne.2.1 hne.1)

lemma U_pure_singleton (G : DetectionModel V E) {b1 : ℕ}
    (σ1 : Act V b1 → ℝ) (e : E) :
    G.U σ1 (pureMixed (⟨{e}, by simp⟩ : Act E 1)) = G.missProb σ1 e := by
  classical
  simp [U, expPay, pureMixed, payoff, undet_eq_sum, DetectionModel.missProb]

 theorem theorem_2_cover (G : DetectionModel V E) {b1 : ℕ} (hb : G.nStar ≤ b1) :
    DetectionRateConclusion G b1 := by
  classical
  refine ⟨⟨1, zero_le_one, le_rfl, ?_⟩, ?_⟩
  · intro b2 hb2 hm σ1 σ2 hne
    exact rate_eq_one_of_U_eq_zero G hne.2.1 hne.1 (equilibrium_U_zero_of_cover G hb hne)
  · intro σ1 σ2 hne b2 hb2 hm
    have hu : G.U σ1 σ2 = 0 := equilibrium_U_zero_of_cover G hb hne
    have hmiss (e : E) : G.missProb σ1 e = 0 := by
      let t : Act E 1 := ⟨{e}, by simp⟩
      have ht : IsMixed (pureMixed t) := by
        constructor
        · intro a; simp only [pureMixed]; split_ifs <;> norm_num
        · simp [pureMixed]
      have h := hne.2.2.1 (pureMixed t) ht
      change G.U σ1 (pureMixed t) ≤ G.U σ1 σ2 at h
      rw [hu] at h
      have hh : G.U σ1 (pureMixed t) = G.missProb σ1 e := U_pure_singleton G σ1 e
      rw [hh] at h
      exact le_antisymm h (missProb_nonneg G σ1 hne.2.1 e)
    have hzero (τ : Act E b2 → ℝ) : G.U σ1 τ = 0 := by
      rw [U_eq_sum_marg]
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
      exact U_nonneg G hτ he

end NetInspect.Rate








namespace NetInspect.Rate
open Finset DetectionModel BlottoLP.Flow
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem marg_nonneg_of_mixed {b : ℕ} (σ : Act E b → ℝ) (hσ : IsMixed σ) (e : E) :
    0 ≤ marg σ e := by
  classical
  unfold marg
  apply sum_nonneg
  intro T _
  split_ifs
  · exact hσ.1 T
  · exact le_rfl

theorem complete_single_marginals [Nonempty E] (σ : Act E 1 → ℝ) (hσ : IsMixed σ) :
    ∃ q : E → ℝ, IsMixed q ∧ ∀ e, marg σ e ≤ q e := by
  classical
  let e0 : E := Classical.choice inferInstance
  let M := ∑ e, marg σ e
  have hM : M ≤ 1 := by simpa [M] using sum_marg_le_budget σ hσ
  let q : E → ℝ := fun e => marg σ e + if e = e0 then 1 - M else 0
  refine ⟨q, ⟨?_, ?_⟩, ?_⟩
  · intro e
    exact add_nonneg (marg_nonneg_of_mixed σ hσ e) (by split_ifs <;> linarith)
  · dsimp [q]
    rw [sum_add_distrib]
    simp [M]
    <;> ring
  · intro e
    dsimp [q]
    have : 0 ≤ if e = e0 then 1 - M else 0 := by split_ifs <;> linarith
    linarith

theorem U_pure_eq_marg_sum {b1 b2 : ℕ} (G : DetectionModel V E)
    (S : Act V b1) (σ2 : Act E b2 → ℝ) :
    G.U (pureMixed S) σ2 = ∑ e, marg σ2 e * (if e ∈ G.CS S.1 then (0 : ℝ) else 1) := by
  classical
  rw [U_eq_sum_marg]
  simp only [DetectionModel.missProb, pureMixed, ite_mul, one_mul, zero_mul,
    sum_ite_eq', sum_ite_eq, mem_univ, ↓reduceIte]

theorem sum_miss_eq_one_sub_coverage (G : DetectionModel V E)
    (q : E → ℝ) (hq : IsMixed q) (S : Finset V) :
    (∑ e, q e * (if e ∈ G.CS S then (0 : ℝ) else 1)) = 1 - ∑ e ∈ G.CS S, q e := by
  classical
  have he (e : E) : q e * (if e ∈ G.CS S then (0 : ℝ) else 1) =
      q e - if e ∈ G.CS S then q e else 0 := by split_ifs <;> simp
  simp_rw [he]
  rw [sum_sub_distrib, hq.2]
  simp

theorem single_equilibrium_of_capped_coverage [Nonempty E] (G : DetectionModel V E)
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
  obtain ⟨q, hq, hqge⟩ := complete_single_marginals σ2 hne.1
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
        rw [U_pure_eq_marg_sum]
        exact sum_le_sum fun e _ => mul_le_mul_of_nonneg_right (hqge e) (by split_ifs <;> norm_num)
      _ = 1 - ∑ e ∈ G.CS S, q e := sum_miss_eq_one_sub_coverage G q hq S
      _ ≤ 1 - v := by linarith
  have hsecure (ρ : Act V b → ℝ) (hρ : IsMixed ρ) : 1 - v ≤ G.U ρ τ2 := by
    apply le_expPay_of_pure_right (G.payoff b 1) τ2 hρ (1 - v)
    intro X
    change 1 - v ≤ G.U (pureMixed X) τ2
    rw [U_pure_eq_marg_sum]
    simp_rw [hmarg]
    rw [sum_miss_eq_one_sub_coverage G p hp]
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

theorem scale_capped_equilibrium (G : DetectionModel V E) {b1 b2 : ℕ}
    (σ1 : Act V b1 → ℝ) (τ1 : Act E 1 → ℝ) (hne : G.IsNE b1 1 σ1 τ1)
    (p : E → ℝ) (hp : IsMixed p) (hmarg : ∀ e, marg τ1 e = p e)
    (hcap : ∀ e, p e ≤ 1 / (G.mStar : ℝ)) (hb2 : 1 ≤ b2) (hbm : b2 < G.mStar) :
    ∃ τ2 : Act E b2 → ℝ, G.IsNE b1 b2 σ1 τ2 ∧
      G.U σ1 τ2 = (b2 : ℝ) * G.U σ1 τ1 ∧
      ∀ e, G.missProb σ1 e ≤ G.U σ1 τ1 := by
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
    apply U_eq_mul_of_marg_eq_mul
    intro e
    rw [hτmarg, hmarg]
  have hmiss (e : E) : G.missProb σ1 e ≤ G.U σ1 τ1 := by
    let t : Act E 1 := ⟨{e}, by simp⟩
    have ht : IsMixed (pureMixed t) := by
      constructor
      · intro X; simp only [pureMixed]; split_ifs <;> norm_num
      · simp [pureMixed]
    have hh := hne.2.2.1 (pureMixed t) ht
    change G.U σ1 (pureMixed t) ≤ G.U σ1 τ1 at hh
    simpa only [t, U_pure_singleton] using hh
  have hu : 0 ≤ G.U σ1 τ1 := by
    rw [U_eq_sum_marg]
    exact sum_nonneg fun e _ => mul_nonneg (marg_nonneg_of_mixed τ1 hne.1 e)
      (missProb_nonneg G σ1 hne.2.1 e)
  refine ⟨τ2, ⟨hτ2, hne.2.1, ?_, ?_⟩, hscale σ1, hmiss⟩
  · intro σ hσ
    change G.U σ1 σ ≤ G.U σ1 τ2
    rw [hscale σ1, U_eq_sum_marg]
    calc
      _ ≤ ∑ e, marg σ e * G.U σ1 τ1 := sum_le_sum fun e _ =>
        mul_le_mul_of_nonneg_left (hmiss e) (marg_nonneg_of_mixed σ hσ e)
      _ = (∑ e, marg σ e) * G.U σ1 τ1 := (sum_mul _ _ _).symm
      _ ≤ (b2 : ℝ) * G.U σ1 τ1 := mul_le_mul_of_nonneg_right (sum_marg_le_budget σ hσ) hu
  · intro σ hσ
    change G.U σ1 τ2 ≤ G.U σ τ2
    rw [hscale σ1, hscale σ]
    exact mul_le_mul_of_nonneg_left (hne.2.2.2 σ hσ) (Nat.cast_nonneg _)

end NetInspect.Rate




namespace NetInspect.Rate
open Finset DetectionModel BlottoLP.Flow
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

 theorem support_card_eq_of_sum_marg_eq {b : ℕ} (σ : Act E b → ℝ)
    (hσ : IsMixed σ) (hsum : ∑ e, marg σ e = (b : ℝ)) :
    ∀ T, 0 < σ T → T.1.card = b := by
  classical
  have hz : ∑ T : Act E b, σ T * ((b : ℝ) - T.1.card) = 0 := by
    simp_rw [mul_sub]
    rw [sum_sub_distrib, ← sum_mul, hσ.2, one_mul,
      ← sum_marg_eq_expected_card, hsum, sub_self]
  have hn T : 0 ≤ σ T * ((b : ℝ) - T.1.card) :=
    mul_nonneg (hσ.1 T) (sub_nonneg.mpr (by exact_mod_cast T.2))
  intro T hT
  have ht := (sum_eq_zero_iff_of_nonneg fun T _ => hn T).mp hz T (mem_univ _)
  have he := (mul_eq_zero.mp ht).resolve_left hT.ne'
  have hc : (T.1.card : ℝ) = b := by linarith
  exact_mod_cast hc

 theorem support_card_eq_of_payoff_eq (G : DetectionModel V E) {b1 b2 : ℕ}
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ) (h2 : IsMixed σ2)
    (v : ℝ) (hv : 0 < v) (hmiss : ∀ e, G.missProb σ1 e ≤ v)
    (hu : G.U σ1 σ2 = (b2 : ℝ) * v) :
    ∀ T, 0 < σ2 T → T.1.card = b2 := by
  have hm (e : E) : 0 ≤ marg σ2 e := by
    unfold marg
    apply sum_nonneg
    intro T _
    split_ifs <;> simp [h2.1 T]
  have hupper : G.U σ1 σ2 ≤ (∑ e, marg σ2 e) * v := by
    rw [U_eq_sum_marg, sum_mul]
    exact sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hmiss e) (hm e)
  have hmass : ∑ e, marg σ2 e = (b2 : ℝ) := by
    have hle := sum_marg_le_budget σ2 h2
    rw [hu] at hupper
    nlinarith
  exact support_card_eq_of_sum_marg_eq σ2 h2 hmass

 theorem ratio_eq_one_sub_undet_div (G : DetectionModel V E) (S : Finset V) (T : Finset E)
    {b : ℕ} (hb : 0 < b) (hT : T.card = b) :
    G.ratio S T = 1 - G.undet S T / (b : ℝ) := by
  have ht : T ≠ ∅ := by intro h; simp [h] at hT; omega
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  unfold ratio undet
  rw [if_neg ht, hT]
  field_simp
  ring

 theorem rate_eq_one_sub_U_div (G : DetectionModel V E) {b1 b2 : ℕ}
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
      rw [ratio_eq_one_sub_undet_div G S.1 T.1 hb (hsupport T hpos)]
      ring
  unfold rate U expPay payoff
  simp_rw [ht, sum_sub_distrib, ← sum_div]
  simp_rw [← mul_sum, h1.2, mul_one, h2.2]

 theorem rate_eq_one_sub_value (G : DetectionModel V E) {b1 b2 : ℕ}
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ)
    (h1 : IsMixed σ1) (h2 : IsMixed σ2) (hb : 0 < b2)
    (v : ℝ) (hv : 0 < v) (hmiss : ∀ e, G.missProb σ1 e ≤ v)
    (hu : G.U σ1 σ2 = (b2 : ℝ) * v) : G.rate σ1 σ2 = 1 - v := by
  rw [rate_eq_one_sub_U_div G σ1 σ2 h1 h2 hb
    (support_card_eq_of_payoff_eq G σ1 σ2 h2 v hv hmiss hu), hu]
  have hbR : (b2 : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [mul_div_cancel_left₀ v hbR]

 theorem equilibrium_U_pos_of_lt_nStar (G : DetectionModel V E) {b1 : ℕ}
    (hb : b1 < G.nStar) (σ1 : Act V b1 → ℝ) (σ2 : Act E 1 → ℝ)
    (hne : G.IsNE b1 1 σ1 σ2) : 0 < G.U σ1 σ2 := by
  classical
  have hn := U_nonneg G hne.2.1 hne.1
  by_contra hpos
  have hu : G.U σ1 σ2 = 0 := le_antisymm (le_of_not_gt hpos) hn
  have hmiss (e : E) : G.missProb σ1 e = 0 := by
    let t : Act E 1 := ⟨{e}, by simp⟩
    have ht : IsMixed (pureMixed t) := by
      constructor
      · intro a; simp only [pureMixed]; split_ifs <;> norm_num
      · simp [pureMixed]
    have h := hne.2.2.1 (pureMixed t) ht
    change G.U σ1 (pureMixed t) ≤ G.U σ1 σ2 at h
    rw [hu] at h
    have he : G.U σ1 (pureMixed t) = G.missProb σ1 e := U_pure_singleton G σ1 e
    rw [he] at h
    exact le_antisymm h (missProb_nonneg G σ1 hne.2.1 e)
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
    unfold DetectionModel.missProb at hzero
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

 theorem equilibrium_rate_eq_of_reference (G : DetectionModel V E) {b1 b2 : ℕ}
    (σref : Act V b1 → ℝ) (τref : Act E b2 → ℝ)
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ)
    (href : G.IsNE b1 b2 σref τref) (hne : G.IsNE b1 b2 σ1 σ2)
    (hb : 0 < b2) (v : ℝ) (hv : 0 < v)
    (hmiss : ∀ e, G.missProb σref e ≤ v)
    (huref : G.U σref τref = (b2 : ℝ) * v) : G.rate σ1 σ2 = 1 - v := by
  have hcross : G.IsNE b1 b2 σref σ2 := hne.cross href
  have hucross : G.U σref σ2 = (b2 : ℝ) * v := (hcross.expPay_eq href).trans huref
  have hu : G.U σ1 σ2 = (b2 : ℝ) * v := (hne.expPay_eq href).trans huref
  have hsupport := support_card_eq_of_payoff_eq G σref σ2 hne.1 v hv hmiss hucross
  rw [rate_eq_one_sub_U_div G σ1 σ2 hne.2.1 hne.1 hb hsupport, hu]
  have hbR : (b2 : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [mul_div_cancel_left₀ v hbR]

end NetInspect.Rate





namespace NetInspect.Rate
open Finset DetectionModel BlottoLP.Flow
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem gameValue_eq_U_of_NE (G : DetectionModel V E) {b1 b2 : ℕ}
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
    apply expPay_le_of_pure_left (G.payoff b1 b2) hne.1 τ1
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

theorem capped_equilibrium_for_defender [Nonempty E] (G : DetectionModel V E)
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
  obtain ⟨p0, v, hp0, hv, hupper0, hopt⟩ := exists_coverage_minimax G b
  obtain ⟨σex, hσopt, hσcap⟩ := theorem_2_step_ia G hb hm
  let p := singletonExWeights σex
  have hp : IsMixed p := singletonExWeights_mixed σex hσopt.1
  have hcap : ∀ e, p e ≤ 1 / (G.mStar : ℝ) := by
    intro e
    simpa only [p, singletonExWeights_marg] using hσcap e
  have hupper : ∀ S : Finset V, S.card ≤ b → ∑ e ∈ G.CS S, p e ≤ v :=
    optimal_singleton_coverage_upper G b hbcard σex hσopt p0 hp0 v hupper0
  obtain ⟨τ1, hτ, hτmarg, hval⟩ := single_equilibrium_of_capped_coverage
    G b hm p hp hcap v hupper hopt σ1 σ2 hne
  exact ⟨p, τ1, hp, hcap, hτ, hτmarg⟩

theorem theorem_2_intermediate (G : DetectionModel V E) {b : ℕ}
    (hb : b < G.nStar) (hm : 1 < G.mStar) : DetectionRateConclusion G b := by
  classical
  have hcardE : 0 < Fintype.card E := lt_of_lt_of_le (by omega) (mStar_le_card G)
  letI : Nonempty E := Fintype.card_pos_iff.mp hcardE
  letI : Nonempty (Act V b) := ⟨⟨∅, by simp⟩⟩
  letI : Nonempty (Act E 1) := ⟨⟨∅, by simp⟩⟩
  obtain ⟨σ2, σ1, hbase⟩ := exists_isNashEq (G.payoff b 1)
  change G.IsNE b 1 σ1 σ2 at hbase
  obtain ⟨p, τ1, hp, hcap, href, hmarg⟩ := capped_equilibrium_for_defender G hb hm σ1 σ2 hbase
  let u := G.U σ1 τ1
  have hu : 0 < u := equilibrium_U_pos_of_lt_nStar G hb σ1 τ1 href
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [U_eq_sum_marg]
    simp_rw [hmarg]
    calc
      _ ≤ ∑ e, p e := sum_le_sum fun e _ => by
        simpa using mul_le_mul_of_nonneg_left (missProb_le_one G σ1 href.2.1 e) (hp.1 e)
      _ = 1 := hp.2
  refine ⟨⟨1-u, by linarith, by linarith, ?_⟩, ?_⟩
  · intro b2 hb2 hbm ρ1 ρ2 hne
    obtain ⟨τ2, hscaled, hval, hmiss⟩ := scale_capped_equilibrium G σ1 τ1 href p hp hmarg hcap hb2 hbm
    exact equilibrium_rate_eq_of_reference G σ1 τ2 ρ1 ρ2 hscaled hne
      (by omega) u hu hmiss hval
  · intro ρ1 ρ2 hne b2 hb2 hbm
    obtain ⟨p', τ', hp', hcap', href', hmarg'⟩ := capped_equilibrium_for_defender G hb hm ρ1 ρ2 hne
    obtain ⟨τ2, hscaled, _, _⟩ := scale_capped_equilibrium G ρ1 τ' href' p' hp' hmarg' hcap' hb2 hbm
    exact ⟨τ2, hscaled⟩

theorem eq_18 (G : DetectionModel V E)
    {b1 b2 : ℕ} (hb1 : b1 < G.nStar) (hb2 : 1 ≤ b2) (hb2m : b2 < G.mStar) :
    G.gameValue b1 b2 = (b2 : ℝ) * G.gameValue b1 1 := by
  classical
  have hm : 1 < G.mStar := hb2.trans_lt hb2m
  have hcardE : 0 < Fintype.card E := lt_of_lt_of_le (by omega) (mStar_le_card G)
  letI : Nonempty E := Fintype.card_pos_iff.mp hcardE
  letI : Nonempty (Act V b1) := ⟨⟨∅, by simp⟩⟩
  letI : Nonempty (Act E 1) := ⟨⟨∅, by simp⟩⟩
  obtain ⟨σ2, σ1, hbase⟩ := exists_isNashEq (G.payoff b1 1)
  change G.IsNE b1 1 σ1 σ2 at hbase
  obtain ⟨p, τ1, hp, hcap, href, hmarg⟩ := capped_equilibrium_for_defender G hb1 hm σ1 σ2 hbase
  obtain ⟨τ2, hscaled, hval, _⟩ := scale_capped_equilibrium G σ1 τ1 href p hp hmarg hcap hb2 hb2m
  rw [gameValue_eq_U_of_NE G σ1 τ2 hscaled, gameValue_eq_U_of_NE G σ1 τ1 href]
  exact hval

theorem theorem_2 (G : DetectionModel V E) (b1 : ℕ) :
    (∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧
      ∀ b2 : ℕ, 1 ≤ b2 → b2 < G.mStar →
        ∀ (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ), G.IsNE b1 b2 σ1 σ2 → G.rate σ1 σ2 = r) ∧
    (∀ (σ1 : Act V b1 → ℝ) (σ2 : Act E 1 → ℝ), G.IsNE b1 1 σ1 σ2 →
      ∀ b2 : ℕ, 1 ≤ b2 → b2 < G.mStar →
        ∃ σ2' : Act E b2 → ℝ, G.IsNE b1 b2 σ1 σ2') := by
  change DetectionRateConclusion G b1
  by_cases hm : G.mStar ≤ 1
  · exact theorem_2_vacuous G b1 hm
  by_cases hz : b1 = 0
  · subst b1
    exact theorem_2_zero G
  by_cases hc : G.nStar ≤ b1
  · exact theorem_2_cover G hc
  exact theorem_2_intermediate G (by omega) (by omega)

end NetInspect.Rate




namespace NetInspect.Rate
open Finset DetectionModel BlottoLP.Flow
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

private lemma pure_mixed {A : Type*} [Fintype A] [DecidableEq A] (a : A) :
    IsMixed (pureMixed a) := by
  constructor
  · intro x; simp only [pureMixed]; split_ifs <;> norm_num
  · simp [pureMixed]

 theorem equilibrium_U_pos (G : DetectionModel V E) {b1 b2 : ℕ}
    (hb1 : b1 < G.nStar) (hb2 : 1 ≤ b2) (hb2m : b2 < G.mStar)
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ) (hne : G.IsNE b1 b2 σ1 σ2) :
    0 < G.U σ1 σ2 := by
  letI : Nonempty (Act V b1) := ⟨⟨∅, by simp⟩⟩
  letI : Nonempty (Act E 1) := ⟨⟨∅, by simp⟩⟩
  obtain ⟨τ2, τ1, hτ⟩ := exists_isNashEq (G.payoff b1 1)
  have ht : 0 < G.U τ1 τ2 := equilibrium_U_pos_of_lt_nStar G hb1 τ1 τ2 hτ
  rw [← gameValue_eq_U_of_NE G σ1 σ2 hne, eq_18 G hb1 hb2 hb2m,
    gameValue_eq_U_of_NE G τ1 τ2 hτ]
  exact mul_pos (by exact_mod_cast (show 0 < b2 by omega)) ht

 theorem equilibrium_attack_full (G : DetectionModel V E) {b1 b2 : ℕ}
    (hb1 : b1 < G.nStar) (hb2 : 1 ≤ b2) (hb2m : b2 < G.mStar)
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ) (hne : G.IsNE b1 b2 σ1 σ2) :
    ∀ T, 0 < σ2 T → T.1.card = b2 := by
  classical
  have hm : 1 < G.mStar := hb2.trans_lt hb2m
  letI : Nonempty E := Fintype.card_pos_iff.mp
    (lt_of_lt_of_le (by omega : 0 < G.mStar) (mStar_le_card G))
  letI : Nonempty (Act V b1) := ⟨⟨∅, by simp⟩⟩
  letI : Nonempty (Act E 1) := ⟨⟨∅, by simp⟩⟩
  obtain ⟨τ2, τ1, hbase⟩ := exists_isNashEq (G.payoff b1 1)
  obtain ⟨p, τ, hp, hcap, href, hmarg⟩ := capped_equilibrium_for_defender G hb1 hm τ1 τ2 hbase
  obtain ⟨τscaled, hs, hval, hmiss⟩ := scale_capped_equilibrium G τ1 τ href p hp hmarg hcap hb2 hb2m
  have hcross : G.IsNE b1 b2 τ1 σ2 := hne.cross hs
  have hu : G.U τ1 σ2 = (b2 : ℝ) * G.U τ1 τ := (hcross.expPay_eq hs).trans hval
  exact support_card_eq_of_payoff_eq G τ1 σ2 hne.1 _
    (equilibrium_U_pos_of_lt_nStar G hb1 τ1 τ href) hmiss hu

 theorem equilibrium_defender_pure_value (G : DetectionModel V E) {b1 b2 : ℕ}
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ) (hne : G.IsNE b1 b2 σ1 σ2)
    (S : Act V b1) (hS : 0 < σ1 S) : G.U (pureMixed S) σ2 = G.U σ1 σ2 := by
  classical
  have hlo (X : Act V b1) : G.U σ1 σ2 ≤ G.U (pureMixed X) σ2 :=
    hne.2.2.2 _ (pure_mixed X)
  have heq : ∑ X, σ1 X * G.U (pureMixed X) σ2 = G.U σ1 σ2 :=
    (expPay_eq_sum_pure_right (G.payoff b1 b2) σ2 σ1).symm
  have hz : ∑ X, σ1 X * (G.U (pureMixed X) σ2 - G.U σ1 σ2) = 0 := by
    simp_rw [mul_sub]
    rw [sum_sub_distrib, heq, ← sum_mul, hne.2.1.2, one_mul, sub_self]
  have hn X : 0 ≤ σ1 X * (G.U (pureMixed X) σ2 - G.U σ1 σ2) :=
    mul_nonneg (hne.2.1.1 X) (sub_nonneg.mpr (hlo X))
  have ht := (sum_eq_zero_iff_of_nonneg fun X _ => hn X).mp hz S (mem_univ _)
  have hh := (mul_eq_zero.mp ht).resolve_left hS.ne'
  linarith

 theorem equilibrium_defender_full (G : DetectionModel V E) {b1 b2 : ℕ}
    (hb1 : b1 < G.nStar) (hb2 : 1 ≤ b2) (hb2m : b2 < G.mStar)
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ) (hne : G.IsNE b1 b2 σ1 σ2) :
    ∀ S, 0 < σ1 S → S.1.card = b1 := by
  classical
  intro S hS
  by_contra hcard
  have hlt : S.1.card < b1 := lt_of_le_of_ne S.2 hcard
  have hv := equilibrium_defender_pure_value G σ1 σ2 hne S hS
  have hpos : 0 < ∑ e, marg σ2 e * (if e ∈ G.CS S.1 then (0 : ℝ) else 1) := by
    rw [← U_pure_eq_marg_sum, hv]
    exact equilibrium_U_pos G hb1 hb2 hb2m σ1 σ2 hne
  have hex : ∃ e : E, 0 < marg σ2 e * (if e ∈ G.CS S.1 then (0 : ℝ) else 1) := by
    by_contra h
    have hh e : marg σ2 e * (if e ∈ G.CS S.1 then (0 : ℝ) else 1) ≤ 0 :=
      le_of_not_gt (fun he => h ⟨e, he⟩)
    exact (not_le_of_gt hpos) (sum_nonpos fun e _ => hh e)
  obtain ⟨e, he⟩ := hex
  have heout : e ∉ G.CS S.1 := by intro h; simp [h] at he
  have hem : 0 < marg σ2 e := by simpa [heout] using he
  obtain ⟨i, hi⟩ := G.coverable e
  let X : Act V b1 := ⟨insert i S.1, (card_insert_le i S.1).trans (by omega)⟩
  have hsub : G.CS S.1 ⊆ G.CS X.1 := by
    intro f hf
    obtain ⟨j, hj, hf⟩ := mem_biUnion.mp hf
    exact mem_biUnion.mpr ⟨j, mem_insert_of_mem hj, hf⟩
  have hei : e ∈ G.CS X.1 := mem_biUnion.mpr ⟨i, mem_insert_self _ _, hi⟩
  have hstrict : G.U (pureMixed X) σ2 < G.U (pureMixed S) σ2 := by
    rw [U_pure_eq_marg_sum, U_pure_eq_marg_sum]
    apply sum_lt_sum
    · intro f _
      have hn := marg_nonneg_of_mixed σ2 hne.1 f
      by_cases ha : f ∈ G.CS S.1
      · simp [ha, hsub ha]
      · by_cases hx : f ∈ G.CS X.1 <;> simp [ha, hx, hn]
    · exact ⟨e, mem_univ _, by simpa [hei, heout] using hem⟩
  have hbest := hne.2.2.2 (pureMixed X) (pure_mixed X)
  change G.U σ1 σ2 ≤ G.U (pureMixed X) σ2 at hbest
  rw [← hv] at hbest
  exact (not_le_of_gt hstrict) hbest

 def exactIncl {A : Type*} {b : ℕ} (X : ActEx A b) : Act A b := ⟨X.1, X.2.le⟩

 theorem exactIncl_injective {A : Type*} {b : ℕ} : Function.Injective (@exactIncl A b) := by
  intro X Y h
  apply Subtype.ext
  exact congrArg (fun X : Act A b => X.1) h

 theorem sum_exact_of_support {A : Type*} [Fintype A] [DecidableEq A] {b : ℕ}
    (f : Act A b → ℝ) (hf : ∀ X, X.1.card ≠ b → f X = 0) :
    ∑ X, f X = ∑ X : ActEx A b, f (exactIncl X) := by
  symm
  apply Fintype.sum_of_injective exactIncl exactIncl_injective _ _ _ (fun _ => rfl)
  intro X hX
  apply hf
  intro hc
  exact hX ⟨⟨X.1, hc⟩, Subtype.ext rfl⟩

 noncomputable def extendEx {A : Type*} {b : ℕ} (σ : ActEx A b → ℝ) : Act A b → ℝ :=
  fun X => if h : X.1.card = b then σ ⟨X.1, h⟩ else 0

 @[simp] theorem extendEx_exact {A : Type*} {b : ℕ} (σ : ActEx A b → ℝ) (X : ActEx A b) :
    extendEx σ (exactIncl X) = σ X := by simp [extendEx, exactIncl, X.2]

 theorem extendEx_zero {A : Type*} {b : ℕ} (σ : ActEx A b → ℝ) (X : Act A b)
    (h : X.1.card ≠ b) : extendEx σ X = 0 := by simp [extendEx, h]

 theorem extendEx_mixed {A : Type*} [Fintype A] [DecidableEq A] {b : ℕ}
    (σ : ActEx A b → ℝ) (hσ : IsMixed σ) : IsMixed (extendEx σ) := by
  classical
  constructor
  · intro X; dsimp [extendEx]; split_ifs <;> simp [hσ.1]
  · rw [sum_exact_of_support _ (extendEx_zero σ)]
    simpa using hσ.2

 theorem restrictEx_mixed {A : Type*} [Fintype A] [DecidableEq A] {b : ℕ}
    (σ : Act A b → ℝ) (hσ : IsMixed σ)
    (hs : ∀ X, X.1.card ≠ b → σ X = 0) : IsMixed (restrictEx σ) := by
  refine ⟨fun X => hσ.1 _, ?_⟩
  have hn := hσ.2
  rw [sum_exact_of_support σ hs] at hn
  exact hn

 theorem extend_restrictEx {A : Type*} {b : ℕ} (σ : Act A b → ℝ)
    (hs : ∀ X, X.1.card ≠ b → σ X = 0) : extendEx (restrictEx σ) = σ := by
  funext X
  dsimp [extendEx, restrictEx]
  split_ifs with h
  · rfl
  · exact (hs X h).symm

 theorem expPay_extendEx (G : DetectionModel V E) {b1 b2 : ℕ}
    (σ1 : ActEx V b1 → ℝ) (σ2 : ActEx E b2 → ℝ) :
    G.U (extendEx σ1) (extendEx σ2) = expPay (G.payoffEx b1 b2) σ2 σ1 := by
  classical
  unfold U expPay
  rw [sum_exact_of_support _ (fun X h => by simp [extendEx_zero σ2 X h])]
  apply sum_congr rfl
  intro T _
  rw [sum_exact_of_support _ (fun X h => by simp [extendEx_zero σ1 X h])]
  simp only [extendEx_exact]
  rfl

 theorem support_zero_of_full {A : Type*} [Fintype A] [DecidableEq A] {b : ℕ}
    (σ : Act A b → ℝ) (hσ : IsMixed σ) (hfull : ∀ X, 0 < σ X → X.1.card = b) :
    ∀ X, X.1.card ≠ b → σ X = 0 := by
  intro X hx
  exact le_antisymm (le_of_not_gt (fun h => hx (hfull X h))) (hσ.1 X)

 theorem U_restrictEx (G : DetectionModel V E) {b1 b2 : ℕ}
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ)
    (h1 : ∀ X, X.1.card ≠ b1 → σ1 X = 0) (h2 : ∀ X, X.1.card ≠ b2 → σ2 X = 0) :
    expPay (G.payoffEx b1 b2) (restrictEx σ2) (restrictEx σ1) = G.U σ1 σ2 := by
  rw [← expPay_extendEx, extend_restrictEx σ1 h1, extend_restrictEx σ2 h2]

 theorem U_extend_pure_attack (G : DetectionModel V E) {b1 b2 : ℕ}
    (σ1 : ActEx V b1 → ℝ) (T : ActEx E b2) :
    G.U (extendEx σ1) (pureMixed (exactIncl T)) =
      expPay (G.payoffEx b1 b2) (pureMixed T) σ1 := by
  classical
  simp only [U, expPay, mul_assoc, ← mul_sum]
  simp only [pureMixed, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]
  rw [sum_exact_of_support _ (fun X h => by simp [extendEx_zero σ1 X h])]
  simp only [extendEx_exact]
  rfl

 theorem U_extend_pure_defender (G : DetectionModel V E) {b1 b2 : ℕ}
    (σ2 : ActEx E b2 → ℝ) (S : ActEx V b1) :
    G.U (pureMixed (exactIncl S)) (extendEx σ2) =
      expPay (G.payoffEx b1 b2) σ2 (pureMixed S) := by
  classical
  simp only [U, expPay, pureMixed, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    sum_ite_eq', sum_ite_eq, mem_univ, ↓reduceIte]
  rw [sum_exact_of_support _ (fun X h => by simp [extendEx_zero σ2 X h])]
  simp only [extendEx_exact]
  rfl

 theorem bar_payoff_le_worst (G : DetectionModel V E) {b1 b2 : ℕ}
    (σ1 : ActEx V b1 → ℝ) (σ2 : ActEx E b2 → ℝ) (h2 : IsMixed σ2) :
    expPay (G.payoffEx b1 b2) σ2 σ1 ≤ G.worst1Ex b2 σ1 := by
  apply expPay_le_of_pure_left _ h2
  intro T
  exact le_csSup (Set.finite_range (fun X : ActEx E b2 =>
    expPay (G.payoffEx b1 b2) (pureMixed X) σ1)).bddAbove (Set.mem_range_self T)

 theorem bar_best_le_payoff (G : DetectionModel V E) {b1 b2 : ℕ}
    (σ1 : ActEx V b1 → ℝ) (σ2 : ActEx E b2 → ℝ) (h1 : IsMixed σ1) :
    G.best2Ex b1 σ2 ≤ expPay (G.payoffEx b1 b2) σ2 σ1 := by
  apply le_expPay_of_pure_right _ _ h1
  intro S
  exact csInf_le (Set.finite_range (fun X : ActEx V b1 =>
    expPay (G.payoffEx b1 b2) σ2 (pureMixed X))).bddBelow (Set.mem_range_self S)

 theorem bar_objectives_of_NE (G : DetectionModel V E) {b1 b2 : ℕ}
    [Nonempty (ActEx V b1)] [Nonempty (ActEx E b2)]
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ) (hne : G.IsNE b1 b2 σ1 σ2)
    (h1 : ∀ X, X.1.card ≠ b1 → σ1 X = 0) (h2 : ∀ X, X.1.card ≠ b2 → σ2 X = 0) :
    G.worst1Ex b2 (restrictEx σ1) = G.U σ1 σ2 ∧
      G.best2Ex b1 (restrictEx σ2) = G.U σ1 σ2 := by
  have hr1 := restrictEx_mixed σ1 hne.2.1 h1
  have hr2 := restrictEx_mixed σ2 hne.1 h2
  have hu := U_restrictEx G σ1 σ2 h1 h2
  constructor
  · apply le_antisymm
    · apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨T, rfl⟩
      change expPay (G.payoffEx b1 b2) (pureMixed T) (restrictEx σ1) ≤ G.U σ1 σ2
      rw [← U_extend_pure_attack, extend_restrictEx σ1 h1]
      exact hne.2.2.1 _ (pure_mixed _)
    · rw [← hu]
      exact bar_payoff_le_worst G _ _ hr2
  · apply le_antisymm
    · rw [← hu]
      exact bar_best_le_payoff G _ _ hr1
    · apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨S, rfl⟩
      change G.U σ1 σ2 ≤ expPay (G.payoffEx b1 b2) (restrictEx σ2) (pureMixed S)
      rw [← U_extend_pure_defender, extend_restrictEx σ2 h2]
      exact hne.2.2.2 _ (pure_mixed _)

 theorem bar_opt_of_NE (G : DetectionModel V E) {b1 b2 : ℕ}
    [Nonempty (ActEx V b1)] [Nonempty (ActEx E b2)]
    (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ) (hne : G.IsNE b1 b2 σ1 σ2)
    (h1 : ∀ X, X.1.card ≠ b1 → σ1 X = 0) (h2 : ∀ X, X.1.card ≠ b2 → σ2 X = 0) :
    G.IsOptLP1bar b1 b2 (restrictEx σ1) ∧ G.IsOptLP2bar b1 b2 (restrictEx σ2) := by
  obtain ⟨hv1, hv2⟩ := bar_objectives_of_NE G σ1 σ2 hne h1 h2
  have hr1 := restrictEx_mixed σ1 hne.2.1 h1
  have hr2 := restrictEx_mixed σ2 hne.1 h2
  constructor
  · refine ⟨hr1, ?_⟩
    intro τ hτ
    rw [hv1]
    have hh := hne.2.2.2 (extendEx τ) (extendEx_mixed τ hτ)
    change G.U σ1 σ2 ≤ G.U (extendEx τ) σ2 at hh
    calc
      _ ≤ G.U (extendEx τ) σ2 := hh
      _ = expPay (G.payoffEx b1 b2) (restrictEx σ2) τ := by
        conv_lhs => rw [← extend_restrictEx σ2 h2]
        exact expPay_extendEx G τ (restrictEx σ2)
      _ ≤ _ := bar_payoff_le_worst G τ _ hr2
  · refine ⟨hr2, ?_⟩
    intro τ hτ
    rw [hv2]
    have hh := hne.2.2.1 (extendEx τ) (extendEx_mixed τ hτ)
    change G.U σ1 (extendEx τ) ≤ G.U σ1 σ2 at hh
    calc
      _ ≤ expPay (G.payoffEx b1 b2) τ (restrictEx σ1) := bar_best_le_payoff G _ τ hr1
      _ = G.U σ1 (extendEx τ) := by
        conv_rhs => rw [← extend_restrictEx σ1 h1]
        exact (expPay_extendEx G (restrictEx σ1) τ).symm
      _ ≤ _ := hh

 theorem mixed_of_restrictEx {A : Type*} [Fintype A] [DecidableEq A] {b : ℕ}
    (σ : Act A b → ℝ) (hs : ∀ X, X.1.card ≠ b → σ X = 0)
    (hr : IsMixed (restrictEx σ)) : IsMixed σ := by
  rw [← extend_restrictEx σ hs]
  exact extendEx_mixed _ hr

 theorem undet_mono_attack (G : DetectionModel V E) (S : Finset V) {T T' : Finset E}
    (h : T ⊆ T') : G.undet S T ≤ G.undet S T' := by
  rw [undet_eq_sum, undet_eq_sum]
  apply sum_le_sum_of_subset_of_nonneg h
  intro e _ _
  split_ifs <;> norm_num

 theorem undet_antitone_defender (G : DetectionModel V E) {S S' : Finset V}
    (h : S ⊆ S') (T : Finset E) : G.undet S' T ≤ G.undet S T := by
  have hCS : G.CS S ⊆ G.CS S' := by
    intro e he
    obtain ⟨i, hi, hie⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨i, h hi, hie⟩
  rw [undet_eq_sum, undet_eq_sum]
  apply sum_le_sum
  intro e _
  by_cases he : e ∈ G.CS S
  · simp [he, hCS he]
  · split_ifs <;> norm_num

 theorem U_pure_attack_mono (G : DetectionModel V E) {b1 b2 : ℕ}
    (σ1 : Act V b1 → ℝ) (hσ : IsMixed σ1) (T T' : Act E b2) (h : T.1 ⊆ T'.1) :
    G.U σ1 (pureMixed T) ≤ G.U σ1 (pureMixed T') := by
  classical
  simp only [U, expPay, mul_assoc, ← mul_sum]
  simp only [pureMixed, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]
  apply sum_le_sum
  intro S _
  exact mul_le_mul_of_nonneg_left (undet_mono_attack G S.1 h) (hσ.1 S)

 theorem U_pure_defender_antitone (G : DetectionModel V E) {b1 b2 : ℕ}
    (σ2 : Act E b2 → ℝ) (hσ : IsMixed σ2) (S S' : Act V b1) (h : S.1 ⊆ S'.1) :
    G.U (pureMixed S') σ2 ≤ G.U (pureMixed S) σ2 := by
  classical
  simp only [U, expPay, pureMixed, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    sum_ite_eq', mem_univ, ↓reduceIte]
  apply sum_le_sum
  intro T _
  exact mul_le_mul_of_nonneg_left (undet_antitone_defender G h T.1) (hσ.1 T)

 theorem full_payoff_le_bar_worst (G : DetectionModel V E) {b1 b2 : ℕ}
    (hb : b2 ≤ Fintype.card E) (σ1 : Act V b1 → ℝ) (hσ : IsMixed σ1)
    (hs : ∀ X, X.1.card ≠ b1 → σ1 X = 0) (τ2 : Act E b2 → ℝ) (hτ : IsMixed τ2) :
    G.U σ1 τ2 ≤ G.worst1Ex b2 (restrictEx σ1) := by
  apply expPay_le_of_pure_left _ hτ
  intro T
  obtain ⟨T', hTT', _, hc⟩ := exists_subsuperset_card_eq (subset_univ T.1) T.2 (by simpa using hb)
  let X : ActEx E b2 := ⟨T', hc⟩
  calc
    _ ≤ G.U σ1 (pureMixed (exactIncl X)) := U_pure_attack_mono G σ1 hσ T _ hTT'
    _ = expPay (G.payoffEx b1 b2) (pureMixed X) (restrictEx σ1) := by
      conv_lhs => rw [← extend_restrictEx σ1 hs]
      exact U_extend_pure_attack G _ X
    _ ≤ _ := le_csSup (Set.finite_range (fun X : ActEx E b2 =>
      expPay (G.payoffEx b1 b2) (pureMixed X) (restrictEx σ1))).bddAbove (Set.mem_range_self X)

 theorem bar_best_le_full_payoff (G : DetectionModel V E) {b1 b2 : ℕ}
    (hb : b1 ≤ Fintype.card V) (σ2 : Act E b2 → ℝ) (hσ : IsMixed σ2)
    (hs : ∀ X, X.1.card ≠ b2 → σ2 X = 0) (τ1 : Act V b1 → ℝ) (hτ : IsMixed τ1) :
    G.best2Ex b1 (restrictEx σ2) ≤ G.U τ1 σ2 := by
  apply le_expPay_of_pure_right _ _ hτ
  intro S
  obtain ⟨S', hSS', _, hc⟩ := exists_subsuperset_card_eq (subset_univ S.1) S.2 (by simpa using hb)
  let X : ActEx V b1 := ⟨S', hc⟩
  calc
    _ ≤ expPay (G.payoffEx b1 b2) (restrictEx σ2) (pureMixed X) :=
      csInf_le (Set.finite_range (fun X : ActEx V b1 =>
        expPay (G.payoffEx b1 b2) (restrictEx σ2) (pureMixed X))).bddBelow (Set.mem_range_self X)
    _ = G.U (pureMixed (exactIncl X)) σ2 := by
      conv_rhs => rw [← extend_restrictEx σ2 hs]
      exact (U_extend_pure_defender G _ X).symm
    _ ≤ _ := U_pure_defender_antitone G σ2 hσ S _ hSS'

 theorem NE_of_bar_defender_opt (G : DetectionModel V E) {b1 b2 : ℕ}
    [Nonempty (ActEx V b1)] [Nonempty (ActEx E b2)] (hb : b2 ≤ Fintype.card E)
    (σ1 : Act V b1 → ℝ) (hs : ∀ X, X.1.card ≠ b1 → σ1 X = 0)
    (hopt : G.IsOptLP1bar b1 b2 (restrictEx σ1))
    (ρ1 : Act V b1 → ℝ) (ρ2 : Act E b2 → ℝ) (href : G.IsNE b1 b2 ρ1 ρ2)
    (hr1 : ∀ X, X.1.card ≠ b1 → ρ1 X = 0) (hr2 : ∀ X, X.1.card ≠ b2 → ρ2 X = 0) :
    G.IsNE b1 b2 σ1 ρ2 := by
  have hσ := mixed_of_restrictEx σ1 hs hopt.1
  have hval := (bar_objectives_of_NE G ρ1 ρ2 href hr1 hr2).1
  have hupper (τ : Act E b2 → ℝ) (hτ : IsMixed τ) : G.U σ1 τ ≤ G.U ρ1 ρ2 := by
    calc
      _ ≤ G.worst1Ex b2 (restrictEx σ1) := full_payoff_le_bar_worst G hb σ1 hσ hs τ hτ
      _ ≤ G.worst1Ex b2 (restrictEx ρ1) := hopt.2 _ (restrictEx_mixed ρ1 href.2.1 hr1)
      _ = _ := hval
  have heq : G.U σ1 ρ2 = G.U ρ1 ρ2 := le_antisymm (hupper ρ2 href.1) (href.2.2.2 σ1 hσ)
  refine ⟨href.1, hσ, ?_, ?_⟩
  · intro τ hτ
    change G.U σ1 τ ≤ G.U σ1 ρ2
    rw [heq]
    exact hupper τ hτ
  · intro τ hτ
    change G.U σ1 ρ2 ≤ G.U τ ρ2
    rw [heq]
    exact href.2.2.2 τ hτ

 theorem NE_of_bar_attacker_opt (G : DetectionModel V E) {b1 b2 : ℕ}
    [Nonempty (ActEx V b1)] [Nonempty (ActEx E b2)] (hb : b1 ≤ Fintype.card V)
    (σ2 : Act E b2 → ℝ) (hs : ∀ X, X.1.card ≠ b2 → σ2 X = 0)
    (hopt : G.IsOptLP2bar b1 b2 (restrictEx σ2))
    (ρ1 : Act V b1 → ℝ) (ρ2 : Act E b2 → ℝ) (href : G.IsNE b1 b2 ρ1 ρ2)
    (hr1 : ∀ X, X.1.card ≠ b1 → ρ1 X = 0) (hr2 : ∀ X, X.1.card ≠ b2 → ρ2 X = 0) :
    G.IsNE b1 b2 ρ1 σ2 := by
  have hσ := mixed_of_restrictEx σ2 hs hopt.1
  have hval := (bar_objectives_of_NE G ρ1 ρ2 href hr1 hr2).2
  have hlower (τ : Act V b1 → ℝ) (hτ : IsMixed τ) : G.U ρ1 ρ2 ≤ G.U τ σ2 := by
    calc
      _ = G.best2Ex b1 (restrictEx ρ2) := hval.symm
      _ ≤ G.best2Ex b1 (restrictEx σ2) := hopt.2 _ (restrictEx_mixed ρ2 href.1 hr2)
      _ ≤ _ := bar_best_le_full_payoff G hb σ2 hσ hs τ hτ
  have heq : G.U ρ1 σ2 = G.U ρ1 ρ2 := le_antisymm (href.2.2.1 σ2 hσ) (hlower ρ1 href.2.1)
  refine ⟨hσ, href.2.1, ?_, ?_⟩
  · intro τ hτ
    change G.U ρ1 τ ≤ G.U ρ1 σ2
    rw [heq]
    exact href.2.2.1 τ hτ
  · intro τ hτ
    change G.U ρ1 σ2 ≤ G.U τ σ2
    rw [heq]
    exact hlower τ hτ

 theorem theorem_1 (G : DetectionModel V E)
    {b1 b2 : ℕ} (hb1 : b1 < G.nStar) (hb2 : 1 ≤ b2) (hb2m : b2 < G.mStar) :
    (∀ (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ), G.IsNE b1 b2 σ1 σ2 →
      (∀ S : Act V b1, 0 < σ1 S → S.1.card = b1) ∧
      (∀ T : Act E b2, 0 < σ2 T → T.1.card = b2)) ∧
    (∀ σ1 : Act V b1 → ℝ, (∃ σ2 : Act E b2 → ℝ, G.IsNE b1 b2 σ1 σ2) ↔
      ((∀ S : Act V b1, S.1.card ≠ b1 → σ1 S = 0) ∧ G.IsOptLP1bar b1 b2 (restrictEx σ1))) ∧
    (∀ σ2 : Act E b2 → ℝ, (∃ σ1 : Act V b1 → ℝ, G.IsNE b1 b2 σ1 σ2) ↔
      ((∀ T : Act E b2, T.1.card ≠ b2 → σ2 T = 0) ∧ G.IsOptLP2bar b1 b2 (restrictEx σ2))) := by
  classical
  have hncard : G.nStar ≤ Fintype.card V := by
    apply Nat.sInf_le
    refine ⟨univ, by simp, ?_⟩
    intro e
    obtain ⟨i, hi⟩ := G.coverable e
    have he : e ∈ G.CS univ := mem_biUnion.mpr ⟨i, mem_univ _, hi⟩
    simp [F, he]
  have hcard1 : b1 ≤ Fintype.card V := hb1.le.trans hncard
  have hcard2 : b2 ≤ Fintype.card E := hb2m.le.trans (mStar_le_card G)
  obtain ⟨S, _, hS⟩ := exists_subset_card_eq (s := (univ : Finset V)) (by simpa using hcard1)
  obtain ⟨T, _, hT⟩ := exists_subset_card_eq (s := (univ : Finset E)) (by simpa using hcard2)
  letI : Nonempty (ActEx V b1) := ⟨⟨S, hS⟩⟩
  letI : Nonempty (ActEx E b2) := ⟨⟨T, hT⟩⟩
  letI : Nonempty (Act V b1) := ⟨⟨∅, by simp⟩⟩
  letI : Nonempty (Act E b2) := ⟨⟨∅, by simp⟩⟩
  obtain ⟨ρ2, ρ1, href⟩ := exists_isNashEq (G.payoff b1 b2)
  have hz1 := support_zero_of_full ρ1 href.2.1 (equilibrium_defender_full G hb1 hb2 hb2m ρ1 ρ2 href)
  have hz2 := support_zero_of_full ρ2 href.1 (equilibrium_attack_full G hb1 hb2 hb2m ρ1 ρ2 href)
  refine ⟨?_, ?_, ?_⟩
  · intro σ1 σ2 hne
    exact ⟨equilibrium_defender_full G hb1 hb2 hb2m σ1 σ2 hne,
      equilibrium_attack_full G hb1 hb2 hb2m σ1 σ2 hne⟩
  · intro σ1
    constructor
    · rintro ⟨σ2, hne⟩
      have h1 := support_zero_of_full σ1 hne.2.1 (equilibrium_defender_full G hb1 hb2 hb2m σ1 σ2 hne)
      have h2 := support_zero_of_full σ2 hne.1 (equilibrium_attack_full G hb1 hb2 hb2m σ1 σ2 hne)
      exact ⟨h1, (bar_opt_of_NE G σ1 σ2 hne h1 h2).1⟩
    · rintro ⟨hs, hopt⟩
      exact ⟨ρ2, NE_of_bar_defender_opt G hcard2 σ1 hs hopt ρ1 ρ2 href hz1 hz2⟩
  · intro σ2
    constructor
    · rintro ⟨σ1, hne⟩
      have h1 := support_zero_of_full σ1 hne.2.1 (equilibrium_defender_full G hb1 hb2 hb2m σ1 σ2 hne)
      have h2 := support_zero_of_full σ2 hne.1 (equilibrium_attack_full G hb1 hb2 hb2m σ1 σ2 hne)
      exact ⟨h2, (bar_opt_of_NE G σ1 σ2 hne h1 h2).2⟩
    · rintro ⟨hs, hopt⟩
      exact ⟨ρ1, NE_of_bar_attacker_opt G hcard1 σ2 hs hopt ρ1 ρ2 href hz1 hz2⟩

end NetInspect.Rate







open NetInspect.Rate NetInspect.Rate.DetectionModel Finset

theorem solution {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DetectionModel V E)
    {b1 b2 : ℕ} (hb1 : b1 < G.nStar) (hb2 : 1 ≤ b2) (hb2m : b2 < G.mStar) :
    (∀ (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ), G.IsNE b1 b2 σ1 σ2 →
      (∀ S : Act V b1, 0 < σ1 S → S.1.card = b1) ∧
      (∀ T : Act E b2, 0 < σ2 T → T.1.card = b2)) ∧
    (∀ σ1 : Act V b1 → ℝ, (∃ σ2 : Act E b2 → ℝ, G.IsNE b1 b2 σ1 σ2) ↔
      ((∀ S : Act V b1, S.1.card ≠ b1 → σ1 S = 0) ∧ G.IsOptLP1bar b1 b2 (restrictEx σ1))) ∧
    (∀ σ2 : Act E b2 → ℝ, (∃ σ1 : Act V b1 → ℝ, G.IsNE b1 b2 σ1 σ2) ↔
      ((∀ T : Act E b2, T.1.card ≠ b2 → σ2 T = 0) ∧ G.IsOptLP2bar b1 b2 (restrictEx σ2))) := by
  exact NetInspect.Rate.theorem_1 G hb1 hb2 hb2m

#print axioms solution
