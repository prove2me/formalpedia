-- Prove2me | solution 1 for NetInspect.Rate.theorem_2_step_ia
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-28T06:05:16.818544+00:00
-- url     : https://prove2.me/submissions/b286782b-6059-486d-adb0-126be6e4772b

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

open NetInspect.Rate NetInspect.Rate.DetectionModel Finset

theorem solution {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DetectionModel V E)
    {b1 : ℕ} (hb1 : b1 < G.nStar) (hm : 1 < G.mStar) :
    ∃ σ2 : ActEx E 1 → ℝ, G.IsOptLP2bar b1 1 σ2 ∧
      ∀ e : E, marg σ2 e ≤ 1 / (G.mStar : ℝ) := by
  exact NetInspect.Rate.theorem_2_step_ia G hb1 hm

#print axioms solution
