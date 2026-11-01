-- Prove2me | solution 1 for MDPComplexity.PartiallyObserved.theorem6_reduction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T12:15:15.535961+00:00
-- url     : https://prove2.me/submissions/2eed09d6-81e3-4b6e-9f61-c21f799cc20d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MDPComplexity_PartiallyObserved_Model
import Definitions.Def_MDPComplexity_PartiallyObserved_QSAT
import Definitions.Def_MDPComplexity_PartiallyObserved_Construction
import Theorems.Thm_MDPComplexity_PartiallyObserved_holds_imp_zero_cost
import Theorems.Thm_MDPComplexity_PartiallyObserved_zero_cost_imp_holds

open MDPComplexity.PartiallyObserved

private def injSt {n m : ℕ} (hm : 0 < m) :
    Option (Option (Option (Fin n ⊕ Fin n))) → St n m
  | none => .s0
  | some none => .sink
  | some (some none) => .Aend ⟨0, hm⟩
  | some (some (some (Sum.inl j))) => .A ⟨0, hm⟩ j
  | some (some (some (Sum.inr j))) => .A' ⟨0, hm⟩ j

private lemma injSt_injective {n m : ℕ} (hm : 0 < m) : Function.Injective (injSt (n := n) hm) := by
  rintro (_ | _ | _ | (j₁ | j₁)) (_ | _ | _ | (j₂ | j₂)) h <;>
    simp [injSt] at h ⊢ <;> exact h

private lemma expCost_nonneg {n m : ℕ} (φ : QBF n m) (hm : 0 < m)
    (π : (φ.toPOMDP hm).Policy) :
    0 ≤ (φ.toPOMDP hm).expCost .s0 π (horizon n) := by
  unfold POMDP.expCost
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg
  · unfold POMDP.trajProb
    apply mul_nonneg
    · split_ifs <;> norm_num
    · apply Finset.prod_nonneg
      intro t _
      exact ENNReal.toReal_nonneg
  · unfold POMDP.trajCost
    apply Finset.sum_nonneg
    intro t _
    have hcost : ∀ (z : Obs n m) (d : φ.Dec z), 0 ≤ φ.cost z d := by
      rintro (_ | _ | _ | _ | _ | _ | _ | _ | _) _ <;> simp [QBF.cost]
    exact hcost (St.obs (x t)) _

theorem solution {n m : ℕ} (φ : QBF n m) (hm : 0 < m)
    (hqsat : φ.IsPaperQSAT) :
    horizon n < Fintype.card (St n m) ∧
    ((∃ π : (φ.toPOMDP hm).Policy, (φ.toPOMDP hm).expCost .s0 π (horizon n) = 0) ↔ φ.holds) ∧
    ((φ.toPOMDP hm).optCost .s0 (horizon n) ≤ 0 ↔ φ.holds) := by
  have hcard : horizon n < Fintype.card (St n m) := by
    have hle := Fintype.card_le_of_injective (injSt (n := n) hm) (injSt_injective hm)
    simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_fin] at hle
    unfold horizon
    omega
  have heq : (∃ π : (φ.toPOMDP hm).Policy, (φ.toPOMDP hm).expCost .s0 π (horizon n) = 0) ↔ φ.holds := by
    constructor
    · rintro ⟨π, h0⟩
      exact zero_cost_imp_holds φ hm hqsat π h0
    · intro h
      exact holds_imp_zero_cost φ hm hqsat h
  refine ⟨hcard, heq, ?_⟩
  let M := φ.toPOMDP hm
  let T := horizon n
  let auxCost : ((x : Fin (T + 1) → St n m) → (t : Fin (T + 1)) → M.D (M.obs (x t))) → ℝ :=
    fun f => ∑ x : Fin (T + 1) → St n m,
      ((if x 0 = .s0 then 1 else 0) *
        ∏ t : Fin T, ((M.p (x t.castSucc) (f x t.castSucc)) (x t.succ)).toReal) *
      (∑ t : Fin (T + 1), M.c (M.obs (x t)) (f x t))
  have hsub : Set.range (fun π : M.Policy => M.expCost .s0 π T) ⊆ Set.range auxCost := by
    rintro _ ⟨π, rfl⟩
    exact ⟨fun x t => M.dec π x t, rfl⟩
  have hFin : (Set.range (fun π : M.Policy => M.expCost .s0 π T)).Finite :=
    (Set.finite_range auxCost).subset hsub
  haveI : Nonempty M.Policy := ⟨fun _ z => Classical.arbitrary (M.D z)⟩
  have hNe : (Set.range (fun π : M.Policy => M.expCost .s0 π T)).Nonempty :=
    Set.range_nonempty _
  constructor
  · intro hopt
    have hmem : M.optCost .s0 T ∈ Set.range (fun π : M.Policy => M.expCost .s0 π T) := by
      unfold POMDP.optCost iInf
      exact Set.Nonempty.csInf_mem hNe hFin
    rcases hmem with ⟨π₀, hπ₀⟩
    have hge : 0 ≤ M.expCost .s0 π₀ T := expCost_nonneg φ hm π₀
    have h0 : M.expCost .s0 π₀ T = 0 := by linarith
    exact heq.mp ⟨π₀, h0⟩
  · intro hholds
    rcases heq.mpr hholds with ⟨π₀, hπ₀⟩
    unfold POMDP.optCost iInf
    have hle : sInf (Set.range (fun π : M.Policy => M.expCost .s0 π T)) ≤ M.expCost .s0 π₀ T :=
      csInf_le hFin.bddBelow ⟨π₀, rfl⟩
    linarith
