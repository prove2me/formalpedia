-- Prove2me | solution 1 for MarkovEntanglement.weakly_coupled_entanglement_le_policy_mismatch
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-08-10T13:56:07.251595+00:00
-- url     : https://prove2.me/submissions/ae551b07-d465-48b6-bff2-6ca2df8d23ee

import Definitions.Def_markov_entanglement_policy
import Theorems.Thm_MarkovEntanglement_separable_apply_local_reward

open scoped BigOperators
open MarkovEntanglement

theorem solution
    {N : ℕ} {St Act : Fin N → Type*}
    [∀ i, Fintype (St i)] [∀ i, DecidableEq (St i)]
    [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    (P : JointState St → JointAction Act → JointState St → ℝ)
    (Pl : ∀ i, St i → Act i → St i → ℝ)
    (hPl : IsLocalKernel Pl) (hwc : IsWeaklyCoupled P Pl)
    (π : JointState St → JointAction Act → ℝ) (hπ : IsJointPolicy π)
    (μ : Joint (StateAction St Act) → ℝ) (hμ : IsPositiveDist μ)
    (hstat : IsStationary (inducedTransition P π) μ)
    (i : Fin N) (πl : St i → Act i → ℝ) (hπl : IsLocalPolicy πl) :
    entanglementN i μ (inducedTransition P π) ≤ policyMismatch i π μ πl := by
  classical
  set T := inducedTransition P π with hT
  set sp : Joint (StateAction St Act) → JointState St := fun p j => (p j).1 with hsp
  set ap : Joint (StateAction St Act) → JointAction Act := fun p j => (p j).2 with hap
  have hμ0 : ∀ p, 0 ≤ μ p := fun p => (hμ.1 p).le
  -- pinning one coordinate of a product kernel leaves that agent's kernel
  have hPabs : ∀ (s : JointState St) (a : JointAction Act) (s' : JointState St),
      0 ≤ P s a s' := by
    intro s a s'
    rw [hwc s a s']
    exact Finset.prod_nonneg (fun j _ => hPl.1 j (s j) (a j) (s' j))
  have hpin : ∀ (s : JointState St) (a : JointAction Act) (t : St i),
      ∑ s' : JointState St, (if s' i = t then P s a s' else 0) = Pl i (s i) (a i) t := by
    intro s a t
    have hA : ∀ j, IsTransitionMatrix (fun x y => Pl j x (a j) y : Matrix (St j) (St j) ℝ) :=
      fun j => ⟨fun x y => hPl.1 j x (a j) y, fun x => hPl.2 j x (a j)⟩
    have h := MarkovEntanglement.separable_apply_local_reward
      (S := St) (K := 1) (fun _ => (1:ℝ))
      (fun _ j => (fun x y => Pl j x (a j) y : Matrix (St j) (St j) ℝ))
      (fun _ j => hA j) (by simp) i (fun y => if y = t then (1:ℝ) else 0) s
    simp only [Fin.sum_univ_one, one_smul, one_mul] at h
    calc ∑ s' : JointState St, (if s' i = t then P s a s' else 0)
        = ∑ s' : JointState St, tensorProdN
            (fun j => (fun x y => Pl j x (a j) y : Matrix (St j) (St j) ℝ)) s s'
              * (if s' i = t then (1:ℝ) else 0) := by
          refine Finset.sum_congr rfl (fun s' _ => ?_)
          rw [hwc s a s']
          by_cases h1 : s' i = t <;> simp [h1, tensorProdN]
      _ = ∑ y : St i, Pl i (s i) (a i) y * (if y = t then (1:ℝ) else 0) := h
      _ = Pl i (s i) (a i) t := by simp
  -- the marginal of the induced transition onto agent `i`
  have hmarg : ∀ (p : Joint (StateAction St Act)) (y : St i × Act i),
      marginalN i T p y
        = ∑ s' : JointState St,
            (if s' i = y.1 then P (sp p) (ap p) s' * policyMarginal i π s' y.2 else 0) := by
    intro p y
    rw [marginalN]
    rw [← Equiv.sum_comp (splitStateAction (St := St) (Act := Act)).symm]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun s' _ => ?_)
    by_cases h1 : s' i = y.1
    · rw [if_pos h1, policyMarginal, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a' _ => ?_)
      by_cases h2 : a' i = y.2
      · have : ((splitStateAction (St := St) (Act := Act)).symm (s', a')) i = y := by
          simp [splitStateAction, h1, h2, Prod.ext_iff]
        rw [if_pos this, if_pos h2, hT, inducedTransition]
        rfl
      · have : ¬ (((splitStateAction (St := St) (Act := Act)).symm (s', a')) i = y) := by
          simp [splitStateAction, Prod.ext_iff]
          intro _; exact h2
        rw [if_neg this, if_neg h2, mul_zero]
    · rw [if_neg h1]
      refine Finset.sum_eq_zero (fun a' _ => ?_)
      refine if_neg ?_
      simp [splitStateAction, Prod.ext_iff]
      intro hc; exact absurd hc h1
  -- the occupancy state marginal is the pushforward of `μ` through `P`
  have hocc : ∀ s' : JointState St,
      occupancyStateMarginal μ s' = ∑ p, μ p * P (sp p) (ap p) s' := by
    intro s'
    rw [occupancyStateMarginal]
    calc ∑ q : Joint (StateAction St Act), (if (fun j => (q j).1) = s' then μ q else 0)
        = ∑ q : Joint (StateAction St Act),
            (if (fun j => (q j).1) = s' then (∑ p, μ p * T p q) else 0) := by
          refine Finset.sum_congr rfl (fun q _ => ?_)
          by_cases h1 : (fun j => (q j).1) = s'
          · rw [if_pos h1, if_pos h1, hstat q]
          · rw [if_neg h1, if_neg h1]
      _ = ∑ q : Joint (StateAction St Act), ∑ p,
            (if (fun j => (q j).1) = s' then μ p * T p q else 0) := by
          refine Finset.sum_congr rfl (fun q _ => ?_)
          by_cases h1 : (fun j => (q j).1) = s' <;> simp [h1]
      _ = ∑ p, ∑ q : Joint (StateAction St Act),
            (if (fun j => (q j).1) = s' then μ p * T p q else 0) := Finset.sum_comm
      _ = ∑ p, μ p * P (sp p) (ap p) s' := by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          have hin : ∑ q : Joint (StateAction St Act),
              (if (fun j => (q j).1) = s' then T p q else 0)
                = P (sp p) (ap p) s' := by
            rw [← Equiv.sum_comp (splitStateAction (St := St) (Act := Act)).symm]
            rw [Fintype.sum_prod_type]
            rw [Finset.sum_eq_single s']
            · have : ∑ a' : JointAction Act, T p ((splitStateAction).symm (s', a'))
                  = P (sp p) (ap p) s' * ∑ a' : JointAction Act, π s' a' := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl (fun a' _ => ?_)
                rw [hT, inducedTransition]
                rfl
              have hstrip : ∀ a' : JointAction Act,
                  (if (fun j => (((splitStateAction (St := St) (Act := Act)).symm
                        (s', a')) j).1) = s'
                   then T p ((splitStateAction (St := St) (Act := Act)).symm (s', a'))
                   else 0)
                  = T p ((splitStateAction (St := St) (Act := Act)).symm (s', a')) :=
                fun a' => if_pos rfl
              rw [Finset.sum_congr rfl (fun a' _ => hstrip a'), this, hπ.2 s', mul_one]
            · intro b _ hb
              refine Finset.sum_eq_zero (fun a' _ => ?_)
              refine if_neg ?_
              simpa [splitStateAction] using hb
            · intro h; exact absurd (Finset.mem_univ _) h
          calc ∑ q : Joint (StateAction St Act),
                (if (fun j => (q j).1) = s' then μ p * T p q else 0)
              = ∑ q : Joint (StateAction St Act),
                  μ p * (if (fun j => (q j).1) = s' then T p q else 0) := by
                refine Finset.sum_congr rfl (fun q _ => ?_)
                by_cases h1 : (fun j => (q j).1) = s' <;> simp [h1]
            _ = μ p * P (sp p) (ap p) s' := by rw [← Finset.mul_sum, hin]
  -- the candidate local transition: move with agent `i`'s kernel, then act with `πl`
  set Pcand : Matrix (St i × Act i) (St i × Act i) ℝ :=
    fun x y => Pl i x.1 x.2 y.1 * πl y.1 y.2 with hPcand
  have hPcandT : IsTransitionMatrix Pcand := by
    constructor
    · intro x y
      exact mul_nonneg (hPl.1 i x.1 x.2 y.1) (hπl.1 y.1 y.2)
    · intro x
      rw [Fintype.sum_prod_type]
      calc ∑ y1 : St i, ∑ y2 : Act i, Pl i x.1 x.2 y1 * πl y1 y2
          = ∑ y1 : St i, Pl i x.1 x.2 y1 := by
            refine Finset.sum_congr rfl (fun y1 _ => ?_)
            rw [← Finset.mul_sum, hπl.2 y1, mul_one]
        _ = 1 := hPl.2 i x.1 x.2
  have hnn : ∀ Pi : Matrix (St i × Act i) (St i × Act i) ℝ, 0 ≤ muAgentTVDistN i μ T Pi := by
    intro Pi
    refine Finset.sum_nonneg (fun p _ => mul_nonneg (hμ0 p) ?_)
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun t _ => abs_nonneg _))
  have hEle : entanglementN i μ T ≤ muAgentTVDistN i μ T Pcand := by
    refine csInf_le ⟨0, ?_⟩ ⟨Pcand, hPcandT, rfl⟩
    rintro x ⟨Pi, -, rfl⟩
    exact hnn Pi
  refine le_trans hEle ?_
  -- per joint state-action pair, the agent-wise deviation is a `P`-average of
  -- the policy deviation at the next state
  set D : JointState St → ℝ := fun s' =>
    ∑ a2 : Act i, |policyMarginal i π s' a2 - πl (s' i) a2| with hD
  have hper : ∀ p : Joint (StateAction St Act),
      ∑ y : St i × Act i, |marginalN i T p y - Pcand (p i) y|
        ≤ ∑ s' : JointState St, P (sp p) (ap p) s' * D s' := by
    intro p
    have hdiff : ∀ y : St i × Act i, marginalN i T p y - Pcand (p i) y
        = ∑ s' : JointState St, (if s' i = y.1 then
            P (sp p) (ap p) s' * (policyMarginal i π s' y.2 - πl (s' i) y.2) else 0) := by
      intro y
      rw [hmarg p y, hPcand]
      have h2 : (Pl i (p i).1 (p i).2 y.1) * πl y.1 y.2
          = ∑ s' : JointState St, (if s' i = y.1 then
              P (sp p) (ap p) s' * πl (s' i) y.2 else 0) := by
        rw [← hpin (sp p) (ap p) y.1, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun s' _ => ?_)
        by_cases h1 : s' i = y.1 <;> simp [h1]
      show _ - (Pl i (p i).1 (p i).2 y.1) * πl y.1 y.2 = _
      rw [h2, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun s' _ => ?_)
      by_cases h1 : s' i = y.1
      · simp only [if_pos h1]; ring
      · simp [h1]
    calc ∑ y : St i × Act i, |marginalN i T p y - Pcand (p i) y|
        ≤ ∑ y : St i × Act i, ∑ s' : JointState St, (if s' i = y.1 then
            P (sp p) (ap p) s' * |policyMarginal i π s' y.2 - πl (s' i) y.2| else 0) := by
          refine Finset.sum_le_sum (fun y _ => ?_)
          rw [hdiff y]
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun s' _ => ?_))
          by_cases h1 : s' i = y.1
          · rw [if_pos h1, if_pos h1, abs_mul, abs_of_nonneg (hPabs (sp p) (ap p) s')]
          · simp [h1]
      _ = ∑ s' : JointState St, P (sp p) (ap p) s' * D s' := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun s' _ => ?_)
          rw [hD, Finset.mul_sum, Fintype.sum_prod_type]
          rw [Finset.sum_eq_single (s' i)]
          · refine Finset.sum_congr rfl (fun a2 _ => by simp)
          · intro b _ hb
            exact Finset.sum_eq_zero (fun a2 _ => if_neg (Ne.symm hb))
          · intro h; exact absurd (Finset.mem_univ _) h
  have hfin : ∑ p, μ p * (∑ s' : JointState St, P (sp p) (ap p) s' * D s')
      = ∑ s' : JointState St, occupancyStateMarginal μ s' * D s' := by
    calc ∑ p, μ p * (∑ s' : JointState St, P (sp p) (ap p) s' * D s')
        = ∑ p, ∑ s' : JointState St, μ p * (P (sp p) (ap p) s' * D s') :=
          Finset.sum_congr rfl (fun p _ => Finset.mul_sum _ _ _)
      _ = ∑ s' : JointState St, ∑ p, μ p * (P (sp p) (ap p) s' * D s') := Finset.sum_comm
      _ = ∑ s' : JointState St, occupancyStateMarginal μ s' * D s' := by
          refine Finset.sum_congr rfl (fun s' _ => ?_)
          rw [hocc s', Finset.sum_mul]
          exact Finset.sum_congr rfl (fun p _ => by ring)
  calc muAgentTVDistN i μ T Pcand
      = ∑ p, μ p * ((1 / 2) * ∑ y : St i × Act i,
          |marginalN i T p y - Pcand (p i) y|) := rfl
    _ ≤ ∑ p, μ p * ((1 / 2) * ∑ s' : JointState St, P (sp p) (ap p) s' * D s') := by
        refine Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left ?_ (hμ0 p))
        exact mul_le_mul_of_nonneg_left (hper p) (by norm_num)
    _ = (1 / 2) * ∑ p, μ p * (∑ s' : JointState St, P (sp p) (ap p) s' * D s') := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun p _ => by ring)
    _ = (1 / 2) * ∑ s' : JointState St, occupancyStateMarginal μ s' * D s' := by rw [hfin]
    _ = policyMismatch i π μ πl := rfl
