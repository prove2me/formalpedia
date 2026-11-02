-- Prove2me | solution 1 for NoSignalPA.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T22:00:24.110318+00:00
-- url     : https://prove2.me/submissions/78bf3645-fd16-4696-b78c-e7c857d4f278

import Mathlib
import Definitions.Def_NoSignalPA_SatisfiesEq6
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability
import Theorems.Thm_NoSignalPA_entry_tail
import Theorems.Thm_NoSignalPA_chsh_tensor_entry

namespace NoSignalPALemma2Aux

lemma uniformProbability_mono {α : Type} [Fintype α] (P Q : α → Prop) (h : ∀ ω, P ω → Q ω) :
    OAI.ThorpCompatibility.uniformProbability P ≤ OAI.ThorpCompatibility.uniformProbability Q := by
  classical
  unfold OAI.ThorpCompatibility.uniformProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card fun ω hω => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact h ω hω

lemma uniformProbability_le_one {α : Type} [Fintype α] [Nonempty α] (P : α → Prop) :
    OAI.ThorpCompatibility.uniformProbability P ≤ 1 := by
  classical
  unfold OAI.ThorpCompatibility.uniformProbability
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [div_le_one hc]
  exact_mod_cast Finset.card_le_univ _

/-- Counting form of the union bound; the decidability instances are taken from the goal. -/
lemma card_filter_exists_le {α ι : Type} [Fintype α] [Fintype ι] (E : ι → α → Prop)
    {d : DecidablePred (fun ω => ∃ i, E i ω)} {dE : ∀ i, DecidablePred (E i)} :
    (@Finset.filter α (fun ω => ∃ i, E i ω) d Finset.univ).card ≤
      ∑ i, (@Finset.filter α (E i) (dE i) Finset.univ).card := by
  classical
  calc (@Finset.filter α (fun ω => ∃ i, E i ω) d Finset.univ).card
      ≤ (Finset.univ.biUnion fun i => @Finset.filter α (E i) (dE i) Finset.univ).card := by
        apply Finset.card_le_card
        intro ω hω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion] at hω ⊢
        exact hω
    _ ≤ ∑ i, (@Finset.filter α (E i) (dE i) Finset.univ).card := Finset.card_biUnion_le

lemma card_filter_or_le {α : Type} [Fintype α] (P Q : α → Prop)
    {d : DecidablePred (fun ω => P ω ∨ Q ω)} {dP : DecidablePred P} {dQ : DecidablePred Q} :
    (@Finset.filter α (fun ω => P ω ∨ Q ω) d Finset.univ).card ≤
      (@Finset.filter α P dP Finset.univ).card + (@Finset.filter α Q dQ Finset.univ).card := by
  classical
  calc (@Finset.filter α (fun ω => P ω ∨ Q ω) d Finset.univ).card
      ≤ ((@Finset.filter α P dP Finset.univ) ∪ (@Finset.filter α Q dQ Finset.univ)).card := by
        apply Finset.card_le_card
        intro ω hω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hω ⊢
        exact hω
    _ ≤ _ := Finset.card_union_le _ _

/-- Union bound. -/
lemma uniformProbability_exists_le {α ι : Type} [Fintype α] [Fintype ι] (E : ι → α → Prop) :
    OAI.ThorpCompatibility.uniformProbability (fun ω => ∃ i, E i ω) ≤
      ∑ i, OAI.ThorpCompatibility.uniformProbability (E i) := by
  unfold OAI.ThorpCompatibility.uniformProbability
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast card_filter_exists_le E

lemma uniformProbability_or_le {α : Type} [Fintype α] (P Q : α → Prop) :
    OAI.ThorpCompatibility.uniformProbability (fun ω => P ω ∨ Q ω) ≤
      OAI.ThorpCompatibility.uniformProbability P + OAI.ThorpCompatibility.uniformProbability Q := by
  unfold OAI.ThorpCompatibility.uniformProbability
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast card_filter_or_le P Q

end NoSignalPALemma2Aux

open NoSignalPALemma2Aux in
theorem solution {Nr Ns : ℕ} (hN : (Ns : ℝ) + Real.sqrt Nr ≤ Nr + 2) :
    OAI.ThorpCompatibility.uniformProbability
        (fun h : NoSignalPA.Str Nr → NoSignalPA.Str Ns => ¬ NoSignalPA.SatisfiesEq6 h)
      < 2 * Real.exp (5 * Nr - (2 : ℝ) ^ Real.sqrt Nr / 4) := by
  rcases Nat.eq_zero_or_pos Nr with h0 | hpos
  · -- `Nr = 0`: the trivial bound `≤ 1` already suffices
    subst h0
    refine lt_of_le_of_lt (uniformProbability_le_one _) ?_
    simp only [Nat.cast_zero, mul_zero, Real.sqrt_zero, Real.rpow_zero, zero_sub]
    have : Real.exp (-(1 / 4)) > 1 / 2 := by
      have h := Real.add_one_le_exp (-(1 / 4 : ℝ))
      linarith
    linarith
  · -- the union bound over the `2^Ns · 16^Nr` entries
    set q : ℝ := (2 : ℝ) ^ Real.sqrt Nr / 4 with hq
    set c : ℝ := (2 : ℝ) ^ (-(Ns : ℝ) - 2 * Nr) with hc
    let I := NoSignalPA.Str Ns × NoSignalPA.Str Nr × NoSignalPA.Str Nr × NoSignalPA.Str Nr ×
      NoSignalPA.Str Nr
    let Mi : I → ℕ := fun i => NoSignalPA.ones
      (fun j => xor (xor (i.2.1 j) (i.2.2.1 j)) (i.2.2.2.1 j && i.2.2.2.2 j))
    let Ti : I → ℝ := fun i =>
      (2 : ℝ) ^ ((Real.sqrt Nr - Nr - Ns) / 2) * ((4 : ℝ) ^ Nr)⁻¹ * 5 ^ Mi i
    let Xi : I → (NoSignalPA.Str Nr → NoSignalPA.Str Ns) → ℝ := fun i h =>
      ∑ t, NoSignalPA.gammaVec t i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2 * (if h t = i.1 then 1 else 0)
    let A : I → (NoSignalPA.Str Nr → NoSignalPA.Str Ns) → Prop := fun i h => c + Ti i ≤ Xi i h
    let B : I → (NoSignalPA.Str Nr → NoSignalPA.Str Ns) → Prop := fun i h => Xi i h ≤ c - Ti i
    -- identities
    have h2c : (2 : ℝ) ^ Ns * c = ((4 : ℝ) ^ Nr)⁻¹ := by
      rw [hc, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num),
        show (Ns : ℝ) + (-(Ns : ℝ) - 2 * Nr) = -(2 * (Nr : ℝ)) by ring,
        Real.rpow_neg (by norm_num), show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul,
        ← Real.rpow_natCast]
      push_cast
      ring_nf
    have hT : ∀ i : I, Real.sqrt ((2 : ℝ) ^ ((Ns : ℝ) + Real.sqrt Nr)) *
        NoSignalPA.chshPow i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2 = (2 : ℝ) ^ Ns * Ti i := by
      intro i
      rw [NoSignalPA.chsh_tensor_entry, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
      simp only [Ti, Mi]
      rw [show (4 : ℝ) ^ Nr = (2 : ℝ) ^ (2 * (Nr : ℝ)) by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul, ← Real.rpow_natCast]
          push_cast; ring_nf,
        ← Real.rpow_neg (by norm_num), ← Real.rpow_natCast 2 Ns]
      rw [show (2 : ℝ) ^ (((Ns : ℝ) + Real.sqrt Nr) * (1 / 2)) *
          ((2 : ℝ) ^ (-(5 * (Nr : ℝ)) / 2) *
            5 ^ NoSignalPA.ones (fun j => xor (xor (i.2.1 j) (i.2.2.1 j)) (i.2.2.2.1 j && i.2.2.2.2 j)))
          = ((2 : ℝ) ^ (((Ns : ℝ) + Real.sqrt Nr) * (1 / 2)) * (2 : ℝ) ^ (-(5 * (Nr : ℝ)) / 2)) *
            5 ^ NoSignalPA.ones (fun j => xor (xor (i.2.1 j) (i.2.2.1 j)) (i.2.2.2.1 j && i.2.2.2.2 j))
          by ring]
      rw [← Real.rpow_add (by norm_num), ← mul_assoc, ← mul_assoc, ← Real.rpow_add (by norm_num),
        ← Real.rpow_add (by norm_num)]
      congr 2
      ring
    -- a violation of (6) at an entry is one of the two tail events
    have hsub : ∀ h, ¬ NoSignalPA.SatisfiesEq6 h → ∃ i : I, A i h ∨ B i h := by
      intro h hns
      simp only [NoSignalPA.SatisfiesEq6, not_forall, not_le] at hns
      obtain ⟨k, a, b, x, y, hv⟩ := hns
      refine ⟨(k, a, b, x, y), ?_⟩
      have hX : ∑ t ∈ Finset.univ.filter (fun t => h t = k), NoSignalPA.gammaVec t a b x y =
          Xi (k, a, b, x, y) h := by
        simp only [Xi, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_filter]
      rw [hX, hT (k, a, b, x, y), ← h2c, ← mul_sub] at hv
      have h2pos : (0 : ℝ) < 2 ^ Ns := by positivity
      rw [abs_mul, abs_of_pos h2pos] at hv
      have hv' : Ti (k, a, b, x, y) < |Xi (k, a, b, x, y) h - c| :=
        lt_of_mul_lt_mul_left hv h2pos.le
      rcases lt_abs.mp hv' with h1 | h1
      · left; simp only [A]; linarith
      · right; simp only [B]; linarith
    -- each entry has both tails at most `e^{-q}` (entry_tail)
    have htail : ∀ i : I,
        OAI.ThorpCompatibility.uniformProbability (A i) ≤
          Real.exp (-((2 : ℝ) ^ Real.sqrt Nr) / 4) ∧
        OAI.ThorpCompatibility.uniformProbability (B i) ≤
          Real.exp (-((2 : ℝ) ^ Real.sqrt Nr) / 4) :=
      fun i => NoSignalPA.entry_tail hN i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2
    have hcardI : (Fintype.card I : ℝ) = (2 : ℝ) ^ Ns * ((2 : ℝ) ^ Nr) ^ 4 := by
      simp [I, NoSignalPA.Str, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
      ring
    have hNs : Ns ≤ Nr + 1 := by
      have h1 : (1 : ℝ) ≤ Real.sqrt Nr := by
        rw [Real.one_le_sqrt]; exact_mod_cast hpos
      have : (Ns : ℝ) ≤ Nr + 1 := by linarith
      exact_mod_cast this
    have hcount : (2 : ℝ) ^ Ns * ((2 : ℝ) ^ Nr) ^ 4 < Real.exp (5 * Nr) := by
      have e1 : (2 : ℝ) ^ Ns ≤ 2 ^ (Nr + 1) := pow_le_pow_right₀ (by norm_num) hNs
      have e2 : (2 : ℝ) ^ (Nr + 1) * ((2 : ℝ) ^ Nr) ^ 4 ≤ (64 : ℝ) ^ Nr := by
        rw [← pow_mul, ← pow_add, show (64 : ℝ) = 2 ^ 6 by norm_num, ← pow_mul]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have e3 : (64 : ℝ) ^ Nr < Real.exp (5 * Nr) := by
        rw [show (5 : ℝ) * Nr = Nr * 5 by ring, Real.exp_nat_mul]
        apply pow_lt_pow_left₀ _ (by norm_num) hpos.ne'
        have he := Real.exp_one_gt_d9
        have : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
        rw [this]
        nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) he.le 5]
      have hpow : (0 : ℝ) ≤ ((2 : ℝ) ^ Nr) ^ 4 := by positivity
      calc (2 : ℝ) ^ Ns * ((2 : ℝ) ^ Nr) ^ 4 ≤ 2 ^ (Nr + 1) * ((2 : ℝ) ^ Nr) ^ 4 :=
            mul_le_mul_of_nonneg_right e1 hpow
        _ ≤ (64 : ℝ) ^ Nr := e2
        _ < Real.exp (5 * Nr) := e3
    calc OAI.ThorpCompatibility.uniformProbability
          (fun h : NoSignalPA.Str Nr → NoSignalPA.Str Ns => ¬ NoSignalPA.SatisfiesEq6 h)
        ≤ OAI.ThorpCompatibility.uniformProbability (fun h => ∃ i : I, A i h ∨ B i h) :=
          uniformProbability_mono _ _ hsub
      _ ≤ ∑ i : I, OAI.ThorpCompatibility.uniformProbability (fun h => A i h ∨ B i h) :=
          uniformProbability_exists_le (fun i h => A i h ∨ B i h)
      _ ≤ ∑ _i : I, 2 * Real.exp (-q) := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine (uniformProbability_or_le (A i) (B i)).trans ?_
          have := htail i
          rw [show -((2 : ℝ) ^ Real.sqrt Nr) / 4 = -q by rw [hq]; ring] at this
          linarith [this.1, this.2]
      _ = (Fintype.card I : ℝ) * (2 * Real.exp (-q)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ < 2 * Real.exp (5 * Nr - (2 : ℝ) ^ Real.sqrt Nr / 4) := by
          rw [hcardI, ← hq, sub_eq_add_neg, Real.exp_add]
          have hE : 0 < Real.exp (-q) := Real.exp_pos _
          nlinarith [hcount, hE]
