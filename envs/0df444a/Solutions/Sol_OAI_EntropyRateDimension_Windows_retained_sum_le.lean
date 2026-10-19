-- Prove2me | solution 1 for OAI.EntropyRateDimension.Windows.retained_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:31:28.667225+00:00
-- url     : https://prove2.me/submissions/5e6eea48-1d8f-4475-bc81-3cf397e0ee81

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadiusGrowth
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadialLimit
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ExactDimension
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Conditioning
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TypedLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TailConvolution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteVariance
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SuffixLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordAverage
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BlockWords
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_EntropyBudget
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RetainedLoss
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairBands
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowCount

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Windows
open scoped BigOperators


theorem solution {q : ℕ} (n K : Fin q → ℕ) (a B : Fin q → ℤ) (A' : ℝ)
    (hsep : ∀ i h : Fin q, h < i → (B h : ℝ)<(a i : ℝ)-A'*n i-1)
    (σ : ℕ → ℝ) (hσ : Monotone σ) (L : ℤ)
    (g : ℕ → ℝ) (hg : Antitone g) (hgn : ∀ j, 0 ≤ g j) :
    (∑ i, ∑ k ∈ Finset.range (K i),
      if Retained σ A' (n i) (a i) (B i) L (k*n i) then
        g (k*n i)-g (k*n i+n i) else 0) ≤ g 0 := by
  classical
  set s : (Σ _ : Fin q, ℕ) → ℕ := fun p => p.2 * n p.1 with hs
  set e : (Σ _ : Fin q, ℕ) → ℕ := fun p => p.2 * n p.1 + n p.1 with he
  let R : (Σ _ : Fin q, ℕ) → Prop := fun p => Retained σ A' (n p.1) (a p.1) (B p.1) L (s p)
  let P := (Finset.univ.sigma (fun i => Finset.range (K i))).filter R
  let I : (Σ _ : Fin q, ℕ) → Finset ℕ := fun p => Finset.Ico (s p) (e p)
  let dl : ℕ → ℝ := fun t => g t - g (t+1)
  have hdl : ∀ t, 0 ≤ dl t := fun t => sub_nonneg.mpr (hg (Nat.le_succ t))
  have hterm : ∀ p, g (s p) - g (e p) = ∑ t ∈ I p, dl t := by
    intro p
    simp only [I, e, dl]
    rw [Finset.sum_Ico_eq_sum_range, add_tsub_cancel_left]
    have := Finset.sum_range_sub' (fun u => g (s p + u)) (n p.1)
    simp only [add_zero] at this
    rw [← this]
    apply Finset.sum_congr rfl; intro u _; simp only [add_assoc]
  have hL : (∑ i, ∑ k ∈ Finset.range (K i),
      if Retained σ A' (n i) (a i) (B i) L (k*n i) then
        g (k*n i)-g (k*n i+n i) else 0) = ∑ p ∈ P, ∑ t ∈ I p, dl t := by
    rw [Finset.sum_filter, Finset.sum_sigma]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _
    split_ifs with h
    · exact hterm ⟨i, k⟩
    · rfl
  -- key separation: h < i, both retained ⇒ e (i-interval) ≤ s (h-interval)
  have hkey : ∀ p p' : (Σ _ : Fin q, ℕ), p'.1 < p.1 → R p → R p' → e p ≤ s p' := by
    intro p p' hlt hp hp'
    by_contra hcon
    push Not at hcon
    obtain ⟨hp1, hp2, -⟩ := hp
    obtain ⟨-, -, hp3⟩ := hp'
    have hmono : σ (s p') ≤ σ (s p + n p.1) := hσ (by simp only [e, s] at hcon ⊢; omega)
    have hsep' := hsep p.1 p'.1 hlt
    have c1 : ((⌈σ (s p)⌉ : ℤ) : ℝ) ≤ (L : ℝ) - a p.1 := by exact_mod_cast (by omega : ⌈σ (s p)⌉ ≤ L - a p.1)
    have c2 : (L : ℝ) - ((⌈σ (s p')⌉ : ℤ) : ℝ) ≤ B p'.1 := by exact_mod_cast hp3
    have c3 := Int.le_ceil (σ (s p))
    have c4 := Int.ceil_lt_add_one (σ (s p'))
    linarith
  have hdisj : (P : Set (Σ _ : Fin q, ℕ)).PairwiseDisjoint I := by
    intro p hp p' hp' hne
    simp only [Finset.coe_filter, Set.mem_setOf_eq, P] at hp hp'
    have hd : ∀ x y : (Σ _ : Fin q, ℕ), e x ≤ s y → Disjoint (I x) (I y) := by
      intro x y hxy
      rw [Finset.disjoint_left]
      intro t h1 h2
      simp only [I, Finset.mem_Ico] at h1 h2
      omega
    rcases lt_trichotomy p.1 p'.1 with h | h | h
    · exact (hd p' p (hkey p' p h hp'.2 hp.2)).symm
    · obtain ⟨i, k⟩ := p
      obtain ⟨i', k'⟩ := p'
      simp only at h
      subst h
      have hk : k ≠ k' := fun hk => hne (by rw [hk])
      rcases lt_or_gt_of_ne hk with hk | hk
      · apply hd
        simp only [e, s]
        have := Nat.mul_le_mul_right (n i) (Nat.succ_le_of_lt hk)
        rw [Nat.succ_mul] at this; exact this
      · apply (hd _ _ _).symm
        simp only [e, s]
        have := Nat.mul_le_mul_right (n i) (Nat.succ_le_of_lt hk)
        rw [Nat.succ_mul] at this; exact this
    · exact hd p p' (hkey p p' h hp.2 hp'.2)
  rw [hL, ← Finset.sum_biUnion hdisj]
  set U := P.biUnion I
  have hsub := Finset.subset_range_sup_succ U
  calc ∑ t ∈ U, dl t ≤ ∑ t ∈ Finset.range (U.sup id).succ, dl t :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => hdl t)
    _ = g 0 - g (U.sup id).succ := Finset.sum_range_sub' g _
    _ ≤ g 0 := by linarith [hgn (U.sup id).succ]

