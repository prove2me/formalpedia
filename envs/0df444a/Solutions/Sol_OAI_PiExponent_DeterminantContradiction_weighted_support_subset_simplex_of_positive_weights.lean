-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_support_subset_simplex_of_positive_weights
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:52:01.780125+00:00
-- url     : https://prove2.me/submissions/ab697553-a56f-4c67-8fc2-ab38860004a8

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem solution
    {n : Nat} (w : Fin n → Real) (H : Real) (hw : ∀ i, 0 < w i)
    (P : {Q : MvPolynomial (Fin n) Complex //
      ∀ a ∈ Q.support, ∑ i, w i * (a i : Real) ≤ H}) :
    P.1.support.map Finsupp.equivFunOnFinite.toEmbedding ⊆ realWeightedSimplex w H := by
  classical
  intro x hx
  rcases Finset.mem_map.mp hx with ⟨a, ha, hax⟩
  subst x
  let b : Fin n → Nat := Finsupp.equivFunOnFinite a
  have hsum : ∑ i : Fin n, w i * (b i : Real) ≤ H := by
    simpa [b] using P.2 a ha
  simp only [realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range]
  constructor
  · intro i
    change b i < ⌊H / w i⌋₊ + 1
    have hterm : w i * (b i : Real) ≤ ∑ j : Fin n, w j * (b j : Real) :=
      Finset.single_le_sum
        (fun j hj => mul_nonneg (le_of_lt (hw j)) (Nat.cast_nonneg (b j)))
        (Finset.mem_univ i)
    have hdiv : (b i : Real) ≤ H / w i := (le_div_iff₀ (hw i)).2 (by
      nlinarith [le_trans hterm hsum])
    by_contra hnot
    have hnat : ⌊H / w i⌋₊ + 1 ≤ b i := Nat.le_of_not_gt hnot
    have hcast : ((⌊H / w i⌋₊ + 1 : Nat) : Real) ≤ (b i : Real) := by
      exact_mod_cast hnat
    push_cast at hcast
    have hfloor : H / w i < (⌊H / w i⌋₊ : Real) + 1 :=
      Nat.lt_floor_add_one _
    linarith
  · exact hsum