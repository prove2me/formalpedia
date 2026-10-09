-- Prove2me | solution 1 for OAI.Erdos3.residuePrimeCoordinateMean_re_le_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T19:16:31.97159+00:00
-- url     : https://prove2.me/submissions/702dfd9e-b35f-4336-a98f-5e4be4c89886

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResiduePrimeDensityError
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
  (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
  (q : ι → ℕ) [∀ i, NeZero (q i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMean_re {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ)
    (M : ℕ) (a : σ → ℤ) (q : ι → ℕ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    (residuePrimeCoordinateMean f lo N M a q I x).re =
      𝔼 z : ResiduePrimeCoordinateCell lo N M a q I x, (f (fun j => (z.val j).val)).re := by
  simp only [residuePrimeCoordinateMean, Fintype.expect_eq_sum_div_card,
    Complex.div_natCast_re, Complex.re_sum]
  congr 3 <;> exact Subsingleton.elim _ _

theorem residuePrimeCoordinateRealMean_bound {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (f : (σ → ℤ) → ℝ) (lo : σ → ℤ) (N : σ → ℕ)
    (M : ℕ) (a : σ → ℤ) (q : ι → ℕ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ z ∈ translatedIntegerBox lo N, |f z| ≤ C) :
    |𝔼 z : ResiduePrimeCoordinateCell lo N M a q I x, f (fun j => (z.val j).val)| ≤ C := by
  classical
  by_cases hne : Nonempty (ResiduePrimeCoordinateCell lo N M a q I x)
  · let := hne
    rw [← FiniteProbabilityWeights.uniform_mean]
    apply FiniteProbabilityWeights.abs_mean_le_on_support
    intro z _
    apply hf
    apply (mem_translatedIntegerBox lo N _).mpr
    intro j
    exact Finset.mem_Ico.mp ((Finset.mem_filter.mp (z.val j).property).1)
  · let : IsEmpty (ResiduePrimeCoordinateCell lo N M a q I x) := not_nonempty_iff.mp hne
    simp only [Fintype.expect_eq_sum_div_card, Fintype.card_of_isEmpty, Nat.cast_zero,
      div_zero, abs_zero]
    exact hC

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueBaselineBounds
namespace OAI

section

namespace Erdos3

theorem residuePrimeCoordinateMean_re_le_one {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (g : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ)
    (M : ℕ) (a : σ → ℤ) (q : ι → ℕ) (K : Finset ι) (base : ∀ i, σ → ZMod (q i))
    (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1) :
    (residuePrimeCoordinateMean g lo N M a q K base).re ≤ 1 := by
  have ha : ∀ z ∈ translatedIntegerBox lo N, |(g z).re| ≤ 1 := by
    intro z hz
    rw [abs_of_nonneg (hg z hz).1]
    exact (hg z hz).2
  have h := residuePrimeCoordinateRealMean_bound (fun z => (g z).re) lo N M a q K base 1 zero_le_one ha
  rw [← residuePrimeCoordinateMean_re] at h
  exact (le_abs_self _).trans h

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.residuePrimeCoordinateMean_re_le_one.{u_1, u_2} := @OAI.Erdos3.residuePrimeCoordinateMean_re_le_one.{u_1, u_2}
