-- Prove2me | solution 1 for OAI.Erdos3.integerBox_joint_error_of_window_tests
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:41:30.489906+00:00
-- url     : https://prove2.me/submissions/5c260d2e-92ea-45e1-84a2-a52798b58e38

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B016

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealFiniteZeroExtension
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem realZeroExtendFinset_on {X : Type*} (S : Finset X) (f : X → ℝ)
    {x : X} (hx : x ∈ S) : realZeroExtendFinset S f x = f x := by
  simp only [realZeroExtendFinset, if_pos hx]

theorem realZeroExtendFinset_off {X : Type*} (S : Finset X) (f : X → ℝ)
    {x : X} (hx : x ∉ S) : realZeroExtendFinset S f x = 0 := by
  simp only [realZeroExtendFinset, if_neg hx]

theorem realZeroExtendFinset_unit {X : Type*} (S : Finset X) (f : X → ℝ)
    (hf : ∀ x ∈ S, 0 ≤ f x ∧ f x ≤ 1) (x : X) :
    0 ≤ realZeroExtendFinset S f x ∧ realZeroExtendFinset S f x ≤ 1 := by
  by_cases hx : x ∈ S
  · simpa only [realZeroExtendFinset_on S f hx] using hf x hx
  · simp only [realZeroExtendFinset_off S f hx, le_refl, zero_le_one, and_self]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineMeshRetention
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerBoxUniformWeights_mean {J : Type*} [Fintype J] [DecidableEq J]
    (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (f : (∀ j, Finset.Ico (lo j) (hi j)) → ℝ) :
    (integerBoxUniformWeights lo hi hlen).mean f = 𝔼 x, f x := by
  let : ∀ j, Nonempty (Finset.Ico (lo j) (hi j)) :=
    fun j => ⟨⟨lo j, Finset.mem_Ico.mpr ⟨le_rfl, hlen j⟩⟩⟩
  have he : integerBoxUniformWeights lo hi hlen =
      FiniteProbabilityWeights.uniform (∀ j, Finset.Ico (lo j) (hi j)) := by
    apply FiniteProbabilityWeights.eq_of_weight_eq
    intro x
    change (∏ j, (Fintype.card (Finset.Ico (lo j) (hi j)) : ℝ)⁻¹) =
      (Fintype.card (∀ j, Finset.Ico (lo j) (hi j)) : ℝ)⁻¹
    rw [Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]
  rw [he, FiniteProbabilityWeights.uniform_mean]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q : ℕ}

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerBox_weighted_joint_mean
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (lo hi : I → ℤ) (hsource : ∀ i, lo i < hi i)
    (parLo parHi : J → ℤ) (hparam : ∀ j, parLo j < parHi j)
    (w : (I → ℤ) → ℝ) (f : (I → ℤ) → (∀ j, Finset.Ico (parLo j) (parHi j)) → ℝ) :
    ((integerBoxUniformWeights parLo parHi hparam).prod
      (integerBoxUniformWeights lo hi hsource)).mean
        (fun tx => w (fun i => (tx.2 i).val) * f (fun i => (tx.2 i).val) tx.1) =
      𝔼 z ∈ Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i)), w z * (𝔼 t, f z t) := by
  rw [FiniteProbabilityWeights.mean_prod, FiniteProbabilityWeights.mean_comm]
  simp only [FiniteProbabilityWeights.mean_const_mul, integerBoxUniformWeights_mean]
  rw [← finiteBoxPoints_expect (fun i => Finset.Ico (lo i) (hi i)) (fun z => w z * (𝔼 t, f z t))]
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ, Fintype.card_coe]
  congr 1
  simpa only [Finset.expect_eq_sum_div_card, Finset.card_univ] using
    Finset.sum_coe_sort (Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i)))
      (fun z => w z * (𝔼 t, f z t))

theorem integerBox_joint_error_of_window_tests
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (lo hi : I → ℤ) (hsource : ∀ i, lo i < hi i)
    (parLo parHi : J → ℤ) (hparam : ∀ j, parLo j < parHi j)
    (f : (I → ℤ) → (∀ j, Finset.Ico (parLo j) (parHi j)) → ℝ) (accuracy : ℝ)
    (htest : ∀ v : (I → ℤ) → ℝ, (∀ z, 0 ≤ v z ∧ v z ≤ 1) →
      |𝔼 z ∈ Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i)), v z * (𝔼 t, f z t)| ≤ accuracy)
    (w : (I → ℤ) → ℝ)
    (hw : ∀ z : (∀ i, Finset.Ico (lo i) (hi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) :
    |((integerBoxUniformWeights parLo parHi hparam).prod
      (integerBoxUniformWeights lo hi hsource)).mean
        (fun tx => w (fun i => (tx.2 i).val) * f (fun i => (tx.2 i).val) tx.1)| ≤ accuracy := by
  let W := Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i))
  have hwW (z) (hz : z ∈ W) : 0 ≤ w z ∧ w z ≤ 1 := by
    exact hw (fun i => ⟨z i, Fintype.mem_piFinset.mp hz i⟩)
  have h := htest (realZeroExtendFinset W w) (realZeroExtendFinset_unit W w hwW)
  rw [integerBox_weighted_joint_mean lo hi hsource parLo parHi hparam w f]
  convert h using 2
  apply Finset.expect_congr rfl
  intro z hz
  rw [realZeroExtendFinset_on W w hz]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.integerBox_joint_error_of_window_tests.{u_1, u_2} := @OAI.Erdos3.integerBox_joint_error_of_window_tests.{u_1, u_2}
