-- Prove2me | solution 1 for OAI.Erdos3.residue_function_alphabet_card_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T19:18:37.454129+00:00
-- url     : https://prove2.me/submissions/cb8b586b-a151-4b34-84d9-2877255d7311

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedPhysicalCRT
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {J I : Type*} [Fintype J] [Fintype I] {q : ℕ} [NeZero q]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {J I : Type*} [Fintype J] [Fintype I] {q : ℕ} [NeZero q]

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem residue_function_alphabet_card_le_exp {I : Type*} [Fintype I] {q : ℕ} [NeZero q]
    {B : ℝ} (hq : (q : ℝ) ≤ Real.exp B) :
    (Fintype.card (I → ZMod q) : ℝ) ≤ Real.exp ((Fintype.card I : ℝ) * B) := by
  simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow]
  exact (pow_le_pow_left₀ (Nat.cast_nonneg q) hq _).trans_eq (Real.exp_nat_mul _ _).symm

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {J : Type*} [Fintype J] {q : ℕ} [NeZero q]

end Erdos3

end

section

namespace Erdos3

open scoped Classical

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

variable {ι J σ : Type*} [Fintype J] [Fintype σ]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

variable [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  (q : ι → ℕ) [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
  (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J σ : Type*} [Fintype J] [Fintype σ]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

variable [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J I : Type*} [Fintype J] [Fintype I]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

variable [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [Fintype σ]
  (q : ι → ℕ) [∀ i, NeZero (q i)] [NeZero (∏ i, q i)]
  (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J I Ω Θ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype J] [Fintype I] [Fintype Ω] [Fintype Θ]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J I : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  [Fintype I]
  (q : ι → ℕ) [∀ i, NeZero (q i)]
  (sourceLo : Option J × I → ℤ) (sourceN : Option J × I → ℕ)
  (sourceHne : Nonempty (IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i)
    (fun _ => 1) (fun _ => 0)))
  (paramLo : J → ℤ) (paramN : J → ℕ)
  (paramHne : Nonempty (IntegerResidueBox paramLo (fun j => paramLo j + paramN j)
    (fun _ => 1) (fun _ => 0)))
  (siteLo : I → ℤ) (siteN : I → ℕ)
  (siteHne : Nonempty (IntegerResidueBox siteLo (fun i => siteLo i + siteN i)
    (fun _ => 1) (fun _ => 0)))
  (D : ℕ) (a : J → ℤ) (b : ℕ) (w : (Option J × I → ℤ) → ℝ) (f : (I → ℤ) → ℝ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I]

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.residue_function_alphabet_card_le_exp.{u_1} := @OAI.Erdos3.residue_function_alphabet_card_le_exp.{u_1}
