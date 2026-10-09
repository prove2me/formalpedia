-- Prove2me | solution 1 for OAI.Erdos3.primeCoordinateReference_weight_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T19:14:02.213731+00:00
-- url     : https://prove2.me/submissions/24bdbc0d-e943-45f8-ae16-4274816ade36

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSampleAlphabet
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q] {J G : Type*} [Fintype J]
  [AddCommGroup G] [Module (ZMod q) G]

variable [Fintype G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {J G : Type*} [Fintype J] [AddCommGroup G] [Fintype G]

variable {q : ℕ} [NeZero q] [Module (ZMod q) G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]
  {p a : ℕ} [NeZero (p ^ a)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q] {J G : Type*} [Fintype J]
  [AddCommGroup G] [Module (ZMod q) G]

variable [Fintype G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q] {J G : Type*} [Fintype J]
  [AddCommGroup G] [Module (ZMod q) G] [Fintype G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  (p q a : ι → ℕ) [∀ i, NeZero (q i)] {G : ι → Type*}
  [∀ i, AddCommGroup (G i)] [∀ i, Module (ZMod (q i)) (G i)] [∀ i, Fintype (G i)]
  (hp : ∀ i, (p i).Prime) (hcard : ∀ i, Fintype.card (G i) = p i ^ a i)

include hp hcard

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

universe u v

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem primeCoordinateReference_weight_pos {ι σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : ι → ℕ) [∀ i, NeZero (q i)] (i : ι) (x : σ → ZMod (q i)) :
    0 < (primeCoordinateReference (σ := σ) q i).weight x := by
  dsimp only [primeCoordinateReference, FiniteProbabilityWeights.uniform]
  positivity

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.primeCoordinateReference_weight_pos.{u_1, u_2} := @OAI.Erdos3.primeCoordinateReference_weight_pos.{u_1, u_2}
