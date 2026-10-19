-- Prove2me | solution 2 for OAI.CirculantHadamard.cyclic_reduction_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:21:43.763906+00:00
-- url     : https://prove2.me/submissions/e38455cb-e374-498e-b197-e2d5b12c9e04

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/OrderProjection.lean:L29-L52
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.cyclic_reduction_fiber_card. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection

-- ---- from OAI.LinearAlgebra.CirculantHadamard.OrderProjection ----
namespace OAI

universe uα

/-!
# The first order projection

The quotient sends the original cyclic generator to the cyclic generator of
the smaller order. Its coefficients are the sums over the actual reduction
fibers. When `n = m * d`, every fiber contains exactly `d` original indices;
an odd number of signs therefore produces an odd integer coefficient.

The norm scalar is preserved by the quotient map. In particular, projecting
from `2^(2*s) * u^2` to `2^(2*s)` does not divide the original norm scalar.
-/

noncomputable section

namespace CirculantHadamard

open scoped BigOperators

/-- Every fiber of reduction modulo a divisor has the exact quotient size. -/
theorem cyclic_reduction_fiber_card {n m d : ℕ} [NeZero n] [NeZero m]
    (hdiv : m ∣ n) (hn : n = m * d) (a : ZMod m) :
    Fintype.card {x : ZMod n // ZMod.castHom hdiv (ZMod m) x = a} = d := by
  classical
  let q : ZMod n →+ ZMod m := (ZMod.castHom hdiv (ZMod m)).toAddMonoidHom
  have hsurj : Function.Surjective q := by
    intro b
    refine ⟨(b.val : ZMod n), ?_⟩
    change ZMod.castHom hdiv (ZMod m) (b.val : ZMod n) = b
    simp only [map_natCast, ZMod.natCast_zmod_val]
  have hcards (b : ZMod m) :
      (Finset.univ.filter (fun x : ZMod n => q x = b)).card =
        (Finset.univ.filter (fun x : ZMod n => q x = a)).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range q (hsurj b) (hsurj a)
  have htotal : n = m * (Finset.univ.filter (fun x : ZMod n => q x = a)).card := by
    calc
      n = (Finset.univ : Finset (ZMod n)).card := by simp
      _ = ∑ b : ZMod m, (Finset.univ.filter (fun x : ZMod n => q x = b)).card :=
        Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
      _ = m * (Finset.univ.filter (fun x : ZMod n => q x = a)).card := by
        simp only [hcards, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
  rw [Fintype.card_subtype]
  exact Nat.eq_of_mul_eq_mul_left (NeZero.pos m) (htotal.symm.trans hn)

end CirculantHadamard

end

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.CirculantHadamard.cyclic_reduction_fiber_card := @_root_.OAI.CirculantHadamard.cyclic_reduction_fiber_card
