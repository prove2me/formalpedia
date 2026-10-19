-- Prove2me | solution 1 for OAI.BalancedTransport.Effectivity.computable_rat_pow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:08:15.326992+00:00
-- url     : https://prove2.me/submissions/04c88bb2-de51-4e2b-942a-c64e2aa28a46

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RationalAlgorithms.lean:L100-L111
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Effectivity.computable_rat_pow. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RationalAlgorithms ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

lemma computable_rat_pow : Computable₂ ((· ^ ·) : ℚ → ℕ → ℚ) := by
  have h : Computable (fun p : ℚ × ℕ =>
      Nat.rec (motive := fun _ => ℚ) (1 : ℚ) (fun _ r => r * p.1) p.2) :=
    Computable.nat_rec Computable.snd (Computable.const 1)
      (computable_rat_mul.comp (Computable.snd.comp Computable.snd)
        (Computable.fst.comp Computable.fst)).to₂
  refine h.of_eq ?_
  intro ⟨q,n⟩
  dsimp
  induction n with
  | zero => simp
  | succ n ih => simpa [pow_succ] using congrArg (fun r => r * q) ih

end BalancedTransport.Effectivity
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity


theorem solution : type_of% @_root_.OAI.BalancedTransport.Effectivity.computable_rat_pow := @_root_.OAI.BalancedTransport.Effectivity.computable_rat_pow
