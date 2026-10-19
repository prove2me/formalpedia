-- Prove2me | solution 1 for OAI.BalancedTransport.Effectivity.computable_sum_range
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:10:12.953267+00:00
-- url     : https://prove2.me/submissions/573b0a20-ef0f-48a0-9c2a-f970e614445b

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RationalAlgorithms.lean:L113-L126
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Effectivity.computable_sum_range. The node keeps its source
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

lemma computable_sum_range {α : Type*} [Primcodable α]
    {f : α → ℕ → ℚ} (hf : Computable₂ f) :
    Computable₂ (fun a n => ∑ i ∈ Finset.range n, f a i) := by
  have hh : Computable (fun p : α × ℕ =>
      Nat.rec (motive := fun _ => ℚ) (0 : ℚ) (fun n r => r + f p.1 n) p.2) :=
    Computable.nat_rec Computable.snd (Computable.const 0)
      (computable_rat_add.comp (Computable.snd.comp Computable.snd)
        (hf.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))).to₂
  refine hh.of_eq ?_
  intro ⟨a,n⟩
  dsimp
  induction n with
  | zero => simp
  | succ n ih => simpa [Finset.sum_range_succ] using congrArg (fun r => r + f a n) ih

end BalancedTransport.Effectivity
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity


theorem solution : type_of% @_root_.OAI.BalancedTransport.Effectivity.computable_sum_range := @_root_.OAI.BalancedTransport.Effectivity.computable_sum_range
