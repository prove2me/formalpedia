-- Prove2me | solution 2 for OAI.BalancedTransport.Effectivity.computable_foldl
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:36:28.111469+00:00
-- url     : https://prove2.me/submissions/10c2ddac-240d-456b-8c62-7d1ac71088ec

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/NumericPrograms.lean:L8-L32
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Effectivity.computable_foldl. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericPrograms ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity

lemma computable_foldl {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    [Inhabited β] {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldl (fun s b => h a (s,b)) (g a)) := by
  have hc : Computable (fun a => Nat.rec (motive := fun _ => σ) (g a)
      (fun j v => h a (v, (f a).getD j default)) (f a).length) :=
    Computable.nat_rec (Computable.list_length.comp hf) hg
      (hh.comp Computable.fst ((Computable.snd.comp Computable.snd).pair
        ((Primrec.list_getD default).to_comp.comp (hf.comp Computable.fst)
          (Computable.fst.comp Computable.snd)))).to₂
  apply hc.of_eq
  intro a
  have he (n : ℕ) (hn : n ≤ (f a).length) : Nat.rec (motive := fun _ => σ) (g a)
      (fun j v => h a (v, (f a).getD j default)) n =
      ((f a).take n).foldl (fun s b => h a (s,b)) (g a) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hl : n < (f a).length := by omega
      change h a (Nat.rec (motive := fun _ => σ) (g a)
        (fun j v => h a (v, (f a).getD j default)) n, (f a).getD n default) = _
      rw [ih (by omega), List.take_succ_eq_append_getElem hl,
        List.foldl_concat]
      rw [List.getD_eq_getElem _ _ hl]
  simpa using he (f a).length le_rfl

end BalancedTransport.Effectivity
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

end BalancedTransport.Effectivity.NumericOp
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity


theorem solution : type_of% @_root_.OAI.BalancedTransport.Effectivity.computable_foldl := @_root_.OAI.BalancedTransport.Effectivity.computable_foldl
