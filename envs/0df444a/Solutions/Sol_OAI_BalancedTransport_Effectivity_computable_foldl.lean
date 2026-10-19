-- Prove2me | solution 1 for OAI.BalancedTransport.Effectivity.computable_foldl
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:25:47.082234+00:00
-- url     : https://prove2.me/submissions/0080fcd6-d323-416e-b618-d88b3b91ec71

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

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
theorem h44_foldl_take {β σ : Type*} [Inhabited β] (l : List β) (g : σ) (h : σ × β → σ) :
    ∀ n, n ≤ l.length → Nat.rec (motive := fun _ => σ) g (fun k acc => h (acc, l.getD k default)) n
      = (l.take n).foldl (fun s b => h (s, b)) g := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [List.take_add_one, List.foldl_append, ← ih (by omega)]
    have : l[n]? = some (l.getD n default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    rw [this]; rfl

theorem solution {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    [Inhabited β] {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldl (fun s b => h a (s,b)) (g a)) := by
  have hc := Computable.nat_rec (f := fun a => (f a).length) (g := g)
    (h := fun a (z : ℕ × σ) => h a (z.2, (f a).getD z.1 default))
    (Primrec.list_length.to_comp.comp hf) hg
    (hh.comp Computable.fst (Computable.pair (Computable.snd.comp Computable.snd)
      ((Primrec.list_getD default).to_comp.comp (hf.comp Computable.fst) (Computable.fst.comp Computable.snd))))
  refine hc.of_eq ?_
  intro a
  have := h44_foldl_take (f a) (g a) (h a) _ le_rfl
  rw [List.take_length] at this
  exact this

