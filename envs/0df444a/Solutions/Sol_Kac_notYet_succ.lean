-- Prove2me | solution 1 for Kac.notYet_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:04:20.100894+00:00
-- url     : https://prove2.me/submissions/1a2f828b-e28c-4db0-a686-d875f6c41c5a

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic

set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory Topology
open scoped ENNReal
open Kac
variable {α : Type*} {f : α → α} {A : Set α}
namespace Kac
theorem _root_.solution (n : ℕ) : notYet f A (n + 1) = Aᶜ ∩ f ⁻¹' notYet f A n := rfl
end Kac
