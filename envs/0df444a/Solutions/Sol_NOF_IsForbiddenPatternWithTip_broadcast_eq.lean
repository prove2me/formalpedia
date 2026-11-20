-- Prove2me | solution 1 for NOF.IsForbiddenPatternWithTip.broadcast_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:16:26.131317+00:00
-- url     : https://prove2.me/submissions/46812591-e738-4b9c-a16d-edb4512c4006

module
public import Definitions.Def_ChandraFurstLipton_MultidimCorners
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.ZMod.Defs
public import Definitions.Def_ChandraFurstLipton_NOFModel
public import Theorems.Thm_NOF_Protocol_broadcast_zero
public import Theorems.Thm_NOF_Protocol_broadcast_succ
public import Theorems.Thm_NOF_Protocol_length_broadcast
public import Theorems.Thm_NOF_Protocol_le_complexity
public import Theorems.Thm_NOF_le_funComplexity
attribute [local simp] NOF.Protocol.broadcast_zero
attribute [local simp] NOF.Protocol.length_broadcast
attribute [local simp] NOF.Protocol.le_complexity
attribute [local simp] NOF.le_funComplexity

set_option autoImplicit false
@[expose] public section
public section
open NOF
variable {ι G : Type*} {d : ℕ} [Fintype ι]
variable {F : (ZMod d → G) → Bool} {P : Protocol G d} {a : ZMod d → ZMod d → G} {v : ZMod d → G}
  {B : List Bool} {t : ℕ}
namespace NOF
namespace IsForbiddenPatternWithTip
theorem _root_.solution (hF : IsForbiddenPatternWithTip a v)
    (hB : ∀ i, P.broadcast (a i) t = B) : P.broadcast v t = B := by
  induction t generalizing B with
  | zero => simpa using hB 0
  | succ t ih =>
  simp_rw [Protocol.broadcast_succ] at *
  obtain _ | ⟨b, B⟩ := B
  · cases hB 0
  simp only [List.cons.injEq, forall_and] at hB
  specialize ih hB.2
  subst ih
  have h₁ : forget (t : ZMod d) v = forget (t : ZMod d) (a t) := hF.forget t
  have h₂ : P.broadcast v t = P.broadcast (a t) t := (hB.2 t).symm
  rw [h₁, h₂, hB.1]
end IsForbiddenPatternWithTip
end NOF
