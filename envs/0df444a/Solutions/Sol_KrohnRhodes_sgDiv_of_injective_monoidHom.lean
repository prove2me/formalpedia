-- Prove2me | solution 1 for KrohnRhodes.sgDiv_of_injective_monoidHom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:55:47.378851+00:00
-- url     : https://prove2.me/submissions/8a038eb6-a82d-416a-8189-11549dccee9c

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.show false
open KrohnRhodes
universe u
variable {M : Type u} [Monoid M] [Finite M] [DecidableEq M]
namespace KrohnRhodes
theorem _root_.solution {A T : Type u} [Monoid A] [Monoid T]
    (f : A →* T) (hf : Function.Injective f) : SgDiv A T := by
  refine ⟨(MonoidHom.mrange f).toSubsemigroup, ?_, ?_⟩
  · refine ⟨fun u => Function.invFun f u.1, ?_⟩
    intro a b
    obtain ⟨ma, ha⟩ := a.2
    obtain ⟨mb, hb⟩ := b.2
    show Function.invFun f _ = Function.invFun f _ * Function.invFun f _
    have hab : ((a * b : (MonoidHom.mrange f).toSubsemigroup) : T)
        = f (ma * mb) := by
      show (a : T) * (b : T) = f (ma * mb)
      rw [map_mul, ha, hb]
    rw [hab, Function.leftInverse_invFun hf (ma * mb),
        ← ha, Function.leftInverse_invFun hf ma,
        ← hb, Function.leftInverse_invFun hf mb]
  · intro m
    refine ⟨⟨f m, ⟨m, rfl⟩⟩, ?_⟩
    show Function.invFun f (f m) = m
    exact Function.leftInverse_invFun hf m
end KrohnRhodes
