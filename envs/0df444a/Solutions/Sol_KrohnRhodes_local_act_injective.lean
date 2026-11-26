-- Prove2me | solution 1 for KrohnRhodes.local_act_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:50.090146+00:00
-- url     : https://prove2.me/submissions/7e7351bb-79d9-4e0f-a821-e23d026e38b2

module
public import Definitions.Def_KrohnRhodes_Defs
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_FactorTower
public import Definitions.Def_KrohnRhodes_PrimeDecomposition

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
open KrohnRhodes
open Green
namespace KrohnRhodes
theorem _root_.solution {M Q : Type} [Monoid M] (act : M →* Function.End Q) (c : M)
    (hf : Function.Injective act) : Function.Injective (localActHom act c) := by
  intro u v huv
  apply LocalDivisor.ext
  apply hf
  funext x
  have h : localActHom act c u ⟨act c x, x, rfl⟩ = localActHom act c v ⟨act c x, x, rfl⟩ :=
    congrFun huv ⟨act c x, x, rfl⟩
  have h1 : act (Classical.choose u.mem_right) (act c x)
      = act (Classical.choose v.mem_right) (act c x) := congrArg Subtype.val h
  have hu := Classical.choose_spec u.mem_right
  have hv := Classical.choose_spec v.mem_right
  calc act u.val x
      = act (Classical.choose u.mem_right * c) x := by rw [← hu]
    _ = act (Classical.choose u.mem_right) (act c x) := by rw [map_mul]; rfl
    _ = act (Classical.choose v.mem_right) (act c x) := h1
    _ = act (Classical.choose v.mem_right * c) x := by rw [map_mul]; rfl
    _ = act v.val x := by rw [← hv]
end KrohnRhodes
