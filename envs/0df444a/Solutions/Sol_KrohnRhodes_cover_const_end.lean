-- Prove2me | solution 1 for KrohnRhodes.cover_const_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:28.273038+00:00
-- url     : https://prove2.me/submissions/94c951fd-fd72-4896-89b9-86a0db97a0f2

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
    (N : Submonoid M) (x : Q) :
    ∃ w : WreathProduct ↥(closureMonoid (localActHom act c))
      ↥(closureMonoid (extAct act N)) (Q ⊕ ↥N),
      Covers (dksProj act c N) w (constEnd x) := by
  refine ⟨⟨fun _ => 1, ⟨constEnd (Sum.inl x),
    Submonoid.subset_closure (Set.mem_union_right _ ⟨Sum.inl x, rfl⟩)⟩⟩, ?_⟩
  intro p y
  rfl
end KrohnRhodes
