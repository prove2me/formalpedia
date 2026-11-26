-- Prove2me | solution 1 for KrohnRhodes.sgdiv_closure_monoid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:03:50.410693+00:00
-- url     : https://prove2.me/submissions/1d9df8f0-45c4-474a-a651-20a830de42e7

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
public import Theorems.Thm_KrohnRhodes_sgDiv_of_injective_monoidHom


set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
open KrohnRhodes
open Green
namespace KrohnRhodes
theorem _root_.solution {M Q : Type} [Monoid M] (act : M →* Function.End Q)
    (hf : Function.Injective act) : SgDiv M ↥(closureMonoid act) := by
  have hmem : ∀ m : M, act m ∈ closureMonoid act := fun m =>
    Submonoid.subset_closure (Set.mem_union_left _ ⟨m, rfl⟩)
  refine KrohnRhodes.sgDiv_of_injective_monoidHom
    (MonoidHom.codRestrict act (closureMonoid act) hmem) ?_
  intro a b hab
  exact hf (congrArg Subtype.val hab)
end KrohnRhodes
