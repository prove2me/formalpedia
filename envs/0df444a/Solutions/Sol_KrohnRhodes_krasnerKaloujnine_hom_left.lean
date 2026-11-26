-- Prove2me | solution 1 for KrohnRhodes.krasnerKaloujnine_hom_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:54:59.084926+00:00
-- url     : https://prove2.me/submissions/acf8a0e7-2d05-46a7-b550-4863ddf8fd46

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Mathlib
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.RegularWreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedDecidableInType false
open KrohnRhodes
universe u
variable {G : Type u} [Group G]
variable (N : Subgroup G) [N.Normal]
namespace KrohnRhodes
theorem _root_.solution (g : G) (q : G ⧸ N) :
    ((krasnerKaloujnine_hom N g).left q : G) =
      (section_ N q)⁻¹ * g * section_ N ((QuotientGroup.mk' N g)⁻¹ * q) := rfl
end KrohnRhodes
