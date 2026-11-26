-- Prove2me | solution 1 for KrohnRhodes.constEnd_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:56:03.309333+00:00
-- url     : https://prove2.me/submissions/c3ae0e82-5db5-402a-b40c-8c983ff7c750

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.show false
open KrohnRhodes
universe u
variable {Q : Type u}
namespace KrohnRhodes
theorem _root_.solution (p : Q) (t : Function.End Q) :
    constEnd p * t = constEnd p := rfl
end KrohnRhodes
