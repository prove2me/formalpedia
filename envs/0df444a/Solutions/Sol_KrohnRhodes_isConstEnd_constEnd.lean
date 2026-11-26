-- Prove2me | solution 1 for KrohnRhodes.isConstEnd_constEnd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:55:56.752057+00:00
-- url     : https://prove2.me/submissions/bdbb1487-ef98-433f-a0e8-5af273e73e24

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
theorem _root_.solution (q : Q) : IsConstEnd (constEnd q) := ⟨q, rfl⟩
end KrohnRhodes
