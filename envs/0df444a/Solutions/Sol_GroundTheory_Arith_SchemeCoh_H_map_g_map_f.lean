-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.H.map_g_map_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:45:05.98353+00:00
-- url     : https://prove2.me/submissions/63229e37-0c1e-4af5-af9e-fb519b96ea3c

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Limits Opposite Abelian
universe w' v u
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)
namespace GroundTheory.Arith.SchemeCoh
namespace H
theorem _root_.solution {n : ℕ} (x : Sheaf.H S.X₁ n) :
    Sheaf.H.map S.g n (Sheaf.H.map S.f n x) = 0 := by
  rw [← Sheaf.H.map_comp_apply, S.zero, Sheaf.H.map_apply, Ext.mk₀_zero, Ext.comp_zero]
end H
end GroundTheory.Arith.SchemeCoh
