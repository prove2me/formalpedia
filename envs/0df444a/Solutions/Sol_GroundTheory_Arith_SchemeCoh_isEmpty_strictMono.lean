-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isEmpty_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:17.944696+00:00
-- url     : https://prove2.me/submissions/576bb990-12e4-4349-8b3a-f68c732851fb

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Ordered

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
open CategoryTheory Opposite TopologicalSpace
universe w u
variable {X : TopCat.{u}} {ι : Type w} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
variable [LinearOrder ι]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution [Finite ι] {n : ℕ} (hn : Nat.card ι ≤ n) :
    IsEmpty {i : Fin (n + 1) → ι // StrictMono i} := by
  refine ⟨fun i => ?_⟩
  have := Fintype.ofFinite ι
  have h := Fintype.card_le_of_injective i.1 i.2.injective
  rw [Fintype.card_fin, ← Nat.card_eq_fintype_card] at h
  omega
end GroundTheory.Arith.SchemeCoh
