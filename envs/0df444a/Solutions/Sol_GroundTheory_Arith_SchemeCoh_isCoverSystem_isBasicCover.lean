-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isCoverSystem_isBasicCover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:54:34.072431+00:00
-- url     : https://prove2.me/submissions/f8528cd9-8a89-484c-a943-5181a15de1bf

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_AffineVanishing
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_basicOpen
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_mem


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
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
universe w w' u
variable {X : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution :
    IsCoverSystem (X := X.toTopCat) IsAffineOpen (fun {κ} V U => IsBasicCover (κ := κ) V U) where
  iSup_eq V κ U hU := hU.2.choose_spec.2
  inter_mem V κ U hU n i := by
    obtain ⟨hV, h, hUh, -⟩ := hU
    have : U = fun a => X.basicOpen (h a) := funext hUh
    subst this
    rw [inter_basicOpen h i]
    exact hV.basicOpen _
  exists_refinement V hV O hO := by
    choose f hfO hxf using fun x : V => hV.exists_basicOpen_le (V := O x) ⟨x.1, hO x⟩ x.2
    obtain ⟨fs, hfs⟩ := hV.isCompact.elim_finite_subcover
      (fun x : V => (X.basicOpen (f x) : Set X)) (fun x => (X.basicOpen (f x)).isOpen)
      (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxf _⟩)
    refine ⟨{x // x ∈ fs}, inferInstance, fun a => X.basicOpen (f a.1),
      ⟨hV, fun a => f a.1, fun a => rfl, ?_⟩, fun a => ⟨a.1, hfO a.1⟩⟩
    refine le_antisymm (iSup_le fun a => X.basicOpen_le _) ?_
    intro y hy
    have := hfs hy
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hx, hyx⟩ := this
    exact Opens.mem_iSup.2 ⟨⟨x, hx⟩, hyx⟩
end GroundTheory.Arith.SchemeCoh
