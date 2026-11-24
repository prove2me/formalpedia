-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.sheaf_eq_of_locally
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:50.234175+00:00
-- url     : https://prove2.me/submissions/6f38b6b8-b2f5-4e21-a0c4-82e90c1f355a

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ModulesTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory Opposite TensorProduct AlgebraicGeometry TopologicalSpace
universe u
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
variable {X : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {C : Type*} [Category.{u} C] {FC : C → C → Type*} {CC : C → Type u}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{u} C FC]
    [Limits.HasLimitsOfSize.{u, u} C] [(forget C).ReflectsIsomorphisms]
    [Limits.PreservesLimitsOfSize.{u, u} (forget C)]
    {T : TopCat.{u}} (F : TopCat.Sheaf C T) {V : Opens T} (s t : ToType (F.1.obj (op V)))
    (h : ∀ x ∈ V, ∃ (W : Opens T) (i : W ≤ V), x ∈ W ∧
      F.1.map (homOfLE i).op s = F.1.map (homOfLE i).op t) : s = t := by
  choose W i hx h using h
  refine F.eq_of_locally_eq' (U := fun x : V => W x.1 x.2) V (fun x => homOfLE (i _ _)) ?_ s t
    (fun x => h _ _)
  intro x hxV
  exact Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _ _⟩
end GroundTheory.Arith.SchemeCoh
