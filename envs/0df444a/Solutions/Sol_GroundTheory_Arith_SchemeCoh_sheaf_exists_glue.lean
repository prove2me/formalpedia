-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.sheaf_exists_glue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:50.47928+00:00
-- url     : https://prove2.me/submissions/9194c727-8f77-4d2b-a02e-e5a3f300963b

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
    {T : TopCat.{u}} (F : TopCat.Sheaf C T) {V : Opens T} {ι : Type u} (W : ι → Opens T)
    (i : ∀ a, W a ≤ V) (hcov : ∀ x ∈ V, ∃ a, x ∈ W a) (sf : ∀ a, ToType (F.1.obj (op (W a))))
    (hsf : ∀ a b, F.1.map (homOfLE (inf_le_left : W a ⊓ W b ≤ W a)).op (sf a) =
      F.1.map (homOfLE (inf_le_right : W a ⊓ W b ≤ W b)).op (sf b)) :
    ∃ s : ToType (F.1.obj (op V)), ∀ a, F.1.map (homOfLE (i a)).op s = sf a := by
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' W V (fun a => homOfLE (i a))
    (fun x hxV => Opens.mem_iSup.2 (hcov x hxV)) sf hsf
  exact ⟨s, hs⟩
end GroundTheory.Arith.SchemeCoh
