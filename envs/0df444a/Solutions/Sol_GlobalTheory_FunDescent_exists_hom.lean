-- Prove2me | solution 1 for GlobalTheory.FunDescent.exists_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:33.862153+00:00
-- url     : https://prove2.me/submissions/f43f47fc-f95c-4e2d-9d15-8370dabca384

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FunDescent
namespace GlobalTheory.FunDescent
theorem _root_.solution {Z : Scheme.{0}} (f : Γ(Z, ⊤)) :
    ∃ g : Z ⟶ Spec (CommRingCat.of (Polynomial ℤ)), g.appTop.hom coord = f := by
  let φ : CommRingCat.of (Polynomial ℤ) ⟶ Γ(Z, ⊤) :=
    CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom _) f)
  refine ⟨ΓSpec.adjunction.homEquiv Z (Opposite.op _) φ.op, ?_⟩
  have := congrArg (fun ψ => ψ.hom Polynomial.X) (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ)
  refine this.trans ?_
  simp [φ]
end GlobalTheory.FunDescent
