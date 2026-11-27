-- Prove2me | solution 1 for GlobalTheory.T.irreducibleSpace_pullback_affine_open_of_isDomain_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:34:13.990733+00:00
-- url     : https://prove2.me/submissions/c3dcca3f-bf96-4677-849c-229f528e574a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpacePullbackAffineOpenOfIsDomainTens
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpacePullbackAffineOpenOfIsDomainTensStatement
import Theorems.Thm_GlobalTheory_GeomIrr_irreducibleSpace_pullback_of_isDomain_tensor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] {X : Scheme.{0}} (g : X ⟶ Sp F) (V : X.Opens), IsAffineOpen V →
    ∀ (k : Type) [Field k] (f : F →+* k),
    letI : Algebra F Γ(X, V) :=
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ g.appTop ≫ X.presheaf.map (homOfLE le_top).op).hom.toAlgebra
    letI : Algebra F k := f.toAlgebra
    IsDomain (k ⊗[F] Γ(X, V)) → IrreducibleSpace ↑(pullback (V.ι ≫ g) (spMap f)) := by
  first | exact @GlobalTheory.GeomIrr.irreducibleSpace_pullback_of_isDomain_tensor | exact GlobalTheory.GeomIrr.irreducibleSpace_pullback_of_isDomain_tensor | (intros; apply GlobalTheory.GeomIrr.irreducibleSpace_pullback_of_isDomain_tensor <;> assumption)
end _root_.GlobalTheory.T
