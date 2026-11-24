-- Prove2me | solution 1 for GlobalTheory.TangentCrit.formallyUnramified_of_tangent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:14.549805+00:00
-- url     : https://prove2.me/submissions/9b9c7469-b0f9-4e1a-b22e-079539cefb0e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.TangentCrit
open AlgebraicGeometry CategoryTheory Limits
universe u
namespace GlobalTheory.TangentCrit
theorem _root_.solution {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (H : ∀ (k : Type u) [Field k] [IsAlgClosed k] (w : Spec (.of (DualNumber k)) ⟶ X),
      w ≫ f = dualBase k ≫ dualPt k ≫ w ≫ f → w = dualBase k ≫ dualPt k ≫ w) :
    FormallyUnramified f := by
  refine ⟨fun {U} hU {V} hV e => formallyUnramified_of_dual_const _
    (f.finiteType_appLE hU hV e).essFiniteType fun k _ _ φ hφ b => ?_⟩
  have := H k (Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec) (by
    simp only [Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV e, ← Spec.map_comp_assoc]
    congr 2
    ext a
    · rfl
    · exact hφ a)
  simp only [← Spec.map_comp_assoc] at this
  rw [cancel_mono, Spec.map_inj] at this
  exact congrArg TrivSqZeroExt.snd congr($this b)
end GlobalTheory.TangentCrit
