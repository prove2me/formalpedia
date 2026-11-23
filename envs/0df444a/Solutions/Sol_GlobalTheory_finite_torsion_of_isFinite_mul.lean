-- Prove2me | solution 1 for GlobalTheory.finite_torsion_of_isFinite_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:38.815495+00:00
-- url     : https://prove2.me/submissions/cc9f7dba-406f-43aa-8646-f39c9ea3f805

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K : Type) [Field K] [IsAlgClosed K]
    (P : PolAV (Spec (CommRingCat.of K))) (N : ℕ) [IsFinite (mulA P.A N).left] :
    Finite {x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A // x ^ N = 1} := by
  haveI := P.isAb.proper
  let p := IsLocalRing.closedPoint K
  let o : P.A.left := (1 : baseOver (Spec (CommRingCat.of K)) ⟶ P.A).left p
  have hfib := Scheme.Hom.finite_preimage_singleton (mulA P.A N).left o
  haveI := hfib.to_subtype
  refine Finite.of_injective (β := (mulA P.A N).left ⁻¹' {o}) (fun x => ⟨x.1.left p, ?_⟩) ?_
  · have h : x.1 ≫ mulA P.A N = 1 := by rw [mulA, MonObj.comp_pow, Category.comp_id, x.2]
    change (x.1 ≫ mulA P.A N).left p = o
    rw [h]
  · intro x y hxy
    refine Subtype.ext (Over.OverMorphism.ext ?_)
    exact ext_of_apply_closedPoint_eq P.A.hom (Over.w x.1) (Over.w y.1) (congrArg Subtype.val hxy)
end GlobalTheory
