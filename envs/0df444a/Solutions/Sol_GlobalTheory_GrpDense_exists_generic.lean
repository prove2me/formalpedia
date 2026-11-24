-- Prove2me | solution 1 for GlobalTheory.GrpDense.exists_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:53:47.927156+00:00
-- url     : https://prove2.me/submissions/1d6a5f6f-e07e-4249-b742-c1009388d044

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GrpDense
variable {Z U : Scheme.{0}} {j : U ⟶ Z}
namespace GlobalTheory.GrpDense
theorem _root_.solution [IsIntegral Z] [Nonempty U] (j : U ⟶ Z) [IsOpenImmersion j] :
    ∃ (W : Scheme.{0}) (k : W ⟶ U), QuasiCompact (k ≫ j) ∧ IsSchemeTheoreticallyDominant (k ≫ j) := by
  have : IsIntegral U := isIntegral_of_isOpenImmersion j
  refine ⟨Spec U.functionField, U.fromSpecStalk (genericPoint U), ?_, ?_⟩
  · constructor
    intro s _ _
    have : Subsingleton (Spec U.functionField) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum U.functionField))
    exact Set.subsingleton_of_subsingleton.isCompact
  · have hk : DenseRange (U.fromSpecStalk (genericPoint U)) := by
      refine Dense.mono ?_ (dense_iff_closure_eq.mpr (isGenericPoint_def.mp (genericPoint_spec U)))
      rintro _ rfl
      rw [Scheme.range_fromSpecStalk]
      exact specializes_refl _
    have hj : DenseRange j :=
      (Scheme.Hom.isOpenEmbedding j).isOpen_range.dense (Set.range_nonempty _)
    have : IsDominant (U.fromSpecStalk (genericPoint U)) := ⟨hk⟩
    have : IsDominant j := ⟨hj⟩
    exact IsSchemeTheoreticallyDominant.of_isDominant _
end GlobalTheory.GrpDense
