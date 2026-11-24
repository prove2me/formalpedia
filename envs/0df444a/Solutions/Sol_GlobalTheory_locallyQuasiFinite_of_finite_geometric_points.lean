-- Prove2me | solution 1 for GlobalTheory.locallyQuasiFinite_of_finite_geometric_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:19:09.493109+00:00
-- url     : https://prove2.me/submissions/6d39fa3c-8312-4e89-b831-06c955a0755c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LocallyQuasiFiniteOfFiniteGeometricPoints
import Theorems.Thm_GlobalTheory_finite_of_finite_sections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Y : Scheme.{0}} (f : X ⟶ Y)
    [LocallyOfFiniteType f]
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
      Finite {x : Spec (.of Ω) ⟶ X // x ≫ f = y}) : LocallyQuasiFinite f := by
  refine LocallyQuasiFinite.of_finite_preimage_singleton f fun y ↦ ?_
  let Ω := AlgebraicClosure (Y.residueField y)
  let y' : Spec (.of Ω) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫ Y.fromSpecResidueField y
  have hy : y ∈ Set.range y' := by
    obtain ⟨z⟩ : Nonempty ↥(Spec (.of Ω)) := inferInstance
    exact ⟨z, (Scheme.Hom.comp_apply _ _ z).trans (Scheme.fromSpecResidueField_apply y _)⟩
  clear_value y'
  have := h Ω y'
  have hP : Finite ↥(pullback f y') := by
    refine finite_of_finite_sections (pullback.snd f y') ?_
    refine Finite.of_injective (β := {x : Spec (.of Ω) ⟶ X // x ≫ f = y'})
      (fun x ↦ ⟨x.1 ≫ pullback.fst f y', by
        rw [Category.assoc, pullback.condition, ← Category.assoc, x.2, Category.id_comp]⟩) ?_
    intro a b hab
    apply Subtype.ext
    apply pullback.hom_ext
    · exact congrArg Subtype.val hab
    · rw [a.2, b.2]
  refine (Set.finite_range (pullback.fst f y')).subset ?_
  rw [Scheme.Pullback.range_fst]
  exact Set.preimage_mono (Set.singleton_subset_iff.mpr hy)
end GlobalTheory
