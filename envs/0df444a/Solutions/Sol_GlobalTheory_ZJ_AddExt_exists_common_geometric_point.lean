-- Prove2me | solution 1 for GlobalTheory.ZJ.AddExt.exists_common_geometric_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:31:50.143607+00:00
-- url     : https://prove2.me/submissions/c4a8da00-bddc-46a2-8569-be3152a4c701

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAddExtension
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.AddExt
namespace GlobalTheory.ZJ.AddExt
theorem _root_.solution {X S S' : Scheme.{0}} (a : S ⟶ X) (a' : S' ⟶ X) (s : S) (s' : S')
    (h : a s = a' s') : ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (u : Sp K ⟶ S) (u' : Sp K ⟶ S'),
      u ≫ a = u' ≫ a' ∧ (∀ x, u x = s) ∧ (∀ x, u' x = s') := by
  obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback s s' h
  let k := (pullback a a').residueField z
  let w : Sp (AlgebraicClosure k) ⟶ pullback a a' :=
    spMap (algebraMap k (AlgebraicClosure k)) ≫ (pullback a a').fromSpecResidueField z
  have hw : ∀ x, w x = z := fun x => by
    rw [← Set.mem_singleton_iff, ← Scheme.range_fromSpecResidueField]
    exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  refine ⟨AlgebraicClosure k, inferInstance, inferInstance, w ≫ pullback.fst _ _, w ≫ pullback.snd _ _,
    by rw [Category.assoc w, Category.assoc w, pullback.condition], fun x => ?_, fun x => ?_⟩
  · rw [Scheme.Hom.comp_apply, hw, hz]
  · rw [Scheme.Hom.comp_apply, hw, hz']
end GlobalTheory.ZJ.AddExt
