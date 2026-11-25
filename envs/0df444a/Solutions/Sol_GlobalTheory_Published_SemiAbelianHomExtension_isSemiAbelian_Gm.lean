-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.isSemiAbelian_Gm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:18:09.790006+00:00
-- url     : https://prove2.me/submissions/84bc828e-a415-45d5-a720-33e9e1261071

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_smooth_splitTorusAff
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_geometricallyConnected_splitTorusAff
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_isAbelianScheme_unit
import Theorems.Thm_GlobalTheory_ExtUnique_splitTorusAff_flat_and_isSeparated
import Theorems.Thm_GlobalTheory_splitTorus_baseChange


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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S]
open scoped TensorProduct
namespace GlobalTheory.Published.SemiAbelianHomExtension
theorem _root_.solution (S : Scheme.{0}) : IsSemiAbelian (Gm S) := by
  have h₁ := smooth_splitTorusAff
  have h₂ := geometricallyConnected_splitTorusAff
  have h₃ := (splitTorusAff_flat_and_isSeparated ZU.{0} (ULift.{0} ℤ)).2
  have h₄ : QuasiCompact (splitTorusAff ZU.{0} (ULift.{0} ℤ)).hom := by
    change QuasiCompact (Spec.map _); infer_instance
  have h₅ : IsCommMonObj (splitTorusAff ZU.{0} (ULift.{0} ℤ)) := by
    have : Coalgebra.IsCocomm ZU.{0} (torusRing ZU.{0} (ULift.{0} ℤ)) :=
      inferInstanceAs (Coalgebra.IsCocomm ZU.{0} (AddMonoidAlgebra ZU.{0} (ULift.{0} ℤ)))
    infer_instance
  have sm : ∀ S : Scheme.{0}, Smooth (Gm S).hom := fun S =>
    inferInstanceAs (Smooth (pullback.snd _ (toZ S)))
  have gc : ∀ S : Scheme.{0}, GeometricallyConnected (Gm S).hom := fun S =>
    inferInstanceAs (GeometricallyConnected (pullback.snd _ (toZ S)))
  have qc : ∀ S : Scheme.{0}, QuasiCompact (Gm S).hom := fun S =>
    inferInstanceAs (QuasiCompact (pullback.snd _ (toZ S)))
  refine ⟨inferInstanceAs (IsCommMonObj ((Over.pullback (toZ S)).obj _)), sm S,
    inferInstanceAs (IsSeparated (pullback.snd _ (toZ S))), qc S, gc S, fun Ω _ _ p => ?_⟩
  obtain ⟨e, he, -⟩ := splitTorus_baseChange S _ p (ULift.{0} ℤ)
  refine ⟨torusExtOfIso e
    { X := ULift.{0} ℤ
      B := 𝟙_ _
      isAbelian := isAbelianScheme_unit _
      q := toUnit _
      q_hom := inferInstance
      q_flat := ?_
      q_surjective := ?_
      q_quasiCompact := ?_
      i := 𝟙 _
      i_hom := inferInstance
      isKernel := ?_ }⟩
  · have := sm (Spec (.of Ω))
    exact inferInstanceAs (Flat (Gm (Spec (.of Ω))).hom)
  · have := gc (Spec (.of Ω))
    exact inferInstanceAs (Surjective (Gm (Spec (.of Ω))).hom)
  · exact qc _
  · have : IsIso (η : 𝟙_ (Over (Spec (.of Ω))) ⟶ 𝟙_ _) := by
      rw [toUnit_unique η (𝟙 _)]; infer_instance
    exact IsPullback.of_horiz_isIso ⟨toUnit_unique _ _⟩
end GlobalTheory.Published.SemiAbelianHomExtension
