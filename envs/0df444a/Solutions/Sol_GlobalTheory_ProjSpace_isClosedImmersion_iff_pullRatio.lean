-- Prove2me | solution 1 for GlobalTheory.ProjSpace.isClosedImmersion_iff_pullRatio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:16.591926+00:00
-- url     : https://prove2.me/submissions/24567c18-b731-489f-b1e4-b7dd5909a85b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Theorems.Thm_GlobalTheory_ProjSpace_surjective_appLE_chart_iff
import Theorems.Thm_GlobalTheory_ProjSpace_gradedMap_apply
import Theorems.Thm_GlobalTheory_ProjSpace_isAffineOpen_chart
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_appLinearBase_apply
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ProjSpace.gradedMap_apply
attribute [local simp] GlobalTheory.QCoh.Qcqs.appLinearBase_apply
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG)
open GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ProjSpace
variable {R : Type} [CommRing R] {N : ℕ} {Y Z : Scheme.{0}}
namespace GlobalTheory.ProjSpace
theorem _root_.solution (φ : Y ⟶ PSpace R N) {U : Fin (N + 1) → Y.Opens}
    (hU : ∀ i, φ ⁻¹ᵁ chart R N i = U i) :
    IsClosedImmersion φ ↔ ∀ i, IsAffineOpen (U i) ∧ Function.Surjective
      (eval₂Hom (baseRingHom (φ ≫ PSpace.str R N) (U i)).hom (pullRatio φ (U i) i (hU i).ge)) := by
  obtain rfl : (fun i => φ ⁻¹ᵁ chart R N i) = U := funext hU
  have key : ∀ i, Function.Surjective (eval₂Hom (baseRingHom (φ ≫ PSpace.str R N) (φ ⁻¹ᵁ chart R N i)).hom
      (pullRatio φ (φ ⁻¹ᵁ chart R N i) i (hU i).ge)) ↔ Function.Surjective (φ.app (chart R N i)).hom :=
    fun i => by rw [← surjective_appLE_chart_iff, Scheme.Hom.app_eq_appLE]
  simp only [key]
  refine ⟨fun _ i => ⟨(isAffineOpen_chart R N i).preimage φ,
    φ.app_surjective _ (isAffineOpen_chart R N i)⟩, fun h => ?_⟩
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) _ (iSup_chart R N)).2 fun i => ?_
  have : IsAffine (chart R N i) := isAffineOpen_chart R N i
  have : IsAffine (φ ⁻¹ᵁ chart R N i) := (h i).1
  rw [MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (Arrow.isoMk (h i).1.isoSpec (isAffineOpen_chart R N i).isoSpec
      (Scheme.Opens.toSpecΓ_naturality φ _) :
      Arrow.mk (φ ∣_ chart R N i) ≅ Arrow.mk (Spec.map (φ.app (chart R N i))))]
  exact IsClosedImmersion.spec_of_surjective _ (h i).2
end GlobalTheory.ProjSpace
