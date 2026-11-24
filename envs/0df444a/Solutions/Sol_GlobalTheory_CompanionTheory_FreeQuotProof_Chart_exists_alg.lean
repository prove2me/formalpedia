-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotProof.Chart.exists_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:33:18.87811+00:00
-- url     : https://prove2.me/submissions/b50c3197-7a3d-4f02-992c-cf7e48a98984

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsQuotientSchemeOfFiniteFlatSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FreeActionAffineChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
open GlobalTheory.AffineQuotient
open TensorProduct Algebra.TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.FreeQuotProof.Chart
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Chart
theorem _root_.solution (Z : Over (Spec (CommRingCat.of R))) [IsAffine Z.left] :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B), Nonempty (specOver R B ≅ Z) := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.left.isoSpec.inv ≫ Z.hom)
  refine ⟨Γ(Z.left, ⊤), inferInstance, φ.hom.toAlgebra, ⟨Over.isoMk Z.left.isoSpec.symm ?_⟩⟩
  exact hφ.symm
end GlobalTheory.CompanionTheory.FreeQuotProof.Chart
