-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotProof.Chart.specHom_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:36:01.532371+00:00
-- url     : https://prove2.me/submissions/d90a5570-1504-4f72-af28-67abe55f943f

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsQuotientSchemeOfFiniteFlatSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FreeActionAffineChart
import Theorems.Thm_GlobalTheory_AffineQuotient_specHom_left


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
variable {Λ B : Type} [CommRing Λ] [HopfAlgebra R Λ] [CommRing B] [Algebra R B]
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Chart
theorem _root_.solution {S T : Type} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (t : specOver R T ⟶ specOver R S) : ∃ φ : S →ₐ[R] T, specHom φ = t := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective t.left
  have h : CommRingCat.ofHom (algebraMap R S) ≫ φ = CommRingCat.ofHom (algebraMap R T) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ]
    exact Over.w t
  refine ⟨⟨φ.hom, fun r ↦ congr($h r)⟩, ?_⟩
  ext1
  rw [specHom_left]
  exact hφ
end GlobalTheory.CompanionTheory.FreeQuotProof.Chart
