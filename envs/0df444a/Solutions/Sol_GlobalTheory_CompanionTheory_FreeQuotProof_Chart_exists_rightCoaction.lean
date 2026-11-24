-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotProof.Chart.exists_rightCoaction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:54:03.883973+00:00
-- url     : https://prove2.me/submissions/f21c28d3-ae10-42bf-94d4-bd873cf5ebc8

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsQuotientSchemeOfFiniteFlatSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FreeActionAffineChart
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Chart_specHom_surjective
import Theorems.Thm_GlobalTheory_HopfQuot_ev_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HopfQuot.ev_tmul



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
variable {H Z : Over (Spec (CommRingCat.of R))} [GrpObj H] [ModObj H Z]
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Chart
theorem _root_.solution (i : specOver R Λ ⟶ H) (v : specOver R B ≅ Z) :
    ∃ ρ : B →ₐ[R] B ⊗[R] Λ, specHom ρ ≫ v.hom =
      (specHom (includeRight : Λ →ₐ[R] B ⊗[R] Λ) ≫ i)⁻¹ •
        (specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ) ≫ v.hom) := by
  obtain ⟨ρ, hρ⟩ := specHom_surjective (((specHom (includeRight : Λ →ₐ[R] B ⊗[R] Λ) ≫ i)⁻¹ •
        (specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ) ≫ v.hom)) ≫ v.inv)
  exact ⟨ρ, by simp [hρ]⟩
end GlobalTheory.CompanionTheory.FreeQuotProof.Chart
