-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotProof.Chart.free_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:33:22.700028+00:00
-- url     : https://prove2.me/submissions/b22db9ce-c666-4185-9e14-b26d0eb6bfe4

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsQuotientSchemeOfFiniteFlatSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FreeActionAffineChart
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
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Chart
theorem _root_.solution {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X]
    (h : Mono (lift (γ[G, X] : G ⊗ X ⟶ X) (snd G X))) : IsFreeAction G X := by
  intro T g x e
  have e₁ : lift g x ≫ lift (γ[G, X] : G ⊗ X ⟶ X) (snd G X) =
      lift (1 : T ⟶ G) x ≫ lift (γ[G, X] : G ⊗ X ⟶ X) (snd G X) := by
    rw [comp_lift, comp_lift, ← Hom.smul_def, ← Hom.smul_def, e, _root_.one_smul, lift_snd, lift_snd]
  have := (cancel_mono _).1 e₁
  simpa using congr($this ≫ fst G X)
end GlobalTheory.CompanionTheory.FreeQuotProof.Chart
