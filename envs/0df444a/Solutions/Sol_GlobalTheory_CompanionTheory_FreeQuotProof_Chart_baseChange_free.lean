-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotProof.Chart.baseChange_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:52:43.918183+00:00
-- url     : https://prove2.me/submissions/26597255-71ab-4cba-a26a-ea7ba5b72672

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsQuotientSchemeOfFiniteFlatSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FreeActionAffineChart
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Chart_mono_of_free
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Chart_free_of_mono
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
variable {S S' : Scheme.{0}} (j : S' ⟶ S)
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Chart
theorem _root_.solution (G Z : Over S) [GrpObj G] [ModObj G Z] (hf : IsFreeAction G Z) :
    letI := Functor.grpObjObj (F := Over.pullback j) (G := G)
    letI := modObjObj (Over.pullback j) G Z
    IsFreeAction ((Over.pullback j).obj G) ((Over.pullback j).obj Z) := by
  letI := Functor.grpObjObj (F := Over.pullback j) (G := G)
  letI := modObjObj (Over.pullback j) G Z
  apply free_of_mono
  have := mono_of_free G Z hf
  have hm : Mono ((Over.pullback j).map (lift (γ[G, Z] : G ⊗ Z ⟶ Z) (snd G Z))) := inferInstance
  have key : Functor.LaxMonoidal.μ (Over.pullback j) G Z ≫
        (Over.pullback j).map (lift (γ[G, Z] : G ⊗ Z ⟶ Z) (snd G Z)) =
      lift (γ[(Over.pullback j).obj G, (Over.pullback j).obj Z] :
          ((Over.pullback j).obj G) ⊗ ((Over.pullback j).obj Z) ⟶ (Over.pullback j).obj Z)
        (snd _ _) ≫ Functor.LaxMonoidal.μ (Over.pullback j) Z Z := by
    rw [← cancel_mono (Functor.OplaxMonoidal.δ (Over.pullback j) Z Z)]
    simp only [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, Category.assoc, Category.assoc, Functor.OplaxMonoidal.δ_fst, ← Functor.map_comp,
        lift_fst]
      rfl
    · rw [lift_snd, Category.assoc, Category.assoc, Functor.OplaxMonoidal.δ_snd, ← Functor.map_comp,
        lift_snd, Functor.Monoidal.μ_snd]
  have : Mono (lift (γ[(Over.pullback j).obj G, (Over.pullback j).obj Z] :
          ((Over.pullback j).obj G) ⊗ ((Over.pullback j).obj Z) ⟶ (Over.pullback j).obj Z)
        (snd _ _) ≫ Functor.LaxMonoidal.μ (Over.pullback j) Z Z) := by
    rw [← key]; infer_instance
  exact mono_of_mono _ (Functor.LaxMonoidal.μ (Over.pullback j) Z Z)
end GlobalTheory.CompanionTheory.FreeQuotProof.Chart
