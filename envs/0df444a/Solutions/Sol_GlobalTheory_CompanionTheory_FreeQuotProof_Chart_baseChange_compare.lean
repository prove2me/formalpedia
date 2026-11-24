-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotProof.Chart.baseChange_compare
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:51:03.367641+00:00
-- url     : https://prove2.me/submissions/6e3f91c7-75ee-4fae-ab2b-062721fa8869

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsQuotientSchemeOfFiniteFlatSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FreeActionAffineChart
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Chart_isIso_pullback_fst
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
theorem _root_.solution [Mono j] (G Z : Over S) [GrpObj G] [ModObj G Z] (z : Z.left ⟶ S')
    (hz : z ≫ j = Z.hom) :
    letI := Functor.grpObjObj (F := Over.pullback j) (G := G)
    letI := modObjObj (Over.pullback j) G Z
    IsIso (pullback.fst Z.hom j) ∧
      ∃ e : (((Over.pullback j).obj G) ⊗ ((Over.pullback j).obj Z)).left ≅ (G ⊗ Z).left,
      e.hom ≫ (γ[G, Z] : G ⊗ Z ⟶ Z).left =
        (γ[(Over.pullback j).obj G, (Over.pullback j).obj Z] :
          ((Over.pullback j).obj G) ⊗ ((Over.pullback j).obj Z) ⟶ (Over.pullback j).obj Z).left ≫
          pullback.fst Z.hom j ∧
      e.hom ≫ (snd G Z).left =
        (snd ((Over.pullback j).obj G) ((Over.pullback j).obj Z)).left ≫ pullback.fst Z.hom j := by
  refine ⟨isIso_pullback_fst j Z z hz, ?_⟩
  have iW : IsIso (pullback.fst (G ⊗ Z).hom j) :=
    isIso_pullback_fst j (G ⊗ Z) ((snd G Z).left ≫ z)
      (by rw [Category.assoc, hz]; exact Over.w (snd G Z))
  have nat : ∀ {A B : Over S} (f : A ⟶ B), ((Over.pullback j).map f).left ≫ pullback.fst B.hom j =
      pullback.fst A.hom j ≫ f.left := by
    intro A B f
    simp
  refine ⟨(Over.forget _).mapIso (Functor.Monoidal.μIso (Over.pullback j) G Z) ≪≫
    asIso (pullback.fst (G ⊗ Z).hom j), ?_, ?_⟩
  · change (Functor.LaxMonoidal.μ (Over.pullback j) G Z).left ≫ pullback.fst (G ⊗ Z).hom j ≫ _ = (Functor.LaxMonoidal.μ (Over.pullback j) G Z ≫ (Over.pullback j).map γ[G, Z]).left ≫ _
    rw [← nat, Over.comp_left, Category.assoc]
  · rw [← Functor.Monoidal.μ_snd (Over.pullback j) G Z]
    change (Functor.LaxMonoidal.μ (Over.pullback j) G Z).left ≫ pullback.fst (G ⊗ Z).hom j ≫ _ = (Functor.LaxMonoidal.μ (Over.pullback j) G Z ≫ (Over.pullback j).map (snd G Z)).left ≫ _
    rw [← nat, Over.comp_left, Category.assoc]
end GlobalTheory.CompanionTheory.FreeQuotProof.Chart
