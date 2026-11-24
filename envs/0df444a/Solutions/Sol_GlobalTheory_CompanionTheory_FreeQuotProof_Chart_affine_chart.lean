-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotProof.Chart.affine_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:11:45.998184+00:00
-- url     : https://prove2.me/submissions/20024e80-08b8-4fe1-983a-3ba248388507

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsQuotientSchemeOfFiniteFlatSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FreeActionAffineChart
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Chart_exists_hopf
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Chart_exists_alg
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Chart_exists_rightCoaction
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Chart_rightCoaction_counit
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Chart_rightCoaction_assoc
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Chart_rightCoaction_free
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Chart_isIso_lift_spec
import Theorems.Thm_GlobalTheory_AffineQuotient_isPushout_equalizer
import Theorems.Thm_GlobalTheory_HopfQuot_ev_tmul
import Theorems.Thm_GlobalTheory_HopfQuot_finite_faithfullyFlat_ker
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
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Chart
theorem _root_.solution (H Z : Over (Spec (CommRingCat.of R))) [GrpObj H] [ModObj H Z]
    (hH : IsFiniteLocallyFree H.hom) (hf : IsFreeAction H Z) [IsAffine Z.left] :
    ∃ (Y : Scheme.{0}) (q : Z.left ⟶ Y), IsAffine Y ∧ IsFinite q ∧ Flat q ∧
      LocallyOfFinitePresentation q ∧ Surjective q ∧
      IsPullback (γ[H, Z] : H ⊗ Z ⟶ Z).left (snd H Z).left q q := by
  obtain ⟨Λ, _, _, _, _, e, _⟩ := exists_hopf H hH
  obtain ⟨B, _, _, ⟨v⟩⟩ := exists_alg Z
  obtain ⟨ρ, hρ⟩ := exists_rightCoaction e.hom v
  have hs := rightCoaction_free e.hom v.hom ρ hρ hf
  obtain ⟨h₁, -, h₃, h₄⟩ := GlobalTheory.HopfQuot.finite_faithfullyFlat_ker ρ
    (rightCoaction_assoc e.hom v.hom ρ hρ) (rightCoaction_counit e.hom v.hom ρ hρ) hs
  let C : Subring B := ρ.toRingHom.eqLocus (includeLeft : B →ₐ[R] B ⊗[R] Λ).toRingHom
  let c : CommRingCat.of C ⟶ CommRingCat.of B := CommRingCat.ofHom C.subtype
  have po : IsPushout c c (CommRingCat.ofHom ρ.toRingHom)
      (CommRingCat.ofHom (includeLeft : B →ₐ[R] B ⊗[R] Λ).toRingHom) :=
    isPushout_equalizer ρ _ hs h₄
  have pb := isPullback_SpecMap_of_isPushout _ _ _ _ po
  have hk := isIso_lift_spec (e ≪≫ invIso H) v
  set k := lift (specHom (includeRight : Λ →ₐ[R] B ⊗[R] Λ) ≫ (e ≪≫ invIso H).hom)
      (specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ) ≫ v.hom) with hkdef
  have hk₁ : k ≫ γ[H, Z] = specHom ρ ≫ v.hom := by
    rw [hρ, Hom.smul_def, hkdef, Hom.inv_def]
    simp [invIso]
  have hk₂ : k ≫ snd H Z = specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ) ≫ v.hom := by
    rw [hkdef, lift_snd]
  let q : Z.left ⟶ Spec (CommRingCat.of C) := v.inv.left ≫ Spec.map c
  have pb' : IsPullback (γ[H, Z] : H ⊗ Z ⟶ Z).left (snd H Z).left q q := by
    refine pb.of_iso ((Over.forget _).mapIso (asIso k)) ((Over.forget _).mapIso v)
      ((Over.forget _).mapIso v) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact congr(($hk₁).left).symm
    · exact congr(($hk₂).left).symm
    · simp [q]
    · simp [q]
  have f₁ : IsFinite (Spec.map c) := (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 h₁)
  have f₂ : Flat (Spec.map c) ∧ Surjective (Spec.map c) :=
    (flat_and_surjective_SpecMap_iff _).2 (RingHom.faithfullyFlat_algebraMap_iff.2 h₃)
  have := f₂.1
  have := f₂.2
  have hq₂ : Flat q := by dsimp [q]; infer_instance
  have hq₃ : Surjective q := by dsimp [q]; infer_instance
  have hq₄ : QuasiCompact q := by dsimp [q]; infer_instance
  refine ⟨_, q, inferInstance, by dsimp [q]; infer_instance, hq₂, ?_, hq₃, pb'⟩
  have h3 := hH.2.2
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFinitePresentation)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) pb'.flip ⟨⟨hq₃, hq₂⟩, hq₄⟩ ?_
  exact MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) H.hom Z.hom h3
end GlobalTheory.CompanionTheory.FreeQuotProof.Chart
