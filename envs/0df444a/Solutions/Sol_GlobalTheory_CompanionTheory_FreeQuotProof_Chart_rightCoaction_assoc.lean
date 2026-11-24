-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotProof.Chart.rightCoaction_assoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:35:58.224545+00:00
-- url     : https://prove2.me/submissions/8e1df8b4-7d30-4cf8-a68e-aa2f1e402b46

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsQuotientSchemeOfFiniteFlatSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpecHomCompCoaction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FreeActionAffineChart
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Chart_specHom_comp_rightCoaction
import Theorems.Thm_GlobalTheory_AffineQuotient_specHom_injective
import Theorems.Thm_GlobalTheory_AffineQuotient_specHom_lift_comul
import Theorems.Thm_GlobalTheory_HopfQuot_ev_tmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
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
variable (i : specOver R Λ ⟶ H) (v : specOver R B ⟶ Z) (ρ : B →ₐ[R] B ⊗[R] Λ)
  (hρ : specHom ρ ≫ v = (specHom (includeRight : Λ →ₐ[R] B ⊗[R] Λ) ≫ i)⁻¹ •
    (specHom (includeLeft : B →ₐ[R] B ⊗[R] Λ) ≫ v))
include hρ
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Chart
theorem _root_.solution [IsMonHom i] [Mono v] (b : B) :
    TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ (ρ b)) =
      (Coalgebra.comul (R := R) (A := Λ)).lTensor B (ρ b) := by
  let l : B →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) := includeLeft
  let r₁ : Λ →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) := includeRight.comp includeLeft
  let r₂ : Λ →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) := includeRight.comp includeRight
  let φ₀ : B ⊗[R] Λ →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) := Algebra.TensorProduct.lift l r₁ fun _ _ ↦ .all _ _
  let φ₁ : B ⊗[R] Λ →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) :=
    Algebra.TensorProduct.lift (φ₀.comp ρ) r₂ fun _ _ ↦ .all _ _
  let φ₂ : B ⊗[R] Λ →ₐ[R] B ⊗[R] (Λ ⊗[R] Λ) :=
    Algebra.TensorProduct.lift l ((Algebra.TensorProduct.lift r₁ r₂ fun _ _ ↦ .all _ _).comp
      (Bialgebra.comulAlgHom R Λ)) fun _ _ ↦ .all _ _
  have h₀ := specHom_comp_rightCoaction i v ρ hρ φ₀
  have h₁ := specHom_comp_rightCoaction i v ρ hρ φ₁
  have h₂ := specHom_comp_rightCoaction i v ρ hρ φ₂
  rw [lift_comp_includeRight', lift_comp_includeLeft] at h₀ h₁ h₂
  have hm : specHom ((Algebra.TensorProduct.lift r₁ r₂ fun _ _ ↦ .all _ _).comp
      (Bialgebra.comulAlgHom R Λ)) ≫ i = (specHom r₁ ≫ i) * (specHom r₂ ≫ i) := by
    rw [specHom_lift_comul, MonObj.mul_comp]
  rw [h₀, ← mul_smul, ← mul_inv_rev, ← hm, ← h₂, cancel_mono] at h₁
  have h : φ₂ (ρ b) = φ₁ (ρ b) := congr($(specHom_injective h₁.symm) b)
  have e₁ (z : B ⊗[R] Λ) :
      TensorProduct.assoc R B Λ Λ (ρ.toLinearMap.rTensor Λ z) = φ₁ z := by
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, φ₁,
        Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply]
      generalize ρ x = w
      induction w with
      | zero => simp
      | add x y hx hy => simp only [map_add, add_tmul, add_mul, hx, hy]
      | tmul x y => simp [φ₀, l, r₁, r₂]
  have e₂ (z : B ⊗[R] Λ) : (Coalgebra.comul (R := R) (A := Λ)).lTensor B z = φ₂ z := by
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
      simp only [LinearMap.lTensor_tmul, φ₂, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
        Bialgebra.comulAlgHom_apply]
      generalize Coalgebra.comul (R := R) y = w
      induction w with
      | zero => simp
      | add x y hx hy => simp only [map_add, tmul_add, mul_add, hx, hy]
      | tmul x y => simp [l, r₁, r₂]
  rw [e₁, e₂, h]
end GlobalTheory.CompanionTheory.FreeQuotProof.Chart
