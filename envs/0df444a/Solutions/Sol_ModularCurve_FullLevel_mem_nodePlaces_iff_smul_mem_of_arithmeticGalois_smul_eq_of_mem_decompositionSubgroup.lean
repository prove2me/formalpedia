-- Prove2me | solution 1 for ModularCurve.FullLevel.mem_nodePlaces_iff_smul_mem_of_arithmeticGalois_smul_eq_of_mem_decompositionSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/6bb97539-14ec-53be-89c3-db77da6e92dd

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_mem_nodePlaces_iff_smul_mem_of_arithmeticGalois_smul_eq_of_mem_decompositionSubgroup

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open scoped Pointwise

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M'))

      (O : Subring ↥F₀) (S : Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ S ↔
        (∀ f : ↥F₀, f ∈ O → (f : ↥(fieldBar q M')) ∈ P.toValuationSubring) ∧
        (∀ (f : ↥F₀) (hfO : f ∈ O), ¬ IsUnit (⟨f, hfO⟩ : ↥O) →
          ∃ h : P.evalAt (f : ↥(fieldBar q M')) ∈ A, (⟨_, h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A)) →

      (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P.IsRational) →

    ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), τ ∈ A.decompositionSubgroup ℚ →
      (∀ f : ↥F₀, f ∈ O → ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (f : ↥(fieldBar q M')) = (f : ↥(fieldBar q M'))) →
      ∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P ∈ S ↔ ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • P ∈ S := by
  intro F₀ O S hS hrat

  have evalAt_smul : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))
      (x : ↥(fieldBar q M')) (hx : x ∈ P.toValuationSubring),
      (ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) σ • P).evalAt
        (ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) σ • x) = σ (P.evalAt x) := by
    intro σ P x hx
    set g := ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) σ with hg
    have hgx : g • x ∈ (g • P).toValuationSubring := by
      rw [AlgebraicCurve.SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]
      exact hx
    apply (g • P).algebraMap_residueField_injective
    rw [(g • P).algebraMap_evalAt (hrat _) hgx]
    have h1 := AlgebraicCurve.SemilinearAut.smulResidueRingEquiv_algebraMap g P (P.evalAt x)
    rw [P.algebraMap_evalAt (hrat P) hx] at h1
    have hb : AlgebraicCurve.SemilinearAut.baseAut g (P.evalAt x) = σ (P.evalAt x) := by rw [hg]; rfl
    rw [hb] at h1
    rw [← h1]
    show IsLocalRing.residue _ _ = IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _)
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    rfl

  have maxA : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ σ a ∈ A) →
      ∀ (e : AlgebraicClosure ℚ) (he : e ∈ A), (⟨e, he⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A →
        ∀ (he' : σ e ∈ A), (⟨σ e, he'⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    intro σ hσA e he hmax he'
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmax ⊢
    intro hu
    apply hmax
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
    have hw' : σ e * (w : AlgebraicClosure ℚ) = 1 := by
      have := congrArg Subtype.val hw
      exact this
    have hσe0 : σ e ≠ 0 := left_ne_zero_of_mul_eq_one hw'
    have he0 : e ≠ 0 := fun h => hσe0 (by rw [h, map_zero])
    have hwinv : (w : AlgebraicClosure ℚ) = σ e⁻¹ := by
      rw [map_inv₀]; exact (eq_inv_of_mul_eq_one_right hw')
    have hinvA : e⁻¹ ∈ A := (hσA _).2 (hwinv ▸ w.2)
    exact isUnit_iff_exists_inv.mpr ⟨⟨e⁻¹, hinvA⟩, Subtype.ext (mul_inv_cancel₀ he0)⟩

  have fwd : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), σ ∈ A.decompositionSubgroup ℚ →
      (∀ f : ↥F₀, f ∈ O → ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) σ • (f : ↥(fieldBar q M')) = (f : ↥(fieldBar q M'))) →
      ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ S →
        ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) σ • P ∈ S := by
    intro σ hσ hfixσ P hP
    have hσA' : σ • A = A := MulAction.mem_stabilizer_iff.mp hσ
    have hσA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ σ a ∈ A := by
      intro a
      constructor
      · intro ha
        have : σ • a ∈ σ • A := ValuationSubring.smul_mem_pointwise_smul σ a A ha
        rwa [hσA'] at this
      · intro ha
        rw [← hσA', ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at ha
        simpa using ha
    obtain ⟨h1, h2⟩ := (hS P).mp hP
    refine (hS _).mpr ⟨?_, ?_⟩
    · intro f hf
      rw [AlgebraicCurve.SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
        inv_smul_eq_iff.mpr (hfixσ f hf).symm]
      exact h1 f hf
    · intro f hfO hnu
      obtain ⟨hA, hmax⟩ := h2 f hfO hnu
      have hev : (ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) σ • P).evalAt (f : ↥(fieldBar q M')) =
          σ (P.evalAt (f : ↥(fieldBar q M'))) := by
        conv_lhs => rw [← hfixσ f hfO]
        exact evalAt_smul σ P _ (h1 f hfO)
      have hA' : σ (P.evalAt (f : ↥(fieldBar q M'))) ∈ A := (hσA _).1 hA
      refine ⟨hev ▸ hA', ?_⟩
      have key := maxA σ hσA _ hA hmax hA'
      convert key using 2
  intro τ hτ hfix P
  constructor
  · exact fwd τ hτ hfix P
  · intro hP
    have hτ' : τ⁻¹ ∈ A.decompositionSubgroup ℚ := (A.decompositionSubgroup ℚ).inv_mem hτ
    have hfix' : ∀ f : ↥F₀, f ∈ O → ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ⁻¹ • (f : ↥(fieldBar q M')) = (f : ↥(fieldBar q M')) := by
      intro f hf
      rw [map_inv]
      exact inv_smul_eq_iff.mpr (hfix f hf).symm
    have := fwd τ⁻¹ hτ' hfix' _ hP
    rwa [map_inv, inv_smul_smul] at this

end S_ModularCurve_FullLevel_mem_nodePlaces_iff_smul_mem_of_arithmeticGalois_smul_eq_of_mem_decompositionSubgroup
end P2MW
export P2MW.S_ModularCurve_FullLevel_mem_nodePlaces_iff_smul_mem_of_arithmeticGalois_smul_eq_of_mem_decompositionSubgroup (solution)
