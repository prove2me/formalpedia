-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.idealLatticePi_poisson_summation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:51:42.322123+00:00
-- url     : https://prove2.me/submissions/f9913ef3-c442-41ad-8e05-568c9a6f54c7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mixedPairingPi_comm
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mixedPairingPi_eq_inner
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mixedFourierPi_eq
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mem_euclidLatticePi
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mem_euclidConjLatticePi
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_covolume_euclidLatticePi
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_dualLattice_euclidLatticePi
import Theorems.Thm_GroundTheory_Global_lattice_poisson_summation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι]
variable {K}
namespace GroundTheory.Automorphic.GJMatrix
theorem _root_.solution (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(ι → mixedSpace K, ℂ)) (a : ι → mixedSpace K) :
    ∑' α : idealLatticePi I, f (α + a) =
      (∏ i, ((FractionalIdeal.absNorm (I i : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
        √|(discr K : ℝ)|))⁻¹ •
        ∑' β : idealLatticePi (fun i ↦ traceDualIdeal K (I i)),
          mixedFourierPi K f β * 𝐞 (mixedPairingPi K β a) := by
  set L := euclidLatticePi I
  set F : 𝓢(EuclidPi K ι, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclidPi K).symm f
  have hF : (F : EuclidPi K ι → ℂ) = f ∘ (toEuclidPi K).symm := rfl
  have hFx : ∀ x, F x = f ((toEuclidPi K).symm x) := fun x ↦ congrFun hF x
  have h := lattice_poisson_summation L F (toEuclidPi K a)
  let eL : idealLatticePi I ≃ L :=
    { toFun := fun α ↦ ⟨toEuclidPi K α, by
        rw [mem_euclidLatticePi, ContinuousLinearEquiv.symm_apply_apply]; exact α.2⟩
      invFun := fun ℓ ↦ ⟨(toEuclidPi K).symm ℓ, ℓ.2⟩
      left_inv := fun α ↦ Subtype.ext (ContinuousLinearEquiv.symm_apply_apply _ _)
      right_inv := fun ℓ ↦ Subtype.ext (ContinuousLinearEquiv.apply_symm_apply _ _) }
  let eD : idealLatticePi (fun i ↦ traceDualIdeal K (I i)) ≃ dualLattice L :=
    { toFun := fun β ↦ ⟨toEuclidPiConj K β, by
        rw [dualLattice_euclidLatticePi, mem_euclidConjLatticePi,
          ContinuousLinearEquiv.symm_apply_apply]; exact β.2⟩
      invFun := fun μ ↦ ⟨(toEuclidPiConj K).symm μ, by
        have hμ : (μ : EuclidPi K ι) ∈ euclidConjLatticePi (fun i ↦ traceDualIdeal K (I i)) := by
          rw [← dualLattice_euclidLatticePi]
          exact μ.2
        exact hμ⟩
      left_inv := fun β ↦ Subtype.ext (ContinuousLinearEquiv.symm_apply_apply _ _)
      right_inv := fun μ ↦ Subtype.ext (ContinuousLinearEquiv.apply_symm_apply _ _) }
  have hlhs : ∑' ℓ : L, F (ℓ + toEuclidPi K a) = ∑' α : idealLatticePi I, f (α + a) := by
    rw [← Equiv.tsum_eq eL]
    refine tsum_congr fun α ↦ ?_
    have heL : (eL α : EuclidPi K ι) = toEuclidPi K α := rfl
    rw [heL, hFx, ← map_add, ContinuousLinearEquiv.symm_apply_apply]
  have hrhs : ∑' μ : dualLattice L,
      𝓕 (F : EuclidPi K ι → ℂ) μ * 𝐞 ⟪(μ : EuclidPi K ι), toEuclidPi K a⟫ =
      ∑' β : idealLatticePi (fun i ↦ traceDualIdeal K (I i)),
        mixedFourierPi K f β * 𝐞 (mixedPairingPi K β a) := by
    rw [← Equiv.tsum_eq eD]
    refine tsum_congr fun β ↦ ?_
    have heD : (eD β : EuclidPi K ι) = toEuclidPiConj K β := rfl
    rw [heD, hF, ← mixedFourierPi_eq, real_inner_comm, ← mixedPairingPi_eq_inner, mixedPairingPi_comm]
  rw [hlhs, hrhs, covolume_euclidLatticePi] at h
  exact h
end GroundTheory.Automorphic.GJMatrix
