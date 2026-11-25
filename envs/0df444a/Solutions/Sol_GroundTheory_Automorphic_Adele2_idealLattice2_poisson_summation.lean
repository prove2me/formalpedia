-- Prove2me | solution 1 for GroundTheory.Automorphic.Adele2.idealLattice2_poisson_summation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:52:43.449786+00:00
-- url     : https://prove2.me/submissions/fcd26a87-0f8e-4617-944a-27f93c9f006a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2
import Theorems.Thm_GroundTheory_Automorphic_Adele2_mixedPairing2_comm
import Theorems.Thm_GroundTheory_Automorphic_Adele2_mixedPairing2_eq_inner
import Theorems.Thm_GroundTheory_Automorphic_Adele2_mixedFourier2_eq
import Theorems.Thm_GroundTheory_Automorphic_Adele2_mem_euclidLattice2
import Theorems.Thm_GroundTheory_Automorphic_Adele2_mem_euclidConjLattice2
import Theorems.Thm_GroundTheory_Automorphic_Adele2_covolume_euclidLattice2
import Theorems.Thm_GroundTheory_Automorphic_Adele2_dualLattice_euclidLattice2
import Theorems.Thm_GroundTheory_Global_lattice_poisson_summation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Adele2
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Automorphic.Adele2
theorem _root_.solution (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(Fin 2 → mixedSpace K, ℂ)) (a : Fin 2 → mixedSpace K) :
    ∑' α : idealLattice2 I, f (α + a) =
      (∏ i, ((FractionalIdeal.absNorm (I i : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
        √|(discr K : ℝ)|))⁻¹ •
        ∑' β : idealLattice2 (fun i => traceDualIdeal K (I i)),
          mixedFourier2 K f β * 𝐞 (mixedPairing2 K β a) := by
  set L := euclidLattice2 I
  set F : 𝓢(WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K), ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclid2 K).symm f
  have hF : (F : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K) → ℂ) =
      f ∘ (toEuclid2 K).symm := rfl
  have h := lattice_poisson_summation L F (toEuclid2 K a)
  let eL : idealLattice2 I ≃ L :=
    { toFun := fun α => ⟨toEuclid2 K α, by
        rw [mem_euclidLattice2, ContinuousLinearEquiv.symm_apply_apply]; exact α.2⟩
      invFun := fun ℓ => ⟨(toEuclid2 K).symm ℓ, ℓ.2⟩
      left_inv := fun α => Subtype.ext (ContinuousLinearEquiv.symm_apply_apply _ _)
      right_inv := fun ℓ => Subtype.ext (ContinuousLinearEquiv.apply_symm_apply _ _) }
  let eD : idealLattice2 (fun i => traceDualIdeal K (I i)) ≃ dualLattice L :=
    { toFun := fun β => ⟨toEuclid2Conj K β, by
        rw [dualLattice_euclidLattice2, mem_euclidConjLattice2,
          ContinuousLinearEquiv.symm_apply_apply]; exact β.2⟩
      invFun := fun μ => ⟨(toEuclid2Conj K).symm μ, by
        have hμ : (μ : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K)) ∈
            euclidConjLattice2 (fun i => traceDualIdeal K (I i)) := by
          rw [← dualLattice_euclidLattice2]
          exact μ.2
        exact hμ⟩
      left_inv := fun β => Subtype.ext (ContinuousLinearEquiv.symm_apply_apply _ _)
      right_inv := fun μ => Subtype.ext (ContinuousLinearEquiv.apply_symm_apply _ _) }
  have hlhs : ∑' ℓ : L, F (ℓ + toEuclid2 K a) = ∑' α : idealLattice2 I, f (α + a) := by
    rw [← Equiv.tsum_eq eL]
    refine tsum_congr fun α => ?_
    change f ((toEuclid2 K).symm (toEuclid2 K α + toEuclid2 K a)) = _
    rw [← map_add, ContinuousLinearEquiv.symm_apply_apply]
  have hrhs : ∑' μ : dualLattice L,
      𝓕 (F : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K) → ℂ) μ *
        𝐞 ⟪(μ : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K)), toEuclid2 K a⟫ =
      ∑' β : idealLattice2 (fun i => traceDualIdeal K (I i)),
        mixedFourier2 K f β * 𝐞 (mixedPairing2 K β a) := by
    rw [← Equiv.tsum_eq eD]
    refine tsum_congr fun β => ?_
    change 𝓕 (F : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K) → ℂ)
        (toEuclid2Conj K β) * 𝐞 ⟪toEuclid2Conj K β, toEuclid2 K a⟫ = _
    rw [hF, ← mixedFourier2_eq, real_inner_comm, ← mixedPairing2_eq_inner, mixedPairing2_comm]
  rw [hlhs, hrhs, covolume_euclidLattice2] at h
  exact h
end GroundTheory.Automorphic.Adele2
