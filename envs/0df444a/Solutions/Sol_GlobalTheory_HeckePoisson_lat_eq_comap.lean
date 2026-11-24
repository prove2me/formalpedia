-- Prove2me | solution 1 for GlobalTheory.HeckePoisson.lat_eq_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:32:24.321957+00:00
-- url     : https://prove2.me/submissions/4263ce9a-208f-4176-8436-cccb8e963dad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeIdealEuclideanLatticeIsZLattice
import Theorems.Thm_GlobalTheory_HeckePoisson_toMixed_embA
import Theorems.Thm_GlobalTheory_HeckePoisson_mem_lat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
noncomputable section
open GlobalTheory GlobalTheory.HeckePoisson
open GlobalTheory.CMVal InfinitePlace ComplexConjugate
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {I : Type} [Fintype I]
open Classical
namespace GlobalTheory.HeckePoisson
theorem _root_.solution {φ : I → K →+* ℂ} (h : IsCMType φ) (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) :
    lat φ M = ZLattice.comap (E := mixedEmbedding.mixedSpace K) (F := EuclideanSpace ℂ I) ℝ (mixedEmbedding.idealLattice K
      (Units.mk0 (M : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.2 hM)))
      (toMixed h).toContinuousLinearEquiv.toLinearMap := by
  ext z
  rw [mem_lat]
  change _ ↔ toMixed h z ∈ mixedEmbedding.idealLattice K _
  rw [mixedEmbedding.mem_idealLattice]
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    exact ⟨(μ : K), (FractionalIdeal.mem_coeIdeal _).2 ⟨μ, hμ, rfl⟩, (toMixed_embA h μ).symm⟩
  · rintro ⟨y, hy, hyz⟩
    have hy' : y ∈ (M : FractionalIdeal (𝓞 K)⁰ K) := hy
    obtain ⟨μ, hμ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy'
    exact ⟨μ, hμ, (toMixed h).injective (by rw [toMixed_embA]; exact hyz)⟩
end GlobalTheory.HeckePoisson
