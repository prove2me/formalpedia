-- Prove2me | solution 1 for GroundTheory.Automorphic.linearIndependent_realEmb_integralBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:58.050517+00:00
-- url     : https://prove2.me/submissions/d9747d2c-b4ab-44dd-884a-0fe923192421

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Places
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_hermTraceBilin_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.hermTraceBilin_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct NumberField NumberField.InfinitePlace
variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R]
variable {H b}
namespace GroundTheory.Automorphic
theorem _root_.solution (hreal : ∀ w : InfinitePlace K, w.IsReal) :
    LinearIndependent ℝ fun t : Free.ChooseBasisIndex ℤ (𝓞 K) =>
      fun w : {w : InfinitePlace K // w.IsReal} => embedding_of_isReal w.2 (integralBasis K t) := by
  have hli := (mixedEmbedding.latticeBasis K).linearIndependent
  have hker : LinearMap.ker (LinearMap.fst ℝ ({w : InfinitePlace K // w.IsReal} → ℝ)
      ({w : InfinitePlace K // w.IsComplex} → ℂ)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    rintro ⟨x, y⟩ h
    simp only [LinearMap.fst_apply] at h
    subst h
    have : y = 0 := funext fun w => absurd (hreal w.1) (not_isReal_iff_isComplex.2 w.2)
    rw [this]; rfl
  have := hli.map' _ hker
  have heq : (fun t : Free.ChooseBasisIndex ℤ (𝓞 K) =>
      fun w : {w : InfinitePlace K // w.IsReal} => embedding_of_isReal w.2 (integralBasis K t)) =
      (LinearMap.fst ℝ ({w : InfinitePlace K // w.IsReal} → ℝ)
        ({w : InfinitePlace K // w.IsComplex} → ℂ)) ∘ (mixedEmbedding.latticeBasis K) := by
    funext t w
    simp only [Function.comp_apply, mixedEmbedding.latticeBasis_apply, LinearMap.fst_apply]
    rw [mixedEmbedding.mixedEmbedding_apply_isReal]
  rw [heq]
  exact this
end GroundTheory.Automorphic
