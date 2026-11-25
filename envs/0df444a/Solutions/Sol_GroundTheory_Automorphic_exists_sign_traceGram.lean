-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_sign_traceGram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:35:59.472807+00:00
-- url     : https://prove2.me/submissions/d9747f12-1a36-4191-9720-2e1cade7b15c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Places
import Theorems.Thm_GroundTheory_Automorphic_vecCoords_vecOfCoords
import Theorems.Thm_GroundTheory_Automorphic_hermTrace_eq_sum_traceGram
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_hermTraceBilin_apply
import Theorems.Thm_GroundTheory_Automorphic_hermTrace_self_of_hermValue
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
omit [NumberField K]
namespace GroundTheory.Automorphic
theorem _root_.solution {w : InfinitePlace K} (hw : w.IsReal)
    (hdef : IsHermDefiniteAt H w hw) :
    ∃ ε : ℝ, ε ≠ 0 ∧ ∀ v : ι × κ → ℝ, v ≠ 0 →
      0 < ε * ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (traceGram H b a c) := by
  let ψ := Completion.ringEquivRealOfIsReal hw
  have key : ∀ v : ι × κ → ℝ, ψ (hermTrace K H w.Completion (vecOfCoords b w.Completion
      (fun a => ψ.symm (v a))) (vecOfCoords b w.Completion (fun a => ψ.symm (v a)))) =
      ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (traceGram H b a c) := by
    intro v
    rw [hermTrace_eq_sum_traceGram (H := H) (b := b) w.Completion,
      vecCoords_vecOfCoords b w.Completion (fun a => ψ.symm (v a)), map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    congr 1
    rw [Completion.ringEquivRealOfIsReal_apply, Completion.algebraMap_apply]
    exact Completion.extensionEmbeddingOfIsReal_coe hw _
  have hne : ∀ v : ι × κ → ℝ, v ≠ 0 →
      vecOfCoords b w.Completion (fun a => ψ.symm (v a)) ≠ 0 := by
    intro v hv h
    apply hv
    funext a
    have := congrFun (vecCoords_vecOfCoords b w.Completion (fun a => ψ.symm (v a))) a
    rw [h] at this
    have h0 : vecCoords w.Completion b (0 : ι → w.Completion ⊗[K] E) a = 0 := by
      simp [vecCoords]
    rw [h0] at this
    have := congrArg ψ this
    rw [RingEquiv.apply_symm_apply, map_zero] at this
    exact this.symm
  rcases hdef with hpos | hneg
  · refine ⟨1, one_ne_zero, fun v hv => ?_⟩
    obtain ⟨t, ht, htpos⟩ := hpos _ (hne v hv)
    rw [one_mul, ← key, hermTrace_self_of_hermValue ht, map_mul, map_ofNat]
    have : ψ t = Completion.extensionEmbeddingOfIsReal hw t := rfl
    rw [this]
    positivity
  · refine ⟨-1, by norm_num, fun v hv => ?_⟩
    obtain ⟨t, ht, htneg⟩ := hneg _ (hne v hv)
    rw [← key, hermTrace_self_of_hermValue ht, map_mul, map_ofNat]
    have : ψ t = Completion.extensionEmbeddingOfIsReal hw t := rfl
    rw [this]
    linarith
end GroundTheory.Automorphic
