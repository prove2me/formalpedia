-- Prove2me | solution 1 for GroundTheory.Automorphic.realEmb_mul_hermTrace_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:35:38.608965+00:00
-- url     : https://prove2.me/submissions/ba75b455-72b5-4f6f-84ae-263c9714131a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Places
import Theorems.Thm_GroundTheory_Automorphic_vecOfCoords_vecCoords
import Theorems.Thm_GroundTheory_Automorphic_hermTrace_eq_sum_traceGram
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
theorem _root_.solution {θ : K}
    (hθ : ∀ (w : InfinitePlace K) (hw : w.IsReal) (v : ι × κ → ℝ), v ≠ 0 →
      0 < ∑ a, ∑ c, v a * v c * embedding_of_isReal hw (θ * traceGram H b a c))
    {w : InfinitePlace K} (hw : w.IsReal) {x : ι → K ⊗[K] E} (hx : x ≠ 0) :
    0 < embedding_of_isReal hw (θ * hermTrace K H K x x) := by
  have hv : (fun a => embedding_of_isReal hw (vecCoords K b x a)) ≠ 0 := by
    intro h
    apply hx
    rw [← vecOfCoords_vecCoords b K x]
    have : vecCoords K b x = 0 := by
      funext a
      have := congrFun h a
      simpa using this
    rw [this]
    funext i
    simp [vecOfCoords]
  have := hθ w hw _ hv
  convert this using 1
  rw [hermTrace_eq_sum_traceGram (H := H) (b := b) K, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Algebra.algebraMap_self, RingHom.id_apply]
  simp only [map_mul]
  ring
end GroundTheory.Automorphic
