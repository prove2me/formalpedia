-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_mul_mul_eq_one_of_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:57:18.808888+00:00
-- url     : https://prove2.me/submissions/5fc54b6d-a3fa-45f4-bdc6-017392704d36

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
variable {K : Type*} [Field K] {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (A : Matrix m l K) :
    ∃ (L : Matrix (Fin A.rank) m K) (R : Matrix l (Fin A.rank) K), L * A * R = 1 := by
  classical
  set f := A.mulVecLin with hf
  have hr : Module.finrank K (LinearMap.range f) = A.rank := rfl
  let b : Module.Basis (Fin A.rank) K (LinearMap.range f) := Module.finBasisOfFinrankEq K _ hr
  have hx : ∀ i, ∃ x, f x = (b i : m → K) := fun i => LinearMap.mem_range.1 (b i).2
  choose x hx using hx
  let R : Matrix l (Fin A.rank) K := Matrix.of fun j i => x i j
  have hRc : ∀ c : Fin A.rank → K, R *ᵥ c = ∑ i, c i • x i := by
    intro c
    ext j
    simp [R, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hAR : ∀ c : Fin A.rank → K, (A * R) *ᵥ c = ∑ i, c i • (b i : m → K) := by
    intro c
    rw [← Matrix.mulVec_mulVec, hRc]
    have : A *ᵥ (∑ i, c i • x i) = f (∑ i, c i • x i) := rfl
    rw [this, map_sum]
    simp only [map_smul, hx]
  have hli : LinearIndependent K (fun i => (b i : m → K)) :=
    b.linearIndependent.map' (LinearMap.range f).subtype (Submodule.ker_subtype _)
  have hker : LinearMap.ker (A * R).mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    have h1 : ∑ i, c i • (b i : m → K) = 0 := by
      rw [← hAR]
      exact hc
    funext i
    exact Fintype.linearIndependent_iff.1 hli c h1 i
  obtain ⟨h, hh⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  refine ⟨LinearMap.toMatrix' h, R, ?_⟩
  have h2 : LinearMap.toMatrix' (h.comp (A * R).mulVecLin) = 1 := by
    rw [hh, LinearMap.toMatrix'_id]
  rw [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at h2
  rw [Matrix.mul_assoc]
  exact h2
end GroundTheory.Automorphic.Parabolic
