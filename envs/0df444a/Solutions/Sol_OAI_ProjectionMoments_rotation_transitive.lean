-- Prove2me | solution 1 for OAI.ProjectionMoments.rotation_transitive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:27:57.504868+00:00
-- url     : https://prove2.me/submissions/a98c68ad-1f28-4ef9-ad70-fb953519be85

import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_Graph
import Definitions.Def_OAI_Probability_ProjectionMoments_Frames

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {E}
theorem solution {ι : Type*} [Fintype ι] {u v : ι → E}
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) :
    ∃ O : Rotation E, ∀ i, (O : E →L[ℝ] E) (u i) = v i := by
  classical
  set n := Module.finrank ℝ E
  have hcard : Fintype.card ι ≤ n := hu.linearIndependent.fintype_card_le_finrank
  let emb : ι → Fin n := fun i => Fin.castLE hcard (Fintype.equivFin ι i)
  have hinj : Function.Injective emb := by
    intro i j h
    have := Fin.castLE_injective hcard h
    exact (Fintype.equivFin ι).injective this
  have hfin : Module.finrank ℝ E = Fintype.card (Fin n) := by simp [n]
  have hext : ∀ w : ι → E, Orthonormal ℝ w →
      ∃ b : OrthonormalBasis (Fin n) ℝ E, ∀ i, b (emb i) = w i := by
    intro w hw
    let W : Fin n → E := Function.extend emb w 0
    have hW : ∀ i, W (emb i) = w i := fun i => hinj.extend_apply w 0 i
    have hr : (Set.range emb).restrict W = w ∘ (Equiv.ofInjective emb hinj).symm := by
      funext x
      obtain ⟨k, i, rfl⟩ := x
      show W (emb i) = w ((Equiv.ofInjective emb hinj).symm ⟨emb i, ⟨i, rfl⟩⟩)
      rw [hW, Equiv.ofInjective_symm_apply]
    have hon : Orthonormal ℝ ((Set.range emb).restrict W) := by
      rw [hr]; exact hw.comp _ (Equiv.injective _)
    obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (s := Set.range emb) hfin
    exact ⟨b, fun i => (hb (emb i) ⟨i, rfl⟩).trans (hW i)⟩
  obtain ⟨bu, hbu⟩ := hext u hu
  obtain ⟨bv, hbv⟩ := hext v hv
  let O : E ≃ₗᵢ[ℝ] E := bu.repr.trans bv.repr.symm
  refine ⟨Unitary.linearIsometryEquiv.symm O, fun i => ?_⟩
  rw [Unitary.coe_symm_linearIsometryEquiv_apply]
  change O (u i) = v i
  rw [← hbu i, ← hbv i]
  simp only [O, LinearIsometryEquiv.trans_apply, OrthonormalBasis.repr_self, OrthonormalBasis.repr_symm_single]

