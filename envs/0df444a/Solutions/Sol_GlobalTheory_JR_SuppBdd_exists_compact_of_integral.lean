-- Prove2me | solution 1 for GlobalTheory.JR.SuppBdd.exists_compact_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:06:03.241019+00:00
-- url     : https://prove2.me/submissions/29392fb6-fe28-4ba8-9a7d-5f335f2dce86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactUnitariesIntegralOrbitOfHankelDetNe
import Theorems.Thm_GlobalTheory_JR_SuppBdd_isClosed_unitary_set
import Theorems.Thm_GlobalTheory_JR_SuppBdd_Bm_actU
import Theorems.Thm_GlobalTheory_JR_NormalFormL_hankel_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.SuppBdd
namespace GlobalTheory.JR.SuppBdd
theorem _root_.solution : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] {n : ℕ} (Y : Hn n F E), Delta (inv Y.toGl) ≠ 0 →
    ∃ K : Set (Matrix.unitaryGroup (Fin n) E), IsCompact K ∧ ∀ g, unitU n F E (actU g Y) ≠ 0 → g ∈ K := by
  intro F E _ _ _ _ _ n Y hD
  haveI : LocallyCompactSpace E := Unram.lcE (F := F)
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : NormedStarGroup E := ⟨fun x => (Unram.norm_star (F := F) x).le⟩
  set B := Bm Y.toGl with hBdef
  have hB : IsUnit B.det := by
    have h := GlobalTheory.JR.NormalFormL.hankel_eq Y.toGl
    have : (Cm Y.toGl * B).det ≠ 0 := by rw [h]; exact hD
    rw [det_mul] at this
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul this)
  let Φ : Matrix (Fin n) (Fin n) E × (Fin n → E) → Matrix (Fin n) (Fin n) E :=
    fun p => (Matrix.of fun i (j : Fin n) => ((p.1 ^ (j : ℕ)) *ᵥ p.2) i) * B⁻¹
  let S : Set (Matrix (Fin n) (Fin n) E × (Fin n → E)) :=
    {A | ∀ i j, ‖A i j‖ ≤ 1} ×ˢ {v | ∀ i, ‖v i‖ ≤ 1}
  have hS : IsCompact S := by
    apply IsCompact.prod
    · have : {A : Matrix (Fin n) (Fin n) E | ∀ i j, ‖A i j‖ ≤ 1} =
          Set.pi Set.univ (fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : E) 1) := by
        ext A; simp only [Set.mem_setOf_eq]
        exact ⟨fun h i _ j _ => by simpa using h i j, fun h i j => by simpa using h i trivial j trivial⟩
      rw [this]
      exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    · have : {v : Fin n → E | ∀ i, ‖v i‖ ≤ 1} = Set.pi Set.univ (fun _ => Metric.closedBall (0 : E) 1) := by
        ext v; simp
      rw [this]
      exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hΦ : Continuous Φ := by
    refine Continuous.matrix_mul ?_ continuous_const
    refine continuous_matrix fun i j => ?_
    exact (continuous_apply i).comp ((continuous_fst.pow (j : ℕ)).matrix_mulVec continuous_snd)
  refine ⟨Subtype.val ⁻¹' (Φ '' S), ?_, ?_⟩
  · exact (isClosed_unitary_set (n := n) (E := E)).isClosedEmbedding_subtypeVal.isCompact_preimage (hS.image hΦ)
  · intro g hg
    have hm := Set.mem_of_indicator_ne_zero hg
    refine ⟨((actU g Y).1.1, (actU g Y).2.1), ⟨hm.1, hm.2.1⟩, ?_⟩
    show Bm (actU g Y).toGl * B⁻¹ = g.1
    rw [Bm_actU, ← hBdef, Matrix.mul_nonsing_inv_cancel_right _ _ hB]
end GlobalTheory.JR.SuppBdd
