-- Prove2me | solution 1 for GlobalTheory.spectralNorm_closedBall_isOpen_isCompact_nhds_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:33:37.67673+00:00
-- url     : https://prove2.me/submissions/4520128e-892a-4b99-97cb-61e7a6f4d3a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SpectralNormClosedBallIsOpenIsCompactNhdsBasisAl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [LocallyCompactSpace F] (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [TopologicalSpace L] [IsModuleTopology F L], IsOpen {y : L | spectralNorm F L y ≤ 1} ∧ IsCompact {y : L | spectralNorm F L y ≤ 1} ∧ ∀ U ∈ 𝓝 (0 : L), ∃ r : ℝ, 0 < r ∧ ∀ y : L, spectralNorm F L y < r → y ∈ U := by
  intro F _ _ _ _ L _ _ _ τ _
  have hcs : ContinuousSMul F L := IsModuleTopology.toContinuousSMul F L
  have hca : ContinuousAdd L := IsModuleTopology.toContinuousAdd F L
  have htg : IsTopologicalAddGroup L :=
    { continuous_neg := by
        have : (fun x : L => -x) = fun x => (-1 : F) • x := by funext x; simp
        rw [this]; exact continuous_const.smul continuous_id }
  let N : NormedAddCommGroup L := spectralNorm.normedAddCommGroup F L
  let NS : NormedSpace F L := spectralNorm.normedSpace F L
  let τ' : TopologicalSpace L := N.toUniformSpace.toTopologicalSpace
  have h1 : τ ≤ τ' := by
    rw [← continuous_id_iff_le]
    exact @IsModuleTopology.continuous_of_linearMap F _ _ L _ _ τ _ L _ _ τ' inferInstance inferInstance LinearMap.id
  have h2 : τ' ≤ τ := by
    rw [← continuous_id_iff_le]
    exact @LinearMap.continuous_of_finiteDimensional F _ L _ _ τ' inferInstance inferInstance L _ _ τ htg hcs _ inferInstance _ (LinearMap.id)
  have hτ : τ = τ' := le_antisymm h1 h2
  subst hτ
  have hU : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (isNonarchimedean_spectralNorm (K := F) (L := L))
  have hPF : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have hPL : ProperSpace L := FiniteDimensional.proper F L
  have hd : ∀ y : L, dist y 0 = spectralNorm F L y := fun y => by
    rw [dist_zero_right]; rfl
  have hS : {y : L | spectralNorm F L y ≤ 1} = Metric.closedBall (0 : L) 1 := by
    ext y; simp only [Set.mem_setOf_eq, Metric.mem_closedBall, hd]
  refine ⟨?_, ?_, ?_⟩
  · rw [hS]; exact IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  · rw [hS]; exact isCompact_closedBall _ _
  · intro U hU0
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp hU0
    exact ⟨ε, hε, fun y hy => hb (by rw [Metric.mem_ball, hd]; exact hy)⟩
end GlobalTheory
