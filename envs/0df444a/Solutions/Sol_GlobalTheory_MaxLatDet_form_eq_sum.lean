-- Prove2me | solution 1 for GlobalTheory.MaxLatDet.form_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:56:16.899726+00:00
-- url     : https://prove2.me/submissions/ebf6aef6-66b0-4a4e-a4bf-81a51c418c54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeBadPrimesIffGramDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.MaxLatDet
open IsDedekindDomain
variable {K V ι : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [Fintype ι]
namespace GlobalTheory.MaxLatDet
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Module.Basis ι K V)
    (he : ∀ i l, i ≠ l → h (e i) (e l) = 0) (x y : V) :
    h x y = ∑ i, star (e.repr x i) * h (e i) (e i) * e.repr y i := by
  conv_lhs => rw [← e.sum_repr x]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, mul_assoc]
  congr 1
  conv_lhs => rw [← e.sum_repr y]
  rw [map_sum, Finset.sum_eq_single i]
  · rw [map_smul, smul_eq_mul, mul_comm]
  · intro l _ hl
    rw [map_smul, he i l hl.symm, smul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi
end GlobalTheory.MaxLatDet
