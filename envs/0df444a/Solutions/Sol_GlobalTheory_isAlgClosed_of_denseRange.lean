-- Prove2me | solution 1 for GlobalTheory.isAlgClosed_of_denseRange
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:22.314074+00:00
-- url     : https://prove2.me/submissions/2d3f8ab5-1917-469e-930a-7ca1db71aafe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution {K L : Type*} [Field K] [NontriviallyNormedField L]
    [CompleteSpace L] [IsUltrametricDist L] [Algebra K L]
    (hi : DenseRange (algebraMap K L)) [IsAlgClosed K] : IsAlgClosed L := by
  apply IsAlgClosed.of_exists_root
  intro f fmon firr
  have fnatdeg0 : f.natDegree ≠ 0 := (Irreducible.natDegree_pos firr).ne'
  let F := f.SplittingField
  letI : NormedField F := spectralNorm.normedField L F
  letI : NormedAlgebra L F := spectralNorm.normedAlgebra L F
  let a := rootOfSplits (SplittingField.splits f)
      (by simpa using degree_ne_of_natDegree_ne fnatdeg0)
  have fa0 : f.aeval a = 0 := by
    rw [← eval_map_algebraMap]
    exact eval_rootOfSplits (Polynomial.SplittingField.splits f)
      (by simpa using degree_ne_of_natDegree_ne fnatdeg0)
  have hcl : IsClosed (Set.range (algebraMap L F)) :=
    (algebraMap_isometry L F).isClosedEmbedding.isClosed_range
  have ha : a ∈ Set.range (algebraMap L F) := by
    rw [← hcl.closure_eq, Metric.mem_closure_iff]
    intro δ δpos
    have hε : (δ / (max ‖a‖ 1)) ^ f.natDegree / (f.natDegree + 1) > 0 := by positivity
    obtain ⟨g, gmon, gdeg, gcoeff⟩ :=
      exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hi fmon hε
    obtain ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
        hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff
        (by simpa [Polynomial.map_map] using (IsAlgClosed.splits g).map ((algebraMap L F).comp _))
    have hab : ‖a - b‖ < δ := by
      rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
          ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hab
      · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖a‖ 1) > 0).ne'] using hab
      · simp [fnatdeg0]
      · positivity
    refine ⟨b, ?_, by rwa [dist_eq_norm]⟩
    rw [Polynomial.aroots_def, Splits.roots_map ((IsAlgClosed.splits g).map _),
        Multiset.mem_map] at hb
    obtain ⟨c, _, hc⟩ := hb
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := ha
  refine ⟨c, ?_⟩
  apply_fun algebraMap L F
  · rwa [← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hc, map_zero]
  · exact RingHom.injective _
end GlobalTheory
