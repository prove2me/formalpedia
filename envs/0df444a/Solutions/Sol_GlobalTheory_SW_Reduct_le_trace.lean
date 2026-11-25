-- Prove2me | solution 1 for GlobalTheory.SW.Reduct.le_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:59:34.447555+00:00
-- url     : https://prove2.me/submissions/b71926f1-a4d3-4fdf-b23d-5e3ecef242ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryMoveHermitianHalfSpaceHigh
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Reduct
variable {N : ℕ}
namespace GlobalTheory.SW.Reduct
theorem _root_.solution {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.PosSemidef) {T : ℝ}
    (hT : M.trace.re ≤ T) : ((T : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - M).PosSemidef := by
  have hs := hM.1.spectral_theorem
  have ht := hM.1.trace_eq_sum_eigenvalues
  set U : Matrix (Fin N) (Fin N) ℂ := (hM.1.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) with hU
  have hUU : U * Uᴴ = 1 := (Unitary.coe_mul_star_self hM.1.eigenvectorUnitary)
  have hs' : M = U * diagonal (fun i => (hM.1.eigenvalues i : ℂ)) * Uᴴ := hs
  have e : (T : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - M =
      U * diagonal (fun i => ((T - hM.1.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have : diagonal (fun i => ((T - hM.1.eigenvalues i : ℝ) : ℂ)) =
        (T : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - diagonal (fun i => (hM.1.eigenvalues i : ℂ)) := by
      ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, ← hs', Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hUU]
  rw [e]
  refine Matrix.PosSemidef.mul_mul_conjTranspose_same ?_ U
  refine Matrix.PosSemidef.diagonal fun i => ?_
  have h1 : hM.1.eigenvalues i ≤ ∑ j, hM.1.eigenvalues j :=
    Finset.single_le_sum (fun j _ => hM.eigenvalues_nonneg j) (Finset.mem_univ i)
  have h2 : M.trace.re = ∑ j, hM.1.eigenvalues j := by
    rw [ht]; simp
  simp only [Pi.zero_apply]
  exact_mod_cast (by linarith : 0 ≤ T - hM.1.eigenvalues i)
end GlobalTheory.SW.Reduct
