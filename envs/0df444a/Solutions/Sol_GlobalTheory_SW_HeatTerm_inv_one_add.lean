-- Prove2me | solution 1 for GlobalTheory.SW.HeatTerm.inv_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:26:11.542793+00:00
-- url     : https://prove2.me/submissions/d355993f-7162-4469-a596-b9fa49526819

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeatTerm
noncomputable section
namespace GlobalTheory.SW.HeatTerm
theorem _root_.solution {N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) (s : ℂ)
    (h : 1 + s * S b a ≠ 0) :
    (1 + S * Matrix.single a b s)⁻¹ = 1 - (s / (1 + s * S b a)) • (S * Matrix.single a b 1) := by
  apply Matrix.inv_eq_right_inv
  have h1 : Matrix.single a b s = s • Matrix.single a b (1 : ℂ) := by simp
  have h2 : S * Matrix.single a b (1 : ℂ) * (S * Matrix.single a b 1) =
      S b a • (S * Matrix.single a b 1) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.single a b 1),
      Matrix.single_mul_mul_single, ← Matrix.mul_smul]
    simp
  rw [h1, Matrix.mul_smul]
  generalize S * Matrix.single a b (1 : ℂ) = P at h2
  rw [add_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, h2]
  have : s / (1 + s * S b a) + s * (s / (1 + s * S b a) * S b a) = s := by field_simp
  rw [smul_smul, smul_smul, sub_add_sub_comm, ← add_smul, mul_assoc, this]
  simp
end GlobalTheory.SW.HeatTerm
