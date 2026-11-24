-- Prove2me | solution 1 for GlobalTheory.CosetCrit.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:11:15.745888+00:00
-- url     : https://prove2.me/submissions/01030c82-6447-4d59-a733-6efd5f68718b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorsionTwistTsumNormGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependenceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TxCosetCriterion
import Theorems.Thm_GlobalTheory_CosetCrit_exists_char_pow
import Theorems.Thm_GlobalTheory_Ex_NumD_exists_tor_iff
import Theorems.Thm_GlobalTheory_T_degenerationData_torsion_structure_algClosed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.CosetCrit
variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
  {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}
omit [IsUltrametricDist C] [CompleteSpace C]
namespace GlobalTheory.CosetCrit
theorem _root_.solution {n g : ℕ} (hn : (n : C) ≠ 0) (hT : N.Tors n g) (j : ℕ) {t : N.A} (ht : t ^ n = 1) :
    ∃ γ : N.Gt, γ ^ n ^ (j + 1) = 1 ∧ γ.b ^ n ^ j = t := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g hn hT j
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  obtain ⟨γ₀, rfl⟩ := h1 t
  obtain ⟨s, hs⟩ := (N.exists_tor_iff (γ₀ ^ n)).2 (by rw [NumD.Gt.pow_b, ht])
  obtain ⟨s', rfl⟩ := exists_char_pow s hn0
  obtain ⟨γ, hγ⟩ := h2 (γ₀ * (N.tor s')⁻¹)
  refine ⟨γ, ?_, ?_⟩
  · rw [pow_succ, pow_mul, hγ, mul_pow, inv_pow, ← N.tor_pow, hs, mul_inv_cancel]
  · rw [← NumD.Gt.pow_b, hγ]
    simp
end GlobalTheory.CosetCrit
