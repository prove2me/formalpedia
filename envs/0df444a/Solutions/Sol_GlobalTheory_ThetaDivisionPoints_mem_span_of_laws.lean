-- Prove2me | solution 1 for GlobalTheory.ThetaDivisionPoints.mem_span_of_laws
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:24:31.444873+00:00
-- url     : https://prove2.me/submissions/ffed033e-cac1-483b-84c2-96e23235e34d

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EntirePeriodicEqZeroOfFourierCoeffEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ClassicalThetaLevelAndLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemSpanThetaOfLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_RiemannThetaLevelOneNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsApplySubSmulNeZeroAndApplyAddNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsThetaDivisionPointNeZero
import Theorems.Thm_GlobalTheory_ClassicalTheta_card_le_pow_of_linearIndependent
import Theorems.Thm_GlobalTheory_ThetaSpan_laws_of_level
import Theorems.Thm_GlobalTheory_entire_periodic_eq_zero_of_fourierCoeff_eq_zero
import Theorems.Thm_GlobalTheory_fourierCoeff_unitCube_translate_of_entire_periodic
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_P2M_GlobalTheory_classicalTheta_level_and_linearIndependent__6b643778a469
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix
open GlobalTheory GlobalTheory.ThetaDivisionPoints
namespace GlobalTheory.ThetaDivisionPoints
theorem _root_.solution {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) {N : ℕ}
    (hN : 1 ≤ N) {f : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f ∧
      (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) ∧
      ∀ (j : Fin g) z, f (z + τ.mulVec (Pi.single j 1)) =
        eC (-(τ j j) / 2) ^ N * cexp (-(2 * Real.pi * I) * N * z j) * f z) :
    f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z : Fin g → ℂ) =>
      theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) := by
  have f4 := @GlobalTheory.fourierCoeff_unitCube_translate_of_entire_periodic
  have f5 := @GlobalTheory.entire_periodic_eq_zero_of_fourierCoeff_eq_zero f4
  have hdim := @GlobalTheory.ClassicalTheta.card_le_pow_of_linearIndependent f4 f5
  obtain ⟨hlev, hli⟩ := classicalTheta_level_and_linearIndependent' g τ hτ N hN
  by_contra hnot
  have hopt := hli.option hnot
  have hcard : Fintype.card (Option (Fin g → Fin N)) = N ^ g + 1 := by simp
  let e := (Fintype.equivFinOfCardEq hcard).symm
  have hli' := hopt.comp e e.injective
  have := hdim g N τ (fun j => eC (-(τ j j) / 2)) hN (fun j => Complex.exp_ne_zero _)
    (N ^ g + 1) _ (fun k => ?_) hli'
  · omega
  · simp only [Function.comp_apply]
    rcases e k with _ | c
    · exact hf
    · exact ⟨(hlev c).1, GlobalTheory.ThetaSpan.laws_of_level τ N _ (hlev c).2⟩
end GlobalTheory.ThetaDivisionPoints
