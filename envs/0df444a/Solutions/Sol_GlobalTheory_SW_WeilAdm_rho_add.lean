-- Prove2me | solution 1 for GlobalTheory.SW.WeilAdm.rho_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:45:33.065287+00:00
-- url     : https://prove2.me/submissions/4008d39d-22db-40fa-bcb4-3a064b28f3be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleLatticeFamilyHermitianWeilAction
import Theorems.Thm_GlobalTheory_SW_WeilAdm_phase_one
import Theorems.Thm_GlobalTheory_SW_WeilLevel_cc_add
import Theorems.Thm_GlobalTheory_SW_WeilLevel_cc_mul
import Theorems.Thm_GlobalTheory_SW_WeilLevel_cc_nat
import Theorems.Thm_GlobalTheory_SW_WeilLevel_cc_sub
import Theorems.Thm_GlobalTheory_SW_WeilLevel_colsIn_smul


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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.WeilAdm
open WeilLevel Base
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ} {Λ Λ' : Lt E n}
namespace GlobalTheory.SW.WeilAdm
theorem _root_.solution (hΛ : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) (R : ℕ)
    {X Y : Matrix (Fin n) (Fin N ⊕ Fin N) E} (hX : X ∈ cols Λ N) (hY : Y ∈ cols Λ N)
    (φ : Matrix (Fin n) (Fin N) E → ℂ) : rho R (Y + X) φ = rho R Y (rho R X φ) := by
  funext x
  have p1 := phase_one hΛ (b := ((2 * R * R : ℕ) : E) • X.toCols₂) (y := Y.toCols₁)
    (colsIn_smul _ fun a => hX (Sum.inr a)) (fun a => hY (Sum.inl a))
  have p2 := phase_one hΛ (b := -(((2 * R * R : ℕ) : E) • Y.toCols₂)) (y := X.toCols₁)
    (fun a => Λ.neg_mem (colsIn_smul _ (fun a => hY (Sum.inr a)) a)) (fun a => hX (Sum.inl a))
  simp only [rho, heisH]
  rw [mul_assoc (φ _), ← Complex.exp_add, ← mul_one (cexp (_ + _)), ← p1, ← Complex.exp_add,
    ← mul_one (cexp (_ + _)), ← p2, ← Complex.exp_add]
  congr 1
  · congr 1
    ext k a
    simp [toCols₁]
    ring
  · congr 1
    rw [← mul_add, ← mul_add, ← mul_add, ← Rat.cast_add, ← Rat.cast_add, ← Rat.cast_add,
      ← map_add, ← map_add, ← map_add]
    simp only [← Finset.sum_add_distrib]
    congr 3
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul, toCols₁, toCols₂,
      Matrix.of_apply, Matrix.add_apply, cc_sub, cc_mul, cc_nat, cc_add]
    push_cast
    ring
end GlobalTheory.SW.WeilAdm
