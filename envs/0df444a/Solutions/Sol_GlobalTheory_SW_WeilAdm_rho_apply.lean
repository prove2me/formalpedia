-- Prove2me | solution 1 for GlobalTheory.SW.WeilAdm.rho_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:29:37.324063+00:00
-- url     : https://prove2.me/submissions/47e2da4c-fefe-4914-a693-588db52bad97

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
import Theorems.Thm_GlobalTheory_SW_WeilAdm_colsIn_of_coprime
import Theorems.Thm_GlobalTheory_SW_WeilAdm_colsIn_transfer
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
open Classical
namespace GlobalTheory.SW.WeilAdm
theorem _root_.solution (hΛ' : ∀ x, x ∈ Λ' ↔ ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) {s R m : ℕ}
    (hs : s.Coprime (m * (2 * R))) (h1 : ∀ v ∈ Λ, (s : E) • v ∈ Λ')
    (h2 : ∀ v ∈ Λ', (s : E) • v ∈ Λ) {φ : Matrix (Fin n) (Fin N) E → ℂ} (hφ : LevelL Λ R φ)
    {X : Matrix (Fin n) (Fin N ⊕ Fin N) E} (hX : X ∈ cols Λ' N) {x : Matrix (Fin n) (Fin N) E}
    (hx : ColsIn Λ (((m * (2 * R) : ℕ) : E) • x)) (hx' : ColsIn Λ' (((m * (2 * R) : ℕ) : E) • x)) :
    rho R X φ x = (if ColsIn Λ X.toCols₁ then 1 else 0) * φ x := by
  have hd' : ColsIn Λ' X.toCols₁ := fun a => hX (Sum.inl a)
  have hb' : ColsIn Λ' X.toCols₂ := fun a => hX (Sum.inr a)
  simp only [rho, heisH]
  split_ifs with hd
  · have e1 : φ (x - ((2 * R : ℕ) : E) • X.toCols₁) = φ x := by
      rw [← hφ.2 x (-(((2 : ℕ) : E) • X.toCols₁)) fun a => Λ.neg_mem (colsIn_smul 2 hd a)]
      congr 1
      rw [smul_neg, smul_smul, sub_eq_add_neg, Nat.cast_mul, mul_comm]
    rw [e1, one_mul]
    by_cases h0 : φ x = 0
    · rw [h0, zero_mul]
    have h3 : ColsIn Λ' ((R : E) • x) :=
      colsIn_transfer (m := m * 2) (by rwa [mul_assoc]) h1 (hφ.1 x h0) (by rwa [mul_assoc])
    have p := phase_one hΛ' hb' (y := ((2 : ℕ) : E) • ((R : E) • x) - ((2 * R * R : ℕ) : E) • X.toCols₁)
      fun a => Λ'.sub_mem (colsIn_smul 2 h3 a) (colsIn_smul _ hd' a)
    rw [← mul_one (φ x), mul_assoc, one_mul, ← p]
    congr 5
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, cc_sub, cc_mul, cc_nat]
    push_cast
    ring
  · rw [zero_mul, mul_eq_zero]
    left
    by_contra h0
    apply hd
    have h3 := colsIn_smul (m * 2) (hφ.1 _ h0)
    refine colsIn_of_coprime (t := (m * (2 * R)) * (2 * R))
      (Nat.Coprime.mul_right hs (Nat.Coprime.coprime_mul_left_right hs)) (fun a => h2 _ (hd' a))
      fun a => ?_
    convert Λ.sub_mem (hx a) (h3 a) using 1
    ext k
    simp
    ring
end GlobalTheory.SW.WeilAdm
