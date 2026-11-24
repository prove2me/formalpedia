-- Prove2me | solution 1 for GlobalTheory.SW.WeilAdm.rho_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:00:07.882835+00:00
-- url     : https://prove2.me/submissions/ee4a5506-080e-49e9-826a-bda03edaa100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleLatticeFamilyHermitianWeilAction
import Theorems.Thm_GlobalTheory_SW_WeilAdm_rho_add
import Theorems.Thm_GlobalTheory_SW_WeilAdm_mem_sub
import Theorems.Thm_GlobalTheory_SW_WeilLevel_heisH_fix


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
theorem _root_.solution (hΛ : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y))
    (hΛ' : ∀ x, x ∈ Λ' ↔ ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) {s R : ℕ}
    (h2 : ∀ v ∈ Λ', (s : E) • v ∈ Λ) {φ : Matrix (Fin n) (Fin N) E → ℂ} (hφ : LevelL Λ R φ)
    (x y : cols Λ' N)
    (h : x - y ∈ ((cols Λ' N).map (nsmulAddMonoidHom s)).addSubgroupOf (cols Λ' N)) :
    rho R x.1 φ = rho R y.1 φ := by
  obtain ⟨z, hz, e⟩ := (mem_sub _).1 h
  have e1 : x.1 = y.1 + (x - y).1 := by simp
  have e2 : rho R (x - y).1 φ = φ := by
    rw [← e]
    exact heisH_fix hΛ hφ (fun a => h2 _ (hz (Sum.inl a))) (fun a => h2 _ (hz (Sum.inr a)))
  rw [e1, rho_add hΛ' R (x - y).2 y.2, e2]
end GlobalTheory.SW.WeilAdm
