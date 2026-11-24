-- Prove2me | solution 1 for GlobalTheory.SW.WeilAdm.sum_rho_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:13:35.942628+00:00
-- url     : https://prove2.me/submissions/27aaa809-c3cb-4618-8fe9-488c114d834c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleLatticeFamilyHermitianWeilAction
import Theorems.Thm_GlobalTheory_SW_WeilAdm_sum_quot_comp
import Theorems.Thm_GlobalTheory_SW_WeilAdm_mem_sub
import Theorems.Thm_GlobalTheory_SW_WeilAdm_rho_congr
import Theorems.Thm_GlobalTheory_SW_WeilAdm_mul_mem_cols
import Theorems.Thm_GlobalTheory_SW_Base_mem_of_coprime
import Theorems.Thm_GlobalTheory_SW_Model_mem_of_coprime


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
    (hΛ' : ∀ x, x ∈ Λ' ↔ ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) {s R c : ℕ} (hs0 : 0 < s)
    (hs : s.Coprime c) [Fintype (Quo Λ' N s)]
    (h2 : ∀ v ∈ Λ', (s : E) • v ∈ Λ) {φ : Matrix (Fin n) (Fin N) E → ℂ} (hφ : LevelL Λ R φ)
    {g g' : M2 E N} (hg : IntM g) (hg' : IntM g') (e : g * g' = (c : E) • 1) :
    ∑ q : Quo Λ' N s, rho R (q.out.1 * g) φ = ∑ q : Quo Λ' N s, rho R q.out.1 φ := by
  refine sum_quot_comp _ (fun x : cols Λ' N => rho R x.1 φ) (rho_congr hΛ hΛ' h2 hφ)
    (fun x => ⟨x.1 * g, mul_mem_cols x.2 hg⟩) fun x y h => ?_
  obtain ⟨z, hz, ez⟩ := (mem_sub _).1 h
  have hsE : (s : E) ≠ 0 := by exact_mod_cast hs0.ne'
  refine (mem_sub _).2 ⟨(s : E)⁻¹ • (x - y).1, fun i => mem_of_coprime Λ' hs ?_ ?_,
    smul_inv_smul₀ hsE _⟩
  · have : (s : E) • ((s : E)⁻¹ • (x - y).1)ᵀ i = (x - y).1ᵀ i := smul_inv_smul₀ hsE _
    rw [this]; exact (x - y).2 i
  · have e3 : (s : E) • z = (x - y).1 * g := by
      rw [ez]; exact (Matrix.sub_mul _ _ _).symm
    have e4 : z * g' = (c : E) • (s : E)⁻¹ • (x - y).1 := by
      rw [smul_comm, eq_inv_smul_iff₀ hsE, ← Matrix.smul_mul, e3, Matrix.mul_assoc, e,
        Matrix.mul_smul, Matrix.mul_one]
    have := mul_mem_cols hz hg' i
    rwa [e4] at this
end GlobalTheory.SW.WeilAdm
