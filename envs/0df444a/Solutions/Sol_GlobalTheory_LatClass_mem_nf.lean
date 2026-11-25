-- Prove2me | solution 1 for GlobalTheory.LatClass.mem_nf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:21:24.261349+00:00
-- url     : https://prove2.me/submissions/c376588a-1f15-4585-8696-af573f7096e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZpowMulMemPow
import Theorems.Thm_GlobalTheory_LatClass_mem_pow_zero
import Theorems.Thm_GlobalTheory_LatClass_zpow_mul_mem_pow
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_NormalRepresentationLattice_nfBasis_val
import Theorems.Thm_GlobalTheory_StepData_mem_latOf_one
import Theorems.Thm_GlobalTheory_StepData_mulVec_mem_latOf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.LatClass
variable {k : Type} [Field k] [ValuativeRel k] {ϖ : kˣ}
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.LatClass
theorem _root_.solution {g : GL n k} {e : Fin (c + 1) → ℤ} {z : n → k} {y : n ⊕ Fin (c + 1) → k} :
    y ∈ latOf (nfBasis ϖ g e z) ↔
      (fun r => y (.inl r) - y (.inr 0) * z r) ∈ latOf g ∧ ∀ i, y (.inr i) ∈ powInt ϖ (e i) := by
  have key : (nfBasis ϖ g e z).val *ᵥ Sum.elim ((g⁻¹).val *ᵥ fun r => y (.inl r) - y (.inr 0) * z r)
      (fun i => (ϖ : k) ^ (-e i) * y (.inr i)) = y := by
    have h0 : ∀ a : ℤ, (ϖ : k) ^ a ≠ 0 := fun a => zpow_ne_zero _ ϖ.ne_zero
    rw [nfBasis_val, fromBlocks_mulVec]
    ext (r | i)
    · simp only [Sum.elim_inl, Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_mulVec, Units.mul_inv, one_mulVec,
        Pi.add_apply]
      simp [mulVec, dotProduct]
      field_simp
      ring
    · simp [mulVec_diagonal, h0]
  conv_lhs => rw [← key, ← mul_one (nfBasis ϖ g e z)]
  rw [mul_one, ← mul_one (nfBasis ϖ g e z)]
  conv_lhs => enter [2]; rw [mul_one]
  rw [mulVec_mem_latOf, mem_latOf_one, Sum.forall]
  refine and_congr Iff.rfl (forall_congr' fun i => ?_)
  rw [Sum.elim_inr, ← mem_pow_zero (ϖ := ϖ), zpow_mul_mem_pow]; simp
end GlobalTheory.LatClass
