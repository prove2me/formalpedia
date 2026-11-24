-- Prove2me | solution 1 for GlobalTheory.HilbFam.constTerm_eq_zetaVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:49:37.709691+00:00
-- url     : https://prove2.me/submissions/11410106-e7cc-4431-b022-5ebac0465a28

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ZetaValueIdeals
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialZetaConstTermEqRationalValue
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ZetaValueIdeals_IsClassZeta_eqOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam
namespace GlobalTheory.HilbFam
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ) (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ), 1 ≤ k → ZetaVals k z → IsPartialZeta C Z → (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) = ((z C / 2 ^ Module.finrank ℚ F : ℚ) : ℂ) := by
  intro F _ _ _ k z C Z hk hz hZ
  obtain ⟨Z', hZ', e⟩ := hz C
  have hne : (1 - (k : ℂ)) ∈ ({1}ᶜ : Set ℂ) := by
    have : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    simpa using this
  have h : Z (1 - (k : ℂ)) = Z' (1 - (k : ℂ)) :=
    GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.IsClassZeta.eqOn (C := C) (Z := Z) (Z' := Z') hZ hZ' hne
  rw [h, e]
  push_cast
  rw [div_eq_mul_inv, mul_comm, inv_pow]
end GlobalTheory.HilbFam
