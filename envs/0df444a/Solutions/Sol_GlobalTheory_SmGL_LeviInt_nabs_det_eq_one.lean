-- Prove2me | solution 1 for GlobalTheory.SmGL.LeviInt.nabs_det_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:33:26.411598+00:00
-- url     : https://prove2.me/submissions/81296eca-216e-496e-9a75-4e5711a2c602

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviIntegralFacts
import Theorems.Thm_GlobalTheory_SmGL_nabs_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open scoped ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.LeviInt
open MeasureTheory Topology
open scoped ENNReal
open ValuativeRel Matrix
namespace GlobalTheory.SmGL.LeviInt
namespace _root_.GlobalTheory.SmGL.LeviInt
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {g : GL n k}
    (hg : g ∈ _root_.GlobalTheory.SplitWeil.KO k n) :
    _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det g) = 1 := by
  obtain ⟨h1, h2⟩ := (_root_.GlobalTheory.SplitFlip.mem_KO_iff g).1 hg
  have hdet : ∀ M : Matrix n n k, (∀ i j, M i j ∈ (valuation k).integer) →
      M.det ∈ (valuation k).integer := by
    intro M hM
    rw [Matrix.det_apply]
    refine sum_mem fun σ _ => ?_
    rw [Units.smul_def]
    exact zsmul_mem (prod_mem fun i _ => hM _ _) _
  apply _root_.GlobalTheory.SmGL.nabs_eq_one
  have hd1 : valuation k ((GeneralLinearGroup.det g : kˣ) : k) ≤ 1 := by
    rw [← Valuation.mem_integer_iff, Matrix.GeneralLinearGroup.val_det_apply]
    exact hdet _ h1
  have hd2 : valuation k (((GeneralLinearGroup.det g)⁻¹ : kˣ) : k) ≤ 1 := by
    rw [← map_inv, ← Valuation.mem_integer_iff, Matrix.GeneralLinearGroup.val_det_apply]
    exact hdet _ h2
  have hprod : valuation k ((GeneralLinearGroup.det g : kˣ) : k) *
      valuation k (((GeneralLinearGroup.det g)⁻¹ : kˣ) : k) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  exact le_antisymm hd1 (hprod ▸ mul_le_of_le_one_right' hd2)
end _root_.GlobalTheory.SmGL.LeviInt
end GlobalTheory.SmGL.LeviInt
