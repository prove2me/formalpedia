-- Prove2me | solution 1 for GlobalTheory.PartRed.evalLaw_direct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:32:52.32246+00:00
-- url     : https://prove2.me/submissions/2fb5c666-23ff-4216-a4f1-cd55df2da58e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMulAddCharLinearFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatCompAffineMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEvaluateEntryOfMulLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionIntegrateEntryOfTranslationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionLowerEntryMultiplicationLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionUpperFreeEntryTranslationLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEqFlatMapFourierJacobiRowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapFourierJacobiRowAddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapLawsFactorFourierJacobiSource
import Theorems.Thm_GlobalTheory_PartRed_red_mul_entry
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_schwartzBruhat_mul_addChar_linearForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory GlobalTheory.PartRed
open GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] {M : Type} [AddCommGroup M]
  [Module ℂ M]
namespace GlobalTheory.PartRed
theorem _root_.solution (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ) (L : SB (Matrix R Q k) →ₗ[ℂ] M)
    (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q) (hI : e ∉ I) (hE : e ∉ E)
    (h : ∀ (b : k) (Φ Φ' : SB (Matrix R Q k)), (∀ t, Φ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Φ.1 t) →
      L Φ' = L Φ) :
    EvalLaw L ψ ν w β E I e := by
  intro b Φ
  let f : Matrix R Q k →ₗ[k] k :=
    { toFun := fun t => b * t e.1 e.2
      map_add' := fun s t => by simp [mul_add]
      map_smul' := fun a t => by simp; ring }
  have hmem : (fun t => (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Φ.1 t) ∈ SB (Matrix R Q k) := by
    have := GlobalTheory.T.schwartzBruhat_mul_addChar_linearForm k ψ hψ R Q f (-(b * β e.1 e.2)) Φ.1 Φ.2
    convert this using 3 with t
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk]
    ring_nf
  refine ⟨⟨_, hmem⟩, h b Φ ⟨_, hmem⟩ (fun t => rfl), fun x => ?_⟩
  exact red_mul_entry ψ ν w β E I e hI hE (fun s => (ψ (b * (s - β e.1 e.2)) : ℂ)) Φ.1 x
end GlobalTheory.PartRed
