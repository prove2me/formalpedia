-- Prove2me | solution 1 for GlobalTheory.PartRed.intLaw_direct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:24:57.409182+00:00
-- url     : https://prove2.me/submissions/6b0a0907-bd3a-4617-ac28-34c581de82d8

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
import Theorems.Thm_GlobalTheory_PartRed_fillAt_add_single
import Theorems.Thm_GlobalTheory_PartRed_circle_neg_mul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_PartRedEval_fillAt_add_single
import Theorems.Thm_GlobalTheory_T_schwartzBruhat_comp_affine_matrix
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
theorem _root_.solution (ψ : AddChar k Circle) (ν : Measure k) (L : SB (Matrix R Q k) →ₗ[ℂ] M)
    (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q) (hI : e ∉ I) (hE : e ∉ E)
    (h : ∀ (a : k) (Φ Φ' : SB (Matrix R Q k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single e.1 e.2 a)) →
      L Φ' = (ψ (w (Matrix.single e.1 e.2 a)) : ℂ) • L Φ) :
    IntLaw L ψ ν w β E I e := by
  intro a Φ
  have hmem1 : (fun t => Φ.1 (t + Matrix.single e.1 e.2 a)) ∈ SB (Matrix R Q k) := by
    have := GlobalTheory.T.schwartzBruhat_comp_affine_matrix k R Q 1 (Matrix.single e.1 e.2 a) Φ.1 Φ.2
    simpa using this
  let Φa : SB (Matrix R Q k) := ⟨_, hmem1⟩
  refine ⟨(ψ (-w (Matrix.single e.1 e.2 a)) : ℂ) • Φa, ?_, fun x => ?_⟩
  · rw [map_smul, h a Φ Φa (fun t => rfl), smul_smul, circle_neg_mul, one_smul]
  · unfold red
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Φa]
    congr 1
    funext y
    rw [← fillAt_add_single β E I x y e hI hE a, map_add, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
end GlobalTheory.PartRed
