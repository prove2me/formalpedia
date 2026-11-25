-- Prove2me | solution 1 for GlobalTheory.LocFlat.pureRow_of_exchange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:56:18.739305+00:00
-- url     : https://prove2.me/submissions/0981f3d2-af03-48cf-93f8-3f27f9088cc3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatRowMapEqRootExchangeOperatorTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeRowUnipotentLatticeFrameConjApplyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeRowUnipotentMemSourceLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IteratedDepthOneLevelCharOfOneRowFirstBlockStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricPositionLevelCharacterEqOneSingleRowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapRowEqZeroUnlessRowMemDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatRowIndicatorOfSymLevelExchange
import Theorems.Thm_GlobalTheory_LocFlat_lam_rowE_symLevel
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_StepData_Chain_ofType_laws
import Theorems.Thm_GlobalTheory_StepData_Chain_ofType_regular
import Theorems.Thm_GlobalTheory_StepData_volNat_Cgrp_pos
import Theorems.Thm_GlobalTheory_T_flatMapRow_eq_zero_unless_row_mem_dualLattice
import Theorems.Thm_GlobalTheory_T_flatRowMap_eq_rootExchangeOperator_translate
import Theorems.Thm_GlobalTheory_T_rootExchangeRowUnipotent_mem_sourceLevel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.LocFlat
namespace GlobalTheory.LocFlat
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type)
    [Fintype t] [DecidableEq t], S.Pattern t → S.ExchangeAt t ν → GlobalTheory.LocFlat.PureRow S t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hP hE
  haveI := hν.1
  intro j c H r hc
  have hodd := S.odd
  obtain ⟨C, hC, hEq⟩ := hE j (c + 1) (by omega) (r + 1) (by omega) (by omega) (by omega)
  have HR : (S.T t).Regular := Chain.ofType_regular _ _ _ _ _
  have HL : (S.T t).Laws := Chain.ofType_laws _ _ _ _ _
  set Φ := (S.T t).Phi j (c + 1) (by omega) with hΦ
  set V := volNat ν ((S.T t).bas (j + 1) (c + 1) (by omega)) (Cgrp ((S.T t).lev (j + 1) (c + 1) (by omega)).J 1)
    with hV
  have hVpos : 0 < V :=
    volNat_Cgrp_pos ν (HR.2.2 (j + 1) (c + 1) (by omega)).1 (HR.2.2 (j + 1) (c + 1) (by omega)).2.1 _ 1
  have hom1 : om ((S.T t).mu (j + 1)) 1 1 Φ = Φ := by
    funext z; simp [om, nabs]
  have hentry : ∀ x₀, (S.T t).entry S.ψ ν j c H 1 1 x₀ = ((V⁻¹ : ℝ) : ℂ) * opE S.ψ ν 1 Φ x₀ := by
    intro x₀
    simp only [Chain.entry, xi, flat]
    rw [hom1]
  refine ⟨C * V, mul_pos hC hVpos, fun x => ?_⟩
  by_cases hu : x (Sum.inr ()) ∈ box (XIx (Fin κ) t j) (S.ϖ ^ (r + 1))
  · rw [if_pos hu, mul_one, hentry]
    have hm := GlobalTheory.T.rootExchangeRowUnipotent_mem_sourceLevel k s κ S t hP j c H r hc _ hu
    have hl := lam_rowE_symLevel k s κ S t j c H r hc _ hm
    have hdet : Matrix.GeneralLinearGroup.det (rowE (c + 1 + 1) (r + 1) (x (Sum.inr ()))) = 1 := by
      ext; simp [rowE, lowU, Matrix.det_fromBlocks_zero₁₂]
    have hT := (HL.1 j (c + 1) (by omega)).1 ⟨_, hm⟩
    rw [hl] at hT
    have hfun : (fun z => Φ (z * (rowE (c + 1 + 1) (r + 1) (x (Sum.inr ()))).val)) = Φ := by
      funext z
      have := congrFun hT z
      simpa [om, hdet, nabs] using this
    rw [GlobalTheory.T.flatRowMap_eq_rootExchangeOperator_translate k S.ψ ν S.cond.continuous inferInstance (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) (c + 1)
      (r + 1) (by omega) (by omega) Φ (HR.1 j (c + 1) (by omega)) x]
    erw [hfun]
    rw [congrFun hEq]
    have hV0 : (V : ℂ) ≠ 0 := by exact_mod_cast hVpos.ne'
    rw [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv]
    field_simp
  · rw [if_neg hu, mul_zero, GlobalTheory.T.flatMapRow_eq_zero_unless_row_mem_dualLattice k ν s κ S t j c H r hc x hu]
end GlobalTheory.LocFlat
