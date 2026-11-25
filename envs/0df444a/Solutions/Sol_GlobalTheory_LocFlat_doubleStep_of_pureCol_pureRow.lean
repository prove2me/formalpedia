-- Prove2me | solution 1 for GlobalTheory.LocFlat.doubleStep_of_pureCol_pureRow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:32.074973+00:00
-- url     : https://prove2.me/submissions/b977e990-796d-4e61-86b6-c10756a88e3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatRowMapEqRootExchangeOperatorTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymLevelDoubleStepOfFlatColumnFlatRow
import Theorems.Thm_GlobalTheory_LocFlat_DoubleStepProof_vol_box_pos
import Theorems.Thm_GlobalTheory_LocFlat_DoubleStepProof_integral_box
import Theorems.Thm_GlobalTheory_LocFlat_DoubleStepProof_hat_box
import Theorems.Thm_GlobalTheory_LocFlat_DoubleStepProof_Phi_mul_rowE
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_om_mem_SB
import Theorems.Thm_GlobalTheory_StepData_Chain_ofType_regular
import Theorems.Thm_GlobalTheory_T_flatRowMap_eq_rootExchangeOperator_translate


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
noncomputable section
open GlobalTheory.LocFlat.DoubleStepProof
open Classical
namespace GlobalTheory.LocFlat
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.OneIndexAt t ν → GlobalTheory.LocFlat.PureCol S t ν → GlobalTheory.LocFlat.PureRow S t ν → GlobalTheory.LocFlat.DoubleStep S t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hP hOne hCol hRow j c H r hc
  haveI := hν.1
  obtain ⟨C₁, hC₁, hC1⟩ := hCol j (c + 1) (by omega) (r + 1) (by omega)
  obtain ⟨V, hV, hVe⟩ := hat_box (n := XIx (Fin κ) t (j + 1)) S.cond ν (S.ϖ ^ (r + 1))
  have hhat : ∀ (p : Matrix (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) k × Matrix (XIx (Fin κ) t (j + 1 + 1)) (XIx (Fin κ) t (j + 1)) k)
      (u : XIx (Fin κ) t (j + 1) → k),
      hat S.ψ ν (-1) (fun y => flCol S.ψ ν (r + 1 + 1) ((S.T t).Phi j (c + 1 + 1) (by omega))
        (fromCols p.1 (Matrix.of fun r _ => y r))) u =
        (C₁ : ℂ) * (S.T t).entry S.ψ ν j (c + 1) (by omega) 1 1 p.1 *
          ((V : ℂ) * (if u ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ (r + 1)) then 1 else 0)) := by
    intro p u
    rw [← hVe u]
    unfold hat
    rw [← integral_const_mul]
    congr 1
    funext y
    dsimp only
    rw [hC1, toCols₁_fromCols]
    have ey : (fun a => (fromCols p.1 (Matrix.of fun r _ => y r) : Matrix _ _ k) a (Sum.inr ())) = y := by funext a; simp
    rw [ey]
    ring
  have hΦ₂ : (S.T t).Phi (j + 1) (c + 1) (by omega) ∈ SB _ := (Chain.ofType_regular _ _ _ _ _).1 (j + 1) (c + 1) (by omega)
  refine ⟨fun h hne => ?_, ?_⟩
  · obtain ⟨p, hp⟩ := Function.ne_iff.mp hne
    refine hOne (j + 1) (c + 1) (by omega) (r + 1) (by omega) (by omega) h (fun h0 => hp ?_)
    simp only [contr]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [Pi.zero_apply]
    rw [hhat p u]
    by_cases hu : u ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ (r + 1))
    · have e1 : (fromRows p.2 (Matrix.of fun _ => u)) (Sum.inr ()) = u := by funext a; simp
      rw [GlobalTheory.T.flatRowMap_eq_rootExchangeOperator_translate k S.ψ ν S.cond.continuous hν.1 _ _ (c + 1) (r + 1) (by omega) (by omega) _
        (om_mem_SB _ 1 h hΦ₂) _, e1, toRows₁_fromRows]
      obtain ⟨a, ha⟩ := Phi_mul_rowE S t hP j c (by omega) r hc u hu
      have e2 : (fun z => om (S.μ (j + 1 + 1)) 1 h ((S.T t).Phi (j + 1) (c + 1) (by omega)) (z * (rowE (c + 1 + 1) (r + 1) u).val)) =
          fun z => a * om (S.μ (j + 1 + 1)) 1 h ((S.T t).Phi (j + 1) (c + 1) (by omega)) z := by
        funext z
        simp only [om]
        rw [show (h⁻¹ : GL _ k).val * (z * (rowE (c + 1 + 1) (r + 1) u).val) * (1 : GL (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) k).val =
          ((h⁻¹ : GL _ k).val * z * (1 : GL (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) k).val) * (rowE (c + 1 + 1) (r + 1) u).val by
          simp [Matrix.mul_assoc], ha]
        ring
      have e3 : opE S.ψ ν (r + 1) (fun z => a * om (S.μ (j + 1 + 1)) 1 h ((S.T t).Phi (j + 1) (c + 1) (by omega)) z) p.2 = 0 := by
        unfold opE
        simp_rw [mul_assoc]
        rw [integral_const_mul]
        have := congrFun h0 p.2
        unfold opE at this
        rw [this]; simp
      refine mul_eq_zero_of_left ?_ _
      rw [← e3]
      congr 1
    · rw [if_neg hu]; simp
  · obtain ⟨C₂, hC₂, hC2⟩ := hRow (j + 1) c H r hc
    have hW := vol_box_pos (n := XIx (Fin κ) t (j + 1)) ν (S.ϖ ^ (r + 1))
    set W := ((Measure.pi fun _ : XIx (Fin κ) t (j + 1) => ν) (box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ (r + 1)) : Set (XIx (Fin κ) t (j + 1) → k))).toReal with hWdef
    refine ⟨C₁ * C₂ * V * W, by positivity, fun p => ?_⟩
    simp only [contr]
    refine (integral_congr_ae (μ := Measure.pi fun _ => ν)
      (g := fun u => ((C₁ : ℂ) * C₂ * V * (S.T t).entry S.ψ ν j (c + 1) (by omega) 1 1 p.1 *
        (S.T t).entry S.ψ ν (j + 1) c H 1 1 p.2) * (if u ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ (r + 1)) then 1 else 0))
      (Filter.Eventually.of_forall fun u => ?_)).trans ?_
    · dsimp only
      rw [hhat p u, hC2]
      have e1 : (fromRows p.2 (Matrix.of fun _ => u)) (Sum.inr ()) = u := by funext a; simp
      rw [e1, toRows₁_fromRows]
      split_ifs <;> ring
    · rw [integral_const_mul, integral_box]
      push_cast
      ring
end GlobalTheory.LocFlat
