-- Prove2me | solution 1 for GlobalTheory.SliceOp.decay_qOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:40:32.989043+00:00
-- url     : https://prove2.me/submissions/b1196aed-b29c-45e9-b3c4-6cbd1244d431

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialOperatorFderivFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialOperatorSchwartzSeminormBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivativeBoundByPartialsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTensorRightOperator
import Theorems.Thm_GlobalTheory_SliceOp_contDiff_qOp_nat
import Theorems.Thm_GlobalTheory_SliceOp_contDiff_qOp
import Theorems.Thm_GlobalTheory_SliceOp_clm_sup_bound
import Theorems.Thm_GlobalTheory_T_iterated_derivative_bound_by_partials
import Theorems.Thm_GlobalTheory_T_partial_operator_fderiv_formula
import Theorems.Thm_GlobalTheory_T_partial_operator_schwartz_seminorm_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SliceSchwartz
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.SliceOp
open GlobalTheory.SliceSchwartz
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']
namespace GlobalTheory.SliceOp
theorem _root_.solution (n : ℕ) : ∀ (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (k : ℕ),
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (z : κ ⊕ κ₁' → V),
      ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (qOp P f) z‖ ≤ C * s.sup (schwartzSeminormFamily ℂ (κ ⊕ κ' → V) ℂ) f := by
  induction n with
  | zero =>
    intro P k
    obtain ⟨s, C, hC, h⟩ := GlobalTheory.T.partial_operator_schwartz_seminorm_bound V κ κ' κ₁' P k
    exact ⟨s, C, hC, fun f z => by rw [norm_iteratedFDeriv_zero]; exact h f z⟩
  | succ n ih =>
    intro P k
    obtain ⟨CE, hCE, hE⟩ := GlobalTheory.T.iterated_derivative_bound_by_partials (κ ⊕ κ₁' → V)
    set b := Module.finBasis ℝ (κ ⊕ κ₁' → V)
    obtain ⟨s1, C1, hC1, h1⟩ := ih P k
    choose s1' C1' hC1' h1' using fun i => clm_sup_bound (pd (padL (κ' := κ') (b i ∘ Sum.inl))) s1
    choose s2 C2 hC2 h2 using fun i => ih ((pd (b i ∘ Sum.inr)).comp P) k
    refine ⟨Finset.univ.sup (fun i => s1' i ∪ s2 i), CE * ∑ i, (C1 * C1' i + C2 i),
      mul_nonneg hCE (Finset.sum_nonneg fun i _ => add_nonneg (mul_nonneg hC1 (hC1' i)) (hC2 i)), fun f z => ?_⟩
    set p := schwartzSeminormFamily ℂ (κ ⊕ κ' → V) ℂ
    set S := (Finset.univ.sup (fun i => s1' i ∪ s2 i)).sup p f
    have hmono : ∀ i (t : Finset (ℕ × ℕ)), t ⊆ s1' i ∪ s2 i → t.sup p f ≤ S := by
      intro i t ht
      exact Seminorm.le_def.1 (Finset.sup_mono (ht.trans
        (Finset.le_sup (f := fun i => s1' i ∪ s2 i) (Finset.mem_univ i)))) f
    have key : ∀ i, ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ (qOp P f) w (b i)) z‖
        ≤ (C1 * C1' i + C2 i) * S := by
      intro i
      have hfun : (fun w => fderiv ℝ (qOp P f) w (b i)) =
          qOp P (pd (padL (κ' := κ') (b i ∘ Sum.inl)) f) + qOp ((pd (b i ∘ Sum.inr)).comp P) f :=
        funext fun w => (GlobalTheory.T.partial_operator_fderiv_formula V κ κ' κ₁' P f).2 w (b i)
      rw [hfun, iteratedFDeriv_add_apply (contDiff_qOp_nat n _ _).contDiffAt (contDiff_qOp_nat n _ _).contDiffAt]
      have e1 := h1 (pd (padL (κ' := κ') (b i ∘ Sum.inl)) f) z
      have e1' := h1' i f
      have e2 := h2 i f z
      have m1 := hmono i (s1' i) Finset.subset_union_left
      have m2 := hmono i (s2 i) Finset.subset_union_right
      have hz : 0 ≤ ‖z‖ ^ k := by positivity
      calc ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (qOp P (pd (padL (κ' := κ') (b i ∘ Sum.inl)) f)) z +
              iteratedFDeriv ℝ n (qOp ((pd (b i ∘ Sum.inr)).comp P) f) z‖
          ≤ ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (qOp P (pd (padL (κ' := κ') (b i ∘ Sum.inl)) f)) z‖ +
              ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (qOp ((pd (b i ∘ Sum.inr)).comp P) f) z‖ := by
            rw [← mul_add]; exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hz
        _ ≤ C1 * (C1' i * S) + C2 i * S := by
            refine add_le_add (e1.trans (mul_le_mul_of_nonneg_left (e1'.trans
              (mul_le_mul_of_nonneg_left m1 (hC1' i))) hC1)) (e2.trans (mul_le_mul_of_nonneg_left m2 (hC2 i)))
        _ = (C1 * C1' i + C2 i) * S := by ring
    have hz : 0 ≤ ‖z‖ ^ k := by positivity
    calc ‖z‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) (qOp P f) z‖
        ≤ ‖z‖ ^ k * (CE * ∑ i, ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ (qOp P f) w (b i)) z‖) :=
          mul_le_mul_of_nonneg_left (hE _ (contDiff_qOp P f) n z) hz
      _ = CE * ∑ i, ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ (qOp P f) w (b i)) z‖ := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]; congr 1; funext i; ring
      _ ≤ CE * ∑ i, (C1 * C1' i + C2 i) * S :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => key i) hCE
      _ = (CE * ∑ i, (C1 * C1' i + C2 i)) * S := by rw [mul_assoc, Finset.sum_mul]
end GlobalTheory.SliceOp
