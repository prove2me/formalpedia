-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.fourthRoot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:55:29.855581+00:00
-- url     : https://prove2.me/submissions/56a013cd-ab62-4444-9bf8-37fb2ead2e0b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_tens4Mem
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_slice_ins
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_ins_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.ThetaVec
open Formalism.L2.Th1 Formalism.L2.Th1.H Complex GlobalTheory.ThetaInter
open scoped BigOperators ComplexConjugate Real
variable (L : PeriodPair)
variable {n : Type} [Fintype n]
namespace GlobalTheory.Mem.Col2.ThetaVec
theorem _root_.solution : FourthRoot := by
  intro n _ h Λ α h0 P hP hne hline
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 hne
  constructor
  · have hf := ins_mem h0 hP z₀
    obtain ⟨c, hc⟩ := hline _ (tens4Mem n h Λ α (fun _ => fun x => P (ins z₀ x)) fun _ => hf)
    have hz : ins z₀ (slice 0 z₀) = z₀ := by
      funext ⟨a, i⟩
      by_cases hw : a = 0 <;> simp [ins, slice, hw]
    have hc0 : c ≠ 0 := by
      rintro rfl
      have := congrFun hc fun w => z₀ (0, w.2)
      rw [zero_smul, Pi.zero_apply, Finset.prod_eq_zero_iff] at this
      obtain ⟨a, -, ha⟩ := this
      exact hz₀ (hz ▸ ha)
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq c⁻¹ (n := 4) (by norm_num)
    refine ⟨r • fun x => P (ins z₀ x), Submodule.smul_mem _ r hf, ?_⟩
    funext v
    have := congrFun hc v
    simp only [tens4, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at this ⊢
    rw [this, hr, inv_mul_cancel_left₀ hc0]
  · intro θ hθ hP4
    obtain ⟨a, ha⟩ : ∃ a, θ a ≠ 0 := ⟨slice 0 z₀, fun h0 => hz₀ (by
      rw [← hP4]; exact Finset.prod_eq_zero (Finset.mem_univ 0) h0)⟩
    have span : ∀ G ∈ Th (matH h) α Λ, ∃ c : ℂ, G = c • θ := by
      intro G hG
      obtain ⟨c, hc⟩ := hline _ (tens4Mem n h Λ α ![G, θ, θ, θ] fun b => by fin_cases b <;> simpa)
      refine ⟨c, funext fun x => ?_⟩
      have := congrFun hc (ins (fun w => a w.2) x)
      have hs : ∀ b, slice b (fun w : Fin 4 × n => a w.2) = a := fun _ => rfl
      rw [← hP4] at this
      simp only [tens4, Pi.smul_apply, smul_eq_mul, Fin.prod_univ_four, slice_ins, hs] at this
      simp only [Fin.isValue, if_true, Fin.reduceEq, if_false, Matrix.cons_val] at this
      apply mul_right_cancel₀ (pow_ne_zero 3 ha)
      rw [Pi.smul_apply, smul_eq_mul]
      linear_combination this
    refine ⟨fun θ' hθ' hP' => ?_, span⟩
    obtain ⟨c, rfl⟩ := span θ' hθ'
    refine ⟨c, ?_, rfl⟩
    have := congrFun (hP'.trans hP4.symm) z₀
    rw [← hP4] at hz₀
    simp only [tens4, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at this
    exact mul_right_cancel₀ hz₀ (this.trans (one_mul _).symm)
end GlobalTheory.Mem.Col2.ThetaVec
