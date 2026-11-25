-- Prove2me | solution 1 for GlobalTheory.ThetaTranslJet.exists_translates_jet_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:59:38.708925+00:00
-- url     : https://prove2.me/submissions/9646faed-7ee6-4dae-adc2-110ee66f8be1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImFormApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaFunctionIsogenyRestriction
import Theorems.Thm_GlobalTheory_ThetaTranslJet_exists_prod_ne_zero
import Theorems.Thm_GlobalTheory_ThetaTranslJet_exists_theta
import Theorems.Thm_GlobalTheory_ThetaTranslJet_differentiable_herm
import Theorems.Thm_GlobalTheory_ThetaTranslJet_mult_add
import Theorems.Thm_GlobalTheory_ThetaTranslJet_exists_completion
import Theorems.Thm_GlobalTheory_ThetaTranslJet_exists_mem_ne_zero
import Theorems.Thm_GlobalTheory_ThetaGauss_exists_zero_fderiv_ne_zero
import Theorems.Thm_GlobalTheory_ThetaGauss_transl_apply
import Theorems.Thm_GlobalTheory_ThetaJet_TwistedLaw_mul
import Theorems.Thm_GlobalTheory_ThetaTranslSpan_exists_im_eq_lattice
import Theorems.Thm_GlobalTheory_ThetaTranslSpan_exists_log_addChar
import Theorems.Thm_GlobalTheory_ThetaTranslSpan_herm_swap
import Theorems.Thm_GlobalTheory_ThetaTranslSpan_mem_span_translates
import Theorems.Thm_GlobalTheory_ThetaTranslSpan_span_eq_top
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ThetaGauss.transl_apply
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open Matrix ReciprocityTheory.ChartRestriction.G.I2
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaTranslJet
variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
namespace GlobalTheory.ThetaTranslJet
theorem _root_.solution : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.PosDef → ∀ (Λ : AddSubgroup (Fin g → ℂ)), DiscreteTopology Λ → (∀ v, (∀ a ∈ Λ, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = k) ↔ v ∈ Λ) → ∀ (χ θ : (Fin g → ℂ) → ℂ), Differentiable ℂ θ → θ ≠ 0 → (∀ a ∈ Λ, ‖χ a‖ = 1) → (∀ a ∈ Λ, ∀ z, θ (z + a) = χ a * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec z) + Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) * θ z) → ∀ (M : ℕ) (Λ₁ : AddSubgroup (Fin g → ℂ)), Λ₁ ≤ Λ → (∀ v, (∀ a ∈ Λ₁, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = M * k) ↔ v ∈ Λ₁) → ∀ (n : ℕ) (P : MvPolynomial (Fin n × Fin g) ℂ), P ≠ 0 → P.totalDegree + 2 ≤ M → ∃ y : Fin n → Fin g → ℂ, (∀ b, (M : ℂ) • y b ∈ Λ₁) ∧ ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (fun q => (Pi.single q.1 (Pi.single q.2 (1 : ℂ) : Fin g → ℂ) : Fin n → Fin g → ℂ)) (fun z : Fin n → Fin g → ℂ => ∏ b, Complex.exp (-(Real.pi * (star (y b) ⬝ᵥ Hm.mulVec (z b)))) * θ (z b + y b)) 0 ≠ 0 := by
  intro g Hm hH Λ hd hΛ χ θ hθ h0 hχ hθt M Λ₁ hle hΛ₁ n P hP hM
  classical
  have hM0 : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hM0' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  haveI hd₁ : DiscreteTopology Λ₁ := DiscreteTopology.of_subset (s := (Λ : Set (Fin g → ℂ))) hd hle
  set H' : Matrix (Fin g) (Fin g) ℂ := (M : ℝ)⁻¹ • Hm with hH'def
  have hH' : H'.PosDef := hH.smul (inv_pos.2 (Nat.cast_pos.2 (by omega)))
  have hHH : ∀ v w : Fin g → ℂ, star v ⬝ᵥ Hm.mulVec w = M * (star v ⬝ᵥ H'.mulVec w) := fun v w => by
    rw [hH'def, smul_mulVec, dotProduct_smul, Complex.real_smul]
    push_cast
    field_simp
  have hΛ' : ∀ v, (∀ a ∈ Λ₁, ∃ k : ℤ, (star v ⬝ᵥ H'.mulVec a).im = k) ↔ v ∈ Λ₁ := fun v => by
    rw [← hΛ₁]
    simp only [hHH, ← Complex.ofReal_natCast, Complex.im_ofReal_mul, mul_right_inj' hM0']
  obtain ⟨χ₁, θ₁, hθ₁, h0₁, hχ₁, hθt₁⟩ := exists_theta hH' Λ₁ hΛ'
  have hχ₁0 : ∀ a ∈ Λ₁, χ₁ a ≠ 0 := fun a ha h => by simpa [h] using hχ₁ a ha
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 h0
  obtain ⟨z₁, hz₁⟩ := Function.ne_iff.1 h0₁
  have hadd : ∀ a b : Λ₁, χ (a + b) / χ₁ (a + b) ^ M = χ a / χ₁ a ^ M * (χ b / χ₁ b ^ M) := by
    intro a b
    rw [mult_add hz₀ hθt (hle a.2) (hle b.2), mult_add hz₁ hθt₁ a.2 b.2, mul_pow, mul_pow,
      ← Complex.exp_nat_mul, hHH, hHH, ← mul_sub, mul_left_comm (M : ℂ),
      mul_div_mul_right _ _ (Complex.exp_ne_zero _), div_mul_div_comm]
  have hψ : ∀ a : Λ₁, ‖χ a / χ₁ a ^ M‖ = 1 := fun a => by
    rw [norm_div, norm_pow, hχ _ (hle a.2), hχ₁ _ a.2, one_pow, div_one]
  let ψ : AddChar Λ₁ ℂ :=
    { toFun := fun a => χ a / χ₁ a ^ M
      map_zero_eq_one' := by
        have h := hadd 0 0
        have h1 : χ (0 : Λ₁) / χ₁ (0 : Λ₁) ^ M ≠ 0 := fun h => by
          have := hψ 0
          rw [h, norm_zero] at this
          exact zero_ne_one this
        rw [← AddSubgroup.coe_add, add_zero] at h
        exact (mul_eq_left₀ h1).1 h.symm
      map_add_eq_mul' := hadd }
  let L : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule Λ₁
  haveI hL : DiscreteTopology L := hd₁
  haveI : Module.Free ℤ Λ₁ := (inferInstance : Module.Free ℤ L)
  obtain ⟨φ, hφ⟩ := ThetaTranslSpan.exists_log_addChar ψ hψ
  obtain ⟨S, hS⟩ := ThetaTranslSpan.exists_im_eq_lattice hH' L
    (ThetaTranslSpan.span_eq_top hH' Λ₁ fun v => (hΛ' v).1) (-φ)
  have hSχ : ∀ a ∈ Λ₁, χ₁ a ^ M *
      Complex.exp (Real.pi * (star a ⬝ᵥ H'.mulVec S - star S ⬝ᵥ H'.mulVec a)) = χ a := by
    intro a ha
    have e1 : (star S ⬝ᵥ H'.mulVec a).im = -φ ⟨a, ha⟩ := hS ⟨a, ha⟩
    have e2 : χ a / χ₁ a ^ M = _ := hφ ⟨a, ha⟩
    rw [div_eq_iff (pow_ne_zero _ (hχ₁0 a ha))] at e2
    rw [e2, mul_comm, ← neg_sub, ThetaTranslSpan.herm_swap hH' S a, Complex.star_def,
      Complex.sub_conj, e1]
    congr 2
    push_cast
    ring
  have hdf : ∀ (b : Fin n) (a : Fin g → ℂ),
      Differentiable ℂ fun z : Fin n → Fin g → ℂ => θ₁ (z b + a) := fun b a =>
    hθ₁.comp ((differentiable_apply b).add_const a)
  obtain ⟨s, hs⟩ := exists_prod_ne_zero (κ := Fin n × {a // θ₁ a = 0})
    (fun q : Fin n × Fin g =>
      (Pi.single q.1 (Pi.single q.2 (1 : ℂ) : Fin g → ℂ) : Fin n → Fin g → ℂ))
    (fun k z => θ₁ (z k.1 + k.2)) (fun k => ThetaJet.analyticAt_of_differentiable (hdf _ _) 0)
    (fun k => by simpa using k.2.2) (fun c hc => by
      obtain ⟨⟨b, i⟩, hb⟩ := Function.ne_iff.1 hc
      obtain ⟨a, ha, ha'⟩ := GlobalTheory.ThetaGauss.exists_zero_fderiv_ne_zero g H' hH' Λ₁ hd₁ hΛ' χ₁ θ₁ hθ₁ h0₁ hχ₁ hθt₁
        (fun i => c (b, i)) (Function.ne_iff.2 ⟨i, hb⟩)
      refine ⟨(b, ⟨a, ha⟩), ?_⟩
      have h1 : HasFDerivAt (fun z : Fin n → Fin g → ℂ => θ₁ (z b + a))
          ((fderiv ℂ θ₁ a).comp (ContinuousLinearMap.proj b)) 0 := by
        refine HasFDerivAt.comp (f := fun z : Fin n → Fin g → ℂ => z b + a) 0 ?_
          ((hasFDerivAt_apply b 0).add_const a)
        simpa using (hθ₁ a).hasFDerivAt
      rw [h1.fderiv]
      simp only [← smul_eq_mul, ← map_smul, ← map_sum, ContinuousLinearMap.comp_apply]
      convert ha' using 2
      funext i'
      simp [Fintype.sum_prod_type, Pi.single_apply, ite_apply]) hP
  choose h hh hh0 hht using fun b : Fin n => exists_completion hθ₁ h0₁ hθt₁ M S
    (Finset.univ.filter fun j => (s j).1 = b) (fun j => ((s j).2 : Fin g → ℂ))
    (by have := Finset.card_filter_le Finset.univ fun j => (s j).1 = b
        rw [Finset.card_univ, Fintype.card_fin] at this
        omega)
  have hne := hs (fun z => ∏ b, h b (z b)) (Finset.analyticAt_fun_prod _ fun b _ =>
    ThetaJet.analyticAt_of_differentiable ((hh b).comp (differentiable_apply b)) 0)
    (Finset.prod_ne_zero_iff.2 fun b _ => hh0 b)
  obtain ⟨G, hG, hG0⟩ := exists_mem_ne_zero P _ _ (by
      rintro _ ⟨y, -, rfl⟩
      exact ((differentiable_herm y).const_mul _).neg.cexp.mul
        (hθ.comp (differentiable_id.add_const y)))
    (fun b z => (∏ j ∈ Finset.univ.filter fun j => (s j).1 = b, θ₁ (z + (s j).2)) * h b z)
    (fun b => ThetaTranslSpan.mem_span_translates g Hm hH Λ hd hΛ χ θ hθ h0 hχ hθt M Λ₁ (by omega)
      hle hΛ₁ _ (Differentiable.mul (fun z => (HasFDerivAt.finsetProd fun j _ =>
        ((hθ₁.comp (differentiable_id.add_const _)) z).hasFDerivAt).differentiableAt) (hh b))
      fun a ha z => by
        rw [hht b a ha z, hSχ a ha, hHH, hHH]
        congr 3
        ring)
    (by
      refine ne_of_eq_of_ne (congrArg (fun F => polyDeriv P _ F 0) (funext fun z => ?_)) hne
      rw [Finset.prod_mul_distrib, ← Finset.prod_fiberwise Finset.univ (fun j => (s j).1)]
      congr 1
      refine Finset.prod_congr rfl fun b _ => Finset.prod_congr rfl fun j hj => ?_
      rw [(Finset.mem_filter.1 hj).2])
  choose y hy hy' using hG
  refine ⟨y, hy, ?_⟩
  simpa only [hy'] using hG0
end GlobalTheory.ThetaTranslJet
