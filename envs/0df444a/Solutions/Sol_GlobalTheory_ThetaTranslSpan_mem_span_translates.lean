-- Prove2me | solution 1 for GlobalTheory.ThetaTranslSpan.mem_span_translates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:05.320352+00:00
-- url     : https://prove2.me/submissions/a4bb8af0-f549-4da7-9832-91a141823782

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EntirePeriodicEqZeroOfFourierCoeffEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependentThetaPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Theorems.Thm_GlobalTheory_ThetaTranslSpan_mem_of_eigen
import Theorems.Thm_GlobalTheory_ThetaTranslSpan_span_eq_top
import Theorems.Thm_GlobalTheory_ThetaTranslSpan_exists_im_eq_lattice
import Theorems.Thm_GlobalTheory_ThetaTranslSpan_exists_log_addChar
import Theorems.Thm_GlobalTheory_ThetaTranslSpan_herm_swap
import Theorems.Thm_GlobalTheory_ThetaTranslSpan_exists_eq_smul
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaTranslSpan
variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
namespace GlobalTheory.ThetaTranslSpan
theorem _root_.solution : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.PosDef → ∀ (Λ : AddSubgroup (Fin g → ℂ)), DiscreteTopology Λ → (∀ v, (∀ a ∈ Λ, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = k) ↔ v ∈ Λ) → ∀ (χ θ : (Fin g → ℂ) → ℂ), Differentiable ℂ θ → θ ≠ 0 → (∀ a ∈ Λ, ‖χ a‖ = 1) → (∀ a ∈ Λ, ∀ z, θ (z + a) = χ a * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec z) + Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) * θ z) → ∀ (M : ℕ) (Λ₁ : AddSubgroup (Fin g → ℂ)), 0 < M → Λ₁ ≤ Λ → (∀ v, (∀ a ∈ Λ₁, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = M * k) ↔ v ∈ Λ₁) → ∀ F : (Fin g → ℂ) → ℂ, Differentiable ℂ F → (∀ a ∈ Λ₁, ∀ z, F (z + a) = χ a * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec z) + Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) * F z) → F ∈ Submodule.span ℂ {G : (Fin g → ℂ) → ℂ | ∃ y : Fin g → ℂ, (M : ℂ) • y ∈ Λ₁ ∧ G = fun z => Complex.exp (-(Real.pi * (star y ⬝ᵥ Hm.mulVec z))) * θ (z + y)} := by
  intro g Hm hH Λ hd hΛ χ θ hθ h0 hχ hθt M Λ₁ hM hle hΛ₁ F hF hFt
  let L : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule Λ
  haveI hL : DiscreteTopology L := hd
  have hsp : Submodule.span ℝ (L : Set (Fin g → ℂ)) = ⊤ := span_eq_top hH Λ fun v => (hΛ v).1
  haveI : Module.Finite ℤ Λ := (inferInstance : Module.Finite ℤ L)
  haveI : Module.Free ℤ Λ := (inferInstance : Module.Free ℤ L)
  have hMs : ∀ y a : Fin g → ℂ, (star ((M : ℂ) • y) ⬝ᵥ Hm.mulVec a).im =
      M * (star y ⬝ᵥ Hm.mulVec a).im := fun y a => by
    rw [star_smul, smul_dotProduct]; simp
  haveI : Finite (Λ ⧸ Λ₁.addSubgroupOf Λ) := by
    haveI : AddGroup.FG Λ := Module.Finite.iff_addGroup_fg.1 inferInstance
    refine AddCommGroup.finite_of_fg_torsion _ fun q => ?_
    induction q using QuotientAddGroup.induction_on with
    | H a =>
      refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨M, hM, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
        AddSubgroup.coe_nsmul, ← Nat.cast_smul_eq_nsmul ℂ]
      refine (hΛ₁ _).1 fun b hb => ?_
      obtain ⟨k, hk⟩ := (hΛ a).2 a.2 b (hle hb)
      exact ⟨k, by rw [hMs, hk]⟩
  let j : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun a z => χ a * Complex.exp
    (Real.pi * (star a ⬝ᵥ Hm.mulVec z) + Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a))
  have hj0 : ∀ a ∈ Λ, ∀ z, j a z ≠ 0 := fun a ha z =>
    mul_ne_zero (fun h => by simpa [h] using hχ a ha) (Complex.exp_ne_zero _)
  have hjs : ∀ a z w, j a (z + w) = j a z * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec w)) :=
    fun a z w => by
      simp only [j, mulVec_add, dotProduct_add]
      rw [mul_assoc (χ a), ← Complex.exp_add]; congr 2; ring
  have hlin : ∀ a : Fin g → ℂ, Differentiable ℂ fun z : Fin g → ℂ => star a ⬝ᵥ Hm.mulVec z :=
    fun a => by
      simp only [dotProduct, mulVec]
      fun_prop
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 h0
  refine mem_of_eigen Λ Λ₁ hle j hj0 (fun a ha b hb z => ?_)
    { carrier := {G | Differentiable ℂ G}
      add_mem' := fun h1 h2 => h1.add h2
      zero_mem' := differentiable_const 0
      smul_mem' := fun c _ h => h.const_smul c } _ F (fun a ha => ?_) hFt
    (fun ψ hψ hψ₁ G hG hGt => ?_)
  · have h1 : j (a + b) z₀ = j a (z₀ + b) * j b z₀ := by
      refine mul_right_cancel₀ hz₀ ?_
      have e1 : θ (z₀ + (a + b)) = j (a + b) z₀ * θ z₀ := hθt _ (Λ.add_mem ha hb) _
      have e2 : θ (z₀ + b + a) = j a (z₀ + b) * θ (z₀ + b) := hθt _ ha _
      have e3 : θ (z₀ + b) = j b z₀ * θ z₀ := hθt _ hb _
      rw [← e1, mul_assoc, ← e3, ← e2]; congr 1; abel
    obtain ⟨w, rfl⟩ : ∃ w, z = z₀ + w := ⟨z - z₀, by abel⟩
    rw [show z₀ + w + b = z₀ + b + w by abel, hjs (a + b), hjs a (z₀ + b), hjs b, h1, star_add,
      add_dotProduct, mul_add, Complex.exp_add]
    ring
  · refine Differentiable.mul (Differentiable.inv ?_ (hj0 a ha)) (hF.comp (differentiable_id.add_const a))
    exact (differentiable_const _).mul (((hlin a).const_mul _).add_const _).cexp
  · have hG' : Differentiable ℂ G := hG
    obtain ⟨φ, hφ⟩ := exists_log_addChar ψ hψ
    obtain ⟨y, hy⟩ := exists_im_eq_lattice hH L hsp (-φ)
    have hy' : ∀ a : Λ, (star y ⬝ᵥ Hm.mulVec a).im = -φ a := hy
    have hyM : (M : ℂ) • y ∈ Λ₁ := (hΛ₁ _).1 fun a ha => by
      have h := hψ₁ ⟨a, hle ha⟩ ha
      rw [hφ, Complex.exp_eq_one_iff] at h
      obtain ⟨n, hn⟩ := h
      have h2 : ((φ ⟨a, hle ha⟩ : ℝ) : ℂ) = n :=
        mul_left_cancel₀ Complex.two_pi_I_ne_zero (hn.trans (mul_comm _ _))
      have h3 : φ ⟨a, hle ha⟩ = n := by exact_mod_cast h2
      exact ⟨-n, by rw [hMs, hy' ⟨a, hle ha⟩, h3]; simp⟩
    obtain ⟨c, hc⟩ := exists_eq_smul hH Λ hΛ χ θ
      (fun w => Complex.exp (Real.pi * (star y ⬝ᵥ Hm.mulVec w)) * G (w + -y)) hχ hθ h0 hθt
      (((hlin y).const_mul _).cexp.mul (hG'.comp (differentiable_id.add_const _)))
      (fun a ha z => by
        have e := hGt ⟨a, ha⟩ (z + -y)
        have e2 : star y ⬝ᵥ Hm.mulVec a - star a ⬝ᵥ Hm.mulVec y =
            -(2 * Complex.I * (φ ⟨a, ha⟩ : ℝ)) := by
          rw [herm_swap hH y a, Complex.star_def, Complex.sub_conj, hy' ⟨a, ha⟩]; push_cast; ring
        change _ = j a z * _
        rw [show z + a + -y = z + -y + a by abel, e, hjs, hφ, mulVec_add, dotProduct_add, mul_add,
          Complex.exp_add, mulVec_neg, dotProduct_neg]
        have e3 : Complex.exp (Real.pi * (star y ⬝ᵥ Hm.mulVec a)) *
            Complex.exp (2 * Real.pi * Complex.I * (φ ⟨a, ha⟩ : ℝ)) *
            Complex.exp (Real.pi * -(star a ⬝ᵥ Hm.mulVec y)) = 1 := by
          rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_zero]; congr 1
          linear_combination (Real.pi : ℂ) * e2
        linear_combination (Complex.exp (Real.pi * (star y ⬝ᵥ Hm.mulVec z)) * j a z *
          G (z + -y)) * e3)
    have hGe : G = (c * Complex.exp (-(Real.pi * (star y ⬝ᵥ Hm.mulVec y)))) •
        fun z => Complex.exp (-(Real.pi * (star y ⬝ᵥ Hm.mulVec z))) * θ (z + y) := by
      ext z
      have h := congrFun hc (z + y)
      simp only [Pi.smul_apply, smul_eq_mul, add_neg_cancel_right, mulVec_add, dotProduct_add,
        mul_add, Complex.exp_add] at h
      simp only [Pi.smul_apply, smul_eq_mul, Complex.exp_neg]
      have := Complex.exp_ne_zero (Real.pi * (star y ⬝ᵥ Hm.mulVec y))
      have := Complex.exp_ne_zero (Real.pi * (star y ⬝ᵥ Hm.mulVec z))
      field_simp
      linear_combination h
    rw [hGe]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hyM, rfl⟩)
end GlobalTheory.ThetaTranslSpan
