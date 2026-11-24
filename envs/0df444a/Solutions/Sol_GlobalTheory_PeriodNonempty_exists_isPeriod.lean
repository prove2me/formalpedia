-- Prove2me | solution 1 for GlobalTheory.PeriodNonempty.exists_isPeriod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:25:05.658595+00:00
-- url     : https://prove2.me/submissions/37b85c28-ae17-40a4-9069-4776d4fdaa3d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Theorems.Thm_GlobalTheory_PeriodNonempty_exists_diag_real
import Theorems.Thm_GlobalTheory_PeriodNonempty_exists_herm
import Theorems.Thm_GlobalTheory_PeriodNonempty_sum_type
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
open NumberField Matrix
open scoped TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodNonempty
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.PeriodNonempty
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (hty : IsTypeFn H D.p D.q ty) : ∃ P, IsPeriod D ty P := by
  classical
  haveI := D.fin
  haveI := D.proj
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  haveI : Module.Free ℤ D.La := inferInstance
  obtain ⟨J, hJ, hinv, hpos, htr⟩ := D.dom
  let ρ₀ : 𝓞 E →+* Module.End ℤ D.La := (Algebra.lsmul ℤ ℤ D.La : 𝓞 E →ₐ[ℤ] Module.End ℤ D.La)
  let ρ : 𝓞 E →+* Module.End ℝ (ℝ ⊗[ℤ] D.La) :=
    (Module.End.baseChangeHom ℤ ℝ D.La : Module.End ℤ D.La →+* Module.End ℝ (ℝ ⊗[ℤ] D.La)).comp ρ₀
  have hρ : ∀ a x, ρ a (1 ⊗ₜ x) = 1 ⊗ₜ (a • x) := fun a x => rfl
  obtain ⟨e, heJ, heρ⟩ := exists_diag_real J hJ ρ ty (fun a => htr a (ρ a) _ (hρ a) (sum_type H hty _))
  let P : D.La →+ (Fin g → ℂ) :=
    { toFun := fun x => e (1 ⊗ₜ x)
      map_zero' := by simp
      map_add' := fun x y => by rw [TensorProduct.tmul_add, map_add] }
  have hP : ∀ x, P x = e (1 ⊗ₜ x) := fun _ => rfl
  let b := Module.Free.chooseBasis ℤ D.La
  let c := (b.baseChange ℝ).map e
  have hc : ∀ i, c i = P (b i) := fun i => by simp [c, hP]
  have hrange : P.range = (Submodule.span ℤ (Set.range c)).toAddSubgroup := by
    have h1 : Set.range c = P.toIntLinearMap '' Set.range b := by
      rw [← Set.range_comp]; congr 1; funext i; exact hc i
    rw [h1, ← Submodule.map_span, b.span_eq]
    ext z; simp
  refine ⟨P, fun a x i => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hP, hP, ← hρ, heρ]
  · rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hP, e.map_eq_zero_iff] at hx
    apply b.ext_elem
    intro i
    have := congrArg (fun v => (b.baseChange ℝ).repr v i) hx
    simpa using this
  · rw [hrange]; infer_instance
  · rw [eq_top_iff, ← c.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨b i, (hc i).symm⟩
  · have halt0 : ∀ x y, D.EF x y = -D.EF y x := fun x y => by
      have := D.alt (x + y)
      simp only [map_add, LinearMap.add_apply, D.alt] at this
      linarith
    have halt : ∀ x y, D.EF.baseChange ℝ x y = -D.EF.baseChange ℝ y x := fun x y => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h']; ring
      | tmul r x =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add y y' h h' => simp only [map_add, LinearMap.add_apply, h, h']; ring
        | tmul r' y => simp [halt0 x y, mul_comm]
    have hs : ∀ z, e.symm (Complex.I • z) = J (e.symm z) := fun z => by
      rw [e.symm_apply_eq, heJ, e.apply_symm_apply]
    obtain ⟨Hm, h1, h2, h3⟩ := exists_herm
      ((D.EF.baseChange ℝ).comp e.symm.toLinearMap e.symm.toLinearMap)
      (fun x y => halt _ _) (fun x y => by simp [hs, hinv])
      (fun x hx => by simpa [hs] using hpos (e.symm x) (by simpa using hx))
    refine ⟨Hm, h1, h2, fun x y => ?_⟩
    rw [h3]
    simp [hP]
end GlobalTheory.PeriodNonempty
