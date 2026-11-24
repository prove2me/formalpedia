-- Prove2me | solution 1 for GlobalTheory.PeriodNonempty.exists_diag_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:06:04.716848+00:00
-- url     : https://prove2.me/submissions/c4b3eec9-b09f-4631-9bae-649a2da299a9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Theorems.Thm_GlobalTheory_PeriodNonempty_exists_diag
import Theorems.Thm_GlobalTheory_PeriodNonempty_trace_real
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
namespace GlobalTheory.PeriodNonempty
theorem _root_.solution {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] (J : W →ₗ[ℝ] W) (hJ : ∀ x, J (J x) = -x) (ρ : 𝓞 E →+* Module.End ℝ W) {g : ℕ}
    (ty : Fin g → (E →+* ℂ))
    (h : ∀ a, J ∘ₗ ρ a = ρ a ∘ₗ J ∧ LinearMap.trace ℝ W (ρ a) = 2 * (∑ i, ty i (a : E)).re ∧
      LinearMap.trace ℝ W (J ∘ₗ ρ a) = -2 * (∑ i, ty i (a : E)).im) :
    ∃ e : W ≃ₗ[ℝ] (Fin g → ℂ), (∀ v, e (J v) = Complex.I • e v) ∧
      ∀ a v i, e (ρ a v) i = ty i (a : E) * e v i := by
  let φ : ℂ →ₐ[ℝ] Module.End ℝ W := Complex.liftAux (J : Module.End ℝ W) (by ext x; simp [hJ])
  letI : Module ℂ W := Module.compHom W (φ : ℂ →+* Module.End ℝ W)
  have hsm : ∀ (z : ℂ) (v : W), z • v = z.re • v + z.im • J v := fun z v => by
    change φ z v = _
    simp [φ, Complex.liftAux_apply]
  haveI : IsScalarTower ℝ ℂ W := ⟨fun r z v => by
    simp [hsm, smul_add, smul_smul]⟩
  haveI : FiniteDimensional ℂ W := Module.Finite.of_restrictScalars_finite ℝ ℂ W
  have hI : ∀ v : W, Complex.I • v = J v := fun v => by simp [hsm]
  let L : 𝓞 E → Module.End ℂ W := fun a =>
    { toFun := ρ a
      map_add' := map_add _
      map_smul' := fun z v => by
        have := LinearMap.congr_fun (h a).1 v
        simp only [LinearMap.comp_apply] at this
        simp [hsm, this] }
  let ρ' : 𝓞 E →+* Module.End ℂ W :=
    { toFun := L
      map_one' := by ext v; simp [L]
      map_mul' := fun a b => by ext v; simp [L]
      map_zero' := by ext v; simp [L]
      map_add' := fun a b => by ext v; simp [L] }
  obtain ⟨e, he⟩ := exists_diag ρ' ty (fun a => by
    have h1 := trace_real (ρ' a)
    have h2 := trace_real (Complex.I • ρ' a)
    have e1 : (ρ' a).restrictScalars ℝ = ρ a := rfl
    have e2 : (Complex.I • ρ' a).restrictScalars ℝ = J ∘ₗ ρ a := by
      ext v; exact hI _
    rw [e1, (h a).2.1] at h1
    rw [e2, (h a).2.2, map_smul] at h2
    apply Complex.ext
    · linarith
    · simp only [smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im] at h2
      linarith)
  exact ⟨e.restrictScalars ℝ, fun v => by rw [← hI]; exact e.map_smul _ _, he⟩
end GlobalTheory.PeriodNonempty
