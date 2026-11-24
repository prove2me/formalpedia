-- Prove2me | solution 1 for GlobalTheory.PeriodDatum.exists_datum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:39:56.299309+00:00
-- url     : https://prove2.me/submissions/ec459452-4fc4-4d75-8d7c-34c82e4f8b58

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HostGeneratorPowFourTraceNormModEight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TwoMulEqOfIsTypeFn
import Theorems.Thm_GlobalTheory_PeriodDatum_lattice_equiv
import Theorems.Thm_GlobalTheory_PeriodDatum_hermForm_smul_left
import Theorems.Thm_GlobalTheory_PeriodDatum_hermForm_smul_right
import Theorems.Thm_GlobalTheory_PeriodDatum_hermForm_add_left
import Theorems.Thm_GlobalTheory_PeriodDatum_hermForm_add_right
import Theorems.Thm_GlobalTheory_PeriodDatum_hermForm_self_im
import Theorems.Thm_GlobalTheory_PeriodDatum_two_mul_eq_of_isTypeFn
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_baseChange
import Theorems.Thm_GlobalTheory_PeriodNonempty_sum_type
import Theorems.Thm_GlobalTheory_PeriodNonempty_trace_real
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_finrank_int_eq_mul_of_finite
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul
attribute [local simp] GlobalTheory.coe_symplecticGroupMap
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct
open GlobalTheory GlobalTheory.PeriodDatum
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.PeriodDatum
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (La : Type)
    [AddCommGroup La] [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La) (p q g : ℕ) (ty : Fin g → (E →+* ℂ))
    (P : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), IsTypeFn H p q ty → Function.Bijective EF →
    (∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (H.bar a • y)) →
    (∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i) → Function.Injective P → DiscreteTopology P.range →
    Submodule.span ℝ (Set.range P) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ x y, (hermForm Hm (P x) (P y)).im = EF x y) →
    ∃ (D' : Datum H) (e : D'.La ≃ₗ[𝓞 E] La), D'.p = p ∧ D'.q = q ∧ ∀ x y, D'.EF x y = EF (e x) (e y) := by
  intro E _ _ _ H La _ _ EF p q g ty P Hm hty hbij hadj hlin hinj hdisc hspan hH hpos him
  classical
  obtain ⟨hfin, hrk, e, he⟩ := lattice_equiv P hinj hdisc hspan
  haveI : Module.Finite (𝓞 E) La := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) La
  have htor : Submodule.torsion (𝓞 E) La = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨a, ha⟩, hx⟩
    have ha0 : (a : E) ≠ 0 := by
      simpa using nonZeroDivisors.ne_zero ha
    rw [Submodule.mem_bot]
    apply hinj
    funext i
    have h1 := hlin a x i
    have h2 : a • x = 0 := hx
    rw [h2, map_zero] at h1
    rw [map_zero]
    exact (mul_eq_zero.1 h1.symm).resolve_left ((map_ne_zero (ty i)).2 ha0)
  haveI : Module.Flat (𝓞 E) La := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  haveI : Module.FinitePresentation (𝓞 E) La := Module.finitePresentation_of_finite _ _
  have hproj : Module.Projective (𝓞 E) La := Module.Flat.projective_of_finitePresentation
  have hrank : Module.finrank (𝓞 E) La = p + q := by
    have h1 := finrank_int_eq_mul_of_finite (O := 𝓞 E) (M := La)
    rw [hrk, two_mul_eq_of_isTypeFn H hty, RingOfIntegers.rank] at h1
    exact (Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1).symm
  have het : ∀ (r : ℝ) x, e (r ⊗ₜ x) = (r : ℂ) • P x := fun r x => by
    rw [← he, Complex.coe_smul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hB : ∀ x y, EF.baseChange ℝ x y = (hermForm Hm (e x) (e y)).im := fun x y => by
    induction x using TensorProduct.induction_on with
    | zero => simp [hermForm]
    | add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h', hermForm_add_left, Complex.add_im]
    | tmul r x =>
      induction y using TensorProduct.induction_on with
      | zero => simp [hermForm]
      | add y y' h h' => simp only [map_add, h, h', hermForm_add_right, Complex.add_im]
      | tmul r' y =>
        rw [het, het, hermForm_smul_left, hermForm_smul_right, LinearMap.BilinForm.baseChange_tmul]
        simp [him]
        ring
  let d : (Fin g → ℂ) → Module.End ℂ (Fin g → ℂ) := fun c => Matrix.toLin' (Matrix.diagonal c)
  have hd : ∀ c z i, d c z i = c i * z i := fun c z i => by simp [d, Matrix.mulVec_diagonal]
  have hdt : ∀ c, LinearMap.trace ℝ _ (e.symm.conj ((d c).restrictScalars ℝ)) = 2 * (∑ i, c i).re := fun c => by
    rw [LinearMap.trace_conj', PeriodNonempty.trace_real]
    simp [d]
  let J : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La := e.symm.conj ((d fun _ => Complex.I).restrictScalars ℝ)
  have hJ : ∀ x, e (J x) = Complex.I • e x := fun x => by
    funext i
    simp [J, LinearEquiv.conj_apply, hd]
  refine ⟨{ La := La, fin := inferInstance, proj := hproj, EF := EF, alt := fun x => ?_, unimod := hbij,
            adj := hadj, p := p, q := q, rank := hrank, dom := ⟨J, fun x => ?_, fun x y => ?_, fun x hx => ?_, ?_⟩ },
    LinearEquiv.refl _ _, rfl, rfl, fun _ _ => rfl⟩
  · have := him x x
    rw [hermForm_self_im hH] at this
    exact_mod_cast this.symm
  · apply e.injective
    rw [hJ, hJ, smul_smul, Complex.I_mul_I, map_neg, neg_smul, one_smul]
  · rw [hB, hB, hJ, hJ, hermForm_smul_left, hermForm_smul_right]
    simp
  · rw [hB, hJ, hermForm_smul_left]
    simpa using hpos (e x) (by simpa using hx)
  · intro a A t hA ht
    rw [← PeriodNonempty.sum_type H hty] at ht
    have hAe : ∀ x i, e (A x) i = ty i (a : E) * e x i := fun x i => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x x' h h' => simp only [map_add, Pi.add_apply, h, h', mul_add]
      | tmul r x =>
        have : (r ⊗ₜ[ℤ] x : ℝ ⊗[ℤ] La) = r • (1 ⊗ₜ[ℤ] x) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this, map_smul, hA, map_smul, map_smul, he, he]
        simp only [Pi.smul_apply, hlin, Complex.real_smul]
        ring
    have h1 : A = e.symm.conj ((d fun i => ty i (a : E)).restrictScalars ℝ) := by
      refine LinearMap.ext fun x => e.injective (funext fun i => ?_)
      simp [LinearEquiv.conj_apply, hd, hAe]
    have h2 : J ∘ₗ A = e.symm.conj ((d fun i => Complex.I * ty i (a : E)).restrictScalars ℝ) := by
      refine LinearMap.ext fun x => e.injective (funext fun i => ?_)
      simp [LinearEquiv.conj_apply, hd, hAe, hJ, mul_assoc]
    refine ⟨?_, ?_, ?_⟩
    · refine LinearMap.ext fun x => e.injective (funext fun i => ?_)
      simp only [LinearMap.comp_apply, hJ, hAe, Pi.smul_apply, smul_eq_mul]
      ring
    · rw [h1, hdt, ht]
    · rw [h2, hdt, ht, ← Finset.mul_sum]
      simp
end GlobalTheory.PeriodDatum
