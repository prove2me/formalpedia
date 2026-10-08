-- Prove2me | solution 1 for OAI.Erdos970.ErdosPrimeInputs.MertensStrong.second_error_strong
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:10:00.883081+00:00
-- url     : https://prove2.me/submissions/e151ca07-823a-4107-a058-2921e48b5cf1

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_Erdos970_I1Bound
import Theorems.Thm_Erdos970_LogDerivZetaBoundedAndHolo
import Theorems.Thm_Erdos970_SmoothedChebyshevClose
import Theorems.Thm_Erdos970_SmoothedChebyshevPull1

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.EulerMaclaurin
namespace Erdos970

open _root_.Finset _root_.Interval _root_.MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}


@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Mathlib.Algebra.Notation.Support
namespace Erdos970

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : _root_.Function.support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : _root_.Function.support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function

end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Rectangle
namespace Erdos970

open _root_.Complex _root_.Set _root_.Topology

open scoped _root_.Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle



end Rectangle




@[simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl





































end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.ResidueCalcOnRectangles
namespace Erdos970

open _root_.Complex _root_.BigOperators _root_.Nat _root_.Classical _root_.Real _root_.Topology _root_.Filter
open _root_.Set _root_.MeasureTheory _root_.intervalIntegral _root_.Asymptotics

open scoped _root_.Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

















theorem HolomorphicOn.vanishesOnRectangle [CompleteSpace E]
    {U : Set ℂ} (f_holo : HolomorphicOn f U)
    (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w
    (f_holo.mono hU)




































































end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.SmoothExistence
namespace Erdos970


open _root_.MeasureTheory _root_.Set _root_.Real
open scoped _root_.ContDiff

lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) := by
  have := exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def,
        Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)
  obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩ := this
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
  use Ψ
  simp only [range_subset_iff, mem_Icc] at hΨrange
  refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a d) isCompact_Icc
    simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
    bound
  · apply Set.indicator_le'
    · intro x hx
      rw [hΨ1 x |>.mp, Pi.one_apply]
      simpa using hx
    · exact fun x _ ↦ (hΨrange x).1
  · intro x
    apply Set.le_indicator_apply
    · exact fun _ ↦ (hΨrange x).2
    · intro hx
      rw [← hΨ0 x |>.mp]
      simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
  · ext x
    simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]

lemma SmoothExistence :
    ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
    ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, ν x / x = 1 := by
  suffices h : ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
      ν.support ⊆ Set.Icc (1 / 2) 2 ∧ 0 < ∫ x in Set.Ici 0, ν x / x by
    obtain ⟨ν, hν, hνnonneg, hνsupp, hνpos⟩ := h
    let c := (∫ x in Ici 0, ν x / x)
    use fun y ↦ ν y / c
    refine ⟨hν.div_const c, fun y ↦ div_nonneg (hνnonneg y) (le_of_lt hνpos), ?_, ?_⟩
    · rw [Function.support_div, Function.support_const (ne_of_lt hνpos).symm, inter_univ]
      convert (preTransparency := .instances) hνsupp
    · simp only [div_right_comm _ c _, integral_div c, div_self <| ne_of_gt hνpos, c]
  have := smooth_urysohn_support_Ioo (a := 1 / 2) (b := 1) (c := 3 / 2) (d := 2)
    (by linarith) (by linarith)
  obtain ⟨ν, hνContDiff, _, hν0, hν1, hνSupport⟩ := this
  use ν, hνContDiff
  unfold indicator at hν0 hν1
  simp only [mem_Icc, Pi.one_apply, Pi.le_def, mem_Ioo] at hν0 hν1
  simp only [hνSupport, subset_def, mem_Ioo, mem_Icc, and_imp]
  split_ands
  · exact fun x ↦ le_trans (by simp [apply_ite]) (hν0 x)
  · exact fun y hy hy' ↦ ⟨by linarith, by linarith⟩
  · rw [integral_pos_iff_support_of_nonneg]
    · simp only [Function.support_div, measurableSet_Ici, Measure.restrict_apply',
        hνSupport, Function.support_id']
      have : (Ioo (1 / 2 : ℝ) 2 ∩ {0}ᶜ ∩ Ici 0) = Ioo (1 / 2) 2 := by
        ext x
        simp only [one_div, mem_inter_iff, mem_Ioo, mem_compl_iff, mem_singleton_iff, mem_Ici]
        bound
      simp only [this, volume_Ioo, ENNReal.ofReal_pos, sub_pos, gt_iff_lt]
      linarith
    · simp_rw [Pi.le_def, Pi.zero_apply]
      intro y
      by_cases h : y ∈ Function.support ν
      · apply div_nonneg <| le_trans (by simp [apply_ite]) (hν0 y)
        rw [hνSupport, mem_Ioo] at h
        linarith [h.left]
      · simp only [Function.mem_support, ne_eq, not_not] at h
        simp [h]
    · have : (fun x ↦ ν x / x).support ⊆ Icc (1 / 2) 2 := by
        rw [Function.support_div, hνSupport]
        exact (inter_subset_left).trans Ioo_subset_Icc_self
      apply (integrableOn_iff_integrable_of_support_subset this).mp
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply hνContDiff.continuous.continuousOn.div continuousOn_id ?_
      simp only [mem_Icc, ne_eq, and_imp, id_eq]
      intros; linarith

end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Sobolev
namespace Erdos970

open _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap _root_.BigOperators
open scoped _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun




section lemmas




end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun



















end CS

namespace trunc







end trunc

namespace W1











end W1

namespace W21













end W21


end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.ZetaConj
namespace Erdos970

open scoped _root_.Complex _root_.ComplexConjugate

theorem deriv_conj_conj' (f : ℂ → ℂ) (p : ℂ) :
    deriv (fun z ↦ conj (f (conj z))) (conj p) = conj (deriv f p) := by
  trans deriv (conj ∘ f ∘ conj) (conj p)
  · rfl
  simp

theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  simp [← deriv_conj_conj']




theorem intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ} :
    ∫ (x : ℝ) in a..b, conj (f x) = conj (∫ (x : ℝ) in a..b, f x) := by
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, integral_conj, ← RCLike.conj_smul,
    ← intervalIntegral.intervalIntegral_eq_integral_uIoc]

end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Fourier
namespace Erdos970

open _root_.FourierTransform _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap VectorFourier _root_.BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]


@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl



@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas


@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Auxiliary
namespace Erdos970

namespace Complex

open _root_.Complex




end Complex

lemma DifferentiableAt.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    DifferentiableAt ℝ (fun x : ℝ ↦ e x) z :=
  hf.hasDerivAt.comp_ofReal.differentiableAt

lemma deriv.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    deriv (fun x : ℝ ↦ e x) z = deriv e z :=
  hf.hasDerivAt.comp_ofReal.deriv


lemma DifferentiableAt.ofReal_comp {z : ℝ} {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z :=
  hf.hasDerivAt.ofReal_comp.differentiableAt


open _root_.Complex _root_.ContinuousLinearMap in
lemma HasDerivAt.of_hasDerivAt_ofReal_comp {z : ℝ} {f : ℝ → ℝ} {u : ℂ}
    (hf : HasDerivAt (fun y ↦ (f y : ℂ)) u z) :
    ∃ u' : ℝ, u = u' ∧ HasDerivAt f u' z := by
  lift u to ℝ
  · have H := (imCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt.deriv
    simp only [Function.comp_def, imCLM_apply, ofReal_im, deriv_const] at H
    rwa [eq_comm, comp_apply, imCLM_apply, toSpanSingleton_apply_one] at H
  refine ⟨u, rfl, ?_⟩
  convert! (preTransparency := .instances) (reCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt
  rw [comp_apply, toSpanSingleton_apply_one, reCLM_apply, ofReal_re]

lemma DifferentiableAt.ofReal_comp_iff {z : ℝ} {f : ℝ → ℝ} :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z ↔ DifferentiableAt ℝ f z := by
  refine ⟨fun H ↦ ?_, ofReal_comp⟩
  obtain ⟨u, _, hu₂⟩ := HasDerivAt.of_hasDerivAt_ofReal_comp H.hasDerivAt
  exact HasDerivAt.differentiableAt hu₂

lemma Differentiable.ofReal_comp_iff {f : ℝ → ℝ} :
    Differentiable ℝ (fun (y : ℝ) ↦ (f y : ℂ)) ↔ Differentiable ℝ f :=
  forall_congr' fun _ ↦ DifferentiableAt.ofReal_comp_iff

lemma deriv.ofReal_comp {z : ℝ} {f : ℝ → ℝ} :
    deriv (fun (y : ℝ) ↦ (f y : ℂ)) z = deriv f z := by
  by_cases hf : DifferentiableAt ℝ f z
  · exact hf.hasDerivAt.ofReal_comp.deriv
  · have hf' := mt DifferentiableAt.ofReal_comp_iff.mp hf
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hf',
      Complex.ofReal_zero]

end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MellinCalculus
namespace Erdos970

open scoped _root_.ContDiff


open _root_.Complex _root_.Topology _root_.Filter _root_.Real _root_.MeasureTheory _root_.Set _root_.Function

theorem MeasureTheory.setIntegral_integral_swap {α : Type*} {β : Type*} {E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : MeasureTheory.Measure α}
    {ν : MeasureTheory.Measure β} [NormedAddCommGroup E]
    [MeasureTheory.SigmaFinite ν] [NormedSpace ℝ E] [MeasureTheory.SigmaFinite μ]
    (f : α → β → E) {s : Set α} {t : Set β}
    (hf : IntegrableOn (f.uncurry) (s ×ˢ t) (μ.prod ν)) :
    (∫ (x : α) in s, ∫ (y : β) in t, f x y ∂ν ∂μ)
      = ∫ (y : β) in t, ∫ (x : α) in s, f x y ∂μ ∂ν := by
  apply integral_integral_swap
  convert (preTransparency := .instances) hf.integrable
  exact Measure.prod_restrict s t

open _root_.Erdos970.MeasureTheory

variable {𝕂 : Type*} [RCLike 𝕂]

lemma MeasureTheory.integral_comp_mul_right_I0i_haar
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (y * a) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  have := integral_comp_mul_right_Ioi (fun y ↦ f y / y) 0 ha
  simp only [RCLike.ofReal_mul, zero_mul, eq_inv_smul_iff₀ (ne_of_gt ha)] at this
  rw [← integral_smul] at this
  rw [← this, setIntegral_congr_fun (by simp)]
  intro _ _
  simp only [RCLike.real_smul_eq_coe_mul]
  rw [mul_comm (a : 𝕂), div_mul, mul_div_assoc, div_self ?_, mul_one]
  exact (RCLike.ofReal_ne_zero).mpr <| ne_of_gt ha


lemma MeasureTheory.integral_comp_mul_left_I0i_haar
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (a * y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  convert (preTransparency := .instances) integral_comp_mul_right_I0i_haar f ha using 5; ring

lemma MeasureTheory.integral_comp_rpow_I0i_haar_real (f : ℝ → ℝ) {p : ℝ} (hp : p ≠ 0) :
    ∫ (y : ℝ) in Ioi 0, |p| * f (y ^ p) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  rw [← integral_comp_rpow_Ioi (fun y ↦ f y / y) hp, setIntegral_congr_fun (by simp)]
  intro y hy
  have ypos : 0 < y := mem_Ioi.mp hy
  simp only [rpow_sub_one ypos.ne', smul_eq_mul]
  field_simp

lemma MeasureTheory.integral_comp_inv_I0i_haar (f : ℝ → 𝕂) :
    ∫ (y : ℝ) in Ioi 0, f (1 / y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  have := integral_comp_rpow_Ioi (fun y ↦ f y / y) (p := -1) (by simp)
  rw [← this, setIntegral_congr_fun (by simp)]
  intro y hy
  have : (y : 𝕂) ≠ 0 := (RCLike.ofReal_ne_zero).mpr <| LT.lt.ne' hy
  simp only [abs_neg, abs_one, rpow_neg_one, map_inv₀, div_inv_eq_mul,
    RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal]
  ring_nf
  simp [field]

lemma MeasureTheory.integral_comp_div_I0i_haar
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (a / y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  calc
    _ = ∫ (y : ℝ) in Ioi 0, f (a * y) / y := ?_
    _ = _ := integral_comp_mul_left_I0i_haar f ha
  convert (preTransparency := .instances) (integral_comp_inv_I0i_haar fun y ↦ f (a * (1 / y))).symm using 4
  · rw [mul_one_div]
  · rw [one_div_one_div]


@[simp]
lemma Function.support_abs {α : Type*} (f : α → 𝕂) :
    (fun x ↦ ‖f x‖).support = f.support := by
  simp only [support, ne_eq]; simp_rw [norm_ne_zero_iff]

@[simp]
lemma Function.support_ofReal {f : ℝ → ℝ} :
    (fun x ↦ ((f x) : ℂ)).support = f.support := by
  apply Function.support_comp_eq (g := ofReal); simp

lemma Function.support_mul_subset_of_subset {s : Set ℝ} {f g : ℝ → 𝕂}
    (fSupp : f.support ⊆ s) : (f * g).support ⊆ s := by
  simp_rw [support_mul', inter_subset, subset_union_of_subset_right fSupp]


lemma Function.support_deriv_subset_Icc {a b : ℝ} {f : ℝ → 𝕂}
    (fSupp : f.support ⊆ Set.Icc a b) :
    (deriv f).support ⊆ Set.Icc a b := by
    have := support_deriv_subset (f := fun x ↦ f x)
    dsimp [tsupport] at this
    have := subset_trans this <| closure_mono fSupp
    rwa [closure_Icc] at this


lemma SetIntegral.integral_eq_integral_inter_of_support_subset {μ : Measure ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s t : Set ℝ} {f : ℝ → E} (h : f.support ⊆ t) (ht : MeasurableSet t) :
    ∫ x in s, f x ∂μ = ∫ x in s ∩ t, f x ∂μ := by
  rw [← setIntegral_indicator ht, indicator_eq_self.2 h]

lemma SetIntegral.integral_eq_integral_inter_of_support_subset_Icc {a b} {μ : Measure ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set ℝ} {f : ℝ → E} (h : f.support ⊆ Icc a b) (hs : Icc a b ⊆ s) :
    ∫ x in s, f x ∂μ = ∫ x in Icc a b, f x ∂μ := by
  rw [SetIntegral.integral_eq_integral_inter_of_support_subset h measurableSet_Icc,
      inter_eq_self_of_subset_right hs]

lemma intervalIntegral.norm_integral_le_of_norm_le_const' {a b C : ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hab : a ≤ b) (h : ∀ x ∈ (Icc a b), ‖f x‖ ≤ C) :
    ‖∫ x in a..b, f x‖ ≤ C * |b - a| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  exact fun x hx ↦ h x <| mem_Icc_of_Ioc <| uIoc_of_le hab ▸ hx

lemma Filter.TendstoAtZero_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂) (ha : 0 < a)
    (fSupp : f.support ⊆ Set.Icc a b) :
    Tendsto f (𝓝[>]0) (𝓝 0) := by
  apply Tendsto.comp (tendsto_nhds_of_eventually_eq ?_) tendsto_id
  filter_upwards [Ioo_mem_nhdsGT ha] with c hc; replace hc := (mem_Ioo.mp hc).2
  have h : c ∉ Icc a b := fun h ↦ by linarith [mem_Icc.mp h]
  convert (preTransparency := .instances) mt (Function.support_subset_iff.mp fSupp c) h; simp

lemma Filter.TendstoAtTop_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂)
    (fSupp : f.support ⊆ Set.Icc a b) :
    Tendsto f atTop (𝓝 0) := by
  apply Tendsto.comp (tendsto_nhds_of_eventually_eq ?_) tendsto_id
  filter_upwards [Ioi_mem_atTop b] with c hc; rw [mem_Ioi] at hc
  have h : c ∉ Icc a b := fun h ↦ by linarith [mem_Icc.mp h]
  convert (preTransparency := .instances) mt (Function.support_subset_iff.mp fSupp c) h; simp

lemma Filter.BigO_zero_atZero_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂) (ha : 0 < a)
    (fSupp : f.support ⊆ Set.Icc a b) :
    f =O[𝓝[>] 0] fun _ ↦ (0 : ℝ) := by
  refine Eventually.isBigO ?_
  filter_upwards [Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < a)] with c hc
  refine norm_le_zero_iff.mpr <| Function.support_subset_iff'.mp fSupp c ?_
  exact fun h ↦ by linarith [mem_Icc.mp h, (mem_Ioo.mp hc).2]

lemma Filter.BigO_zero_atTop_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂)
    (fSupp : f.support ⊆ Set.Icc a b) :
    f =O[atTop] fun _ ↦ (0 : ℝ) := by
  refine Eventually.isBigO ?_
  filter_upwards [Ioi_mem_atTop b] with c hc; replace hc := mem_Ioi.mp hc
  refine norm_le_zero_iff.mpr <| Function.support_subset_iff'.mp fSupp c ?_
  exact fun h ↦ by linarith [mem_Icc.mp h]

open _root_.Erdos970.Filter

lemma deriv.ofReal_comp' {f : ℝ → ℝ} :
    deriv (fun x : ℝ ↦ (f x : ℂ)) = (fun x ↦ ((deriv f) x : ℂ)) :=
  funext fun _ ↦ deriv.ofReal_comp


lemma PartialIntegration (f g : ℝ → ℂ)
    (fDiff : DifferentiableOn ℝ f (Ioi 0))
    (gDiff : DifferentiableOn ℝ g (Ioi 0))
    (fDerivgInt : IntegrableOn (f * deriv g) (Ioi 0))
    (gDerivfInt : IntegrableOn (deriv f * g) (Ioi 0))
    (lim_at_zero : Tendsto (f * g) (𝓝[>] 0) (𝓝 0))
    (lim_at_inf : Tendsto (f * g) atTop (𝓝 0)) :
    ∫ x in Ioi 0, f x * deriv g x = -∫ x in Ioi 0, deriv f x * g x := by
  simpa using integral_Ioi_mul_deriv_eq_deriv_mul
    (fun x hx ↦ fDiff.hasDerivAt (Ioi_mem_nhds hx))
    (fun x hx ↦ gDiff.hasDerivAt (Ioi_mem_nhds hx))
    fDerivgInt gDerivfInt lim_at_zero lim_at_inf

lemma PartialIntegration_of_support_in_Icc {a b : ℝ} (f g : ℝ → ℂ) (ha : 0 < a)
    (h : a ≤ b)
    (fSupp : f.support ⊆ Set.Icc a b)
    (fDiff : DifferentiableOn ℝ f (Ioi 0))
    (gDiff : DifferentiableOn ℝ g (Ioi 0))
    (fderivCont : ContinuousOn (deriv f) (Ioi 0))
    (gderivCont : ContinuousOn (deriv g) (Ioi 0)) :
    ∫ x in Ioi 0, f x * deriv g x = -∫ x in Ioi 0, deriv f x * g x := by
  have Icc_sub : Icc a b ⊆ Ioi 0 := (Icc_subset_Ioi_iff h).mpr ha
  have fderivSupp := Function.support_deriv_subset_Icc fSupp
  have fgSupp : (f * g).support ⊆ Icc a b := Function.support_mul_subset_of_subset fSupp
  have fDerivgInt : IntegrableOn (f * deriv g) (Ioi 0) := by
    apply (integrableOn_iff_integrable_of_support_subset <|
           Function.support_mul_subset_of_subset fSupp).mp
    exact fDiff.continuousOn.mono Icc_sub |>.mul (gderivCont.mono Icc_sub) |>.integrableOn_Icc
  have gDerivfInt : IntegrableOn (deriv f * g) (Ioi 0) := by
    apply (integrableOn_iff_integrable_of_support_subset <|
           Function.support_mul_subset_of_subset fderivSupp).mp
    exact fderivCont.mono Icc_sub |>.mul (gDiff.continuousOn.mono Icc_sub) |>.integrableOn_Icc
  have lim_at_zero : Tendsto (f * g) (𝓝[>]0) (𝓝 0) :=
    TendstoAtZero_of_support_in_Icc (f * g) ha fgSupp
  have lim_at_inf : Tendsto (f * g) atTop (𝓝 0) := TendstoAtTop_of_support_in_Icc (f * g) fgSupp
  apply PartialIntegration f g fDiff gDiff fDerivgInt gDerivfInt lim_at_zero lim_at_inf

local notation (name := mellintransform) "𝓜" => mellin


lemma MellinConvolutionSymmetric (f g : ℝ → 𝕂) {x : ℝ} (xpos : 0 < x) :
    MellinConvolution f g x = MellinConvolution g f x := by
  unfold MellinConvolution
  calc
    _ = ∫ y in Ioi 0, f (y * x) * g (1 / y) / y := ?_
    _ = _ := ?_
  · rw [← integral_comp_mul_right_I0i_haar (fun y ↦ f y * g (x / y)) xpos]
    simp [div_mul_cancel_right₀ <| ne_of_gt xpos]
  · convert (preTransparency := .instances) (integral_comp_inv_I0i_haar fun y ↦ f (y * x) * g (1 / y)).symm using 3
    rw [one_div_one_div, mul_comm, mul_comm_div, one_mul]




lemma MellinConvolutionTransform (f g : ℝ → ℂ) (s : ℂ)
    (hf : IntegrableOn (fun x y ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)).uncurry
      (Ioi 0 ×ˢ Ioi 0)) :
    𝓜 (MellinConvolution f g) s = 𝓜 f s * 𝓜 g s := by
  dsimp [mellin, MellinConvolution]
  set f₁ : ℝ × ℝ → ℂ :=
    fun ⟨x, y⟩ ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)
  calc
    _ = ∫ (x : ℝ) in Ioi 0, ∫ (y : ℝ) in Ioi 0, f₁ (x, y) := ?_
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0, f₁ (x, y) :=
        setIntegral_integral_swap _ hf
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0,
        f y * g (x / y) / ↑y * ↑x ^ (s - 1) := rfl
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0,
        f y * g (x * y / y) / ↑y * ↑(x * y) ^ (s - 1) * y := ?_
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0,
        f y * ↑y ^ (s - 1) * (g x * ↑x ^ (s - 1)) := ?_
    _ = ∫ (y : ℝ) in Ioi 0,
        f y * ↑y ^ (s - 1) * ∫ (x : ℝ) in Ioi 0, g x * ↑x ^ (s - 1) := ?_
    _ = _ := integral_mul_const _ _
  <;> try (rw [setIntegral_congr_fun (by simp)]; intro y hy; simp only [ofReal_mul])
  · simp only [integral_mul_const, f₁, mul_comm]
  · simp only [integral_mul_const]
    have := integral_comp_mul_right_Ioi
      (fun x ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)) 0 hy
    have y_ne_zeroℂ : (y : ℂ) ≠ 0 := slitPlane_ne_zero (Or.inl hy)
    field_simp at this ⊢
    simp only [ofReal_mul, one_div, mul_zero, real_smul, ofReal_inv, field] at this ⊢
    rw [← this]
    field_simp
    congr with x
    ring_nf
  · rw [setIntegral_congr_fun (by simp)]
    intro x hx
    have y_ne_zeroℝ : y ≠ 0 := ne_of_gt (mem_Ioi.mp hy)
    have y_ne_zeroℂ : (y : ℂ) ≠ 0 := by exact_mod_cast y_ne_zeroℝ
    field_simp
    rw [mul_cpow_ofReal_nonneg hy.le hx.le]
    ring
  · apply integral_const_mul
  · congr <;> ext <;> ring


lemma MellinOfPsi_aux {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2)
    {s : ℂ} (hs : s ≠ 0) :
    ∫ (x : ℝ) in Ioi 0, (ν x) * (x : ℂ) ^ (s - 1) =
    - (1 / s) * ∫ (x : ℝ) in Ioi 0, (deriv ν x) * (x : ℂ) ^ s := by
  let g (s : ℂ) := fun (x : ℝ)  ↦ x ^ s / s
  have gderiv {s : ℂ} (hs : s ≠ 0) {x: ℝ} (hx : x ∈ Ioi 0) :
      deriv (g s) x = x ^ (s - 1) := by
    have := HasDerivAt.cpow_const (c := s) (hasDerivAt_id (x : ℂ)) (Or.inl hx)
    simp_rw [mul_one, id_eq] at this
    rw [deriv_div_const, deriv.comp_ofReal (e := fun x ↦ x ^ s)]
    · rw [this.deriv, mul_div_right_comm, div_self hs, one_mul]
    · apply hasDerivAt_deriv_iff.mp
      simp only [this.deriv, this]
  calc
    _ =  ∫ (x : ℝ) in Ioi 0, ↑(ν x) * deriv (@g s) x := ?_
    _ = -∫ (x : ℝ) in Ioi 0, deriv (fun x ↦ ↑(ν x)) x * @g s x := ?_
    _ = -∫ (x : ℝ) in Ioi 0, deriv ν x * @g s x := ?_
    _ = -∫ (x : ℝ) in Ioi 0, deriv ν x * x ^ s / s := by simp only [mul_div, g]
    _ = _ := ?_
  · rw [setIntegral_congr_fun (by simp)]
    intro _ hx
    simp only [gderiv hs hx]
  · apply PartialIntegration_of_support_in_Icc (ν ·) (g s)
      (a := 1 / 2) (b := 2) (by norm_num) (by norm_num)
    · simpa only [Function.support_subset_iff, ne_eq, ofReal_eq_zero]
    · exact (Differentiable.ofReal_comp_iff.mpr
        (diffν.differentiable (by norm_num))).differentiableOn
    · refine DifferentiableOn.div_const ?_ s
      intro a ha
      refine DifferentiableAt.comp_ofReal (e := fun x ↦ x ^ s) ?_ |>.differentiableWithinAt
      apply differentiableAt_fun_id.cpow (differentiableAt_const s) <| by exact Or.inl ha
    · simp only [deriv.ofReal_comp']
      exact continuous_ofReal.comp (diffν.continuous_deriv (by norm_num)) |>.continuousOn
    · apply ContinuousOn.congr (f := fun (x : ℝ) ↦ (x : ℂ) ^ (s - 1)) ?_
        fun x hx ↦ gderiv hs hx
      exact Continuous.continuousOn (by continuity) |>.cpow continuousOn_const (by simp)
  · congr; funext; congr
    apply (hasDerivAt_deriv_iff.mpr ?_).ofReal_comp.deriv
    exact diffν.contDiffAt.differentiableAt (by norm_num)
  · simp only [neg_mul, neg_inj]
    conv => lhs; rhs; intro; rw [← mul_one_div, mul_comm]
    rw [integral_const_mul]

lemma MellinOfPsi {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    ∃ C > 0, ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2),
    ‖𝓜 (fun x ↦ (ν x : ℂ)) s‖ ≤ C * ‖s‖⁻¹ := by
  let f := fun (x : ℝ) ↦ ‖deriv ν x‖
  have cont : ContinuousOn f (Icc (1 / 2) 2) :=
    (Continuous.comp (by continuity) <| diffν.continuous_deriv (by norm_num)).continuousOn
  obtain ⟨a, _, max⟩ := isCompact_Icc.exists_isMaxOn (f := f) (by norm_num) cont
  let σ₂ : ℝ := 2
  let C : ℝ := f a * 2 ^ σ₂ * (3 / 2)
  have mainBnd : ∀ (σ₁ : ℝ), 0 < σ₁ → ∀ (s : ℂ), σ₁ ≤ s.re → s.re ≤ 2 →
      ‖𝓜 (fun x ↦ (ν x : ℂ)) s‖ ≤ C * ‖s‖⁻¹ := by
    intro σ₁ σ₁pos s hs₁ hs₂
    have s_ne_zero: s ≠ 0 := fun h ↦ by linarith [zero_re ▸ h ▸ hs₁]
    simp only [mellin, f, MellinOfPsi_aux diffν suppν s_ne_zero, norm_mul, smul_eq_mul, mul_comm]
    gcongr
    · simp
    calc
      _ ≤ ∫ (x : ℝ) in Ioi 0, ‖(deriv ν x * (x : ℂ) ^ s)‖ := ?_
      _ = ∫ (x : ℝ) in Icc (1 / 2) 2, ‖(deriv ν x * (x : ℂ) ^ s)‖ := ?_
      _ ≤ ‖∫ (x : ℝ) in Icc (1 / 2) 2, ‖(deriv ν x * (x : ℂ) ^ s)‖‖ :=
          le_abs_self _
      _ ≤ _ := ?_
    · simp_rw [norm_integral_le_integral_norm]
    · apply SetIntegral.integral_eq_integral_inter_of_support_subset_Icc
      · simp only [Function.support_abs, Function.support_mul, Function.support_ofReal]
        apply subset_trans (by apply inter_subset_left) <| Function.support_deriv_subset_Icc suppν
      · exact (Icc_subset_Ioi_iff (by norm_num)).mpr (by norm_num)
    · have := intervalIntegral.norm_integral_le_of_norm_le_const' (C := f a * 2 ^ σ₂)
        (f := fun x ↦ f x * ‖(x : ℂ) ^ s‖) (a := (1 / 2 : ℝ)) ( b := 2) (by norm_num) ?_
      · simp only [Real.norm_eq_abs, norm_real, norm_mul] at this ⊢
        rwa [(by norm_num: |(2 : ℝ) - 1 / 2| = 3 / 2),
            intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc] at this
      · intro x hx;
        have f_bound := isMaxOn_iff.mp max x hx
        have pow_bound : ‖(x : ℂ) ^ s‖ ≤ 2 ^ σ₂ := by
          rw [norm_cpow_eq_rpow_re_of_pos (by linarith [mem_Icc.mp hx])]
          have xpos : 0 ≤ x := by linarith [(mem_Icc.mp hx).1]
          have h := rpow_le_rpow xpos (mem_Icc.mp hx).2 (by linarith : 0 ≤ s.re)
          exact le_trans h <| rpow_le_rpow_of_exponent_le (by norm_num) hs₂
        convert! (preTransparency := .instances) mul_le_mul f_bound pow_bound (norm_nonneg _) ?_ using 1 <;> simp [f]
  have Cnonneg : 0 ≤ C := by
    have hh := mainBnd 1 (by norm_num) ((3 : ℂ) / 2) (by norm_num) (by norm_num)
    have hhh : 0 ≤ ‖𝓜 (fun x ↦ (ν x : ℂ)) ((3 : ℂ) / 2)‖ := by positivity
    have hhhh : 0 < ‖(3 : ℂ) / 2‖⁻¹ := by norm_num
    have := hhh.trans hh
    exact (mul_nonneg_iff_of_pos_right hhhh).mp this
  by_cases CeqZero : C = 0
  · refine ⟨1, by linarith, ?_⟩
    intro ε εpos s hs₁ hs₂
    have := mainBnd ε εpos s hs₁ hs₂
    rw [CeqZero, zero_mul] at this
    have : 0 ≤ 1 * ‖s‖⁻¹ := by positivity
    linarith
  · exact ⟨C, lt_of_le_of_ne Cnonneg fun a ↦ CeqZero (id (Eq.symm a)), mainBnd⟩



lemma DeltaSpikeSupport_aux {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    (fun x ↦ if x < 0 then 0 else DeltaSpike ν ε x).support ⊆ Icc (2 ^ (-ε)) (2 ^ ε) := by
  unfold DeltaSpike
  simp only [one_div, Function.support_subset_iff, ne_eq, ite_eq_left_iff, not_lt, div_eq_zero_iff,
    not_forall, exists_prop, mem_Icc, and_imp]
  intro x hx h; push Not at h
  have := suppν <| Function.mem_support.mpr h.1
  simp only [one_div, mem_Icc] at this
  have hl := (le_rpow_inv_iff_of_pos (by norm_num) hx εpos).mp this.1
  rw [inv_rpow (by norm_num) ε, ← rpow_neg (by norm_num)] at hl
  refine ⟨hl, (rpow_inv_le_iff_of_pos ?_ (by norm_num) εpos).mp this.2⟩
  linarith [(by apply rpow_nonneg (by norm_num) : 0 ≤ (2 : ℝ) ^ (-ε))]

lemma DeltaSpikeSupport' {ν : ℝ → ℝ} {ε x : ℝ} (εpos : 0 < ε) (xnonneg : 0 ≤ x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    DeltaSpike ν ε x ≠ 0 → x ∈ Icc (2 ^ (-ε)) (2 ^ ε) := by
  intro h
  have : (fun x ↦ if x < 0 then 0 else DeltaSpike ν ε x) x = DeltaSpike ν ε x := by
    simp [xnonneg]
  rw [← this] at h
  exact (Function.support_subset_iff.mp <| DeltaSpikeSupport_aux εpos suppν) _ h

lemma DeltaSpikeSupport {ν : ℝ → ℝ} {ε x : ℝ} (εpos : 0 < ε) (xnonneg : 0 ≤ x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    x ∉ Icc (2 ^ (-ε)) (2 ^ ε) → DeltaSpike ν ε x = 0 := by
  contrapose!; exact DeltaSpikeSupport' εpos xnonneg suppν

@[fun_prop]
lemma DeltaSpikeContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ DeltaSpike ν ε x) := by
  apply diffν.continuous.comp (g := ν) _ |>.div_const
  exact continuous_id.rpow_const fun _ ↦ Or.inr <| div_nonneg (by norm_num) εpos.le

lemma DeltaSpikeOfRealContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ (DeltaSpike ν ε x : ℂ)) :=
  continuous_ofReal.comp <| DeltaSpikeContinuous εpos diffν


theorem MellinOfDeltaSpike (ν : ℝ → ℝ) {ε : ℝ} (εpos : ε > 0) (s : ℂ) :
    𝓜 (fun x ↦ (DeltaSpike ν ε x : ℂ)) s = 𝓜 (fun x ↦ (ν x : ℂ)) (ε * s) := by
  unfold DeltaSpike
  push_cast
  rw [mellin_div_const, mellin_comp_rpow (fun x ↦ (ν x : ℂ)), abs_of_nonneg (by positivity)]
  simp only [one_div, inv_inv, ofReal_inv, div_inv_eq_mul, real_smul]
  rw [mul_div_cancel_left₀ _ (ne_zero_of_re_pos εpos)]
  ring_nf


lemma MellinOfDeltaSpikeAt1_asymp {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2)
    (mass_one : ∫ x in Set.Ioi 0, ν x / x = 1) :
    (fun (ε : ℝ) ↦ (𝓜 (fun x ↦ (ν x : ℂ)) ε) - 1) =O[𝓝[>]0] id := by
  have diff : DifferentiableWithinAt ℝ
      (fun (ε : ℝ) ↦ 𝓜 (fun x ↦ (ν x : ℂ)) ε - 1) (Ioi 0) 0 := by
    apply DifferentiableAt.differentiableWithinAt
    simp only [(differentiableAt_const _).fun_sub_iff_left]
    refine DifferentiableAt.comp_ofReal ?_
    refine mellin_differentiableAt_of_isBigO_rpow (a := 1) (b := -1) ?_ ?_ (by simp) ?_ (by simp)
    · apply (Continuous.continuousOn ?_).locallyIntegrableOn (by simp)
      have := diffν.continuous; continuity
    · apply Asymptotics.IsBigO.trans_le (g' := fun _ ↦ (0 : ℝ)) ?_ (by simp)
      apply BigO_zero_atTop_of_support_in_Icc (a := 1 / 2) (b := 2)
      rwa [Erdos970.Function.support_ofReal (f := ν)]
    · apply Asymptotics.IsBigO.trans_le (g' := fun _ ↦ (0 : ℝ)) ?_ (by simp)
      apply BigO_zero_atZero_of_support_in_Icc (a := 1 / 2) (b := 2) (ha := (by norm_num))
      rwa [Erdos970.Function.support_ofReal (f := ν)]
  have := ofReal_zero ▸ diff.isBigO_sub
  simp only [sub_sub_sub_cancel_right, sub_zero] at this
  convert! (preTransparency := .instances) this using 1
  simp only [mellin, zero_sub, cpow_neg_one, smul_eq_mul]
  funext ε
  congr 1
  symm
  calc (∫ (t : ℝ) in Ioi 0, (↑t)⁻¹ * ↑(ν t) : ℂ)
      = ∫ (t : ℝ) in Ioi 0, ((ν t / t : ℝ) : ℂ) :=
        integral_congr_ae (Filter.Eventually.of_forall fun t => by push_cast; ring)
    _ = ((∫ t in Ioi 0, ν t / t : ℝ) : ℂ) := integral_ofReal
    _ = 1 := by rw [mass_one, ofReal_one]

lemma MellinOf1 (s : ℂ) (h : s.re > 0) :
    𝓜 ((fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0)) s = 1 / s := by
  convert (preTransparency := .instances) (hasMellin_one_Ioc h).right
  congr



lemma Smooth1Properties_estimate {ε : ℝ} (εpos : 0 < ε) :
    (1 - 2 ^ (-ε)) / ε < Real.log 2 := by
  apply (div_lt_iff₀' εpos).mpr
  have : 1 - 1 / (2 : ℝ) ^ ε = ((2 : ℝ) ^ ε - 1) / (2 : ℝ) ^ ε := by
    rw [sub_div, div_self (by positivity)]
  rw [← Real.log_rpow (by norm_num), rpow_neg (by norm_num), inv_eq_one_div (2 ^ ε), this]
  set c := (2 : ℝ) ^ ε
  have hc : 1 < c := by
    rw [← rpow_zero (2 : ℝ)]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) εpos
  apply (div_lt_iff₀' (by positivity)).mpr <| lt_sub_iff_add_lt'.mp ?_
  let f := (fun x ↦ x * Real.log x - x)
  rw [(by simp [f] : -1 = f 1), (by simp [f] : c * Real.log c - c = f c)]
  have mono: StrictMonoOn f <| Ici 1 := by
    refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ ?_
    · apply continuousOn_id.mul (continuousOn_id.log ?_) |>.sub continuousOn_id
      intro x hx; simp only [mem_Ici] at hx; simp only [id_eq, ne_eq]; linarith
    · intro x hx; simp only [nonempty_Iio, interior_Ici', mem_Ioi] at hx
      dsimp only [f]
      rw [deriv_fun_sub, deriv_fun_mul, Real.deriv_log, deriv_id'', one_mul, mul_inv_cancel₀]
      · simp [log_pos hx]
      · linarith
      · simp only [differentiableAt_fun_id]
      · simp only [differentiableAt_log_iff, ne_eq]; linarith
      · exact differentiableAt_fun_id.mul <| differentiableAt_fun_id.log (by linarith)
      · simp only [differentiableAt_fun_id]
  exact mono (by rw [mem_Ici]) (mem_Ici.mpr <| le_of_lt hc) hc



lemma Smooth1Properties_above_aux {x ε : ℝ} (hx : 1 + (2 * Real.log 2) * ε ≤ x)
    (hε : ε ∈ Ioo 0 1) :
    2 ^ ε < x := by
  calc
    x ≥ 1 + (2 * Real.log 2) * ε := hx
    _ > 2 ^ ε := ?_
  refine lt_add_of_sub_left_lt <| (div_lt_iff₀ hε.1).mp ?_
  calc
    2 * Real.log 2 > 2 * (1 - 2 ^ (-ε)) / ε := ?_
    _ > 2 ^ ε * (1 - 2 ^ (-ε)) / ε := ?_
    _ = (2 ^ ε - 1) / ε := ?_
  · field_simp
    exact Smooth1Properties_estimate hε.1
  · have : (2 : ℝ) ^ ε < 2 := by
      have h := rpow_lt_rpow_of_exponent_lt (x := 2) (by norm_num) hε.2
      rwa [Real.rpow_one] at h
    have pos: 0 < (1 - 2 ^ (-ε)) / ε := by
      refine div_pos ?_ hε.1
      rw [sub_pos]
      have h := rpow_lt_rpow_of_exponent_lt (x := 2) (by norm_num) (neg_lt_zero.mpr hε.1)
      rwa [Real.rpow_zero] at h
    have := (mul_lt_mul_iff_left₀ pos).mpr this
    ring_nf at this ⊢
    exact this
  · have : (2 : ℝ) ^ ε * (2 : ℝ) ^ (-ε) = (2 : ℝ) ^ (ε - ε) := by
      rw [← rpow_add (by norm_num), add_neg_cancel, sub_self]
    conv => lhs; lhs; ring_nf; rhs; simp [this]

lemma Smooth1Properties_above_aux2 {x y ε : ℝ} (hε : ε ∈ Ioo 0 1) (hy : y ∈ Ioc 0 1)
  (hx2 : 2 ^ ε < x) :
    2 < (x / y) ^ (1 / ε) := by
  obtain ⟨εpos, ε1⟩ := hε
  obtain ⟨ypos, y1⟩ := hy
  calc
    _ > (2 ^ ε / y) ^ (1 / ε) := ?_
    _ = 2 / y ^ (1 / ε) := ?_
    _ ≥ 2 / y := ?_
    _ ≥ 2 := ?_
  · rw [gt_iff_lt, div_rpow, div_rpow, lt_div_iff₀, mul_comm_div, div_self, mul_one]
    <;> try positivity
    · exact rpow_lt_rpow (by positivity) hx2 (by positivity)
    · exact LT.lt.le <| lt_trans (by positivity) hx2
  · rw [div_rpow, ← rpow_mul, mul_div_cancel₀ 1 <| ne_of_gt εpos, rpow_one] <;> positivity
  · have : y ^ (1 / ε) ≤ y := by
      nth_rewrite 2 [← rpow_one y]
      exact rpow_le_rpow_of_exponent_ge ypos y1 (by linarith [one_lt_one_div εpos ε1])
    have pos : 0 < y ^ (1 / ε) := rpow_pos_of_pos ypos _
    rw [ge_iff_le, div_le_iff₀, div_mul_eq_mul_div, le_div_iff₀', mul_comm] <;> try linarith
  · rw [ge_iff_le, le_div_iff₀ <| ypos]; exact (mul_le_iff_le_one_right zero_lt_two).mpr y1

lemma Smooth1Properties_above {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    ∃ (c : ℝ), 0 < c ∧ c = 2 * Real.log 2 ∧
      ∀ (ε x) (_ : ε ∈ Ioo 0 1), 1 + c * ε ≤ x → Smooth1 ν ε x = 0 := by
  set c := 2 * Real.log 2; use c
  constructor
  · simp only [c, zero_lt_two, mul_pos_iff_of_pos_left]; exact log_pos (by norm_num)
  constructor
  · rfl
  intro ε x hε hx
  have hx2 := Smooth1Properties_above_aux hx hε
  unfold Smooth1 MellinConvolution
  simp only [ite_mul, one_mul, zero_mul, RCLike.ofReal_real_eq_id, id_eq]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  have ypos := mem_Ioi.mp hy
  by_cases y1 : y ≤ 1
  swap
  · simp [ypos, y1]
  simp only [mem_Ioi.mp hy, y1, and_self, ↓reduceIte, div_eq_zero_iff]; left
  apply DeltaSpikeSupport hε.1 ?_ suppν
  on_goal 1 =>
    simp only [mem_Icc, not_and, not_le]
  on_goal 2 =>
    suffices h : 2 ^ ε < x / y by
      linarith [(by apply rpow_pos_of_pos (by norm_num) : 0 < (2 : ℝ) ^ ε)]
  all_goals
  try intro
  have : x / y = ((x / y) ^ (1 / ε)) ^ ε := by
    rw [← rpow_mul]
    simp only [one_div, inv_mul_cancel₀ (ne_of_gt hε.1), rpow_one]
    apply div_nonneg_iff.mpr; left;
    exact ⟨(le_trans (rpow_pos_of_pos (by norm_num) ε).le) hx2.le, ypos.le⟩
  rw [this]
  refine rpow_lt_rpow (by norm_num) ?_ hε.1
  exact Smooth1Properties_above_aux2 hε ⟨ypos, y1⟩ hx2

lemma DeltaSpikeNonNeg_of_NonNeg {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x)
     {x ε : ℝ} (xpos : 0 < x) (εpos : 0 < ε) :
    0 ≤ DeltaSpike ν ε x := by
  dsimp [DeltaSpike]
  have : 0 < x ^ (1 / ε) := by positivity
  have : 0 ≤ ν (x ^ (1 / ε)) := νnonneg _ this
  positivity

lemma MellinConvNonNeg_of_NonNeg {f g : ℝ → ℝ} (f_nonneg : ∀ x > 0, 0 ≤ f x)
    (g_nonneg : ∀ x > 0, 0 ≤ g x) {x : ℝ} (xpos : 0 < x) :
    0 ≤ MellinConvolution f g x := by
  dsimp [MellinConvolution]
  apply MeasureTheory.setIntegral_nonneg
  · exact measurableSet_Ioi
  · intro y ypos; simp only [mem_Ioi] at ypos
    have : 0 ≤ f y := f_nonneg _ ypos
    have : 0 < x / y := by positivity
    have : 0 ≤ g (x / y) := g_nonneg _ this
    positivity

lemma Smooth1Nonneg {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x) {ε x : ℝ}
    (xpos : 0 < x) (εpos : 0 < ε) : 0 ≤ Smooth1 ν ε x := by
  dsimp [Smooth1]
  apply MellinConvNonNeg_of_NonNeg ?_ ?_ xpos
  · intro y hy; by_cases h : y ≤ 1 <;> simp [h, hy]
  · intro y ypos; exact DeltaSpikeNonNeg_of_NonNeg νnonneg ypos εpos

lemma Smooth1LeOne_aux {x ε : ℝ} {ν : ℝ → ℝ} (xpos : 0 < x) (εpos : 0 < ε)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∫ (y : ℝ) in Ioi 0, ν ((x / y) ^ (1 / ε)) / ε / y = 1 := by
    calc
      _ = ∫ (y : ℝ) in Ioi 0, (ν (y ^ (1 / ε)) / ε) / y := ?_
      _ = ∫ (y : ℝ) in Ioi 0, ν y / y := ?_
      _ = 1 := mass_one
    · have := integral_comp_div_I0i_haar (fun y ↦ ν ((x / y) ^ (1 / ε)) / ε) xpos
      convert! (preTransparency := .instances) this.symm using 1
      congr; funext y; congr; field_simp [mul_comm]
    · have := integral_comp_rpow_I0i_haar_real (fun y ↦ ν y) (one_div_ne_zero εpos.ne')
      rw [← this, abs_of_pos <| one_div_pos.mpr εpos]
      field_simp

lemma Smooth1LeOne {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (εpos : 0 < ε) {x : ℝ} (xpos : 0 < x) :
    Smooth1 ν ε x ≤ 1 := by
  unfold Smooth1 MellinConvolution DeltaSpike
  have := Smooth1LeOne_aux xpos εpos mass_one
  calc
    _ = ∫ (y : ℝ) in Ioi 0,
        (fun y ↦ if y ∈ Ioc 0 1 then 1 else 0) y * (ν ((x / y) ^ (1 / ε)) / ε / y) := ?_
    _ ≤ ∫ (y : ℝ) in Ioi 0, (ν ((x / y) ^ (1 / ε)) / ε) / y := ?_
    _ = 1 := this
  · rw [setIntegral_congr_fun (by simp)]
    simp only [ite_mul, one_mul, zero_mul, RCLike.ofReal_real_eq_id, id_eq, mem_Ioc]
    intro y hy; aesop
  · refine setIntegral_mono_on ?_ (integrable_of_integral_eq_one this) (by simp) ?_
    · refine integrable_of_integral_eq_one this |>.bdd_mul ?_
        (ae_of_all _ <| by aesop)
      have : (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) =
          indicator (Ioc 0 1) (1 : ℝ → ℝ) := by
        aesop
      simp only [mem_Ioc, this, measurableSet_Ioc, aestronglyMeasurable_indicator_iff]
      exact aestronglyMeasurable_one
    · simp only [ite_mul, one_mul, zero_mul]
      intro y hy
      by_cases h : y ≤ 1
      · aesop
      field_simp
      simp only [mem_Ioc, h, and_false, ↓reduceIte, one_div, mul_zero]
      simp only [mem_Ioi] at hy
      apply div_nonneg
      · apply νnonneg; exact rpow_pos_of_pos (div_pos xpos <| mem_Ioi.mp hy) _
      · positivity

lemma MellinOfSmooth1a {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {s : ℂ} (hs : 0 < s.re) :
    𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s =
      s⁻¹ * 𝓜 (fun x ↦ (ν x : ℂ)) (ε * s) := by
  let f' : ℝ → ℂ := fun x ↦ DeltaSpike ν ε x
  let f : ℝ → ℂ := fun x ↦ DeltaSpike ν ε x / x
  let g : ℝ → ℂ := fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0
  let F : ℝ × ℝ → ℂ := Function.uncurry fun x y ↦ f y * g (x / y) * (x : ℂ) ^ (s - 1)
  let S := {⟨x, y⟩ : ℝ × ℝ | 0 < x  ∧ x ≤ y ∧ 2 ^ (-ε) ≤ y ∧ y ≤ 2 ^ ε}
  let F' : ℝ × ℝ → ℂ := piecewise S (fun ⟨x, y⟩ ↦ f y * (x : ℂ) ^ (s - 1))
     (fun _ ↦ 0)
  let Tx := Ioc 0 ((2 : ℝ) ^ ε)
  let Ty := Icc ((2 : ℝ) ^ (-ε)) ((2 : ℝ) ^ ε)

  have Seq : S = (Tx ×ˢ Ty) ∩ {(x, y) : ℝ × ℝ | x ≤ y} := by
    ext ⟨x, y⟩; constructor
    · exact fun h ↦ ⟨⟨⟨h.1, le_trans h.2.1 h.2.2.2⟩, ⟨h.2.2.1, h.2.2.2⟩⟩, h.2.1⟩
    · exact fun h ↦  ⟨h.1.1.1, ⟨h.2, h.1.2.1, h.1.2.2⟩⟩
  have SsubI : S ⊆ Ioi 0 ×ˢ Ioi 0 :=
    fun z hz ↦ ⟨hz.1, lt_of_lt_of_le (by apply rpow_pos_of_pos; norm_num) hz.2.2.1⟩
  have SsubT: S ⊆ Tx ×ˢ Ty := by simp_rw [Seq, inter_subset_left]
  have Smeas : MeasurableSet S := by
    rw [Seq]; apply MeasurableSet.inter ?_ <| measurableSet_le measurable_fst measurable_snd
    simp [measurableSet_prod, Tx, Ty]

  have int_F: IntegrableOn F (Ioi 0 ×ˢ Ioi 0) := by
    apply IntegrableOn.congr_fun (f := F') ?_ ?_ (by simp [measurableSet_prod]); swap
    · simp only [F, F', f, g, mul_ite, mul_one, mul_zero]
      intro ⟨x, y⟩ hz
      by_cases hS : ⟨x, y⟩ ∈ S <;> simp only [hS, piecewise]
      <;> simp only [mem_prod, mem_Ioi, mem_ofPred_eq, not_and, not_le, S] at hz hS
      · simp [div_pos hz.1 hz.2, (div_le_one hz.2).mpr hS.2.1]
      · by_cases hxy : x / y ≤ 1
        swap
        · simp [hxy]
        have hy : y ∉ Icc (2 ^ (-ε)) (2 ^ ε) := by
          simp only [mem_Icc, not_and, not_le]; exact hS hz.1 <| (div_le_one hz.2).mp hxy
        simp [DeltaSpikeSupport εpos hz.2.le suppν hy]
    · apply Integrable.piecewise Smeas ?_ integrableOn_zero
      simp only [IntegrableOn, Measure.restrict_restrict_of_subset SsubI]
      apply MeasureTheory.Integrable.mono_measure ?_
      · apply MeasureTheory.Measure.restrict_mono' SsubT.eventuallyLE le_rfl
      change Integrable (fun x : ℝ × ℝ => f x.2 * (x.1 : ℂ) ^ (s - 1))
        (volume.restrict (Tx ×ˢ Ty))
      have : volume.restrict (Tx ×ˢ Ty) = (volume.restrict Tx).prod (volume.restrict Ty) := by
        rw [Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod]
      conv => rw [this]; lhs; intro; rw [mul_comm]
      apply MeasureTheory.Integrable.mul_prod (f := fun x ↦ (x : ℂ) ^ (s - 1))
        (μ := Measure.restrict volume Tx)
      · simp only [Tx]
        rw [← IntegrableOn, integrableOn_Ioc_iff_integrableOn_Ioo,
          intervalIntegral.integrableOn_Ioo_cpow_iff]
        · simp [hs]
        · apply rpow_pos_of_pos (by norm_num)
      · apply (ContinuousOn.div ?_ ?_ ?_).integrableOn_compact isCompact_Icc
        · exact (DeltaSpikeOfRealContinuous εpos diffν).continuousOn
        · exact continuous_ofReal.continuousOn
        · intro x hx; simp only [mem_Icc] at hx; simp only [ofReal_ne_zero]
          linarith [(by apply rpow_pos_of_pos (by norm_num) : (0 : ℝ) < 2 ^ (-ε))]

  have : 𝓜 (MellinConvolution g f') s = 𝓜 g s * 𝓜 f' s := by
    rw [mul_comm, ← MellinConvolutionTransform f' g s
      (by convert (preTransparency := .instances) int_F using 1; simp only [f', F, f]; field_simp)]
    dsimp [mellin]; rw [setIntegral_congr_fun (by simp)]
    intro x hx; simp_rw [MellinConvolutionSymmetric _ _ <| mem_Ioi.mp hx]

  convert! (preTransparency := .instances) this using 1
  · congr; funext x; convert! (preTransparency := .instances) integral_ofReal.symm
    simp only [MellinConvolution, RCLike.ofReal_div, ite_mul, one_mul, zero_mul, @apply_ite ℝ ℂ,
      algebraMap.coe_zero, g]; rfl
  · rw [MellinOf1 s hs, MellinOfDeltaSpike ν εpos s]
    simp

lemma MellinOfSmooth1b {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    ∃ (C : ℝ) (_ : 0 < C), ∀ (σ₁ : ℝ) (_ : 0 < σ₁)
    (s) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
    ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ C * (ε * ‖s‖ ^ 2)⁻¹ := by
  obtain ⟨C, Cpos, hC⟩ := MellinOfPsi diffν suppν
  refine ⟨C, Cpos, ?_⟩
  intro σ₁ σ₁pos s hs1 hs2 ε εpos ε_lt_one
  rw [MellinOfSmooth1a diffν suppν εpos <| lt_of_le_of_lt' hs1 σ₁pos]
  have hh1 : ε * σ₁ ≤ (ε * s).re := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    nlinarith
  have hh2 : (ε * s).re ≤ 2 := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    nlinarith
  calc
    ‖s⁻¹ * 𝓜 (fun x ↦ (ν x : ℂ)) (ε * s)‖ =
        ‖s⁻¹‖ * ‖𝓜 (fun x ↦ (ν x : ℂ)) (ε * s)‖ := by simp
    _                        ≤ ‖s⁻¹‖ * (C * (ε * ‖s‖)⁻¹) := by
      gcongr
      convert! (preTransparency := .instances) hC (ε * σ₁) (by positivity) (ε * s) hh1 hh2
      simp [abs_eq_self.mpr εpos.le]
    _                        = C * (ε * ‖s‖ ^ 2)⁻¹ := by
      simp only [norm_inv, mul_inv_rev]
      ring

lemma MellinOfSmooth1c {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    (fun ε ↦ 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 - 1) =O[𝓝[>]0] id := by
  have h := MellinOfDeltaSpikeAt1_asymp diffν suppν mass_one
  rw [Asymptotics.isBigO_iff] at h ⊢
  obtain ⟨c, hc⟩ := h
  use c
  filter_upwards [hc, Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < 1)] with ε hε hε'
  rw [MellinOfSmooth1a diffν suppν hε'.1 (s := 1) (by norm_num)]
  simp only [inv_one, mul_one, one_mul, id_eq, Real.norm_eq_abs]
  exact hε

lemma Smooth1ContinuousAt {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : SmoothingF.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {y : ℝ} (ypos : 0 < y) :
    ContinuousAt (fun x ↦ Smooth1 SmoothingF ε x) y := by
  apply ContinuousAt.congr
    (f := (fun x ↦ MellinConvolution (DeltaSpike SmoothingF ε)
      (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) x)) _
  · filter_upwards [lt_mem_nhds ypos] with x hx
    apply MellinConvolutionSymmetric _ _ hx
  apply continuousAt_of_dominated (bound := (fun x ↦ 2 ^ ε * DeltaSpike SmoothingF ε x))
  · filter_upwards [lt_mem_nhds ypos] with x hx
    apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · apply Measurable.mul
      · exact Continuous.measurable <| DeltaSpikeContinuous εpos diffSmoothingF
      · apply Measurable.ite _ (by fun_prop) (by fun_prop)
        apply MeasurableSet.congr (s := Ici x) (by measurability)
        ext a
        constructor
        · intro ha
          have apos : 0 < a := lt_of_lt_of_le hx ha
          constructor
          · exact div_pos hx apos
          · exact (div_le_one apos).mpr ha
        · intro ha
          have : 0 < a := (div_pos_iff_of_pos_left hx).mp ha.1
          exact (div_le_one this).mp ha.2
    · fun_prop
  · filter_upwards [lt_mem_nhds ypos] with x hx
    filter_upwards [ae_restrict_mem (by measurability)] with t ht
    simp only [mul_ite, mul_one, mul_zero, RCLike.ofReal_real_eq_id, id_eq, norm_div, norm_eq_abs]
    by_cases! h : DeltaSpike SmoothingF ε t = 0
    · simp [h]
    have := DeltaSpikeSupport' εpos ht.le suppSmoothingF h
    have dsnonneg : 0 ≤ DeltaSpike SmoothingF ε t := by
      apply DeltaSpikeNonNeg_of_NonNeg <;> assumption
    calc
      _ ≤ |DeltaSpike SmoothingF ε t| / |t| := by
        gcongr
        · split_ifs with h
          · apply le_refl
          · exact dsnonneg
      _ ≤ _ := by
        rw [_root_.abs_of_nonneg dsnonneg, mul_comm, div_eq_mul_one_div, _root_.abs_of_pos ht]
        gcongr
        apply (one_div_le ht (by bound)).mpr
        · convert (preTransparency := .instances) this.1 using 1
          rw [div_eq_iff (by positivity), ← rpow_add (by norm_num), neg_add_cancel, rpow_zero]
  · apply Integrable.const_mul
    apply (integrable_indicator_iff (by measurability)).mp
    apply (integrableOn_iff_integrable_of_support_subset (s := Icc (2 ^ (-ε)) (2 ^ ε)) _).mp
    · apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply ContinuousOn.congr  (f := DeltaSpike SmoothingF ε)
      · apply Continuous.continuousOn
        apply DeltaSpikeContinuous<;> assumption
      · intro x hx
        have : x ∈ Ioi 0 := by
          apply mem_Ioi.mpr
          apply lt_of_lt_of_le (by bound) hx.1
        rw [indicator, if_pos this]
    · unfold indicator
      simp_rw [mem_Ioi]
      apply Function.support_subset_iff.mpr
      simp only [ne_eq, ite_eq_right_iff, Classical.not_imp, mem_Icc, and_imp]
      intro x hx
      apply DeltaSpikeSupport' εpos hx.le suppSmoothingF
  · have : ∀ᵐ (a : ℝ) ∂volume.restrict (Ioi 0), a ≠ y := by
      apply ae_iff.mpr
      simp
    filter_upwards [ae_restrict_mem (by measurability), this] with x hx hx2
    simp only [mem_Ioi] at hx
    apply ContinuousAt.div_const
    apply ContinuousAt.mul (by fun_prop)
    have : (fun x_1 ↦ if 0 < x_1 / x ∧ x_1 / x ≤ 1 then 1 else 0) =
        (Ioc 0 x).indicator (fun _ ↦ (1 : ℝ)) := by
      ext t
      unfold indicator
      simp [div_pos_iff_of_pos_right, div_le_one₀, hx]
    rw [this]
    apply ContinuousOn.continuousAt_indicator (by fun_prop)
    simp [frontier_Ioc hx, ypos.ne', hx2.symm]


lemma Smooth1MellinDifferentiable {Ψ : ℝ → ℝ} {ε : ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
    (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2) (hε : ε ∈ Ioo 0 1)
    (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x) (mass_one : ∫ x in Ioi 0, Ψ x / x = 1)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (𝓜 (fun x ↦ (Smooth1 Ψ ε x : ℂ))) s := by
  apply mellin_differentiableAt_of_isBigO_rpow_exp zero_lt_one _ _ _ hs
  · apply ContinuousOn.locallyIntegrableOn _ (by measurability)
    apply continuousOn_of_forall_continuousAt
    exact fun x hx ↦ Smooth1ContinuousAt diffΨ Ψnonneg suppΨ hε.1 hx |>.ofReal
  · rw [Asymptotics.isBigO_iff]
    use 1
    obtain ⟨c, cpos, ceq, hc⟩ := Smooth1Properties_above suppΨ
    filter_upwards [eventually_ge_atTop (1 + c * ε)] with x hx
    rw [hc _ _ hε hx]
    simp only [ofReal_zero, norm_zero, neg_mul, one_mul, norm_eq_abs, abs_exp]
    bound
  · rw [Asymptotics.isBigO_iff]
    use 1
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    simp only [norm_real, norm_eq_abs, neg_zero, rpow_zero, one_mem, CStarRing.norm_of_mem_unitary,
      mul_one]
    rw [_root_.abs_of_nonneg <| Smooth1Nonneg Ψnonneg hx hε.1]
    exact Smooth1LeOne Ψnonneg mass_one hε.1 hx

end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.ZetaBounds
namespace Erdos970


open _root_.Complex _root_.Topology _root_.Filter _root_.Interval _root_.Set _root_.Asymptotics






local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta


theorem analyticAt_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
  AnalyticAt ℂ riemannZeta s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [eventually_ne_nhds s_ne_one] with z hz using differentiableAt_riemannZeta hz

theorem differentiableAt_deriv_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
    DifferentiableAt ℂ ζ' s := by
  exact (analyticAt_riemannZeta s_ne_one).deriv.differentiableAt
















local notation (name := riemannzeta0) "ζ₀" => riemannZeta0
























































lemma mul_le_mul₃ {α : Type*} {a b c d e f : α} [MulZeroClass α] [Preorder α] [PosMulMono α]
    [MulPosMono α] (h₁ : a ≤ b) (h₂ : c ≤ d) (h₃ : e ≤ f) (c0 : 0 ≤ c) (b0 : 0 ≤ b)
    (e0 : 0 ≤ e) : a * c * e ≤ b * d * f := by
  apply mul_le_mul (mul_le_mul h₁ h₂ c0 b0) h₃ e0 <| mul_nonneg b0 <| le_trans c0 h₂


lemma logt_gt_one {t : ℝ} (t_ge : 3 ≤ t) : 1 < Real.log t :=
  (Real.lt_log_iff_exp_lt (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])

































































lemma ZetaCont : ContinuousOn ζ (univ \ {1}) := by
  apply continuousOn_of_forall_continuousAt (fun x hx ↦ ?_)
  apply DifferentiableAt.continuousAt (𝕜 := ℂ)
  convert (preTransparency := .instances) differentiableAt_riemannZeta ?_
  simp only [Set.mem_sdiff, mem_univ, mem_singleton_iff, true_and] at hx
  exact hx

lemma ZetaNoZerosInBox (T : ℝ) :
    ∃ (σ : ℝ) (_ : σ < 1), ∀ (t : ℝ) (_ : |t| ≤ T)
    (σ' : ℝ) (_ : σ' ≥ σ), ζ (σ' + t * Complex.I) ≠ 0 := by
  by_contra! h
  have hn (n : ℕ) := h (1 - 1 / (n + 1)) (sub_lt_self _ (by positivity))

  have : ∃ (tn : ℕ → ℝ) (σn : ℕ → ℝ), (∀ n, σn n ≤ 1) ∧
    (∀ n, (1 : ℝ) - 1 / (n + 1) ≤ σn n) ∧ (∀ n, |tn n| ≤ T) ∧
    (∀ n, ζ (σn n + tn n * Complex.I) = 0) := by
    choose t ht σ' hσ' hζ using hn
    refine ⟨t, σ', ?_, hσ', ht, hζ⟩
    intro n
    by_contra! hσn
    have := riemannZeta_ne_zero_of_one_lt_re (s := σ' n + t n * Complex.I)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, ne_eq] at this
    exact this hσn (hζ n)

  choose t σ' hσ'_le hσ'_ge ht hζ using this

  have σTo1 : Filter.Tendsto σ' Filter.atTop (𝓝 1) := by
    use sub_zero (1: ℝ)▸tendsto_order.2 ⟨fun A B=>? _,fun A B=>?_⟩
    · apply (((tendsto_inv_atTop_nhds_zero_nat.comp
        (Filter.tendsto_add_atTop_nat (1))).congr (by norm_num)).const_sub 1).eventually_const_lt
          B|>.mono (hσ'_ge ·|>.trans_lt')
    · norm_num[(hσ'_le _).trans_lt, B.trans_le']

  have : ∃ (t₀ : ℝ) (subseq : ℕ → ℕ),
      Filter.Tendsto (t ∘ subseq) Filter.atTop (𝓝 t₀) ∧
      Filter.Tendsto subseq Filter.atTop Filter.atTop := by
    refine (isCompact_Icc.isSeqCompact fun and => abs_le.1 (ht and)).imp fun and ⟨x, A, B, _⟩ => ?_
    use A, by omega, B.tendsto_atTop

  obtain ⟨t₀, subseq, tTendsto, subseqTendsto⟩ := this

  have σTo1 : Filter.Tendsto (σ' ∘ subseq) Filter.atTop (𝓝 1) :=
    σTo1.comp subseqTendsto

  have (n : ℕ) : ζ (σ' (subseq n) + Complex.I * (t (subseq n))) = 0 := by
    convert (preTransparency := .instances) hζ (subseq n) using 3
    ring

  have ToOneT0 : Filter.Tendsto (fun n ↦ (σ' (subseq n) : ℂ) + Complex.I * (t (subseq n))) Filter.atTop
      (𝓝[≠]((1 : ℂ) + Complex.I * t₀)) := by
    simp_rw [tendsto_nhdsWithin_iff, Function.comp_def] at tTendsto ⊢
    constructor
    · exact (σTo1.ofReal.add (tTendsto.ofReal.const_mul _)).trans (by simp)
    · filter_upwards with n
      apply ne_of_apply_ne ζ
      rw [this]
      apply Ne.symm
      apply riemannZeta_ne_zero_of_one_le_re
      simp only [add_re, one_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, add_zero, le_refl]

  by_cases ht₀ : t₀ = 0
  · have ZetaBlowsUp : ∀ᶠ s in 𝓝[≠](1 : ℂ), ‖ζ s‖ ≥ 1 := by
      simp_all only [ge_iff_le, one_div, tsub_le_iff_right, Function.comp_def, ofReal_zero,
        mul_zero, add_zero, norm_eq_sqrt_real_inner, Complex.inner, mul_re, conj_re, conj_im,
        mul_neg, sub_neg_eq_add, Real.one_le_sqrt, eventually_nhdsWithin_iff, mem_compl_iff,
        mem_singleton_iff]
      contrapose! h
      simp_all only [ne_eq]
      delta abs at*
      exfalso
      simp_rw [Metric.nhds_basis_ball.frequently_iff]at*
      choose! I A B using h
      choose a s using exists_seq_strictAnti_tendsto (0: ℝ)
      apply ((isCompact_closedBall _ _).isSeqCompact
        fun and=>(A _ (s.2.1 and)).le.trans (s.2.2.bddAbove_range.some_mem ⟨and, rfl⟩)).elim
      simp only [Metric.mem_ball, dist_eq_norm_sub] at A
      refine fun and ⟨a, H, S, M⟩=> ?_
      refine absurd (tendsto_nhds_unique M (tendsto_sub_nhds_zero_iff.1
        (( squeeze_zero_norm fun and=>le_of_lt (A _ (s.2.1 _) ) )
          (s.2.2.comp S.tendsto_atTop)))) fun and=>?_
      norm_num[*,Function.comp_def] at M
      have:=@riemannZeta_residue_one
      use one_ne_zero (tendsto_nhds_unique (this.comp (tendsto_nhdsWithin_iff.2
        ⟨ M,.of_forall (by norm_num[*])⟩)) ( squeeze_zero_norm ?_
          ((M.sub_const 1).norm.trans (by rw [sub_self,norm_zero]))))
      use fun and =>.trans (norm_mul_le_of_le ↑(le_rfl) (Complex.norm_def _▸Real.sqrt_le_one.mpr
        (B ↑_ (s.2.1 ↑_)).right.le)) (by rw [mul_one])

    have ZetaNonZ : ∀ᶠ s in 𝓝[≠](1 : ℂ), ζ s ≠ 0 := by
      filter_upwards [ZetaBlowsUp]
      intro s hs hfalse
      rw [hfalse] at hs
      simp only [norm_zero, ge_iff_le] at hs
      linarith

    rw [ht₀] at ToOneT0
    simp only [ofReal_zero, mul_zero, add_zero] at ToOneT0
    rcases (ToOneT0.eventually ZetaNonZ).exists with ⟨n, hn⟩
    exact hn (this n)

  · have zetaIsZero : ζ (1 + Complex.I * t₀) = 0 := by
      have cont := @ZetaCont
      use isClosed_singleton.isSeqClosed
        this
        (.comp
          (cont.continuousAt.comp (eventually_ne_nhds (by field_simp; simp [ht₀])).mono
            fun and=>.intro ⟨⟩)
          (ToOneT0.trans (inf_le_left)))

    exact riemannZeta_ne_zero_of_one_le_re (s := 1 + Complex.I * t₀) (by simp) zetaIsZero

lemma LogDerivZetaHoloOn {S : Set ℂ} (s_ne_one : 1 ∉ S)
    (nonzero : ∀ s ∈ S, ζ s ≠ 0) :
    HolomorphicOn (fun s ↦ ζ' s / ζ s) S := by
  apply DifferentiableOn.div _ _ nonzero <;> intro s hs <;> apply DifferentiableAt.differentiableWithinAt
  · apply differentiableAt_deriv_riemannZeta
    exact ne_of_mem_of_not_mem hs s_ne_one
  · apply differentiableAt_riemannZeta
    exact ne_of_mem_of_not_mem hs s_ne_one

theorem LogDerivZetaHolcSmallT :
    ∃ (σ₂ : ℝ) (_ : σ₂ < 1), HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
      (( [[ σ₂, 2 ]] ×ℂ [[ -3, 3 ]]) \ {1}) := by
  obtain ⟨σ₂, hσ₂_lt_one, hζ_ne_zero⟩ := ZetaNoZerosInBox 3
  refine ⟨σ₂, hσ₂_lt_one, ?_⟩
  let U := ([[σ₂, 2]] ×ℂ [[-3, 3]]) \ {1}
  have s_in_U_im_le3 : ∀ s ∈ U, |s.im| ≤ 3 := by
    intro s hs
    rw [Set.mem_sdiff_singleton] at hs
    rcases hs with ⟨hbox, _hne⟩
    rcases hbox with ⟨hre, him⟩
    simp only [Set.mem_preimage] at him
    obtain ⟨him_lower, him_upper⟩ := him
    apply abs_le.2
    simp only [neg_le_self_iff, Nat.ofNat_nonneg, inf_of_le_left] at him_lower
    simp only [neg_le_self_iff, Nat.ofNat_nonneg, sup_of_le_right] at him_upper
    exact ⟨him_lower, him_upper⟩

  have s_in_U_re_ges2 : ∀ s ∈ U, σ₂ ≤ s.re := by
    intro s hs
    rw [Set.mem_sdiff_singleton] at hs
    rcases hs with ⟨hbox, _hne⟩
    rcases hbox with ⟨hre, _him⟩
    simp only [Set.mem_preimage] at hre
    obtain ⟨hre_lower, hre_upper⟩ := hre
    have : min σ₂ 2 = σ₂ := by
      apply min_eq_left
      linarith [hσ₂_lt_one]
    rwa [← this]

  apply LogDerivZetaHoloOn
  · exact Set.notMem_sdiff_of_mem rfl
  · intro s hs
    rw[← re_add_im s]
    apply hζ_ne_zero
    · apply s_in_U_im_le3 _ hs
    · apply s_in_U_re_ges2 _ hs



open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
                                                              



end Erdos970

end

section
-- module Solutions.OAIChowla.StrongPNT.Erdos970.PNT5_Strong
namespace Erdos970


open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

open _root_.ArithmeticFunction (vonMangoldt)


lemma MellinTransform_integral (f : ℝ → ℂ) (s : ℂ) :
    MellinTransform f s = ∫ x in Set.Ioi (0 : ℝ), f x * (x : ℂ) ^ (s - 1) := by
  simp only [MellinTransform, mellin, smul_eq_mul, mul_comm]





local notation (name := mellintransform2) "𝓜" => MellinTransform

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

local notation "I" => Complex.I


local notation "ψ" => ChebyshevPsi




open _root_.ComplexConjugate

lemma smoothedChebyshevIntegrand_conj {SmoothingF : ℝ → ℝ} {ε X : ℝ} (Xpos : 0 < X) (s : ℂ) :
    SmoothedChebyshevIntegrand SmoothingF ε X (conj s) = conj (SmoothedChebyshevIntegrand SmoothingF ε X s) := by
  unfold SmoothedChebyshevIntegrand
  simp only [map_mul, map_div₀, map_neg]
  congr
  · exact deriv_riemannZeta_conj s
  · exact riemannZeta_conj s
  · simp_rw [MellinTransform_integral]

    rw[← integral_conj]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x xpos
    simp only [map_mul, Complex.conj_ofReal]
    congr
    nth_rw 1 [← map_one conj]
    rw[← map_sub, Complex.cpow_conj, Complex.conj_ofReal]
    rw[Complex.arg_ofReal_of_nonneg xpos.le]
    exact Real.pi_ne_zero.symm
  · rw[Complex.cpow_conj, Complex.conj_ofReal]
    rw[Complex.arg_ofReal_of_nonneg Xpos.le]
    exact Real.pi_ne_zero.symm

open _root_.MeasureTheory


attribute [fun_prop] Continuous.const_cpow
















theorem realDiff_of_complexDiff {f : ℂ → ℂ} (s : ℂ) (hf : DifferentiableAt ℂ f s) :
    ContinuousAt (fun (x : ℝ) ↦ f (s.re + x * I)) s.im := by
  apply ContinuousAt.comp _ (by fun_prop)
  convert (preTransparency := .instances) hf.continuousAt
  simp















lemma interval_membership (r : ℝ)(a b: ℝ)(h1 : r ∈ Set.Icc (min a b) (max a b)) (h2 : a < b) :
  a ≤ r ∧ r ≤ b := by
                                                       
  have min_eq : min a b = a := min_eq_left (le_of_lt h2)
  have max_eq : max a b = b := max_eq_right (le_of_lt h2)
  rw [min_eq, max_eq] at h1
  rw [← @mem_Icc]
  exact h1

lemma verticalIntegral_split_three_finite {s a b e σ : ℝ} {f : ℂ → ℂ}
    (hf : IntegrableOn (fun t : ℝ ↦ f (σ + t * I)) (Icc s e))
    (hab: s < a ∧ a < b ∧ b < e):
    VIntegral f σ s e =
    VIntegral f σ s a +
    VIntegral f σ a b +
    VIntegral f σ b e := by
  dsimp [VIntegral]
  rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)] at hf
  rw[← intervalIntegral.integral_add_adjacent_intervals (b := a), ← intervalIntegral.integral_add_adjacent_intervals (a := a) (b := b)]
  · ring
  all_goals apply IntervalIntegrable.mono_set hf; apply uIcc_subset_uIcc <;> apply mem_uIcc_of_le <;> linarith

lemma verticalIntegral_split_three_finite' {s a b e σ : ℝ} {f : ℂ → ℂ}
    (hf : IntegrableOn (fun t : ℝ ↦ f (σ + t * I)) (Icc s e))
    (hab: s < a ∧ a < b ∧ b < e):
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ s e) =
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ s a) +
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ a b) +
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ b e) := by
  have : (1 : ℂ) / (2 * π * I) * (VIntegral f σ s a) +
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ a b) +
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ b e) = (1 : ℂ) / (2 * π * I) * ((VIntegral f σ s a) +
    (VIntegral f σ a b) +
    (VIntegral f σ b e)) := by ring
  rw [this]
  clear this
  rw [← verticalIntegral_split_three_finite hf hab]

theorem SmoothedChebyshevPull2_aux1 {T σ₁ : ℝ} (σ₁lt : σ₁ < 1)
  (holoOn : HolomorphicOn (ζ' / ζ) (Icc σ₁ 2 ×ℂ Icc (-T) T \ {1})) :
  ContinuousOn (fun (t : ℝ) ↦ -ζ' (σ₁ + t * I) / ζ (σ₁ + t * I)) (Icc (-T) T) := by
  rw [show (fun (t : ℝ) ↦ -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) = -(ζ' / ζ) ∘ (fun (t : ℝ) ↦ ↑σ₁ + ↑t * I) by ext; simp; ring_nf]
  apply ContinuousOn.neg
  apply holoOn.continuousOn.comp (by fun_prop)
  intro t ht
  simp
  constructor
  · apply mem_reProdIm.mpr
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add, left_mem_Icc, ht, and_true]
    linarith
  · intro h
    replace h := congr_arg re h
    simp at h
    linarith

theorem SmoothedChebyshevPull2 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos: 0 < ε) (ε_lt_one : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (T_pos : 3 < T) {σ₁ σ₂ : ℝ}
    (σ₂_pos : 0 < σ₂) (σ₁_lt_one : σ₁ < 1)
    (σ₂_lt_σ₁ : σ₂ < σ₁)
    (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2)×ℂ (Icc (-T) T) \ {1}))
    (holoOn2 : HolomorphicOn (SmoothedChebyshevIntegrand SmoothingF ε X)
      (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (diff_SmoothingF : ContDiff ℝ 1 SmoothingF) :
    I₃₇ SmoothingF ε T X σ₁ =
      I₃ SmoothingF ε T X σ₁ -
      I₄ SmoothingF ε X σ₁ σ₂ +
      I₅ SmoothingF ε X σ₂ +
      I₆ SmoothingF ε X σ₁ σ₂ +
      I₇ SmoothingF ε T X σ₁ := by
  let z : ℂ := σ₂ - 3 * I
  let w : ℂ := σ₁ + 3 * I
  have σ₁_pos : 0 < σ₁ := by linarith

  have sub : z.Rectangle w ⊆ Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1} := by
                                         
    intro x hx
    constructor
    .                                       
      simp only [Rectangle, uIcc] at hx
      rw [Complex.mem_reProdIm] at hx ⊢
      obtain ⟨hx_re, hx_im⟩ := hx
                                                      
      have hzw_re : z.re < w.re := by
        simp only [z, w, add_re, sub_re, mul_re, ofReal_re, re_ofNat, im_ofNat, I_re, I_im, mul_zero, sub_zero, add_zero, mul_one]
        linarith
      have x_re_bounds : z.re ≤ x.re ∧ x.re ≤ w.re := by
        exact interval_membership x.re z.re w.re hx_re hzw_re
      have x_re_in_Icc : x.re ∈ Icc σ₂ 2 := by
        have ⟨h_left, h_right⟩ := x_re_bounds
        have h_left' : σ₂ ≤ x.re := by
          simp only [z, sub_re, mul_re, ofReal_re, re_ofNat, im_ofNat, I_re, I_im, mul_zero, sub_zero, mul_one] at h_left
          linarith
        have h_right' : x.re ≤ 2 := by
          apply le_trans h_right
          simp only [w, add_re, mul_re, ofReal_re, re_ofNat, im_ofNat, I_re, I_im, mul_zero, sub_zero, add_zero, mul_one]
          linarith
        exact ⟨h_left', h_right'⟩
                                                           
      have hzw_im : z.im < w.im := by
        simp only [z, w, ofReal_im, re_ofNat, im_ofNat, I_re, I_im, mul_zero, add_zero, add_im, sub_im, mul_im, mul_one, zero_sub]
        linarith
      have x_im_bounds : z.im ≤ x.im ∧ x.im ≤ w.im := by
        exact interval_membership x.im z.im w.im hx_im hzw_im
      have x_im_in_Icc : x.im ∈ Icc (-3) 3 := by
        have ⟨h_left, h_right⟩ := x_im_bounds
        have h_left' : -3 ≤ x.im := by
          simp only [z, ofReal_im, re_ofNat, im_ofNat, I_re, I_im, mul_zero, add_zero, sub_im, mul_im, mul_one, zero_sub] at h_left
          linarith
        have h_right' : x.im ≤ 3 := by
          simp only [w, ofReal_im, re_ofNat, im_ofNat, I_re, I_im, mul_zero, add_zero, add_im, mul_im, mul_one] at h_right
          linarith
        exact ⟨h_left', h_right'⟩
      exact ⟨x_re_in_Icc, x_im_in_Icc⟩
                                       
    . simp only [mem_singleton_iff]
                                    
      have x_re_upper: x.re ≤ σ₁ := by
        simp only [Rectangle, uIcc] at hx
        rw [Complex.mem_reProdIm] at hx
        obtain ⟨hx_re, _⟩ := hx
                                                
        have hzw_re : z.re < w.re := by
          simp only [z, w, add_re, sub_re, mul_re, ofReal_re, re_ofNat, im_ofNat, I_re, I_im, mul_zero, sub_zero, add_zero, mul_one]
          linarith
        have x_re_bounds : z.re ≤ x.re ∧ x.re ≤ w.re := by
          exact interval_membership x.re z.re w.re hx_re hzw_re
        have x_re_upper' : x.re ≤ w.re := by exact x_re_bounds.2
        simp only [w, add_re, mul_re, ofReal_re, re_ofNat, im_ofNat, I_re, I_im, mul_zero, sub_zero, add_zero, mul_one] at x_re_upper'
        linarith
                          
      have h_x_ne_one : x ≠ 1 := by
        intro h_eq
        have h_re : x.re = 1 := by rw [h_eq, Complex.one_re]
        have h1 : 1 ≤ σ₁ := by
          rw [← h_re]
          exact x_re_upper
        linarith
      exact h_x_ne_one
  have zero_over_box := HolomorphicOn.vanishesOnRectangle holoOn2 sub
  have splitting : I₃₇ SmoothingF ε T X σ₁ =
    I₃ SmoothingF ε T X σ₁ + I₅ SmoothingF ε X σ₁ + I₇ SmoothingF ε T X σ₁ := by
    unfold I₃₇ I₃ I₅ I₇
    apply verticalIntegral_split_three_finite'
    · apply ContinuousOn.integrableOn_Icc
      unfold SmoothedChebyshevIntegrand
      apply ContinuousOn.mul
      · apply ContinuousOn.mul
        · apply SmoothedChebyshevPull2_aux1 σ₁_lt_one holoOn
        · apply continuousOn_of_forall_continuousAt
          intro t t_mem
          have := Smooth1MellinDifferentiable diff_SmoothingF suppSmoothingF  ⟨ε_pos, ε_lt_one⟩ SmoothingFnonneg mass_one (s := ↑σ₁ + ↑t * I) (by simpa)
          simpa using! realDiff_of_complexDiff _ this
      · apply continuousOn_of_forall_continuousAt
        intro t t_mem
        apply ContinuousAt.comp
        · refine continuousAt_const_cpow' ?_
          intro h
          have : σ₁ = 0 := by
            have h_real : (↑σ₁ + ↑t * I).re = (0 : ℂ).re := by
              rw [h]
            simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
              sub_self, add_zero, zero_re] at h_real
            exact h_real
          linarith
        ·                        
          apply ContinuousAt.add
          · exact continuousAt_const
          · apply ContinuousAt.mul
            · apply continuous_ofReal.continuousAt
            · exact continuousAt_const
    · refine ⟨by linarith, by linarith, by linarith⟩
  calc I₃₇ SmoothingF ε T X σ₁ = I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) * (0 : ℂ) := by simp
    _ = I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) * (RectangleIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z w) := by rw [← zero_over_box]
    _ = I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) * (HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re z.im
    - HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
    + VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by simp [RectangleIntegral]
    _ = I₃₇ SmoothingF ε T X σ₁ - ((1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re z.im
    - (1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
    + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by ring
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - (1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
    + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, HIntegral, sub_im, ofReal_im, mul_im,
        re_ofNat, I_im, mul_one, im_ofNat, I_re, mul_zero, add_zero, zero_sub, ofReal_neg,
        ofReal_ofNat, sub_re, ofReal_re, mul_re, sub_self, sub_zero, add_re, add_im, zero_add,
        sub_neg_eq_add, I₄, sub_right_inj, add_left_inj, neg_inj, mul_eq_mul_left_iff, mul_eq_zero,
        I_ne_zero, inv_eq_zero, ofReal_eq_zero, OfNat.ofNat_ne_zero, or_false, false_or, z, w]
      left
      rfl
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, HIntegral, add_im, ofReal_im, mul_im,
        re_ofNat, I_im, mul_one, im_ofNat, I_re, mul_zero, add_zero, zero_add, ofReal_ofNat, sub_re,
        ofReal_re, mul_re, sub_self, sub_zero, add_re, sub_neg_eq_add, sub_im, zero_sub, I₆, w, z]
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, VIntegral, add_re, ofReal_re, mul_re,
        re_ofNat, I_re, mul_zero, im_ofNat, I_im, mul_one, sub_self, add_zero, sub_im, ofReal_im,
        mul_im, zero_sub, add_im, zero_add, smul_eq_mul, sub_re, sub_zero, sub_neg_eq_add, I₅,
        w, z]
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - I₅ SmoothingF ε X σ₂) := by
      simp only [I₅, one_div, mul_inv_rev, inv_I, neg_mul, VIntegral, sub_re, ofReal_re, mul_re,
        re_ofNat, I_re, mul_zero, im_ofNat, I_im, mul_one, sub_self, sub_zero, sub_im, ofReal_im,
        mul_im, add_zero, zero_sub, add_im, zero_add, smul_eq_mul, sub_neg_eq_add, z, w]
                                                                                                                               
    _ = I₃ SmoothingF ε T X σ₁
    + I₅ SmoothingF ε X σ₁
    + I₇ SmoothingF ε T X σ₁
    - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - I₅ SmoothingF ε X σ₂) := by
      rw [splitting]
    _ = I₃ SmoothingF ε T X σ₁
    - I₄ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₂
    + I₆ SmoothingF ε X σ₁ σ₂
    + I₇ SmoothingF ε T X σ₁ := by
      ring








lemma IBound_aux1 (X₀ : ℝ) (X₀pos : X₀ > 0) (k : ℕ) : ∃ C ≥ 1, ∀ X ≥ X₀, Real.log X ^ k ≤ C * X := by
                                          
  have ⟨M, hM⟩ := Filter.eventually_atTop.mp (isLittleO_log_rpow_rpow_atTop k zero_lt_one).eventuallyLE
                                                    
  let f := fun X ↦ Real.log X ^ k / X
  let I1 := Icc X₀ M
  have : 0 ∉ I1 := notMem_Icc_of_lt X₀pos
  have f_cont : ContinuousOn f (Icc X₀ M) :=
    ((continuousOn_log.pow k).mono (subset_compl_singleton_iff.mpr this)).div
    continuous_id.continuousOn (fun x hx ↦ ne_of_mem_of_not_mem hx this)
  have ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn f_cont
  use max C₁ 1, le_max_right C₁ 1
  intro X hX
  have Xpos : X > 0 := lt_of_lt_of_le X₀pos hX
  by_cases hXM : X ≤ M
  · rw[← div_le_iff₀ Xpos]
    calc
      f X ≤ ‖f X‖ := le_norm_self _
      _ ≤ C₁ := hC₁ X ⟨hX, hXM⟩
      _ ≤ max C₁ 1 := le_max_left C₁ 1
  · calc
      Real.log X ^ k ≤ ‖Real.log X ^ k‖ := le_norm_self _
      _ ≤ ‖X ^ 1‖ := by exact_mod_cast hM X (by linarith[hXM])
      _ = 1 * X := by
        rw[pow_one, one_mul]
        apply norm_of_nonneg
        exact Xpos.le
      _ ≤ max C₁ 1 * X := by
        rw[mul_le_mul_iff_left₀ Xpos]
        exact le_max_right C₁ 1


lemma I9I1 {SmoothingF : ℝ → ℝ} {ε X T : ℝ} (Xpos : 0 < X) :
    I₉ SmoothingF ε X T = conj (I₁ SmoothingF ε X T) := by
  unfold I₉ I₁
  simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
  rw [neg_mul, mul_neg, ← neg_mul]
  congr
  · ring
  · rw [← integral_conj, ← integral_comp_neg_Ioi, integral_Ici_eq_integral_Ioi]
    apply setIntegral_congr_fun <| measurableSet_Ioi
    intro t ht
    simp only
    rw[← smoothedChebyshevIntegrand_conj Xpos]
    simp

theorem I9Bound
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀{ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₉ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T) := by
  obtain ⟨C, Cpos, bound⟩ := I1Bound suppSmoothingF ContDiffSmoothingF SmoothingFnonneg mass_one
  refine ⟨C, Cpos, ?_⟩
  intro ε εpos ε_lt_one X X_gt T T_gt
  specialize bound ε εpos ε_lt_one X X_gt T_gt
  rwa [I9I1 (by linarith), norm_conj]

lemma one_add_inv_log {X : ℝ} (X_ge : 3 ≤ X): (1 + (Real.log X)⁻¹) < 2 := by
  rw[← one_add_one_eq_two]
  refine (add_lt_add_iff_left 1).mpr ?_
  refine inv_lt_one_of_one_lt₀ ?_
  refine (lt_log_iff_exp_lt ?_).mpr ?_ <;> linarith[Real.exp_one_lt_d9]

theorem log_pos (T : ℝ) (T_gt : 3 < T) : (Real.log T > 1) := by
    have elt3 : Real.exp 1 < 3 := by
      linarith[Real.exp_one_lt_d9]
    have logTgt1 : Real.log T > 1 := by
      refine (lt_log_iff_exp_lt ?_).mpr ?_
      · linarith
      · linarith
    exact logTgt1

lemma I2Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
                                                     
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A C₂ : ℝ} (has_bound: LogDerivZetaHasBound A C₂) (C₂pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1) {T : ℝ} (_ : 3 < T),
    let σ₁ := sigma1Of A T
    ‖I₂ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T) := by
  have ⟨C₁, C₁pos, Mbd⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  have := (IBound_aux1 3 (by norm_num) 9)
  obtain ⟨C₃, ⟨C₃_gt, hC₃⟩⟩ := this

  let C' : ℝ := C₁ * C₂ * C₃ * rexp 1
  have : C' > 0 := by positivity
  use ‖1/(2*π*I)‖ * (2 * C'), by
    refine Right.mul_pos ?_ ?_
    · rw[norm_pos_iff]
      simp[pi_ne_zero]
    · simp[this]
  intro X X_gt ε ε_pos ε_lt_one T T_gt σ₁
                                                    
  have Xpos : 0 < X := lt_trans (by simp only [Nat.ofNat_pos]) X_gt
  have Tpos : 0 < T := lt_trans (by norm_num) T_gt
  have log_big : 1 < Real.log T := by exact log_pos T (T_gt)
  unfold I₂
  rw[norm_mul, mul_assoc (c := X), ← mul_div]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have interval_length_nonneg : σ₁ ≤ 1 + (Real.log X)⁻¹ := by
    have : σ₁ = sigma1Of A T := rfl
    rw [this]
    unfold sigma1Of
    rw[sub_le_iff_le_add]
    nth_rw 1 [← add_zero 1]
    rw[add_assoc]
    apply add_le_add_right
    refine Left.add_nonneg ?_ ?_
    · rw[inv_nonneg, log_nonneg_iff Xpos]
      exact le_trans (by norm_num) (le_of_lt X_gt)
    · refine div_nonneg ?_ ?_
      exact A_in.1.le
      rw[log_nonneg_iff Tpos]
      exact le_trans (by norm_num) (le_of_lt T_gt)
  have : σ₁ = sigma1Of A T := rfl
  have σ₁pos : 0 < σ₁ := by
    have : σ₁ = sigma1Of A T := rfl
    rw [this]
    unfold sigma1Of
    rw[sub_pos]
    calc
      A / Real.log T ≤ 1 / 2 / Real.log T := by
        refine div_le_div_of_nonneg_right (A_in.2) ?_
        apply le_of_lt
        linarith
                                                          
      _ ≤ 1 / 2 / 1 := by
        refine div_le_div_of_nonneg_left (by norm_num) (by norm_num) ?_
        apply le_of_lt
        refine (lt_log_iff_exp_lt ?_).mpr ?_ <;> linarith[Real.exp_one_lt_d9]
      _ < 1 := by norm_num
  suffices ∀ σ ∈ Ioc σ₁ (1 + (Real.log X)⁻¹), ‖SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I)‖ ≤ C' * X / (ε * T) by
    calc
      ‖∫ (σ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
          SmoothedChebyshevIntegrand SmoothingF ε X (↑σ - ↑T * I)‖ ≤
          C' * X / (ε * T) * |1 + (Real.log X)⁻¹ - σ₁| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
        convert (preTransparency := .instances) this using 3
        apply uIoc_of_le
        exact interval_length_nonneg
      _ ≤ C' * X / (ε * T) * 2 := by
        apply mul_le_mul_of_nonneg_left
        rw[abs_of_nonneg (sub_nonneg.mpr interval_length_nonneg)]
        calc
          1 + (Real.log X)⁻¹ - σ₁ ≤ 1 + (Real.log X)⁻¹ := by linarith
          _ ≤ 2 := (one_add_inv_log X_gt.le).le
        positivity
      _ = 2 * C' * X / (ε * T) := by ring
                            
  intro σ hσ
  unfold SmoothedChebyshevIntegrand
  have log_deriv_zeta_bound : ‖ζ' (σ - T * I) / ζ (σ - T * I)‖ ≤ C₂ * (C₃ * T) := by
    calc
      ‖ζ' (σ - (T : ℝ) * I) / ζ (σ - (T : ℝ) * I)‖ = ‖ζ' (σ + (-T : ℝ) * I) / ζ (σ + (-T : ℝ) * I)‖ := by
        have Z : σ - (T : ℝ) * I = σ + (- T : ℝ) * I := by simp; ring_nf
        simp [Z]
      _ ≤ C₂ * Real.log |-T| ^ 9 := has_bound σ (-T) (by simp; rw [abs_of_pos Tpos]; exact T_gt) (by rw[this] at hσ; unfold sigma1Of at hσ; simp at hσ ⊢; replace hσ := hσ.1; linarith)
      _ ≤ C₂ * Real.log T ^ 9 := by simp
      _ ≤ C₂ * (C₃ * T) := by gcongr; exact hC₃ T (by linarith)

  calc
    ‖-ζ' (σ - T * I) / ζ (σ - T * I) * 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x))
        (σ - T * I) * X ^ (σ - T * I)‖ =
        ‖-ζ' (σ - T * I) / ζ (σ - T * I)‖ * ‖𝓜 (fun x ↦ (Smooth1 SmoothingF ε x))
        (σ - T * I)‖ * ‖(X : ℂ) ^ (σ - T * I)‖ := by
      repeat rw[norm_mul]
    _ ≤ C₂ * (C₃ * T) * (C₁ * (ε * ‖σ - T * I‖ ^ 2)⁻¹) * (rexp 1 * X) := by
      apply mul_le_mul₃
      · rw[neg_div, norm_neg]
        exact log_deriv_zeta_bound
      · refine Mbd σ₁ σ₁pos _ ?_ ?_ ε ε_pos ε_lt_one
        · simp only [mem_Ioc, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, sub_zero] at hσ ⊢
          linarith
        · simp only [mem_Ioc, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, sub_zero] at hσ ⊢
          linarith[one_add_inv_log X_gt.le]
      · rw[cpow_def_of_ne_zero]
        · rw[norm_exp,← ofReal_log, re_ofReal_mul]
          simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            sub_zero]
          rw[← le_log_iff_exp_le, Real.log_mul (exp_ne_zero 1), Real.log_exp, ← le_div_iff₀', add_comm, add_div, div_self, one_div]
          exact hσ.2
          · refine (Real.log_pos ?_).ne.symm
            linarith
          · apply Real.log_pos
            linarith
          · linarith
          · positivity
          · positivity
        · exact_mod_cast Xpos.ne.symm
      · positivity
      · positivity
      · positivity
    _ = (C' * X * T) / (ε * ‖σ - T * I‖ ^ 2) := by ring
    _ ≤ C' * X / (ε * T) := by
      have : ‖σ - T * I‖ ^ 2 ≥ T ^ 2 := by
        calc
          ‖σ - T * I‖ ^ 2 = ‖σ + (-T : ℝ) * I‖ ^ 2 := by
            congr 2
            push_cast
            ring
          _ = normSq (σ + (-T : ℝ) * I) := (normSq_eq_norm_sq _).symm
          _ = σ^2 + (-T)^2 := by
            rw[Complex.normSq_add_mul_I]
          _ ≥ T^2 := by
            rw[neg_sq]
            exact le_add_of_nonneg_left (sq_nonneg _)
      calc
        C' * X * T / (ε * ‖↑σ - ↑T * I‖ ^ 2) ≤ C' * X * T / (ε * T ^ 2) := by
          rw[div_le_div_iff_of_pos_left, mul_le_mul_iff_right₀]
          exact this
          exact ε_pos
          positivity
          apply mul_pos ε_pos
          exact lt_of_lt_of_le (pow_pos Tpos 2) this
          positivity
        _ = C' * X / (ε * T) := by
          field_simp

lemma I8I2 {SmoothingF : ℝ → ℝ}
    {X ε T σ₁ : ℝ} (T_gt : 3 < T) :
    I₈ SmoothingF ε X T σ₁ = -conj (I₂ SmoothingF ε X T σ₁) := by
  unfold I₂ I₈
  rw[map_mul, ← neg_mul]
  congr
  · simp[conj_ofNat]
  · rw[← intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro σ hσ
    simp only []
    rw[← smoothedChebyshevIntegrand_conj]
    simp only [map_sub, conj_ofReal, map_mul, conj_I, mul_neg, sub_neg_eq_add]
    exact lt_trans (by norm_num) T_gt

lemma I8Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A C₂ : ℝ} (has_bound : LogDerivZetaHasBound A C₂) (C₂_pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
                                                       
    ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_: 0 < ε)
    (_ : ε < 1)
    {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T)
    ‖I₈ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T) := by

  obtain ⟨C, hC, i2Bound⟩ := I2Bound suppSmoothingF ContDiffSmoothingF has_bound C₂_pos A_in
  use C, hC
  intro X hX ε hε0 hε1 T hT σ₁
  let i2Bound := i2Bound X hX hε0 hε1 hT
  rw[I8I2 hX, norm_neg, norm_conj]
            
  change ‖I₂ SmoothingF ε T X (sigma1Of A T)‖ ≤ C * X / (ε * T) at i2Bound
  unfold sigma1Of at i2Bound
  have σ₁_eq : σ₁ = 1 - A / (Real.log T) := rfl
  rw[σ₁_eq]
  exact i2Bound

lemma log_pow_over_xsq_integral_bounded :
  ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ T >3, ∫ x in Ioo 3 T, (Real.log x)^n / x^2 < C := by
  have elt3 : Real.exp 1 < 3 := by
    linarith[Real.exp_one_lt_d9]
  have log3gt1: 1 < Real.log 3 := by
    apply (Real.lt_log_iff_exp_lt (by norm_num)).mpr
    exact elt3
  intro n
  induction n with
  | zero =>
    use 1
    constructor
    · norm_num
    · intro T hT
      have Tgt3 : (3 : ℝ) < T := hT
      simp only [pow_zero]
      have h1 :(0 ≤ (-2) ∨ (-2) ≠ (-1) ∧ 0 ∉ Set.uIcc 3 T) := by
        right
        constructor
        · linarith
        · refine notMem_uIcc_of_lt ?_ ?_
          · exact three_pos
          · linarith
      have integral := integral_zpow h1
      ring_nf at integral

      have swap_int_kind : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), 1 / x ^ 2 = ∫ (x : ℝ) in Ioo 3 T, 1 / x ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.integral_Ioc_eq_integral_Ioo
      rw [← swap_int_kind]
      have change_int_power : ∫ (x : ℝ) in (3 : ℝ)..T, (1 : ℝ) / x ^ (↑ 2)
                            = ∫ (x : ℝ) in (3 : ℝ).. T, x ^ (-2 : ℤ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp
      rw [change_int_power, integral]
      have : T ^ (-1 : ℤ) > 0 := by
        refine zpow_pos ?_ (-1)
        linarith
      linarith
  | succ d ih =>
    obtain ⟨Cd, Cdpos, IH⟩ := ih
    use ((Real.log 3)^(d+1) / 3) + (d+1) * Cd
    constructor
    · have logpowpos : (Real.log 3) ^ (d + 1) > 0 := by
        refine pow_pos ?_ (d + 1)
        linarith
      have :  0 < (Real.log 3) ^ (d + 1) / 3 := by
        exact div_pos logpowpos (by norm_num)
      have dbound : d + 1 ≥ 1 := by
        exact Nat.le_add_left 1 d
      have : Real.log 3 ^ (d + 1) / 3 + (↑d + 1) * Cd > 0 / 3 + 0 := by
        have term1_pos : 0 < Real.log 3 ^ (d + 1) / 3 := this
        have term2_pos : 0 < (↑d + 1) * Cd := by
          refine (mul_pos_iff_of_pos_right Cdpos).mpr ?_
          exact Nat.cast_add_one_pos d
        refine add_lt_add ?_ term2_pos
        refine div_lt_div₀ logpowpos ?_ ?_ ?_
        linarith
        linarith
        linarith
      ring_nf at this
      ring_nf
      exact this
    · intro T Tgt3
      let u := fun x : ℝ ↦ (Real.log x) ^ (d + 1)
      let v := fun x : ℝ ↦ -1 / x
      let u' := fun x : ℝ ↦ (d + 1 : ℝ) * (Real.log x)^d / x
      let v' := fun x : ℝ ↦ 1 / x^2

      have swap_int_type : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ (d + 1) / x ^ 2
                          = ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ (d + 1) / x ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.integral_Ioc_eq_integral_Ioo

      rw [← swap_int_type]

      have uIcc_is_Icc : Set.uIcc 3 T = Set.Icc 3 T := by
        exact uIcc_of_lt Tgt3

      have cont_u : ContinuousOn u (Set.uIcc 3 T) := by
        unfold u
        rw[uIcc_is_Icc]
        refine ContinuousOn.pow ?_ (d + 1)
        refine continuousOn_of_forall_continuousAt ?_
        intro x hx
        refine continuousAt_log ?_
        linarith [hx.1]

      have cont_v : ContinuousOn v (Set.uIcc 3 T) := by
        unfold v
        rw[uIcc_is_Icc]
        refine continuousOn_of_forall_continuousAt ?_
        intro x hx
        have cont1 : ContinuousAt (fun (x : ℝ) ↦ 1 / x) x := by
          refine ContinuousAt.div₀ ?_ (fun ⦃U⦄ a ↦ a) ?_
          · exact continuousAt_const
          · linarith [hx.1]
        have cont2 : ContinuousAt (fun (x : ℝ) ↦ 1 / x) (-x) := by
          refine ContinuousAt.div₀ ?_ (fun ⦃U⦄ a ↦ a) ?_
          · exact continuousAt_const
          · linarith [hx.1]
        have fun1 : (fun (x : ℝ) ↦ -1 / x) = (fun (x : ℝ) ↦ 1 / (-x)) := by
          ext x
          ring_nf
        rw [fun1]
        exact ContinuousAt.comp cont2 (HasDerivAt.neg (hasDerivAt_id x)).continuousAt

      have deriv_u : (∀ x ∈ Set.Ioo (3 ⊓ T) (3 ⊔ T), HasDerivAt u (u' x) x) := by
        intro x hx
        have min3t : min 3 T = 3 := by
          exact min_eq_left_of_lt Tgt3
        have max3t : max 3 T = T := by
          exact max_eq_right_of_lt Tgt3
        rw[min3t, max3t] at hx
        unfold u u'
        have xne0 : x ≠ 0 := by linarith [hx.1]
        have deriv1 := Real.deriv_log x
        have deriv2 := (Real.hasDerivAt_log xne0).pow (d + 1)
        have fun1 : (fun x ↦ (↑d + 1) * Real.log x ^ d / x) = (fun x ↦ (↑d + 1) * Real.log x ^ d * x⁻¹) := by
          exact rfl
        have fun2 : (↑d + 1) * Real.log x ^ d / x =  (↑d + 1) * Real.log x ^ d * x⁻¹:= by
          exact rfl
        rw [fun2]
        simpa [Nat.cast_add, Nat.cast_one] using! deriv2

      have deriv_v : (∀ x ∈ Set.Ioo (3 ⊓ T) (3 ⊔ T), HasDerivAt v (v' x) x) := by
        intro x hx
        have min3t : min 3 T = 3 := by
          exact min_eq_left_of_lt Tgt3
        have max3t : max 3 T = T := by
          exact max_eq_right_of_lt Tgt3
        rw[min3t, max3t] at hx
        have xne0 : x ≠ 0 := by linarith [hx.1]
        unfold v v'
        have deriv1 := hasDerivAt_inv xne0
        have fun1 : (fun (x : ℝ) ↦ x⁻¹) = (fun (x : ℝ) ↦ 1 / x) := by
          ext x
          exact inv_eq_one_div x
        rw [fun1] at deriv1
        have fun2 : -(x ^ 2)⁻¹ = - 1 / x ^ 2 := by
          field_simp
        rw [fun2] at deriv1
        simpa [neg_div, neg_neg] using! HasDerivAt.neg deriv1

      have cont_u' : ContinuousOn u' (Set.uIcc 3 T) := by
        rw[uIcc_is_Icc]
        unfold u'
        refine ContinuousOn.div₀ ?_ ?_ ?_
        · refine ContinuousOn.mul ?_ ?_
          · exact continuousOn_const
          · refine ContinuousOn.pow ?_ d
            refine continuousOn_of_forall_continuousAt ?_
            intro x hx
            refine continuousAt_log ?_
            linarith [hx.1]
        · exact continuousOn_id' (Icc 3 T)
        · intro x hx
          linarith [hx.1]

      have cont_v' : ContinuousOn v' (Set.uIcc 3 T) := by
        rw[uIcc_is_Icc]
        unfold v'
        refine ContinuousOn.div₀ ?_ ?_ ?_
        · exact continuousOn_const
        · exact continuousOn_pow 2
        · intro x hx
          refine pow_ne_zero 2 ?_
          linarith [hx.1]

      have int_u': IntervalIntegrable u' MeasureTheory.volume 3 T := by
        exact ContinuousOn.intervalIntegrable cont_u'

      have int_v': IntervalIntegrable v' MeasureTheory.volume 3 T := by
        exact ContinuousOn.intervalIntegrable cont_v'

      have IBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt cont_u cont_v deriv_u deriv_v int_u' int_v'

      unfold u u' v v' at IBP

      have int1 : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ (d + 1) * (1 / x ^ 2)
                = ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ (d + 1) / x ^ 2 := by
          refine intervalIntegral.integral_congr ?_
          intro x hx
          field_simp

      rw[int1] at IBP
      rw[IBP]

      have int2 : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), (↑d + 1) * Real.log x ^ d / x * (-1 / x)
                = -(↑d + 1) * ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ d / x ^ 2 := by
        have : ∀ x, (↑d + 1) * Real.log x ^ d / x * (-1 / x)
         = -((↑d + 1) * Real.log x ^ d / x ^ 2) := by
          intro x
          field_simp
        have : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), (↑d + 1) * Real.log x ^ d / x * (-1 / x)
                = ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), -((↑d + 1) * Real.log x ^ d / x ^ 2) := by
          exact intervalIntegral.integral_congr fun ⦃x⦄ a ↦ this x
        rw [this]
        rw [←intervalIntegral.integral_const_mul]
        ring_nf

      rw[int2]

      have int3 : ∫ (x : ℝ) in (3 : ℝ)..(T : ℝ), Real.log x ^ d / x ^ 2
                = ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d / x ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.integral_Ioc_eq_integral_Ioo

      rw[int3]

      have IHbound : ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d / x ^ 2 < Cd := by
        exact IH T Tgt3

      ring_nf
      have bound2 : (Real.log T * Real.log T ^ d * T⁻¹) ≥ 0 := by
        have logTpos : Real.log T ≥ 0 := by
          refine log_nonneg ?_
          linarith
        apply mul_nonneg
        · apply mul_nonneg
          · exact logTpos
          · exact pow_nonneg logTpos d
        · positivity

      have bound3 : -(Real.log T * Real.log T ^ d * T⁻¹) ≤ 0 := by
        exact Right.neg_nonpos_iff.mpr bound2
      let S := Real.log T * Real.log T ^ d * T⁻¹
      have Spos : S ≥ 0 := by
        unfold S
        exact bound2

      have : (-(Real.log T * Real.log T ^ d * T⁻¹) + Real.log 3 * Real.log 3 ^ d * (1 / 3) +
                ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2) +
              ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2 = (-S + Real.log 3 * Real.log 3 ^ d * (1 / 3) +
                ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2) +
              ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2 := by
        unfold S
        rfl
      rw [this]

      have GetRidOfS : (-S + Real.log 3 * Real.log 3 ^ d * (1 / 3)
                      + ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2)
                      + ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2
                      ≤ ( Real.log 3 * Real.log 3 ^ d * (1 / 3)
                      + ↑d * ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2)
                      + ∫ (x : ℝ) in Ioo 3 T, Real.log x ^ d * x⁻¹ ^ 2 := by
        linarith [Spos]
      apply lt_of_le_of_lt GetRidOfS
      rw [add_assoc]

      have bound4 : ∫ x in Ioo 3 T, Real.log x ^ d / x ^ 2 < Cd := IHbound

      have bound5 : ↑d * ∫ x in Ioo 3 T, Real.log x ^ d / x ^ 2 ≤ ↑d * Cd := by
        apply (mul_le_mul_of_nonneg_left bound4.le)
        exact Nat.cast_nonneg d

      have bound_sum : ↑d * (∫ x in Ioo 3 T, Real.log x ^ d / x ^ 2)
                       + ∫ x in Ioo 3 T, Real.log x ^ d / x ^ 2 < ↑d * Cd + Cd := by
        linarith [bound4, bound5]
      rw[add_assoc]
      apply add_lt_add_right
      field_simp
      linarith [bound_sum]

theorem I3Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 < C),
      ∀ (X : ℝ) (_ : 3 < X)
        {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
        {T : ℝ} (_ : 3 < T),

        let σ₁ : ℝ := 1 - A / (Real.log T)
        ‖I₃ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T)) / ε := by
                                                      
  obtain ⟨CM, CMpos, CMhyp⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  obtain ⟨Cint, Cintpos, Cinthyp⟩ := log_pow_over_xsq_integral_bounded 9
  use Cint * CM * Cζ
  have : Cint * CM > 0 := mul_pos Cintpos CMpos
  have : Cint * CM * Cζ > 0 := mul_pos this Cζpos
  use this
  intro X Xgt3 ε εgt0 εlt1 T Tgt3 σ₁                             
  unfold I₃
  unfold SmoothedChebyshevIntegrand

  have elt3 : Real.exp 1 < 3 := by
    linarith[Real.exp_one_lt_d9]

  have log3gt1: 1 < Real.log 3 := by
    apply (Real.lt_log_iff_exp_lt (by norm_num)).mpr
    exact elt3

  have logXgt1 : Real.log X > 1 := by
    refine (lt_log_iff_exp_lt ?_).mpr ?_
    linarith
    linarith

  have logTgt1 : Real.log T > 1 := by
    refine (lt_log_iff_exp_lt ?_).mpr ?_
    linarith
    linarith

  have logX9gt1 : Real.log X ^ 1 > 1 := by
    refine (one_lt_pow_iff_of_nonneg ?_ ?_).mpr logXgt1
    linarith
    linarith

  have logT9gt1 : Real.log T ^ 1 > 1 := by
    refine (one_lt_pow_iff_of_nonneg ?_ ?_).mpr logTgt1
    linarith
    linarith

  have t_bounds : ∀ t ∈ Ioo (-T) (-3), 3 < |t| ∧ |t| < T := by
    intro t ht
    obtain ⟨h1,h2⟩ := ht
    have : |t| = -t := by
      refine abs_of_neg ?_
      linarith[h2]
    have abs_tgt3 : 3 < |t| := by
      rw[this]
      linarith[h2]
    have abs_tltX : |t| < T := by
      rw[this]
      linarith[h1]
    exact ⟨abs_tgt3, abs_tltX⟩

  have logtgt1_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| > 1 := by
    intro t ht
    obtain ⟨h1,h2⟩ := ht
    refine logt_gt_one ?_
    exact h1.le

  have logt9gt1_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| ^ 9  > 1 := by
    intro t ht
    refine one_lt_pow₀ (logtgt1_bounds t ht) ?_
    linarith

  have logtltlogT_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| < Real.log T := by
    intro t ht
    obtain ⟨h1,h2⟩ := ht
    have m := log_lt_log (by linarith : 0 < (|t|)) (h2 : |t| < T )
    exact m

  have logt9ltlogT9_bounds : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| ^ 9 < Real.log T ^ 9 := by
    intro t ht
    obtain h1 := logtltlogT_bounds t ht
    obtain h2 := logtgt1_bounds t ht
    have h3: 0 ≤ Real.log |t| := by linarith
    refine (pow_lt_pow_iff_left₀ ?_ ?_ ?_).mpr h1
    linarith
    linarith
    linarith

  have Aoverlogt9gtAoverlogT9_bounds : ∀ t, 3 < |t| ∧ |t| < T →
        A / Real.log |t| ^ 9 > A / Real.log T ^ 9 := by
    intro t ht
    have h1 := logt9ltlogT9_bounds t ht
    have h2 :=logt9gt1_bounds t ht
    refine div_lt_div_of_pos_left ?_ ?_ h1
    linarith [hA.1]
    linarith

  have AoverlogT9in0half: A / Real.log T ^ 1 ∈ Ioo 0 (1/2) := by
    constructor
    · refine div_pos ?_ ?_
      refine EReal.coe_pos.mp ?_
      exact EReal.coe_lt_coe hA.1
      linarith
    · refine (div_lt_comm₀ ?_ ?_).mpr ?_
      linarith
      linarith
      refine (div_lt_iff₀' ?_).mpr ?_
      linarith
      have hA_lt : A ≤ 1 / 2 := hA.2
      have hbound : 1 / 2 < (1 / 2) * Real.log T ^ 1 := by
        linarith
      linarith

  have σ₁lt2 : (σ₁ : ℝ) < 2 := by
    unfold σ₁
    calc 1 - A / Real.log T
      < 1 - 0 := by simp only [sub_zero]; exact sub_lt_self 1 (div_pos hA.1 (lt_trans zero_lt_one logTgt1))
      _ = 1 := by norm_num
      _ < 2 := by norm_num

  have σ₁lt1 : σ₁ < 1 := by
    unfold σ₁
    calc 1 - A / Real.log T
      < 1 - 0 := by simp only [sub_zero]; exact sub_lt_self 1 (div_pos hA.1 (by linarith [logTgt1]))
      _ = 1 := by norm_num

  have σ₁pos : 0 < σ₁ := by
    unfold σ₁
    rw [sub_pos]
    calc
      A / Real.log T ≤ (1/2) / Real.log T := by
        apply div_le_div_of_nonneg_right hA.2 (by linarith)
      _ ≤ (1/2) / 1 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      _ = 1/2 := by norm_num
      _ < 1 := by norm_num

  have quotient_bound : ∀ t, 3 < |t| ∧ |t| < T → Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2) ≤ Real.log |t| ^ 9/ t ^ 2  := by
    intro t ht
    have loght := logt9gt1_bounds t ht
    have logpos : Real.log |t| ^ 9 > 0 := by linarith
    have denom_le : t ^ 2 ≤ σ₁ ^ 2 + t ^ 2 := by linarith [sq_nonneg σ₁]
    have denom_pos : 0 < t ^ 2 := by
      have : t ^ 2 = |t| ^ 2 := by
        exact Eq.symm (sq_abs t)
      rw [this]
      have h1 := ht.1
      have abspos : |t| > 0 := by linarith
      exact sq_pos_of_pos abspos
    have denom2_pos : 0 < σ₁ ^ 2 + t ^ 2 := by linarith [sq_nonneg σ₁]
    exact (div_le_div_iff_of_pos_left logpos denom2_pos denom_pos).mpr denom_le

  have boundthing : ∀ t, 3 < |t| ∧ |t| < T → σ₁ ∈ Ici (1 - A / Real.log |t|) := by
    intro t ht
    have h1 := Aoverlogt9gtAoverlogT9_bounds t ht
    unfold σ₁
    apply mem_Ici.mpr
    ring_nf

    apply sub_le_sub_left
    have : Real.log |t| ≤ Real.log T := by
      apply Real.log_le_log (by linarith) (le_of_lt ht.2)
    exact div_le_div_of_nonneg_left (le_of_lt hA.1) (Real.log_pos (by linarith)) this

  have : ∫ (t : ℝ) in -T..-3,
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I) = ∫ (t : ℝ) in Ioo (-T : ℝ) (-3 : ℝ),
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I) := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact MeasureTheory.integral_Ioc_eq_integral_Ioo
  rw[this]

  have MellinBound : ∀ (t : ℝ) , ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ₁ + t * I)‖ ≤ CM * (ε * ‖(σ₁ + t * I)‖ ^ 2)⁻¹ := by
    intro t
    apply CMhyp σ₁
    exact σ₁pos
    · simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
      exact le_rfl
    · simpa only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero] using σ₁lt2.le
    exact εgt0
    exact εlt1

  have logzetabnd : ∀ t : ℝ, 3 < |t| ∧ |t| < T → ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ ≤ Cζ * Real.log (|t| : ℝ) ^ 9 := by
    intro t tbounds
    obtain ⟨tgt3, tltT⟩ := tbounds
    apply hCζ
    · exact tgt3
    · apply boundthing
      constructor
      · exact tgt3
      · exact tltT

  have Mellin_bd : ∀ t, 3 < |t| ∧ |t| < T →
  ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ₁ + t * I)‖ ≤ CM * (ε * ‖σ₁ + t * I‖ ^ 2)⁻¹ := by
    intro t ht
    apply MellinBound

  have logzeta_bd : ∀ t, 3 < |t| ∧ |t| < T →
    ‖ζ' (σ₁ + t * I) / ζ (σ₁ + t * I)‖ ≤ Cζ * Real.log |t| ^ 9 := by
    intro t t_bounds
    obtain ⟨abs_tgt3,abs_tltX⟩ := t_bounds
    apply logzetabnd
    constructor
    · exact abs_tgt3
    · exact abs_tltX
  have : ‖1 / (2 * ↑π * I) *
        (I * ∫ (t : ℝ) in -X..-3,
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) *
          𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
          ↑T ^ (↑σ₁ + ↑t * I))‖
    =
    (1 / (2 * π)) * ‖∫ (t : ℝ) in -X..-3,
        -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
        ↑T ^ (↑σ₁ + ↑t * I)‖ := by
    simp only [norm_mul]
    rw[Complex.norm_I]
    simp only [one_mul]
    have : ‖1 / (2 * ↑π * I)‖ = 1 / (2 * π) := by

      ring_nf
      simp only [norm_mul]
      rw[inv_I]
      have : ‖-I‖ = ‖-1 * I‖ := by
        simp
      rw[this]
      have : ‖-1 * I‖ = ‖-1‖ * ‖I‖ := by
        simp
      rw[this, Complex.norm_I]
      ring_nf
      simp [Real.pi_nonneg]
    rw[this]

  let f t := (-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
        ↑X ^ (↑σ₁ + ↑t * I)

  let g t := Cζ * CM * Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) * X ^ σ₁

  have norm_X_sigma1: ∀ (t : ℝ), ‖↑(X : ℂ) ^ (↑σ₁ + ↑t * I)‖ = X ^ σ₁ := by
    intro t
    have Xpos : 0 < X := by linarith
    have : ((↑σ₁ + ↑t * I).re) = σ₁ := by
      simp

    nth_rw 2[← this]
    apply Complex.norm_cpow_eq_rpow_re_of_pos Xpos

  have bound_integral : ∀ (t : ℝ), 3  < |t| ∧ |t| < T → ‖f t‖ ≤ g t := by
    intro t
    rintro ⟨ht_gt3, ht_ltT⟩
    have Xσ_bound : ‖↑(X : ℂ) ^ (↑σ₁ + ↑t * I)‖ = X ^ σ₁ := norm_X_sigma1 t
    have logtgt1 : 1 < Real.log |t| := by
        exact logt_gt_one ht_gt3.le
    have hζ := logzetabnd t ⟨ht_gt3, ht_ltT⟩
    have h𝓜 := MellinBound t
    have : ‖f ↑t‖ = ‖(-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
            𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I)‖ := by
      rfl
    rw[this]
    have : ‖(-ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)) *
            𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I)‖ ≤ ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
            ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑(X : ℝ) : ℂ) ^ (↑σ₁ + ↑t * I)‖ := by
      simp [norm_neg]

    have : ‖ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I)‖ *
            ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I)‖ *
            ‖(↑X : ℂ) ^ (↑σ₁ + ↑t * I)‖ ≤ (Cζ * Real.log |t| ^ 9) *
            (CM * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹) * X ^ σ₁:= by
      rw[Xσ_bound]
      gcongr
    have : (Cζ * Real.log |t| ^ 9) * (CM * (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)⁻¹) * X ^ σ₁ = g t := by
      unfold g
      ring_nf
    linarith

  have int_with_f: ‖1 / (2 * ↑π * I) *
      (I *
        ∫ (t : ℝ) in Ioo (-T) (-3),
          -ζ' (↑σ₁ + ↑t * I) / ζ (↑σ₁ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₁ + ↑t * I) *
            ↑X ^ (↑σ₁ + ↑t * I))‖ = ‖1 / (2 * ↑π * I) *
      (I *
        ∫ (t : ℝ) in Ioo (-T) (-3),
          f t)‖ := by
      unfold f
      simp
  rw[int_with_f]
  apply (norm_mul_le _ _).trans
  have int_mulbyI_is_int : ‖I * ∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ = ‖ ∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ := by
    rw [Complex.norm_mul, Complex.norm_I]
    ring
  rw[int_mulbyI_is_int]

  have norm_1over2pii_le1: ‖1 / (2 * ↑π * I)‖ ≤ 1 := by
    simp
    have pi_gt_3 : Real.pi > 3 := by
      exact pi_gt_three
    have pi_pos : 0 < π := by linarith [pi_gt_3]
    have abs_pi_inv_le : |π|⁻¹ ≤ (1 : ℝ) := by
      rw [abs_of_pos pi_pos]
      have h : 1 = π * π⁻¹ := by
        field_simp
      rw[h]
      nth_rw 1 [← one_mul π⁻¹]
      apply mul_le_mul_of_nonneg_right
      · linarith
      · exact inv_nonneg.mpr (le_of_lt pi_pos)
    have : (0 : ℝ) < (2 : ℝ) := by norm_num
    have h_half_le_one : (2 : ℝ)⁻¹ ≤ 1 := by norm_num
    rw [abs_of_pos pi_pos] at abs_pi_inv_le
    norm_num [abs_of_pos pi_pos]; linarith

  have : ‖1 / (2 * ↑π * I)‖ * ‖∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ ≤  ‖∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ := by
    apply mul_le_of_le_one_left
    · apply norm_nonneg
    · exact norm_1over2pii_le1
  apply le_trans this
  have : ‖ ∫ (t : ℝ) in Ioo (-T) (-3), f ↑t‖ ≤  ∫ (t : ℝ) in Ioo (-T) (-3), ‖f ↑ t‖ := by
    apply norm_integral_le_integral_norm
  apply le_trans this

  have norm_f_nonneg: ∀ t, ‖f t‖ ≥ 0 := by
    exact fun t ↦ norm_nonneg (f t)

  have g_cont : ContinuousOn g (Icc (-T) (-3)) := by
    unfold g
    refine ContinuousOn.mul ?_ ?_
    refine ContinuousOn.mul ?_ ?_
    refine ContinuousOn.mul ?_ ?_
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_const
    · exact continuousOn_const
    · refine ContinuousOn.pow ?_ 9
      refine ContinuousOn.log ?_ ?_
      · refine Continuous.continuousOn ?_
        exact _root_.continuous_abs
      · intro t ht
        have h1 := ht.1
        have h2 := ht.2
        by_contra!
        have : t = 0 := by
          exact abs_eq_zero.mp this
        rw[this] at h2
        absurd
        h2
        linarith
    · refine ContinuousOn.inv₀ ?_ ?_
      · refine ContinuousOn.mul ?_ ?_
        · exact continuousOn_const
        · refine ContinuousOn.pow ?_ 2
          refine ContinuousOn.norm ?_
          refine ContinuousOn.add ?_ ?_
          · exact continuousOn_const
          · refine ContinuousOn.mul ?_ ?_
            · refine continuousOn_of_forall_continuousAt ?_
              intro x hx
              exact continuous_ofReal.continuousAt
            · exact continuousOn_const
      · intro x hx
        have norm_sq_pos : ‖(σ₁ : ℂ) + x * Complex.I‖ ^ 2 = σ₁ ^ 2 + x ^ 2 := by
          rw [Complex.sq_norm]
          exact normSq_add_mul_I σ₁ x
        have : 0 < σ₁ ^ 2 + x ^ 2 := by
          apply add_pos_of_pos_of_nonneg
          · exact sq_pos_of_pos σ₁pos
          · exact sq_nonneg x
        apply mul_ne_zero
        · linarith
        · rw [norm_sq_pos]
          exact ne_of_gt this
    · exact continuousOn_const

  have g_integrable_Icc : IntegrableOn g (Icc (-T) (-3)) volume := by
    exact ContinuousOn.integrableOn_Icc g_cont

  have g_integrable_Ioo : IntegrableOn g (Ioo (-T) (-3)) volume := by
    apply MeasureTheory.IntegrableOn.mono_set g_integrable_Icc
    exact Ioo_subset_Icc_self

  have int_normf_le_int_g: ∫ (t : ℝ) in Ioo (-T) (-3), ‖f ↑t‖
                        ≤ ∫ (t : ℝ) in Ioo (-T) (-3), g ↑t := by

    by_cases h_int : IntervalIntegrable (fun t : ℝ ↦ ‖f t‖) volume (-T) (-3)
    · have f_int : IntegrableOn (fun (t : ℝ) ↦ ‖f t‖) (Ioo (-T : ℝ) (-3 : ℝ)) volume := by
        have hle : -T ≤ -3 := by linarith
        exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hle).mp h_int
      apply MeasureTheory.setIntegral_mono_on
      exact f_int
      exact g_integrable_Ioo
      exact measurableSet_Ioo
      intro t ht
      apply bound_integral
      have : |t| = -t := by
        refine abs_of_neg ?_
        linarith [ht.2]
      have abs_tgt3 : 3 < |t| := by
        rw[this]
        linarith[ht.2]
      have abs_tltX : |t| < T := by
        rw[this]
        linarith[ht.1]
      constructor
      · linarith
      · linarith
    · have : ∫ (t : ℝ) in -T..-3, ‖f ↑ t‖ = ∫ (t : ℝ) in Ioo (-T) (-3), ‖f ↑t‖  := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.integral_Ioc_eq_integral_Ioo
      have : ∫ (t : ℝ) in Ioo (-T) (-3), ‖f ↑t‖ = 0 := by
        rw [← this]
        exact intervalIntegral.integral_undef h_int
      rw [this]
      apply MeasureTheory.setIntegral_nonneg
      · exact measurableSet_Ioo
      · intro t ht
        have abst_negt : |t| = -t := by
          refine abs_of_neg ?_
          linarith [ht.2]
        have tbounds1 : 3 < |t| ∧ |t| < T := by
          rw[abst_negt]
          constructor
          · linarith [ht.2]
          · linarith [ht.1]
        unfold g
        apply mul_nonneg
        apply mul_nonneg
        apply mul_nonneg
        apply mul_nonneg
        · linarith
        · linarith
        · have : 0 ≤ Real.log |t| := by
            apply Real.log_nonneg
            linarith [tbounds1.1]
          positivity
        · positivity

        · apply Real.rpow_nonneg
          linarith

  apply le_trans int_normf_le_int_g
  unfold g

  have : X ^ σ₁ = X ^ (1 - A / Real.log T ) := by
    rfl
  rw[this]

  have : X ^ (1 - A / Real.log T) = X * X ^ (- A / Real.log T) := by
    have hX : X > 0 := by linarith
    simp only [Real.rpow_sub hX, Real.rpow_one]
    have h₁ : X ^ (-A / Real.log T) * X ^ (A / Real.log T) = 1 := by
      rw [← Real.rpow_add hX]
      ring_nf
      exact rpow_zero X
    field_simp
    simpa only [neg_div, mul_comm] using h₁.symm

  rw[this]

  have Bound_of_log_int: ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) ≤ Cint / ε := by
    have : ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)
        = (1 / ε) * ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / ‖↑σ₁ + ↑t * I‖ ^ 2 := by
      rw [← integral_const_mul]
      congr with t
      field_simp [εgt0]
    rw[this]
    have normsquared : ∀ (t : ℝ), ‖↑σ₁ + ↑t * I‖ ^ 2 = σ₁ ^ 2 + t ^ 2 := by
      intro t
      simp only [Complex.sq_norm]
      exact normSq_add_mul_I σ₁ t

    have : ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / ‖↑σ₁ + ↑t * I‖ ^ 2
          = ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2) := by
      simp_rw [normsquared]

    have bound : ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / ‖↑σ₁ + ↑t * I‖ ^ 2 ≤ Cint := by
      rw [this]
      have : ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)
            ≤ ∫ t in Ioo (-T) (-3), Real.log |t| ^ 9 /  t ^ 2 := by
        refine setIntegral_mono_on ?_ ?_ ?_ ?_
        ·
          have cont : ContinuousOn (fun t ↦ Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)) (Set.Icc (-T) (-3)) := by
            refine ContinuousOn.div ?_ ?_ ?_
            · refine ContinuousOn.pow ?_ 9
              refine ContinuousOn.log ?_ ?_
              · refine continuousOn_of_forall_continuousAt ?_
                intro x hx
                refine Continuous.continuousAt ?_
                exact _root_.continuous_abs
              · intro x hx
                have h1 : x ≤ -3 := hx.2
                have xne0 : x ≠ 0 := by linarith
                exact abs_ne_zero.mpr xne0
            · refine ContinuousOn.add ?_ ?_
              · exact continuousOn_const
              · refine ContinuousOn.pow ?_ 2
                exact continuousOn_id' (Icc (-T) (-3))
            · intro t ht
              have h1 : t ≤ -3 := ht.2
              have h2 : t ≠ 0 := by linarith
              have h3 : 0 < t ^ 2 := pow_two_pos_of_ne_zero h2
              have h4 : 0 < σ₁ ^ 2 := sq_pos_of_pos σ₁pos
              linarith [h3, h4]
          have int_Icc : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)) (Icc (-T) (-3)) volume := by
            exact ContinuousOn.integrableOn_Icc cont
          have int_Ioo : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / (σ₁ ^ 2 + t ^ 2)) (Ioo (-T) (-3)) volume := by
            apply MeasureTheory.IntegrableOn.mono_set int_Icc
            exact Ioo_subset_Icc_self
          exact int_Ioo
        · have cont : ContinuousOn (fun t ↦ Real.log |t| ^ 9 / t ^ 2) (Set.Icc (-T) (-3)) := by
            refine ContinuousOn.div ?_ ?_ ?_
            · refine ContinuousOn.pow ?_ 9
              refine ContinuousOn.log ?_ ?_
              · refine continuousOn_of_forall_continuousAt ?_
                intro x hx
                refine Continuous.continuousAt ?_
                exact _root_.continuous_abs
              · intro x hx
                have h1 : x ≤ -3 := hx.2
                have xne0 : x ≠ 0 := by linarith
                exact abs_ne_zero.mpr xne0
            · refine ContinuousOn.pow ?_ 2
              exact continuousOn_id' (Icc (-T) (-3))
            · intro t ht
              have h1 : t ≤ -3 := ht.2
              have tne0 : t ≠ 0 := by linarith
              exact pow_ne_zero 2 tne0
          have int_Icc : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / t ^ 2) (Icc (-T) (-3)) volume := by
            exact ContinuousOn.integrableOn_Icc cont
          have int_Ioo : IntegrableOn (fun t ↦ Real.log |t| ^ 9 / t ^ 2) (Ioo (-T) (-3)) volume := by
            apply MeasureTheory.IntegrableOn.mono_set int_Icc
            exact Ioo_subset_Icc_self
          exact int_Ioo
        · exact measurableSet_Ioo
        · intro x hx
          have xneg : x < 0 := by linarith[hx.2]
          have absx : |x| = -x := abs_of_neg xneg
          have h1 : 3 < |x| ∧ |x| < T := by
            rw[absx]
            constructor
            · linarith [hx.2]
            · linarith [hx.1]
          exact quotient_bound x (t_bounds x hx)
      apply le_trans this
      have : ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / t ^ 2
            = ∫ (t : ℝ) in Ioo 3 T, Real.log t ^ 9 / t ^ 2 := by
        have eq_integrand : ∀ (t : ℝ), t ∈ Ioo (-T) (-3) → (Real.log |t|) ^ 9 / t ^ 2 = (Real.log (-t)) ^ 9 / (-t) ^ 2 := by
          intro t ht
          have tneg : t < 0 := by linarith[ht.2]
          have : |t| = -t := abs_of_neg tneg
          rw [this, neg_sq]

        have : ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / t ^ 2
              = ∫ (t : ℝ) in Ioo (-T) (-3), Real.log (-t) ^ 9 / (-t) ^ 2 := by
          exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo eq_integrand

        rw [this]

        have interval_to_Ioo1 : ∫ (t : ℝ) in -T..-3, Real.log (-t) ^ 9 / (-t) ^ 2
                        = ∫ (t : ℝ) in Ioo (-T) (-3), Real.log (-t) ^ 9 / (-t) ^ 2 := by
          rw [intervalIntegral.integral_of_le (by linarith)]
          exact MeasureTheory.integral_Ioc_eq_integral_Ioo

        have interval_to_Ioo2 : ∫ (t : ℝ) in (3)..(T), Real.log t ^ 9 / t ^ 2
                    = ∫ (t : ℝ) in Ioo 3 T, Real.log t ^ 9 / t ^ 2 := by
          rw [intervalIntegral.integral_of_le (by linarith)]
          exact MeasureTheory.integral_Ioc_eq_integral_Ioo

        rw [← interval_to_Ioo1, ← interval_to_Ioo2]
        rw [intervalIntegral.integral_comp_neg (fun (t : ℝ) ↦ Real.log (t) ^ 9 / (t) ^ 2)]
        simp
      rw [this]
      have : ∫ (t : ℝ) in Ioo 3 T, Real.log t ^ 9 / t ^ 2 < Cint := by
        exact Cinthyp T Tgt3
      linarith
    rw [ mul_comm]
    rw [← mul_div_assoc, mul_one]
    exact (div_le_div_iff_of_pos_right εgt0).mpr bound

  have factor_out_constants :
  ∫ (t : ℝ) in Ioo (-T) (-3), Cζ * CM * Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) * (X * X ^ (-A / Real.log T ))
  = Cζ * CM * (X * X ^ (-A / Real.log T)) * ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2) := by
     rw [mul_assoc, ← mul_assoc (Cζ * CM), ← mul_assoc]
     field_simp
     rw [← integral_const_mul]
     apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
     intro t ht
     ring_nf

  rw [factor_out_constants]

  have : Cζ * CM * (X * X ^ (-A / Real.log T)) * ∫ (t : ℝ) in Ioo (-T) (-3), Real.log |t| ^ 9 / (ε * ‖↑σ₁ + ↑t * I‖ ^ 2)
        ≤ Cζ * CM * ((X : ℝ) * X ^ (-A / Real.log T)) * (Cint / ε) := by
    apply mul_le_mul_of_nonneg_left
    · exact Bound_of_log_int
    · have hpos : 0 < X * X ^ (-A / Real.log T) := by
        apply mul_pos
        · linarith
        · apply Real.rpow_pos_of_pos
          linarith
      apply mul_nonneg
      · apply mul_nonneg
        · linarith
        · linarith
      · linarith [hpos]

  apply le_trans this
  ring_nf
  field_simp; norm_num

lemma I7I3 {SmoothingF : ℝ → ℝ} {ε X T σ₁ : ℝ} (Xpos : 0 < X) :
    I₇ SmoothingF ε T X σ₁ = conj (I₃ SmoothingF ε T X σ₁) := by
  unfold I₃ I₇
  simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
  rw [neg_mul, mul_neg, ← neg_mul]
  congr
  · ring
  · rw [← intervalIntegral_conj, ← intervalIntegral.integral_comp_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only
    rw [← smoothedChebyshevIntegrand_conj Xpos]
    simp

lemma I7Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2))
    : ∃ (C : ℝ) (_ : 0 < C),
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1) {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T)
    ‖I₇ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T)) / ε := by
  obtain ⟨C, Cpos, bound⟩ := I3Bound suppSmoothingF ContDiffSmoothingF hCζ Cζpos hA
  refine ⟨C, Cpos, fun X X_gt ε εpos ε_lt_one T T_gt ↦ ?_⟩
  specialize bound X X_gt εpos ε_lt_one T_gt
  intro σ₁
  rwa [I7I3 (by linarith), norm_conj]

lemma I4Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)

    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {A : ℝ}                                                                
    (hA : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T)
    ‖I₄ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T)) / ε := by

  have reOne : re 1 = 1 := by exact rfl
  have imOne : im 1 = 0 := by exact rfl
  have reThree : re 3 = 3 := by exact rfl
  have imThree : im 3 = 0 := by exact rfl

  have elt3 : Real.exp 1 < 3 := by
    linarith[Real.exp_one_lt_d9]

  unfold I₄ SmoothedChebyshevIntegrand

  let S : Set ℝ := (fun (t : ℝ) ↦ ↑‖-ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)‖₊) '' Icc 0 1
  let C' : ℝ := sSup S
  have bddAboveS : BddAbove S := by
    refine IsCompact.bddAbove ?_
    unfold S
    refine IsCompact.image_of_continuousOn ?_ ?_
    · exact isCompact_Icc
    · refine ContinuousOn.norm ?_
      have : (fun (t : ℝ) ↦ -ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)) =
        (fun (t : ℝ) ↦ -(ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I))) := by
        apply funext
        intro x
        apply neg_div
      rw[this]
      refine ContinuousOn.neg ?_
      have : (fun (t : ℝ) ↦ ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)) =
        ((ζ' / ζ) ∘ (fun (t : ℝ) ↦ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I))) := by exact rfl
      rw[this]
      apply h_logDeriv_holo.continuousOn.comp' (by fun_prop)
      unfold MapsTo
      intro x xInIcc
      simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le, Set.mem_sdiff]
      have : ¬↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I = 1 := by
        by_contra h
        rw[Complex.ext_iff, sub_re, add_re, sub_im, add_im] at h
        repeat rw[mul_im] at h
        repeat rw[mul_re] at h
        rw[sub_im, sub_re, reOne, imOne, reThree, imThree, I_im, I_re] at h
        repeat rw[ofReal_re] at h
        repeat rw[ofReal_im] at h
        ring_nf at h
        obtain ⟨_, ripGoal⟩ := h
        have : -3 ≠ 0 := by norm_num
        linarith
      refine ⟨?_, this⟩
      rw [mem_reProdIm]
      simp only [sub_re, add_re, ofReal_re, mul_re, one_re, ofReal_im, sub_im, one_im, sub_self,
        mul_zero, sub_zero, re_ofNat, I_re, im_ofNat, I_im, mul_one, add_im, mul_im, zero_mul,
        add_zero, zero_sub, mem_Icc, le_refl, neg_le_self_iff, Nat.ofNat_nonneg, and_self, and_true]
      rw [Set.uIcc_of_le]
      · rw [mem_Icc]
        constructor
        · simp only [le_add_iff_nonneg_right]
          apply mul_nonneg
          · exact xInIcc.1
          · linarith [hσ₂.2]
        · have : σ₂ + x * (1 - σ₂) = σ₂ * (1 - x) + x := by ring
          rw [this]
          clear this
          have : (2 : ℝ) = 1 * 1 + 1 := by norm_num
          rw [this]
          clear this
          gcongr
          · linarith [xInIcc.2]
          · exact hσ₂.2.le
          · linarith [xInIcc.1]
          · exact xInIcc.2
      · linarith [hσ₂.2]

  have CPrimeNonneg : 0 ≤ C' := by
    apply Real.sSup_nonneg
    intro x x_in_S
    obtain ⟨t, ht, rfl⟩ := x_in_S
    exact NNReal.coe_nonneg _

  obtain ⟨D, Dpos, MellinSmooth1bBound⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  let C : ℝ := C' * D / sInf ((fun t => ‖ σ₂ + (t : ℝ) * (1 - σ₂) - 3 * I ‖₊ ^ 2) '' Set.Icc 0 1)
  use C
  have sInfPos : 0 < sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1) := by
    refine (IsCompact.lt_sInf_iff_of_continuous ?_ ?_ ?_ 0).mpr ?_
    · exact isCompact_Icc
    · exact Nonempty.of_subtype
    · have : (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) =
        (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ * ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊) := by
        apply funext
        intro x
        rw[pow_two]
      rw[this]
      have : ContinuousOn (fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊) (Icc 0 1) := by
        refine ContinuousOn.nnnorm ?_
        refine ContinuousOn.sub ?_ (by exact continuousOn_const)
        refine ContinuousOn.add (by exact continuousOn_const) ?_
        exact ContinuousOn.mul (by exact Complex.continuous_ofReal.continuousOn) (by exact continuousOn_const)
      exact ContinuousOn.mul (by exact this) (by exact this)
    · intro x xLoc
      apply pow_pos
      have temp : |(↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I).im| ≤
        ‖↑σ₂ + ↑x * (1 - ↑σ₂) - 3 * I‖₊ := by apply Complex.abs_im_le_norm
      rw[sub_im, add_im, mul_im, mul_im, I_re, I_im, sub_im, sub_re] at temp
      repeat rw[ofReal_re] at temp
      repeat rw[ofReal_im] at temp
      rw[reThree, imOne] at temp
      ring_nf at temp ⊢
      rw[abs_of_neg, neg_neg] at temp
      · have : (3 : NNReal) ≤ ‖↑σ₂ - ↑σ₂ * ↑x + (↑x - I * 3)‖₊ := by
          apply (NNReal.coe_le_coe).mp
          convert! (preTransparency := .instances) temp using 1; congr 2; ring
        have hp : (0 : NNReal) < ‖↑σ₂ - ↑σ₂ * ↑x + (↑x - I * 3)‖₊ :=
          lt_of_lt_of_le (by norm_num) this
        convert! (preTransparency := .instances) hp using 1; congr 2; ring
      · rw[neg_lt_zero]
        norm_num
  have CNonneg : 0 ≤ C := by
    unfold C
    apply mul_nonneg
    · exact mul_nonneg (by exact CPrimeNonneg) (by exact Dpos.le)
    · rw[inv_nonneg]
      norm_cast
      convert (preTransparency := .instances) sInfPos.le using 5
      norm_cast
  use CNonneg

  let Tlb : ℝ := max 4 (max (rexp A) (rexp (A / (1 - σ₂))))
  use Tlb

  have : 3 < Tlb := by
    unfold Tlb
    rw[lt_max_iff]
    refine Or.inl ?_
    norm_num
  use this

  intro X X_gt_three ε ε_pos ε_lt_one T T_gt_Tlb σ₁
  have σ₂_le_σ₁ : σ₂ ≤ σ₁ := by
    have logTlb_pos : 0 < Real.log Tlb := by
      rw[← Real.log_one]
      exact log_lt_log (by norm_num) (by linarith)
    have logTlb_nonneg : 0 ≤ Real.log Tlb := by exact le_of_lt (by exact logTlb_pos)
    have expr_nonneg : 0 ≤ A / (1 - σ₂) := by
      apply div_nonneg
      · linarith [hA.1]
      · rw[sub_nonneg]
        exact le_of_lt hσ₂.2
    have temp : σ₂ ≤ 1 - A / Real.log Tlb := by
      have : rexp (A / (1 - σ₂)) ≤ Tlb := by
        unfold Tlb
        apply le_max_of_le_right
        apply le_max_right
      rw[← Real.le_log_iff_exp_le] at this
      · rw[div_le_iff₀, mul_comm, ← div_le_iff₀] at this
        · linarith
        · exact logTlb_pos
        · rw[sub_pos]
          exact hσ₂.2
      · positivity
    have : 1 - A / Real.log Tlb ≤ 1 - A / Real.log T := by
      apply sub_le_sub (by rfl)
      apply div_le_div₀
      · exact le_of_lt (by exact hA.1)
      · rfl
      · exact logTlb_pos
      · apply log_le_log (by positivity)
        exact le_of_lt (by exact T_gt_Tlb)
    exact le_trans temp this
  have minσ₂σ₁ : min σ₂ σ₁ = σ₂ := by exact min_eq_left (by exact σ₂_le_σ₁)
  have maxσ₂σ₁ : max σ₂ σ₁ = σ₁ := by exact max_eq_right (by exact σ₂_le_σ₁)
  have σ₁_lt_one : σ₁ < 1 := by
    rw[← sub_zero 1]
    unfold σ₁
    apply sub_lt_sub_left
    apply div_pos (by exact hA.1)
    rw[← Real.log_one]
    exact log_lt_log (by norm_num) (by linarith)

  rw[norm_mul, ← one_mul C]
  have : 1 * C * X * X ^ (-A / Real.log T) / ε = 1 * (C * X * X ^ (-A / Real.log T) / ε) := by ring
  rw[this]
  apply mul_le_mul
  · rw[norm_div, norm_one]
    repeat rw[norm_mul]
    rw[Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg, Complex.norm_I, mul_one]
    have : 1 / (2 * π) < 1 / 6 := by
      rw[one_div_lt_one_div]
      · refine (div_lt_iff₀' ?_).mp ?_
        norm_num
        ring_nf
        refine gt_iff_lt.mpr ?_
        exact Real.pi_gt_three
      · positivity
      · norm_num
    apply le_of_lt
    exact lt_trans this (by norm_num)
    exact pi_nonneg
  · let f : ℝ → ℂ := fun σ ↦ (-ζ' (↑σ - 3 * I) / ζ (↑σ - 3 * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ - 3 * I) * ↑X ^ (↑σ - 3 * I))
    have temp : ‖∫ (σ : ℝ) in σ₂..σ₁, -ζ' (↑σ - 3 * I) / ζ (↑σ - 3 * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ - 3 * I) * ↑X ^ (↑σ - 3 * I)‖ ≤
      C * X * X ^ (-A / Real.log T) / ε * |σ₁ - σ₂| := by
      have : ∀ x ∈ Set.uIoc σ₂ σ₁, ‖f x‖ ≤ C * X * X ^ (-A / Real.log T) / ε := by
        intro x xInIoc
        let t : ℝ := (x - σ₂) / (1 - σ₂)
        have tInIcc : t ∈ Icc 0 1 := by
          unfold t
          constructor
          · apply div_nonneg
            · rw[sub_nonneg]
              unfold uIoc at xInIoc
              rw[minσ₂σ₁] at xInIoc
              exact le_of_lt (by exact xInIoc.1)
            · rw[sub_nonneg]
              apply le_of_lt (by exact hσ₂.2)
          · rw[div_le_one]
            · refine sub_le_sub ?_ (by rfl)
              unfold uIoc at xInIoc
              rw[maxσ₂σ₁] at xInIoc
              apply le_trans xInIoc.2
              exact le_of_lt (by exact σ₁_lt_one)
            · rw[sub_pos]
              exact hσ₂.2
        have tExpr : (↑σ₂ + t * (1 - ↑σ₂) - 3 * I) = (↑x - 3 * I) := by
          unfold t
          simp only [ofReal_div, ofReal_sub, ofReal_one, sub_left_inj]
          rw[div_mul_comm, div_self]
          · simp only [one_mul, add_sub_cancel]
          · refine sub_ne_zero_of_ne ?_
            apply Ne.symm
            rw[Complex.ofReal_ne_one]
            exact ne_of_lt (by exact hσ₂.2)
        unfold f
        simp only [Complex.norm_mul]
        have : C * X * X ^ (-A / Real.log T) / ε =
          (C / ε) * (X * X ^ (-A / Real.log T)) := by ring
        rw[this]
        have temp : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑x - 3 * I)‖ ≤
          C / ε := by
          unfold C
          rw[div_div]
          nth_rewrite 2 [div_eq_mul_inv]
          have temp : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ ≤ C' := by
            unfold C'
            have : ‖-ζ' (↑x - 3 * I) / ζ (↑x - 3 * I)‖ ∈
              (fun (t : ℝ) ↦ ↑‖-ζ' (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I) / ζ (↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I)‖₊) '' Icc 0 1 := by
              rw[Set.mem_image]
              use t
              constructor
              · exact tInIcc
              · rw[tExpr]
                rfl
            exact le_csSup (by exact bddAboveS) (by exact this)
          have : ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑x - 3 * I)‖ ≤
            D * ((sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1)) * ε)⁻¹ := by
            nth_rewrite 3 [mul_comm]
            let s : ℂ := x - 3 * I
            have : 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑x - 3 * I) =
              𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) s := by exact rfl
            rw[this]
            have temp : σ₂ ≤ s.re := by
              unfold s
              rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
              ring_nf
              apply le_of_lt
              unfold uIoc at xInIoc
              rw[minσ₂σ₁] at xInIoc
              exact xInIoc.1
            have : s.re ≤ 2 := by
              unfold s
              rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
              ring_nf
              have : x < 1 := by
                unfold uIoc at xInIoc
                rw[maxσ₂σ₁] at xInIoc
                exact lt_of_le_of_lt xInIoc.2 σ₁_lt_one
              linarith
            have temp : ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) s‖ ≤ D * (ε * ‖s‖ ^ 2)⁻¹ := by
              exact MellinSmooth1bBound σ₂ hσ₂.1 s temp this ε ε_pos ε_lt_one
            have : D * (ε * ‖s‖ ^ 2)⁻¹ ≤ D * (ε * ↑(sInf ((fun (t : ℝ) ↦ ‖↑σ₂ + ↑t * (1 - ↑σ₂) - 3 * I‖₊ ^ 2) '' Icc 0 1)))⁻¹ := by
              refine mul_le_mul (by rfl) ?_ ?_ (by exact le_of_lt (by exact Dpos))
              · rw[inv_le_inv₀]
                · apply mul_le_mul (by rfl)
                  · rw[NNReal.coe_sInf]
                    apply csInf_le
                    · apply NNReal.bddBelow_coe
                    · unfold s
                      rw[Set.mem_image]
                      let xNorm : NNReal := ‖x - 3 * I‖₊ ^ 2
                      use xNorm
                      constructor
                      · rw[Set.mem_image]
                        use t
                        exact ⟨tInIcc, by rw[tExpr]⟩
                      · rfl
                  · exact le_of_lt (by exact sInfPos)
                  · exact le_of_lt (by exact ε_pos)
                · apply mul_pos (ε_pos)
                  refine sq_pos_of_pos ?_
                  refine norm_pos_iff.mpr ?_
                  refine ne_zero_of_re_pos ?_
                  unfold s
                  rw[sub_re, mul_re, I_re, I_im, reThree, imThree, ofReal_re]
                  ring_nf
                  unfold uIoc at xInIoc
                  rw[minσ₂σ₁] at xInIoc
                  exact lt_trans hσ₂.1 xInIoc.1
                · exact mul_pos (ε_pos) (sInfPos)
              · rw[inv_nonneg]
                apply mul_nonneg (by exact le_of_lt (by exact ε_pos))
                exact sq_nonneg ‖s‖
            exact le_trans temp this
          rw[mul_assoc]
          apply mul_le_mul (by exact temp) (by exact this)
          · have this : 0 ≤ |(𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑x - 3 * I)).re| := by
              apply abs_nonneg
            exact le_trans this (by refine Complex.abs_re_le_norm ?_)
          · exact CPrimeNonneg
        have : ‖(X : ℂ) ^ (↑x - 3 * I)‖ ≤
          X * X ^ (-A / Real.log T) := by
          nth_rewrite 2 [← Real.rpow_one X]
          rw[← Real.rpow_add]
          · rw[Complex.norm_cpow_of_ne_zero]
            · rw[sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, reThree, imThree]
              ring_nf
              rw[Complex.norm_of_nonneg]
              · rw[Complex.arg_ofReal_of_nonneg]

                · have one_inv: (1⁻¹ : ℝ) = ( 1 : ℝ) := by norm_num
                  rw[zero_mul, neg_zero, Real.exp_zero, one_inv, mul_one]
                  refine rpow_le_rpow_of_exponent_le ?_ ?_
                  · linarith
                  · unfold uIoc at xInIoc
                    rw[maxσ₂σ₁] at xInIoc
                    unfold σ₁ at xInIoc
                    rw [←div_eq_mul_inv]
                    ring_nf at xInIoc ⊢
                    exact xInIoc.2
                · positivity
              · positivity
            · refine ne_zero_of_re_pos ?_
              rw[ofReal_re]
              positivity
          · positivity
        apply mul_le_mul
        · exact temp
        · exact this
        · rw[Complex.norm_cpow_eq_rpow_re_of_pos]
          · rw[sub_re, mul_re, ofReal_re, I_re, I_im, reThree, imThree]
            ring_nf
            apply Real.rpow_nonneg
            positivity
          · positivity
        · exact div_nonneg CNonneg (le_of_lt ε_pos)
      exact intervalIntegral.norm_integral_le_of_norm_le_const this
    have : C * X * X ^ (-A / Real.log T) / ε * |σ₁ - σ₂| ≤
      C * X * X ^ (-A / Real.log T) / ε := by
      have : |σ₁ - σ₂| ≤ 1 := by
        rw[abs_of_nonneg]
        · rw[← sub_zero 1]
          exact sub_le_sub σ₁_lt_one.le hσ₂.1.le
        · rw[sub_nonneg]
          exact σ₂_le_σ₁
      bound
    exact le_trans temp this
  simp only [norm_nonneg]
  norm_num

lemma I6I4 {SmoothingF : ℝ → ℝ} {ε X σ₁ σ₂ : ℝ} (Xpos : 0 < X) :
    I₆ SmoothingF ε X σ₁ σ₂ = -conj (I₄ SmoothingF ε X σ₁ σ₂) := by
  unfold I₆ I₄
  simp only [map_mul, map_div₀, conj_ofReal, conj_I, map_one, conj_ofNat]
  rw [← neg_mul]
  congr
  · ring
  · rw [← intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro σ hσ
    simp only
    rw[← smoothedChebyshevIntegrand_conj Xpos]
    simp [conj_ofNat]

lemma I6Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)

    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {A : ℝ}                                                                
    (hA : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T)
    ‖I₆ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T)) / ε := by
  obtain ⟨C, Cpos, Tlb, Tlb_gt, bound⟩ := I4Bound suppSmoothingF ContDiffSmoothingF h_logDeriv_holo hσ₂ hA
  refine ⟨C, Cpos, Tlb, Tlb_gt, fun X X_gt ε εpos ε_lt_one T T_gt ↦ ?_⟩
  specialize bound X X_gt εpos ε_lt_one T_gt
  intro σ₁
  rwa [I6I4 (by linarith), norm_neg, norm_conj]

lemma I5Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    : ∃ (C : ℝ) (_ : 0 < C),
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1),
    ‖I₅ SmoothingF ε X σ₂‖ ≤ C * X ^ σ₂ / ε := by

  unfold LogDerivZetaIsHoloSmall HolomorphicOn at h_logDeriv_holo
  let zeta'_zeta_on_line := fun (t : ℝ) ↦ ζ' (σ₂ + t * I) / ζ (σ₂ + t * I)

  have subst : {σ₂} ×ℂ uIcc (-3) 3 ⊆ (uIcc σ₂ 2 ×ℂ uIcc (-3) 3) \ {1} := by
    simp! only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le]
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, neg_le_self_iff,
      Nat.ofNat_nonneg, uIcc_of_le]
    intro z hyp_z
    simp only [mem_reProdIm, mem_singleton_iff, mem_Icc] at hyp_z
    simp only [Set.mem_sdiff, mem_reProdIm, mem_Icc, mem_singleton_iff]
    constructor
    · constructor
      · rw [hyp_z.1]
        apply left_mem_uIcc
      · exact hyp_z.2
    · push Not
      by_contra h
      rw [h] at hyp_z
      simp only [one_re, one_im, Left.neg_nonpos_iff, Nat.ofNat_nonneg, and_self, and_true] at hyp_z
      linarith [hσ₂.2]

  have zeta'_zeta_cont := (h_logDeriv_holo.mono subst).continuousOn

  have is_compact' : IsCompact ({σ₂} ×ℂ uIcc (-3) 3) := by
    refine IsCompact.reProdIm ?_ ?_
    · exact isCompact_singleton
    · exact isCompact_uIcc

  let ⟨zeta_bound, zeta_prop⟩ :=
    IsCompact.exists_bound_of_continuousOn (is_compact') zeta'_zeta_cont

  let ⟨M, ⟨M_is_pos, M_bounds_mellin_hard⟩⟩ :=
    MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF

  clear is_compact' zeta'_zeta_cont subst zeta'_zeta_on_line h_logDeriv_holo

  unfold I₅
  unfold SmoothedChebyshevIntegrand

  let mellin_prop : ∀ (t ε : ℝ),
  0 < ε → ε < 1 → ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)‖ ≤ M * (ε * ‖↑σ₂ + ↑t * I‖ ^ 2)⁻¹  :=
    fun (t : ℝ) ↦ (M_bounds_mellin_hard σ₂ (by linarith[hσ₂.1]) (σ₂ + t * I) (by simp only [add_re,
      ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, le_refl]) (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]; linarith[hσ₂.2]))

  simp only [mul_inv_rev] at mellin_prop

  let Const := 1 + (σ₂^2)⁻¹ * (abs zeta_bound) * M

  let C := |π|⁻¹ * 2⁻¹ * 6 * Const
  use C
  have C_pos : 0 < C := by positivity
  use C_pos

  have U : σ₂ ∈ Ioo 0 1 := by
    refine mem_Ioo.mpr ?_
    · constructor
      · linarith[hσ₂.1]
      · linarith[hσ₂.2]

  clear U    C_pos

  intros X X_gt ε ε_pos ε_lt_one

  have mellin_bound := fun (t : ℝ) ↦ mellin_prop t ε ε_pos ε_lt_one

  have U: 0 < σ₂^2 := by
    exact sq_pos_of_pos (by linarith[hσ₂.1])

  have easy_bound : ∀(t : ℝ), (‖↑σ₂ + ↑t * I‖^2)⁻¹ ≤ (σ₂^2)⁻¹ :=
    by
      intro t
      rw [inv_le_inv₀]
      rw [Complex.sq_norm]; rw [Complex.normSq_apply]; simp only [add_re, ofReal_re, mul_re, I_re,
        mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add]; ring_nf; simp only [le_add_iff_nonneg_right]; exact zpow_two_nonneg t
      rw [Complex.sq_norm, Complex.normSq_apply]; simp only [add_re, ofReal_re, mul_re, I_re,
        mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add]; ring_nf; positivity
      positivity

  have T1 : ∀(t : ℝ), t ∈ uIoc (-3) (3 : ℝ) → ‖-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I) * 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I) *
          (↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ ≤ Const * ε⁻¹ * X ^ σ₂ := by
    intro t hyp_t
    have Z := by
      calc
        ‖(-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)) * (𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)) *
        (↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ = ‖-ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)‖ * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by simp only [Complex.norm_mul,
          Complex.norm_div, norm_neg]
        _ ≤ ‖ζ' (↑σ₂ + ↑t * I) / ζ (↑σ₂ + ↑t * I)‖ * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖ := by simp only [Complex.norm_div,
          norm_neg, le_refl]
        _ ≤ zeta_bound *  ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  :=
          by
            have U := zeta_prop (↑σ₂ + t * I) (by
                simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le]
                simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
                  mul_one, sub_self, add_zero, mem_singleton_iff, add_im, mul_im, zero_add, mem_Icc]
                constructor
                · trivial
                · refine mem_Icc.mp ?_
                  · refine mem_Icc_of_Ioc ?_
                    · have T : (-3 : ℝ) ≤ 3 := by simp only [neg_le_self_iff, Nat.ofNat_nonneg]
                      rw [←Set.uIoc_of_le T]
                      exact hyp_t)
            simp only [Complex.norm_div] at U
            simp only [Complex.norm_div, ge_iff_le]
            linear_combination U * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖
        _ ≤ abs zeta_bound * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          have U : zeta_bound ≤ abs zeta_bound := by simp only [le_abs_self]
          linear_combination (U * ‖𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (↑σ₂ + ↑t * I)‖ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  )
        _ ≤ abs zeta_bound * M * ((‖↑σ₂ + ↑t * I‖ ^ 2)⁻¹ * ε⁻¹) * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          have U := mellin_bound t
          linear_combination (abs zeta_bound) * U * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖
        _ ≤ abs zeta_bound * M * (σ₂^2)⁻¹ * ε⁻¹ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖  := by
          have T : 0 ≤ abs zeta_bound * M := by positivity
          linear_combination (abs zeta_bound * M * easy_bound t * ε⁻¹ * ‖(↑X : ℂ) ^ (↑σ₂ + ↑t * I)‖)
        _ = abs zeta_bound * M * (σ₂^2)⁻¹ * ε⁻¹ * X ^ (σ₂) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos]
          simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            add_zero]
          positivity
        _ ≤ Const * ε⁻¹ * X ^ σ₂ := by
          unfold Const
          ring_nf
          simp only [inv_pow, le_add_iff_nonneg_right, inv_pos, mul_nonneg_iff_of_pos_left, ε_pos]
          positivity

    exact Z

  simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
    norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, ge_iff_le]
  have Z :=
    intervalIntegral.norm_integral_le_of_norm_le_const T1
  simp only [ge_iff_le]

  have S : |π|⁻¹ * 2⁻¹ * (Const * ε⁻¹ * X ^ σ₂ * |3 + 3|) = C * X ^ σ₂ / ε :=
    by
      unfold C
      ring_nf

  simp only [sub_neg_eq_add] at Z
  simp only [← S, ge_iff_le]
  linear_combination (|π|⁻¹ * 2⁻¹ * Z)


lemma MellinOfSmooth1cExplicit {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∃ ε₀ c : ℝ, 0 < ε₀ ∧ 0 < c ∧
    ∀ ε ∈ Ioo 0 ε₀, ‖𝓜 ((Smooth1 ν ε) ·) 1 - 1‖ ≤ c * ε := by
  have := MellinOfSmooth1c diffν suppν mass_one
  rw [Asymptotics.isBigO_iff'] at this
  rcases this with ⟨c, cpos, hc⟩
  unfold Filter.Eventually at hc
  rw [mem_nhdsGT_iff_exists_Ioo_subset] at hc
  rcases hc with ⟨ε₀, ε₀pos, h⟩
  refine ⟨ε₀, c, ε₀pos, cpos, fun ε hε ↦ ?_⟩
  specialize h hε
  rw [mem_ofPred_eq, id_eq, norm_of_nonneg hε.1.le] at h
  exact h

open _root_.Filter _root_.Topology

theorem Strong_PNT : ∃ c > 0,
    (ψ - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)) := by
  have ⟨ν, ContDiffν, ν_nonneg', ν_supp, ν_massOne'⟩ := SmoothExistence
  have ContDiff1ν : ContDiff ℝ 1 ν := by
    exact ContDiffν.of_le (by simp)
  have ν_nonneg : ∀ x > 0, 0 ≤ ν x := fun x _ ↦ ν_nonneg' x
  have ν_massOne : ∫ x in Ioi 0, ν x / x = 1 := by
    rwa [← integral_Ici_eq_integral_Ioi]
  clear ContDiffν ν_nonneg'  ν_massOne'
  obtain ⟨c_close, c_close_pos, h_close⟩ :=
    SmoothedChebyshevClose ContDiff1ν ν_supp ν_nonneg ν_massOne
  obtain ⟨ε_main, C_main, ε_main_pos, C_main_pos, h_main⟩  := MellinOfSmooth1cExplicit ContDiff1ν ν_supp ν_massOne
  obtain ⟨A, C_bnd, C_bnd_pos, A_in_Ioc, zeta_bnd, holo1⟩ := LogDerivZetaBoundedAndHolo
  obtain ⟨σ₂', σ₂'_lt_one, holo2'⟩ := LogDerivZetaHolcSmallT
  let σ₂ : ℝ := max σ₂' (1 / 2)
  have σ₂_pos : 0 < σ₂ := by bound
  have σ₂_lt_one : σ₂ < 1 := by bound
  have holo2 : HolomorphicOn (fun s ↦ ζ' s / ζ s) (uIcc σ₂ 2 ×ℂ uIcc (-3) 3 \ {1}) := by
    apply holo2'.mono
    intro s hs
    simp [mem_reProdIm] at hs ⊢
    refine ⟨?_, hs.2⟩
    refine ⟨?_, hs.1.2⟩
    rcases hs.1.1 with ⟨left, right⟩
    constructor
    · apply le_trans _ left
      apply min_le_min_right
      apply le_max_left
    · rw [max_eq_right (by linarith)] at right ⊢
      exact right

  clear holo2' σ₂'_lt_one

  obtain ⟨c₁, c₁pos, hc₁⟩ := I1Bound ν_supp ContDiff1ν ν_nonneg ν_massOne
  obtain ⟨c₂, c₂pos, hc₂⟩ := I2Bound ν_supp ContDiff1ν zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₃, c₃pos, hc₃⟩ := I3Bound ν_supp ContDiff1ν zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₅, c₅pos, hc₅⟩ := I5Bound ν_supp ContDiff1ν holo2  ⟨σ₂_pos, σ₂_lt_one⟩
  obtain ⟨c₇, c₇pos, hc₇⟩ := I7Bound ν_supp ContDiff1ν zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₈, c₈pos, hc₈⟩ := I8Bound ν_supp ContDiff1ν zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₉, c₉pos, hc₉⟩ := I9Bound ν_supp ContDiff1ν ν_nonneg ν_massOne

  obtain ⟨c₄, c₄pos, Tlb₄, Tlb₄bnd, hc₄⟩ := I4Bound ν_supp ContDiff1ν
    holo2 ⟨σ₂_pos, σ₂_lt_one⟩ A_in_Ioc

  obtain ⟨c₆, c₆pos, Tlb₆, Tlb₆bnd, hc₆⟩ := I6Bound ν_supp ContDiff1ν
    holo2 ⟨σ₂_pos, σ₂_lt_one⟩ A_in_Ioc

  let C' := c_close + C_main
  let C'' := c₁ + c₂ + c₈ + c₉
  let C''' := c₃ + c₄ + c₆ + c₇

  let c : ℝ := A ^ ((1 : ℝ) / 2) / 4
  have cpos : 0 < c := by
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, gt_iff_lt, mem_Ioo, and_imp,
      mem_Ioc, lt_sup_iff,
      inv_pos, Nat.ofNat_pos, or_true, sup_lt_iff, neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le,
      div_pos_iff_of_pos_right, σ₂, c]
    obtain ⟨left, right⟩ := A_in_Ioc
    positivity
  refine ⟨c, cpos, ?_⟩
  rw [Asymptotics.isBigO_iff]
  let C : ℝ := C' + C'' + C''' + c₅
  refine ⟨C, ?_⟩

  let c_εx : ℝ := A ^ ((1 : ℝ) / 2) / 2
  have c_εx_pos : 0 < c_εx := by
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, gt_iff_lt, mem_Ioo, and_imp,
      mem_Ioc, lt_sup_iff,
      inv_pos, Nat.ofNat_pos, or_true, sup_lt_iff, neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le,
      div_pos_iff_of_pos_right, σ₂, c, c_εx]
  let c_Tx : ℝ := A ^ ((1 : ℝ) / 2)
  have c_Tx_pos : 0 < c_Tx := by
    simp_all only [one_div, support_subset_iff, ne_eq, mem_Icc, gt_iff_lt, mem_Ioo, and_imp,
      mem_Ioc, lt_sup_iff,
      inv_pos, Nat.ofNat_pos, or_true, sup_lt_iff, neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le,
      div_pos_iff_of_pos_right, σ₂, c, c_εx, c_Tx]

  let εx := (fun x ↦ Real.exp (-c_εx * (Real.log x) ^ ((1 : ℝ) / 2)))
  let Tx := (fun x ↦ Real.exp (c_Tx * (Real.log x) ^ ((1 : ℝ) / 2)))

  have coeff_to_zero {B : ℝ} (B_le : B < 1) :
      Tendsto (fun x ↦ Real.log x ^ (B - 1)) atTop (𝓝 0) := by
    have B_minus_1_neg : B - 1 < 0 := by linarith
    rw [← Real.zero_rpow (ne_of_lt B_minus_1_neg)]
    rw [zero_rpow (ne_of_lt B_minus_1_neg)]
    have one_minus_B_pos : 0 < 1 - B := by linarith
    rw [show B - 1 = -(1 - B) by ring]
    have : ∀ᶠ (x : ℝ) in atTop, Real.log x ^ (-(1 - B)) = (Real.log x ^ ((1 - B)))⁻¹ := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      apply Real.rpow_neg
      exact Real.log_nonneg hx
    rw [tendsto_congr' this]
    apply tendsto_inv_atTop_zero.comp
    apply (tendsto_rpow_atTop one_minus_B_pos).comp
    exact tendsto_log_atTop

  have log_sub_log_pow_inf (c : ℝ) {B : ℝ} (B_le : B < 1) :
      Tendsto (fun (x : ℝ) ↦ Real.log x - c * Real.log x ^ B) atTop atTop := by
    have factor_form : ∀ x > 1, Real.log x - c * Real.log x ^ B =
        Real.log x * (1 - c * Real.log x ^ (B - 1)) := by
      intro x hx
      ring_nf
      congr! 1
      rw [mul_assoc, mul_comm (Real.log x), mul_assoc]
      congr! 1
      have log_pos : 0 < Real.log x := Real.log_pos hx
      rw [(by simp : Real.log x ^ (-1 + B) * Real.log x =
        Real.log x ^ (-1 + B) * (Real.log x) ^ (1 : ℝ))]
      rw [← Real.rpow_add log_pos]
      ring_nf
    have B_minus_1_neg : B - 1 < 0 := by linarith
    have coeff_to_one : Tendsto (fun x ↦ 1 - c * Real.log x ^ (B - 1)) atTop (𝓝 1) := by
      specialize coeff_to_zero B_le
      apply Tendsto.const_mul c at coeff_to_zero
      convert (preTransparency := .instances) (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ))).sub coeff_to_zero
      ring

    have eventually_pos : ∀ᶠ x in atTop, 0 < 1 - c * Real.log x ^ (B - 1) := by
      apply (tendsto_order.mp coeff_to_one).1
      norm_num

    have eventually_factored : ∀ᶠ x in atTop, Real.log x - c * Real.log x ^ B =
    Real.log x * (1 - c * Real.log x ^ (B - 1)) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact factor_form x hx

    rw [tendsto_congr' eventually_factored]
    apply Tendsto.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) tendsto_log_atTop  coeff_to_one

  have x_εx_eq (c B : ℝ) : ∀ᶠ (x : ℝ) in atTop, x * rexp (-c * Real.log x ^ B) =
        rexp (Real.log x - c * Real.log x ^ B) := by
    filter_upwards [eventually_gt_atTop 0] with x hx_pos
    conv =>
      enter [1, 1]
      rw [(Real.exp_log hx_pos).symm]
    rw [← Real.exp_add]
    ring_nf

  have x_ε_to_inf (c : ℝ) {B : ℝ} (B_le : B < 1) : Tendsto
    (fun x ↦ x * Real.exp (-c * (Real.log x) ^ B)) atTop atTop := by
    rw [tendsto_congr' (x_εx_eq c B)]
    exact tendsto_exp_atTop.comp (log_sub_log_pow_inf c B_le)

  have Tx_to_inf : Tendsto Tx atTop atTop := by
    unfold Tx
    apply tendsto_exp_atTop.comp
    apply Tendsto.pos_mul_atTop c_Tx_pos tendsto_const_nhds
    exact (tendsto_rpow_atTop (by norm_num : 0 < (1 : ℝ) / 2)).comp Real.tendsto_log_atTop

  have ex_to_zero : Tendsto εx atTop (𝓝 0) := by
    unfold εx
    apply Real.tendsto_exp_atBot.comp
    have this (x : ℝ) : -c_εx * Real.log x ^ ((1 : ℝ) / 2) = -(c_εx * Real.log x ^ ((1 : ℝ) / 2)) := by
      ring
    simp_rw [this]
    rw [tendsto_neg_atBot_iff]
    apply Tendsto.const_mul_atTop c_εx_pos
    apply (tendsto_rpow_atTop (by norm_num)).comp
    exact tendsto_log_atTop

  have eventually_εx_lt_one : ∀ᶠ (x : ℝ) in atTop, εx x < 1 := by
    apply (tendsto_order.mp ex_to_zero).2
    norm_num

  have eventually_2_lt : ∀ᶠ (x : ℝ) in atTop, 2 < x * εx x := by
    have := x_ε_to_inf c_εx (by norm_num : (1 : ℝ) / 2 < 1)
    exact this.eventually_gt_atTop 2

  have eventually_T_gt_3 : ∀ᶠ (x : ℝ) in atTop, 3 < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop 3

  have eventually_T_gt_Tlb₄ : ∀ᶠ (x : ℝ) in atTop, Tlb₄ < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop _
  have eventually_T_gt_Tlb₆ : ∀ᶠ (x : ℝ) in atTop, Tlb₆ < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop _

  have eventually_σ₂_lt_σ₁ : ∀ᶠ (x : ℝ) in atTop, σ₂ < 1 - A / (Real.log (Tx x)) := by
                                      
    apply (tendsto_order.mp ?_).1
    · exact σ₂_lt_one
    have := tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1)).comp
      (tendsto_log_atTop.comp Tx_to_inf))
    have := Tendsto.const_mul (b := A) this
    convert (preTransparency := .instances) (tendsto_const_nhds (x := (1 : ℝ))).sub this using 2
    · simp [Function.comp, div_eq_mul_inv]
    · simp

  have eventually_ε_lt_ε_main : ∀ᶠ (x : ℝ) in atTop, εx x < ε_main := by
    apply (tendsto_order.mp ex_to_zero).2
    assumption

  have event_logX_ge : ∀ᶠ (x : ℝ) in atTop, 1 ≤ Real.log x := by
    apply Real.tendsto_log_atTop.eventually_ge_atTop

  have event_1_aux_1 {const1 const2 : ℝ} (const1pos : 0 < const1) (const2pos : 0 < const2) :
    ∀ᶠ (x : ℝ) in atTop,
    rexp (-const1 * Real.log x ^ const2) * Real.log x ≤
    rexp 0 := by
      have := ((isLittleO_log_rpow_atTop const2pos).bound const1pos)
      have : ∀ᶠ (x : ℝ) in atTop, Real.log (Real.log x) ≤
          const1 * (Real.log x) ^ const2 := by
        have := tendsto_log_atTop.eventually this
        filter_upwards [this, eventually_gt_atTop 100] with x hx x_gt
        convert (preTransparency := .instances) hx using 1
        · rw [Real.norm_of_nonneg]
          apply Real.log_nonneg
          have : (1 : ℝ) = Real.log (rexp 1) := by
            exact Eq.symm (Real.log_exp 1)

          rw [this]
          apply Real.log_le_log
          · exact Real.exp_pos _
          · have := Real.exp_one_lt_d9
                       
            linarith
        · congr! 1
          rw [Real.norm_of_nonneg]
          apply Real.rpow_nonneg
          apply Real.log_nonneg
          linarith
      have loglogx :  ∀ᶠ (x : ℝ) in atTop,
          Real.log x = rexp (Real.log (Real.log x)) := by
        filter_upwards [eventually_gt_atTop 3] with x hx
        rw [Real.exp_log]
        apply Real.log_pos
        linarith
      filter_upwards [loglogx, this] with x loglogx hx
      conv =>
        enter [1, 2]
        rw [loglogx]
      rw [← Real.exp_add]
      apply Real.exp_monotone
      grw [hx]
      simp

  have event_1_aux {const1 const1' const2 : ℝ} (const1bnds : const1' < const1)
    (const2pos : 0 < const2) :
    ∀ᶠ (x : ℝ) in atTop,
    rexp (-const1 * Real.log x ^ const2) * Real.log x ≤
    rexp (-const1' * Real.log x ^ const2) := by
      have : 0 < const1 - const1' := by linarith
      filter_upwards [event_1_aux_1 this const2pos] with x hx
      have : rexp (-const1 * Real.log x ^ const2) * Real.log x
        = rexp (-(const1') * Real.log x ^ const2)
          * rexp (-(const1 - const1') * Real.log x ^ const2) * Real.log x := by
          congr! 1
          rw [← Real.exp_add]
          congr! 1
          ring
      rw [this]
      rw [mul_assoc]
      grw [hx]
      simp

  have event_1 : ∀ᶠ (x : ℝ) in atTop, C' * (εx x) * x * Real.log x ≤
      C' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / 2)) := by
    unfold c εx c_εx
    have : 0 < (A ^ ((1 : ℝ) / 2) / 4) := by
        positivity
    have const1bnd : (A ^ ((1 : ℝ) / 2) / 4) < (A ^ ((1 : ℝ) / 2) / 2) := by
        linarith
    have const2bnd : (0 : ℝ) < 1 / 2 := by norm_num
    have this (x : ℝ) :
      C' * rexp (-(A ^ ((1 : ℝ) / 2) / 2) * Real.log x ^ ((1 : ℝ) / 2)) * x * Real.log x =
      C' * x * (rexp (-(A ^ ((1 : ℝ) / 2) / 2) * Real.log x ^ ((1 : ℝ) / 2)) * Real.log x) := by ring
    simp_rw [this]
    filter_upwards [event_1_aux const1bnd const2bnd, eventually_gt_atTop 3] with x x_bnd x_gt
    grw [x_bnd]

  have event_2 : ∀ᶠ (x : ℝ) in atTop, C'' * x * Real.log x / (εx x * Tx x) ≤
      C'' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / 2)) := by
    unfold c εx c_εx Tx c_Tx
    set const2 : ℝ := 1 / 2
    have const2bnd : 0 < const2 := by norm_num
    set const1 := (A ^ const2 / 2)
    set const1' := (A ^ const2 / 4)
    have : 0 < A ^ const2 := by
      unfold const2
                                           
      apply Real.rpow_pos_of_pos
      exact A_in_Ioc.1
    have this (x : ℝ) : -(-const1 * Real.log x ^ const2 + A ^ const2 * Real.log x ^ const2) =
      -(A ^ const2 - const1) * Real.log x ^ const2 := by ring
    simp_rw [← Real.exp_add, div_eq_mul_inv, ← Real.exp_neg, this]
    have const1bnd : const1' < (A ^ const2 - const1) := by
      unfold const1' const1
      linarith
    filter_upwards [event_1_aux const1bnd const2bnd, eventually_gt_atTop 3] with x x_bnd x_gt
    rw [mul_assoc]
    conv =>
      enter [1, 2]
      rw [mul_comm]
    grw [x_bnd]

  have event_3_aux {const1 const1' const2 : ℝ} (const2_eq : const2 = 1 / 2)
    (const1_eq : const1 = (A ^ const2 / 2)) (const1'_eq : const1' = (A ^ const2 / 4)) :
    ∀ᶠ (x : ℝ) in atTop,
      x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)) ^ (1 : ℝ)) *
      rexp (-(-const1 * Real.log x ^ const2)) ≤
      rexp (-const1' * Real.log x ^ const2) := by
    have : ∀ᶠ (x : ℝ) in atTop, x = rexp (Real.log x) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [Real.exp_log hx]
    filter_upwards [this, eventually_gt_atTop 3] with x hx x_gt_3
    have logxpos : 0 < Real.log x := by apply Real.log_pos; linarith
    conv =>
      enter [1, 1, 1]
      rw [hx]
    rw [← Real.exp_mul]
    rw [Real.log_exp]
    rw [Real.mul_rpow]
    · have {y : ℝ} (ypos : 0 < y) : y / (y ^ const2) ^ (1 : ℝ) = y ^ const2 := by
        rw [← Real.rpow_mul ypos.le]
        rw [div_eq_mul_inv]
        rw [← Real.rpow_neg ypos.le]
        conv =>
          enter [1, 1]
          rw [← Real.rpow_one y]
        rw [← Real.rpow_add ypos]
        rw [(by linarith : 1 + -(const2 * 1) = const2)]
      rw [div_mul_eq_div_div]
      rw [neg_div]
      rw [this (A_in_Ioc.1)]

      rw [mul_div]
      conv =>
        enter [1, 1, 1, 1]
        rw [mul_comm]
      rw [← mul_div]

      rw [this (y := Real.log x) logxpos]

      rw [← Real.exp_add]
      apply Real.exp_monotone

      have : -A ^ const2 * Real.log x ^ const2 + -(-const1 * Real.log x ^ const2)
       = (-(A ^ const2 - const1) * Real.log x ^ const2) := by ring
      rw [this]

      gcongr

      rw [const1'_eq, const1_eq]
      have : 0 ≤ A ^ const2 := by
        apply Real.rpow_nonneg A_in_Ioc.1.le
      linarith
    · rw [const2_eq]
      rw [←Real.sqrt_eq_rpow]
      apply Real.sqrt_nonneg

    · apply Real.rpow_nonneg
      apply Real.log_nonneg
      linarith

  have event_3 : ∀ᶠ (x : ℝ) in atTop, C''' * x * x ^ (-A / Real.log (Tx x) ) / (εx x) ≤
      C''' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / 2)) := by
    unfold c Tx c_Tx εx c_εx
    set const2 : ℝ := 1 / 2
    have const2eq : const2 = 1 / 2 := by rfl
    have const2bnd : 0 < const2 := by norm_num
    set const1 := (A ^ const2 / 2)
    have const1eq : const1 = (A ^ const2 / 2) := by rfl
    set const1' := (A ^ const2 / 4)
    have const1'eq : const1' = (A ^ const2 / 4) := by rfl
    have A_pow_pos : 0 < A ^ const2 := by
      unfold const2
      apply Real.rpow_pos_of_pos
      exact A_in_Ioc.1

    conv =>
      enter [1, x, 1]
      rw [div_eq_mul_inv, ← Real.exp_neg]

    filter_upwards [event_3_aux const2eq const1eq const1'eq,
      eventually_gt_atTop 3] with x x_bnd x_gt

    have this (x : ℝ) : C''' * x * x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)))
        * rexp (-(-const1 * Real.log x ^ const2))
      = C''' * x * (x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)))
        * rexp (-(-const1 * Real.log x ^ const2))) := by
      ring
    rw [this]
    rw [rpow_one] at x_bnd
    grw [x_bnd]

  have event_4_aux4 {pow2 : ℝ} (pow2_neg : pow2 < 0) {c : ℝ} (cpos : 0 < c) (c' : ℝ) :
      Tendsto (fun x ↦ c' * Real.log x ^ pow2) atTop (𝓝 0) := by
    rw [← mul_zero c']
    apply Tendsto.const_mul
    have := tendsto_rpow_neg_atTop (y := -pow2) (by linarith)
    rw [neg_neg] at this
    apply this.comp
    exact Real.tendsto_log_atTop

  have event_4_aux3 {pow2 : ℝ} (pow2_neg : pow2 < 0) {c : ℝ} (cpos : 0 < c) (c' : ℝ) :
      ∀ᶠ (x : ℝ) in atTop, c' * (Real.log x) ^ pow2 < c := by
    apply (event_4_aux4 pow2_neg cpos c').eventually_lt_const
    exact cpos

  have event_4_aux2 {c1 : ℝ} (c1pos : 0 < c1) (c2 : ℝ) {pow1 : ℝ} (pow1_lt : pow1 < 1) :
      ∀ᶠ (x : ℝ) in atTop, 0 ≤ Real.log x * (c1 - c2 * (Real.log x) ^ (pow1 - 1)) := by
    filter_upwards [eventually_gt_atTop 3 , event_4_aux3 (by linarith : pow1 - 1 < 0)
      (by linarith : 0 < c1 / 2) c2] with x x_gt hx
    have : 0 ≤ Real.log x := by
      apply Real.log_nonneg
      linarith
    apply mul_nonneg this
    linarith

  have event_4_aux1 {const1 : ℝ} (const1_lt : const1 < 1) (const2 const3 : ℝ)
      {pow1 : ℝ} (pow1_lt : pow1 < 1) : ∀ᶠ (x : ℝ) in atTop,
      const1 * Real.log x + const2 * Real.log x ^ pow1
        ≤ Real.log x - const3 * Real.log x ^ pow1 := by
    filter_upwards [event_4_aux2 (by linarith : 0 < 1 - const1) (const2 + const3) pow1_lt,
      eventually_gt_atTop 3] with x hx x_gt
    rw [← sub_nonneg]
    have :
      Real.log x - const3 * Real.log x ^ pow1 - (const1 * Real.log x + const2 * Real.log x ^ pow1)
      = (1 - const1) * Real.log x - (const2 + const3) * Real.log x ^ pow1 := by ring
    rw [this]
    convert (preTransparency := .instances) hx using 1
    ring_nf
    congr! 1
    have : Real.log x * const2 * Real.log x ^ (-1 + pow1)
        = const2 * Real.log x ^ pow1 := by
      rw [mul_assoc, mul_comm, mul_assoc]
      congr! 1
      conv =>
        enter [1, 2]
        rw [← Real.rpow_one (Real.log x)]
      rw [← Real.rpow_add (Real.log_pos (by linarith))]
      ring_nf
    rw [this]
    have : Real.log x * const3 * Real.log x ^ (-1 + pow1)
        = const3 * Real.log x ^ pow1 := by
      rw [mul_assoc, mul_comm, mul_assoc]
      congr! 1
      conv =>
        enter [1, 2]
        rw [← Real.rpow_one (Real.log x)]
      rw [← Real.rpow_add (Real.log_pos (by linarith))]
      ring_nf
    rw [this]

  have event_4_aux : ∀ᶠ (x : ℝ) in atTop,
      c₅ * rexp (σ₂ * Real.log x + (A ^ ((1 : ℝ) / 2) / 2) * Real.log x ^ ((1 : ℝ) / 2)) ≤
      c₅ * rexp (Real.log x - (A ^ ((1 : ℝ) / 2) / 4) * Real.log x ^ ((1 : ℝ) / 2)) := by
    filter_upwards [eventually_gt_atTop 3, event_4_aux1 σ₂_lt_one (A ^ ((1 : ℝ) / 2) / 2)
      (A ^ ((1 : ℝ) / 2) / 4) (by norm_num : (1 : ℝ) / 2 < 1)] with x x_gt hx
    rw [mul_le_mul_iff_right₀ c₅pos]
    apply Real.exp_monotone
    convert (preTransparency := .instances) hx

  have event_4 : ∀ᶠ (x : ℝ) in atTop, c₅ * x ^ σ₂ / (εx x) ≤
      c₅ * x * rexp (-c * Real.log x ^ ((1 : ℝ) / 2)) := by
    unfold εx c_εx c
    filter_upwards [event_4_aux, eventually_gt_atTop 0] with x hx xpos
    convert (preTransparency := .instances) hx using 1
    · rw [← mul_div]
      congr! 1
      rw [div_eq_mul_inv, ← Real.exp_neg]
      conv =>
        enter [1, 1, 1]
        rw [← Real.exp_log xpos]
      rw [← exp_mul, ← Real.exp_add]
      ring_nf

    · rw [mul_assoc]
      congr! 1
      conv =>
        enter [1, 1]
        rw [← Real.exp_log xpos]
      rw [← Real.exp_add]
      ring_nf

  filter_upwards [eventually_gt_atTop 3, eventually_εx_lt_one, eventually_2_lt,
    eventually_T_gt_3, eventually_T_gt_Tlb₄, eventually_T_gt_Tlb₆,
      eventually_σ₂_lt_σ₁, eventually_ε_lt_ε_main, event_logX_ge, event_1, event_2,
      event_3, event_4] with X X_gt_3 ε_lt_one ε_X T_gt_3 T_gt_Tlb₄ T_gt_Tlb₆
      σ₂_lt_σ₁ ε_lt_ε_main logX_ge event_1 event_2 event_3 event_4

  clear eventually_εx_lt_one eventually_2_lt eventually_T_gt_3 eventually_T_gt_Tlb₄
    eventually_T_gt_Tlb₆ eventually_σ₂_lt_σ₁ eventually_ε_lt_ε_main event_logX_ge zeta_bnd

  let ε : ℝ := εx X
  have ε_pos : 0 < ε := by positivity
  specialize h_close X X_gt_3 ε ε_pos ε_lt_one ε_X
  let ψ_ε_of_X := SmoothedChebyshev ν ε X

  let T : ℝ := Tx X
  specialize holo1 T T_gt_3.le
  let σ₁ : ℝ := 1 - A / (Real.log T)
  have σ₁pos : 0 < σ₁ := by calc
    1 - A / (Real.log T) >= 1 - (1/2) / 1 := by
      gcongr
      · exact A_in_Ioc.2
      · apply (Real.le_log_iff_exp_le (by positivity)).mpr
        linarith[Real.exp_one_lt_d9]
    _ > 0 := by norm_num
  have σ₁_lt_one : σ₁ < 1 := by
    apply sub_lt_self
    apply div_pos A_in_Ioc.1
    bound

  rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at holo2

  have holo1_compat : HolomorphicOn (ζ' / ζ) (Icc σ₁ 2 ×ℂ Icc (-T) T \ {1}) := by
                                          
    simpa [σ₁, pow_one] using! holo1

  have holo2a : HolomorphicOn (SmoothedChebyshevIntegrand ν ε X)
      (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}) := by
    apply DifferentiableOn.mul
    · apply DifferentiableOn.mul
      · rw [(by ext; ring : (fun s ↦ -ζ' s / ζ s) = (fun s ↦ -(ζ' s / ζ s)))]
        apply DifferentiableOn.neg holo2
      · intro s hs
        apply DifferentiableAt.differentiableWithinAt
        apply Smooth1MellinDifferentiable ContDiff1ν ν_supp ⟨ε_pos, ε_lt_one⟩ ν_nonneg ν_massOne
        linarith[mem_reProdIm.mp hs.1 |>.1.1]
    · intro s hs
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.const_cpow (by fun_prop)
      left
      norm_cast
      linarith
  have ψ_ε_diff : ‖ψ_ε_of_X - 𝓜 ((Smooth1 ν ε) ·) 1 * X‖ ≤ ‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖
    + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖ + ‖I₅ ν ε X σ₂‖ + ‖I₆ ν ε X σ₁ σ₂‖ + ‖I₇ ν ε T X σ₁‖
    + ‖I₈ ν ε T X σ₁‖ + ‖I₉ ν ε X T‖ := by
    unfold ψ_ε_of_X
    rw [SmoothedChebyshevPull1 ε_pos ε_lt_one X X_gt_3 (T := T) (by linarith)
      σ₁pos σ₁_lt_one holo1_compat ν_supp ν_nonneg ν_massOne ContDiff1ν]
    rw [SmoothedChebyshevPull2 ε_pos ε_lt_one X X_gt_3 (T := T) (by linarith)
      σ₂_pos σ₁_lt_one σ₂_lt_σ₁ holo1_compat holo2a ν_supp ν_nonneg ν_massOne ContDiff1ν]
    ring_nf
    iterate 5
      apply le_trans (by apply norm_add_le)
      gcongr
    exact (norm_sub_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans
        (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)

  specialize h_main ε ⟨ε_pos, ε_lt_ε_main⟩
  have main : ‖𝓜 ((Smooth1 ν ε) ·) 1 * X - X‖ ≤ C_main * ε * X := by
    nth_rewrite 2 [← one_mul X]
    push_cast
    rw [← sub_mul, norm_mul]
    gcongr
    rw [norm_real, norm_of_nonneg (by linarith)]
  specialize hc₁ ε ε_pos ε_lt_one X X_gt_3 T_gt_3
  specialize hc₂ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₃ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₅ X X_gt_3 ε_pos ε_lt_one
  specialize hc₇ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₈ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₉ ε_pos ε_lt_one X X_gt_3 T_gt_3
  specialize hc₄ X X_gt_3 ε_pos ε_lt_one T_gt_Tlb₄
  specialize hc₆ X X_gt_3 ε_pos ε_lt_one T_gt_Tlb₆

  clear ν_nonneg ν_massOne ContDiff1ν ν_supp holo2

  have C'bnd : c_close * ε * X * Real.log X + C_main * ε * X ≤ C' * ε * X * Real.log X := by
    have : C_main * ε * X * 1 ≤ C_main * ε * X * Real.log X := by
      gcongr
    linarith

  have C''bnd : c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T) + c₈ * X / (ε * T)
    + c₉ * X * Real.log X / (ε * T) ≤ C'' * X * Real.log X / (ε * T) := by
    unfold C''
    rw [(by ring : (c₁ + c₂ + c₈ + c₉) * X * Real.log X / (ε * T)
      = c₁ * X * Real.log X / (ε * T) + c₂ * X * Real.log X / (ε * T)
        + c₈ * X * Real.log X / (ε * T) + c₉ * X * Real.log X / (ε * T))]
    have : c₂ * X / (ε * T) * 1 ≤ c₂ * X / (ε * T) * Real.log X := by
      gcongr
    have : c₂ * X / (ε * T) ≤ c₂ * X * Real.log X / (ε * T) := by
      ring_nf at this ⊢
      linarith
    grw [this]
    have : c₈ * X / (ε * T) * 1 ≤ c₈ * X / (ε * T) * Real.log X := by
      gcongr
    have : c₈ * X / (ε * T) ≤ c₈ * X * Real.log X / (ε * T) := by
      ring_nf at this ⊢
      linarith
    grw [this]

  have C'''bnd : c₃ * X * X ^ (-A / Real.log T) / ε
                    + c₄ * X * X ^ (-A / Real.log T) / ε
                    + c₆ * X * X ^ (-A / Real.log T) / ε
                    + c₇ * X * X ^ (-A / Real.log T) / ε
                  ≤ C''' * X * X ^ (-A / Real.log T) / ε := by
    apply le_of_eq
    ring

  calc
    _         = ‖(ψ X - ψ_ε_of_X) + (ψ_ε_of_X - X)‖ := by ring_nf; norm_cast
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖ψ_ε_of_X - X‖ := norm_add_le _ _
    _         = ‖ψ X - ψ_ε_of_X‖ + ‖(ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X)
                  + (𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X - X)‖ := by ring_nf
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X‖
                  + ‖𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X - X‖ := by
                    rw [add_assoc]
                    gcongr
                    apply norm_add_le
    _         = ‖ψ X - ψ_ε_of_X‖ + ‖𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X - X‖
                  + ‖ψ_ε_of_X - 𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X‖ := by ring
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖𝓜 (fun x ↦ (Smooth1 ν ε x)) 1 * X - X‖
                  + (‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖ + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖
                  + ‖I₅ ν ε X σ₂‖ + ‖I₆ ν ε X σ₁ σ₂‖ + ‖I₇ ν ε T X σ₁‖ + ‖I₈ ν ε T X σ₁‖
                  + ‖I₉ ν ε X T‖) := by gcongr
    _         ≤ c_close * ε * X * Real.log X + C_main * ε * X
                  + (c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T)
                  + c₃ * X * X ^ (-A / Real.log T) / ε
                  + c₄ * X * X ^ (-A / Real.log T) / ε
                  + c₅ * X ^ σ₂ / ε
                  + c₆ * X * X ^ (-A / Real.log T) / ε
                  + c₇ * X * X ^ (-A / Real.log T) / ε
                  + c₈ * X / (ε * T)
                  + c₉ * X * Real.log X / (ε * T)) := by
      gcongr
      convert! (preTransparency := .instances) h_close using 1
      rw [← norm_neg]
      congr
      ring

      change ‖I₂ ν ε (Tx X) X σ₁‖ ≤ c₂ * X / (ε * (Tx X))
      dsimp at hc₂
      dsimp [σ₁]
                                                    
      unfold sigma1Of at hc₂

      exact hc₂

    _         =  (c_close * ε * X * Real.log X + C_main * ε * X)
                  + ((c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T)
                  + c₈ * X / (ε * T)
                  + c₉ * X * Real.log X / (ε * T))
                  + (c₃ * X * X ^ (-A / Real.log T) / ε
                  + c₄ * X * X ^ (-A / Real.log T) / ε
                  + c₆ * X * X ^ (-A / Real.log T) / ε
                  + c₇ * X * X ^ (-A / Real.log T) / ε)
                  + c₅ * X ^ σ₂ / ε
                  ) := by ring
    _         ≤ C' * ε * X * Real.log X
                  + (C'' * X * Real.log X / (ε * T)
                  + C''' * X * X ^ (-A / Real.log T) / ε
                  + c₅ * X ^ σ₂ / ε
                  ) := by
      gcongr
    _        = C' * ε * X * Real.log X
                  + C'' * X * Real.log X / (ε * T)
                  + C''' * X * X ^ (-A / Real.log T) / ε
                  + c₅ * X ^ σ₂ / ε
                    := by ring
    _        ≤ C' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 2))
                  + C'' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 2))
                  + C''' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 2))
                  + c₅ * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 2))
                    := by
      gcongr
    _        = C * X * rexp (-c * Real.log X ^ ((1 : ℝ) / 2))
                    := by ring
    _        = _ := by
      rw [Real.norm_of_nonneg]
      · rw [← mul_assoc]
      · positivity

end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MertensClassical
namespace Erdos970


namespace Real

open _root_.Real _root_.Filter _root_.Asymptotics

theorem inv_log_eq_o_one : (fun x ↦ 1 / log x) =o[atTop] (fun _ ↦ (1:ℝ)) := by
    rw [isLittleO_one_iff]
    convert (preTransparency := .instances) tendsto_log_atTop.inv_tendsto_atTop using 1
    ext; simp


end Real

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology




end Issue1584

namespace Mertens

open _root_.Real _root_.Erdos970.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa


theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert (preTransparency := .instances) MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]


theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]



theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring







theorem sum_log_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p = log x + E₁p x := by
    grind

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]


lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp; linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all; linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! (preTransparency := .instances) HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (preTransparency := .instances) (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! (preTransparency := .instances) Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (preTransparency := .instances) (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! (preTransparency := .instances) summable_nat_add_iff 1|>.mpr this using 2
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq

theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! (preTransparency := .instances) summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast; ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl


theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]

theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply Real.log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun _ hx ↦ sum_log_prime_div_eq_log  hx⟩





lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa

private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! (preTransparency := .instances) this.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

attribute [fun_prop] measurable_from_top


private theorem integrable_E₁p_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁p x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁p.bounded
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)


private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! (preTransparency := .instances) MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! (preTransparency := .instances) HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! (preTransparency := .instances) tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp





section
open _root_.MeasureTheory _root_.Set

namespace LogZetaInteg



@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]






end LogZetaInteg
end











section
open _root_.MeasureTheory _root_.Set








end












theorem E₂p.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
  unfold E₂p
  rw [sum_filter, ← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have (n : ℕ) : (if Nat.Prime n then (1 : ℝ) / n else 0) = (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with h
    · have : log n ≠ 0 := by simp; grind [h.two_le]
      field
    · simp
  simp_rw [this]
  rw [sum_div_log_eq hx, sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [sum_log_prime_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, if Nat.Prime n then log ↑n / ↑n else 0) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁p t / (t * log t ^2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter, sum_log_prime_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold M
    calc
    _ = E₁p x / log x + (∫ (x : ℝ) in 2..x, E₁p x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁p t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁p_div_mul_log_sq (by rfl)) (integrable_E₁p_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁p_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
    have : 0 < log x := by apply Real.log_pos; linarith
    rw [E₂p.eq hx, abs_le']
    constructor
    · grw [E₁p.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≥ (- 2 - E₁) / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2 - E₁) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2 - E₁) hx)
            (integrable_E₁p_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := Real.log_pos this
          gcongr; exact E₁p.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2 - E₁) hx
      grw [this]
      grind
    grw [E₁p.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁p_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := Real.log_pos this
          gcongr; exact E₁p.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind

theorem E₂p.bound : E₂p =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6 + E₁, 2
    intro x hx
    convert (preTransparency := .instances) E₂p.abs_le hx using 1
    have : 0 < log x := by apply Real.log_pos; linarith
    grind [abs_of_pos this]

theorem E₂p.bound' : E₂p =o[atTop] (fun _ ↦ (1:ℝ)) := E₂p.bound.trans_isLittleO inv_log_eq_o_one





























end Mertens

end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.Jacobsthal.Primes.HighPrimeRemoval
namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosPrimeInputs.StrongChebyshev

open _root_.Filter _root_.Asymptotics
open scoped _root_.Topology


theorem errorScale_nonneg (c : ℝ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ errorScale c x := by
  exact mul_nonneg hx (Real.exp_pos _).le

theorem psi_eq_original {x : ℝ} (hx : 0 ≤ x) : Chebyshev.psi x = _root_.Erdos970.ChebyshevPsi x := by
  rw [Chebyshev.psi_eq_sum_Icc, _root_.Erdos970.ChebyshevPsi, Nat.floor_add_one hx,
    Nat.range_succ_eq_Icc_zero]

theorem sqrt_le_errorScale {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, Real.sqrt x ≤ errorScale c x := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((2 * c) ^ 2))] with x hx hlog
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hy0 := Real.sqrt_nonneg (Real.log x)
  have hy2 := Real.sq_sqrt hl0
  have hy : 2 * c ≤ Real.sqrt (Real.log x) := by nlinarith
  have hmul := mul_nonneg hy0 (sub_nonneg.mpr hy)
  have hlin : Real.log x * (1 / 2) ≤ Real.log x - c * Real.sqrt (Real.log x) := by
    nlinarith
  calc
    Real.sqrt x = Real.exp (Real.log x * (1 / 2)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]
    _ ≤ Real.exp (Real.log x - c * Real.sqrt (Real.log x)) := Real.exp_le_exp.mpr hlin
    _ = errorScale c x := by
      rw [Real.exp_sub, Real.exp_log hx0, errorScale, neg_mul, Real.exp_neg]
      ring

theorem sqrt_isBigO_errorScale {c : ℝ} (hc : 0 < c) :
    Real.sqrt =O[atTop] errorScale c := by
  apply IsBigO.of_bound 1
  filter_upwards [sqrt_le_errorScale hc, eventually_ge_atTop (0 : ℝ)] with x hb hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x),
    abs_of_nonneg (errorScale_nonneg c hx), one_mul] using hb

theorem psi_strong : ∃ c : ℝ, 0 < c ∧
    (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] errorScale c := by
  obtain ⟨c, hc, h⟩ := _root_.Erdos970.Strong_PNT
  refine ⟨c, hc, h.congr' ?_ ?_⟩
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [Pi.sub_apply, id_eq, psi_eq_original hx]
  · filter_upwards [] with x
    simp only [errorScale, Real.sqrt_eq_rpow]

theorem theta_strong : ∃ c : ℝ, 0 < c ∧
    (fun x : ℝ => Chebyshev.theta x - x) =O[atTop] errorScale c := by
  obtain ⟨c, hc, hpsi⟩ := psi_strong
  have hdiff := Chebyshev.isBigO_psi_sub_theta_sqrt.trans (sqrt_isBigO_errorScale hc)
  refine ⟨c, hc, (hpsi.sub hdiff).congr_left ?_⟩
  intro x
  simp only [Pi.sub_apply]
  ring

end ErdosPrimeInputs.StrongChebyshev



namespace ErdosPrimeInputs.PrimeAbel

open _root_.Set _root_.Finset _root_.MeasureTheory
open scoped _root_.Topology


theorem prefix_primeLogWeight (x : ℝ) :
    ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeLogWeight n = Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  rfl

theorem reciprocal_eq_weighted (a b : ℝ) :
    reciprocalPrimes a b = ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, invLogWeight n * primeLogWeight n := by
  rw [reciprocalPrimes, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hnl : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt))
    simp only [primeLogWeight, hp, ite_true, invLogWeight]
    field_simp
  · simp [primeLogWeight, hp]

theorem hasDerivAt_invLogWeight {t : ℝ} (ht : 1 < t) :
    HasDerivAt invLogWeight (-errorKernel t) t := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  convert! (preTransparency := .instances) ((hasDerivAt_id t).mul (Real.hasDerivAt_log ht0)).inv (mul_ne_zero ht0 hl0) using 1
  · ext x
    simp [invLogWeight, one_div]
  · dsimp [errorKernel]
    field_simp

theorem deriv_invLogWeight {t : ℝ} (ht : 1 < t) : deriv invLogWeight t = -errorKernel t :=
  (hasDerivAt_invLogWeight ht).deriv

theorem invLogWeight_continuousOn {a b : ℝ} (ha : 1 < a) :
    ContinuousOn invLogWeight (Set.Icc a b) := by
  intro t ht
  exact (hasDerivAt_invLogWeight (lt_of_lt_of_le ha ht.1)).continuousAt.continuousWithinAt

theorem deriv_invLogWeight_continuousOn {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (deriv invLogWeight) (Set.Icc a b) := by
  have hc : ContinuousOn (fun t => -errorKernel t) (Set.Icc a b) := by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht1)
    have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    apply ContinuousAt.continuousWithinAt
    unfold errorKernel
    fun_prop (disch := simp [ht0, hl0])
  apply hc.congr
  intro t ht
  exact deriv_invLogWeight (lt_of_lt_of_le ha ht.1)

theorem abel_theta {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    reciprocalPrimes a b = invLogWeight b * Chebyshev.theta b - invLogWeight a * Chebyshev.theta a -
      ∫ t in Set.Ioc a b, deriv invLogWeight t * Chebyshev.theta t := by
  rw [reciprocal_eq_weighted]
  have h := sum_mul_eq_sub_sub_integral_mul primeLogWeight (le_of_lt (lt_trans zero_lt_one ha)) hab
    (fun t ht => (hasDerivAt_invLogWeight (lt_of_lt_of_le ha ht.1)).differentiableAt)
    (deriv_invLogWeight_continuousOn ha).integrableOn_Icc
  simpa only [prefix_primeLogWeight] using h

theorem error_identity {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    reciprocalPrimes a b - (∫ t in Set.Ioc a b, invLogWeight t) =
      invLogWeight b * (Chebyshev.theta b - b) - invLogWeight a * (Chebyshev.theta a - a) -
      ∫ t in Set.Ioc a b, deriv invLogWeight t * (Chebyshev.theta t - t) := by
  have hf : IntegrableOn invLogWeight (Set.Ioc a b) :=
    (invLogWeight_continuousOn ha).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hfd : ContinuousOn (deriv invLogWeight) (Set.Icc a b) := deriv_invLogWeight_continuousOn ha
  have hlin : IntegrableOn (fun t => deriv invLogWeight t * t) (Set.Ioc a b) :=
    (hfd.mul continuousOn_id).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have htheta : IntegrableOn (fun t => deriv invLogWeight t * Chebyshev.theta t) (Set.Ioc a b) := by
    have h := integrableOn_mul_sum_Icc primeLogWeight (m := 0)
      (le_of_lt (lt_trans zero_lt_one ha)) hfd.integrableOn_Icc
    simp only [prefix_primeLogWeight] at h
    exact h.mono_set Set.Ioc_subset_Icc_self
  have hmain : (∫ t in Set.Ioc a b, deriv invLogWeight t * t) +
      (∫ t in Set.Ioc a b, invLogWeight t) = invLogWeight b * b - invLogWeight a * a := by
    rw [← integral_add hlin hf, ← intervalIntegral.integral_of_le hab]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      rw [deriv_invLogWeight (lt_of_lt_of_le ha ht.1)]
      simpa only [one_mul, mul_one] using!
        ((hasDerivAt_invLogWeight (lt_of_lt_of_le ha ht.1)).mul (hasDerivAt_id t))
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (hlin.add hf)
  have hrem : (∫ t in Set.Ioc a b, deriv invLogWeight t * (Chebyshev.theta t - t)) =
      (∫ t in Set.Ioc a b, deriv invLogWeight t * Chebyshev.theta t) -
      (∫ t in Set.Ioc a b, deriv invLogWeight t * t) := by
    simp_rw [mul_sub]
    exact integral_sub htheta hlin
  have hAbel := abel_theta ha hab
  linear_combination hAbel - hmain + hrem

theorem hasDerivAt_loglog {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun x => Real.log (Real.log x)) (invLogWeight t) t := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  convert! (preTransparency := .instances) (Real.hasDerivAt_log hl0).comp t (Real.hasDerivAt_log ht0) using 1
  simp [invLogWeight, one_div, mul_inv_rev, mul_comm]

theorem integral_invLogWeight {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in Set.Ioc a b, invLogWeight t) = Real.log (Real.log b) - Real.log (Real.log a) := by
  rw [← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact hasDerivAt_loglog (lt_of_lt_of_le ha ht.1)
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      ((invLogWeight_continuousOn ha).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)

end ErdosPrimeInputs.PrimeAbel



namespace ErdosPrimeInputs.PrimeEndpoints

open _root_.Finset
open _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeAbel







end ErdosPrimeInputs.PrimeEndpoints



namespace ErdosPrimeInputs.PrimeErrorDecay

open _root_.Set _root_.MeasureTheory _root_.Filter _root_.Asymptotics
open scoped _root_.Topology
open _root_.OAI.Erdos970.ErdosPrimeInputs.StrongChebyshev _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeAbel


lemma decay_pos (c t : ℝ) : 0 < decay c t := Real.exp_pos _

lemma decay_antitone {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 < a) (hab : a ≤ b) :
    decay c b ≤ decay c a := by
  apply Real.exp_le_exp.mpr
  have h := Real.sqrt_le_sqrt (Real.log_le_log ha hab)
  nlinarith

lemma hasDerivAt_decay {c t : ℝ} (ht : 1 < t) :
    HasDerivAt (decay c) (-(c / 2) * tailKernel c t) t := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have hs0 : Real.sqrt (Real.log t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Real.log_pos ht))
  have h := (((Real.hasDerivAt_sqrt hl0).comp t (Real.hasDerivAt_log ht0)).const_mul (-c)).exp
  convert! (preTransparency := .instances) h using 1
  dsimp [tailKernel, decay]
  field_simp

lemma tailKernel_continuousOn {c a b : ℝ} (ha : 1 < a) :
    ContinuousOn (tailKernel c) (Set.Icc a b) := by
  intro t ht
  have ht1 := lt_of_lt_of_le ha ht.1
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht1)
  have hs0 : Real.sqrt (Real.log t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Real.log_pos ht1))
  apply ContinuousAt.continuousWithinAt
  unfold tailKernel decay
  fun_prop (disch := simp [ht0, hs0])

lemma hasDerivAt_tailPrimitive {c t : ℝ} (hc : 0 < c) (ht : 1 < t) :
    HasDerivAt (fun t => -(2 / c) * decay c t) (tailKernel c t) t := by
  convert! (preTransparency := .instances) (hasDerivAt_decay ht).const_mul (-(2 / c)) using 1
  field_simp

lemma tailIntegral {c a b : ℝ} (hc : 0 < c) (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in Set.Ioc a b, tailKernel c t) = (2 / c) * (decay c a - decay c b) := by
  have h : (∫ t in a..b, tailKernel c t) = -(2 / c) * decay c b - (-(2 / c) * decay c a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact hasDerivAt_tailPrimitive hc (lt_of_lt_of_le ha ht.1)
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
        ((tailKernel_continuousOn ha).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
  rw [intervalIntegral.integral_of_le hab] at h
  rw [h]
  ring

lemma tailIntegral_le {c a b : ℝ} (hc : 0 < c) (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in Set.Ioc a b, tailKernel c t) ≤ (2 / c) * decay c a := by
  rw [tailIntegral hc ha hab]
  exact mul_le_mul_of_nonneg_left (sub_le_self _ (decay_pos c b).le) (by positivity)

lemma kernel_comparison {t : ℝ} (ht : 1 < t) (hl : 1 ≤ Real.log t) :
    errorKernel t * t ≤ 2 / (t * Real.sqrt (Real.log t)) := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hl0 : 0 < Real.log t := lt_of_lt_of_le zero_lt_one hl
  have hs0 : 0 < Real.sqrt (Real.log t) := Real.sqrt_pos.mpr hl0
  have hsle : Real.sqrt (Real.log t) ≤ Real.log t := by
    have hs2 := Real.sq_sqrt hl0.le
    have hs := Real.sqrt_nonneg (Real.log t)
    nlinarith
  calc
    errorKernel t * t = (Real.log t + 1) / (t * Real.log t ^ 2) := by
      unfold errorKernel
      field_simp
    _ ≤ (2 * Real.log t) / (t * Real.log t ^ 2) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = 2 / (t * Real.log t) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (mul_pos ht0 hs0)
      (mul_le_mul_of_nonneg_left hsle ht0.le)

lemma endpoint_error_bound {c C t : ℝ} (hC : 0 ≤ C) (ht : 1 < t) (hl : 1 ≤ Real.log t)
    (hθ : |Chebyshev.theta t - t| ≤ C * errorScale c t) :
    |invLogWeight t * (Chebyshev.theta t - t)| ≤ C * decay c t := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hl0 : 0 < Real.log t := lt_of_lt_of_le zero_lt_one hl
  rw [abs_mul, abs_of_nonneg (show 0 ≤ invLogWeight t by unfold invLogWeight; positivity)]
  calc
    _ ≤ invLogWeight t * (C * errorScale c t) :=
      mul_le_mul_of_nonneg_left hθ (by unfold invLogWeight; positivity)
    _ = C * decay c t / Real.log t := by unfold invLogWeight errorScale decay; field_simp
    _ ≤ C * decay c t := div_le_self (mul_nonneg hC (decay_pos c t).le) hl

lemma integral_error_bound {c C a b : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (ha : 1 < a) (hla : 1 ≤ Real.log a) (hab : a ≤ b)
    (hθ : ∀ t ∈ Set.Icc a b, |Chebyshev.theta t - t| ≤ C * errorScale c t) :
    |∫ t in Set.Ioc a b, deriv invLogWeight t * (Chebyshev.theta t - t)| ≤
      (4 * C / c) * decay c a := by
  have hi : IntegrableOn (fun t => (2 * C) * tailKernel c t) (Set.Ioc a b) :=
    ((tailKernel_continuousOn ha).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).const_mul _
  have hb : ∀ t ∈ Set.Ioc a b,
      ‖deriv invLogWeight t * (Chebyshev.theta t - t)‖ ≤ (2 * C) * tailKernel c t := by
    intro t ht
    have ht1 : 1 < t := lt_trans ha ht.1
    have ht0 : 0 < t := lt_trans zero_lt_one ht1
    have hlt : 1 ≤ Real.log t := le_trans hla (Real.log_le_log (lt_trans zero_lt_one ha) ht.1.le)
    have hk0 : 0 ≤ errorKernel t := by unfold errorKernel; positivity
    rw [deriv_invLogWeight ht1, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hk0]
    calc
      _ ≤ errorKernel t * (C * errorScale c t) := mul_le_mul_of_nonneg_left (hθ t ⟨ht.1.le, ht.2⟩) hk0
      _ = (errorKernel t * t) * (C * decay c t) := by unfold errorScale decay; ring
      _ ≤ (2 / (t * Real.sqrt (Real.log t))) * (C * decay c t) :=
        mul_le_mul_of_nonneg_right (kernel_comparison ht1 hlt) (mul_nonneg hC (decay_pos c t).le)
      _ = _ := by unfold tailKernel; ring
  have hint := norm_integral_le_of_norm_le hi (ae_restrict_of_forall_mem measurableSet_Ioc hb)
  rw [integral_const_mul] at hint
  calc
    _ ≤ (2 * C) * ∫ t in Set.Ioc a b, tailKernel c t := hint
    _ ≤ (2 * C) * ((2 / c) * decay c a) :=
      mul_le_mul_of_nonneg_left (tailIntegral_le hc ha hab) (by positivity)
    _ = _ := by ring

theorem uniform_prime_interval_error : ∃ c C a₀ : ℝ, 0 < c ∧ 0 < C ∧
    1 < a₀ ∧ 1 ≤ Real.log a₀ ∧
    ∀ a b : ℝ, a₀ ≤ a → a ≤ b →
      |reciprocalPrimes a b - (Real.log (Real.log b) - Real.log (Real.log a))| ≤ C * decay c a := by
  obtain ⟨c, hc, hstrong⟩ := theta_strong
  obtain ⟨K, hK, hbound⟩ := hstrong.exists_pos
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hbound.bound
  let a₀ := max x₀ (Real.exp 1)
  have ha₀ : 1 < a₀ := by
    have he : 1 < Real.exp 1 := by linarith [Real.exp_one_gt_two]
    exact lt_of_lt_of_le he (le_max_right x₀ (Real.exp 1))
  have hlog₀ : 1 ≤ Real.log a₀ := by
    have h := Real.log_le_log (Real.exp_pos 1) (le_max_right x₀ (Real.exp 1))
    simpa only [Real.log_exp] using h
  refine ⟨c, 2 * K + 4 * K / c, a₀, hc, by positivity, ha₀, hlog₀, ?_⟩
  intro a b haa hab
  have ha : 1 < a := lt_of_lt_of_le ha₀ haa
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have hla : 1 ≤ Real.log a := le_trans hlog₀ (Real.log_le_log (lt_trans zero_lt_one ha₀) haa)
  have hlb : 1 ≤ Real.log b := le_trans hla (Real.log_le_log (lt_trans zero_lt_one ha) hab)
  have hθ : ∀ t, a₀ ≤ t → |Chebyshev.theta t - t| ≤ K * errorScale c t := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt (lt_of_lt_of_le (lt_trans zero_lt_one ha₀) ht)
    have h := hx₀ t (le_trans (le_max_left _ _) ht)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (errorScale_nonneg c ht0)] using h
  rw [← integral_invLogWeight ha hab, error_identity ha hab]
  calc
    _ ≤ |invLogWeight b * (Chebyshev.theta b - b)| + |invLogWeight a * (Chebyshev.theta a - a)| +
        |∫ t in Set.Ioc a b, deriv invLogWeight t * (Chebyshev.theta t - t)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ K * decay c a + K * decay c a + (4 * K / c) * decay c a := by
      apply add_le_add
      · apply add_le_add
        · exact (endpoint_error_bound hK.le hb hlb (hθ b (le_trans haa hab))).trans
            (mul_le_mul_of_nonneg_left (decay_antitone hc.le (lt_trans zero_lt_one ha) hab) hK.le)
        · exact endpoint_error_bound hK.le ha hla (hθ a haa)
      · exact integral_error_bound hc hK.le ha hla hab (fun t ht => hθ t (le_trans haa ht.1))
    _ = _ := by ring

end ErdosPrimeInputs.PrimeErrorDecay



namespace ErdosPrimeInputs.HarmonicPrimeMeasure

open _root_.Filter _root_.Asymptotics
open scoped _root_.Topology
open _root_.OAI.Erdos970.ErdosPrimeInputs.StrongChebyshev _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeAbel _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay











end ErdosPrimeInputs.HarmonicPrimeMeasure



namespace ErdosPrimeInputs.MertensStrong

open _root_.Filter _root_.Asymptotics _root_.Finset
open scoped _root_.Topology
open _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeAbel _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay

lemma second_error_difference {a b : ℝ} (hab : a ≤ b) :
    _root_.Erdos970.Mertens.E₂p b - _root_.Erdos970.Mertens.E₂p a =
      reciprocalPrimes a b - (Real.log (Real.log b) - Real.log (Real.log a)) := by
  have h := Finset.sum_Ioc_consecutive
    (fun p : ℕ => if p.Prime then (p : ℝ)⁻¹ else 0) (Nat.zero_le ⌊a⌋₊) (Nat.floor_mono hab)
  unfold _root_.Erdos970.Mertens.E₂p reciprocalPrimes
  simp only [Finset.sum_filter, one_div] at *
  linarith

theorem second_error_strong : ∃ c C a₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < a₀ ∧
    ∀ a : ℝ, a₀ ≤ a → |_root_.Erdos970.Mertens.E₂p a| ≤ C * decay c a := by
  obtain ⟨c,C,a₀,hc,hC,ha₀,_,h⟩ := uniform_prime_interval_error
  refine ⟨c,C,a₀,hc,hC,ha₀,?_⟩
  intro a ha
  have ht : Tendsto _root_.Erdos970.Mertens.E₂p atTop (𝓝 0) := (isLittleO_one_iff ℝ).mp _root_.Erdos970.Mertens.E₂p.bound'
  have hb : |0 - _root_.Erdos970.Mertens.E₂p a| ≤ C * decay c a := by
    apply le_of_tendsto (ht.sub_const (_root_.Erdos970.Mertens.E₂p a)).abs
    filter_upwards [eventually_ge_atTop a] with b hab
    rw [second_error_difference hab]
    exact h a b ha hab
  simpa only [zero_sub, abs_neg] using hb






end ErdosPrimeInputs.MertensStrong



namespace ErdosInversePrimeBin
open _root_.Filter _root_.Asymptotics
open scoped _root_.Topology
open _root_.OAI.Erdos970.ErdosPrimeInputs.StrongChebyshev _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay




end ErdosInversePrimeBin



namespace ErdosPrimeInputs.PrimePrefixMass

open _root_.Finset
open _root_.OAI.Erdos970.ErdosPrimeInputs.StrongChebyshev _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeAbel _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay











end ErdosPrimeInputs.PrimePrefixMass



namespace ErdosPrimeInputs.PrimePrefixTail

open _root_.Finset







end ErdosPrimeInputs.PrimePrefixTail



namespace ErdosPrimeInputs.LongPrimePaths

open _root_.Filter _root_.Asymptotics
open scoped _root_.Topology
open _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeAbel _root_.OAI.Erdos970.ErdosPrimeInputs.PrimeErrorDecay



end ErdosPrimeInputs.LongPrimePaths



namespace ErdosPrimeInputs.HighPrimeGeometry

open _root_.Finset















end ErdosPrimeInputs.HighPrimeGeometry



namespace ErdosPrimeInputs.HighPrimeMass

open _root_.Finset





end ErdosPrimeInputs.HighPrimeMass



namespace ErdosPrimeInputs.HighPrimeRemoval

open _root_.Filter _root_.Asymptotics
open scoped _root_.Topology






end ErdosPrimeInputs.HighPrimeRemoval


end Erdos970

end OAI

end

theorem solution : type_of% @OAI.Erdos970.ErdosPrimeInputs.MertensStrong.second_error_strong := @OAI.Erdos970.ErdosPrimeInputs.MertensStrong.second_error_strong
