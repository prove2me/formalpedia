-- Prove2me | solution 1 for OAI.TwoPointCorrelations.modFive_smoothed_contour_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:02:31.114326+00:00
-- url     : https://prove2.me/submissions/0faa8d1f-c66b-4954-95f7-5a5765f051a8

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_modFive_nonprincipal_zero_free
import Theorems.Thm_OAI_TwoPointCorrelations_modFive_normalized_logderiv_norm

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveLFunctions
namespace OAI

/-! The three analytic functions needed for the fixed modulus-five input.

Every nonprincipal character modulo five is determined here by its value at
two, which is one of `-1`, `I`, or `-I`. Its L-function is an explicit finite
linear combination of the existing Hurwitz zeta functions. The final
identity identifies the corresponding Mangoldt Dirichlet series with the
negative logarithmic derivative on the half-plane of absolute convergence.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex _root_.HurwitzZeta
open scoped _root_.BigOperators _root_.Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveCharacterSums
namespace OAI

/-! Bounded character sums and the exact Abel integral for modulus five.

Periodicity and the vanishing sum over one period give an absolute bound
four, independent of the character and of the cutoff. This is the first
analytic estimate for the three nonprincipal L-functions.
-/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.Asymptotics _root_.MeasureTheory
open scoped _root_.BigOperators _root_.Classical _root_.Topology

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveCenterBounds
namespace OAI

/-! Uniform lower bounds on `Re s = 2`, from the exact Möbius inverse.
Together with the Abel upper bound these give the polynomial bound for a
normalized analytic disk used in the fixed-modulus zero-free argument.
-/

namespace TwoPointCorrelations

open _root_.Complex _root_.ArithmeticFunction
open scoped _root_.BigOperators _root_.Classical _root_.LSeries.notation _root_.ArithmeticFunction.Moebius


lemma modFiveInverseConstant_pos : 0 < modFiveInverseConstant := by
  unfold modFiveInverseConstant
  have : 0 ≤ ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (2 : ℂ) n‖ :=
    tsum_nonneg fun _ => norm_nonneg _
  linarith








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePositivity
namespace OAI

/-! The de la Vallée Poussin positivity inequality for modulus five.
The proof is termwise and uses the actual Mangoldt Dirichlet series.
It does not assume a zero-free region or a prime-number estimate.
-/

namespace TwoPointCorrelations

open _root_.Complex _root_.ArithmeticFunction
open scoped _root_.BigOperators _root_.Classical _root_.LSeries.notation









lemma modFive_twisted_series_logderiv (χ : DirichletCharacter ℂ 5)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (modFiveMangoldtTwist χ) s =
      -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact χ.LSeries_twist_vonMangoldt_eq hs


end TwoPointCorrelations

end OAI

end

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













lemma verticalIntegral_split_three (a b : ℝ)
    (hf : Integrable (fun t : ℝ ↦ f (σ + t * Complex.I))) :
    VerticalIntegral f σ =
      Complex.I • (∫ t in Iic a, f (σ + t * Complex.I)) + VIntegral f σ a b +
      Complex.I • ∫ t in Ici b, f (σ + t * Complex.I) := by
  simp_rw [VerticalIntegral, VIntegral, ← smul_add]
  congr
  rw [← integral_Iic_sub_Iic hf.restrict hf.restrict, add_sub_cancel,
    integral_Iic_eq_integral_Iio, integral_Iio_add_Ici hf.restrict hf.restrict]



theorem existsDifferentiableOn_of_bddAbove [CompleteSpace E]
    {s : Set ℂ} {c : ℂ} (hc : s ∈ nhds c)
    (hd : HolomorphicOn f (s \ {c}))
    (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    ∃ (g : ℂ → E),
      HolomorphicOn g s ∧ Set.EqOn f g (s \ {c}) :=
  ⟨Function.update f c (limUnder (𝓝[{c}ᶜ] c) f),
    differentiableOn_update_limUnder_of_bddAbove hc hd hb,
    fun z hz ↦ if h : z = c then (hz.2 h).elim
      else by simp [h]⟩

theorem HolomorphicOn.vanishesOnRectangle [CompleteSpace E]
    {U : Set ℂ} (f_holo : HolomorphicOn f U)
    (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w
    (f_holo.mono hU)






































lemma IsBigO_to_BddAbove {f : ℂ → ℂ} {p : ℂ}
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    ∃ U ∈ 𝓝 p, BddAbove (norm ∘ f '' (U \ {p})) := by
  simp only [isBigO_iff, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one] at f_near_p
  obtain ⟨c, hc⟩ := f_near_p
  dsimp [Filter.Eventually, nhdsWithin] at hc
  rw [mem_inf_principal'] at hc
  obtain ⟨U, hU, ⟨U_is_open, p_in_U⟩⟩ := mem_nhds_iff.mp hc
  use U
  constructor
  · exact IsOpen.mem_nhds U_is_open p_in_U
  · refine bddAbove_def.mpr ?_
    use c
    intro y hy
    simp only [Function.comp_apply, mem_image, Set.mem_sdiff, mem_singleton_iff] at hy
    obtain ⟨x, ⟨x_in_U, x_not_p⟩, fxy⟩ := hy
    rw [← fxy]
    simpa [x_not_p] using hU x_in_U






























end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveContourKernel
namespace OAI

/-! Elementary kernel estimates for the finite Perron rectangle.
The vertical side has an integrable quadratic majorant, while each
horizontal side has the explicit inverse-square height saving.
-/

namespace TwoPointCorrelations

open _root_.Complex


lemma modFive_perron_denominator_vertical {σ : ℝ} (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    (1 + t ^ 2) / 4 ≤
      ‖((σ : ℂ) + (t : ℂ) * Complex.I) *
        ((σ : ℂ) + (t : ℂ) * Complex.I + 1)‖ := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hnorm : ‖z‖ ≤ ‖z + 1‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [Complex.sq_norm, Complex.normSq_apply, z, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hnorm (norm_nonneg z)
  rw [← sq, Complex.sq_norm] at hm
  have hz : Complex.normSq z = σ ^ 2 + t ^ 2 := by
    simp [Complex.normSq_apply, z]
    ring
  rw [hz] at hm
  rw [norm_mul]
  change (1 + t ^ 2) / 4 ≤ ‖z‖ * ‖z + 1‖
  nlinarith [sq_nonneg t, sq_nonneg (σ - 1 / 2)]

lemma modFive_perron_denominator_horizontal (σ t : ℝ) :
    t ^ 2 ≤ ‖((σ : ℂ) + (t : ℂ) * Complex.I) *
      ((σ : ℂ) + (t : ℂ) * Complex.I + 1)‖ := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have h1 : |t| ≤ ‖z‖ := by simpa [z] using Complex.abs_im_le_norm z
  have h2 : |t| ≤ ‖z + 1‖ := by simpa [z] using Complex.abs_im_le_norm (z + 1)
  have hm := mul_le_mul h1 h2 (abs_nonneg t) (norm_nonneg z)
  simpa only [← sq, sq_abs, norm_mul] using hm

lemma modFive_perron_kernel_vertical {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (t : ℝ) :
    ‖modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      4 * x ^ σ / (1 + t ^ 2) := by
  have hp : 0 < (1 + t ^ 2) / 4 := by positivity
  have hd := modFive_perron_denominator_vertical hσ t
  rw [modFivePerronKernel, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
  exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) hp hd).trans_eq (by
    field_simp)

lemma modFive_perron_kernel_horizontal {x : ℝ} (hx : 0 < x) (σ : ℝ)
    {t : ℝ} (ht : t ≠ 0) :
    ‖modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ x ^ σ / t ^ 2 := by
  rw [modFivePerronKernel, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) (sq_pos_of_ne_zero ht)
    (modFive_perron_denominator_horizontal σ t)

lemma modFivePerronKernel_integrable {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) :
    MeasureTheory.Integrable (fun t : ℝ =>
      modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have h0 : ∀ t : ℝ, (σ : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro t ht
    have he := congrArg Complex.re ht
    norm_num at he
    linarith
  have h1 : ∀ t : ℝ, (σ : ℂ) + (t : ℂ) * Complex.I + 1 ≠ 0 := by
    intro t ht
    have he := congrArg Complex.re ht
    norm_num at he
    linarith
  have hcont : Continuous (fun t : ℝ =>
      modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    unfold modFivePerronKernel
    apply Continuous.div
    · exact (show Continuous (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) by
        fun_prop).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
    · fun_prop
    · intro t
      exact mul_ne_zero (h0 t) (h1 t)
  have hmaj : MeasureTheory.Integrable (fun t : ℝ => 4 * x ^ σ / (1 + t ^ 2)) := by
    simpa only [div_eq_mul_inv] using
      (integrable_inv_one_add_sq.const_mul (4 * x ^ σ))
  apply hmaj.mono' hcont.aestronglyMeasurable
  exact Filter.Eventually.of_forall (modFive_perron_kernel_vertical hx hσ)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePerronInversion
namespace OAI

/-! Triangular Perron inversion from Mellin inversion. The triangular
function is a difference of two elementary Mellin transforms. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Set _root_.MeasureTheory
open scoped _root_.Classical


lemma modFiveTriangle_hasMellin {s : ℂ} (hs : 0 < s.re) :
    HasMellin modFiveTriangle s (1 / (s * (s + 1))) := by
  have h0 := hasMellin_one_Ioc hs
  have h1 := hasMellin_cpow_Ioc (1 : ℂ) (s := s) (by simpa using (show 0 < s.re + 1 by linarith))
  have hd := hasMellin_sub h0.1 h1.1
  rw [h0.2, h1.2] at hd
  have he : ∀ t ∈ Ioi (0 : ℝ), modFiveTriangle t =
      (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t -
        (Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (1 : ℂ)) t := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · have hm : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, ht1⟩
      simp [modFiveTriangle, indicator_of_mem hm, max_eq_left (sub_nonneg.mpr ht1)]
    · have hm : t ∉ Ioc (0 : ℝ) 1 := fun h => ht1 h.2
      simp [modFiveTriangle, indicator_of_notMem hm, max_eq_right (by linarith : 1 - t ≤ 0)]
  have hc : MellinConvergent modFiveTriangle s := by
    exact hd.1.congr_fun (fun t ht => by rw [he t ht]) measurableSet_Ioi
  refine ⟨hc, ?_⟩
  calc
    mellin modFiveTriangle s = mellin
        (fun t => (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t -
          (Ioc (0 : ℝ) 1).indicator (fun u => (u : ℂ) ^ (1 : ℂ)) t) s := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [he t ht]
    _ = 1 / s - 1 / (s + 1) := hd.2
    _ = _ := by
      have hs0 : s ≠ 0 := by intro h; simp [h] at hs
      have hs1 : s + 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
      field_simp
      ring

lemma modFiveTriangle_continuous : Continuous modFiveTriangle := by
  unfold modFiveTriangle
  fun_prop

lemma modFiveTriangle_verticalIntegrable {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    Complex.VerticalIntegrable (mellin modFiveTriangle) σ := by
  have hi := modFivePerronKernel_integrable (by norm_num : (0 : ℝ) < 1) hσ
  apply hi.congr
  filter_upwards [] with t
  have hs : 0 < (((σ : ℂ) + (t : ℂ) * Complex.I)).re := by simpa using (show 0 < σ by linarith)
  rw [(modFiveTriangle_hasMellin hs).2]
  simp [modFivePerronKernel]

theorem modFivePerron_inversion {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) :
    Erdos970.VerticalIntegral' (modFivePerronKernel x) σ = modFiveTriangle (1 / x) := by
  have hsp : 0 < σ := by linarith
  have hi := mellinInv_mellin_eq σ modFiveTriangle (one_div_pos.mpr hx)
    (modFiveTriangle_hasMellin (by simpa using hsp)).1
    (modFiveTriangle_verticalIntegrable hσ) (modFiveTriangle_continuous.continuousAt)
  have hpoint : ∀ t : ℝ,
      ((1 / x : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) *
        mellin modFiveTriangle ((σ : ℂ) + (t : ℂ) * Complex.I) =
          modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    intro t
    rw [show (1 / x : ℝ) = x⁻¹ by ring, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg hx.le, Complex.cpow_neg, inv_inv,
      (modFiveTriangle_hasMellin (by simpa using hsp)).2]
    unfold modFivePerronKernel
    ring
  have hconst : (1 / (2 * (Real.pi : ℂ) * Complex.I)) * Complex.I =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [← hi]
  simp only [Erdos970.VerticalIntegral', Erdos970.VerticalIntegral, mellinInv,
    smul_eq_mul, ← mul_assoc, hconst]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => (hpoint t).symm

lemma modFivePerron_gt_one {x σ : ℝ} (hx : 1 < x) (hσ : 1 / 2 ≤ σ) :
    Erdos970.VerticalIntegral' (modFivePerronKernel x) σ = 1 - 1 / (x : ℂ) := by
  rw [modFivePerron_inversion (zero_lt_one.trans hx) hσ]
  have hi : (1 : ℝ) / x ≤ 1 := (div_le_one (zero_lt_one.trans hx)).mpr hx.le
  rw [modFiveTriangle, max_eq_left (sub_nonneg.mpr hi)]
  push_cast
  rfl

lemma modFivePerron_lt_one {x σ : ℝ} (hx : 0 < x) (hx1 : x < 1) (hσ : 1 / 2 ≤ σ) :
    Erdos970.VerticalIntegral' (modFivePerronKernel x) σ = 0 := by
  rw [modFivePerron_inversion hx hσ]
  have hi : (1 : ℝ) ≤ 1 / x := (le_div_iff₀ hx).mpr (by simpa using hx1.le)
  rw [modFiveTriangle, max_eq_right (sub_nonpos.mpr hi)]
  rfl

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePerronSeries
namespace OAI

/-! Absolute interchange for the triangular Perron kernel. The estimate is
proved for any absolutely convergent Dirichlet series and then specialized
to the actual twisted von Mangoldt series.
-/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory
open _root_.Erdos970 hiding B1 Bf Cf ChebyshevPsi DRinD1 DeltaSpike Err H_auxiliary I If_ext If_taxicab I₁ I₂ I₃ I₃₇ I₄ I₅ I₆ I₇ I₈ I₉ LogDerivZetaHasBound LogDerivZetaIsHoloSmall MellinConvolution MellinInverseTransform MellinTransform S_horiz S_max S_vert Smooth1 SmoothedChebyshev SmoothedChebyshevIntegrand ZetaZerosNearPoint aestronglyMeasurable_B1 ballDR e f_M lemKRinK1 lemKinDR lem_Contra_finiteKR lem_DRcompact lem_ballDR lem_bolzano_weierstrass lem_identity_infiniteKR lem_identity_theorem lem_identity_theoremKR lem_identity_theoremR lem_zeros_have_limit_point logDerivZeta riemannZeta0 sigma1Of zeroZ zerosetKfR zerosetKfRc zetaPartialSum
open scoped _root_.BigOperators

lemma modFivePerron_term_kernel (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0)
    {x : ℝ} (hx : 0 < x) (s : ℂ) :
    LSeries.term a s n * modFivePerronKernel x s =
      a n * modFivePerronKernel (x / (n : ℝ)) s := by
  rw [LSeries.term_of_ne_zero hn]
  unfold modFivePerronKernel
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hx.le (Nat.cast_nonneg n)]
  push_cast
  ring

lemma modFivePerron_term_integrable (a : ℕ → ℂ) (n : ℕ) {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 / 2 ≤ σ) :
    Integrable (fun t : ℝ => LSeries.term a ((σ : ℂ) + (t : ℂ) * Complex.I) n *
      modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp_rw [modFivePerron_term_kernel a hn hx]
    exact (modFivePerronKernel_integrable (div_pos hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)))
      hσ).const_mul (a n)

lemma modFivePerron_term_norm (a : ℕ → ℂ) (n : ℕ) (x σ t : ℝ) :
    ‖LSeries.term a ((σ : ℂ) + (t : ℂ) * Complex.I) n *
      modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ =
      ‖LSeries.term a (σ : ℂ) n‖ *
        ‖modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  rw [norm_mul]
  congr 1
  simp [LSeries.norm_term_eq]

theorem modFivePerron_series_interchange (a : ℕ → ℂ) {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (ha : LSeriesSummable a (σ : ℂ)) :
    VerticalIntegral' (fun s => LSeries a s * modFivePerronKernel x s) σ =
      ∑' n : ℕ, VerticalIntegral'
        (fun s => LSeries.term a s n * modFivePerronKernel x s) σ := by
  have hi := modFivePerronKernel_integrable hx hσ
  have hterms := fun n => modFivePerron_term_integrable a n hx hσ
  have hnorm : Summable (fun n : ℕ => ∫ t : ℝ,
      ‖LSeries.term a ((σ : ℂ) + (t : ℂ) * Complex.I) n *
        modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by
    simp_rw [modFivePerron_term_norm, integral_const_mul]
    exact ha.norm.mul_right _
  have he := integral_tsum_of_summable_integral_norm hterms hnorm
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
  rw [tsum_mul_left, tsum_mul_left, he]
  congr 2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun _ => tsum_mul_right.symm

lemma modFivePerron_term_value (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0)
    {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (hxn : x ≠ (n : ℝ)) :
    VerticalIntegral' (fun s => LSeries.term a s n * modFivePerronKernel x s) σ =
      if (n : ℝ) < x then a n * ((1 - (n : ℝ) / x : ℝ) : ℂ) else 0 := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hk : (fun s => LSeries.term a s n * modFivePerronKernel x s) =
      fun s => a n * modFivePerronKernel (x / (n : ℝ)) s := by
    funext s
    exact modFivePerron_term_kernel a hn hx s
  rw [hk]
  have hconst : VerticalIntegral' (fun s => a n * modFivePerronKernel (x / (n : ℝ)) s) σ =
      a n * VerticalIntegral' (modFivePerronKernel (x / (n : ℝ))) σ := by
    simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul, integral_const_mul]
    ring
  rw [hconst]
  by_cases hnlt : (n : ℝ) < x
  · rw [if_pos hnlt]
    have hp := modFivePerron_gt_one ((one_lt_div hn').mpr hnlt) hσ
    change VerticalIntegral' (modFivePerronKernel (x / (n : ℝ))) σ = _ at hp
    rw [hp]
    congr 1
    push_cast
    field_simp
  · rw [if_neg hnlt]
    have hlt : x < (n : ℝ) := lt_of_le_of_ne (le_of_not_gt hnlt) hxn
    have hp := modFivePerron_lt_one (div_pos hx hn') ((div_lt_one hn').mpr hlt) hσ
    change VerticalIntegral' (modFivePerronKernel (x / (n : ℝ))) σ = 0 at hp
    rw [hp, mul_zero]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveSmoothedPsi
namespace OAI

/-! The exact triangular Perron formula for the twisted von Mangoldt sums.
Nonintegral real cutoffs avoid the irrelevant boundary value of the scalar
kernel; later we use half-integral cutoffs to recover every integer sum.
-/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Finset
open _root_.Erdos970 hiding B1 Bf Cf ChebyshevPsi DRinD1 DeltaSpike Err H_auxiliary I If_ext If_taxicab I₁ I₂ I₃ I₃₇ I₄ I₅ I₆ I₇ I₈ I₉ LogDerivZetaHasBound LogDerivZetaIsHoloSmall MellinConvolution MellinInverseTransform MellinTransform S_horiz S_max S_vert Smooth1 SmoothedChebyshev SmoothedChebyshevIntegrand ZetaZerosNearPoint aestronglyMeasurable_B1 ballDR e f_M lemKRinK1 lemKinDR lem_Contra_finiteKR lem_DRcompact lem_ballDR lem_bolzano_weierstrass lem_identity_infiniteKR lem_identity_theorem lem_identity_theoremKR lem_identity_theoremR lem_zeros_have_limit_point logDerivZeta riemannZeta0 sigma1Of zeroZ zerosetKfR zerosetKfRc zetaPartialSum
open scoped _root_.BigOperators _root_.Classical


theorem modFivePerron_finite_sum (a : ℕ → ℂ) {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (ha : LSeriesSummable a (σ : ℂ))
    (hxnat : ∀ n : ℕ, x ≠ (n : ℝ)) :
    VerticalIntegral' (fun s => LSeries a s * modFivePerronKernel x s) σ =
      ∑ n ∈ Icc 1 ⌊x⌋₊, a n * ((1 - (n : ℝ) / x : ℝ) : ℂ) := by
  rw [modFivePerron_series_interchange a hx hσ ha]
  have hz : ∀ n ∉ Icc 1 ⌊x⌋₊,
      VerticalIntegral' (fun s => LSeries.term a s n * modFivePerronKernel x s) σ = 0 := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [VerticalIntegral', VerticalIntegral]
    · rw [modFivePerron_term_value a hn0 hx hσ (hxnat n)]
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hnlarge : ⌊x⌋₊ < n := by
        by_contra! h
        exact hn (mem_Icc.mpr ⟨hn1, h⟩)
      have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt hnlarge
      exact if_neg (not_lt.mpr hxn.le)
  rw [tsum_eq_sum hz]
  apply sum_congr rfl
  intro n hn
  have hn1 := (mem_Icc.mp hn).1
  have hn0 : n ≠ 0 := by omega
  rw [modFivePerron_term_value a hn0 hx hσ (hxnat n)]
  have hnle : (n : ℝ) ≤ x := (Nat.cast_le.mpr (mem_Icc.mp hn).2).trans (Nat.floor_le hx.le)
  have hnlt : (n : ℝ) < x := lt_of_le_of_ne hnle (hxnat n).symm
  rw [if_pos hnlt]

theorem modFiveSmoothedPsi_perron (χ : DirichletCharacter ℂ 5) {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 < σ) (hxnat : ∀ n : ℕ, x ≠ (n : ℝ)) :
    modFiveSmoothedPsi χ x =
      VerticalIntegral' (fun s =>
        (-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) *
          modFivePerronKernel x s) σ := by
  have ha : LSeriesSummable (modFiveMangoldtTwist χ) (σ : ℂ) :=
    χ.LSeriesSummable_twist_vonMangoldt (by simpa using hσ)
  rw [modFiveSmoothedPsi, ← modFivePerron_finite_sum (modFiveMangoldtTwist χ) hx
    (by linarith) ha hxnat]
  simp only [VerticalIntegral', VerticalIntegral]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with t
  rw [modFive_twisted_series_logderiv χ (by simpa using hσ)]

end TwoPointCorrelations

end OAI

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
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.ZetaBounds
namespace Erdos970


open _root_.Complex _root_.Topology _root_.Filter _root_.Interval _root_.Set _root_.Asymptotics






local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

theorem ResidueOfTendsTo {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (hU : U ∈ 𝓝 p)
    (hf : HolomorphicOn f (U \ {p}))
    {A : ℂ}
    (h_limit : Tendsto (fun s ↦ (s - p) * f s) (𝓝[≠] p) (𝓝 A)) :
    ∃ V ∈ 𝓝 p,
    BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (V \ {p})) := by
                                                                
  have h_event : ∀ᶠ s in 𝓝[≠] p, ‖(s - p) * f s - A‖ < 1 := by
    simp_rw [← dist_eq_norm_sub]
    exact h_limit.eventually (Metric.ball_mem_nhds _ (by norm_num))
  have h_event_nhds :
      ∀ᶠ s in 𝓝 p, s ≠ p → ‖(s - p) * f s - A‖ < 1 := by
    exact (eventually_nhdsWithin_iff).1 h_event
  rcases (eventually_nhds_iff.1 h_event_nhds) with ⟨V₀, hV₀_mem, hV₀_prop⟩
  have h_bound :
      ∀ s, s ∈ V₀ \ {p} → ‖(s - p) * f s‖ ≤ ‖A‖ + 1 := by
    intro s hs
    rcases hs with ⟨hV₀, hsne⟩
    calc ‖(s - p) * f s‖ = ‖((s - p) * f s - A) + A‖ := by
          ring_nf
        _ ≤ ‖(s - p) * f s - A‖ + ‖A‖ := norm_add_le ((s - p) * f s - A) A
        _ ≤ 1 + ‖A‖ := add_le_add_left (le_of_lt (hV₀_mem s hV₀ hsne)) ‖A‖
        _ = ‖A‖ + 1 := add_comm 1 ‖A‖
  have h_bdd :
      BddAbove (norm ∘ (fun s ↦ (s - p) * f s) '' (V₀ \ {p})) := by
    refine ⟨‖A‖ + 1, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact h_bound s hs
                                                                 
  set W : Set ℂ := V₀ ∩ U with hW_def
  have hW_mem : (W : Set ℂ) ∈ 𝓝 p := inter_mem (IsOpen.mem_nhds hV₀_prop.1 hV₀_prop.2) hU
  have h_subset_V₀ : (W \ {p}) ⊆ (V₀ \ {p}) := by
    intro z hz; exact ⟨hz.1.1, hz.2⟩
  have h_prod_holo : HolomorphicOn (fun z ↦ (z - p) * f z) (W \ {p}) := by
    have h_id : HolomorphicOn (fun z : ℂ ↦ z - p) (W \ {p}) :=
      Differentiable.differentiableOn (Differentiable.sub_const differentiable_fun_id p)
    have hfW : HolomorphicOn f (W \ {p}) := by
      apply hf.mono
      exact Set.sdiff_subset_sdiff_left inter_subset_right
    simpa using! h_id.mul hfW
  have h_bdd_W : BddAbove (norm ∘ (fun s ↦ (s - p) * f s) '' (W \ {p})) :=
    h_bdd.mono (image_mono h_subset_V₀)
                                                                    
  obtain ⟨g, hg_holo, hg_eq⟩ :=
    existsDifferentiableOn_of_bddAbove hW_mem h_prod_holo h_bdd_W
  have h_event_eq :
      (fun z ↦ g z) =ᶠ[𝓝[≠] p] fun z ↦ (z - p) * f z := by
    have hW_diff_mem : (W \ {p} : Set ℂ) ∈ 𝓝[≠] p :=
      sdiff_mem_nhdsWithin_compl hW_mem {p}
    exact (hg_eq.eventuallyEq_of_mem hW_diff_mem).symm
  have h_tendsto_gA : Tendsto g (𝓝[≠] p) (𝓝 A) :=
      h_limit.congr' (id (EventuallyEq.symm h_event_eq))
  have hpW : p ∈ W := by
    exact mem_of_mem_nhds hW_mem
  have h_cont_g : ContinuousAt g p := by
    apply (hg_holo.continuousOn.continuousWithinAt hpW).continuousAt hW_mem
  have h_tendsto_gp : Tendsto g (𝓝[≠] p) (𝓝 (g p)) :=
    h_cont_g.tendsto.mono_left inf_le_left
  have g_p_eq : g p = A :=
    tendsto_nhds_unique' (NormedField.nhdsNE_neBot p) h_tendsto_gp h_tendsto_gA
  let q : ℂ → ℂ := fun z ↦ (g z - A) / (z - p)
  have h_deriv : HasDerivAt g (deriv g p) p := by
    exact DifferentiableOn.hasDerivAt hg_holo hW_mem
  have h_q_limit : Tendsto q (𝓝[≠] p) (𝓝 (deriv g p)) := by
    rw [hasDerivAt_iff_tendsto_slope] at h_deriv
    unfold slope at h_deriv
    simp only [vsub_eq_sub, smul_eq_mul, inv_mul_eq_div, g_p_eq] at h_deriv
    exact h_deriv
  have h_event_q : ∀ᶠ z in 𝓝[≠] p, ‖q z - deriv g p‖ < 1 := by
    simp_rw [← dist_eq_norm_sub]
    exact h_q_limit.eventually (Metric.ball_mem_nhds _ (by norm_num))
  have h_event_q_nhds : ∀ᶠ z in 𝓝 p, z ≠ p → ‖q z - deriv g p‖ < 1 := by
    simpa using (eventually_nhdsWithin_iff).1 h_event_q
  rcases (eventually_nhds_iff.1 h_event_q_nhds) with
    ⟨V₁, hV₁_mem, hV₁_prop⟩
  have h_q_bound :
      ∀ z, z ∈ V₁ \ {p} → ‖q z‖ ≤ ‖deriv g p‖ + 1 := by
    intro z hz
    rcases hz with ⟨hV₁, hz_ne⟩
    calc ‖q z‖ = ‖(q z - deriv g p) + (deriv g p)‖ := by
          ring_nf
        _ ≤ ‖q z - deriv g p‖ + ‖deriv g p‖ := norm_add_le (q z - deriv g p) (deriv g p)
        _ ≤ 1 + ‖deriv g p‖  := add_le_add_left (le_of_lt (hV₁_mem z hV₁ hz_ne)) ‖deriv g p‖
        _ = ‖deriv g p‖ + 1 := add_comm 1 ‖deriv g p‖
                                                   
  have h_eq_diff :
      EqOn (fun z ↦ f z - A * (z - p)⁻¹) q (W \ {p}) := by
    intro z hz
    simp only
    have hz_ne : (z - p) ≠ 0 := sub_ne_zero.mpr hz.2
    have hgz : g z = (z - p) * f z := by
      exact id (EqOn.symm hg_eq) hz
    simp only [hgz, q]
    field_simp
  apply IsBigO_to_BddAbove
  rw [isBigO_iff]
  use ‖deriv g p‖ + 1
  apply eventually_nhdsWithin_iff.mpr
  filter_upwards [IsOpen.mem_nhds hV₁_prop.1 hV₁_prop.2, hW_mem] with z hV₁ hW z_ne_p
  specialize h_eq_diff ⟨ hW, z_ne_p⟩
  simp only [Pi.sub_apply, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary,
    mul_one] at h_eq_diff ⊢
  rw [h_eq_diff]
  exact h_q_bound _ ⟨hV₁, z_ne_p⟩



theorem riemannZetaResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (ζ - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by
  have zeta_holc : HolomorphicOn ζ (univ \ {1}) := by
    intro y hy
    exact DifferentiableAt.differentiableWithinAt <| differentiableAt_riemannZeta hy.2
  convert (preTransparency := .instances) ResidueOfTendsTo univ_mem zeta_holc riemannZeta_residue_one using 6
  simp

theorem deriv_eqOn_of_eqOn_punctured (f g : ℂ → ℂ) (U : Set ℂ) (p : ℂ)
    (hU_open : IsOpen U)
    (h_eq : EqOn f g (U \ {p})) :
    EqOn (deriv f) (deriv g) (U \ {p}) := by
  intro x hx
  apply EventuallyEq.deriv_eq
  filter_upwards [IsOpen.mem_nhds (hU_open.sdiff isClosed_singleton) hx] with t ht using h_eq ht

theorem analytic_deriv_bounded_near_point
    (f : ℂ → ℂ) {U : Set ℂ} {p : ℂ} (hU : IsOpen U) (hp : p ∈ U) (hf : HolomorphicOn f U) :
    (deriv f) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have U_in_filter : U ∈ 𝓝 p := by
    exact IsOpen.mem_nhds hU hp
  have T := (analyticOn_iff_differentiableOn hU).mpr hf
  have T2 : ContDiffOn ℂ 1 f U :=
      DifferentiableOn.contDiffOn hf hU
  have T3 : ContinuousOn (fun x ↦ ((deriv f) x)) U := by
    apply T2.continuousOn_deriv_of_isOpen hU (by simp)
  have T4 := T3.continuousAt U_in_filter
  have T5 : (deriv f) =O[𝓝 p] (1 : ℂ → ℂ) :=
    T4.norm.isBoundedUnder_le.isBigO_one ℂ
  exact Asymptotics.IsBigO.mono T5 inf_le_left

theorem derivative_const_plus_product {g : ℂ → ℂ} (A p x : ℂ) (hg : DifferentiableAt ℂ g x) :
    deriv ((fun _ ↦ A) + g * fun s ↦ s - p) x = deriv g x * (x - p) + g x := by
  rw [deriv_add (by fun_prop) (by fun_prop), deriv_const, deriv_mul hg (by fun_prop)]
  simp

lemma deriv_inv_sub {x p : ℂ} (hp : x ≠ p) :
  deriv (fun z => (z - p)⁻¹) x =  -((x - p) ^ 2)⁻¹ := by
  rw [deriv_fun_inv'' (by fun_prop) (by grind)]
  simp
  field

theorem deriv_f_minus_A_inv_sub_clean (f : ℂ → ℂ) (A x p : ℂ)
    (hf : DifferentiableAt ℂ f x) (hp : x ≠ p) :
    deriv (f  - (fun z ↦ A * (z - p)⁻¹)) x = deriv f x + A * ((x - p) ^ 2)⁻¹ := by
  have h1 : DifferentiableAt ℂ (fun z => (z - p)⁻¹) x := by
    fun_prop (disch := grind)
  rw [deriv_sub hf (h1.const_mul A), deriv_const_mul A h1, deriv_inv_sub hp]
  ring

theorem nonZeroOfBddAbove {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, IsOpen V ∧ ∀ s ∈ V \ {p}, f s ≠ 0 := by

  have h_decomp : ∀ s, f s = (f s - A * (s - p)⁻¹) + A * (s - p)⁻¹ := by
    intro s
    ring
                                      
  obtain ⟨M, hM⟩ := f_near_p

  have A_norm_pos : 0 < ‖A‖ := norm_pos_iff.mpr A_ne_zero
                                                                        
  let δ := ‖A‖ / (‖M‖ + 1)
  have δ_pos : 0 < δ := by
    refine div_pos A_norm_pos (add_pos_of_nonneg_of_pos (norm_nonneg M) one_pos)
                                                                            
  obtain ⟨V, hV_open, hV_mem, hV_sub⟩ : ∃ V, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∩ Metric.ball p δ := by
                                     
    obtain ⟨W, hW_sub, hW_open, hW_mem⟩ := mem_nhds_iff.mp U_in_nhds
    let V := W ∩ Metric.ball p δ
    have VNp : V ∈ 𝓝 p := (𝓝 p).inter_mem (IsOpen.mem_nhds hW_open hW_mem)
      (Metric.ball_mem_nhds p δ_pos)
    exact ⟨V, IsOpen.inter hW_open Metric.isOpen_ball, mem_of_mem_nhds VNp,
      inter_subset_inter_left _ hW_sub⟩
  use V, mem_nhds_iff.mpr ⟨V, subset_refl V, hV_open, hV_mem⟩, hV_open
                    
  intro s hs
  have hs_in_U : s ∈ U := hV_sub hs.1 |>.1
  have hs_near_p : dist s p < δ := hV_sub hs.1 |>.2
  have hs_ne_p : s ≠ p := hs.2
                                                              
  rw [h_decomp s]
                                 
  have bound_first : ‖f s - A * (s - p)⁻¹‖ ≤ M := by
    apply hM
    exact ⟨s, ⟨hs_in_U, hs_ne_p⟩, rfl⟩
                                      
  have large_second : ‖M‖ + 1 < ‖A * (s - p)⁻¹‖ := by
    rw [norm_mul, norm_inv, ← div_eq_mul_inv]
    rw [lt_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs_ne_p))]
    rw [mul_comm, ← lt_div_iff₀ (add_pos_of_nonneg_of_pos (norm_nonneg M) one_pos)]
    rw [dist_eq_norm_sub] at hs_near_p
    exact hs_near_p
                                                
  by_contra h_zero
                                                                  
  rw [add_eq_zero_iff_eq_neg] at h_zero
  rw [h_zero, norm_neg] at bound_first
                                    
  have : ‖M‖ + 1 < ‖M‖ := (lt_of_lt_of_le (lt_of_lt_of_le large_second bound_first)
    (Real.le_norm_self M))
  norm_num at this

theorem logDerivResidue' {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_is_open : IsOpen U)
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by

  have simpleHolo : HolomorphicOn (fun s ↦ A / (s - p)) (U \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx => by rw [sub_ne_zero]; exact hx
    · rintro s ⟨_, hs⟩ ; exact hs

  have f_minus_pole_is_holomorphic : HolomorphicOn (f - (fun s ↦ A * (s - p)⁻¹)) (U \ {p}) := by
    exact (DifferentiableOn.sub_iff_right holc).mpr simpleHolo

  let ⟨g, ⟨g_is_holomorphic, g_is_f_minus_pole⟩⟩ := existsDifferentiableOn_of_bddAbove
    U_in_nhds f_minus_pole_is_holomorphic f_near_p

  let h := (fun _ ↦ A) + g * (fun (s : ℂ) ↦ (s - p))

  have linear_is_holomorphic : HolomorphicOn (fun (s : ℂ ) ↦ (s - p)) U := by
    exact DifferentiableOn.sub_const differentiableOn_id p

  have h_is_holomorphic : HolomorphicOn h U := by
    have T := DifferentiableOn.mul g_is_holomorphic linear_is_holomorphic
    exact DifferentiableOn.const_add A T

  have h_continuous : ContinuousOn h U :=
    by exact DifferentiableOn.continuousOn h_is_holomorphic

  have deriv_h_identity : ∀x ∈ (U \ {p}), (deriv h) x = f x + (deriv f x) * (x - p) := by
    intro x x_in_u_not_p
    have x_in_u : x ∈ U := by exact Set.mem_of_mem_sdiff x_in_u_not_p
    have x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp x_in_u_not_p).2

    have weird : U ∈ 𝓝 x := by
      exact IsOpen.mem_nhds (U_is_open) (x_in_u)

    rw [derivative_const_plus_product, ← g_is_f_minus_pole x_in_u_not_p,
      ← deriv_eqOn_of_eqOn_punctured _ _ U p U_is_open g_is_f_minus_pole x_in_u_not_p,
      deriv_f_minus_A_inv_sub_clean]
    · simp only [Pi.sub_apply]
      have := sub_ne_zero_of_ne x_not_p
      field_simp
      ring
    · apply holc.differentiableAt
      exact Filter.inter_mem weird <| compl_singleton_mem_nhds x_not_p
    · exact x_not_p
    · exact g_is_holomorphic.differentiableAt weird
  have h_identity : ∀x ∈ (U \ {p}), h x = (f x) * (x - p)  := by
    intro x x_in_u_not_p
    have hyp_x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp x_in_u_not_p).2
    simp only [h, Pi.add_apply, Pi.mul_apply]
    rw [← g_is_f_minus_pole x_in_u_not_p]
    simp only [Pi.sub_apply]
    field [sub_ne_zero.mpr hyp_x_not_p]
  have log_deriv_f_plus_pole_equal_log_deriv_h :
      EqOn (deriv f * f⁻¹ + fun s ↦ (s - p)⁻¹) ((deriv h) * h⁻¹) (U \ {p}) := by
    simp only [Set.mem_sdiff, mem_singleton_iff, ne_eq, and_imp, Function.comp_apply, Pi.sub_apply,
      DifferentiableOn.sub_iff_right, differentiableOn_const, DifferentiableOn.fun_sub_iff_left,
      holc] at *
    intro x hyp_x
    have x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp hyp_x).2
    have x_in_u : x ∈ U := by exact Set.mem_of_mem_sdiff hyp_x
    simp only [Pi.add_apply, Pi.mul_apply, Pi.inv_apply]
    rw [deriv_h_identity _ x_in_u x_not_p, h_identity _ x_in_u x_not_p]

    field [sub_ne_zero.mpr x_not_p, non_zero x (x_in_u) x_not_p]
  have h_inv_bounded :
      h⁻¹ =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    have : ContinuousAt h⁻¹ p := by
      apply ContinuousOn.continuousAt h_continuous U_in_nhds |>.inv₀
      simp [h, A_ne_zero]
    exact Asymptotics.IsBigO.mono (this.norm.isBoundedUnder_le.isBigO_one ℂ) inf_le_left

  have h_deriv_bounded :
        (deriv h) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
          analytic_deriv_bounded_near_point h U_is_open
            (by exact mem_of_mem_nhds U_in_nhds) h_is_holomorphic

  have h_log_deriv_bounded :
    ((deriv h) * h⁻¹) =O[𝓝[≠] p] (1 : ℂ → ℂ)  := by
      have T := Asymptotics.IsBigO.mul h_deriv_bounded h_inv_bounded
      exact IsBigO.of_const_mul_right T

  have u_not_p_in_filter : U \ {p} ∈ 𝓝[≠] p := by
    exact sdiff_mem_nhdsWithin_compl U_in_nhds {p}
  have T := Set.EqOn.eventuallyEq_of_mem log_deriv_f_plus_pole_equal_log_deriv_h u_not_p_in_filter
  exact EventuallyEq.trans_isBigO T h_log_deriv_bounded

theorem logDerivResidue {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    by
      let ⟨U', ⟨a,b,c⟩⟩ := mem_nhds_iff.mp U_in_nhds
      have W : (U' \ {p}) ⊆ U' := by
        exact Set.sdiff_subset

      have T : (U' \ {p}) ⊆ (U \ {p}) := by
        exact Set.sdiff_subset_sdiff a (subset_refl _)

      refine logDerivResidue' b ?_ ?_ (IsOpen.mem_nhds b c) A_ne_zero ?_
      · intro x hyp_x
        exact non_zero x <| T hyp_x
      · exact DifferentiableOn.mono holc T
      · exact (f_near_p.mono (image_mono (Set.sdiff_subset_sdiff a (subset_refl _))))

lemma BddAbove_to_IsBigO {f : ℂ → ℂ} {p : ℂ}
    {U : Set ℂ} (hU : U ∈ 𝓝 p) (bdd : BddAbove (norm ∘ f '' (U \ {p}))) :
    f =O[𝓝[≠] p] (1 : ℂ → ℂ)  := by
  dsimp [BddAbove, upperBounds] at bdd
  rcases bdd with ⟨C, hC⟩

  have h : ∀ x ∈ U \ {p}, ‖f x‖ ≤ C := by
    intro x hx
    have fx_is_norm : ‖f x‖ ∈ norm ∘ f ''(U \ {p}) := by
      exact ⟨x, hx, rfl⟩
    exact hC fx_is_norm

  rw [Asymptotics.isBigO_iff]
  use C
  rw [eventually_nhdsWithin_iff]
  simp only [Set.mem_sdiff, mem_singleton_iff, and_imp, mem_compl_iff, Pi.one_apply, one_mem,
    CStarRing.norm_of_mem_unitary, mul_one] at h ⊢
  filter_upwards [hU] using h

theorem logDerivResidue'' {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, BddAbove (norm ∘ (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) '' (V \ {p})) := by
  apply IsBigO_to_BddAbove
  exact logDerivResidue non_zero holc U_in_nhds A_ne_zero f_near_p


theorem riemannZetaLogDerivResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (-(ζ' / ζ) - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by
  obtain ⟨U,U_in_nhds, hU⟩ := riemannZetaResidue
  have hU' : BddAbove (norm ∘ (ζ - fun s ↦ 1 * (s - 1)⁻¹) '' (U \ {1})) := by
    simp only [Function.comp_apply, Pi.sub_apply, one_mul] at hU ⊢
    exact hU
  obtain ⟨V,V_in_nhds, V_is_open, hV⟩ := nonZeroOfBddAbove U_in_nhds one_ne_zero hU'
  let W := V ∩ interior U
  have hW : ∀ s ∈ W \ {1}, ζ s ≠ 0 := by
    intro s hs
    have s_in_V_diff : s ∈ V \ {1} := ⟨hs.1.1, hs.2⟩
    exact hV s s_in_V_diff
  have ζ_holc: HolomorphicOn ζ (W \ {1}) := by
    intro y hy
    simp only [Set.mem_sdiff, mem_singleton_iff] at hy
    refine DifferentiableAt.differentiableWithinAt ?_
    apply differentiableAt_riemannZeta hy.2
  have W_in_nhds : W ∈ 𝓝 1 := by
    refine inter_mem V_in_nhds ?_
    exact interior_mem_nhds.mpr U_in_nhds
  have := logDerivResidue'' hW ζ_holc W_in_nhds one_ne_zero
  have HW : BddAbove (norm ∘ (ζ - fun s ↦ (s - 1)⁻¹) '' (W \ {1})) := by
    obtain ⟨c, hc⟩ := bddAbove_def.mp hU
    apply bddAbove_def.mpr
    use c
    rintro y ⟨x, x_in_W, fxy⟩
    apply hc
    exact ⟨x, ⟨interior_subset x_in_W.1.2, x_in_W.2⟩, fxy⟩
  simp only [one_mul] at this
  have aux: ∀ a, ‖-(deriv ζ a / ζ a) - (a - 1)⁻¹‖ = ‖(deriv ζ a / ζ a) + (a - 1)⁻¹‖ := by
    intro a
    calc ‖-(deriv ζ a / ζ a) - (a - 1)⁻¹‖
         = ‖-((deriv ζ a / ζ a) + (a - 1)⁻¹)‖ := by ring_nf
       _ = ‖(deriv ζ a / ζ a) + (a - 1)⁻¹‖ := by rw [norm_neg]
  simp only [Function.comp_apply, Pi.sub_apply] at hU
  simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply, aux]
  apply this HW

theorem riemannZetaLogDerivResidueBigO :
    (-ζ' / ζ - fun z ↦ (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
  obtain ⟨U, hU, bdd⟩ := riemannZetaLogDerivResidue
  convert (preTransparency := .instances) BddAbove_to_IsBigO hU bdd using 2
  rw [neg_div]


local notation (name := riemannzeta0) "ζ₀" => riemannZeta0

































































































































open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
                                                              



end Erdos970

end

section
-- module Solutions.OAIChowla.StrongPNT.Erdos970.PNT1_ComplexAnalysis
namespace Erdos970






lemma lem_exprule (n : ℕ) (hn : n ≥ 1) (α β : ℂ) : (n : ℂ) ^ (α + β) = (n : ℂ) ^ α * (n : ℂ) ^ β := by
  apply Complex.cpow_add
                              
  rw [Nat.cast_ne_zero]
                        
  rw [← Nat.one_le_iff_ne_zero]
  exact hn

lemma lem_realbw (b : ℝ) (w : ℂ) : (b * w).re = b * w.re := by
  exact Complex.re_ofReal_mul b w


lemma lem_Euler (a : ℝ) : Complex.exp (a * Complex.I) = Real.cos a + Real.sin a * Complex.I := by
  rw [Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma lem_Reecos (a : ℝ) : (Complex.exp (a * Complex.I)).re = Real.cos a := by
  rw [lem_Euler]
  rw [Complex.add_re]
  rw [Complex.ofReal_re]
  rw [Complex.re_ofReal_mul]
  rw [Complex.I_re]
  simp


lemma lem_coseven (a : ℝ) : Real.cos (-a) = Real.cos a := by
  exact Real.cos_neg a

lemma lem_coseveny (n : ℕ) (_hn : n ≥ 1) (y : ℝ) : Real.cos (-y * Real.log (n : ℝ)) = Real.cos (y * Real.log (n : ℝ)) := by
  rw [neg_mul]
  exact lem_coseven (y * Real.log (n : ℝ))

lemma lem_niyelog (n : ℕ) (hn : n ≥ 1) (y : ℝ) : (n : ℂ) ^ (-y * Complex.I) = Complex.exp (-y * Complex.I * Real.log (n : ℝ)) := by
                                
  have h1 : (n : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    rw [← Nat.one_le_iff_ne_zero]
    exact hn
                                                     
  rw [Complex.cpow_def_of_ne_zero h1]

  rw [← Complex.natCast_log]

  ring_nf

lemma lem_eacosalog (n : ℕ) (_hn : n ≥ 1) (y : ℝ) : (Complex.exp (-y * Complex.I * Real.log (n : ℝ))).re = Real.cos (-y * Real.log (n : ℝ)) := by
                                  
  let a := -y * Real.log (n : ℝ)
                                               
  have h : -y * Complex.I * Real.log (n : ℝ) = a * Complex.I := by
    simp [a, mul_assoc, mul_comm Complex.I]
  rw [h]
                     
  exact lem_Reecos a

lemma lem_eacosalog2 (n : ℕ) (hn : n ≥ 1) (y : ℝ) : ((n : ℂ) ^ (-y * Complex.I)).re = Real.cos (-y * Real.log (n : ℝ)) := by
  rw [lem_niyelog n hn y]
  exact lem_eacosalog n hn y

lemma lem_eacosalog3 (n : ℕ) (hn : n ≥ 1) (y : ℝ) : ((n : ℂ) ^ (-y * Complex.I)).re = Real.cos (y * Real.log (n : ℝ)) := by
  rw [lem_eacosalog2 n hn y]
  exact lem_coseveny n hn y




















































































































































































































open _root_.Complex _root_.MeasureTheory _root_.intervalIntegral
open scoped _root_.Interval











































open _root_.Filter _root_.Topology



















open _root_.Classical
                                                                                      

















open scoped _root_.Topology






























end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveZeroTerms
namespace OAI

/-! Transfer the normalized disk expansion back to the actual L-functions.
Every zero in the finite disk lies left of the line of evaluation, so its
logarithmic-derivative contribution has nonnegative real part.
-/

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.BigOperators _root_.Classical



lemma modFivePhysicalPoint_real (σ t : ℝ) :
    modFivePhysicalPoint t (modFiveRealDiskPoint σ) =
      (σ : ℂ) + Complex.I * (t : ℂ) := by
  unfold modFivePhysicalPoint modFiveRealDiskPoint
  push_cast
  ring

lemma modFiveNormalizedLFunction_deriv (χ : DirichletCharacter ℂ 5)
    (hχ : χ ≠ 1) (t : ℝ) (z : ℂ) :
    deriv (modFiveNormalizedLFunction χ t) z =
      (deriv (DirichletCharacter.LFunction χ) (modFivePhysicalPoint t z) * (3 / 2 : ℂ)) /
        DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (t : ℂ)) := by
  have ha : HasDerivAt (modFivePhysicalPoint t) (3 / 2 : ℂ) z := by
    exact (hasDerivAt_const_mul (3 / 2 : ℂ)).const_add
      ((2 : ℂ) + Complex.I * (t : ℂ))
  exact (((DirichletCharacter.differentiable_LFunction hχ _).hasDerivAt.comp z ha).div_const
    (DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (t : ℂ)))).deriv

lemma modFiveNormalized_logderiv_eq (χ : DirichletCharacter ℂ 5)
    (hχ : χ ≠ 1) (t : ℝ) (z : ℂ)
    (hn : DirichletCharacter.LFunction χ (modFivePhysicalPoint t z) ≠ 0) :
    deriv (modFiveNormalizedLFunction χ t) z / modFiveNormalizedLFunction χ t z =
      (3 / 2 : ℂ) *
        (deriv (DirichletCharacter.LFunction χ) (modFivePhysicalPoint t z) /
          DirichletCharacter.LFunction χ (modFivePhysicalPoint t z)) := by
  have hc : DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (t : ℂ)) ≠ 0 :=
    χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by norm_num)
  rw [modFiveNormalizedLFunction_deriv χ hχ]
  change (_ / _) / (DirichletCharacter.LFunction χ (modFivePhysicalPoint t z) / _) = _
  field_simp [hn, hc]

lemma modFiveNormalizedZeros_physical_zero (χ : DirichletCharacter ℂ 5)
    (t : ℝ) {ρ : ℂ} (hρ : ρ ∈ modFiveNormalizedZeros χ t) :
    DirichletCharacter.LFunction χ (modFivePhysicalPoint t ρ) = 0 := by
  have hzero : modFiveNormalizedLFunction χ t ρ = 0 := hρ.2
  have hc : DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (t : ℂ)) ≠ 0 :=
    χ.LFunction_ne_zero_of_one_le_re (Or.inr (by
      intro h; have := congrArg Complex.re h; norm_num at this)) (by norm_num)
  exact (div_eq_zero_iff.mp hzero).resolve_right hc









end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveLogGrowth
namespace OAI

/-! Uniform logarithmic growth constants for the fixed disk estimate.
These elementary inequalities expose a single constant independent of the
character and the height, ready for the zero-free-region calculation.
-/

namespace TwoPointCorrelations

lemma modFiveLogDerivativeConstant_pos : 0 < modFiveLogDerivativeConstant := by
  have hl : 0 < Real.log ((15 / 16 : ℝ) / (7 / 8)) := Real.log_pos (by norm_num)
  unfold modFiveLogDerivativeConstant
  positivity

lemma modFive_log_height_pos (t : ℝ) : 0 < Real.log (|t| + 2) :=
  Real.log_pos (by linarith [abs_nonneg t])


lemma modFive_log_disk_growth (t : ℝ) :
    Real.log (8 * modFiveInverseConstant * (|t| + 4)) ≤
      (Real.log (16 * modFiveInverseConstant) / Real.log 2 + 1) *
        Real.log (|t| + 2) := by
  have hK : 1 ≤ modFiveInverseConstant := by
    unfold modFiveInverseConstant
    exact le_add_of_nonneg_right (tsum_nonneg fun _ => norm_nonneg _)
  have hA : 0 < 16 * modFiveInverseConstant := by positivity
  have hlogA : 0 ≤ Real.log (16 * modFiveInverseConstant) :=
    Real.log_nonneg (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hratio : Real.log (16 * modFiveInverseConstant) ≤
      (Real.log (16 * modFiveInverseConstant) / Real.log 2) * Real.log (|t| + 2) := by
    calc
      _ = (Real.log (16 * modFiveInverseConstant) / Real.log 2) * Real.log 2 :=
        (div_mul_cancel₀ _ hlog2.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (div_nonneg hlogA hlog2.le)
  calc
    _ ≤ Real.log ((16 * modFiveInverseConstant) * (|t| + 2)) := by
      apply Real.log_le_log (by positivity)
      nlinarith [mul_nonneg modFiveInverseConstant_pos.le (abs_nonneg t)]
    _ = Real.log (16 * modFiveInverseConstant) + Real.log (|t| + 2) :=
      Real.log_mul hA.ne' (by positivity)
    _ ≤ _ := by nlinarith


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.StrongPNT.Erdos970.Z0
namespace Erdos970

open _root_.Complex _root_.Topology _root_.Filter _root_.Interval _root_.Set _root_.Asymptotics

local notation (name := riemannzeta1) "ζ" => riemannZeta
local notation (name := derivriemannzeta1) "ζ'" => deriv riemannZeta

lemma Z0bound_aux :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0)) (fun (delta : ℝ) => -(ζ' / ζ) ((1 : ℂ) + delta) - (1 / (delta : ℂ))) (fun _ => (1 : ℂ)) := by

  let F := fun s : ℂ => -(ζ' / ζ) s - (s - 1)⁻¹

  have h_F_bigO : F =O[𝓝[≠] 1] (1 : ℂ → ℂ) := by
    have h_fun_eq : F = (-ζ' / ζ - fun z ↦ (z - 1)⁻¹) := by
      ext s
      simp only [F, Pi.sub_apply, Pi.neg_apply, Pi.div_apply, neg_div]
    rw [h_fun_eq]
    exact riemannZetaLogDerivResidueBigO

  let u := fun (delta : ℝ) => (1 : ℂ) + delta
  have h_tendsto : Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (𝓝[≠] 1) := by

    apply tendsto_inf.mpr
    constructor
    ·                                     
      have h_cont : Continuous u := continuous_const.add continuous_ofReal
                                                             
      have h_tendsto_nhds : Tendsto u (𝓝 0) (𝓝 (u 0)) := h_cont.continuousAt.tendsto
                                                                     
      simp only [u, Complex.ofReal_zero, add_zero] at h_tendsto_nhds

      exact h_tendsto_nhds.mono_left nhdsWithin_le_nhds
    ·                                                  
                                                      
      simp
                                                  
      filter_upwards [self_mem_nhdsWithin] with delta h_delta_pos
      simp only [u]

      refine add_ne_left.mpr ?_
      rw [Complex.ofReal_ne_zero]
      exact ne_of_gt h_delta_pos

  have h_comp := h_F_bigO.comp_tendsto h_tendsto

  convert (preTransparency := .instances) h_comp using 1
  ext delta
                                                           
  simp only [F, u, Function.comp_apply, Pi.div_apply]
  rw [inv_eq_one_div]
  aesop
  all_goals rfl

lemma Z0bound :
    Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0)) (fun (delta : ℝ) => -logDerivZeta ((1 : ℂ) + delta) - (1 / (delta : ℂ))) (fun _ => (1 : ℂ)) := Z0bound_aux

end Erdos970

end

section
-- module Solutions.OAIChowla.StrongPNT.Erdos970.PNT4_ZeroFreeRegion
namespace Erdos970











































































lemma neg_logDeriv_zeta_eq_vonMangoldt_sum (s : ℂ) (hs : 1 < s.re) : -(deriv riemannZeta s / riemannZeta s) = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-s) := by
                                                                                     
  have h1 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

  have h2 : -deriv riemannZeta s / riemannZeta s = LSeries (fun n => ↑(ArithmeticFunction.vonMangoldt n)) s := h1.symm
                                                                                                                 
  have h3 : -(deriv riemannZeta s / riemannZeta s) = -deriv riemannZeta s / riemannZeta s := by ring
  rw [h3, h2]

  rw [LSeries]
  congr 1
  ext n
  rw [LSeries.term_def]
  split_ifs with h_zero
  ·                                
    simp [h_zero]
  ·                                                                     
    rw [div_eq_mul_inv, Complex.cpow_neg]

lemma zeta1zetaseries {s : ℂ} (hs : 1 < s.re) :
-logDerivZeta s = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-s) := by
  unfold logDerivZeta
                                                                                                                       
  exact neg_logDeriv_zeta_eq_vonMangoldt_sum s hs


lemma Zconverges1 (x y : ℝ) (hx : 1 < x) : riemannZeta (x + y * I) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_lt_re

  have h : (x + y * I).re = x := by
    rw [Complex.add_re, Complex.ofReal_re]
    simp [Complex.mul_re]
    right
    exact Complex.I_re
  rw [h]
  exact hx

lemma complex_re_of_real_add_imag (x y : ℝ) : (x + y * I).re = x := by
  simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im]
                                                                           
  right
  exact Complex.I_re

lemma vonMangoldt_LSeriesSummable (s : ℂ) (hs : 1 < s.re) : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
                                                                            
  exact ArithmeticFunction.LSeriesSummable_vonMangoldt hs

lemma summable_of_support_singleton {α : Type*} [SeminormedAddCommGroup α] (f : ℕ → α) (n₀ : ℕ) (h : ∀ n : ℕ, n ≠ n₀ → f n = 0) : Summable f := by
                                                     
  have h_finite_support : Set.Finite (Function.support f) := by
                                       
    have h_subset : Function.support f ⊆ {n₀} := by
      intro n hn

      by_contra h_ne
                                                 
      have h_zero : f n = 0 := h n h_ne
                                     
      simp [Function.mem_support] at hn
      exact hn h_zero
                                                                 
    exact Set.Finite.subset (Set.finite_singleton n₀) h_subset

  exact summable_of_hasFiniteSupport h_finite_support

lemma summable_of_summable_add_sub {α : Type*} [SeminormedAddCommGroup α] (f g h : ℕ → α) (h_eq : f = g + h) (hf : Summable f) (hh : Summable h) : Summable g := by

  have g_eq_f_sub_h : g = f - h := by
                                           
    rw [← sub_eq_iff_eq_add] at h_eq
    exact h_eq.symm

  rw [g_eq_f_sub_h]

  exact hf.sub hh

lemma LSeriesSummable_to_summable (f : ℕ → ℂ) (s : ℂ) (h : LSeriesSummable f s) : Summable (fun n => f n * (n : ℂ) ^ (-s)) := by
                                                          
  have h_term_summable : Summable (LSeries.term f s) := h

  have h_eq_nonzero : ∀ n : ℕ, n ≠ 0 → LSeries.term f s n = f n * (n : ℂ) ^ (-s) := by
    intro n hn
    rw [LSeries.term_of_ne_zero hn]
    rw [div_eq_mul_inv, Complex.cpow_neg]

  let diff := fun n => LSeries.term f s n - f n * (n : ℂ) ^ (-s)

  have h_diff_support : ∀ n : ℕ, n ≠ 0 → diff n = 0 := by
    intro n hn
    simp only [diff]
    rw [h_eq_nonzero n hn]
    simp

  have h_diff_summable : Summable diff := by
                                              
    apply summable_of_support_singleton diff 0 h_diff_support

  have h_rw : LSeries.term f s = (fun n => f n * (n : ℂ) ^ (-s)) + diff := by
    ext n
    simp only [diff, Pi.add_apply]
    ring

  exact summable_of_summable_add_sub (LSeries.term f s) (fun n => f n * (n : ℂ) ^ (-s)) diff h_rw h_term_summable h_diff_summable

lemma ReZconverges1 (x y : ℝ) (hx : 1 < x) :
Summable (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re) := by
                                                                                                
  have h_nonzero : riemannZeta (x + y * I) ≠ 0 := Zconverges1 x y hx

  have h_re_gt_one : 1 < (x + y * I).re := by
    rw [complex_re_of_real_add_imag]
    exact hx

  have h_L_summable : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) :=
    vonMangoldt_LSeriesSummable (x + y * I) h_re_gt_one

  have h_summable : Summable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))) :=
    LSeriesSummable_to_summable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) h_L_summable

  have h_hasSum : HasSum (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))) (∑' n, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))) :=
    h_summable.hasSum

  have h_hasSum_re : HasSum (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))).re) (∑' n, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))).re :=
    Complex.hasSum_re h_hasSum

  exact h_hasSum_re.summable


lemma lem_nxy (n : ℕ) (hn : n ≥ 1) (x y : ℝ) :
    Complex.cpow (n : ℂ) (-(x + y * I)) = Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I)) := by
                                              
  have h : -(x + y * I) = (-x : ℂ) + (-(y * I)) := by ring
  rw [h]
                                                         
  exact lem_exprule n hn (-x : ℂ) (-(y * I))









lemma complex_cpow_neg_real (n : ℕ) (x : ℝ) (_hn : n ≥ 1) : Complex.cpow (n : ℂ) ((-x) : ℂ) = Complex.ofReal ((n : ℝ) ^ (-x)) := by
                                     
  have h_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
                                   
  rw [Complex.cpow_eq_pow]
                                                   
  rw [Complex.ofReal_cpow h_nonneg (-x)]
                                          
  congr 1
                                 
  simp

lemma RealLambdaxy (n : ℕ) (x y : ℝ) (hn : n ≥ 1) (_hx : 1 < x) :
    ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))).re =
((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) * (Complex.cpow (n : ℂ) (-(y * I))).re := by
                                                              
  let b := ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-x)

  have h1 : (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) = (b : ℂ) := by
                                                
    have h_real_pow : Complex.cpow (n : ℂ) ((-x) : ℂ) = Complex.ofReal ((n : ℝ) ^ (-x)) := by
      exact complex_cpow_neg_real n x hn

    rw [h_real_pow]
    rw [← Complex.ofReal_mul]

  have h2 : (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I)) =
           ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ)) * Complex.cpow (n : ℂ) (-(y * I)) := by
    rw [mul_assoc]

  rw [h2, h1]

  exact lem_realbw b (Complex.cpow (n : ℂ) (-(y * I)))



lemma complex_vonMangoldt_real_part_eq (n : ℕ) (x y : ℝ) (hn : n ≥ 1) (hx : 1 < x) :
((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re =
(ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ)) := by
                                                   
  rw [lem_nxy n hn x y]

  rw [← mul_assoc]

  rw [RealLambdaxy n x y hn hx]

  have h_cpow : (Complex.cpow (n : ℂ) (-(y * I))).re = ((n : ℂ) ^ (-(y * I))).re := by
    rw [Complex.cpow_eq_pow]

  have h_I : -(y * I) = -y * Complex.I := by
    simp [I]

  rw [h_cpow, h_I]

  rw [lem_eacosalog3 n hn y]

lemma Rezetaseries_convergence (x y : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ))) := by
                                                                           
  have h1 : Summable (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re) :=
    ReZconverges1 x y hx

  have h2 : ∀ n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re =
                      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ)) := by
    intro n
    by_cases h : n = 0
    · simp [h]
    · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
      exact complex_vonMangoldt_real_part_eq n x y hn hx

  have h3 : (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re) =
            (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ))) :=
    funext h2
  rwa [← h3]


lemma lem_cost0 (n : ℕ) (_hn : n ≥ 1) (t : ℝ) (ht : t = 0) : Real.cos (t * Real.log (n : ℝ)) = 1 := by
  rw [ht]
  simp

lemma Rezetaseries0 (x : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) := by
                                              
  have h1 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (0 * Real.log (n : ℝ))) :=
    Rezetaseries_convergence x 0 hx
                                             
  convert (preTransparency := .instances) h1 using 1
  ext n
  by_cases h : n = 0
  · simp [h]
  · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    rw [lem_cost0 n hn 0 rfl]
    ring

lemma uniform_bound_Z0_complex : ∃ δ0 > 0, ∃ C0 ≥ 0, ∀ δ : ℝ, 0 < δ → δ < δ0 → ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C0 := by
                                             
  let f : ℝ → ℂ := fun δ => -logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))
                                           
  have hO := Z0bound
                                                                 
  rcases (Asymptotics.isBigO_iff).1 hO with ⟨c, hc⟩
  have h_event : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ‖f δ‖ ≤ c := by
                             
    have : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ‖f δ‖ ≤ c * ‖(1 : ℂ)‖ := hc
    refine this.mono ?_
    intro δ hδ
    have : ‖(1 : ℂ)‖ = (1 : ℝ) := by simp
    simpa [this] using hδ
                                                                                 
  rcases (Filter.eventually_iff_exists_mem).1 h_event with ⟨S, hS_in, hS_bound⟩
                                                                   
  rcases (mem_nhdsGT_iff_exists_Ioc_subset).1 hS_in with ⟨δ0, hδ0pos, hIoc_sub_S⟩
                                                                       
  refine ⟨δ0, hδ0pos, max c 0, le_max_right _ _, ?_⟩
  intro δ hδpos hδlt
                             
  have hδ_in_S : δ ∈ S := hIoc_sub_S ⟨hδpos, le_of_lt hδlt⟩
                                        
  have hnorm_le_c : ‖f δ‖ ≤ c := hS_bound δ hδ_in_S
                                                      
  exact le_trans hnorm_le_c (le_max_left _ _)


lemma tsum_nonneg_of_nonneg {f : ℕ → ℝ} (hnon : ∀ n, 0 ≤ f n) : 0 ≤ ∑' n, f n := by
  simpa using (tsum_nonneg hnon)

lemma vonMangoldt_rpow_nonneg (x : ℝ) : ∀ n, 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) := by
  intro n
  have h1 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have h2 : 0 ≤ (n : ℝ) ^ (-x) := by
    exact Real.rpow_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n) _
  simpa using mul_nonneg h1 h2


lemma norm_negLogDerivZeta_real_eq_abs_tsum_vonMangoldt (x : ℝ) (hx : 1 < x) :
  ‖-logDerivZeta (x : ℂ)‖ = |∑' n, ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x))| := by
                                                    
  have hx' : 1 < (x : ℂ).re := by simpa using hx
  have hseries := zeta1zetaseries (s := (x : ℂ)) hx'
                                                                                      
  let g : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
  have hterm : ∀ n : ℕ,
      (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ)) = (g n : ℂ) := by
    intro n
    by_cases h : n = 0
    ·                                               
      have hv0C : (ArithmeticFunction.vonMangoldt 0 : ℂ) = 0 := by
        simp
      have hv0R : (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 := by
        simp
      simp [g, h, hv0R]
    ·                                               
      have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
      have hcp : (n : ℂ) ^ (-(x : ℂ)) = Complex.ofReal ((n : ℝ) ^ (-x)) :=
        complex_cpow_neg_real n x hn
                                              
      have : (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ))
              = Complex.ofReal (ArithmeticFunction.vonMangoldt n) * Complex.ofReal ((n : ℝ) ^ (-x)) := by
        simp [hcp]
      simpa [g, Complex.ofReal_mul] using this
                                                          
  have hsum_eq : (∑' n, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ)))
                = ∑' n, (g n : ℂ) := by
                                             
    have hfun : (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ)))
                = (fun n => (g n : ℂ)) := funext hterm
    simp [hfun]
                                                                     
  have hsum_ofReal : (∑' n, (g n : ℂ)) = Complex.ofReal (∑' n, g n) := by
    simpa using (Complex.ofReal_tsum g).symm
                                                                                               
  have hval : -logDerivZeta (x : ℂ) = Complex.ofReal (∑' n, g n) := by
                                         
    simpa [hsum_eq, hsum_ofReal] using hseries
                                                                            
  calc
    ‖-logDerivZeta (x : ℂ)‖ = ‖Complex.ofReal (∑' n, g n)‖ := by simp [hval]
    _ = |∑' n, g n| := by
      exact (RCLike.norm_ofReal (K := ℂ) (∑' n, g n))

lemma tsum_le_of_nonneg_of_le {f g : ℕ → ℝ} (hf : Summable f) (hg : Summable g) (_hnonneg : ∀ n, 0 ≤ f n) (hle : ∀ n, f n ≤ g n) : (∑' n, f n) ≤ (∑' n, g n) := by
  classical
  exact Summable.tsum_le_tsum hle hf hg

lemma rpow_neg_antitone {a x y : ℝ} (ha : 1 ≤ a) (hxy : x ≥ y) : a ^ (-x) ≤ a ^ (-y) := by

  simpa using (Real.rpow_le_rpow_of_exponent_le ha (neg_le_neg hxy))


lemma bounded_on_compact_interval (a b : ℝ) (h0 : 0 < a) (_hle : a ≤ b) : ∃ Cmid ≥ 0, ∀ δ : ℝ, a ≤ δ → δ ≤ b → ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ Cmid := by
                                      
  let s : Set ℝ := Set.Icc a b
  let f : ℝ → ℂ := fun δ => -logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))

  let H : ℂ → ℂ := Function.update (fun z : ℂ => (z - 1) * riemannZeta z) 1 1

  have hH_diff : Differentiable ℂ H := by
    intro z
    rcases eq_or_ne z 1 with rfl | hz
    ·                                                 
      refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
      ·                                                           
        filter_upwards [self_mem_nhdsWithin] with t ht
        have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) t := by
          have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) t :=
            (differentiableAt_id.sub_const 1)
          have h2 : DifferentiableAt ℂ riemannZeta t :=
            (differentiableAt_riemannZeta ht)
          exact h1.mul h2
        apply DifferentiableAt.congr_of_eventuallyEq hdiff
        filter_upwards [eventually_ne_nhds ht] with u hu using by
          simp [H, Function.update_of_ne hu]
      ·                                                     
        simpa [H, continuousAt_update_same] using riemannZeta_residue_one
    ·                                                        
      have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) z := by
        have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) z := (differentiableAt_id.sub_const 1)
        have h2 : DifferentiableAt ℂ riemannZeta z := (differentiableAt_riemannZeta hz)
        exact h1.mul h2
      apply DifferentiableAt.congr_of_eventuallyEq hdiff
      filter_upwards [eventually_ne_nhds hz] with u hu using by
        simp [H, Function.update_of_ne hu]

  let G : ℂ → ℂ := fun z => - (deriv H z) / H z

  have h_eq_on_pos : ∀ ⦃δ : ℝ⦄, 0 < δ →
      (-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))) = G ((1 : ℂ) + δ) := by
    intro δ hδ
                    
    let z : ℂ := (1 : ℂ) + δ
    have hz_ne_one : z ≠ (1 : ℂ) := by
      intro h
      have hre : (1 + δ : ℝ) = 1 := by
        simpa [z, Complex.add_re, Complex.ofReal_re] using congrArg Complex.re h
      have : δ = 0 := by linarith
      exact (ne_of_gt hδ) this
    have hzeta_ne : riemannZeta z ≠ 0 := by
      have : 1 < z.re := by simpa [z, Complex.add_re, Complex.ofReal_re] using by linarith
      exact riemannZeta_ne_zero_of_one_le_re (le_of_lt this)

    have h_id_deriv : deriv (fun u : ℂ => u - 1) z = 1 := by
      exact ((hasDerivAt_id z).sub_const 1).deriv
    have h_log_id : logDeriv (fun u : ℂ => u - 1) z = 1 / (z - 1) := by
      simp [logDeriv_apply, h_id_deriv]
    have hz1 : z - 1 ≠ 0 := by simpa using sub_ne_zero.mpr hz_ne_one
    have hζ : riemannZeta z ≠ 0 := hzeta_ne

    have h_deriv_mul : deriv (fun u : ℂ => (u - 1) * riemannZeta u) z
          = riemannZeta z + (z - 1) * deriv riemannZeta z := by
      have h1 : HasDerivAt (fun u : ℂ => u - 1) 1 z := (hasDerivAt_id z).sub_const 1
      have h2 : HasDerivAt riemannZeta (deriv riemannZeta z) z :=
        (differentiableAt_riemannZeta hz_ne_one).hasDerivAt
      simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using! (h1.mul h2).deriv

    have h_prodLog :
        logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z =
          logDeriv (fun u : ℂ => u - 1) z + logDerivZeta z := by
      have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) z := (differentiableAt_id.sub_const 1)
      have h2 : DifferentiableAt ℂ riemannZeta z := (differentiableAt_riemannZeta hz_ne_one)
      have hfnz : (fun u : ℂ => u - 1) z ≠ 0 := by simpa using hz1
      have hgnz : riemannZeta z ≠ 0 := hζ
      simpa [logDerivZeta] using!
        (logDeriv_mul (x := z) (f := fun u : ℂ => u - 1) (g := riemannZeta) hfnz hgnz h1 h2)

    have h_step : -logDerivZeta z - (1 / (z - 1))
        = - logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z := by
      have : logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z
            = 1 / (z - 1) + logDerivZeta z := by
        simpa [h_log_id, add_comm] using h_prodLog
      have hneg : - logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z
                 = - (1 / (z - 1) + logDerivZeta z) := by
        simpa using congrArg Neg.neg this
      simpa [sub_eq_add_neg, add_comm] using hneg.symm

    have h_H_eq : H z = (z - 1) * riemannZeta z := by
      simp [H, Function.update_of_ne hz_ne_one]

    have h_eq_event : (fun u : ℂ => H u) =ᶠ[nhds z] (fun u : ℂ => (u - 1) * riemannZeta u) := by
      filter_upwards [eventually_ne_nhds hz_ne_one] with u hu
      simp [H, Function.update_of_ne hu]

    have h_hasDeriv_prod :
        HasDerivAt (fun u : ℂ => (u - 1) * riemannZeta u)
          (riemannZeta z + (z - 1) * deriv riemannZeta z) z := by
      have h1 : HasDerivAt (fun u : ℂ => u - 1) 1 z := (hasDerivAt_id z).sub_const 1
      have h2 : HasDerivAt riemannZeta (deriv riemannZeta z) z :=
        (differentiableAt_riemannZeta hz_ne_one).hasDerivAt
      simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using! (h1.mul h2)

    have h_hasDeriv_H :
        HasDerivAt H (riemannZeta z + (z - 1) * deriv riemannZeta z) z :=
      h_hasDeriv_prod.congr_of_eventuallyEq h_eq_event

    have h_dH : deriv H z = riemannZeta z + (z - 1) * deriv riemannZeta z := by
      simpa using h_hasDeriv_H.deriv

    have h_log_to_G : - logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z = G z := by
      have h' : logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z = (deriv H z) / H z := by
        simp [logDeriv_apply, h_H_eq, h_dH, h_deriv_mul]
      have hneg' := congrArg (fun w => -w) h'
      simpa [G, neg_div] using hneg'

    have : -logDerivZeta z - (1 / (z - 1)) = G z := by
      simpa using h_step.trans h_log_to_G

    simpa [z] using this

  let F : ℝ → ℂ := fun δ => G ((1 : ℂ) + δ)

  have hH_analytic_univ : AnalyticOnNhd ℂ H Set.univ :=
    (Complex.analyticOnNhd_univ_iff_differentiable).2 hH_diff

  have hF_contOn : ContinuousOn F s := by
    intro δ0 hδ0
                           
    let s0 : ℂ := (1 : ℂ) + δ0
    have hδ0pos : 0 < δ0 := lt_of_lt_of_le h0 hδ0.1
    have hs0_ne_one : s0 ≠ (1 : ℂ) := by
      intro h
      have hre : (1 + δ0 : ℝ) = 1 := by
        simpa [s0, Complex.add_re, Complex.ofReal_re] using congrArg Complex.re h
      have : δ0 = 0 := by linarith
      exact (ne_of_gt hδ0pos) this
    have hs0_re_gt_one : 1 < s0.re := by
      simpa [s0, Complex.add_re, Complex.ofReal_re] using by linarith
    have hζ_ne : riemannZeta s0 ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (le_of_lt hs0_re_gt_one)
    have hHs0_eq : H s0 = (s0 - 1) * riemannZeta s0 := by
      simp [H, Function.update_of_ne hs0_ne_one]
    have hHs0_ne : H s0 ≠ 0 := by
      have hs0m1_ne : s0 - 1 ≠ 0 := sub_ne_zero.mpr hs0_ne_one
      have : (s0 - 1) * riemannZeta s0 ≠ 0 := mul_ne_zero hs0m1_ne hζ_ne
      simpa [hHs0_eq] using this
                                                                                
    have hH_an_at_s0 : AnalyticAt ℂ H s0 := hH_analytic_univ s0 (by simp)
    have hH'_an_at_s0 : AnalyticAt ℂ (fun z => deriv H z) s0 := hH_an_at_s0.deriv
    have hG_an_at_s0 : AnalyticAt ℂ (fun z => G z) s0 := by
      have h_div : AnalyticAt ℂ (fun z => (deriv H z) / H z) s0 :=
        hH'_an_at_s0.div hH_an_at_s0 (by simpa using hHs0_ne)
      have h_neg : AnalyticAt ℂ (fun z => -((deriv H z) / H z)) s0 := h_div.neg
      simpa [G, div_eq_mul_inv, mul_left_comm, mul_comm, mul_assoc] using h_neg
    have hG_cont_s0 : ContinuousAt (fun z : ℂ => G z) s0 := hG_an_at_s0.continuousAt
                                               
    let affine : ℝ → ℂ := fun δ => (1 : ℂ) + (δ : ℂ)
    have h_affine_at : ContinuousAt affine δ0 :=
      (continuousAt_const).add Complex.continuous_ofReal.continuousAt
                           
    have hy : affine δ0 = s0 := by simp [affine, s0]
    have hG_at : ContinuousAt (fun z : ℂ => G z) (affine δ0) := by simpa [hy] using hG_cont_s0
    have h_comp_at : ContinuousAt (fun δ : ℝ => G (affine δ)) δ0 := hG_at.comp h_affine_at
    simpa [F, s, affine] using h_comp_at.continuousWithinAt

  have h_eq_on_s : ∀ ⦃δ : ℝ⦄, δ ∈ s → f δ = F δ := by
    intro δ hδ
    have hδpos : 0 < δ := lt_of_lt_of_le h0 hδ.1
    simpa [f, F] using h_eq_on_pos hδpos

  have hK : IsCompact s := isCompact_Icc
  have hNorm_contOn : ContinuousOn (fun δ => ‖F δ‖) s := hF_contOn.norm
  have hBdd : BddAbove ((fun δ => ‖F δ‖) '' s) := IsCompact.bddAbove_image hK hNorm_contOn
  rcases hBdd with ⟨C, hC⟩

  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro δ hδa hδb
                                                               
  change ‖f δ‖ ≤ max C 0
  have hδmem : δ ∈ s := ⟨hδa, hδb⟩
  have himg : (fun δ => ‖F δ‖) δ ∈ (fun δ => ‖F δ‖) '' s := ⟨δ, hδmem, rfl⟩
  have hbound : ‖F δ‖ ≤ C := hC himg
  have hbound' : ‖F δ‖ ≤ max C 0 := le_trans hbound (le_max_left _ _)
                                       
  have hfδ_eq : f δ = F δ := h_eq_on_s hδmem
  calc
    ‖f δ‖ = ‖F δ‖ := by simp [hfδ_eq]
    _ ≤ max C 0 := hbound'

lemma norm_one_div_coe_real_le_one_of_one_le {δ : ℝ} (h : 1 ≤ δ) : ‖(1 : ℂ) / (δ : ℂ)‖ ≤ 1 := by
                                                
  have hδpos : 0 < δ := lt_of_lt_of_le zero_lt_one h
  calc
    ‖(1 : ℂ) / (δ : ℂ)‖ = ‖(1 : ℂ)‖ / ‖(δ : ℂ)‖ := by
      exact norm_div (1 : ℂ) (δ : ℂ)
    _ = 1 / ‖(δ : ℂ)‖ := by simp
    _ = 1 / |δ| := by simp
    _ = 1 / δ := by simp [abs_of_nonneg (le_of_lt hδpos)]
    _ ≤ 1 := by
                                                           
      simpa using (one_div_le_one_div_of_le (ha := (zero_lt_one)) (h := h))

lemma Z0bound_const :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    ‖ -logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C := by
                                                 
  rcases uniform_bound_Z0_complex with ⟨δ0, hδ0pos, C0, hC0nonneg, hsmall⟩
                          
  let a : ℝ := min δ0 1
  have ha_pos : 0 < a := lt_min_iff.2 ⟨hδ0pos, zero_lt_one⟩
  have ha_le_one : a ≤ 1 := min_le_right _ _
  rcases bounded_on_compact_interval a 1 ha_pos ha_le_one with ⟨Cmid, hCmid_nonneg, hmid⟩
                                                       
  let C2 : ℝ := ∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ))
  have hC2_nonneg : 0 ≤ C2 := by
    have hnn : ∀ n, 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) :=
      vonMangoldt_rpow_nonneg 2
    exact tsum_nonneg_of_nonneg hnn
                                                                                
  let C : ℝ := 2 + C0 + Cmid + C2
  have hCgt1 : 1 < C := by
    have : 2 ≤ 2 + C0 + Cmid + C2 := by linarith [hC0nonneg, hCmid_nonneg, hC2_nonneg]
    linarith
  refine ⟨C, hCgt1, ?_⟩
  intro δ hδpos
  by_cases hlt : δ < δ0
  ·                                        
    have hbound : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C0 :=
      hsmall δ hδpos hlt
             
    have hC0_le_C : C0 ≤ C := by linarith
    exact le_trans hbound hC0_le_C
  ·          
    have hge : δ0 ≤ δ := le_of_not_gt hlt
    rcases le_total δ 1 with hδle1 | hδge1
    ·                              
      have ha_le_δ : a ≤ δ := le_trans (min_le_left δ0 1) hge
      have hbound : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ Cmid :=
        hmid δ ha_le_δ hδle1
                 
      have hCmid_le_C : Cmid ≤ C := by linarith
      exact le_trans hbound hCmid_le_C
    ·                                                     
                      
      let x : ℝ := 1 + δ
      have hx1 : 1 < x := by
        have : 0 < δ := hδpos
        have : 1 < 1 + δ := lt_add_of_pos_right 1 this
        exact this
                                                           
      have h_norm_eq_abs_real : ‖-logDerivZeta (x : ℂ)‖
            = |∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)| :=
        norm_negLogDerivZeta_real_eq_abs_tsum_vonMangoldt x hx1
                                      
      have eqArg : ((1 : ℂ) + δ) = (x : ℂ) := by simp [x]
                                             
      have h_norm_eq_abs : ‖-logDerivZeta ((1 : ℂ) + δ)‖
            = |∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)| := by
        simpa [eqArg] using h_norm_eq_abs_real
                              
      let S : ℝ := ∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
      have hsum_nonneg : 0 ≤ S := by
        change 0 ≤ ∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
        exact tsum_nonneg_of_nonneg (vonMangoldt_rpow_nonneg x)
                                                                      
      have h_norm_le_sum : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ S := by
        have : ‖-logDerivZeta ((1 : ℂ) + δ)‖ = |S| := h_norm_eq_abs
        have : |S| = S := abs_of_nonneg hsum_nonneg
        exact le_of_eq (h_norm_eq_abs.trans this)
                                                                 
      have hx_ge_two : 2 ≤ x := by
                                     
        have : 1 ≤ δ := hδge1
        have : 2 ≤ 1 + δ := by linarith
        exact this
                                                   
      have h_le_2 : ∀ n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
                          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) := by
        intro n
        by_cases h0 : n = 0
        · simp [h0]
        · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h0
          have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          have hrpow : (n : ℝ) ^ (-x) ≤ (n : ℝ) ^ (-(2 : ℝ)) :=
            rpow_neg_antitone hn' hx_ge_two
          have hΛ_nonneg : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
            ArithmeticFunction.vonMangoldt_nonneg
          exact mul_le_mul_of_nonneg_left hrpow hΛ_nonneg
                                   
      have h_summ_x : Summable (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) := by
        exact Rezetaseries0 x hx1
      have h_summ_2 : Summable (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ))) :=
        Rezetaseries0 2 (by norm_num)
      have hsum_le : S ≤ C2 := by
                                                
        have h_nonneg_x : ∀ n, 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) :=
          vonMangoldt_rpow_nonneg x
        exact tsum_le_of_nonneg_of_le h_summ_x h_summ_2 h_nonneg_x h_le_2
                                        
      have h_norm_le_C2 : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ C2 :=
        le_trans h_norm_le_sum hsum_le
                                                                
      have h_one_div_le : ‖(1 : ℂ) / (δ : ℂ)‖ ≤ 1 := norm_one_div_coe_real_le_one_of_one_le hδge1
      have htriangle : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖
                        ≤ ‖-logDerivZeta ((1 : ℂ) + δ)‖ + ‖(1 : ℂ) / (δ : ℂ)‖ :=
        norm_sub_le _ _
      have hlarge_bound : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C2 + 1 := by
        refine le_trans htriangle ?_
        exact add_le_add h_norm_le_C2 h_one_div_le
                     
      have hC2_le_C : C2 + 1 ≤ C := by linarith
      exact le_trans hlarge_bound hC2_le_C
















































































































































lemma lem_term_real_nonneg (n : ℕ) (σ : ℝ) (_hσ : 1 < σ) : ∃ r ≥ (0:ℝ), ((ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))) = (r : ℂ) := by
                                                     
  let r : ℝ := (ArithmeticFunction.vonMangoldt n) / ((n : ℝ) ^ σ)
  refine ⟨r, ?_, ?_⟩
  ·                                                                                      
    have hbase_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hden_nonneg : 0 ≤ (n : ℝ) ^ σ := by
      simpa using (Real.rpow_nonneg hbase_nonneg σ)
                                          
    have hv_nonneg : 0 ≤ (ArithmeticFunction.vonMangoldt n) := by
      simp
    have : 0 ≤ (ArithmeticFunction.vonMangoldt n) * ((n : ℝ) ^ σ)⁻¹ :=
      mul_nonneg hv_nonneg (inv_nonneg.mpr hden_nonneg)
    simpa [r, div_eq_mul_inv] using this
  ·                                            
    have hbase_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hden_eq : (((n : ℝ) ^ σ : ℝ) : ℂ) = (n : ℂ) ^ (σ : ℂ) := by
      simpa using (Complex.ofReal_cpow (x := (n : ℝ)) (hx := hbase_nonneg) (y := σ))
    calc
      ((ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ)))
          = ((ArithmeticFunction.vonMangoldt n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ)) := by
              simp [hden_eq.symm]
      _ = (((ArithmeticFunction.vonMangoldt n : ℝ) / ((n : ℝ) ^ σ)) : ℝ) := by
              simp
      _ = (r : ℂ) := by rfl








lemma helper_norm_neg_logDeriv_eq_tsum_norm (σ : ℝ) (hσ : 1 < σ) :
  ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ =
    (∑' n : ℕ, ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))‖) := by
  classical
                                  
  let s : ℂ := (σ : ℂ)
                                                                             
  let f : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
                                                     
  let u : ℕ → ℂ := fun n => LSeries.term f s n
                                                   
  have hs_re : 1 < s.re := by simpa using! hσ
  have hsum_term : Summable (fun n : ℕ => LSeries.term f s n) := by
    simpa [f] using! (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := s) hs_re)
                       
  have hsum_u : Summable u := hsum_term
                                                        
  have hL_eq : (∑' n : ℕ, LSeries.term f s n) = - deriv riemannZeta s / riemannZeta s :=
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := s) hs_re)
  have hsum_eq : (∑' n, u n) = - deriv riemannZeta s / riemannZeta s := by
    simpa [u] using hL_eq

  have hterm_as_div : ∀ n,
      u n = ((ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))) := by
    intro n; by_cases h0 : n = 0
    ·         
      subst h0; simp [u, LSeries.term, f, s]
    ·         
      simp [u, LSeries.term, f, s, h0]
                                                           
  let r : ℕ → ℝ := fun n => Classical.choose (lem_term_real_nonneg n σ hσ)
  have hr_nonneg : ∀ n, 0 ≤ r n := by
    intro n; exact (Classical.choose_spec (lem_term_real_nonneg n σ hσ)).1
  have hr_cast : ∀ n,
      ((ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))) = (r n : ℂ) := by
    intro n; exact (Classical.choose_spec (lem_term_real_nonneg n σ hσ)).2
  have hr_eq' : ∀ n, u n = (r n : ℂ) := by
    intro n; simpa [hterm_as_div n] using (hr_cast n)
                                       
  have hsum_rc : Summable (fun n => (r n : ℂ)) := by
    simpa [u, hr_eq'] using hsum_u
  have hsum_r : Summable r := (Complex.summable_ofReal).1 hsum_rc
                                                         
  have hsum_u_as_real : (∑' n, u n) = ((∑' n, r n) : ℝ) := by
    have hru : (fun n => (r n : ℂ)) = u := by
      funext n; symm; exact hr_eq' n
    have := (Complex.ofReal_tsum (L := SummationFilter.unconditional ℕ) (f := r))

    simpa [hru] using this.symm
                                                             
  have hpoint_norm : (fun n : ℕ => ‖u n‖)
        = (fun n : ℕ => ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))‖) := by
    funext n; by_cases h0 : n = 0
    · subst h0; simp [u, LSeries.term, f, s]
    · simp [u, LSeries.term, f, s, h0]
  have hnorm_fun : (fun n : ℕ => ‖u n‖) = r := by
    funext n; simp [hr_eq' n, Complex.norm_real, abs_of_nonneg (hr_nonneg n)]
  have hsum_norm : Summable (fun n : ℕ => ‖u n‖) := by
    simpa [hnorm_fun] using hsum_r
                                                        
  have hineq : ‖∑' n, u n‖ ≤ ∑' n, ‖u n‖ :=
    norm_tsum_le_tsum_norm (f := u) hsum_norm
                                                  
  set S : ℝ := ∑' n, r n
  have hS_le : ‖((S : ℝ) : ℂ)‖ ≤ S := by
    simpa [S, hsum_u_as_real, hnorm_fun] using hineq
                              
  have hS_nonneg : 0 ≤ S := by
    have habs_le : |S| ≤ S := by simpa [Complex.norm_real] using hS_le
    exact (abs_nonneg S).trans habs_le
                                                
  have h_left : ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖
      = ‖∑' n, u n‖ := by
    have : - deriv riemannZeta s / riemannZeta s = ∑' n, u n := by simpa [hsum_u_as_real] using hsum_eq.symm
    simp [s, this]
  have h_mid : ‖∑' n, u n‖ = S := by
                                               
    have : ‖((S : ℝ) : ℂ)‖ = S := by simp [Complex.norm_real, abs_of_nonneg hS_nonneg]
    simpa [S, hsum_u_as_real] using this
  have h_right : (∑' n : ℕ, ‖u n‖) = S := by simp [S, hnorm_fun]
                                            
  calc
    ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖
        = ‖∑' n, u n‖ := h_left
    _ = S := h_mid
    _ = (∑' n : ℕ, ‖u n‖) := h_right.symm
    _ = (∑' n : ℕ, ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))‖) := by
          simp [hpoint_norm]





open _root_.Set _root_.Function _root_.Filter _root_.Complex _root_.Real

end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveZeroDistance
namespace OAI

/-! Quantitative separation between the inner evaluation point and all zeros
in the fixed disk. The only strip used below is the one already proved for
the actual modulus-five L-functions.
-/

namespace TwoPointCorrelations

open _root_.Complex
open scoped _root_.Classical

lemma modFive_log_height_ge_half (t : ℝ) : 1 / 2 ≤ Real.log (|t| + 2) := by
  have hlog : 1 / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  exact hlog.trans (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))

lemma modFive_physical_zero_height (χ : DirichletCharacter ℂ 5) (t : ℝ)
    {ρ : ℂ} (hρ : ρ ∈ modFiveNormalizedZeros χ t) :
    |(modFivePhysicalPoint t ρ).im| ≤ |t| + 2 := by
  have hn : ‖ρ‖ ≤ 7 / 8 := by simpa using hρ.1
  have hi := (Complex.abs_im_le_norm ρ).trans hn
  have he : (modFivePhysicalPoint t ρ).im = t + (3 / 2 : ℝ) * ρ.im := by
    simp [modFivePhysicalPoint, Complex.mul_im]
  rw [he]
  calc
    _ ≤ |t| + |(3 / 2 : ℝ) * ρ.im| := abs_add_le _ _
    _ = |t| + (3 / 2 : ℝ) * |ρ.im| := by rw [abs_mul]; norm_num
    _ ≤ _ := by linarith

lemma modFive_physical_zero_log_height (χ : DirichletCharacter ℂ 5) (t : ℝ)
    {ρ : ℂ} (hρ : ρ ∈ modFiveNormalizedZeros χ t) :
    Real.log (|(modFivePhysicalPoint t ρ).im| + 2) ≤ 2 * Real.log (|t| + 2) := by
  calc
    _ ≤ Real.log ((|t| + 2) ^ 2) := by
      apply Real.log_le_log (by positivity)
      have h := modFive_physical_zero_height χ t hρ
      nlinarith [abs_nonneg t, sq_nonneg (|t|)]
    _ = _ := by rw [Real.log_pow]; norm_num

lemma modFive_zero_distance_of_strip {c : ℝ} (hc : 0 < c)
    (hfree : ∀ (χ : DirichletCharacter ℂ 5), χ ≠ 1 → ∀ (t β : ℝ),
      1 - c / Real.log (|t| + 2) ≤ β →
        DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * (t : ℂ)) ≠ 0)
    (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1) (t σ : ℝ)
    (hσ : 1 - c / (4 * Real.log (|t| + 2)) ≤ σ)
    {ρ : ℂ} (hρ : ρ ∈ modFiveNormalizedZeros χ t) :
    c / (6 * Real.log (|t| + 2)) ≤ ‖modFiveRealDiskPoint σ - ρ‖ := by
  let v := modFivePhysicalPoint t ρ
  have hzero : DirichletCharacter.LFunction χ ((v.re : ℂ) + Complex.I * (v.im : ℂ)) = 0 := by
    have he : (v.re : ℂ) + Complex.I * (v.im : ℂ) = v := by
      apply Complex.ext <;> simp
    rw [he]
    exact modFiveNormalizedZeros_physical_zero χ t hρ
  have hv : v.re < 1 - c / Real.log (|v.im| + 2) := by
    by_contra! h
    exact hfree χ hχ v.im v.re h hzero
  have hH := modFive_log_height_pos t
  have hvH := modFive_log_height_pos v.im
  have hlog := modFive_physical_zero_log_height χ t hρ
  have hinv : c / (2 * Real.log (|t| + 2)) ≤ c / Real.log (|v.im| + 2) :=
    div_le_div_of_nonneg_left hc.le hvH hlog
  have hgap : c / (4 * Real.log (|t| + 2)) ≤ σ - v.re := by
    have he : c / (2 * Real.log (|t| + 2)) = 2 * (c / (4 * Real.log (|t| + 2))) := by ring
    rw [he] at hinv
    linarith
  have hre : (modFiveRealDiskPoint σ - ρ).re = (2 / 3 : ℝ) * (σ - v.re) := by
    dsimp [modFiveRealDiskPoint, v, modFivePhysicalPoint]
    simp only [Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im]
    norm_num
    ring
  calc
    _ = (2 / 3 : ℝ) * (c / (4 * Real.log (|t| + 2))) := by ring
    _ ≤ (2 / 3 : ℝ) * (σ - v.re) := mul_le_mul_of_nonneg_left hgap (by norm_num)
    _ = (modFiveRealDiskPoint σ - ρ).re := hre.symm
    _ ≤ |(modFiveRealDiskPoint σ - ρ).re| := le_abs_self _
    _ ≤ _ := Complex.abs_re_le_norm _

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveStripBound
namespace OAI

/-! Full logarithmic-derivative control in a narrower zero-free strip.
Jensen counts all nearby zeros, and their proved horizontal separation
bounds the entire pole sum, including at bounded height.
-/

namespace TwoPointCorrelations

open _root_.Complex
open scoped _root_.Classical

theorem modFive_logderiv_strip_bound : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (χ : DirichletCharacter ℂ 5), χ ≠ 1 → ∀ (t σ : ℝ),
      1 - c / Real.log (|t| + 2) ≤ σ → σ ≤ 2 →
      DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ)) ≠ 0 ∧
      ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (t : ℂ)) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
          C * Real.log (|t| + 2) ^ 2 := by
  obtain ⟨c0, hc0, hfree0⟩ := modFive_nonprincipal_zero_free
  let c := min c0 (1 / 4)
  have hc : 0 < c := lt_min hc0 (by norm_num)
  have hcsmall : c ≤ 1 / 4 := min_le_right _ _
  have hfree : ∀ (χ : DirichletCharacter ℂ 5), χ ≠ 1 → ∀ (t β : ℝ),
      1 - c / Real.log (|t| + 2) ≤ β →
      DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
    intro χ hχ t β hβ
    apply hfree0 χ hχ t β
    have hd := div_le_div_of_nonneg_right (min_le_left c0 (1 / 4))
      (modFive_log_height_pos t).le
    linarith
  let P := 1 / Real.log ((15 / 16 : ℝ) / (7 / 8))
  have hP : 0 < P := by dsimp [P]; exact one_div_pos.mpr (Real.log_pos (by norm_num))
  let A := Real.log (16 * modFiveInverseConstant) / Real.log 2 + 1
  have hA : 0 < A := by
    have hK : 1 ≤ modFiveInverseConstant := by
      unfold modFiveInverseConstant
      exact le_add_of_nonneg_right (tsum_nonneg fun _ => norm_nonneg _)
    have hlog : 0 ≤ Real.log (16 * modFiveInverseConstant) := Real.log_nonneg (by linarith)
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [A]
    positivity
  let C := A * (2 * modFiveLogDerivativeConstant + 6 * P / c)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos hA (add_pos (mul_pos (by norm_num) modFiveLogDerivativeConstant_pos)
      (div_pos (mul_pos (by norm_num) hP) hc))
  refine ⟨c / 4, C, by positivity, hC, ?_⟩
  intro χ hχ t σ hσ hσ2
  let H := Real.log (|t| + 2)
  have hH : 0 < H := modFive_log_height_pos t
  have hHhalf : 1 / 2 ≤ H := modFive_log_height_ge_half t
  have hσ' : 1 - c / (4 * H) ≤ σ := by
    have he : (c / 4) / H = c / (4 * H) := by ring
    change 1 - (c / 4) / H ≤ σ at hσ
    rwa [he] at hσ
  have hsmall : c / (4 * H) ≤ 1 / 8 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * H)).mpr
    nlinarith
  have hσlow : 7 / 8 ≤ σ := by linarith
  have hne : DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
    apply hfree χ hχ t σ
    have hi : c / (4 * H) ≤ c / H :=
      div_le_div_of_nonneg_left hc.le hH (by linarith)
    linarith
  refine ⟨hne, ?_⟩
  let z := modFiveRealDiskPoint σ
  have hz : ‖z‖ ≤ 3 / 4 := by
    rw [show z = modFiveRealDiskPoint σ from rfl, modFiveRealDiskPoint,
      Complex.norm_real, Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> linarith
  have hp : DirichletCharacter.LFunction χ (modFivePhysicalPoint t z) ≠ 0 := by
    rwa [modFivePhysicalPoint_real]
  have hn : modFiveNormalizedLFunction χ t z ≠ 0 :=
    div_ne_zero hp (χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by norm_num))
  have hd : ∀ ρ ∈ modFiveNormalizedZeros χ t, c / (6 * H) ≤ ‖z - ρ‖ := by
    intro ρ hρ
    exact modFive_zero_distance_of_strip hc hfree χ hχ t σ hσ' hρ
  have he := modFive_normalized_logderiv_norm χ hχ t hz hn
    (show 0 < c / (6 * H) by positivity) hd
  have hcoef : 0 ≤ modFiveLogDerivativeConstant + P / (c / (6 * H)) := by
    exact add_nonneg modFiveLogDerivativeConstant_pos.le (div_nonneg hP.le (by positivity))
  have hlog := mul_le_mul_of_nonneg_left (modFive_log_disk_growth t) hcoef
  have htotal := he.trans hlog
  have hrecip : P / (c / (6 * H)) = (6 * P / c) * H := by
    field_simp
  change _ ≤ (modFiveLogDerivativeConstant + P / (c / (6 * H))) * (A * H) at htotal
  rw [hrecip] at htotal
  have hlinear : H ≤ 2 * H ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hlinear
    (mul_nonneg hA.le modFiveLogDerivativeConstant_pos.le)
  have htotal' : ‖deriv (modFiveNormalizedLFunction χ t) z /
      modFiveNormalizedLFunction χ t z‖ ≤ C * H ^ 2 := by
    dsimp [C]
    nlinarith only [htotal, hmul]
  rw [modFiveNormalized_logderiv_eq χ hχ t z hp, norm_mul, modFivePhysicalPoint_real] at htotal'
  norm_num at htotal'
  apply (le_mul_of_one_le_left (norm_nonneg _)
    (by norm_num : (1 : ℝ) ≤ 3 / 2)).trans
  simpa only [norm_div] using htotal'

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveContourRegion
namespace OAI

/-! A common closed zero-free rectangle and its uniform logarithmic-
derivative bound. This prepares the finite contour shift without a
height-dependent analyticity assumption.
-/

namespace TwoPointCorrelations

open _root_.Complex _root_.Set

theorem modFive_logderiv_rectangles : ∃ a C : ℝ,
    0 < a ∧ a ≤ 1 / 4 ∧ 0 < C ∧
    ∀ (χ : DirichletCharacter ℂ 5), χ ≠ 1 → ∀ T : ℝ, 2 ≤ T →
      ∀ s : ℂ, 1 - a / Real.log (T + 2) ≤ s.re → s.re ≤ 2 → |s.im| ≤ T →
        DirichletCharacter.LFunction χ s ≠ 0 ∧
        ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
          C * Real.log (T + 2) ^ 2 := by
  obtain ⟨c, C, hc, hC, hbound⟩ := modFive_logderiv_strip_bound
  let a := min c (1 / 4)
  have ha : 0 < a := lt_min hc (by norm_num)
  have hac : a ≤ c := min_le_left _ _
  refine ⟨a, C, ha, min_le_right _ _, hC, ?_⟩
  intro χ hχ T hT s hs hs2 ht
  have hH : 0 < Real.log (T + 2) := Real.log_pos (by linarith)
  have hh := modFive_log_height_pos s.im
  have hlog : Real.log (|s.im| + 2) ≤ Real.log (T + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hdiv : a / Real.log (T + 2) ≤ c / Real.log (|s.im| + 2) :=
    (div_le_div_of_nonneg_left ha.le hh hlog).trans
      (div_le_div_of_nonneg_right hac hh.le)
  have hs' : 1 - c / Real.log (|s.im| + 2) ≤ s.re := by linarith
  have he : (s.re : ℂ) + Complex.I * (s.im : ℂ) = s := by
    apply Complex.ext <;> simp
  have hb := hbound χ hχ s.im s.re hs' hs2
  rw [he] at hb
  refine ⟨hb.1, hb.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh.le hlog 2) hC.le

lemma modFive_logderiv_differentiableAt (χ : DirichletCharacter ℂ 5)
    (hχ : χ ≠ 1) {s : ℂ} (hs : DirichletCharacter.LFunction χ s ≠ 0) :
    DifferentiableAt ℂ (fun z =>
      -deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z) s := by
  have hf := DirichletCharacter.differentiable_LFunction hχ
  exact ((hf.analyticAt s).deriv.differentiableAt.neg).div (hf s) hs

lemma modFive_perron_integrand_differentiableAt (χ : DirichletCharacter ℂ 5)
    (hχ : χ ≠ 1) {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs : DirichletCharacter.LFunction χ s ≠ 0) (hs0 : s ≠ 0) (hs1 : s + 1 ≠ 0) :
    DifferentiableAt ℂ (fun z =>
      (-deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z) *
        modFivePerronKernel x z) s := by
  apply (modFive_logderiv_differentiableAt χ hχ hs).mul
  unfold modFivePerronKernel
  apply DifferentiableAt.div
  · exact differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  · fun_prop
  · exact mul_ne_zero hs0 hs1

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveRectangleShift
namespace OAI

/-! The exact finite rectangle shift, with an explicit horizontal cost.
All functions are complex scalar functions, as needed for the three fixed
nonprincipal Dirichlet L-functions.
-/

namespace TwoPointCorrelations

open _root_.Complex _root_.Set _root_.MeasureTheory _root_.intervalIntegral
open _root_.Erdos970 hiding ChebyshevPsi DeltaSpike I₁ I₂ I₃ I₃₇ I₄ I₅ I₆ I₇ I₈ I₉ LogDerivZetaHasBound LogDerivZetaIsHoloSmall MellinConvolution MellinInverseTransform MellinTransform Smooth1 SmoothedChebyshev SmoothedChebyshevIntegrand sigma1Of

lemma modFive_rectangle_shift {f : ℂ → ℂ} {a b T : ℝ}
    (hf : DifferentiableOn ℂ f (Rectangle ((a : ℂ) - Complex.I * (T : ℂ))
      ((b : ℂ) + Complex.I * (T : ℂ)))) :
    VIntegral f b (-T) T =
      VIntegral f a (-T) T + HIntegral f a b T - HIntegral f a b (-T) := by
  have hz := Erdos970.HolomorphicOn.vanishesOnRectangle hf (subset_refl _)
  simp only [RectangleIntegral, Complex.sub_re, Complex.add_re, Complex.sub_im,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, one_mul,
    zero_sub, sub_zero, add_zero, zero_add] at hz
  linear_combination hz

lemma modFive_rectangle_shift_bound {f : ℂ → ℂ} {a b T B : ℝ}
    (hab : a ≤ b)
    (hf : DifferentiableOn ℂ f (Rectangle ((a : ℂ) - Complex.I * (T : ℂ))
      ((b : ℂ) + Complex.I * (T : ℂ))))
    (hup : ∀ σ ∈ Icc a b, ‖f ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ B)
    (hdown : ∀ σ ∈ Icc a b, ‖f ((σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ B) :
    ‖VIntegral f b (-T) T‖ ≤ ‖VIntegral f a (-T) T‖ + 2 * B * (b - a) := by
  have htop : ‖HIntegral f a b T‖ ≤ B * (b - a) := by
    have hpoint : ∀ σ ∈ uIoc a b, ‖f ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ B := by
      intro σ hσ
      exact hup σ (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hσ))
    simpa only [HIntegral, abs_of_nonneg (sub_nonneg.mpr hab)] using
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have hbot : ‖HIntegral f a b (-T)‖ ≤ B * (b - a) := by
    have hpoint : ∀ σ ∈ uIoc a b, ‖f ((σ : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ B := by
      intro σ hσ
      exact hdown σ (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hσ))
    simpa only [HIntegral, abs_of_nonneg (sub_nonneg.mpr hab)] using
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [modFive_rectangle_shift hf]
  calc
    _ ≤ ‖VIntegral f a (-T) T + HIntegral f a b T‖ + ‖HIntegral f a b (-T)‖ := norm_sub_le _ _
    _ ≤ (‖VIntegral f a (-T) T‖ + ‖HIntegral f a b T‖) + ‖HIntegral f a b (-T)‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := by linarith

lemma modFive_vertical_quadratic_bound {f : ℂ → ℂ} {σ T D : ℝ}
    (hT : 0 ≤ T) (hD : 0 ≤ D)
    (hf : ∀ t ∈ Icc (-T) T, ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ D / (1 + t ^ 2)) :
    ‖VIntegral f σ (-T) T‖ ≤ D * Real.pi := by
  rw [VIntegral, norm_smul, Complex.norm_I, one_mul]
  have hgi : IntervalIntegrable (fun t : ℝ => D / (1 + t ^ 2)) volume (-T) T := by
    simpa only [div_eq_mul_inv] using (integrable_inv_one_add_sq.const_mul D).intervalIntegrable
  have hb := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -T ≤ T)
    (Filter.Eventually.of_forall fun t ht => hf t ⟨ht.1.le, ht.2⟩) hgi
  refine hb.trans ?_
  simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul, integral_inv_one_add_sq]
  apply mul_le_mul_of_nonneg_left _ hD
  linarith [Real.arctan_lt_pi_div_two T, Real.neg_pi_div_two_lt_arctan (-T)]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePerronShift
namespace OAI

/-! Quantitative finite contour shift for the actual twisted Mangoldt
integrand. The left side stays inside the proved zero-free rectangle and
the two horizontal sides are bounded explicitly.
-/

namespace TwoPointCorrelations

open _root_.Complex _root_.Set
open _root_.Erdos970 hiding ChebyshevPsi DeltaSpike I₁ I₂ I₃ I₃₇ I₄ I₅ I₆ I₇ I₈ I₉ LogDerivZetaHasBound LogDerivZetaIsHoloSmall MellinConvolution MellinInverseTransform MellinTransform Smooth1 SmoothedChebyshev SmoothedChebyshevIntegrand sigma1Of


theorem modFive_finite_perron_shift : ∃ a C : ℝ,
    0 < a ∧ a ≤ 1 / 4 ∧ 0 < C ∧
    ∀ (χ : DirichletCharacter ℂ 5), χ ≠ 1 → ∀ T x b : ℝ,
      2 ≤ T → 1 ≤ x → 1 - a / Real.log (T + 2) ≤ b → b ≤ 2 →
      ‖VIntegral (modFivePerronIntegrand χ x) b (-T) T‖ ≤
        4 * Real.pi * C * Real.log (T + 2) ^ 2 * x ^ (1 - a / Real.log (T + 2)) +
          2 * (b - (1 - a / Real.log (T + 2))) *
            (C * Real.log (T + 2) ^ 2 * x ^ b / T ^ 2) := by
  obtain ⟨a, C, ha, ha4, hC, hreg⟩ := modFive_logderiv_rectangles
  refine ⟨a, C, ha, ha4, hC, ?_⟩
  intro χ hχ T x b hT hx hab hb2
  let A := 1 - a / Real.log (T + 2)
  let H := Real.log (T + 2)
  have hTp : 0 < T := by linarith
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hH : 0 < H := Real.log_pos (by linarith)
  have hHhalf : 1 / 2 ≤ H := by
    simpa only [abs_of_nonneg hTp.le] using modFive_log_height_ge_half T
  have hAhalf : 1 / 2 ≤ A := by
    have hadiv : a / H ≤ 1 / 2 := by
      apply (div_le_iff₀ hH).mpr
      linarith
    dsimp [A, H] at *
    linarith
  have heval (σ t : ℝ) (hσ : A ≤ σ) (hσ2 : σ ≤ 2) (ht : |t| ≤ T) :
      DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 ∧
      ‖-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * H ^ 2 := by
    have he := hreg χ hχ T hT ((σ : ℂ) + (t : ℂ) * Complex.I)
      (by
        have hr : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
        rw [hr]
        exact hσ) (by simpa using hσ2) (by simpa using ht)
    exact ⟨he.1, by simpa only [neg_div, norm_neg] using he.2⟩
  have hf : DifferentiableOn ℂ (modFivePerronIntegrand χ x)
      (Rectangle ((A : ℂ) - Complex.I * (T : ℂ)) ((b : ℂ) + Complex.I * (T : ℂ))) := by
    intro s hs
    have hab' : A ≤ b := hab
    have hs' : s.re ∈ Icc A b ∧ s.im ∈ Icc (-T) T := by
      simpa [Rectangle, Complex.mem_reProdIm, uIcc_of_le hab', uIcc_of_le (show -T ≤ T by linarith)] using hs
    have hn := (hreg χ hχ T hT s hs'.1.1 (hs'.1.2.trans hb2) (abs_le.mpr hs'.2)).1
    have hs0 : s ≠ 0 := by
      intro he
      have hre := hs'.1.1
      rw [he] at hre
      simp only [Complex.zero_re] at hre
      linarith
    have hs1 : s + 1 ≠ 0 := by
      intro he
      have hre := congrArg Complex.re he
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
      linarith [hs'.1.1]
    exact (modFive_perron_integrand_differentiableAt χ hχ hxp hn hs0 hs1).differentiableWithinAt
  have hside (t : ℝ) (ht : |t| = T) :
      ∀ σ ∈ Icc A b, ‖modFivePerronIntegrand χ x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * H ^ 2 * x ^ b / T ^ 2 := by
    intro σ hσ
    have ht0 : t ≠ 0 := by intro he; simp [he] at ht; linarith
    have ht2 : t ^ 2 = T ^ 2 := by rw [← sq_abs, ht]
    have hlog := (heval σ t hσ.1 (hσ.2.trans hb2) ht.le).2
    have hk := modFive_perron_kernel_horizontal hxp σ ht0
    have hpow : x ^ σ ≤ x ^ b := Real.rpow_le_rpow_of_exponent_le hx hσ.2
    calc
      _ = ‖-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I) /
          DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ *
            ‖modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_mul _ _
      _ ≤ (C * H ^ 2) * (x ^ σ / t ^ 2) :=
        mul_le_mul hlog hk (norm_nonneg _) (mul_nonneg hC.le (sq_nonneg H))
      _ ≤ _ := by
        rw [ht2, ← mul_div_assoc]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow
          (mul_nonneg hC.le (sq_nonneg H))) (sq_nonneg T)
  have hv : ‖VIntegral (modFivePerronIntegrand χ x) A (-T) T‖ ≤
      (4 * C * H ^ 2 * x ^ A) * Real.pi := by
    apply modFive_vertical_quadratic_bound hTp.le (by positivity)
    intro t ht
    have hlog := (heval A t le_rfl (hab.trans hb2) (abs_le.mpr ht)).2
    have hk := modFive_perron_kernel_vertical hxp hAhalf t
    calc
      _ = ‖-deriv (DirichletCharacter.LFunction χ) ((A : ℂ) + (t : ℂ) * Complex.I) /
          DirichletCharacter.LFunction χ ((A : ℂ) + (t : ℂ) * Complex.I)‖ *
            ‖modFivePerronKernel x ((A : ℂ) + (t : ℂ) * Complex.I)‖ := norm_mul _ _
      _ ≤ (C * H ^ 2) * (4 * x ^ A / (1 + t ^ 2)) :=
        mul_le_mul hlog hk (norm_nonneg _) (mul_nonneg hC.le (sq_nonneg H))
      _ = _ := by ring
  have hs := modFive_rectangle_shift_bound hab hf
    (hside T (abs_of_nonneg hTp.le)) (hside (-T) (by simp [abs_of_nonneg hTp.le]))
  calc
    _ ≤ (4 * C * H ^ 2 * x ^ A) * Real.pi +
        2 * (C * H ^ 2 * x ^ b / T ^ 2) * (b - A) :=
      hs.trans (add_le_add hv le_rfl)
    _ = _ := by dsimp [A, H]; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveRightBound
namespace OAI

/-! Absolute convergence bounds on the right Perron line.  The twisted
series is dominated term by term by the untwisted Mangoldt series, whose
pole has the explicit reciprocal-distance bound. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.ArithmeticFunction
open _root_.Erdos970 hiding ChebyshevPsi DeltaSpike I₁ I₂ I₃ I₃₇ I₄ I₅ I₆ I₇ I₈ I₉ LogDerivZetaHasBound LogDerivZetaIsHoloSmall MellinConvolution MellinInverseTransform MellinTransform Smooth1 SmoothedChebyshev SmoothedChebyshevIntegrand sigma1Of
open scoped _root_.BigOperators

lemma modFive_mangoldt_norm (χ : DirichletCharacter ℂ 5) (n : ℕ) :
    ‖modFiveMangoldtTwist χ n‖ ≤ ‖(vonMangoldt n : ℂ)‖ := by
  unfold modFiveMangoldtTwist
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)).trans_eq
    (one_mul _)

lemma modFive_logderiv_right_domination (χ : DirichletCharacter ℂ 5)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I) /
      DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ‖-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hs : 1 < s.re := by simpa [s] using hσ
  have hsum := χ.LSeriesSummable_twist_vonMangoldt hs
  have hsum0 := LSeriesSummable_vonMangoldt (s := (σ : ℂ)) hσ
  have hterm (n : ℕ) : ‖LSeries.term (modFiveMangoldtTwist χ) s n‖ ≤
      ‖LSeries.term (fun m => (vonMangoldt m : ℂ)) (σ : ℂ) n‖ := by
    have he : ‖LSeries.term (modFiveMangoldtTwist χ) s n‖ =
        ‖LSeries.term (modFiveMangoldtTwist χ) (σ : ℂ) n‖ := by
      simp only [LSeries.norm_term_eq, s, add_re, ofReal_re, mul_I_re, ofReal_im,
        neg_zero, add_zero]
    rw [he]
    exact LSeries.norm_term_le _ (modFive_mangoldt_norm χ n)
  have heq : (∑' n, ‖LSeries.term (fun m => (vonMangoldt m : ℂ)) (σ : ℂ) n‖) =
      ‖-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ := by
    rw [helper_norm_neg_logDeriv_eq_tsum_norm σ hσ]
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · subst n
      simp
    · rw [LSeries.term_of_ne_zero hn]
  rw [← modFive_twisted_series_logderiv χ hs]
  change ‖∑' n, LSeries.term (modFiveMangoldtTwist χ) s n‖ ≤ _
  exact (norm_tsum_le_tsum_norm hsum.norm).trans
    ((hsum.norm.tsum_le_tsum hterm hsum0.norm).trans_eq heq)

/-- A uniform right-line bound, valid for every character, with only the
explicit simple-pole dependence on the distance from one. -/
theorem modFive_logderiv_right_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : DirichletCharacter ℂ 5) (δ t : ℝ), 0 < δ →
      ‖-deriv (DirichletCharacter.LFunction χ) (((1 + δ : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
        DirichletCharacter.LFunction χ (((1 + δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          1 / δ + C := by
  obtain ⟨C, hC, hbound⟩ := Z0bound_const
  refine ⟨C, lt_trans zero_lt_one hC, ?_⟩
  intro χ δ t hδ
  have hmain := modFive_logderiv_right_domination χ (by linarith : 1 < 1 + δ) t
  have hz := hbound δ hδ
  have hz' : ‖-deriv riemannZeta (((1 + δ : ℝ) : ℂ)) /
      riemannZeta (((1 + δ : ℝ) : ℂ)) - 1 / (δ : ℂ)‖ ≤ C := by
    simpa only [Complex.ofReal_add, Complex.ofReal_one, logDerivZeta, neg_div] using hz
  have hn : ‖(1 : ℂ) / (δ : ℂ)‖ = 1 / δ := by
    simp [abs_of_pos hδ]
  have hb := norm_le_insert' (-deriv riemannZeta (((1 + δ : ℝ) : ℂ)) /
      riemannZeta (((1 + δ : ℝ) : ℂ))) (1 / (δ : ℂ))
  exact hmain.trans (hb.trans (by rw [hn]; linarith))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveVerticalTails
namespace OAI

/-! The two tails of the actual Perron integral.  The inverse-square
majorant gives explicit inverse-height bounds after integration. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.MeasureTheory _root_.Set
open _root_.Erdos970 hiding ChebyshevPsi DeltaSpike I₁ I₂ I₃ I₃₇ I₄ I₅ I₆ I₇ I₈ I₉ LogDerivZetaHasBound LogDerivZetaIsHoloSmall MellinConvolution MellinInverseTransform MellinTransform Smooth1 SmoothedChebyshev SmoothedChebyshevIntegrand sigma1Of

lemma modFive_inverse_square_tail {f : ℝ → ℂ} {T D : ℝ}
    (hT : 0 < T) (hbound : ∀ t ∈ Ioi T, ‖f t‖ ≤ D / t ^ 2) :
    ‖∫ t in Ioi T, f t‖ ≤ D / T := by
  have hi : IntegrableOn (fun t : ℝ => D * t ^ (-2 : ℝ)) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT).const_mul D
  have he : (∫ t in Ioi T, D * t ^ (-2 : ℝ)) = D / T := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT]
    norm_num [Real.rpow_neg_one, div_eq_mul_inv]
  apply (norm_integral_le_of_norm_le hi ?_).trans_eq he
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  convert (preTransparency := .instances) hbound t ht using 1
  rw [Real.rpow_neg (le_of_lt (hT.trans ht)), Real.rpow_two, div_eq_mul_inv]

lemma modFive_vertical_tails {f : ℂ → ℂ} {σ T D : ℝ}
    (hT : 0 < T)
    (hf : Integrable (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)))
    (hbound : ∀ t : ℝ, T ≤ |t| →
      ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ D / t ^ 2) :
    ‖VerticalIntegral f σ - VIntegral f σ (-T) T‖ ≤ 2 * D / T := by
  have hup : ‖∫ t in Ioi T, f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ D / T := by
    apply modFive_inverse_square_tail hT
    intro t ht
    exact hbound t (by rw [abs_of_pos (hT.trans ht)]; exact ht.le)
  have hdown : ‖∫ t in Iic (-T), f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ D / T := by
    rw [← integral_comp_neg_Ioi T]
    apply modFive_inverse_square_tail hT
    intro t ht
    have hb := hbound (-t) (by rw [abs_neg, abs_of_pos (hT.trans ht)]; exact ht.le)
    simpa only [neg_sq] using hb
  have he := verticalIntegral_split_three (f := f) (σ := σ) (-T) T hf
  rw [he]
  have halg (a b c : ℂ) : a + b + c - b = a + c := by ring
  rw [halg]
  calc
    _ ≤ ‖Complex.I • (∫ t in Iic (-T), f ((σ : ℂ) + (t : ℂ) * Complex.I))‖ +
        ‖Complex.I • (∫ t in Ici T, f ((σ : ℂ) + (t : ℂ) * Complex.I))‖ := norm_add_le _ _
    _ = ‖∫ t in Iic (-T), f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ +
        ‖∫ t in Ioi T, f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
      rw [norm_smul, norm_smul, norm_I, one_mul, one_mul, integral_Ici_eq_integral_Ioi]
    _ ≤ D / T + D / T := add_le_add hdown hup
    _ = _ := by ring

lemma modFive_perron_integrable (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1)
    {x σ B : ℝ} (hx : 0 < x) (hσ : 1 < σ) (hB : 0 ≤ B)
    (hbound : ∀ t : ℝ,
      ‖-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B) :
    Integrable (fun t : ℝ => modFivePerronIntegrand χ x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hc : Continuous (fun t : ℝ =>
      modFivePerronIntegrand χ x ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hsr : 1 ≤ ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ.le
    have hn := χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) hsr
    have h0 : (σ : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
      intro he
      have hr := congrArg Complex.re he
      simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero, zero_re] at hr
      linarith
    have h1 : (σ : ℂ) + (t : ℂ) * Complex.I + 1 ≠ 0 := by
      intro he
      have hr := congrArg Complex.re he
      simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero,
        one_re, zero_re] at hr
      linarith
    have hline : ContinuousAt (fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) t := by
      fun_prop
    exact (modFive_perron_integrand_differentiableAt χ hχ hx hn h0 h1).continuousAt.comp (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * Complex.I) hline
  have hi : Integrable (fun t : ℝ => B * (4 * x ^ σ / (1 + t ^ 2))) := by
    simpa only [div_eq_mul_inv, mul_assoc] using
      (integrable_inv_one_add_sq.const_mul (B * (4 * x ^ σ)))
  apply hi.mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    rw [modFivePerronIntegrand, norm_mul]
    exact mul_le_mul (hbound t) (modFive_perron_kernel_vertical hx (by linarith) t)
      (norm_nonneg _) hB

/-- Uniform tails of the actual nonprincipal Perron integrals. -/
theorem modFive_perron_tail_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : DirichletCharacter ℂ 5), χ ≠ 1 → ∀ δ x T : ℝ,
      0 < δ → 0 < x → 0 < T →
      ‖VerticalIntegral (modFivePerronIntegrand χ x) (1 + δ) -
        VIntegral (modFivePerronIntegrand χ x) (1 + δ) (-T) T‖ ≤
          2 * (1 / δ + C) * x ^ (1 + δ) / T := by
  obtain ⟨C, hC, hb⟩ := modFive_logderiv_right_bound
  refine ⟨C, hC, ?_⟩
  intro χ hχ δ x T hδ hx hT
  have hB : 0 ≤ 1 / δ + C := by positivity
  have hi := modFive_perron_integrable χ hχ hx (by linarith : 1 < 1 + δ) hB
    (hb χ δ · hδ)
  have ht := modFive_vertical_tails hT hi (D := (1 / δ + C) * x ^ (1 + δ)) ?_
  · simpa only [mul_assoc] using ht
  intro t ht
  have ht0 : t ≠ 0 := by intro he; simp [he] at ht; linarith
  rw [modFivePerronIntegrand, norm_mul]
  exact (mul_le_mul (hb χ δ t hδ) (modFive_perron_kernel_horizontal hx (1 + δ) ht0)
    (norm_nonneg _) hB).trans_eq (by ring)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFiveSmoothedContour
namespace OAI

/-! A finite quantitative contour bound for the actual smoothed twisted
Mangoldt sums, using the zero-free region and the inverse-square tail
estimate. -/

namespace TwoPointCorrelations

open _root_.Complex
open _root_.Erdos970 hiding ChebyshevPsi DeltaSpike I₁ I₂ I₃ I₃₇ I₄ I₅ I₆ I₇ I₈ I₉ LogDerivZetaHasBound LogDerivZetaIsHoloSmall MellinConvolution MellinInverseTransform MellinTransform Smooth1 SmoothedChebyshev SmoothedChebyshevIntegrand sigma1Of

lemma modFive_perron_normalization : ‖(1 / (2 * Real.pi * Complex.I) : ℂ)‖ ≤ 1 := by
  have hp : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  simp only [norm_div, norm_one, norm_mul, norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_I, mul_one]
  exact (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr hp

theorem modFive_smoothed_contour_bound : ∃ a C D : ℝ,
    0 < a ∧ a ≤ 1 / 4 ∧ 0 < C ∧ 0 < D ∧
    ∀ (χ : DirichletCharacter ℂ 5), χ ≠ 1 → ∀ T x δ : ℝ,
      2 ≤ T → 1 ≤ x → 0 < δ → δ ≤ 1 →
      (∀ n : ℕ, x ≠ (n : ℝ)) →
      ‖modFiveSmoothedPsi χ x‖ ≤
        4 * Real.pi * C * Real.log (T + 2) ^ 2 * x ^ (1 - a / Real.log (T + 2)) +
          4 * C * Real.log (T + 2) ^ 2 * x ^ (1 + δ) / T ^ 2 +
          2 * (1 / δ + D) * x ^ (1 + δ) / T := by
  obtain ⟨a, C, ha, ha4, hC, hfinite⟩ := modFive_finite_perron_shift
  obtain ⟨D, hD, htail⟩ := modFive_perron_tail_bound
  refine ⟨a, C, D, ha, ha4, hC, hD, ?_⟩
  intro χ hχ T x δ hT hx hδ hδ1 hxnat
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hH : 0 < Real.log (T + 2) := Real.log_pos (by linarith)
  have hleft : 1 - a / Real.log (T + 2) ≤ 1 + δ := by
    have hd := div_nonneg ha.le hH.le
    linarith
  have hfin := hfinite χ hχ T x (1 + δ) hT hx hleft (by linarith)
  have hta := htail χ hχ δ x T hδ hxpos (by linarith)
  have hlength : 1 + δ - (1 - a / Real.log (T + 2)) ≤ 2 := by
    have hlog : 1 / 2 ≤ Real.log (T + 2) := by
      simpa only [abs_of_nonneg (by linarith : 0 ≤ T)] using modFive_log_height_ge_half T
    have hdiv : a / Real.log (T + 2) ≤ 1 := (div_le_one hH).mpr (by linarith)
    linarith
  have hfin' : ‖VIntegral (modFivePerronIntegrand χ x) (1 + δ) (-T) T‖ ≤
      4 * Real.pi * C * Real.log (T + 2) ^ 2 * x ^ (1 - a / Real.log (T + 2)) +
        4 * C * Real.log (T + 2) ^ 2 * x ^ (1 + δ) / T ^ 2 := by
    apply hfin.trans
    apply add_le_add le_rfl
    calc
      _ ≤ 2 * 2 * (C * Real.log (T + 2) ^ 2 * x ^ (1 + δ) / T ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlength (by norm_num))
          (by positivity)
      _ = _ := by ring
  have hvert : ‖VerticalIntegral (modFivePerronIntegrand χ x) (1 + δ)‖ ≤
      ‖VIntegral (modFivePerronIntegrand χ x) (1 + δ) (-T) T‖ +
        2 * (1 / δ + D) * x ^ (1 + δ) / T := by
    exact (norm_le_insert' _ _).trans (add_le_add le_rfl hta)
  rw [modFiveSmoothedPsi_perron χ hxpos (by linarith : 1 < 1 + δ) hxnat]
  change ‖(1 / (2 * Real.pi * Complex.I)) •
    VerticalIntegral (modFivePerronIntegrand χ x) (1 + δ)‖ ≤ _
  rw [norm_smul]
  calc
    _ ≤ ‖VerticalIntegral (modFivePerronIntegrand χ x) (1 + δ)‖ :=
      (mul_le_mul_of_nonneg_right modFive_perron_normalization (norm_nonneg _)).trans_eq
        (one_mul _)
    _ ≤ _ := hvert.trans (add_le_add hfin' le_rfl)

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.modFive_smoothed_contour_bound := @OAI.TwoPointCorrelations.modFive_smoothed_contour_bound
