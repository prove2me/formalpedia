-- Prove2me | solution 1 for OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.strip_logderiv
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:56:41.476123+00:00
-- url     : https://prove2.me/submissions/37b791f3-1851-4433-a9d6-0c157337ddbb

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_Erdos970_lem_analytic_zero_factor
import Theorems.Thm_Erdos970_lem_sum_m_rho_bound
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_disk_logderiv
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_moving_zero_free

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Basic
namespace OAI

/-!
# Ordinary two-point correlations: concrete sums and affine transfer

Definitions follow the introduction of the supplied manuscript
*Ordinary two-point correlations of multiplicative functions* (September 24, 2026).
The exact Liouville identities below are the algebraic part of §8.
No cancellation estimate is assumed or asserted here.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations







@[simp] theorem liouville_mul (m n : ℕ) :
    liouville (m * n) = liouville m * liouville n := by
  simp [liouville, ArithmeticFunction.liouville_apply_mul]

@[simp] theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : liouville n ^ 2 = 1 := by
  have h : (ArithmeticFunction.liouville n) ^ 2 = (1 : ℤ) := by
    rw [ArithmeticFunction.liouville_apply hn, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  unfold liouville
  exact_mod_cast h





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
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MertensClassical
namespace Erdos970


namespace Real

open _root_.Real _root_.Filter _root_.Asymptotics



end Real

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology




end Issue1584

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open ArithmeticFunction hiding log













































attribute [fun_prop] measurable_from_top












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












































end Mertens

end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterCenterBounds
namespace OAI

/-! The Mobius inverse bounds the reciprocal L-function on Re(s)=2
uniformly in the modulus. Combining this with the q-dependent Abel bound
gives growth of the normalized nonprincipal character L-function on a
fixed disk. No zero-free region is asserted here. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.ArithmeticFunction
open scoped _root_.BigOperators _root_.Classical _root_.LSeries.notation _root_.ArithmeticFunction.Moebius

variable {q : ℕ} [NeZero q]



omit [NeZero q] in
lemma mrtCharacter_twisted_moebius_norm (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖χ (n : ZMod q) * ((μ n : ℤ) : ℂ)‖ ≤ 1 := by
  rw [norm_mul]
  have hμ : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (show |μ n| ≤ 1 from abs_moebius_le_one)
  exact (mul_le_mul (χ.norm_le_one _) hμ (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)







end TwoPointCorrelations

end OAI

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterLogGrowth
namespace OAI

/-! One absolute constant in the nonprincipal disk bounds, with all
modulus and height dependence kept in log(q*(abs(t)+2)). -/

namespace TwoPointCorrelations







lemma mrtCharacterLogDerivativeConstant_pos : 0 < mrtCharacterLogDerivativeConstant := by
  have hl : 0 < Real.log ((15/16:ℝ)/(7/8)) := Real.log_pos (by norm_num)
  unfold mrtCharacterLogDerivativeConstant
  positivity



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTAdaptiveDisk
namespace OAI

/-! A local analytic disk estimate with an explicit logarithmic growth budget.
The statement is independent of the physical radius, so it can be used on the
shrinking disks required by a Vinogradov--Korobov growth estimate. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Filter
open scoped _root_.BigOperators _root_.Classical _root_.Topology



private lemma mrt_disk_factorization (f : ℂ → ℂ)
    (hf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h0 : f 0 = 1) :
    ∃ g : ℂ → ℂ → ℂ, ∀ ρ ∈ mrtDiskZeros f,
      AnalyticAt ℂ (g ρ) ρ ∧ g ρ ρ ≠ 0 ∧
        ∀ᶠ w in 𝓝 ρ, f w = (w - ρ) ^ (analyticOrderAt f ρ).toNat * g ρ w := by
  have hfactor : ∀ ρ : ℂ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      (ρ ∈ mrtDiskZeros f →
        ∀ᶠ w in 𝓝 ρ, f w = (w - ρ) ^ (analyticOrderAt f ρ).toNat * g w) := by
    intro ρ
    by_cases hρ : ρ ∈ mrtDiskZeros f
    · obtain ⟨g, hg, hgne, heq⟩ := Erdos970.lem_analytic_zero_factor
        (15 / 16) (7 / 8) (by norm_num) (by norm_num) (by norm_num) f hf
        (by rw [h0]; exact one_ne_zero) ρ hρ
      exact ⟨g, hg, hgne, fun _ => heq⟩
    · exact ⟨fun _ => 1, analyticAt_const, one_ne_zero, fun h => (hρ h).elim⟩
  exact ⟨fun ρ => Classical.choose (hfactor ρ), fun ρ hρ =>
    ⟨(Classical.choose_spec (hfactor ρ)).1,
      (Classical.choose_spec (hfactor ρ)).2.1,
      (Classical.choose_spec (hfactor ρ)).2.2 hρ⟩⟩


/-- The total multiplicity in the inner disk has the same logarithmic cost. -/
theorem mrt_disk_zero_count (f : ℂ → ℂ)
    (hf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h0 : f 0 = 1) {B : ℝ} (hB : 0 < B)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16), ‖f z‖ ≤ Real.exp B) :
    (∑ ρ ∈ (mrtDiskZeros_finite f hf h0).toFinset,
      ((analyticOrderAt f ρ).toNat : ℝ)) ≤
      (1 / Real.log ((15 / 16 : ℝ) / (7 / 8))) * B := by
  obtain ⟨g, hg⟩ := mrt_disk_factorization f hf h0
  have h := Erdos970.lem_sum_m_rho_bound (Real.exp B) (15 / 16) (7 / 8)
    (Real.one_lt_exp_iff.mpr hB) (by norm_num) (by norm_num) (by norm_num) f hf
    (by rw [h0]; exact one_ne_zero) h0 (mrtDiskZeros_finite f hf h0) g (fun z hz => hbound z (by simpa using hz)) hg
  simpa only [mrtDiskZeros, Real.log_exp] using h

/-- A zero separation estimate completes the local norm bound. -/
theorem mrt_disk_logderiv_norm (f : ℂ → ℂ)
    (hf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h0 : f 0 = 1) {B : ℝ} (hB : 0 < B)
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16), ‖f z‖ ≤ Real.exp B)
    {z : ℂ} (hz : ‖z‖ ≤ 3 / 4) (hn : f z ≠ 0)
    {η : ℝ} (hη : 0 < η)
    (hd : ∀ ρ ∈ mrtDiskZeros f, η ≤ ‖z - ρ‖) :
    ‖deriv f z / f z‖ ≤
      (mrtCharacterLogDerivativeConstant +
        (1 / Real.log ((15 / 16 : ℝ) / (7 / 8))) / η) * B := by
  let S := (mrtDiskZeros_finite f hf h0).toFinset
  let m : ℂ → ℕ := fun ρ => (analyticOrderAt f ρ).toNat
  have hs : ‖∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ)‖ ≤ (∑ ρ ∈ S, (m ρ : ℝ)) / η := by
    calc
      _ ≤ ∑ ρ ∈ S, ‖(m ρ : ℂ) / (z - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ S, (m ρ : ℝ) / η := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hη
          (hd ρ ((mrtDiskZeros_finite f hf h0).mem_toFinset.mp hρ))
      _ = _ := by rw [Finset.sum_div]
  have hc := div_le_div_of_nonneg_right (mrt_disk_zero_count f hf h0 hB hbound) hη.le
  have he := mrt_disk_logderiv f hf h0 hB hbound hz hn
  have ht := norm_add_le
    (deriv f z / f z - ∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ))
    (∑ ρ ∈ S, (m ρ : ℂ) / (z - ρ))
  rw [sub_add_cancel] at ht
  calc
    _ ≤ mrtCharacterLogDerivativeConstant * B +
        ((1 / Real.log ((15 / 16 : ℝ) / (7 / 8))) * B) / η :=
      ht.trans (add_le_add he (hs.trans hc))
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterMovingCenter
namespace OAI

/-! Normalization of Dirichlet L-functions on a moving disk. The radius is
an explicit parameter; all characters, including the principal character,
are allowed when the disk stays away from the real axis. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Filter
open scoped _root_.BigOperators _root_.Classical _root_.Topology

variable {q : ℕ} [NeZero q]



lemma mrt_moving_point_ne_one {r t : ℝ} (hr : 0 < r) (ht : 3 * r < |t|)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : mrtMovingPoint r t z ≠ 1 := by
  intro he
  have him := congrArg Complex.im he
  have him' : t + 3 * r * z.im = 0 := by
    simpa [mrtMovingPoint, Complex.mul_im] using him
  have hzi := (Complex.abs_im_le_norm z).trans hz
  have heq : t = -(3 * r * z.im) := by linarith
  rw [heq, abs_neg, abs_mul, abs_of_pos (by positivity : 0 < 3 * r)] at ht
  nlinarith

lemma mrt_moving_point_center_ne_zero (χ : DirichletCharacter ℂ q)
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    DirichletCharacter.LFunction χ (mrtMovingPoint r t 0) ≠ 0 := by
  apply χ.LFunction_ne_zero_of_one_le_re
  · right
    intro h
    have hh := congrArg Complex.re h
    simp [mrtMovingPoint] at hh
    linarith
  · simp [mrtMovingPoint]
    linarith

lemma mrt_moving_LFunction_zero (χ : DirichletCharacter ℂ q)
    {r : ℝ} (hr : 0 < r) (t : ℝ) : mrtMovingLFunction χ r t 0 = 1 :=
  div_self (mrt_moving_point_center_ne_zero χ hr t)

lemma mrt_moving_LFunction_analytic (χ : DirichletCharacter ℂ q)
    {r t : ℝ} (hr : 0 < r) (ht : 3 * r < |t|) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ (mrtMovingLFunction χ r t) z := by
  intro z hz
  have hn := mrt_moving_point_ne_one hr ht (by simpa using hz)
  have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) := by
    intro w hw
    exact (χ.differentiableAt_LFunction w (Or.inl hw)).differentiableWithinAt
  have ha := hd.analyticAt (isOpen_compl_singleton.mem_nhds hn)
  have hp : AnalyticAt ℂ (mrtMovingPoint r t) z := by
    apply Differentiable.analyticAt
    unfold mrtMovingPoint
    fun_prop
  exact (ha.comp hp).div_const

lemma mrt_moving_LFunction_growth (χ : DirichletCharacter ℂ q)
    {r t A V B : ℝ}
    (hA : 0 ≤ A)
    (hg : ∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
      ‖DirichletCharacter.LFunction χ (mrtMovingPoint r t z)‖ ≤ A)
    (hi : ‖(DirichletCharacter.LFunction χ (mrtMovingPoint r t 0))⁻¹‖ ≤ V)
    (hB : A * V ≤ Real.exp B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
      ‖mrtMovingLFunction χ r t z‖ ≤ Real.exp B := by
  intro z hz
  unfold mrtMovingLFunction
  rw [div_eq_mul_inv, norm_mul]
  exact (mul_le_mul (hg z hz) hi (norm_nonneg _) hA).trans hB

lemma mrt_moving_LFunction_deriv (χ : DirichletCharacter ℂ q)
    {r t : ℝ} (hr : 0 < r) (ht : 3 * r < |t|)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    deriv (mrtMovingLFunction χ r t) z =
      (deriv (DirichletCharacter.LFunction χ) (mrtMovingPoint r t z) *
        ((3 * r : ℝ) : ℂ)) /
        DirichletCharacter.LFunction χ (mrtMovingPoint r t 0) := by
  have hp : HasDerivAt (mrtMovingPoint r t) ((3 * r : ℝ) : ℂ) z := by
    exact (hasDerivAt_const_mul ((3 * r : ℝ) : ℂ)).const_add
      (((1 + 2 * r : ℝ) : ℂ) + Complex.I * (t : ℂ))
  have hn := mrt_moving_point_ne_one hr ht hz
  exact (((χ.differentiableAt_LFunction _ (Or.inl hn)).hasDerivAt.comp z hp).div_const
    (DirichletCharacter.LFunction χ (mrtMovingPoint r t 0))).deriv

lemma mrt_moving_logderiv_eq (χ : DirichletCharacter ℂ q)
    {r t : ℝ} (hr : 0 < r) (ht : 3 * r < |t|)
    {z : ℂ} (hz : ‖z‖ ≤ 1)
    (hn : DirichletCharacter.LFunction χ (mrtMovingPoint r t z) ≠ 0) :
    deriv (mrtMovingLFunction χ r t) z / mrtMovingLFunction χ r t z =
      ((3 * r : ℝ) : ℂ) *
        (deriv (DirichletCharacter.LFunction χ) (mrtMovingPoint r t z) /
          DirichletCharacter.LFunction χ (mrtMovingPoint r t z)) := by
  rw [mrt_moving_LFunction_deriv χ hr ht hz]
  unfold mrtMovingLFunction
  field_simp [hn, mrt_moving_point_center_ne_zero χ hr t]

/-- A separated normalized zero set bounds the actual logarithmic derivative.
The factor `1/(3r)` is the only cost of changing the disk radius. -/
theorem mrt_moving_logderiv_norm (χ : DirichletCharacter ℂ q)
    {r t B η : ℝ} (hr : 0 < r) (ht : 3 * r < |t|) (hB : 0 < B)
    (hg : ∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
      ‖mrtMovingLFunction χ r t z‖ ≤ Real.exp B)
    {z : ℂ} (hz : ‖z‖ ≤ 3 / 4)
    (hn : DirichletCharacter.LFunction χ (mrtMovingPoint r t z) ≠ 0)
    (hη : 0 < η)
    (hd : ∀ ρ ∈ mrtDiskZeros (mrtMovingLFunction χ r t), η ≤ ‖z - ρ‖) :
    ‖deriv (DirichletCharacter.LFunction χ) (mrtMovingPoint r t z) /
      DirichletCharacter.LFunction χ (mrtMovingPoint r t z)‖ ≤
      ((mrtCharacterLogDerivativeConstant +
        (1 / Real.log ((15 / 16 : ℝ) / (7 / 8))) / η) * B) / (3 * r) := by
  have hf := mrt_moving_LFunction_analytic χ hr ht
  have h0 := mrt_moving_LFunction_zero χ hr t
  have hfn : mrtMovingLFunction χ r t z ≠ 0 :=
    div_ne_zero hn (mrt_moving_point_center_ne_zero χ hr t)
  have hh := mrt_disk_logderiv_norm _ hf h0 hB hg hz hfn hη hd
  rw [mrt_moving_logderiv_eq χ hr ht (hz.trans (by norm_num)) hn, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 3 * r)] at hh
  exact (le_div_iff₀ (by positivity : 0 < 3 * r)).mpr (by nlinarith only [hh])

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMovingInverse
namespace OAI

/-! The center normalization on shrinking disks costs only the reciprocal
radius. This uses the absolutely convergent Möbius inverse and the proved
residue of the Riemann zeta function; no zero-free hypothesis is used. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.ArithmeticFunction _root_.Filter
open scoped _root_.BigOperators _root_.Classical _root_.Topology _root_.LSeries.notation _root_.ArithmeticFunction.Moebius

variable {q : ℕ} [NeZero q]

lemma mrt_character_inverse_real_majorant (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    ‖(DirichletCharacter.LFunction χ s)⁻¹‖ ≤
      ∑' n : ℕ, 1 / (n : ℝ) ^ s.re := by
  have hm := χ.LSeriesSummable_mul (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  have hb : Summable (fun n : ℕ => 1 / (n : ℝ) ^ s.re) := by
    have hh := (LSeriesSummable_one_iff.mpr
      (show 1 < (s.re : ℂ).re by simpa using hs)).norm
    convert (preTransparency := .instances) hh using 1
    funext n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · simp [hn, Real.zero_rpow (show s.re ≠ 0 by linarith)]
    · simp [hn]
  have heq := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hne := χ.LSeries_ne_zero_of_one_lt_re hs
  have hi : (LSeries (fun n => χ (n : ZMod q)) s)⁻¹ =
      LSeries (fun n => χ (n : ZMod q) * ((μ n : ℤ) : ℂ)) s := by
    apply mul_left_cancel₀ hne
    simpa only [mul_inv_cancel₀ hne, Pi.mul_def] using heq.symm
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs, hi]
  calc
    _ ≤ ∑' n : ℕ, ‖LSeries.term
        (fun n => χ (n : ZMod q) * ((μ n : ℤ) : ℂ)) s n‖ :=
      norm_tsum_le_tsum_norm hm.norm
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ s.re := by
      apply Summable.tsum_le_tsum (fun n => ?_) hm.norm hb
      rw [LSeries.norm_term_eq]
      split_ifs with hn
      · exact div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      · exact div_le_div_of_nonneg_right (mrtCharacter_twisted_moebius_norm χ n)
          (Real.rpow_nonneg n.cast_nonneg _)

/-- The local center reciprocal has an absolute radius threshold, independent
of the modulus, character and height. -/
theorem mrt_moving_center_inverse : ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 / 4 ∧
    ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ (q : ℕ) [NeZero q],
      ∀ (χ : DirichletCharacter ℂ q) (t : ℝ),
        ‖(DirichletCharacter.LFunction χ (mrtMovingPoint r t 0))⁻¹‖ ≤ 1 / r := by
  have he := tendsto_sub_mul_tsum_nat_rpow.eventually
    (gt_mem_nhds (show (1 : ℝ) < 2 by norm_num))
  obtain ⟨ε, hε, hlocal⟩ := Metric.mem_nhdsWithin_iff.mp he
  refine ⟨min (ε / 4) (1 / 4), lt_min (by positivity) (by norm_num), min_le_right _ _, ?_⟩
  intro r hr hrr q _ χ t
  have hrε : r ≤ ε / 4 := hrr.trans (min_le_left _ _)
  have hnear : (1 + 2 * r : ℝ) ∈ Metric.ball 1 ε := by
    rw [Metric.mem_ball, Real.dist_eq, show 1 + 2 * r - 1 = 2 * r by ring,
      abs_of_pos (by positivity : 0 < 2 * r)]
    linarith
  have hright : 1 + 2 * r ∈ Set.Ioi (1 : ℝ) := by simp; linarith
  have ht := hlocal ⟨hnear, hright⟩
  have hs : 1 < (mrtMovingPoint r t 0).re := by simp [mrtMovingPoint]; linarith
  have hb := mrt_character_inverse_real_majorant χ hs
  have hre : (mrtMovingPoint r t 0).re = 1 + 2 * r := by simp [mrtMovingPoint]
  rw [hre] at hb
  apply hb.trans
  apply (le_div_iff₀ hr).mpr
  change (1 + 2 * r - 1) * (∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 2 * r)) < 2 at ht
  have ht' : 2 * r * (∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 2 * r)) < 2 := by
    simpa only [show 1 + 2 * r - 1 = 2 * r by ring] using ht
  nlinarith only [ht']

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMovingZeroTerms
namespace OAI

/-! The one-zero de la Vallée Poussin estimate on a shrinking disk.
All constants retain the physical radius and logarithmic growth budget. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset
open scoped _root_.BigOperators _root_.Classical

variable {q : ℕ} [NeZero q]


lemma mrt_moving_real_point {r : ℝ} (hr : 0 < r) (t σ : ℝ) :
    mrtMovingPoint r t (mrtMovingRealPoint r σ) = (σ : ℂ) + Complex.I * (t : ℂ) := by
  unfold mrtMovingPoint mrtMovingRealPoint
  push_cast
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp [hrC]
  ring

lemma mrt_moving_real_point_norm {r σ : ℝ} (hr : 0 < r)
    (hσ : 1 - r / 4 ≤ σ) (hσ2 : σ ≤ 1 + r) :
    ‖mrtMovingRealPoint r σ‖ ≤ 3 / 4 := by
  rw [mrtMovingRealPoint, Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 3 * r)).mpr
    nlinarith
  · apply (div_le_iff₀ (by positivity : 0 < 3 * r)).mpr
    nlinarith

lemma mrt_moving_zero_physical (χ : DirichletCharacter ℂ q)
    {r t : ℝ} (hr : 0 < r) {ρ : ℂ}
    (hρ : ρ ∈ mrtDiskZeros (mrtMovingLFunction χ r t)) :
    DirichletCharacter.LFunction χ (mrtMovingPoint r t ρ) = 0 := by
  exact (div_eq_zero_iff.mp hρ.2).resolve_right (mrt_moving_point_center_ne_zero χ hr t)




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeakHurwitzGrowth
namespace OAI

/-! Weak Vinogradov--Korobov growth for the Hurwitz zeta function with
its first term removed, and the finite-character reduction. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset _root_.HurwitzZeta
open scoped _root_.Classical





lemma mrt_hurwitz_first_term_bound {q : ℕ} [NeZero q] (j : ZMod q)
    {s : ℂ} (hs : s.re ≤ 2) :
    ‖mrtHurwitzFirstTerm ((j.val : ℝ) / q) s‖ ≤ (q : ℝ) ^ 2 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have ha : (j.val : ℝ) / q ≤ 1 := by
    exact (div_le_one hq).mpr (by exact_mod_cast (ZMod.val_lt j).le)
  by_cases hj : j.val = 0
  · simp [mrtHurwitzFirstTerm, hj]
  have hjp : (0 : ℝ) < j.val := by exact_mod_cast Nat.pos_of_ne_zero hj
  have ha0 : 0 < (j.val : ℝ) / q := div_pos hjp hq
  have hlo : 1 / (q : ℝ) ≤ (j.val : ℝ) / q :=
    div_le_div_of_nonneg_right (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj) hq.le
  rw [mrtHurwitzFirstTerm, if_neg ha0.ne', Complex.norm_cpow_eq_rpow_re_of_pos ha0,
    Complex.neg_re]
  calc
    _ ≤ ((j.val : ℝ) / q) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge ha0 ha (by linarith)
    _ ≤ (1 / (q : ℝ)) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hlo (by norm_num)
    _ = (q : ℝ) ^ 2 := by norm_num [Real.rpow_neg (by positivity : 0 ≤ 1 / (q : ℝ)),
      Real.rpow_two, one_div]

/-- Exact finite Hurwitz decomposition retains a polynomial modulus cost. -/
theorem mrt_character_of_hurwitz_growth {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} {A : ℝ}
    (hσ : 0 ≤ s.re) (hσ2 : s.re ≤ 2)
    (hh : ∀ a ∈ Set.Icc (0 : ℝ) 1,
      ‖hurwitzZeta (a : UnitAddCircle) s - mrtHurwitzFirstTerm a s‖ ≤ A) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ (q : ℝ) * ((q : ℝ) ^ 2 + A) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hb (j : ZMod q) :
      ‖hurwitzZeta (ZMod.toAddCircle j) s‖ ≤ (q : ℝ) ^ 2 + A := by
    have ha : (j.val : ℝ) / q ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one (by positivity : (0 : ℝ) < q)).mpr
        (by exact_mod_cast (ZMod.val_lt j).le)⟩
    have he := norm_add_le
      (hurwitzZeta (((j.val : ℝ) / (q : ℝ)) : UnitAddCircle) s -
        mrtHurwitzFirstTerm ((j.val : ℝ) / q) s)
      (mrtHurwitzFirstTerm ((j.val : ℝ) / q) s)
    rw [sub_add_cancel] at he
    rw [ZMod.toAddCircle_apply]
    exact he.trans (by linarith [hh _ ha, mrt_hurwitz_first_term_bound j hσ2])
  have hpow : ‖(q : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos
      (by positivity : (0 : ℝ) < q), Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hq (by linarith)
  unfold DirichletCharacter.LFunction ZMod.LFunction
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖∑ j : ZMod q, χ j * hurwitzZeta (ZMod.toAddCircle j) s‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ ≤ ∑ j : ZMod q, ‖χ j * hurwitzZeta (ZMod.toAddCircle j) s‖ := by
      simpa only [one_mul] using norm_sum_le (Finset.univ) _
    _ ≤ ∑ _j : ZMod q, ((q : ℝ) ^ 2 + A) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      calc
        _ ≤ 1 * ((q : ℝ) ^ 2 + A) := mul_le_mul (χ.norm_le_one _) (hb j)
          (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    _ = (q : ℝ) * ((q : ℝ) ^ 2 + A) := by simp [mul_add]

lemma mrt_moving_point_region {r t : ℝ} (hr : 0 ≤ r)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    1 - r ≤ (mrtMovingPoint r t z).re ∧
      (mrtMovingPoint r t z).re ≤ 1 + 5 * r ∧
      |(mrtMovingPoint r t z).im - t| ≤ 3 * r := by
  have hre := abs_le.mp ((Complex.abs_re_le_norm z).trans hz)
  have him := (Complex.abs_im_le_norm z).trans hz
  simp only [mrtMovingPoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_zero,
    Complex.add_im, Complex.mul_im, zero_add]
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  rw [add_sub_cancel_left, add_zero, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 3 * r)]
  nlinarith


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMovingGrowth
namespace OAI

/-! Normalize the weak Hurwitz growth bound without losing a power of the
height. The logarithmic disk budget is O(1+log q+loglog |t|), uniformly in q. -/

namespace TwoPointCorrelations

open _root_.Complex
open scoped _root_.Classical


lemma mrt_moving_growth_budget {x H C : ℝ} (hx : 1 ≤ x) (hH : 1 ≤ H) (hC : 0 < C) :
    x * (x ^ 2 + H ^ C) * H ^ (2 / 3 : ℝ) ≤
      Real.exp ((C + 4) * (1 + Real.log x + Real.log H)) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hHC : 1 ≤ H ^ C := Real.one_le_rpow hH hC.le
  have hx3 : x ≤ x ^ 3 := by
    have hm := mul_nonneg (sub_nonneg.mpr hx) (show 0 ≤ x * (x + 1) by positivity)
    nlinarith only [hm]
  have hx30 : 0 ≤ x ^ 3 := pow_nonneg hx0.le _
  have ha : x * (x ^ 2 + H ^ C) ≤ 2 * x ^ 3 * H ^ C := by
    have ha1 := mul_le_mul_of_nonneg_left hHC hx30
    have ha2 := mul_le_mul_of_nonneg_right hx3 (Real.rpow_nonneg hH0.le C)
    nlinarith only [ha1, ha2]
  have hxpow : x ^ 3 ≤ x ^ (C + 4) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hx
    norm_num
    linarith
  have hHpow : H ^ (C + 2 / 3) ≤ H ^ (C + 4) :=
    Real.rpow_le_rpow_of_exponent_le hH (by linarith)
  have hE : 2 ≤ Real.exp (C + 4) := by linarith [Real.add_one_le_exp (C + 4)]
  have he : Real.exp ((C + 4) * (1 + Real.log x + Real.log H)) =
      Real.exp (C + 4) * x ^ (C + 4) * H ^ (C + 4) := by
    rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hH0,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ (2 * x ^ 3 * H ^ C) * H ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hH0.le _)
    _ = 2 * x ^ 3 * H ^ (C + 2 / 3) := by rw [Real.rpow_add hH0]; ring
    _ ≤ Real.exp (C + 4) * x ^ (C + 4) * H ^ (C + 4) := by
      exact mul_le_mul (mul_le_mul hE hxpow hx30 (Real.exp_nonneg _)) hHpow
        (Real.rpow_nonneg hH0.le _) (by positivity)
    _ = _ := he.symm

lemma mrt_VKWeight_ge_one {q : ℕ} [NeZero q] {t : ℝ} (hH : 1 ≤ mrtVKLog t) :
    1 ≤ mrtVKWeight q t := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  unfold mrtVKWeight
  linarith [Real.log_nonneg hq, Real.log_nonneg hH]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMovingGrowthWindow
namespace OAI

/-! The same weak Hurwitz estimate controls all nearby character disks.
Using radius R(2t)/16 leaves room for both the first and doubled heights. -/

namespace TwoPointCorrelations

open _root_.Complex
open scoped _root_.Classical

lemma mrt_VKLog_pos (t : ℝ) : 0 < mrtVKLog t :=
  Real.log_pos (by linarith [abs_nonneg t])

lemma mrt_VKLog_double (t : ℝ) : mrtVKLog t ≤ mrtVKLog (2 * t) := by
  apply Real.log_le_log (by positivity : 0 < |t| + 3)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith [abs_nonneg t]

lemma mrt_VKRadius_double (t : ℝ) : mrtVKRadius (2 * t) ≤ mrtVKRadius t := by
  exact Real.rpow_le_rpow_of_nonpos (mrt_VKLog_pos t) (mrt_VKLog_double t) (by norm_num)

lemma mrt_moving_shifted_region {r R v t : ℝ} (hr : 0 ≤ r) (hR : r ≤ R)
    (hshift : 3 * r + |v - t| ≤ 3 * R) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    1 - R ≤ (mrtMovingPoint r v z).re ∧
      (mrtMovingPoint r v z).re ≤ 1 + 5 * R ∧
      |(mrtMovingPoint r v z).im - t| ≤ 3 * R := by
  have hreg := mrt_moving_point_region (t := v) hr hz
  refine ⟨by linarith [hreg.1], by linarith [hreg.2.1], ?_⟩
  calc
    _ = |((mrtMovingPoint r v z).im - v) + (v - t)| := by congr 1; ring
    _ ≤ |(mrtMovingPoint r v z).im - v| + |v - t| := abs_add_le _ _
    _ ≤ 3 * r + |v - t| := add_le_add_left hreg.2.2 _
    _ ≤ _ := hshift

/-- The actual nearby disks satisfy a common logarithmic growth budget;
there is no independent regularity-in-height premise. -/
theorem MRTWeakHurwitzGrowthInput.local_disks (h : MRTWeakHurwitzGrowthInput) :
    ∃ D T r₀ : ℝ, 1 ≤ D ∧ 0 < T ∧ 0 < r₀ ∧ r₀ ≤ 1 / 5 ∧
      ∀ t : ℝ, T ≤ |t| → 1 ≤ mrtVKLog (2 * t) →
        mrtVKRadius (2 * t) / 16 ≤ r₀ →
        ∀ (q : ℕ) [NeZero q], ∀ (χ : DirichletCharacter ℂ q),
        ∀ v : ℝ, |v - t| ≤ 3 * (mrtVKRadius (2 * t) / 16) →
          (∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
            ‖mrtMovingLFunction χ (mrtVKRadius (2 * t) / 16) v z‖ ≤
              Real.exp (D * mrtVKWeight q (2 * t))) ∧
          (∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
            ‖mrtMovingLFunction (χ ^ 2) (mrtVKRadius (2 * t) / 16) (2 * v) z‖ ≤
              Real.exp (D * mrtVKWeight q (2 * t))) := by
  obtain ⟨C, T, hC, hT, hg⟩ := h
  obtain ⟨r₀, hr₀, _, hi⟩ := mrt_moving_center_inverse
  have hl16 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
  refine ⟨C + 4 + Real.log 16, T, min r₀ (1 / 5), by linarith, hT,
    lt_min hr₀ (by norm_num), min_le_right _ _, ?_⟩
  intro t ht hH hr q _ χ v hv
  let H := mrtVKLog (2 * t)
  let r := mrtVKRadius (2 * t) / 16
  let A := (q : ℝ) * ((q : ℝ) ^ 2 + H ^ C)
  have hH0 : 0 < H := mrt_VKLog_pos (2 * t)
  have hrp : 0 < r := div_pos (Real.rpow_pos_of_pos hH0 _) (by norm_num)
  have hrsmall : r ≤ 1 / 5 := hr.trans (min_le_right _ _)
  have hrR2 : r ≤ mrtVKRadius (2 * t) := by
    have hR : 0 < mrtVKRadius (2 * t) := Real.rpow_pos_of_pos hH0 _
    dsimp [r]
    linarith
  have hrR : r ≤ mrtVKRadius t := hrR2.trans (mrt_VKRadius_double t)
  have ht2 : T ≤ |2 * t| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg t]
  have hraw (ψ : DirichletCharacter ℂ q) (w u : ℝ)
      (hu : T ≤ |u|) (hru : r ≤ mrtVKRadius u)
      (hshift : 3 * r + |w - u| ≤ 3 * mrtVKRadius u)
      (hHu : mrtVKLog u ≤ H) :
      ∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
        ‖DirichletCharacter.LFunction ψ (mrtMovingPoint r w z)‖ ≤ A := by
    intro z hz
    have hzn : ‖z‖ ≤ 1 := by
      have hh : ‖z‖ ≤ 15 / 16 := by simpa using hz
      linarith
    have hreg := mrt_moving_shifted_region hrp.le hru hshift hzn
    have hown := mrt_moving_point_region (t := w) hrp.le hzn
    apply mrt_character_of_hurwitz_growth ψ (by linarith [hown.1])
      (by linarith [hown.2.1])
    intro a ha
    exact (hg u hu a ha _ hreg.1 hreg.2.1 hreg.2.2).trans
      (Real.rpow_le_rpow (mrt_VKLog_pos u).le hHu hC.le)
  have hraw1 := hraw χ v t ht hrR (by
    change |v - t| ≤ 3 * r at hv
    have hRR := mrt_VKRadius_double t
    have heR : 16 * r = mrtVKRadius (2 * t) := by dsimp [r]; ring
    nlinarith) (mrt_VKLog_double t)
  have hshift2 : 3 * r + |2 * v - 2 * t| ≤ 3 * mrtVKRadius (2 * t) := by
    have he : 2 * v - 2 * t = 2 * (v - t) := by ring
    rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    change |v - t| ≤ 3 * r at hv
    have heR : 16 * r = mrtVKRadius (2 * t) := by dsimp [r]; ring
    nlinarith
  have hraw2 := hraw (χ ^ 2) (2 * v) (2 * t) ht2 hrR2 hshift2 le_rfl
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hw : 1 ≤ mrtVKWeight q (2 * t) := mrt_VKWeight_ge_one hH
  have hbudget := mrt_moving_growth_budget hq hH hC
  have hrinv : r⁻¹ = 16 * H ^ (2 / 3 : ℝ) := by
    change (mrtVKRadius (2 * t) / 16)⁻¹ = _
    rw [inv_div, div_eq_mul_inv, mrtVKRadius, Real.rpow_neg hH0.le, inv_inv]
  have hprod : A * (1 / r) ≤
      Real.exp ((C + 4 + Real.log 16) * mrtVKWeight q (2 * t)) := by
    rw [one_div, hrinv]
    calc
      _ = 16 * ((q : ℝ) * ((q : ℝ) ^ 2 + H ^ C) * H ^ (2 / 3 : ℝ)) := by dsimp [A]; ring
      _ ≤ 16 * Real.exp ((C + 4) * mrtVKWeight q (2 * t)) := by
        exact mul_le_mul_of_nonneg_left hbudget (by norm_num)
      _ = Real.exp (Real.log 16 + (C + 4) * mrtVKWeight q (2 * t)) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg hl16 (sub_nonneg.mpr hw)])
  constructor
  · exact mrt_moving_LFunction_growth χ (by dsimp [A]; positivity) hraw1
      (hi r hrp (hr.trans (min_le_left _ _)) q χ v) hprod
  · exact mrt_moving_LFunction_growth (χ ^ 2) (by dsimp [A]; positivity) hraw2
      (hi r hrp (hr.trans (min_le_left _ _)) q (χ ^ 2) (2 * v)) hprod

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMovingStripNorm
namespace OAI

/-! The shrinking-disk estimate inside a narrower zero-free strip. This
extension to the left of one is used for the smoothed Mangoldt contour. -/

namespace TwoPointCorrelations

open _root_.Complex
open scoped _root_.Classical

theorem mrt_moving_strip_logderiv : ∃ c K r₀ : ℝ, 0 < c ∧ 0 < K ∧ 0 < r₀ ∧
    ∀ (q : ℕ) [NeZero q], ∀ (χ : DirichletCharacter ℂ q),
    ∀ (r t B σ : ℝ), 0 < r → r ≤ r₀ → 6 * r < |t| → 1 ≤ B →
      (∀ v : ℝ, |v - t| ≤ 3 * r →
        (∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
          ‖mrtMovingLFunction χ r v z‖ ≤ Real.exp B) ∧
        (∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
          ‖mrtMovingLFunction (χ ^ 2) r (2 * v) z‖ ≤ Real.exp B)) →
      1 - c * r / B ≤ σ → σ ≤ 1 + r →
        DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ)) ≠ 0 ∧
        ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (t : ℂ)) /
          DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ K * B ^ 2 / r := by
  obtain ⟨c₀, r₀, hc₀, hr₀, hstrip⟩ := mrt_moving_zero_free
  let d := min c₀ (1 / 2)
  let P := 1 / Real.log ((15 / 16 : ℝ) / (7 / 8))
  let K := mrtCharacterLogDerivativeConstant / 3 + 2 * P / d
  have hd : 0 < d := lt_min hc₀ (by norm_num)
  have hdc : d ≤ c₀ := min_le_left _ _
  have hdhalf : d ≤ 1 / 2 := min_le_right _ _
  have hP : 0 < P := by dsimp [P]; exact one_div_pos.mpr (Real.log_pos (by norm_num))
  have hK : 0 < K := by
    dsimp [K]
    exact add_pos (div_pos mrtCharacterLogDerivativeConstant_pos (by norm_num)) (by positivity)
  refine ⟨d / 2, K, r₀, by positivity, hK, hr₀, ?_⟩
  intro q _ χ r t B σ hr hrr ht hB hg hσ hσ2
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have ht3 : 3 * r < |t| := by linarith
  have hlocal := hg t (by simpa using (show 0 ≤ 3 * r by positivity))
  have hdelt : (d / 2) * r / B = (d * r / B) / 2 := by ring
  have hdcost : d * r / B ≤ c₀ * r / B :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hdc hr.le) hBp.le
  have hdz : 0 ≤ d * r / B := by positivity
  have hn : DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
    apply hstrip q χ r t B σ hr hrr ht3 hB hlocal.1 hlocal.2
    rw [hdelt] at hσ
    linarith
  have hrad : (d / 2) * r / B ≤ r / 4 := by
    have hnumer : (d / 2) * r ≤ r / 4 := by nlinarith
    exact (div_le_div_of_nonneg_right hnumer hBp.le).trans
      (div_le_self (by positivity) hB)
  have hz := mrt_moving_real_point_norm hr (by linarith) hσ2
  have hn' : DirichletCharacter.LFunction χ (mrtMovingPoint r t (mrtMovingRealPoint r σ)) ≠ 0 := by
    rwa [mrt_moving_real_point hr]
  have hsep : ∀ ρ ∈ mrtDiskZeros (mrtMovingLFunction χ r t),
      d / (6 * B) ≤ ‖mrtMovingRealPoint r σ - ρ‖ := by
    intro ρ hρ
    have hρn : ‖ρ‖ ≤ 7 / 8 := by simpa using hρ.1
    let v := (mrtMovingPoint r t ρ).im
    have hv : |v - t| ≤ 3 * r := by
      have hi := (Complex.abs_im_le_norm ρ).trans (hρn.trans (by norm_num : (7 / 8 : ℝ) ≤ 1))
      have he : v - t = 3 * r * ρ.im := by
        dsimp [v, mrtMovingPoint]
        simp only [Complex.ofReal_im, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, mul_zero, zero_add, add_zero]
        ring
      rw [he, abs_mul, abs_of_pos (by positivity : 0 < 3 * r)]
      nlinarith
    have hvt : 3 * r < |v| := by
      have hh := abs_add_le (t - v) v
      rw [sub_add_cancel, abs_sub_comm] at hh
      linarith
    have hβ : (mrtMovingPoint r t ρ).re < 1 - c₀ * r / B := by
      by_contra! hh
      have he : (((mrtMovingPoint r t ρ).re : ℝ) : ℂ) + Complex.I * (v : ℂ) =
          mrtMovingPoint r t ρ := by dsimp [v]; apply Complex.ext <;> simp
      apply hstrip q χ r v B (mrtMovingPoint r t ρ).re hr hrr hvt hB
        (hg v hv).1 (hg v hv).2 hh
      rw [he]
      exact mrt_moving_zero_physical χ hr hρ
    have hgap : (d * r / B) / 2 ≤ σ - (mrtMovingPoint r t ρ).re := by
      rw [hdelt] at hσ
      linarith
    have hre : (mrtMovingRealPoint r σ - ρ).re =
        (σ - (mrtMovingPoint r t ρ).re) / (3 * r) := by
      simp only [Complex.sub_re, mrtMovingRealPoint, Complex.ofReal_re, mrtMovingPoint,
        Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
        zero_mul, mul_zero, sub_zero]
      field_simp
      ring
    calc
      _ = ((d * r / B) / 2) / (3 * r) := by field_simp; norm_num
      _ ≤ (σ - (mrtMovingPoint r t ρ).re) / (3 * r) :=
        div_le_div_of_nonneg_right hgap (by positivity)
      _ = (mrtMovingRealPoint r σ - ρ).re := hre.symm
      _ ≤ |(mrtMovingRealPoint r σ - ρ).re| := le_abs_self _
      _ ≤ _ := Complex.abs_re_le_norm _
  have hh := mrt_moving_logderiv_norm χ hr ht3 hBp hlocal.1 hz hn'
    (show 0 < d / (6 * B) by positivity) hsep
  rw [mrt_moving_real_point hr] at hh
  refine ⟨hn, hh.trans ?_⟩
  change ((mrtCharacterLogDerivativeConstant + P / (d / (6 * B))) * B) / (3 * r) ≤ _
  have hmul : mrtCharacterLogDerivativeConstant * B ≤ mrtCharacterLogDerivativeConstant * B ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith : B ≤ B ^ 2) mrtCharacterLogDerivativeConstant_pos.le
  have heq : P / (d / (6 * B)) = 6 * P * B / d := by field_simp
  rw [heq]
  have halg : (mrtCharacterLogDerivativeConstant + 6 * P * B / d) * B / (3 * r) =
      (mrtCharacterLogDerivativeConstant * B / 3 + (2 * P / d) * B ^ 2) / r := by ring
  rw [halg]
  apply div_le_div_of_nonneg_right _ hr.le
  dsimp [K]
  nlinarith only [hmul]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeakVKStrip
namespace OAI

/-! The weak Hurwitz input supplies an actual zero-free strip and a
logarithmic-derivative norm bound on both sides of one. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Filter
open scoped _root_.Classical _root_.Topology

theorem MRTWeakHurwitzGrowthInput.strip_logderiv_oai (h : MRTWeakHurwitzGrowthInput) :
    ∃ c C T : ℝ, 0 < c ∧ 0 < C ∧ 0 < T ∧ ∀ (q : ℕ) [NeZero q],
      ∀ (χ : DirichletCharacter ℂ q) (t σ : ℝ), T ≤ |t| →
      1 - c * mrtVKRadius (2 * t) / mrtVKWeight q (2 * t) ≤ σ →
      σ ≤ 1 + mrtVKRadius (2 * t) / 16 →
        DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ)) ≠ 0 ∧
        ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (t : ℂ)) /
          DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
            C * (mrtVKWeight q (2 * t)) ^ 2 * (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ) := by
  obtain ⟨D, T, r₁, hD, hT, hr₁, _, hg⟩ := h.local_disks
  obtain ⟨c, K, r₂, hc, hK, hr₂, hb⟩ := mrt_moving_strip_logderiv
  have hrzero : Tendsto (fun x : ℝ => x ^ (-(2 / 3 : ℝ)) / 16) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (show (0 : ℝ) < 2 / 3 by norm_num)).div_const 16
  have hrsmall := hrzero.eventually (gt_mem_nhds (lt_min hr₁ hr₂))
  obtain ⟨H₀, hH₀⟩ := eventually_atTop.mp hrsmall
  let T₀ := max T (max 7 (Real.exp (max H₀ 1)))
  have hT₀ : 0 < T₀ := hT.trans_le (le_max_left _ _)
  refine ⟨c / (16 * D), 16 * K * D ^ 2, T₀, by positivity, by positivity, hT₀, ?_⟩
  intro q _ χ t σ ht hσ hσr
  have htT : T ≤ |t| := (le_max_left _ _).trans ht
  have ht7 : 7 ≤ |t| := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have htE : Real.exp (max H₀ 1) ≤ |t| :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have hHmax : max H₀ 1 ≤ mrtVKLog (2 * t) := by
    apply (Real.le_log_iff_exp_le (by positivity : 0 < |2 * t| + 3)).mpr
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hH : 1 ≤ mrtVKLog (2 * t) := (le_max_right _ _).trans hHmax
  have hsmall := hH₀ _ ((le_max_left _ _).trans hHmax)
  have hr1 : mrtVKRadius (2 * t) / 16 ≤ r₁ := (le_of_lt hsmall).trans (min_le_left _ _)
  have hr2 : mrtVKRadius (2 * t) / 16 ≤ r₂ := (le_of_lt hsmall).trans (min_le_right _ _)
  let r := mrtVKRadius (2 * t) / 16
  have hH0 : 0 < mrtVKLog (2 * t) := mrt_VKLog_pos (2 * t)
  have hr : 0 < r := div_pos (Real.rpow_pos_of_pos hH0 _) (by norm_num)
  have hrle : r ≤ 1 / 16 := by
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 16)
    exact Real.rpow_le_one_of_one_le_of_nonpos hH (by norm_num)
  have hheight : 6 * r < |t| := by linarith
  have hw : 1 ≤ mrtVKWeight q (2 * t) := mrt_VKWeight_ge_one hH
  have hbudget : 1 ≤ D * mrtVKWeight q (2 * t) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hD) (sub_nonneg.mpr hw)]
  have hgrowth := hg t htT hH hr1 q χ
  have hh := hb q χ r t (D * mrtVKWeight q (2 * t)) σ hr hr2 hheight hbudget
    hgrowth (by
      convert (preTransparency := .instances) hσ using 1
      dsimp [r]
      congr 1
      ring) hσr
  have hrinv : r⁻¹ = 16 * (mrtVKLog (2 * t)) ^ (2 / 3 : ℝ) := by
    dsimp [r]
    rw [inv_div, div_eq_mul_inv, mrtVKRadius, Real.rpow_neg hH0.le, inv_inv]
  refine ⟨hh.1, hh.2.trans ?_⟩
  apply le_of_eq
  rw [div_eq_mul_inv, hrinv]
  ring

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.strip_logderiv_oai := @OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.strip_logderiv_oai
