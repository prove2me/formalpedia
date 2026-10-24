-- Prove2me | solution 1 for OAI.Bernoulli.DeSilvaJerison.upperFlux_primitive_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T21:36:20.68613+00:00
-- url     : https://prove2.me/submissions/007c0870-25b5-45e2-b834-be30bc4cf64f

import Mathlib
import Definitions.Def_BernoulliNonflatInSeven
import Definitions.Def_OAIQWBNS000

section
-- module Solutions.OAIQW_BernoulliCone.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.SobolevCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uE uF uK uι

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology Convolution

namespace Bernoulli
open scoped _root_.Bernoulli
namespace LipschitzSobolev
variable {d : ℕ} {u : Space d → ℝ} {K : NNReal}

lemma measurable_gradient : Measurable (gradient u) := by
  exact (InnerProductSpace.toDual ℝ (Space d)).symm.continuous.measurable.comp
    (measurable_fderiv ℝ u)

end LipschitzSobolev
end Bernoulli

open scoped Manifold
namespace Bernoulli
open scoped _root_.Bernoulli
lemma exists_cutoff {d : ℕ} {K D : Set (Space d)} (hK : IsCompact K)
    (hD : IsOpen D) (hKD : K ⊆ D) :
    ∃ φ : Space d → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ D ∧
      (∀ᶠ x in 𝓝ˢ K, φ x = 1) ∧ (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) := by
  obtain ⟨δ, hδ, hδD⟩ := hK.exists_thickening_subset_open hD hKD
  have hki : K ⊆ interior (Metric.cthickening (δ/2) K) := by
    exact (Metric.self_subset_thickening (half_pos hδ) _).trans
      (Metric.thickening_subset_interior_cthickening _ _)
  obtain ⟨φ, hφ1, hφ0, hφb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, Space d)) (n := ⊤) hK.isClosed hki
  refine ⟨φ, φ.contMDiff.contDiff, HasCompactSupport.intro (hK.cthickening) hφ0, ?_, hφ1, hφb⟩
  have hs : tsupport (φ : Space d → ℝ) ⊆ Metric.cthickening (δ/2) K := by
    apply closure_minimal _ Metric.isClosed_cthickening
    intro x hx
    by_contra hn
    exact hx (hφ0 x hn)
  exact hs.trans ((Metric.cthickening_subset_thickening' hδ (by linarith) _).trans hδD)
end Bernoulli

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.LowerSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uι

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

noncomputable section
open Set Filter Finset
open scoped Topology
namespace Bernoulli.DeSilvaJerison

lemma p_le_one (t : ℝ) : p t ≤ 1 := by
  rw [p, ← f_zero]
  apply f_strictAnti.antitoneOn ⟨le_rfl,by norm_num⟩
    ⟨le_min (abs_nonneg _) t7_pos.le, (min_le_right _ _).trans_lt t7_lt_one⟩
  exact le_min (abs_nonneg _) t7_pos.le

lemma exists_lipschitz_p : ∃ K : NNReal, LipschitzWith K p := by
  have hc : ContDiffOn ℝ 1 f (Icc 0 t7) := by
    intro t ht
    exact (contDiffAt_f ⟨by linarith [ht.1],ht.2.trans_lt t7_lt_one⟩).contDiffWithinAt
  obtain ⟨K,hK⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc 0 t7) isCompact_Icc
  have hclip : LipschitzWith 1 (fun t : ℝ => min |t| t7) := by
    simpa only [Real.norm_eq_abs] using ((lipschitzWith_one_norm : LipschitzWith 1 (fun t : ℝ => ‖t‖)).min_const t7)
  refine ⟨K, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  have hm (t : ℝ) : min |t| t7 ∈ Icc 0 t7 :=
    ⟨le_min (abs_nonneg _) t7_pos.le, min_le_right _ _⟩
  exact (hK.dist_le_mul _ (hm x) _ (hm y)).trans (by
    have hh := hclip.dist_le_mul x y
    norm_num at hh
    exact mul_le_mul_of_nonneg_left hh K.coe_nonneg)

end Bernoulli.DeSilvaJerison

/-! The concrete seven-dimensional cone belonging to the De Silva–Jerison profile.
These are actual function/Sobolev constructions, not an assumption of minimality. -/
namespace Bernoulli.DeSilvaJerison

lemma Z_le_norm (x : Space 7) : Z x ≤ ‖x‖ := by
  calc Z x ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left (p_le_one _) (norm_nonneg x)
    _ = _ := mul_one _

lemma coordinate_le_norm (x : Space 7) : |x 6| ≤ ‖x‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x (6 : Fin 7)

lemma angular_estimate {x y : Space 7} (hx : x≠0) (hy : y≠0) :
    ‖y‖ * |x 6/‖x‖ - y 6/‖y‖| ≤ 2*‖x-y‖ := by
  have hr : 0<‖x‖ := norm_pos_iff.mpr hx
  have hs : 0<‖y‖ := norm_pos_iff.mpr hy
  have hq : |x 6/‖x‖| ≤ 1 := by
    rw [abs_div,abs_of_pos hr]
    exact (div_le_one hr).mpr (coordinate_le_norm x)
  have hxy : |x 6-y 6| ≤ ‖x-y‖ := by
    simpa only [PiLp.sub_apply] using coordinate_le_norm (x-y)
  calc
    ‖y‖ * |x 6/‖x‖ - y 6/‖y‖| =
        |(‖y‖-‖x‖)*(x 6/‖x‖) + (x 6-y 6)| := by
      rw [← abs_of_pos hs, ← abs_mul]
      congr 1
      rw [abs_of_pos hs]
      field_simp
      ring
    _ ≤ |‖y‖-‖x‖| * |x 6/‖x‖| + |x 6-y 6| := by
      simpa only [abs_mul] using abs_add_le ((‖y‖-‖x‖)*(x 6/‖x‖)) (x 6-y 6)
    _ ≤ |‖y‖-‖x‖| * 1 + ‖x-y‖ := by gcongr
    _ ≤ ‖x-y‖ + ‖x-y‖ := by
      rw [mul_one]
      gcongr
      simpa only [norm_sub_rev] using abs_norm_sub_norm_le y x
    _ = _ := by ring

lemma exists_lipschitz_Z : ∃ K : NNReal, LipschitzWith K Z := by
  obtain ⟨K,hK⟩ := exists_lipschitz_p
  refine ⟨1+2*K, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_add, NNReal.coe_mul,
    NNReal.coe_one, NNReal.coe_ofNat]
  by_cases hx : x=0
  · subst x
    rw [Z_zero,zero_sub,abs_neg,abs_of_nonneg (Z_nonneg y),zero_sub,norm_neg]
    exact (Z_le_norm y).trans (by nlinarith [K.coe_nonneg,norm_nonneg y])
  by_cases hy : y=0
  · subst y
    rw [Z_zero,sub_zero,abs_of_nonneg (Z_nonneg x),sub_zero]
    exact (Z_le_norm x).trans (by nlinarith [K.coe_nonneg,norm_nonneg x])
  have hpd : |p (x 6/‖x‖)-p (y 6/‖y‖)| ≤ K * |x 6/‖x‖- y 6/‖y‖| := by
    simpa only [Real.dist_eq] using hK.dist_le_mul (x 6/‖x‖) (y 6/‖y‖)
  have hpb : |p (x 6/‖x‖)| ≤ 1 := by
    rw [abs_of_nonneg (p_nonneg _)]
    exact p_le_one _
  calc
    |Z x-Z y| = |(‖x‖-‖y‖)*p (x 6/‖x‖) + ‖y‖*(p (x 6/‖x‖)-p (y 6/‖y‖))| := by
      unfold Z
      congr 1
      ring
    _ ≤ |‖x‖-‖y‖| * |p (x 6/‖x‖)| + ‖y‖* |p (x 6/‖x‖)-p (y 6/‖y‖)| := by
      simpa only [abs_mul, abs_of_nonneg (norm_nonneg y)] using
        abs_add_le ((‖x‖-‖y‖)*p (x 6/‖x‖)) (‖y‖*(p (x 6/‖x‖)-p (y 6/‖y‖)))
    _ ≤ |‖x‖-‖y‖| * 1 + ‖y‖*(K* |x 6/‖x‖-y 6/‖y‖|) := by gcongr
    _ = |‖x‖-‖y‖| + K*(‖y‖* |x 6/‖x‖-y 6/‖y‖|) := by ring
    _ ≤ ‖x-y‖ + K*(2*‖x-y‖) := by
      exact add_le_add (abs_norm_sub_norm_le x y)
        (mul_le_mul_of_nonneg_left (angular_estimate hx hy) K.coe_nonneg)
    _ = _ := by ring

lemma exists_lipschitz_U : ∃ K : NNReal, LipschitzWith K U := by
  obtain ⟨K,hK⟩ := exists_lipschitz_Z
  exact ⟨‖κ‖₊*K, (lipschitzWith_smul κ).comp hK⟩

lemma U_continuous : Continuous U := exists_lipschitz_U.choose_spec.continuous

end Bernoulli.DeSilvaJerison

/-! Euclidean calculus for the actual De Silva–Jerison axisymmetric construction.
No free-boundary or variational conclusion is built into these definitions. -/
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff Laplacian
namespace Bernoulli.Axisymmetric
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hasDerivAt_lineFirst {φ φ₁ : ℝ → ℝ} {φ₂ : ℝ} (e x v : E) (α t : ℝ)
    (hx : x+t • v≠0)
    (hφ : HasDerivAt φ (φ₁ (inner ℝ (x+t • v) e / ‖x+t • v‖))
      (inner ℝ (x+t • v) e / ‖x+t • v‖))
    (hφ₁ : HasDerivAt φ₁ φ₂ (inner ℝ (x+t • v) e / ‖x+t • v‖)) :
    HasDerivAt (lineFirst e x v α φ φ₁)
      (‖x+t • v‖^α / ‖x+t • v‖^2 *
        (α * φ (inner ℝ (x+t • v) e / ‖x+t • v‖) * ‖v‖^2 +
         α * (α-2) * φ (inner ℝ (x+t • v) e / ‖x+t • v‖) *
           (inner ℝ (x+t • v) v / ‖x+t • v‖)^2 +
         2*(α-1) * φ₁ (inner ℝ (x+t • v) e / ‖x+t • v‖) *
           (inner ℝ (x+t • v) v / ‖x+t • v‖) *
           (inner ℝ v e - inner ℝ (x+t • v) e / ‖x+t • v‖ *
             (inner ℝ (x+t • v) v / ‖x+t • v‖)) -
         inner ℝ (x+t • v) e / ‖x+t • v‖ *
           φ₁ (inner ℝ (x+t • v) e / ‖x+t • v‖) *
           (‖v‖^2-(inner ℝ (x+t • v) v / ‖x+t • v‖)^2) +
         φ₂ * (inner ℝ v e - inner ℝ (x+t • v) e / ‖x+t • v‖ *
           (inner ℝ (x+t • v) v / ‖x+t • v‖))^2)) t := by
  have hn := norm_ne_zero_iff.mpr hx
  have hr := hasDerivAt_radius x v t hx
  have ha := hasDerivAt_axis x v e t
  have hq : HasDerivAt (fun a:ℝ=>inner ℝ (x+a • v) v) (‖v‖^2) t := by
    simpa only [real_inner_self_eq_norm_sq] using hasDerivAt_axis x v v t
  have hs := hasDerivAt_angular x v e t hx
  have hp := hφ.comp t hs
  have hp₁ := hφ₁.comp t hs
  have hQ := ((hq.const_mul α).div (hr.pow 2) (pow_ne_zero _ hn)).mul hp
  have hS := (((hr.pow 2).const_mul (inner ℝ v e)).sub (ha.mul hq)).div
    (hr.pow 3) (pow_ne_zero _ hn)
  apply (((hr.rpow_const (p:=α) (Or.inl hn)).mul
    (hQ.add (hp₁.mul hS)))).congr_deriv
  simp only [Function.comp_def, Pi.pow_apply, Pi.div_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
  rw [Real.rpow_sub_one hn]
  field_simp
  ring

lemma secondCoeff_sum {ι : Type uι} [Fintype ι]
    (α F F₁ F₂ s : ℝ) (p b : ι → ℝ)
    (hp : ∑ i, (p i)^2 = 1) (hb : ∑ i, (b i)^2 = 1)
    (hpb : ∑ i, p i*b i = s) :
    ∑ i, secondCoeff α F F₁ F₂ s (p i) (b i) 1 =
      α*(α+(Fintype.card ι : ℝ)-2)*F - ((Fintype.card ι : ℝ)-1)*s*F₁ + (1-s^2)*F₂ := by
  have he (i:ι) : secondCoeff α F F₁ F₂ s (p i) (b i) 1 =
      (α*F-s*F₁) + (α*(α-2)*F-(2*α-3)*s*F₁+s^2*F₂)*(p i)^2 +
        (2*(α-1)*F₁-2*s*F₂)*(p i*b i) + F₂*(b i)^2 := by
    unfold secondCoeff
    ring
  simp_rw [he, Finset.sum_add_distrib, ←Finset.mul_sum]
  rw [hp,hb,hpb]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

lemma lift_line_second {φ φ₁ : ℝ → ℝ} {φ₂ : ℝ} (e x v : E) (α : ℝ)
    (hx : x≠0)
    (hφ : ∀ᶠ s in 𝓝 (inner ℝ x e / ‖x‖), HasDerivAt φ (φ₁ s) s)
    (hφ₁ : HasDerivAt φ₁ φ₂ (inner ℝ x e / ‖x‖)) :
    deriv (deriv (fun t:ℝ=>lift e α φ (x+t • v))) 0 =
      ‖x‖^α / ‖x‖^2 * secondCoeff α (φ (inner ℝ x e / ‖x‖))
        (φ₁ (inner ℝ x e / ‖x‖)) φ₂ (inner ℝ x e / ‖x‖)
        (inner ℝ x v / ‖x‖) (inner ℝ v e) (‖v‖^2) := by
  have hx0 : x+(0:ℝ) • v≠0 := by simpa
  have hc : ContinuousAt (fun t:ℝ=>x+t • v) 0 := by fun_prop
  have hnear : ∀ᶠ t:ℝ in 𝓝 0, x+t • v≠0 :=
    hc.eventually_ne hx0
  have hs := (hasDerivAt_angular x v e 0 hx0).continuousAt
  have hp : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt φ (φ₁ (inner ℝ (x+t • v) e / ‖x+t • v‖))
      (inner ℝ (x+t • v) e / ‖x+t • v‖) := by
    exact hs.tendsto.eventually (p:=fun s=>HasDerivAt φ (φ₁ s) s) (by simpa using hφ)
  have he : deriv (fun t:ℝ=>lift e α φ (x+t • v)) =ᶠ[𝓝 0] lineFirst e x v α φ φ₁ := by
    filter_upwards [hnear,hp] with t ht hpt
    exact (hasDerivAt_lift_line e x v α t ht hpt).deriv
  rw [he.deriv_eq]
  have hh := hasDerivAt_lineFirst e x v α 0 hx0 (by simpa using hφ.self_of_nhds)
    (by simpa using hφ₁)
  simpa only [zero_smul, add_zero, secondCoeff] using hh.deriv

lemma line_second_derivative {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (v : E) :
    deriv (deriv (fun t:ℝ=>f (x+t • v))) 0=(fderiv ℝ (fderiv ℝ f) x v) v := by
  let c := fun t:ℝ=>x+t • v
  let q := fun t:ℝ=>(fderiv ℝ f (c t)) v
  have hc (t:ℝ) : HasDerivAt c v t := by
    simpa only [one_smul,id_eq,c] using ((hasDerivAt_id t).smul_const v).const_add x
  have hc0 : c 0=x := by simp [c]
  have hnear : ∀ᶠ t in 𝓝 (0:ℝ), ContDiffAt ℝ 2 f (c t) :=
    (hc 0).continuousAt.tendsto.eventually (hc0 ▸ hf.eventually (by norm_num))
  have hq : deriv (fun t:ℝ=>f (x+t • v)) =ᶠ[𝓝 0] q := by
    filter_upwards [hnear] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hc t)).deriv
  have hff := (hf.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hff' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (c 0) := hc0.symm ▸ hff.hasFDerivAt
  have hh := (hff'.comp_hasDerivAt 0 (hc 0)).clm_apply (hasDerivAt_const 0 v)
  have hqq : HasDerivAt q ((fderiv ℝ (fderiv ℝ f) x v) v) 0 := by
    simpa only [Function.comp_def,ContinuousLinearMap.map_zero,add_zero,q] using hh
  rw [hq.deriv_eq,hqq.deriv]

lemma laplacian_lift [FiniteDimensional ℝ E] {φ φ₁ : ℝ → ℝ} {φ₂ : ℝ}
    (e x : E) (α : ℝ) (he : ‖e‖=1) (hx : x≠0)
    (hc : ContDiffAt ℝ 2 φ (inner ℝ x e / ‖x‖))
    (hφ : ∀ᶠ s in 𝓝 (inner ℝ x e / ‖x‖), HasDerivAt φ (φ₁ s) s)
    (hφ₁ : HasDerivAt φ₁ φ₂ (inner ℝ x e / ‖x‖)) :
    Δ (lift e α φ) x = ‖x‖^α / ‖x‖^2 *
      (α*(α+(Module.finrank ℝ E : ℝ)-2)*φ (inner ℝ x e / ‖x‖) -
        ((Module.finrank ℝ E : ℝ)-1)*(inner ℝ x e / ‖x‖)*φ₁ (inner ℝ x e / ‖x‖) +
        (1-(inner ℝ x e / ‖x‖)^2)*φ₂) := by
  let b := stdOrthonormalBasis ℝ E
  have hn := norm_ne_zero_iff.mpr hx
  have hp : ∑ i, (inner ℝ x (b i) / ‖x‖)^2 = 1 := by
    simp_rw [div_pow, ←Finset.sum_div]
    rw [b.sum_sq_inner_left]
    exact div_self (pow_ne_zero _ hn)
  have hb : ∑ i, (inner ℝ (b i) e)^2 = 1 := by
    rw [b.sum_sq_inner_right,he]
    norm_num
  have hpb : ∑ i, (inner ℝ x (b i) / ‖x‖) * inner ℝ (b i) e = inner ℝ x e / ‖x‖ := by
    simp_rw [div_mul_eq_mul_div, ←Finset.sum_div]
    rw [b.sum_inner_mul_inner]
  have hs := secondCoeff_sum α (φ (inner ℝ x e / ‖x‖)) (φ₁ (inner ℝ x e / ‖x‖)) φ₂
    (inner ℝ x e / ‖x‖) (fun i=>inner ℝ x (b i) / ‖x‖) (fun i=>inner ℝ (b i) e) hp hb hpb
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp_rw [iteratedFDeriv_two_apply]
  simp only [Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one]
  have hcc := contDiffAt_lift (α:=α) hx hc
  simp_rw [←line_second_derivative hcc, lift_line_second e x _ α hx hφ hφ₁]
  have hbunit (i:Fin (Module.finrank ℝ E)) : ‖b i‖^2 = (1:ℝ) := by simp
  change (∑ i, ‖x‖^α / ‖x‖^2 * secondCoeff α (φ (inner ℝ x e / ‖x‖))
    (φ₁ (inner ℝ x e / ‖x‖)) φ₂ (inner ℝ x e / ‖x‖)
    (inner ℝ x (b i) / ‖x‖) (inner ℝ (b i) e) (‖b i‖^2)) = _
  simp_rw [hbunit, ←Finset.mul_sum]
  rw [hs]
  simp

lemma radial_norm {x : E} (hx : x≠0) : ‖radial x‖=1 := by
  rw [radial,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

lemma radial_inner (x e : E) : inner ℝ (radial x) e = inner ℝ x e / ‖x‖ := by
  simp only [radial,real_inner_smul_left,div_eq_mul_inv,mul_comm]

lemma norm_sq_polarGradient {e x : E} (he : ‖e‖=1) (hx : x≠0) (a b : ℝ) :
    ‖polarGradient e x a b‖^2 = a^2 + (1-(inner ℝ x e / ‖x‖)^2)*b^2 := by
  have hn : inner ℝ (radial x) (radial x)=1 := by
    rw [real_inner_self_eq_norm_sq,radial_norm hx]; norm_num
  have het : inner ℝ e e=1 := by rw [real_inner_self_eq_norm_sq,he]; norm_num
  have hrev : inner ℝ e (radial x) = inner ℝ x e / ‖x‖ :=
    (real_inner_comm e (radial x)).symm.trans (radial_inner x e)
  rw [←real_inner_self_eq_norm_sq]
  simp only [polarGradient,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right,hn,het,hrev,radial_inner]
  ring

end Bernoulli.Axisymmetric

namespace Bernoulli.DeSilvaJerison
open Axisymmetric InnerProductSpace
open scoped Laplacian ContDiff

lemma signed_laplacian {x : Space 7} (hx : x≠0) (ha : |angle x|<1) : Δ Zsigned x=0 := by
  have ht : angle x ∈ Ioo (-1:ℝ) 1 := abs_lt.mp ha
  have hp : ∀ᶠ s in 𝓝 (inner ℝ x axis/‖x‖), HasDerivAt f (fp s) s := by
    simp only [inner_axis]
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hasDerivAt_f hs
  have ht' : inner ℝ x axis / ‖x‖ ∈ Ioo (-1:ℝ) 1 := by simpa only [inner_axis,angle] using ht
  have hl := laplacian_lift axis x 1 axis_norm hx (contDiffAt_f ht') hp (hasDerivAt_fp ht')
  have hd : 1-(angle x)^2≠0 := by nlinarith [sq_nonneg (angle x),ht.1,ht.2]
  have hr := f_relation ht
  have he : 6*f (angle x)-6*angle x*fp (angle x)+(1-(angle x)^2)*(-6/(1-(angle x)^2)^4)=0 := by
    field_simp at hr ⊢
    nlinarith [hr]
  change Δ (lift axis 1 f) x=0
  simp only [inner_axis,Space,finrank_euclideanSpace_fin, Nat.cast_ofNat] at hl
  norm_num only at hl
  change Δ (lift axis 1 f) x = ‖x‖^ (1:ℝ) / ‖x‖^2 *
    (6*f (angle x)-6*angle x*fp (angle x)+(1-(angle x)^2)*(-6/(1-(angle x)^2)^4)) at hl
  simpa only [he,mul_zero] using hl

end Bernoulli.DeSilvaJerison

namespace Bernoulli.DeSilvaJerison
open scoped BigOperators

lemma f_series_lower (n:ℕ) {t:ℝ} (ht:0≤t) (ht1:t<1) :
    (8-25*t^2+15*(t^2)^2)/(8*(1-t^2)^2)
      -15/8*t^2*(B n (t^2)+(t^2)^n/(1-t^2)) ≤ f t := by
  have ha := (A_series_bounds n ht ht1).2
  have hp := mul_le_mul_of_nonneg_left ha (show (0:ℝ)≤15/8*t from by positivity)
  unfold f
  convert! sub_le_sub_left hp ((8-25*t^2+15*t^4)/(8*(1-t^2)^2)) using 1
  ring

end Bernoulli.DeSilvaJerison

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.ScalarLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff Laplacian
namespace Bernoulli.ScalarLaplacian
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma deriv2_mul {f g : ℝ → ℝ} {t:ℝ}
    (hf:ContDiffAt ℝ 2 f t) (hg:ContDiffAt ℝ 2 g t) :
    deriv (deriv (fun s=>f s*g s)) t =
      deriv (deriv f) t*g t+2*deriv f t*deriv g t+f t*deriv (deriv g) t := by
  have hf' := (hf.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hg' := (hg.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have he : deriv (fun s=>f s*g s) =ᶠ[𝓝 t] fun s=>deriv f s*g s+f s*deriv g s := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with s hs ht
    exact deriv_mul (hs.differentiableAt (by norm_num)) (ht.differentiableAt (by norm_num))
  rw [he.deriv_eq]
  have hh := (hf'.hasDerivAt.mul (hg.differentiableAt (by norm_num)).hasDerivAt).add
    ((hf.differentiableAt (by norm_num)).hasDerivAt.mul hg'.hasDerivAt)
  change deriv (deriv f*g+f*deriv g) t = _
  rw [hh.deriv]
  ring

lemma laplacian_sum_line {f:E→ℝ} {x:E} (hf:ContDiffAt ℝ 2 f x) :
    Δ f x = ∑ i, deriv (deriv (fun t:ℝ=>f (x+t • stdOrthonormalBasis ℝ E i))) 0 := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp_rw [iteratedFDeriv_two_apply]
  simp only [Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one]
  simp_rw [Axisymmetric.line_second_derivative hf]

lemma laplacian_mul {f g:E→ℝ} {x:E} (hf:ContDiffAt ℝ 2 f x)
    (hg:ContDiffAt ℝ 2 g x) :
    Δ (fun y=>f y*g y) x = g x*Δ f x+2*inner ℝ (gradient f x) (gradient g x)+f x*Δ g x := by
  let b := stdOrthonormalBasis ℝ E
  have hfL (v:E) : ContDiffAt ℝ 2 (fun t:ℝ=>f (x+t • v)) 0 := by
    have hh : ContDiffAt ℝ 2 (fun t:ℝ=>x+t • v) 0 := contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
    exact (show ContDiffAt ℝ 2 f (x+(0:ℝ) • v) by simpa using hf).comp 0 hh
  have hgL (v:E) : ContDiffAt ℝ 2 (fun t:ℝ=>g (x+t • v)) 0 := by
    have hh : ContDiffAt ℝ 2 (fun t:ℝ=>x+t • v) 0 := contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
    exact (show ContDiffAt ℝ 2 g (x+(0:ℝ) • v) by simpa using hg).comp 0 hh
  rw [laplacian_sum_line (hf.mul hg),laplacian_sum_line hf,laplacian_sum_line hg]
  simp_rw [deriv2_mul (hfL _) (hgL _),zero_smul,add_zero,
    line_deriv (hf.differentiableAt (by norm_num)),line_deriv (hg.differentiableAt (by norm_num))]
  simp_rw [Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,mul_assoc]
  have hc : (∑ i,inner ℝ (gradient f x) (b i)*inner ℝ (gradient g x) (b i))=
      inner ℝ (gradient f x) (gradient g x) := by
    convert b.sum_inner_mul_inner (gradient f x) (gradient g x) using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_comm (gradient g x) (b i)]
  dsimp only [b] at hc
  rw [←Finset.mul_sum,hc]
  ring

lemma laplacian_comp {φ:ℝ→ℝ} {f:E→ℝ} {x:E} (hφ:ContDiffAt ℝ 2 φ (f x))
    (hf:ContDiffAt ℝ 2 f x) :
    Δ (fun y=>φ (f y)) x = deriv (deriv φ) (f x)*‖gradient f x‖^2 + deriv φ (f x)*Δ f x := by
  let b := stdOrthonormalBasis ℝ E
  have he (v:E) : deriv (deriv (fun t:ℝ=>φ (f (x+t • v)))) 0 =
      deriv (deriv φ) (f x)*(inner ℝ (gradient f x) v)^2+
        deriv φ (f x)*deriv (deriv (fun t:ℝ=>f (x+t • v))) 0 := by
    have hfL : ContDiffAt ℝ 2 (fun t:ℝ=>f (x+t • v)) 0 := by
      have hh : ContDiffAt ℝ 2 (fun t:ℝ=>x+t • v) 0 := contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
      exact (show ContDiffAt ℝ 2 f (x+(0:ℝ) • v) by simpa using hf).comp 0 hh
    have hh := iteratedDeriv_comp_two (show ContDiffAt ℝ 2 φ (f (x+(0:ℝ) • v)) by simpa using hφ) hfL
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,Function.comp_def,zero_smul,add_zero,
      line_deriv (hf.differentiableAt (by norm_num))] using hh
  change Δ (φ ∘ f) x = _
  rw [laplacian_sum_line (hφ.comp x hf),laplacian_sum_line hf]
  simp only [Function.comp_apply]
  simp_rw [he,Finset.sum_add_distrib,←Finset.mul_sum]
  rw [b.sum_sq_inner_left]
end Bernoulli.ScalarLaplacian

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.CylindricalCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff Laplacian
namespace Bernoulli.Cylindrical
open ScalarLaplacian
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem transverse_inner [FiniteDimensional ℝ E] (e x:E) (he:‖e‖=1) : inner ℝ (transverse e x) e=0 := by
  simp [transverse,axis,inner_sub_left,real_inner_smul_left,he]
lemma laplacian_axis (e x:E) : Δ (axis e) x=0 := by
  rw [laplacian_sum_line (axis_contDiff e).contDiffAt]
  apply Finset.sum_eq_zero
  intro i hi
  have hh : deriv (fun t:ℝ=>axis e (x+t • stdOrthonormalBasis ℝ E i))=
      fun _=>inner ℝ (stdOrthonormalBasis ℝ E i) e := by
    funext t; exact (Axisymmetric.hasDerivAt_axis x _ e t).deriv
  rw [hh,deriv_const]
lemma laplacian_norm_sq (x:E) : Δ (fun z:E=>‖z‖^2) x=2*(Module.finrank ℝ E : ℝ) := by
  rw [laplacian_sum_line (contDiff_norm_sq (𝕜:=ℝ) (E:=E) (n:=2)).contDiffAt]
  have hh (v:E) : deriv (deriv (fun t:ℝ=>‖x+t • v‖^2)) 0=2*‖v‖^2 := by
    have hl (t:ℝ) : HasDerivAt (fun s:ℝ=>x+s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have he : deriv (fun t:ℝ=>‖x+t • v‖^2)=fun t=>2*inner ℝ (x+t • v) v := by
      funext t; exact (hl t).norm_sq.deriv
    rw [he]
    have hd:=((hl 0).inner ℝ (hasDerivAt_const (0:ℝ) v)).const_mul 2
    simpa using hd.deriv
  simp_rw [hh]
  simp [mul_comm]
lemma laplacian_radiusSq (e x:E) (he:‖e‖=1) : Δ (radiusSq e) x=2*((Module.finrank ℝ E : ℝ)-1) := by
  have hφ : ContDiffAt ℝ 2 (fun s:ℝ=>s^2) (axis e x) := contDiffAt_id.pow 2
  have hh:=laplacian_comp hφ (axis_contDiff e).contDiffAt
  have hder : deriv (fun s:ℝ=>s^2) = fun s=>2*s := by funext s; simp
  have hder2 : deriv (deriv (fun s:ℝ=>s^2)) (axis e x)=2 := by rw [hder]; simp
  rw [hder2,gradient_axis,he,laplacian_axis] at hh
  change Δ ((fun z:E=>‖z‖^2)-(fun z:E=>(axis e z)^2)) x = _
  rw [(contDiff_norm_sq (𝕜:=ℝ) (E:=E) (n:=2)).contDiffAt.laplacian_sub ((axis_contDiff e).pow 2).contDiffAt,
    laplacian_norm_sq,hh]
  ring

lemma laplacian_lift {e x:E} (he:‖e‖=1) {y k h:ℝ→ℝ}
    (hy:ContDiffAt ℝ 2 y (radiusSq e x)) (hk:ContDiffAt ℝ 2 k (radiusSq e x))
    (hh:ContDiffAt ℝ 2 h (axis e x*k (radiusSq e x))) :
    Δ (lift e y k h) x =
      y (radiusSq e x)*deriv (deriv h) (axis e x*k (radiusSq e x))*
        ((k (radiusSq e x))^2+4*radiusSq e x*(axis e x)^2*(deriv k (radiusSq e x))^2)+
      deriv h (axis e x*k (radiusSq e x))*
        (axis e x*y (radiusSq e x)*(4*radiusSq e x*deriv (deriv k) (radiusSq e x)+
          2*((Module.finrank ℝ E:ℝ)-1)*deriv k (radiusSq e x))+
          8*radiusSq e x*axis e x*deriv y (radiusSq e x)*deriv k (radiusSq e x))+
      h (axis e x*k (radiusSq e x))*(4*radiusSq e x*deriv (deriv y) (radiusSq e x)+
        2*((Module.finrank ℝ E:ℝ)-1)*deriv y (radiusSq e x)) := by
  let q := radiusSq e
  let a := axis e
  let Y := fun z=>y (q z)
  let K := fun z=>k (q z)
  let s := fun z=>a z*K z
  have hq : ContDiffAt ℝ 2 q x := (radiusSq_contDiff e).contDiffAt
  have ha : ContDiffAt ℝ 2 a x := (axis_contDiff e).contDiffAt
  have hY : ContDiffAt ℝ 2 Y x := hy.comp x hq
  have hK : ContDiffAt ℝ 2 K x := hk.comp x hq
  have hs : ContDiffAt ℝ 2 s x := ha.mul hK
  have gY : gradient Y x=deriv y (q x) • ((2:ℝ) • transverse e x) := by
    rw [gradient_comp (hy.differentiableAt (by norm_num)) (hq.differentiableAt (by norm_num))]
    rw [show gradient q x=(2:ℝ) • transverse e x from gradient_radiusSq e x]
  have gK : gradient K x=deriv k (q x) • ((2:ℝ) • transverse e x) := by
    rw [gradient_comp (hk.differentiableAt (by norm_num)) (hq.differentiableAt (by norm_num))]
    rw [show gradient q x=(2:ℝ) • transverse e x from gradient_radiusSq e x]
  have gs : gradient s x=K x • e+(a x*deriv k (q x)*2) • transverse e x := by
    rw [gradient_mul (ha.differentiableAt (by norm_num)) (hK.differentiableAt (by norm_num)),gK]
    rw [show gradient a x=e from gradient_axis e x]
    simp [smul_smul,mul_assoc]
  have gn : ‖gradient q x‖^2=4*q x := by
    rw [show gradient q x=(2:ℝ) • transverse e x from gradient_radiusSq e x,norm_smul,mul_pow,
      Real.norm_eq_abs,transverse_sq e x he]
    norm_num [q]
  have gort : inner ℝ e (transverse e x)=0 := by rw [real_inner_comm,transverse_inner e x he]
  have gsn : ‖gradient s x‖^2=(K x)^2+4*q x*(a x)^2*(deriv k (q x))^2 := by
    rw [gs,norm_add_sq_real]
    simp only [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,he,mul_one,
      real_inner_smul_left,real_inner_smul_right,gort,mul_zero,add_zero,transverse_sq e x he]
    dsimp [q]; ring
  have gaK : inner ℝ (gradient a x) (gradient K x)=0 := by
    rw [show gradient a x=e from gradient_axis e x,gK]
    simp [real_inner_smul_right,gort]
  have gYs : inner ℝ (gradient Y x) (gradient s x)=4*q x*a x*deriv y (q x)*deriv k (q x) := by
    rw [gY,gs]
    simp only [inner_add_right,real_inner_smul_left,real_inner_smul_right,
      transverse_inner e x he,mul_zero,zero_add,real_inner_self_eq_norm_sq,transverse_sq e x he]
    dsimp [q]; ring
  have lY : Δ Y x=deriv (deriv y) (q x)*(4*q x)+deriv y (q x)*(2*((Module.finrank ℝ E:ℝ)-1)) := by
    rw [laplacian_comp hy hq,gn,show Δ q x=2*((Module.finrank ℝ E:ℝ)-1) from laplacian_radiusSq e x he]
  have lK : Δ K x=deriv (deriv k) (q x)*(4*q x)+deriv k (q x)*(2*((Module.finrank ℝ E:ℝ)-1)) := by
    rw [laplacian_comp hk hq,gn,show Δ q x=2*((Module.finrank ℝ E:ℝ)-1) from laplacian_radiusSq e x he]
  have ls : Δ s x=a x*Δ K x := by
    rw [laplacian_mul ha hK,show Δ a x=0 from laplacian_axis e x,gaK]
    ring
  have gH : gradient (fun z=>h (s z)) x=deriv h (s x) • gradient s x :=
    gradient_comp (hh.differentiableAt (by norm_num)) (hs.differentiableAt (by norm_num))
  change Δ (fun z=>Y z*h (s z)) x = _
  have hH : ContDiffAt ℝ 2 (fun z=>h (s z)) x := hh.comp x hs
  rw [laplacian_mul hY hH,laplacian_comp (f:=s) hh hs,gH,
    real_inner_smul_right,gYs,gsn,ls,lK,lY]
  dsimp [Y,K,s,a,q]
  ring
end Bernoulli.Cylindrical

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter Finset
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison

lemma capH_zero : capH 0=1+capAmplitude := by norm_num [capH,capRadius,capAngle,f_zero]
lemma capHP_end : capHP (3/4)=capAmplitude/6-3125/768 := by
  have hh:=f_relation (t:=3/5) (by norm_num)
  rw [capHP,capAngle_end,capRadius_end,capAmplitude]
  norm_num at hh ⊢
  linear_combination (16/15)*hh

end Bernoulli.DeSilvaJerison

noncomputable section
namespace Bernoulli.DeSilvaJerison.CapSign
lemma identity (x:ℝ) : -polyK (9/25*x)=bern x := by
  unfold polyK flo bern
  ring
lemma polyK_nonpos {u:ℝ} (hu:0≤u) (hu1:u≤9/25) : polyK u≤0 := by
  let x:ℝ := 25/9*u
  have hx:0≤x:=by dsimp [x]; positivity
  have hx1:x≤1:=by dsimp [x]; linarith
  have hh:0≤bern x := by
    have hy:0≤1-x:=sub_nonneg.mpr hx1
    unfold bern
    positivity
  have hi:=identity x
  have he:9/25*x=u:=by dsimp [x]; ring
  rw [he] at hi
  linarith
end Bernoulli.DeSilvaJerison.CapSign

namespace Bernoulli.DeSilvaJerison

lemma capH_nonneg {s:ℝ} (hs:|s|≤3/4) :0≤capH s := by
  have hh:=capH_antitone (show (|s|:ℝ)∈Set.Ici 0 from abs_nonneg s) (by norm_num : (3/4:ℝ)∈Set.Ici 0) hs
  rw [capH_end] at hh
  rcases le_total 0 s with hp|hn
  · simpa only [abs_of_nonneg hp] using hh
  · simpa only [abs_of_nonpos hn,capH_even] using hh

lemma capHPP_nonpos (s:ℝ) :-5*(capRadius s)^3+4*capAmplitude≤0 := by
  have hh:1≤(capRadius s)^3:=one_le_pow₀ (capRadius_one_le s)
  linarith [capAmplitude_le]

lemma capAngle_bounds {s:ℝ} (hs:0≤ s) (hs1:s≤3/4) : 0≤capAngle s ∧ capAngle s≤3/5 := by
  have hr:=capRadius_pos s
  constructor
  · exact div_nonneg hs hr.le
  · rw [capAngle,div_le_iff₀ hr]
    have hs2:s^2≤9/16:=by nlinarith
    nlinarith [capRadius_sq s]

lemma cap_flo_bound {t:ℝ} (ht:0≤t) (ht1:t≤3/5) : CapSign.flo (t^2)≤8*(1-t^2)^2*f t := by
  have hd:0<1-t^2:=by nlinarith
  have hl:=f_series_lower 6 ht (by linarith : t<1)
  have hi:CapSign.flo (t^2)/(8*(1-t^2)^2)=
      (8-25*t^2+15*(t^2)^2)/(8*(1-t^2)^2)-15/8*t^2*(B 6 (t^2)+(t^2)^6/(1-t^2)) := by
    unfold CapSign.flo B
    norm_num [Finset.sum_range_succ]
    field_simp [hd.ne']
    ring
  rw [←hi] at hl
  exact (div_le_iff₀ (by positivity)).mp hl |>.trans_eq (mul_comm _ _)

lemma cap_K_identity (s:ℝ) :
    (-5*(capRadius s)^3+4*capAmplitude-(673/250)*s*capHP s+(431/200)*capH s)/(capRadius s)^5=
      (431/200-673/250)*(1-(capAngle s)^2)^2*f (capAngle s)+673/250-5*(1-(capAngle s)^2)+
        capAmplitude/(capRadius s)^3*(4*(1-(capAngle s)^2)-4*(673/250)*(capAngle s)^2+431/200*(1+(capAngle s)^2)) := by
  rw [capHP,capH,capAngle_d,cap_f_relation]
  unfold capAngle
  field_simp [(capRadius_pos s).ne']
  have he:s^2=(capRadius s)^2-1:=by linarith [capRadius_sq s]
  have he3:s^3=s*((capRadius s)^2-1):=by linear_combination s*he
  ring_nf
  rw [he,he3]
  ring

theorem cap_K_nonpos {s:ℝ} (hs:|s|≤3/4) :
    -5*(capRadius s)^3+4*capAmplitude-(673/250)*s*capHP s+(431/200)*capH s≤0 := by
  suffices hp:∀t:ℝ, 0≤t → t≤3/4 →
      -5*(capRadius t)^3+4*capAmplitude-(673/250)*t*capHP t+(431/200)*capH t≤0 by
    rcases le_total 0 s with hpos|hneg
    · exact hp s hpos (by rw [abs_of_nonneg hpos] at hs; exact hs)
    · have hh:=hp (-s) (by linarith) (by rw [abs_of_nonpos hneg] at hs; exact hs)
      simpa only [capRadius,neg_sq,capHP_odd,capH_even,mul_neg,neg_mul,neg_neg] using hh
  intro s hs hs1
  obtain ⟨ht,ht1⟩:=capAngle_bounds hs hs1
  have hu:0≤(capAngle s)^2:=sq_nonneg _
  have hu1:(capAngle s)^2≤9/25:=by nlinarith
  have hd:0≤1-(capAngle s)^2:=by linarith
  have hB:0≤4*(1-(capAngle s)^2)-4*(673/250)*(capAngle s)^2+431/200*(1+(capAngle s)^2):=by linarith
  have hF:=cap_flo_bound ht ht1
  have hF':(431/200-673/250)*(1-(capAngle s)^2)^2*f (capAngle s)≤
      (431/200-673/250)*CapSign.flo ((capAngle s)^2)/8 := by nlinarith
  have hr:=capRadius_pos s
  have hr1:=capRadius_one_le s
  have hRa:capAmplitude/(capRadius s)^3≤29/100*(1-(capAngle s)^2) := by
    rw [capAngle_d]
    field_simp [hr.ne']
    nlinarith [capAmplitude_le]
  have hAB:=mul_le_mul_of_nonneg_right hRa hB
  have hp:=CapSign.polyK_nonpos hu hu1
  unfold CapSign.polyK at hp
  have hh:(-5*(capRadius s)^3+4*capAmplitude-(673/250)*s*capHP s+(431/200)*capH s)/(capRadius s)^5≤0 := by
    rw [cap_K_identity]
    linarith
  simpa only [zero_mul] using (div_le_iff₀ (pow_pos hr 5)).mp hh

end Bernoulli.DeSilvaJerison

namespace Bernoulli.DeSilvaJerison

lemma capP_bounds : 3884/10000≤capP ∧ capP≤3886/10000 := by
  have hh:=capB_bounds
  unfold capB at hh
  constructor <;> linarith [hh.1,hh.2]
lemma capEta_bounds : 1/3≤capEta ∧ capEta≤capP := by
  have hp:=capP_bounds
  have hq:0<1+(9/16)*capP^2:=by positivity
  have hpp:0≤capP*(capP-3/25):=mul_nonneg (by linarith [hp.1]) (by linarith [hp.1])
  have hprod:capP*(capP-3/25)≤(3886/10000)*(2686/10000):=by
    exact mul_le_mul hp.2 (by linarith [hp.2]) (by linarith [hp.1]) (by norm_num)
  have hsq:(3884/10000:ℝ)^2≤capP^2:=by nlinarith [hp.1]
  unfold capEta
  constructor
  · have hdelta : (9/16)*capP*(capP-3/25)/(1+(9/16)*capP^2)≤capP-1/3 := by
      apply (div_le_iff₀ hq).mpr
      have hh:=mul_le_mul_of_nonneg_left hsq (show (0:ℝ)≤9/16 from by norm_num)
      have ha:0≤capP-1/3:=by linarith [hp.1]
      have hb:((3884/10000:ℝ)-1/3)*(1+(9/16)*(3884/10000:ℝ)^2)≤(capP-1/3)*(1+(9/16)*capP^2):=
        mul_le_mul (by linarith [hp.1]) (by linarith) (by positivity) ha
      nlinarith
    linarith
  · exact sub_le_self _ (div_nonneg (by nlinarith) hq.le)

lemma capW_even (s : ℝ) : capW (-s)=capW s := by
  simp only [capW,capH_even,capHP_odd,neg_sq,mul_neg,neg_mul,neg_neg]
lemma capW_zero_nonpos : capW 0≤0 := by
  rw [capW,capH_zero,capHP_zero]
  norm_num
  have hprod:=mul_le_mul_of_nonneg_right capEta_bounds.1 capAmplitude_pos.le
  nlinarith [capAmplitude_bounds.1,capEta_bounds.1]
lemma capW_end : capW (3/4)=0 := by
  rw [capW,capH_end,capHP_end]
  simp only [mul_zero,zero_add]
  have hd:3125/1024-capAmplitude/8≠0:=ne_of_gt (by linarith [capAmplitude_le])
  have hp : capP*(3125/1024-capAmplitude/8)=3125/1024-13/2*capAmplitude := by
    rw [capP,div_mul_cancel₀ _ hd]
  nlinarith

lemma hasDerivAt_capW (s : ℝ) : HasDerivAt capW (capWP s) s := by
  have hh:=(((hasDerivAt_capH s).const_mul (1-capEta)).add
    (((hasDerivAt_id s).const_mul (capP-1)).mul (hasDerivAt_capHP s))).sub
    (((hasDerivAt_const s (1:ℝ)).add (((hasDerivAt_id s).pow 2).const_mul 2)).const_mul (3*capAmplitude))
  convert! hh using 1
  simp only [capWP,id_eq,Nat.cast_ofNat]
  ring
lemma hasDerivAt_capWP (s : ℝ) : HasDerivAt capWP (capWPP s) s := by
  have hR:=hasDerivAt_capRadius s
  have hH:HasDerivAt (fun t=>-5*(capRadius t)^3+4*capAmplitude) (-15*s*capRadius s) s := by
    convert! ((hR.pow 3).const_mul (-5)).add_const (4*capAmplitude) using 1
    norm_num only [Nat.reduceSub,Nat.cast_ofNat]
    field_simp [(capRadius_pos s).ne']
    ring
  have hh:=(((hasDerivAt_capHP s).const_mul (capP-capEta)).add
    (((hasDerivAt_id s).const_mul (capP-1)).mul hH)).sub ((hasDerivAt_id s).const_mul (12*capAmplitude))
  convert! hh using 1
  simp only [capWPP,id_eq]
  ring

lemma capRadius_cube_bound (s : ℝ) : (capRadius s)^3-1≤(3/2)*(capRadius s)*s^2 := by
  have hr:=capRadius_pos s
  have hh:=mul_nonneg (sq_nonneg (capRadius s-1)) (by linarith : 0≤capRadius s+2)
  nlinarith [capRadius_sq s, mul_nonneg (sq_nonneg (capRadius s-1)) hr.le]

lemma capW_radial_convex {s : ℝ} (hs : 0≤ s) : 0≤ s*capWPP s-capWP s := by
  have he:s*capWPP s-capWP s=(capP-capEta)*(s*(-5*(capRadius s)^3+4*capAmplitude)-capHP s)+
      15*(1-capP)*s^3*capRadius s := by unfold capWPP capWP; ring
  rw [he]
  have hc:0≤capP-capEta:=sub_nonneg.mpr capEta_bounds.2
  have hb:=mul_le_mul_of_nonneg_left (capHP_le_linear hs) hc
  have hR:=mul_le_mul_of_nonneg_left (capRadius_cube_bound s) (show 0≤5*(capP-capEta)*s by positivity)
  have hex:0≤(15*(1-capP)-(15/2)*(capP-capEta))*s^3*capRadius s := by
    have hh:0≤15*(1-capP)-(15/2)*(capP-capEta):=by linarith [capP_bounds.2,capEta_bounds.1]
    exact mul_nonneg (mul_nonneg hh (pow_nonneg hs 3)) (capRadius_pos s).le
  nlinarith

lemma hasDerivAt_capZ {q : ℝ} (hq : 0<q) : HasDerivAt capZ (capZP q) q := by
  convert! (hasDerivAt_capW (Real.sqrt q)).comp q (Real.hasDerivAt_sqrt hq.ne') using 1
  dsimp [capZP]
  ring
lemma hasDerivAt_capZP {q : ℝ} (hq : 0<q) :
    HasDerivAt capZP ((Real.sqrt q*capWPP (Real.sqrt q)-capWP (Real.sqrt q))/(4*(Real.sqrt q)^3)) q := by
  have hs:=Real.sqrt_pos.mpr hq
  convert! ((hasDerivAt_capWP (Real.sqrt q)).comp q (Real.hasDerivAt_sqrt hq.ne')).div
    ((Real.hasDerivAt_sqrt hq.ne').const_mul 2) (by positivity : 2*Real.sqrt q≠0) using 1
  simp only [Function.comp_apply]
  field_simp [hs.ne']
  ring
lemma capZ_convex : ConvexOn ℝ (Set.Icc 0 (9/16:ℝ)) capZ := by
  have hcont : Continuous capZ := (continuous_iff_continuousAt.mpr (fun s=>(hasDerivAt_capW s).continuousAt)).comp Real.continuous_sqrt
  have hp {q : ℝ} (hq : 0<q) : deriv capZ=ᶠ[𝓝 q] capZP := by
    filter_upwards [Ioi_mem_nhds hq] with t ht
    exact (hasDerivAt_capZ ht).deriv
  apply convexOn_of_deriv2_nonneg (convex_Icc _ _) hcont.continuousOn
  · intro q hq
    rw [interior_Icc] at hq
    exact (hasDerivAt_capZ hq.1).differentiableAt.differentiableWithinAt
  · intro q hq
    rw [interior_Icc] at hq
    exact ((hasDerivAt_capZP hq.1).congr_of_eventuallyEq (hp hq.1)).differentiableAt.differentiableWithinAt
  · intro q hq
    rw [interior_Icc] at hq
    rw [Function.iterate_succ_apply',Function.iterate_one,(hp hq.1).deriv_eq,(hasDerivAt_capZP hq.1).deriv]
    exact div_nonneg (capW_radial_convex (Real.sqrt_nonneg q)) (by positivity)

/-- The exact jump sign at the cylindrical gluing interface of the outer
harmonic perturbation and the interior smooth cap. -/
theorem cap_interface_nonpos {s : ℝ} (hs : |s|≤3/4) : capW s≤0 := by
  have hsq : s^2∈Set.Icc (0:ℝ) (9/16) := ⟨sq_nonneg s,by nlinarith [sq_abs s,abs_nonneg s]⟩
  have hh:=capZ_convex.le_max_of_mem_Icc (by norm_num : (0:ℝ)∈Set.Icc 0 (9/16:ℝ))
    (by norm_num : (9/16:ℝ)∈Set.Icc 0 (9/16:ℝ)) hsq
  have hz0:capZ 0=capW 0:=by simp [capZ]
  have hz1:capZ (9/16)=0:=by
    rw [capZ,show Real.sqrt (9/16:ℝ)=3/4 by norm_num,capW_end]
  rw [hz0,hz1,max_eq_right capW_zero_nonpos] at hh
  dsimp [capZ] at hh
  rw [Real.sqrt_sq_eq_abs] at hh
  rcases le_total 0 s with hp|hn
  · simpa only [abs_of_nonneg hp] using hh
  · simpa only [abs_of_nonpos hn,capW_even] using hh

end Bernoulli.DeSilvaJerison
noncomputable section
namespace Bernoulli.DeSilvaJerison.CapAlgebra

lemma Mlo_0_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Mlo_0 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Mlo_0
  positivity
lemma Mlo_1_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Mlo_1 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Mlo_1
  positivity
lemma Mlo_2_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Mlo_2 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Mlo_2
  positivity
lemma Mlo_3_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Mlo_3 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Mlo_3
  positivity
lemma Mlo_4_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Mlo_4 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Mlo_4
  positivity
lemma identity_Mlo (u z:ℝ) :
    (let b:ℝ := 2242/10000+z/10000; MN u b)=bern_Mlo u z := by
  dsimp
  simp only [MN, H,D, E, bern_Mlo, Mlo_0, Mlo_1, Mlo_2, Mlo_3, Mlo_4]
  ring
lemma Mlo_nonneg {u b:ℝ} (hu:0≤u) (hu1:u≤1) (hb:2242/10000≤b) (hb1:b≤2243/10000) :
    0≤MN u b := by
  let z:ℝ := (b-2242/10000)*10000
  have hz:0≤z:=by dsimp [z]; linarith
  have hz1:z≤1:=by dsimp [z]; linarith
  have he:2242/10000+z/10000=b:=by dsimp [z]; ring
  have hi:=identity_Mlo u z
  dsimp only at hi
  rw [he] at hi
  rw [hi]
  have hx:0≤1-u:=sub_nonneg.mpr hu1
  have h0:= Mlo_0_nonneg hz hz1
  have h1:= Mlo_1_nonneg hz hz1
  have h2:= Mlo_2_nonneg hz hz1
  have h3:= Mlo_3_nonneg hz hz1
  have h4:= Mlo_4_nonneg hz hz1
  unfold bern_Mlo
  positivity
lemma Mhi_0_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Mhi_0 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Mhi_0
  positivity
lemma Mhi_1_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Mhi_1 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Mhi_1
  positivity
lemma Mhi_2_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Mhi_2 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Mhi_2
  positivity
lemma Mhi_3_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Mhi_3 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Mhi_3
  positivity
lemma Mhi_4_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Mhi_4 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Mhi_4
  positivity
lemma identity_Mhi (u z:ℝ) :
    (let b:ℝ := 2242/10000+z/10000; 673/250*H u b-MN u b)=bern_Mhi u z := by
  dsimp
  simp only [MN, H,D, E, bern_Mhi, Mhi_0, Mhi_1, Mhi_2, Mhi_3, Mhi_4]
  ring
lemma Mhi_nonneg {u b:ℝ} (hu:0≤u) (hu1:u≤1) (hb:2242/10000≤b) (hb1:b≤2243/10000) :
    0≤673/250*H u b-MN u b := by
  let z:ℝ := (b-2242/10000)*10000
  have hz:0≤z:=by dsimp [z]; linarith
  have hz1:z≤1:=by dsimp [z]; linarith
  have he:2242/10000+z/10000=b:=by dsimp [z]; ring
  have hi:=identity_Mhi u z
  dsimp only at hi
  rw [he] at hi
  rw [hi]
  have hx:0≤1-u:=sub_nonneg.mpr hu1
  have h0:= Mhi_0_nonneg hz hz1
  have h1:= Mhi_1_nonneg hz hz1
  have h2:= Mhi_2_nonneg hz hz1
  have h3:= Mhi_3_nonneg hz hz1
  have h4:= Mhi_4_nonneg hz hz1
  unfold bern_Mhi
  positivity
lemma Nlo_0_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nlo_0 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nlo_0
  positivity
lemma Nlo_1_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nlo_1 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nlo_1
  positivity
lemma Nlo_2_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nlo_2 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nlo_2
  positivity
lemma Nlo_3_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nlo_3 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nlo_3
  positivity
lemma Nlo_4_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nlo_4 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nlo_4
  positivity
lemma Nlo_5_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nlo_5 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nlo_5
  positivity
lemma Nlo_6_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nlo_6 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nlo_6
  positivity
lemma Nlo_7_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nlo_7 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nlo_7
  positivity
lemma identity_Nlo (u z:ℝ) :
    (let b:ℝ := 2242/10000+z/10000; NN u b)=bern_Nlo u z := by
  dsimp
  simp only [NN, MN, H, V, D, E, bern_Nlo, Nlo_0, Nlo_1, Nlo_2, Nlo_3, Nlo_4, Nlo_5, Nlo_6, Nlo_7]
  ring
lemma Nlo_nonneg {u b:ℝ} (hu:0≤u) (hu1:u≤1) (hb:2242/10000≤b) (hb1:b≤2243/10000) :
    0≤NN u b := by
  let z:ℝ := (b-2242/10000)*10000
  have hz:0≤z:=by dsimp [z]; linarith
  have hz1:z≤1:=by dsimp [z]; linarith
  have he:2242/10000+z/10000=b:=by dsimp [z]; ring
  have hi:=identity_Nlo u z
  dsimp only at hi
  rw [he] at hi
  rw [hi]
  have hx:0≤1-u:=sub_nonneg.mpr hu1
  have h0:= Nlo_0_nonneg hz hz1
  have h1:= Nlo_1_nonneg hz hz1
  have h2:= Nlo_2_nonneg hz hz1
  have h3:= Nlo_3_nonneg hz hz1
  have h4:= Nlo_4_nonneg hz hz1
  have h5:= Nlo_5_nonneg hz hz1
  have h6:= Nlo_6_nonneg hz hz1
  have h7:= Nlo_7_nonneg hz hz1
  unfold bern_Nlo
  positivity
lemma Nhi_0_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nhi_0 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nhi_0
  positivity
lemma Nhi_1_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nhi_1 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nhi_1
  positivity
lemma Nhi_2_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nhi_2 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nhi_2
  positivity
lemma Nhi_3_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nhi_3 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nhi_3
  positivity
lemma Nhi_4_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nhi_4 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nhi_4
  positivity
lemma Nhi_5_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nhi_5 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nhi_5
  positivity
lemma Nhi_6_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nhi_6 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nhi_6
  positivity
lemma Nhi_7_nonneg {z:ℝ} (hz:0≤z) (hz1:z≤1) : 0≤Nhi_7 z := by
  have hh:0≤1-z:=sub_nonneg.mpr hz1
  unfold Nhi_7
  positivity
lemma identity_Nhi (u z:ℝ) :
    (let b:ℝ := 2242/10000+z/10000; 431/200*(H u b)^2-NN u b)=bern_Nhi u z := by
  dsimp
  simp only [NN, MN, H, V, D, E, bern_Nhi, Nhi_0, Nhi_1, Nhi_2, Nhi_3, Nhi_4, Nhi_5, Nhi_6, Nhi_7]
  ring
lemma Nhi_nonneg {u b:ℝ} (hu:0≤u) (hu1:u≤1) (hb:2242/10000≤b) (hb1:b≤2243/10000) :
    0≤431/200*(H u b)^2-NN u b := by
  let z:ℝ := (b-2242/10000)*10000
  have hz:0≤z:=by dsimp [z]; linarith
  have hz1:z≤1:=by dsimp [z]; linarith
  have he:2242/10000+z/10000=b:=by dsimp [z]; ring
  have hi:=identity_Nhi u z
  dsimp only at hi
  rw [he] at hi
  rw [hi]
  have hx:0≤1-u:=sub_nonneg.mpr hu1
  have h0:= Nhi_0_nonneg hz hz1
  have h1:= Nhi_1_nonneg hz hz1
  have h2:= Nhi_2_nonneg hz hz1
  have h3:= Nhi_3_nonneg hz hz1
  have h4:= Nhi_4_nonneg hz hz1
  have h5:= Nhi_5_nonneg hz hz1
  have h6:= Nhi_6_nonneg hz hz1
  have h7:= Nhi_7_nonneg hz hz1
  unfold bern_Nhi
  positivity

lemma coeff_bounds {u b:ℝ} (hu:0≤u) (hu1:u≤1) (hb:2242/10000≤b) (hb1:b≤2243/10000) :
    0≤MN u b/H u b ∧ MN u b/H u b≤673/250 ∧
      0≤NN u b/(H u b)^2 ∧ NN u b/(H u b)^2≤431/200 := by
  have hh:=H_pos (b:=b) hu
  refine ⟨div_nonneg (Mlo_nonneg hu hu1 hb hb1) hh.le,?_,
    div_nonneg (Nlo_nonneg hu hu1 hb hb1) (sq_nonneg _),?_⟩
  · rw [div_le_iff₀ hh]
    linarith [Mhi_nonneg hu hu1 hb hb1]
  · rw [div_le_iff₀ (sq_pos_of_pos hh)]
    linarith [Nhi_nonneg hu hu1 hb hb1]
end Bernoulli.DeSilvaJerison.CapAlgebra

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.CapCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
namespace CapAlgebra
lemma hasDerivAt_E (q b:ℝ) : HasDerivAt (fun q=>E q b) (-9/50) q := by
  convert! (hasDerivAt_const q (2*b)).sub ((hasDerivAt_id q).const_mul (9/50)) using 1
  ring
lemma hasDerivAt_Y1 {q b C:ℝ} (hH:0<H q b) : HasDerivAt (fun q=>Y1 q b C) (Y2 q b C) q := by
  have hS:=Real.sqrt_pos.mpr hH
  have hs := (hasDerivAt_H q b).sqrt hH.ne'
  have hd := hasDerivAt_D q b
  have he := hasDerivAt_E q b
  have hv := hasDerivAt_V q b
  convert! (((hd.div_const 2).div hs hS.ne').sub
    ((hv.mul ((hd.const_mul (9/16)).mul he)).div ((hs.pow 3).const_mul 2) (mul_ne_zero (by norm_num) (pow_ne_zero _ hS.ne')))).const_mul C using 1
  dsimp [Y1,Y2]
  field_simp
  ring
lemma deriv2_Y {q b C:ℝ} (hH:0<H q b) : deriv (deriv (fun q=>Y q b C)) q=Y2 q b C := by
  have hh : deriv (fun q=>Y q b C)=ᶠ[𝓝 q] fun q=>Y1 q b C := by
    filter_upwards [(H_contDiff b (n:=∞)).continuous.continuousAt.eventually (Ioi_mem_nhds hH)] with t ht
    exact deriv_Y ht
  rw [hh.deriv_eq]
  exact (hasDerivAt_Y1 hH).deriv
lemma deriv2_invV {q b:ℝ} (hv:V q b≠0) :
    deriv (deriv (fun q=>(V q b)⁻¹)) q= (D q b)^2/(2*(V q b)^3)+3/(100*(V q b)^2) := by
  have hh : deriv (fun q=>(V q b)⁻¹)=ᶠ[𝓝 q] fun q=>-D q b/(2*(V q b)^2) := by
    filter_upwards [((V_contDiff b (n:=∞)).continuous.continuousAt.eventually_ne hv)] with t ht
    exact (hasDerivAt_invV ht).deriv
  rw [hh.deriv_eq]
  have hd := ((hasDerivAt_D q b).neg.div (((hasDerivAt_V q b).pow 2).const_mul 2) (by positivity : 2*(V q b)^2≠0)).deriv
  change deriv (fun q=>-D q b/(2*(V q b)^2)) q = _ at hd
  rw [hd]
  simp only [Pi.pow_apply,Pi.neg_apply]
  field_simp
  ring
lemma lap_Y {q b C:ℝ} (hV:V q b≠0) (hH:0<H q b) :
    4*q*Y2 q b C+12*Y1 q b C = Y q b C/V q b*(NN q b/(H q b)^2) := by
  have hS := (Real.sqrt_pos.mpr hH).ne'
  have hSq := Real.sq_sqrt hH.le
  have hE : E q b=D q b-3/25*q := by unfold E D; ring
  unfold Y Y1 Y2 NN MN
  generalize hvv : V q b=v at *
  generalize hdd : D q b=z at *
  generalize hee : E q b=e at *
  generalize hhh : H q b=h at *
  have hdef : h=1+9/16*q*z^2 := by rw [←hhh, H, hdd]
  field_simp [hS,hV,hH.ne']
  ring_nf
  simp only [show Real.sqrt h^4=h^2 by calc
    _ = (Real.sqrt h^2)^2 := by ring
    _ = _ := by rw [hSq], hSq]
  rw [hE,hdef]
  ring

lemma invV_mixed {q b C:ℝ} (hV:V q b≠0) (hH:0<H q b) :
    Y q b C*(4*q*((D q b)^2/(2*(V q b)^3)+3/(100*(V q b)^2))+
      12*(-D q b/(2*(V q b)^2)))+8*q*Y1 q b C*(-D q b/(2*(V q b)^2)) =
      -Y q b C/(V q b)^2*(MN q b/H q b) := by
  have hS := (Real.sqrt_pos.mpr hH).ne'
  have hSq := Real.sq_sqrt hH.le
  have hE : E q b=D q b-3/25*q := by unfold E D; ring
  unfold Y Y1 MN
  generalize hvv : V q b=v at *
  generalize hdd : D q b=z at *
  generalize hee : E q b=e at *
  generalize hhh : H q b=h at *
  have hdef : h=1+9/16*q*z^2 := by rw [←hhh, H, hdd]
  field_simp [hS,hV,hH.ne']
  ring_nf
  rw [hSq,hE,hdef]
  ring

end CapAlgebra

lemma deriv2_capH (s:ℝ) : deriv (deriv capH) s=-5*(capRadius s)^3+4*capAmplitude := by
  have hh : deriv capH=capHP := funext fun t=>(hasDerivAt_capH t).deriv
  rw [hh]
  exact (hasDerivAt_capHP s).deriv

lemma laplacian_smoothCap {x:Space 7} (hx:Cylindrical.radiusSq axis x≤1) :
    let q := Cylindrical.radiusSq axis x
    let V := CapAlgebra.V q capB
    let ξ := Cylindrical.axis axis x/V
    Δ smoothCap x = CapAlgebra.Y q capB capC/V^2 *
      ((-5*(capRadius ξ)^3+4*capAmplitude)*(1+q*ξ^2*(CapAlgebra.D q capB)^2)-
        ξ*capHP ξ*V*(CapAlgebra.MN q capB/CapAlgebra.H q capB)+
        capH ξ*V*(CapAlgebra.NN q capB/(CapAlgebra.H q capB)^2)) := by
  dsimp only
  let q := Cylindrical.radiusSq axis x
  let a := Cylindrical.axis axis x
  have hq : 0≤q := Cylindrical.radiusSq_nonneg axis x axis_norm
  have hv := (CapAlgebra.V_bounds hq hx capB_bounds.1 capB_bounds.2).1
  have hh := CapAlgebra.H_pos (b:=capB) hq
  have hc := Cylindrical.laplacian_lift axis_norm
    (CapAlgebra.Y_contDiffAt (C:=capC) (n:=2) hh)
    ((CapAlgebra.V_contDiff capB (n:=2)).contDiffAt.inv hv.ne')
    (capH_contDiff.of_le (by norm_cast : (2:WithTop ℕ∞)≤∞)).contDiffAt
  change Δ smoothCap x=_ at hc
  simp only [Space,finrank_euclideanSpace_fin,Nat.cast_ofNat] at hc
  norm_num only at hc
  change Δ smoothCap x =
    CapAlgebra.Y q capB capC * deriv (deriv capH) (a*(CapAlgebra.V q capB)⁻¹) *
      (((CapAlgebra.V q capB)⁻¹)^2+4*q*a^2*deriv (fun q=>(CapAlgebra.V q capB)⁻¹) q^2)+
    deriv capH (a*(CapAlgebra.V q capB)⁻¹)*
      (a*CapAlgebra.Y q capB capC*(4*q*deriv (deriv (fun q=>(CapAlgebra.V q capB)⁻¹)) q+
        12*deriv (fun q=>(CapAlgebra.V q capB)⁻¹) q)+
        8*q*a*deriv (fun q=>CapAlgebra.Y q capB capC) q*deriv (fun q=>(CapAlgebra.V q capB)⁻¹) q)+
    capH (a*(CapAlgebra.V q capB)⁻¹)*(4*q*deriv (deriv (fun q=>CapAlgebra.Y q capB capC)) q+
      12*deriv (fun q=>CapAlgebra.Y q capB capC) q) at hc
  rw [hc]
  simp only [CapAlgebra.deriv_Y hh, CapAlgebra.deriv2_Y hh,
    (CapAlgebra.hasDerivAt_invV hv.ne').deriv, CapAlgebra.deriv2_invV hv.ne',
    deriv2_capH,(hasDerivAt_capH _).deriv]
  change _ = CapAlgebra.Y q capB capC/(CapAlgebra.V q capB)^2 * _
  have hm:=CapAlgebra.invV_mixed (C:=capC) hv.ne' hh
  have hn:=CapAlgebra.lap_Y (C:=capC) hv.ne' hh
  have h1 : ((CapAlgebra.V q capB)⁻¹)^2+4*q*a^2*(-CapAlgebra.D q capB/(2*(CapAlgebra.V q capB)^2))^2 =
      (1+q*(a/CapAlgebra.V q capB)^2*(CapAlgebra.D q capB)^2)/(CapAlgebra.V q capB)^2 := by
    field_simp
    ring
  have h2 : a*CapAlgebra.Y q capB capC*
      (4*q*((CapAlgebra.D q capB)^2/(2*(CapAlgebra.V q capB)^3)+3/(100*(CapAlgebra.V q capB)^2))+
        12*(-CapAlgebra.D q capB/(2*(CapAlgebra.V q capB)^2)))+
      8*q*a*CapAlgebra.Y1 q capB capC*(-CapAlgebra.D q capB/(2*(CapAlgebra.V q capB)^2)) =
      -a*CapAlgebra.Y q capB capC/(CapAlgebra.V q capB)^2*(CapAlgebra.MN q capB/CapAlgebra.H q capB) := by
    calc
      _ = a*(CapAlgebra.Y q capB capC*
          (4*q*((CapAlgebra.D q capB)^2/(2*(CapAlgebra.V q capB)^3)+3/(100*(CapAlgebra.V q capB)^2))+
            12*(-CapAlgebra.D q capB/(2*(CapAlgebra.V q capB)^2)))+
          8*q*CapAlgebra.Y1 q capB capC*(-CapAlgebra.D q capB/(2*(CapAlgebra.V q capB)^2))) := by ring
      _ = _ := by rw [hm]; ring
  rw [h1,h2,hn]
  change _=CapAlgebra.Y q capB capC/(CapAlgebra.V q capB)^2 *
    ((-5*(capRadius (a/CapAlgebra.V q capB))^3+4*capAmplitude)*(1+q*(a/CapAlgebra.V q capB)^2*(CapAlgebra.D q capB)^2)-
      (a/CapAlgebra.V q capB)*capHP (a/CapAlgebra.V q capB)*CapAlgebra.V q capB*(CapAlgebra.MN q capB/CapAlgebra.H q capB)+
      capH (a/CapAlgebra.V q capB)*CapAlgebra.V q capB*(CapAlgebra.NN q capB/(CapAlgebra.H q capB)^2))
  simp only [← div_eq_mul_inv]
  field_simp
  ring
lemma cap_sHP_nonpos (s:ℝ) : s*capHP s≤0 := by
  rcases le_total 0 s with h|h
  · exact mul_nonpos_of_nonneg_of_nonpos h (capHP_nonpos h)
  · have hh:=mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr h) (capHP_nonpos (neg_nonneg.mpr h))
    simpa only [capHP_odd,neg_mul_neg] using hh

/-- The actual smooth cylindrical cap is superharmonic on its positive strip. -/
theorem smoothCap_laplacian_nonpos {x:Space 7} (hx:Cylindrical.radiusSq axis x≤1)
    (hs:|Cylindrical.axis axis x/CapAlgebra.V (Cylindrical.radiusSq axis x) capB|≤3/4) :
    Δ smoothCap x≤0 := by
  let q:=Cylindrical.radiusSq axis x
  let V:=CapAlgebra.V q capB
  let s:=Cylindrical.axis axis x/V
  have hq:0≤q:=Cylindrical.radiusSq_nonneg axis x axis_norm
  obtain ⟨hv,hv1⟩:=CapAlgebra.V_bounds hq hx capB_bounds.1 capB_bounds.2
  obtain ⟨hM,hM1,hN,hN1⟩:=CapAlgebra.coeff_bounds hq hx capB_bounds.1 capB_bounds.2
  have hh:=capH_nonneg hs
  have hph:=capHPP_nonpos s
  have hsp:=cap_sHP_nonpos s
  have hK:=cap_K_nonpos hs
  change -5*capRadius s^3+4*capAmplitude-(673/250)*s*capHP s+(431/200)*capH s≤0 at hK
  have hvm : V*(CapAlgebra.MN q capB/CapAlgebra.H q capB)≤673/250 :=
    (mul_le_mul_of_nonneg_right hv1 hM).trans (by simpa using hM1)
  have hvn : V*(CapAlgebra.NN q capB/(CapAlgebra.H q capB)^2)≤431/200 :=
    (mul_le_mul_of_nonneg_right hv1 hN).trans (by simpa using hN1)
  have h0:=mul_nonpos_of_nonpos_of_nonneg hph
    (show 0≤q*s^2*(CapAlgebra.D q capB)^2 by positivity)
  have h1:=mul_le_mul_of_nonneg_left hvm (neg_nonneg.mpr hsp)
  have h2:=mul_le_mul_of_nonneg_left hvn hh
  have hbr : (-5*capRadius s^3+4*capAmplitude)*(1+q*s^2*(CapAlgebra.D q capB)^2)-
      s*capHP s*V*(CapAlgebra.MN q capB/CapAlgebra.H q capB)+
      capH s*V*(CapAlgebra.NN q capB/(CapAlgebra.H q capB)^2)≤0 := by
    nlinarith only [h0,h1,h2,hK]
  rw [laplacian_smoothCap hx]
  have hY:0≤CapAlgebra.Y q capB capC := by unfold CapAlgebra.Y capC; positivity
  exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg hY (sq_nonneg V)) hbr

end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.OuterGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
open Axisymmetric

lemma hasDerivAt_gSup1 {t:ℝ} (ht:|t|<1) : HasDerivAt gSup1 (gSup2 t) t := by
  have hd:1-t^2≠0 := by obtain ⟨h1,h2⟩:=abs_lt.mp ht; nlinarith
  convert! ((((hasDerivAt_id t).const_mul 2).mul
    ((hasDerivAt_const t (3:ℝ)).add ((hasDerivAt_id t).pow 2))).div
      (((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).pow 2)).pow 3)
        (pow_ne_zero 3 hd)) using 1
  norm_num only [gSup1,gSup2,id_eq,pow_one,Pi.add_apply,Pi.sub_apply,Pi.pow_apply,Pi.mul_apply]
  field_simp [hd]
  ring
lemma gSup_equation {t:ℝ} (ht:|t|<1) : (1-t^2)*gSup2 t-6*t*gSup1 t-6*gSup t=0 := by
  have hd:1-t^2≠0 := by obtain ⟨h1,h2⟩:=abs_lt.mp ht; nlinarith
  unfold gSup2 gSup1 gSup
  field_simp [hd]
  ring

lemma KSup_laplacian {x:Space 7} (hx:x≠0) (ha:|angle x|<1) : Δ KSup x=0 := by
  have hi:|inner ℝ x axis/‖x‖|<1:=by simpa only [inner_axis,angle] using ha
  have hp:∀ᶠ s in 𝓝 (inner ℝ x axis/‖x‖),HasDerivAt gSup (gSup1 s) s := by
    filter_upwards [isOpen_Ioo.mem_nhds (abs_lt.mp hi)] with s hs
    exact hasDerivAt_gSup (abs_lt.mpr hs)
  have hh:=laplacian_lift axis x (-2) axis_norm hx (gSup_contDiffAt hi) hp (hasDerivAt_gSup1 hi)
  have he:=gSup_equation hi
  simp only [Space,finrank_euclideanSpace_fin,Nat.cast_ofNat] at hh
  norm_num only at hh
  rw [KSup,hh]
  convert mul_zero (‖x‖^(-2:ℝ)/‖x‖^2) using 1
  congr 1
  linarith
lemma outerSigned_laplacian {x:Space 7} (hx:x≠0) (ha:|angle x|<1) : Δ outerSigned x=0 := by
  have hc : ContDiffAt ℝ 2 (fun y:Space 7=>capAmplitude*KSup y) x :=
    contDiffAt_const.mul (KSup_contDiffAt hx ha)
  have hadd : Δ outerSigned x=Δ Zsigned x+Δ (fun y:Space 7=>capAmplitude*KSup y) x :=
    (signed_contDiffAt hx ha).laplacian_add hc
  have hmul : Δ (fun y:Space 7=>capAmplitude*KSup y) x=capAmplitude*Δ KSup x :=
    InnerProductSpace.laplacian_smul capAmplitude (KSup_contDiffAt hx ha)
  rw [hadd,hmul,signed_laplacian hx ha,KSup_laplacian hx ha]
  ring

lemma outerSigned_radial_defect_pos {x:Space 7} (hx:x≠0) (ha:|angle x|<1) :
    0<outerSigned x-inner ℝ x (gradient outerSigned x) := by
  rw [outerSigned_radial_defect hx ha]
  exact mul_pos (mul_pos (by norm_num) capAmplitude_pos) (KSup_pos hx ha)

end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperSeam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.Cylindrical
lemma axis_add_axis {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e x:E) (he:‖e‖=1) (t:ℝ) : axis e (x+t • e)=axis e x+t := by
  simp [axis,inner_add_left,real_inner_smul_left,he]
lemma radiusSq_add_axis {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e x:E) (he:‖e‖=1) (t:ℝ) : radiusSq e (x+t • e)=radiusSq e x := by
  simp only [radiusSq,axis_add_axis e x he,norm_add_sq_real,norm_smul,
    Real.norm_eq_abs,sq_abs,he,mul_one,real_inner_smul_right]
  unfold axis
  ring
end Bernoulli.Cylindrical
namespace Bernoulli.DeSilvaJerison

namespace CapAlgebra
lemma E_one : E 1 capB=capP-3/25 := by unfold E capB; ring
lemma Y1_one : 2*Y1 1 capB capC=capEta := by
  rw [Y1_eq (H_pos (by norm_num)) (by rw [V_one]; norm_num),Y_one,V_one,D_one,E_one,H_one,capC_sq]
  simp only [one_mul,div_one,capEta]
end CapAlgebra

lemma outerSigned_axis_at_seam {x:Space 7} (hq:Cylindrical.radiusSq axis x=1) :
    inner ℝ (gradient outerSigned x) axis=capHP (Cylindrical.axis axis x) := by
  have hqp:0<Cylindrical.radiusSq axis x:=by rw [hq]; norm_num
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hqp
  rw [←ScalarLaplacian.line_deriv ((outerSigned_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)) axis]
  have he : (fun t:ℝ=>outerSigned (x+t • axis))=fun t=>capH (Cylindrical.axis axis x+t) := by
    funext t
    rw [outerSigned_at_seam (by rw [Cylindrical.radiusSq_add_axis axis x axis_norm,hq]),
      Cylindrical.axis_add_axis axis x axis_norm]
  rw [he]
  have hh:HasDerivAt (fun t:ℝ=>capH (Cylindrical.axis axis x+t)) (capHP (Cylindrical.axis axis x)) 0 := by
    convert! (hasDerivAt_capH (Cylindrical.axis axis x+0)).comp 0 ((hasDerivAt_id 0).const_add (Cylindrical.axis axis x)) using 1
    simp
  exact hh.deriv

lemma outerSigned_transverse_at_seam {x:Space 7} (hq:Cylindrical.radiusSq axis x=1) :
    inner ℝ (gradient outerSigned x) (Cylindrical.transverse axis x)=
      capH (Cylindrical.axis axis x)-Cylindrical.axis axis x*capHP (Cylindrical.axis axis x)-
        3*capAmplitude*(1+2*(Cylindrical.axis axis x)^2) := by
  have hqp:0<Cylindrical.radiusSq axis x:=by rw [hq]; norm_num
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hqp
  have hh:=outerSigned_radial_defect hx ha
  rw [outerSigned_at_seam hq,KSup_cylindrical hqp,hq] at hh
  norm_num only [one_pow,div_one] at hh
  rw [Cylindrical.transverse,inner_sub_right,real_inner_smul_right,outerSigned_axis_at_seam hq,
    real_inner_comm x (gradient outerSigned x)]
  linarith

lemma smoothCap_transverse_at_seam {x:Space 7} (hq:Cylindrical.radiusSq axis x=1) :
    inner ℝ (gradient smoothCap x) (Cylindrical.transverse axis x)=
      capEta*capH (Cylindrical.axis axis x)-
        capP*Cylindrical.axis axis x*capHP (Cylindrical.axis axis x) := by
  have he:inner ℝ axis (Cylindrical.transverse axis x)=0 := by
    rw [real_inner_comm,Cylindrical.transverse_inner axis x axis_norm]
  have ht:inner ℝ (Cylindrical.transverse axis x) (Cylindrical.transverse axis x)=1 := by
    rw [real_inner_self_eq_norm_sq,Cylindrical.transverse_sq axis x axis_norm,hq]
  rw [gradient_smoothCap (le_of_eq hq)]
  simp only [hq,CapAlgebra.V_one,CapAlgebra.Y_one,CapAlgebra.D_one,CapAlgebra.Y1_one,
    div_one,one_pow,inv_one,one_mul,inner_add_left,real_inner_smul_left,he,ht,mul_zero,mul_one,zero_add]
  ring

/-- Actual normal derivative jump of the glued Euclidean supersolution. -/
theorem upper_seam_jump {x:Space 7} (hq:Cylindrical.radiusSq axis x=1)
    (ha:|Cylindrical.axis axis x|≤3/4) :
    inner ℝ (gradient outerSigned x-gradient smoothCap x) (Cylindrical.transverse axis x)≤0 := by
  rw [inner_sub_left,outerSigned_transverse_at_seam hq,smoothCap_transverse_at_seam hq]
  have he : capH (Cylindrical.axis axis x)-Cylindrical.axis axis x*capHP (Cylindrical.axis axis x)-
      3*capAmplitude*(1+2*(Cylindrical.axis axis x)^2)-
      (capEta*capH (Cylindrical.axis axis x)-capP*Cylindrical.axis axis x*capHP (Cylindrical.axis axis x))=
        capW (Cylindrical.axis axis x) := by unfold capW; ring
  rw [he]
  exact cap_interface_nonpos ha
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
lemma outerSigned_cylindrical {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    let r:=Real.sqrt (Cylindrical.radiusSq axis x)
    let s:=Cylindrical.axis axis x/r
    outerSigned x=r*capH s+capAmplitude*((Cylindrical.radiusSq axis x)⁻¹-r)*(1+2*s^2) := by
  dsimp only
  let q:=Cylindrical.radiusSq axis x
  let r:=Real.sqrt q
  let a:=Cylindrical.axis axis x
  have hr:0<r:=Real.sqrt_pos.mpr hq
  have hr2:r^2=q:=Real.sq_sqrt hq.le
  let y:=r⁻¹ • x
  have hy:Cylindrical.radiusSq axis y=1 := by
    rw [Cylindrical.radiusSq_smul]
    change (r⁻¹)^2*q=1
    rw [←hr2]; field_simp
  have hay:Cylindrical.axis axis y=a/r := by rw [Cylindrical.axis_smul]; dsimp [a]; ring
  have he:=outerSigned_at_seam hy
  rw [outerSigned,Zsigned_smul x (inv_pos.mpr hr),KSup_smul hq (inv_pos.mpr hr),hay] at he
  change r⁻¹*Zsigned x+capAmplitude*( (r⁻¹)^(-2:ℤ)*KSup x)=capH (a/r) at he
  norm_num only [zpow_neg,zpow_ofNat,inv_inv] at he
  rw [outerSigned,KSup_cylindrical hq]
  rw [KSup_cylindrical hq] at he
  change Zsigned x+capAmplitude*((q+2*a^2)/q^2)=r*capH (a/r)+capAmplitude*(q⁻¹-r)*(1+2*(a/r)^2)
  change r⁻¹*Zsigned x+capAmplitude*((r⁻¹^2)⁻¹*((q+2*a^2)/q^2))=capH (a/r) at he
  rw [←he,←hr2]
  field_simp
  ring

lemma capH_nonneg_iff (s:ℝ) : 0≤capH s ↔ |s|≤3/4 := by
  constructor
  · intro hs
    by_contra hn
    have hh:=capH_strictAnti (show (3/4:ℝ)∈Ici 0 by norm_num) (abs_nonneg s) (lt_of_not_ge hn)
    rw [capH_end,capH_abs] at hh
    linarith
  · exact capH_nonneg
lemma outer_nonnegative_sector {x:Space 7} (hq:1≤Cylindrical.radiusSq axis x) (hp:0≤outerSigned x) :
    |Cylindrical.axis axis x/Real.sqrt (Cylindrical.radiusSq axis x)|≤3/4 := by
  have hqp:0<Cylindrical.radiusSq axis x:=by linarith
  have hr:1≤Real.sqrt (Cylindrical.radiusSq axis x):= (Real.le_sqrt (by norm_num) hqp.le).mpr (by simpa)
  have hqi:(Cylindrical.radiusSq axis x)⁻¹≤1 := inv_le_one_of_one_le₀ hq
  have hs:capAmplitude*((Cylindrical.radiusSq axis x)⁻¹-Real.sqrt (Cylindrical.radiusSq axis x))*
      (1+2*(Cylindrical.axis axis x/Real.sqrt (Cylindrical.radiusSq axis x))^2)≤0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos capAmplitude_pos.le (by linarith)) (by positivity)
  rw [outerSigned_cylindrical hqp] at hp
  have hh:0≤capH (Cylindrical.axis axis x/Real.sqrt (Cylindrical.radiusSq axis x)) := by
    apply nonneg_of_mul_nonneg_right (show 0≤Real.sqrt (Cylindrical.radiusSq axis x)*capH
      (Cylindrical.axis axis x/Real.sqrt (Cylindrical.radiusSq axis x)) by linarith) (by positivity)
  exact (capH_nonneg_iff _).mp hh
lemma outer_nonnegative_angle {x:Space 7} (hq:1≤Cylindrical.radiusSq axis x) (hp:0≤outerSigned x) : |angle x|≤3/5 := by
  have hqp:0<Cylindrical.radiusSq axis x:=by linarith
  have hx: x≠0:=(radiusSq_pos_data hqp).1
  have hr:0<Real.sqrt (Cylindrical.radiusSq axis x):=Real.sqrt_pos.mpr hqp
  have hh:=outer_nonnegative_sector hq hp
  rw [abs_div,abs_of_pos hr,div_le_iff₀ hr] at hh
  have hsq:=Real.sq_sqrt hqp.le
  have hn:0<‖x‖:=norm_pos_iff.mpr hx
  rw [angle,abs_div,abs_norm,div_le_iff₀ hn]
  rw [Cylindrical.axis,inner_axis] at hh
  have hh2:= (sq_le_sq₀ (abs_nonneg (x 6)) (show 0≤3/4*Real.sqrt (Cylindrical.radiusSq axis x) by positivity)).mpr hh
  rw [mul_pow,sq_abs,hsq] at hh2
  rw [Cylindrical.radiusSq,Cylindrical.axis,inner_axis] at hh2
  nlinarith [sq_abs (x 6)]

lemma upperFamily_continuous (l:ℝ) : Continuous (upperFamily l) := by
  have hc:Continuous (fun x:Space 7=>l⁻¹ • x):=continuous_id.const_smul l⁻¹
  have hg:Continuous (fun x:Space 7=>max (upperSigned (l⁻¹ • x)) 0):=
    (upperSigned_continuous.comp hc).max continuous_const
  exact continuous_const.mul hg
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.PositiveFoliation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology
namespace Bernoulli.Foliation

lemma monotone_positive_part {f:ℝ→ℝ} {a b:ℝ} (hab:a≤b)
    (hc:ContinuousOn f (Icc a b))
    (hd:∀t∈Ico a b, 0<f t → ∃v:ℝ, 0<v ∧ HasDerivWithinAt f v (Ici t) t) :
    max (f a) 0 ≤ max (f b) 0 := by
  rcases hab.eq_or_lt with h|h
  · simp [h]
  · rcases lt_or_ge 0 (f a) with hp|hp
    · exact max_le_max ((strict_increase_above_zero h hc hp hd).le) le_rfl
    · rw [max_eq_right hp]
      exact le_max_right _ _

end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperFoliation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison

lemma upperFamily_monotone (x:Space 7) : MonotoneOn (fun l=>upperFamily l x) (Ioi 0) := by
  intro a ha b hb hab
  change upperFamily a x ≤ upperFamily b x
  rw [upperFamily_eq_max ha.le,upperFamily_eq_max hb.le]
  exact Foliation.monotone_positive_part hab
    ((upperTrace_continuous x).mono (fun t ht=>ha.trans_le ht.1))
    (fun t ht hp=>upperTrace_right_derivative x (ha.trans_le ht.1) hp)
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology
namespace Bernoulli.DeSilvaJerison

lemma upperParameter_spec {x:Space 7} {t:ℝ} (ht:U x<t) :
    0<upperParameter x t ∧ upperFamily (upperParameter x t) x=t := by
  rw [upperParameter,dite_eq_left ht]
  exact (existsUnique_upper_leaf x ht).exists.choose_spec
lemma upperParameter_unique {x:Space 7} {t l:ℝ} (ht:U x<t) (hl:0<l) (he:upperFamily l x=t) :
    upperParameter x t=l := by
  exact ExistsUnique.unique (existsUnique_upper_leaf x ht) (upperParameter_spec ht) ⟨hl,he⟩
lemma upperParameter_lt_iff {x:Space 7} {t l:ℝ} (ht:U x<t) (hl:0<l) :
    upperParameter x t<l ↔ t<upperFamily l x := by
  obtain ⟨hp,he⟩:=upperParameter_spec ht
  constructor
  · intro h
    rw [←he]
    exact upperFamily_strict hp h (by rw [he]; exact (U_nonneg x).trans_lt ht)
  · intro h
    by_contra hn
    have hh:=upperFamily_monotone x hl hp (le_of_not_gt hn)
    dsimp only at hh
    rw [he] at hh
    linarith
lemma lt_upperParameter_iff {x:Space 7} {t l:ℝ} (ht:U x<t) (hl:0<l) :
    l<upperParameter x t ↔ upperFamily l x<t := by
  obtain ⟨hp,he⟩:=upperParameter_spec ht
  constructor
  · intro h
    by_cases hw:0<upperFamily l x
    · rw [←he]; exact upperFamily_strict hl h hw
    · exact (le_of_not_gt hw).trans_lt ((U_nonneg x).trans_lt ht)
  · intro h
    by_contra hn
    have hh:=upperFamily_monotone x hp hl (le_of_not_gt hn)
    dsimp only at hh
    rw [he] at hh
    linarith
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

lemma upperParameter_continuousAt {p:Space 7×ℝ} (hp:U p.1<p.2) :
    ContinuousAt (fun z:Space 7×ℝ=>upperParameter z.1 z.2) p := by
  have hdom:∀ᶠ z:Space 7×ℝ in 𝓝 p,U z.1<z.2 :=
    (U_continuous.continuousAt.comp continuous_fst.continuousAt).eventually_lt
      continuous_snd.continuousAt hp
  rw [ContinuousAt,tendsto_order]
  constructor
  · intro a ha
    by_cases hapos:0<a
    · have hat:upperFamily a p.1<p.2:=(lt_upperParameter_iff hp hapos).mp ha
      have hnear:∀ᶠ z:Space 7×ℝ in 𝓝 p,upperFamily a z.1<z.2 :=
        ((upperFamily_continuous a).continuousAt.comp continuous_fst.continuousAt).eventually_lt
          continuous_snd.continuousAt hat
      filter_upwards [hdom,hnear] with z hz hz1
      exact (lt_upperParameter_iff hz hapos).mpr hz1
    · filter_upwards [hdom] with z hz
      exact (le_of_not_gt hapos).trans_lt (upperParameter_spec hz).1
  · intro b hb
    have hbpos:0<b := (upperParameter_spec hp).1.trans hb
    have hbt:p.2<upperFamily b p.1:=(upperParameter_lt_iff hp hbpos).mp hb
    have hnear:∀ᶠ z:Space 7×ℝ in 𝓝 p,z.2<upperFamily b z.1 :=
      continuous_snd.continuousAt.eventually_lt
        ((upperFamily_continuous b).continuousAt.comp continuous_fst.continuousAt) hbt
    filter_upwards [hdom,hnear] with z hz hz1
    exact (upperParameter_lt_iff hz hbpos).mpr hz1
lemma upperParameter_continuousOn : ContinuousOn (fun z:Space 7×ℝ=>upperParameter z.1 z.2)
    {z|U z.1<z.2} := fun _ hp=>(upperParameter_continuousAt hp).continuousWithinAt
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.ScalarImplicit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
lemma real_linear_invertible {L:ℝ→L[ℝ] ℝ} (hL:L 1≠0) :L.IsInvertible := by
  have he:∀s:ℝ,L s=s*L 1:=fun s=>by simpa using L.map_smul s (1:ℝ)
  let R:ℝ→L[ℝ] ℝ:=(L 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ
  apply ContinuousLinearMap.IsInvertible.of_inverse (g:=R)
  · apply ContinuousLinearMap.ext
    intro s
    simp only [ContinuousLinearMap.comp_apply,R,smul_apply,
      ContinuousLinearMap.id_apply,smul_eq_mul]
    rw [he]
    field_simp
  · apply ContinuousLinearMap.ext
    intro s
    simp only [ContinuousLinearMap.comp_apply,R,smul_apply,
      ContinuousLinearMap.id_apply,smul_eq_mul]
    rw [he]
    field_simp
    rw [he]
    ring
lemma scalar_implicit {F:E×ℝ→ℝ} {x:E} {l ρ:ℝ}
    (hF:ContDiffAt ℝ ∞ F (x,l)) (hd:HasDerivAt (fun s:ℝ=>F (x,s)) ρ l) (hρ:ρ≠0) :
    ∃ψ:E→ℝ, ContDiffAt ℝ ∞ ψ x ∧ ψ x=l ∧
      ∀ᶠ y in 𝓝 x,F (y,ψ y)=F (x,l) := by
  have hc:HasDerivAt (fun s:ℝ=>F (x,s)) ((fderiv ℝ F (x,l)) (0,1)) l := by
    exact (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt l
      ((hasDerivAt_const l x).prodMk (hasDerivAt_id l))
  have hl:(fderiv ℝ F (x,l) ∘L ContinuousLinearMap.inr ℝ E ℝ) 1=ρ := by
    simpa using hc.unique hd
  have hi:(fderiv ℝ F (x,l) ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible:=
    real_linear_invertible (by rw [hl]; exact hρ)
  exact ⟨hF.implicitFunction (by simp) hi,hF.contDiffAt_implicitFunction (by simp) hi,
    hF.implicitFunction_apply_self (by simp) hi,hF.eventually_apply_implicitFunction (by simp) hi⟩
/-- The local uniqueness clause of the scalar implicit-function theorem is
needed for a smooth extension up to one side of a genuine seam. -/
lemma scalar_implicit_unique {F:E×ℝ→ℝ} {x:E} {l ρ:ℝ}
    (hF:ContDiffAt ℝ ∞ F (x,l)) (hd:HasDerivAt (fun s:ℝ=>F (x,s)) ρ l) (hρ:ρ≠0) :
    ∃ψ:E→ℝ, ContDiffAt ℝ ∞ ψ x ∧ ψ x=l ∧
      (∀ᶠ y in 𝓝 x,F (y,ψ y)=F (x,l)) ∧
      ∀ᶠ z in 𝓝 (x,l), F z=F (x,l) ↔ ψ z.1=z.2 := by
  have hc:HasDerivAt (fun s:ℝ=>F (x,s)) ((fderiv ℝ F (x,l)) (0,1)) l :=
    (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt l
      ((hasDerivAt_const l x).prodMk (hasDerivAt_id l))
  have hl:(fderiv ℝ F (x,l) ∘L ContinuousLinearMap.inr ℝ E ℝ) 1=ρ := by
    simpa using hc.unique hd
  have hi:(fderiv ℝ F (x,l) ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible:=
    real_linear_invertible (by rw [hl]; exact hρ)
  exact ⟨hF.implicitFunction (by simp) hi,hF.contDiffAt_implicitFunction (by simp) hi,
    hF.implicitFunction_apply_self (by simp) hi,
    hF.eventually_apply_implicitFunction (by simp) hi,
    hF.eventually_apply_eq_iff_implicitFunction (by simp) hi⟩
end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperSmoothLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

lemma upperSigned_contDiffAt {x:Space 7} (hq:Cylindrical.radiusSq axis x≠1) :
    ContDiffAt ℝ ∞ upperSigned x := by
  have hcont:ContinuousAt (Cylindrical.radiusSq axis) x :=
    (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt
  rcases lt_or_gt_of_ne hq with h|h
  · apply (smoothCap_contDiffAt h.le).congr_of_eventuallyEq
    filter_upwards [hcont.eventually (gt_mem_nhds h)] with y hy
    exact upperSigned_cap hy.le
  · have hqp:0<Cylindrical.radiusSq axis x:=by linarith
    obtain ⟨hx,ha⟩:=radiusSq_pos_data hqp
    apply (outerSigned_contDiffAt hx ha).congr_of_eventuallyEq
    filter_upwards [hcont.eventually (lt_mem_nhds h)] with y hy
    exact upperSigned_outer hy.le
lemma upperFamily_joint_contDiffAt {p:ℝ×Space 7} (hl:0<p.1)
    (hp:0<upperFamily p.1 p.2) (hq:Cylindrical.radiusSq axis (p.1⁻¹ • p.2)≠1) :
    ContDiffAt ℝ ∞ (fun z:ℝ×Space 7=>upperFamily z.1 z.2) p := by
  have hpos:0<upperSigned (p.1⁻¹ • p.2) := by
    have hh:0 < max (upperSigned (p.1⁻¹ • p.2)) 0:=
      pos_of_mul_pos_right hp (mul_nonneg κ_pos.le hl.le)
    simpa using hh
  have hi:ContDiffAt ℝ ∞ (fun z:ℝ×Space 7=>z.1⁻¹ • z.2) p:=
    (contDiffAt_fst.inv hl.ne').smul contDiffAt_snd
  have hs0 : ContDiffAt ℝ ∞ upperSigned (p.1⁻¹ • p.2) :=
    upperSigned_contDiffAt hq
  have hs:ContDiffAt ℝ ∞ (fun z:ℝ×Space 7=>upperSigned (z.1⁻¹ • z.2)) p := by
    exact ContDiffAt.comp (f:=fun z:ℝ×Space 7=>z.1⁻¹ • z.2) (g:=upperSigned) p hs0 hi
  apply ((contDiffAt_const.mul contDiffAt_fst).mul hs).congr_of_eventuallyEq
  filter_upwards [hs.continuousAt.eventually (lt_mem_nhds hpos)] with z hz
  exact congrArg (κ*z.1* ·) (max_eq_left hz.le)
lemma upperFamily_scale_derivative {x:Space 7} {l:ℝ} (hl:0<l)
    (hp:0<upperFamily l x) (hq:Cylindrical.radiusSq axis (l⁻¹ • x)≠1) :
    ∃ρ:ℝ,0<ρ ∧ HasDerivAt (fun s:ℝ=>upperFamily s x) ρ l := by
  let ρ:=κ*(upperSigned (l⁻¹ • x)-inner ℝ (l⁻¹ • x) (gradient upperSigned (l⁻¹ • x)))
  have hd:HasDerivAt (upperTrace x) ρ l := by
    have hh:HasDerivAt (fun s:ℝ=>κ*(s*upperSigned (s⁻¹ • x))) ρ l:=
      (Foliation.hasDerivAt_dilate x hl.ne'
        ((upperSigned_contDiffAt hq).differentiableAt (by simp))).const_mul κ
    change HasDerivAt (fun s=>κ*s*upperSigned (s⁻¹ • x)) ρ l
    simpa only [mul_assoc] using hh
  have hpt:0<upperTrace x l := by rw [upperFamily_eq_max hl.le x] at hp; simpa using hp
  obtain ⟨v,hv,hdv⟩:=upperTrace_right_derivative x hl hpt
  have he:ρ=v:=(uniqueDiffWithinAt_Ici l).eq_deriv (Ici l) hd.hasDerivWithinAt hdv
  refine ⟨ρ,he.symm ▸ hv,?_⟩
  apply hd.congr_of_eventuallyEq
  have hln:∀ᶠ s:ℝ in 𝓝 l,0<s:=lt_mem_nhds hl
  have hpn:∀ᶠ s:ℝ in 𝓝 l,0<upperTrace x s:=hd.continuousAt.eventually (lt_mem_nhds hpt)
  filter_upwards [hln,hpn] with s hs hs1
  rw [upperFamily_eq_max hs.le,max_eq_left hs1.le]
lemma upperParameter_contDiffAt {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≠1) :
    ContDiffAt ℝ ∞ (fun z:Space 7×ℝ=>upperParameter z.1 z.2) p := by
  let l:=upperParameter p.1 p.2
  have hl:0<l:=(upperParameter_spec hp).1
  have he:upperFamily l p.1=p.2:=(upperParameter_spec hp).2
  have ht:0<p.2:=(U_nonneg p.1).trans_lt hp
  let F:(Space 7×ℝ)×ℝ→ℝ:=fun z=>upperFamily z.2 z.1.1-z.1.2
  have hpl:0<upperFamily l p.1 := by rw [he]; exact ht
  have hUF:ContDiffAt ℝ ∞ (fun z:ℝ×Space 7=>upperFamily z.1 z.2) (l,p.1) :=
    upperFamily_joint_contDiffAt (p:=(l,p.1)) hl hpl hq
  have hF:ContDiffAt ℝ ∞ F (p,l) := by
    have hh:ContDiffAt ℝ ∞ (fun z:(Space 7×ℝ)×ℝ=>(z.2,z.1.1)) (p,l):=by fun_prop
    exact (hUF.comp (p,l) hh).sub
      (contDiffAt_fst.snd)
  obtain ⟨ρ,hρ,hd⟩:=upperFamily_scale_derivative hl hpl hq
  have hdF:HasDerivAt (fun s:ℝ=>F (p,s)) ρ l:=by simpa only [F] using hd.sub_const p.2
  obtain ⟨ψ,hψ,hψ0,hψeq⟩:=Foliation.scalar_implicit hF hdF hρ.ne'
  have hF0:F (p,l)=0:=by dsimp [F]; rw [he,sub_self]
  apply hψ.congr_of_eventuallyEq
  have hψpos:∀ᶠ z in 𝓝 p,0<ψ z:=hψ.continuousAt.eventually (lt_mem_nhds (by rwa [hψ0]))
  have hdom:∀ᶠ z:Space 7×ℝ in 𝓝 p,U z.1<z.2 :=
    (U_continuous.continuousAt.comp continuous_fst.continuousAt).eventually_lt continuous_snd.continuousAt hp
  filter_upwards [hψeq,hψpos,hdom] with z hz hz1 hz2
  rw [hF0] at hz
  exact upperParameter_unique hz2 hz1 (sub_eq_zero.mp hz)
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.FoliationDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uG

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff Laplacian
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma inner_spatialGradient (F:E×ℝ→ℝ) (p:E×ℝ) (v:E) :
    inner ℝ (spatialGradient F p) v = fderiv ℝ F p (v,0) := by
  rw [spatialGradient,←toDual_apply_apply (𝕜:=ℝ),LinearIsometryEquiv.apply_symm_apply]
  rfl

omit [FiniteDimensional ℝ E] in
lemma linear_prod_decomposition {G : Type uG} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L:E×ℝ→L[ℝ] G) (v:E) (s:ℝ) : L (v,s)=L (v,0)+s • L (0,1) := by
  calc
    _ = L ((v,0)+s • ((0:E),(1:ℝ))) := by congr 1; ext <;> simp
    _ = _ := by rw [map_add,map_smul]

omit [FiniteDimensional ℝ E] in
lemma sliceLeft_hasFDerivAt {G : Type uG} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F:E×ℝ→G} {p:E×ℝ} (hF:DifferentiableAt ℝ F p) :
    HasFDerivAt (fun x:E=>F (x,p.2)) (fderiv ℝ F p ∘L ContinuousLinearMap.inl ℝ E ℝ) p.1 := by
  rcases p with ⟨x,t⟩
  have hi:HasFDerivAt (fun y:E=>(y,t)) (ContinuousLinearMap.inl ℝ E ℝ) x := by
    simpa only [ContinuousLinearMap.inl,id_eq] using (hasFDerivAt_id (𝕜:=ℝ) x).prodMk (hasFDerivAt_const t x)
  exact hF.hasFDerivAt.comp x hi

lemma spatialGradient_eq {F:E×ℝ→ℝ} {p:E×ℝ} (hF:DifferentiableAt ℝ F p) :
    spatialGradient F p=gradient (fun x:E=>F (x,p.2)) p.1 := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_spatialGradient,inner_gradient_left]
  have hd := sliceLeft_hasFDerivAt hF
  rw [hd.fderiv]
  simp

lemma spatialGradient_contDiffAt {F:E×ℝ→ℝ} {p:E×ℝ} (hF:ContDiffAt ℝ ∞ F p) :
    ContDiffAt ℝ ∞ (spatialGradient F) p := by
  have hpart : ContDiffAt ℝ ∞ (fun q:E×ℝ=>fderiv ℝ F q ∘L ContinuousLinearMap.inl ℝ E ℝ) p :=
    (hF.fderiv_right (by simp)).clm_comp contDiffAt_const
  exact (toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp p hpart

lemma parameter_directional {F:E×ℝ→ℝ} {L:E×ℝ→ℝ} {p:E×ℝ}
    (hF:DifferentiableAt ℝ F (p.1,L p)) (hL:DifferentiableAt ℝ L p)
    (he:∀ᶠ z in 𝓝 p,F (z.1,L z)=z.2)
    (hρ:fderiv ℝ F (p.1,L p) (0,1)≠0) (v:E) (s:ℝ) :
    fderiv ℝ L p (v,s)=(s-inner ℝ (spatialGradient F (p.1,L p)) v)/
      fderiv ℝ F (p.1,L p) (0,1) := by
  have hd := hF.hasFDerivAt.comp p ((hasFDerivAt_fst (p:=p)).prodMk hL.hasFDerivAt)
  have hh := congrArg (fun T:E×ℝ→L[ℝ] ℝ=>T (v,s))
    ((hd.congr_of_eventuallyEq (he.mono (fun _ h=>h.symm))).unique (hasFDerivAt_snd (p:=p)))
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ] at hh
  rw [linear_prod_decomposition,smul_eq_mul,←inner_spatialGradient] at hh
  change inner ℝ (spatialGradient F (p.1,L p)) v +
    fderiv ℝ L p (v,s) * fderiv ℝ F (p.1,L p) (0,1) = s at hh
  apply (eq_div_iff hρ).mpr
  linarith

lemma divergence_gradient {f:E→ℝ} {x:E} (hf:ContDiffAt ℝ ∞ f x) :
    divergence (gradient f) x=Δ f x := by
  have hg:ContDiffAt ℝ ∞ (gradient f) x :=
    (toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp x (hf.fderiv_right (by simp))
  rw [divergence,laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply Finset.sum_congr rfl
  intro i _
  let v:=stdOrthonormalBasis ℝ E i
  have he:(fun y=>inner ℝ (gradient f y) v)=(fun y=>fderiv ℝ f y v) := by
    ext y
    exact inner_gradient_left
  have hh := congrArg (fun T:E→L[ℝ] ℝ=>T v) (congrArg (fun a:E→ℝ=>fderiv ℝ a x) he)
  have hdir: DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  rw [((hg.differentiableAt (by simp)).hasFDerivAt.inner ℝ (hasFDerivAt_const v x)).fderiv,
    fderiv_clm_apply hdir (differentiableAt_const v)] at hh
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    zero_apply,add_apply,ContinuousLinearMap.flip_apply,
    fderiv_const_apply,map_zero,zero_add] at hh
  simp only [fderivInnerCLM_apply,inner_zero_right,zero_add] at hh
  rw [real_inner_comm] at hh
  rw [iteratedFDeriv_two_apply]
  simpa only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] using hh

/-- Cancellation of the parameter derivatives in the extended calibration.
This is the differential identity for an actual foliation, not an assumed PDE. -/
lemma foliation_divergence {F:E×ℝ→ℝ} {L:E×ℝ→ℝ} {p:E×ℝ}
    (hF:ContDiffAt ℝ ∞ F (p.1,L p)) (hL:ContDiffAt ℝ ∞ L p)
    (he:∀ᶠ z in 𝓝 p,F (z.1,L z)=z.2)
    (hρ:fderiv ℝ F (p.1,L p) (0,1)≠0) :
    let A:E×ℝ→E:=fun z=>spatialGradient F (z.1,L z)
    divergence (fun x=>A (x,p.2)) p.1+
      inner ℝ (A p) (deriv (fun t=>A (p.1,t)) p.2)=
      Δ (fun x:E=>F (x,L p)) p.1 := by
  dsimp only
  let q:E×ℝ:=(p.1,L p)
  let B:=spatialGradient F
  let A:E×ℝ→E:=fun z=>B (z.1,L z)
  let T:=fderiv ℝ B q (0,1)
  let ρ:=fderiv ℝ F q (0,1)
  have hBd:DifferentiableAt ℝ B q:=(spatialGradient_contDiffAt hF).differentiableAt (by simp)
  have hLd:DifferentiableAt ℝ L p:=hL.differentiableAt (by simp)
  have hFd:DifferentiableAt ℝ F q:=hF.differentiableAt (by simp)
  have hmap:HasFDerivAt (fun z:E×ℝ=>(z.1,L z))
      ((ContinuousLinearMap.fst ℝ E ℝ).prod (fderiv ℝ L p)) p :=
    hasFDerivAt_fst.prodMk hLd.hasFDerivAt
  have hAd:HasFDerivAt A (fderiv ℝ B q ∘L
      ((ContinuousLinearMap.fst ℝ E ℝ).prod (fderiv ℝ L p))) p :=
    by simpa only [A,Function.comp_def,q] using hBd.hasFDerivAt.comp p hmap
  have hd (v:E) (s:ℝ) : fderiv ℝ A p (v,s)=fderiv ℝ B q (v,0)+
      ((s-inner ℝ (B q) v)/ρ) • T := by
    rw [hAd.fderiv]
    change fderiv ℝ B q (v,fderiv ℝ L p (v,s)) = _
    rw [linear_prod_decomposition,parameter_directional hFd hLd he hρ]
  have hx (v:E) : fderiv ℝ (fun x:E=>A (x,p.2)) p.1 v=fderiv ℝ A p (v,0) := by
    rw [(sliceLeft_hasFDerivAt hAd.differentiableAt).fderiv]
    simp
  have ht : deriv (fun t:ℝ=>A (p.1,t)) p.2=ρ⁻¹ • T := by
    have hh:=hAd.comp_hasDerivAt p.2 ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
    change HasDerivAt (fun t:ℝ=>A (p.1,t)) _ p.2 at hh
    rw [←hAd.fderiv] at hh
    rw [hh.deriv]
    rw [hd]
    simp only [inner_zero_right,sub_zero,one_div]
    rw [show ((0:E),(0:ℝ))=(0:E×ℝ) from rfl,map_zero,zero_add]
  have hspatial : divergence (fun x:E=>B (x,L p)) p.1=Δ (fun x:E=>F (x,L p)) p.1 := by
    have heq:(fun x:E=>B (x,L p)) =ᶠ[𝓝 p.1] gradient (fun x:E=>F (x,L p)) := by
      have hn:Tendsto (fun x:E=>(x,L p)) (𝓝 p.1) (𝓝 q):=continuousAt_id.prodMk continuousAt_const
      have hF1:ContDiffAt ℝ 1 F q:=hF.of_le (by simp)
      filter_upwards [hn.eventually (hF1.eventually (by simp))] with x hx
      exact spatialGradient_eq (hx.differentiableAt (by simp))
    have hfs:ContDiffAt ℝ ∞ (fun x:E=>F (x,L p)) p.1 :=
      hF.comp p.1 (contDiffAt_id.prodMk contDiffAt_const)
    rw [divergence,heq.fderiv_eq]
    exact divergence_gradient hfs
  have hbase (v:E):fderiv ℝ (fun x:E=>B (x,L p)) p.1 v=fderiv ℝ B q (v,0) := by
    rw [(sliceLeft_hasFDerivAt hBd).fderiv]
    simp
  change divergence (fun x=>A (x,p.2)) p.1+inner ℝ (B q) (deriv (fun t=>A (p.1,t)) p.2)=_
  rw [ht,←hspatial,divergence,divergence]
  simp_rw [hx,hbase,hd,inner_add_right,real_inner_smul_right,zero_sub,neg_div]
  rw [Finset.sum_add_distrib]
  have hec:(∑ i, -(inner ℝ (B q) (stdOrthonormalBasis ℝ E i)/ρ)*
      inner ℝ (stdOrthonormalBasis ℝ E i) T) = - (inner ℝ (B q) T/ρ) := by
    simp only [neg_mul,Finset.sum_neg_distrib,div_mul_eq_mul_div,←Finset.sum_div]
    rw [(stdOrthonormalBasis ℝ E).sum_inner_mul_inner]
  rw [hec]
  ring
end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.LaplacianDilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.ScalarLaplacian
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
lemma laplacian_comp_smul {f:E→ℝ} {x:E} (a:ℝ) (hf:ContDiffAt ℝ 2 f (a • x)) :
    Δ (fun y=>f (a • y)) x=a^2*Δ f (a • x) := by
  have hg:ContDiffAt ℝ 2 (fun y:E=>f (a • y)) x:=
    hf.comp x (contDiffAt_const.smul contDiffAt_id)
  rw [laplacian_sum_line hg,laplacian_sum_line hf,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  let v:=stdOrthonormalBasis ℝ E i
  have he:(fun t:ℝ=>f (a • (x+t • v)))=(fun t:ℝ=>f (a • x+t • (a • v))) := by
    ext t
    rw [smul_add,smul_comm a t v]
  change deriv (deriv (fun t:ℝ=>f (a • (x+t • v)))) 0 = _
  rw [he,Axisymmetric.line_second_derivative hf,Axisymmetric.line_second_derivative hf]
  simp only [map_smul,smul_apply,smul_eq_mul]
  ring
end Bernoulli.ScalarLaplacian

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.UpperCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
lemma upperSigned_laplacian_nonpos {x:Space 7}
    (hp:0<upperSigned x) (hq:Cylindrical.radiusSq axis x≠1) : Δ upperSigned x≤0 := by
  have hc:ContinuousAt (Cylindrical.radiusSq axis) x:=
    (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt
  rcases lt_or_gt_of_ne hq with h|h
  · have he:upperSigned =ᶠ[𝓝 x] smoothCap := by
      filter_upwards [hc.eventually (gt_mem_nhds h)] with y hy
      exact upperSigned_cap hy.le
    rw [(laplacian_congr_nhds he).self_of_nhds]
    have hp':0<smoothCap x:=by rwa [upperSigned_cap h.le] at hp
    have hv:= (CapAlgebra.V_bounds (Cylindrical.radiusSq_nonneg axis x axis_norm)
      h.le capB_bounds.1 capB_bounds.2).1
    have hy:=CapAlgebra.Y_pos (Cylindrical.radiusSq_nonneg axis x axis_norm) hv capC_pos
    have hs:0<capH (Cylindrical.axis axis x/CapAlgebra.V (Cylindrical.radiusSq axis x) capB) := by
      change 0<CapAlgebra.Y _ _ _ * capH (_ * (CapAlgebra.V _ _)⁻¹) at hp'
      rw [←div_eq_mul_inv] at hp'
      exact pos_of_mul_pos_right hp' hy.le
    exact smoothCap_laplacian_nonpos h.le ((capH_pos_iff _).mp hs).le
  · have he:upperSigned =ᶠ[𝓝 x] outerSigned := by
      filter_upwards [hc.eventually (lt_mem_nhds h)] with y hy
      exact upperSigned_outer hy.le
    obtain ⟨hx,ha⟩:=radiusSq_pos_data (show 0<Cylindrical.radiusSq axis x by linarith)
    rw [(laplacian_congr_nhds he).self_of_nhds,outerSigned_laplacian hx ha]

lemma upperFamily_laplacian_nonpos {x:Space 7} {l:ℝ} (hl:0<l)
    (hp:0<upperFamily l x) (hq:Cylindrical.radiusSq axis (l⁻¹ • x)≠1) :
    Δ (upperFamily l) x≤0 := by
  have hpos:0<upperSigned (l⁻¹ • x) := by
    have hh:0 < max (upperSigned (l⁻¹ • x)) 0:=pos_of_mul_pos_right hp (mul_nonneg κ_pos.le hl.le)
    simpa using hh
  have hf:ContDiffAt ℝ 2 upperSigned (l⁻¹ • x):=(upperSigned_contDiffAt hq).of_le (by exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hi:ContDiffAt ℝ 2 (fun y:Space 7=>l⁻¹ • y) x:=
    (contDiffAt_id (𝕜:=ℝ) (n:=2) (x:=x)).const_smul l⁻¹
  have hg:ContDiffAt ℝ 2 (fun y:Space 7=>upperSigned (l⁻¹ • y)) x:=
    ContDiffAt.comp (f:=fun y:Space 7=>l⁻¹ • y) x hf hi
  have he:(upperFamily l) =ᶠ[𝓝 x] (fun y=>κ*l*upperSigned (l⁻¹ • y)) := by
    filter_upwards [hg.continuousAt.eventually (lt_mem_nhds hpos)] with y hy
    exact congrArg (κ*l* ·) (max_eq_left hy.le)
  rw [(laplacian_congr_nhds he).self_of_nhds]
  have hh:Δ (fun y:Space 7=>κ*l*upperSigned (l⁻¹ • y)) x=
      κ*l*Δ (fun y:Space 7=>upperSigned (l⁻¹ • y)) x:=laplacian_smul (κ*l) hg
  rw [hh,ScalarLaplacian.laplacian_comp_smul l⁻¹ hf]
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg κ_pos.le hl.le)
    (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (upperSigned_laplacian_nonpos hpos hq))

lemma upperFamily_contDiffAt_swap {x:Space 7} {l:ℝ} (hl:0<l)
    (hp:0<upperFamily l x) (hq:Cylindrical.radiusSq axis (l⁻¹ • x)≠1) :
    ContDiffAt ℝ ∞ (fun z:Space 7×ℝ=>upperFamily z.2 z.1) (x,l) := by
  have hh:ContDiffAt ℝ ∞ (fun z:ℝ×Space 7=>upperFamily z.1 z.2) (l,x):=
    upperFamily_joint_contDiffAt (p:=(l,x)) hl hp hq
  have hi:ContDiffAt ℝ ∞ (fun z:Space 7×ℝ=>(z.2,z.1)) (x,l):=
    contDiffAt_snd.prodMk contDiffAt_fst
  exact ContDiffAt.comp (f:=fun z:Space 7×ℝ=>(z.2,z.1)) (x,l) hh hi

theorem upperCalibration_bulk {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≠1) :
    Foliation.divergence (fun x=>upperCalibration (x,p.2)) p.1+
      inner ℝ (upperCalibration p) (deriv (fun t=>upperCalibration (p.1,t)) p.2)≤0 := by
  let F:Space 7×ℝ→ℝ:=fun z=>upperFamily z.2 z.1
  let L:Space 7×ℝ→ℝ:=fun z=>upperParameter z.1 z.2
  have hl:0<L p:=(upperParameter_spec hp).1
  have heq:upperFamily (L p) p.1=p.2:=(upperParameter_spec hp).2
  have hpos:0<upperFamily (L p) p.1:=by rw [heq]; exact (U_nonneg _).trans_lt hp
  have hF:ContDiffAt ℝ ∞ F (p.1,L p):=by
    exact upperFamily_contDiffAt_swap hl hpos hq
  have hL:ContDiffAt ℝ ∞ L p:=upperParameter_contDiffAt hp hq
  have he:∀ᶠ z:Space 7×ℝ in 𝓝 p,F (z.1,L z)=z.2:=by
    have hn:∀ᶠ z:Space 7×ℝ in 𝓝 p,U z.1<z.2:=
      (U_continuous.continuousAt.comp continuous_fst.continuousAt).eventually_lt
        continuous_snd.continuousAt hp
    filter_upwards [hn] with z hz
    exact (upperParameter_spec hz).2
  obtain ⟨ρ,hρ,hd⟩:=upperFamily_scale_derivative hl hpos hq
  have hρ':fderiv ℝ F (p.1,L p) (0,1)≠0:=by
    have his:HasDerivAt (fun t:ℝ=>(p.1,t)) (0,1) (L p):=by
      simpa using (hasDerivAt_const (L p) p.1).prodMk (hasDerivAt_id (L p))
    have hh:HasDerivAt (fun t:ℝ=>upperFamily t p.1) (fderiv ℝ F (p.1,L p) (0,1)) (L p):=by
      exact (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (L p) his
    exact (hh.unique hd).symm ▸ hρ.ne'
  have hid:=Foliation.foliation_divergence hF hL he hρ'
  change Foliation.divergence (fun x=>upperCalibration (x,p.2)) p.1+
    inner ℝ (upperCalibration p) (deriv (fun t=>upperCalibration (p.1,t)) p.2)=
      Δ (upperFamily (L p)) p.1 at hid
  rw [hid]
  exact upperFamily_laplacian_nonpos hl hpos hq
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.FoliationSeam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open scoped RealInnerProductSpace
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The extended calibration jump across the graph of a matching seam. -/
lemma seam_flux_identity (Gp Gm H N:E) (ρp ρm:ℝ)
    (hp:H=Gp+ρp • N) (hm:H=Gm+ρm • N) :
    ‖Gp‖^2-‖Gm‖^2-2*inner ℝ (Gp-Gm) H=
      -(ρp+ρm)*inner ℝ (Gp-Gm) N := by
  have hh:Gp+Gm-(2:ℝ) • H=-(ρp+ρm) • N := by
    rw [hp] at hm
    have hg:Gm=Gp+(ρp-ρm) • N := by
      calc
        Gm = (Gm+ρm • N)-ρm • N := by abel
        _ = _ := by rw [←hm]; module
    rw [hg,hp]
    module
  have hid:inner ℝ (Gp-Gm) (Gp+Gm-(2:ℝ) • H)=
      ‖Gp‖^2-‖Gm‖^2-2*inner ℝ (Gp-Gm) H := by
    simp only [inner_sub_right,inner_add_right,inner_sub_left,real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    rw [real_inner_comm Gm Gp]
    ring
  rw [←hid,hh,real_inner_smul_right]
lemma seam_flux_nonpos (Gp Gm H N:E) (ρp ρm:ℝ)
    (hp:H=Gp+ρp • N) (hm:H=Gm+ρm • N)
    (hρ:0≤ρp+ρm) (hj:0 ≤ inner ℝ (Gp-Gm) N) :
    ‖Gp‖^2-‖Gm‖^2-2*inner ℝ (Gp-Gm) H≤0 := by
  rw [seam_flux_identity Gp Gm H N ρp ρm hp hm]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ) hj
end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.SeamCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
open Axisymmetric
lemma polarGradient_span (x:Space 7) (a b:ℝ) :
    ∃c d:ℝ,polarGradient axis x a b=c • axis+d • x := by
  refine ⟨b,(a-b*(inner ℝ x axis/‖x‖))*‖x‖⁻¹,?_⟩
  unfold polarGradient radial
  module
lemma outerGradient_span {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    ∃a b:ℝ,gradient outerSigned x=a • axis+b • x := by
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hq
  have hdz:DifferentiableAt ℝ Zsigned x:=(signed_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  have hdk:DifferentiableAt ℝ KSup x:=(KSup_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  have hz:gradient Zsigned x=polarGradient axis x (f (angle x)) (fp (angle x)) := by
    have hi:inner ℝ x axis/‖x‖∈Ioo (-1:ℝ) 1:=by
      simpa only [mem_Ioo,inner_axis,angle] using (show -1<angle x ∧ angle x<1 from abs_lt.mp ha)
    rw [Zsigned,(hasGradientAt_lift axis x 1 hx (hasDerivAt_f hi)).gradient]
    simp only [Real.rpow_one,div_self (norm_ne_zero_iff.mpr hx),one_smul,one_mul,inner_axis,angle]
  obtain ⟨a,b,hab⟩:=polarGradient_span x (f (angle x)) (fp (angle x))
  obtain ⟨c,d,hcd⟩:=polarGradient_span x (-2*gSup (angle x)) (gSup1 (angle x))
  change ∃a b:ℝ,gradient (fun x=>Zsigned x+capAmplitude*KSup x) x=a • axis+b • x
  rw [gradient_add' hdz (hdk.const_mul capAmplitude),gradient_const_mul _ hdk,hz,
    KSup_gradient hx ha,hab,hcd]
  refine ⟨a+capAmplitude*(‖x‖^(-2:ℝ)/‖x‖)*c,b+capAmplitude*(‖x‖^(-2:ℝ)/‖x‖)*d,?_⟩
  module
lemma cylindrical_projection {x G:Space 7} (hq:Cylindrical.radiusSq axis x=1)
    (hG:∃a b:ℝ,G=a • axis+b • x) :
    G=inner ℝ G axis • axis+inner ℝ G (Cylindrical.transverse axis x) • Cylindrical.transverse axis x := by
  obtain ⟨a,b,hab⟩:=hG
  have hn:inner ℝ (Cylindrical.transverse axis x) axis=0:=Cylindrical.transverse_inner axis x axis_norm
  have hn':inner ℝ axis (Cylindrical.transverse axis x)=0:=by rw [real_inner_comm,hn]
  have hnn:inner ℝ (Cylindrical.transverse axis x) (Cylindrical.transverse axis x)=1:=by
    rw [real_inner_self_eq_norm_sq,Cylindrical.transverse_sq axis x axis_norm,hq]
  have hg:G=(a+b*Cylindrical.axis axis x) • axis+b • Cylindrical.transverse axis x:=by
    rw [hab,Cylindrical.transverse]
    module
  rw [hg]
  simp only [inner_add_left,real_inner_smul_left,hn,hn',hnn,mul_zero,mul_one,zero_add,add_zero,
    real_inner_self_eq_norm_sq,axis_norm,one_pow]

lemma smoothCap_gradient_at_seam {x:Space 7} (hq:Cylindrical.radiusSq axis x=1) :
    gradient smoothCap x=capHP (Cylindrical.axis axis x) • axis+
      (capEta*capH (Cylindrical.axis axis x)-
        capP*Cylindrical.axis axis x*capHP (Cylindrical.axis axis x)) • Cylindrical.transverse axis x := by
  rw [gradient_smoothCap (le_of_eq hq)]
  simp only [hq,CapAlgebra.V_one,CapAlgebra.Y_one,CapAlgebra.D_one,CapAlgebra.Y1_one,
    div_one,one_pow,inv_one,one_mul]
  module
lemma outer_gradient_at_seam {x:Space 7} (hq:Cylindrical.radiusSq axis x=1) :
    gradient outerSigned x=capHP (Cylindrical.axis axis x) • axis+
      (capH (Cylindrical.axis axis x)-Cylindrical.axis axis x*capHP (Cylindrical.axis axis x)-
        3*capAmplitude*(1+2*(Cylindrical.axis axis x)^2)) • Cylindrical.transverse axis x := by
  rw [cylindrical_projection hq (outerGradient_span (by rw [hq]; norm_num)),
    outerSigned_axis_at_seam hq,outerSigned_transverse_at_seam hq]
lemma seamGradient_matching {x G:Space 7} (hq:Cylindrical.radiusSq axis x=1)
    {b:ℝ} (hg:G=capHP (Cylindrical.axis axis x) • axis+b • Cylindrical.transverse axis x) :
    seamGradient x=G+(capH (Cylindrical.axis axis x)-inner ℝ x G) • Cylindrical.transverse axis x := by
  have hn:inner ℝ x (Cylindrical.transverse axis x)=1:=by
    rw [Cylindrical.transverse,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
    change ‖x‖^2-Cylindrical.axis axis x*Cylindrical.axis axis x=1
    simpa only [Cylindrical.radiusSq,pow_two] using hq
  rw [hg]
  simp only [inner_add_right,real_inner_smul_right,hn,mul_one]
  change seamGradient x=_
  unfold seamGradient Cylindrical.axis
  module

/-- The actual cap/exterior calibration has the required nonpositive seam flux.
This verifies the jump, rather than inserting a comparison premise. -/
theorem upperCalibration_seam {x:Space 7} (hq:Cylindrical.radiusSq axis x=1)
    (hp:0<smoothCap x) :
    ‖κ • gradient smoothCap x‖^2-‖κ • gradient outerSigned x‖^2-
      2*inner ℝ (κ • gradient smoothCap x-κ • gradient outerSigned x) (κ • seamGradient x)≤0 := by
  have ha:|Cylindrical.axis axis x|<3/4 := by
    rw [smoothCap_at_seam hq] at hp
    exact (capH_pos_iff _).mp hp
  have hoc:0<outerSigned x:=by rwa [←upper_seam_agreement hq]
  obtain ⟨hx,ht⟩:=radiusSq_pos_data (show 0<Cylindrical.radiusSq axis x by rw [hq]; norm_num)
  let ρc:=κ*(smoothCap x-inner ℝ x (gradient smoothCap x))
  let ρo:=κ*(outerSigned x-inner ℝ x (gradient outerSigned x))
  have hρc:0<ρc:=mul_pos κ_pos (smoothCap_radial_defect_pos (le_of_eq hq) hp)
  have hρo:0<ρo:=mul_pos κ_pos (outerSigned_radial_defect_pos hx ht)
  have hc:κ • seamGradient x=κ • gradient smoothCap x+ρc • Cylindrical.transverse axis x := by
    rw [seamGradient_matching hq (smoothCap_gradient_at_seam hq),smul_add,smul_smul]
    dsimp only [ρc]
    rw [smoothCap_at_seam hq]
  have ho:κ • seamGradient x=κ • gradient outerSigned x+ρo • Cylindrical.transverse axis x := by
    rw [seamGradient_matching hq (outer_gradient_at_seam hq),smul_add,smul_smul]
    dsimp only [ρo]
    rw [outerSigned_at_seam hq]
  apply Foliation.seam_flux_nonpos _ _ _ _ ρc ρo hc ho (add_nonneg hρc.le hρo.le)
  rw [←smul_sub,real_inner_smul_left,inner_sub_left]
  have hj:=upper_seam_jump hq ha.le
  rw [inner_sub_left] at hj
  exact mul_nonneg κ_pos.le (by linarith)
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.OuterSlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
open Axisymmetric
lemma Zsigned_gradient {x:Space 7} (hx:x≠0) (ha:|angle x|<1) :
    gradient Zsigned x=polarGradient axis x (f (angle x)) (fp (angle x)) := by
  have hi:inner ℝ x axis/‖x‖∈Ioo (-1:ℝ) 1:=by
    simpa only [inner_axis,angle] using (show angle x∈Ioo (-1:ℝ) 1 from abs_lt.mp ha)
  rw [Zsigned,(hasGradientAt_lift axis x 1 hx (hasDerivAt_f hi)).gradient]
  simp only [Real.rpow_one,div_self (norm_ne_zero_iff.mpr hx),one_smul,one_mul,inner_axis,angle]
lemma outerSigned_gradient {x:Space 7} (hx:x≠0) (ha:|angle x|<1) :
    gradient outerSigned x=polarGradient axis x (f (angle x)) (fp (angle x))+
      (capAmplitude*(‖x‖^(-2:ℝ)/‖x‖)) • polarGradient axis x (-2*gSup (angle x)) (gSup1 (angle x)) := by
  have hdz: DifferentiableAt ℝ Zsigned x := (signed_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  have hdk: DifferentiableAt ℝ KSup x := (KSup_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  change gradient (fun x=>Zsigned x+capAmplitude*KSup x) x=_
  rw [gradient_add' hdz (hdk.const_mul capAmplitude),gradient_const_mul _ hdk,
    Zsigned_gradient hx ha,KSup_gradient hx ha,smul_smul]
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.CalibrationTraces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff Laplacian
namespace Bernoulli.DeSilvaJerison
lemma gradient_dilation {f:Space 7→ℝ} {x:Space 7} {l:ℝ} (hl:l≠0)
    (hf:DifferentiableAt ℝ f (l⁻¹ • x)) :
    gradient (fun y=>κ*l*f (l⁻¹ • y)) x=κ • gradient f (l⁻¹ • x) := by
  have hd:HasFDerivAt (fun y:Space 7=>l⁻¹ • y)
      (l⁻¹ • ContinuousLinearMap.id ℝ (Space 7)) x := (hasFDerivAt_id x).const_smul l⁻¹
  have hh:HasFDerivAt (fun y:Space 7=>κ*l*f (l⁻¹ • y))
      ((κ*l) • (fderiv ℝ f (l⁻¹ • x) ∘L (l⁻¹ • ContinuousLinearMap.id ℝ (Space 7)))) x :=
    (hf.hasFDerivAt.comp x hd).const_mul (κ*l)
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,hh.fderiv,real_inner_smul_left,inner_gradient_left]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]
  field_simp

lemma upperFamily_gradient {x:Space 7} {l:ℝ} (hl:0<l)
    (hp:0<upperFamily l x) (hq:Cylindrical.radiusSq axis (l⁻¹ • x)≠1) :
    gradient (upperFamily l) x=κ • gradient upperSigned (l⁻¹ • x) := by
  have hf:ContDiffAt ℝ ∞ upperSigned (l⁻¹ • x):=upperSigned_contDiffAt hq
  have hs:ContinuousAt (fun y:Space 7=>upperSigned (l⁻¹ • y)) x:=
    hf.continuousAt.comp ((continuous_id.const_smul l⁻¹).continuousAt)
  have hpos:0<upperSigned (l⁻¹ • x):=by
    have hh:0 < max (upperSigned (l⁻¹ • x)) 0:=pos_of_mul_pos_right hp (mul_nonneg κ_pos.le hl.le)
    simpa using hh
  have he:upperFamily l =ᶠ[𝓝 x] (fun y=>κ*l*upperSigned (l⁻¹ • y)) := by
    filter_upwards [hs.eventually (lt_mem_nhds hpos)] with y hy
    exact congrArg (κ*l* ·) (max_eq_left hy.le)
  rw [gradient,he.fderiv_eq]
  exact gradient_dilation hl.ne' (hf.differentiableAt (by simp))

lemma upperCalibration_eq {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≠1) :
    upperCalibration p=κ • gradient upperSigned ((upperParameter p.1 p.2)⁻¹ • p.1) := by
  obtain ⟨hl,he⟩:=upperParameter_spec hp
  have hpos:0<upperFamily (upperParameter p.1 p.2) p.1:=by rw [he]; exact (U_nonneg _).trans_lt hp
  rw [upperCalibration,Foliation.spatialGradient_eq
    ((upperFamily_contDiffAt_swap hl hpos hq).differentiableAt (by simp))]
  exact upperFamily_gradient hl hpos hq

end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.FluxBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison
open Axisymmetric
lemma cap_positive_bounded {x:Space 7} (hq:Cylindrical.radiusSq axis x≤1)
    (hp:0<smoothCap x) : ‖x‖≤2 := by
  have hq0:=Cylindrical.radiusSq_nonneg axis x axis_norm
  obtain ⟨hv,hv1⟩:=CapAlgebra.V_bounds hq0 hq capB_bounds.1 capB_bounds.2
  have hy:=CapAlgebra.Y_pos hq0 hv capC_pos
  have hH:0<capH (Cylindrical.axis axis x/CapAlgebra.V (Cylindrical.radiusSq axis x) capB):=by
    change 0<CapAlgebra.Y _ _ _ * capH (_ * (CapAlgebra.V _ _)⁻¹) at hp
    rw [←div_eq_mul_inv] at hp
    exact pos_of_mul_pos_right hp hy.le
  have ha:|Cylindrical.axis axis x|<3/4:=by
    have hh:=(capH_pos_iff _).mp hH
    rw [abs_div,abs_of_pos hv,div_lt_iff₀ hv] at hh
    nlinarith
  have hsq:(Cylindrical.axis axis x)^2<(3/4:ℝ)^2:=by
    rw [←sq_abs]
    exact (sq_lt_sq₀ (abs_nonneg _) (by norm_num)).mpr ha
  unfold Cylindrical.radiusSq at hq
  nlinarith [norm_nonneg x]
lemma cap_gradient_uniform_bound : ∃C:ℝ,0<C ∧
    ∀x:Space 7,Cylindrical.radiusSq axis x≤1 → 0<smoothCap x → ‖gradient smoothCap x‖≤C := by
  let S:Set (Space 7):={x|Cylindrical.radiusSq axis x≤1} ∩ Metric.closedBall 0 2
  have hs:IsCompact S:=(isCompact_closedBall (0:Space 7) 2).inter_left
    (isClosed_le (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous continuous_const)
  have hg:ContinuousOn (gradient smoothCap) S:=by
    intro x hx
    have hh:ContDiffAt ℝ ∞ (gradient smoothCap) x:=
      (toDual ℝ (Space 7)).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp x
        ((smoothCap_contDiffAt hx.1).fderiv_right (by simp))
    exact hh.continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩:=hs.exists_bound_of_continuousOn hg
  refine ⟨|C|+1,by positivity,?_⟩
  intro x hq hp
  have hx:x∈S:=⟨hq,by simpa using cap_positive_bounded hq hp⟩
  exact (hC x hx).trans (by linarith [le_abs_self C])
lemma polarGradient_norm_bound {x:Space 7} (hx:x≠0) (a b:ℝ) :
    ‖polarGradient axis x a b‖≤|a|+|b| := by
  have hh:=norm_sq_polarGradient axis_norm hx a b
  have hab:0≤|a| * |b|:=mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hb:0≤(inner ℝ x axis/‖x‖)^2*b^2:=mul_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith [sq_abs a,sq_abs b,norm_nonneg (polarGradient axis x a b),abs_nonneg a,abs_nonneg b]
lemma outer_gradient_uniform_bound : ∃C:ℝ,0<C ∧
    ∀x:Space 7,1≤Cylindrical.radiusSq axis x → 0<outerSigned x → ‖gradient outerSigned x‖≤C := by
  let R:ℝ→ℝ:=fun t=>|f t|+|fp t|+capAmplitude*(2*|gSup t|+|gSup1 t|)
  have hR:ContinuousOn R (Icc (-3/5:ℝ) (3/5)):=by
    intro t ht
    have ht1:t∈Ioo (-1:ℝ) 1:=⟨by linarith [ht.1],by linarith [ht.2]⟩
    have ht2:|t|<1:=abs_lt.mpr ht1
    exact (((hasDerivAt_f ht1).continuousAt.abs.add (hasDerivAt_fp ht1).continuousAt.abs).add
      (continuousAt_const.mul (((hasDerivAt_gSup ht2).continuousAt.abs.const_mul 2).add
        (hasDerivAt_gSup1 ht2).continuousAt.abs))).continuousWithinAt
  obtain ⟨C,hC⟩:=isCompact_Icc.exists_bound_of_continuousOn hR
  refine ⟨|C|+1,by positivity,?_⟩
  intro x hq hp
  obtain ⟨hx,ha⟩:=radiusSq_pos_data (show 0<Cylindrical.radiusSq axis x by linarith)
  have hat:|angle x|≤3/5:=outer_nonnegative_angle hq hp.le
  have hn:1≤‖x‖:=by
    unfold Cylindrical.radiusSq at hq
    nlinarith [norm_nonneg x,sq_nonneg (Cylindrical.axis axis x)]
  have hn0:0<‖x‖:=by linarith
  have hfac:0≤‖x‖^(-2:ℝ)/‖x‖ ∧ ‖x‖^(-2:ℝ)/‖x‖≤1:=by
    rw [Real.rpow_neg (norm_nonneg x),Real.rpow_two]
    constructor
    · positivity
    · apply (div_le_one hn0).mpr
      exact (inv_le_one_of_one_le₀ (by nlinarith : 1≤‖x‖^2)).trans hn
  have hc:0≤capAmplitude*(‖x‖^(-2:ℝ)/‖x‖):=mul_nonneg capAmplitude_pos.le hfac.1
  have hc1:capAmplitude*(‖x‖^(-2:ℝ)/‖x‖)≤capAmplitude:=by nlinarith [capAmplitude_pos]
  have hm:‖gradient outerSigned x‖≤R (angle x):=by
    rw [outerSigned_gradient hx ha]
    calc
      _≤‖polarGradient axis x (f (angle x)) (fp (angle x))‖+
          ‖(capAmplitude*(‖x‖^(-2:ℝ)/‖x‖)) • polarGradient axis x (-2*gSup (angle x)) (gSup1 (angle x))‖ := norm_add_le _ _
      _≤(|f (angle x)|+|fp (angle x)|)+
          capAmplitude*(2*|gSup (angle x)|+|gSup1 (angle x)|) := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hc]
        apply add_le_add (polarGradient_norm_bound hx _ _)
        have hh:=polarGradient_norm_bound hx (-2*gSup (angle x)) (gSup1 (angle x))
        norm_num only [abs_mul,abs_neg,abs_of_pos (by norm_num : 0<(2:ℝ))] at hh
        exact (mul_le_mul_of_nonneg_left hh hc).trans
          (mul_le_mul_of_nonneg_right hc1 (show 0≤2*|gSup (angle x)|+|gSup1 (angle x)| by positivity))
      _=R (angle x):=rfl
  have hbound:‖R (angle x)‖≤C:=hC _ (by simpa only [neg_div,Set.mem_Icc] using abs_le.mp hat)
  exact hm.trans ((le_abs_self _).trans (hbound.trans (by linarith [le_abs_self C])))
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.ExteriorCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison
lemma upperFamily_outer_gradient {x:Space 7} {l:ℝ} (hl:0<l)
    (hq:l^2<Cylindrical.radiusSq axis x) (hp:0<upperFamily l x) :
    gradient (upperFamily l) x=κ • gradient Zsigned x+
      (κ*capAmplitude*l^3) • gradient KSup x := by
  have hqp:0<Cylindrical.radiusSq axis x:=(sq_pos_of_pos hl).trans hq
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hqp
  have hdZ:DifferentiableAt ℝ Zsigned x:=(signed_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  have hdK:DifferentiableAt ℝ KSup x:=(KSup_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  have he:upperFamily l =ᶠ[𝓝 x] (fun y=>κ*(Zsigned y+capAmplitude*l^3*KSup y)) := by
    filter_upwards [((Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt).eventually (lt_mem_nhds hq),
      (upperFamily_continuous l).continuousAt.eventually (lt_mem_nhds hp)] with y hy hpy
    rw [upperFamily_outer_formula hl hy.le] at hpy ⊢
    have hh:0<Zsigned y+capAmplitude*l^3*KSup y:=by
      have hm:=pos_of_mul_pos_right hpy κ_pos.le
      simpa using hm
    rw [max_eq_left hh.le]
  rw [gradient,he.fderiv_eq]
  change gradient (fun y=>κ*(Zsigned y+capAmplitude*l^3*KSup y)) x=_
  have hdf:DifferentiableAt ℝ (fun y=>Zsigned y+capAmplitude*l^3*KSup y) x:=
    hdZ.add (hdK.const_mul (capAmplitude*l^3))
  rw [gradient_const_mul κ hdf,
    gradient_add' hdZ (hdK.const_mul (capAmplitude*l^3)),gradient_const_mul (capAmplitude*l^3) hdK,smul_add,smul_smul]
  congr 2
  ring

/-- On the actual exterior branch the inverse leaf parameter cancels completely.
The calibration extends affinely to the lower graph; there is no cube-root
singularity in the field itself. -/
theorem upperCalibration_outer_affine {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:(upperParameter p.1 p.2)^2<Cylindrical.radiusSq axis p.1) :
    upperCalibration p=κ • gradient Zsigned p.1+
      ((p.2-κ*Zsigned p.1)/KSup p.1) • gradient KSup p.1 := by
  let l:=upperParameter p.1 p.2
  obtain ⟨hl,he⟩:=upperParameter_spec hp
  change 0<l at hl
  change upperFamily l p.1=p.2 at he
  have ht:0<p.2:=(U_nonneg _).trans_lt hp
  have hpos:0<upperFamily l p.1:=by rw [he]; exact ht
  have hqp:0<Cylindrical.radiusSq axis p.1:=(sq_pos_of_pos hl).trans hq
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hqp
  have hK:KSup p.1≠0:=(KSup_pos hx ha).ne'
  have hqe:Cylindrical.radiusSq axis (l⁻¹ • p.1)≠1:=by
    rw [Cylindrical.radiusSq_smul]
    have hh:(l⁻¹)^2*Cylindrical.radiusSq axis p.1>1:=by
      rw [inv_pow,←div_eq_inv_mul]
      change 1<Cylindrical.radiusSq axis p.1/l^2
      exact (lt_div_iff₀ (sq_pos_of_pos hl)).mpr (by simpa only [one_mul] using hq)
    exact ne_of_gt hh
  rw [upperCalibration,Foliation.spatialGradient_eq
    ((upperFamily_contDiffAt_swap hl hpos hqe).differentiableAt (by simp)),
    upperFamily_outer_gradient hl hq hpos]
  congr 1
  have hh:=upperFamily_outer_formula hl hq.le
  rw [he] at hh
  have hsg:0<Zsigned p.1+capAmplitude*l^3*KSup p.1:=by
    have hm:0 < max (Zsigned p.1+capAmplitude*l^3*KSup p.1) 0:=by
      exact pos_of_mul_pos_right (hh ▸ ht) κ_pos.le
    simpa using hm
  rw [max_eq_left hsg.le] at hh
  apply congrArg (fun a:ℝ=>a • gradient KSup p.1)
  apply (eq_div_iff hK).mpr
  nlinarith [hh]
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.BoundedCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

lemma upperParameter_signed_pos {p:Space 7×ℝ} (hp:U p.1<p.2) :
    0<upperSigned ((upperParameter p.1 p.2)⁻¹ • p.1) := by
  obtain ⟨hl,he⟩:=upperParameter_spec hp
  have hpos:0<upperFamily (upperParameter p.1 p.2) p.1:=by
    rw [he]; exact (U_nonneg _).trans_lt hp
  have hh:0 < max (upperSigned ((upperParameter p.1 p.2)⁻¹ • p.1)) 0:=
    pos_of_mul_pos_right hpos (mul_nonneg κ_pos.le hl.le)
  simpa using hh
lemma upperFlux_uniform_bound : ∃C:ℝ,0<C ∧ ∀p:Space 7×ℝ,‖upperFlux p‖≤C := by
  obtain ⟨C,hC,hcap⟩:=cap_gradient_uniform_bound
  obtain ⟨D,hD,hext⟩:=outer_gradient_uniform_bound
  refine ⟨κ*(C+D),mul_pos κ_pos (add_pos hC hD),?_⟩
  intro p
  by_cases hp:U p.1<p.2
  · have hpos:=upperParameter_signed_pos hp
    rw [upperFlux,ite_eq_left hp,norm_smul,Real.norm_eq_abs,abs_of_pos κ_pos]
    apply mul_le_mul_of_nonneg_left _ κ_pos.le
    split_ifs with hq
    · rw [upperSigned_cap hq] at hpos
      exact (hcap _ hq hpos).trans (by linarith)
    · have hq':1≤Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1):=
        (lt_of_not_ge hq).le
      rw [upperSigned_outer hq'] at hpos
      exact (hext _ hq' hpos).trans (by linarith)
  · simp only [upperFlux,ite_eq_right hp,norm_zero]
    exact mul_nonneg κ_pos.le (by linarith)
lemma upperSigned_gradient_cap {x:Space 7} (hq:Cylindrical.radiusSq axis x<1) :
    gradient upperSigned x=gradient smoothCap x := by
  have hc:ContinuousAt (Cylindrical.radiusSq axis) x:=
    (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt
  have he:upperSigned =ᶠ[𝓝 x] smoothCap:=by
    filter_upwards [hc.eventually (gt_mem_nhds hq)] with y hy
    exact upperSigned_cap hy.le
  exact congrArg ((toDual ℝ (Space 7)).symm) he.fderiv_eq
lemma upperSigned_gradient_outer {x:Space 7} (hq:1<Cylindrical.radiusSq axis x) :
    gradient upperSigned x=gradient outerSigned x := by
  have hc:ContinuousAt (Cylindrical.radiusSq axis) x:=
    (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt
  have he:upperSigned =ᶠ[𝓝 x] outerSigned:=by
    filter_upwards [hc.eventually (lt_mem_nhds hq)] with y hy
    exact upperSigned_outer hy.le
  exact congrArg ((toDual ℝ (Space 7)).symm) he.fderiv_eq
lemma upperFlux_eq_calibration {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≠1) :
    upperFlux p=upperCalibration p := by
  rw [upperCalibration_eq hp hq,upperFlux,ite_eq_left hp]
  congr 1
  rcases lt_or_gt_of_ne hq with h|h
  · rw [ite_eq_left h.le,upperSigned_gradient_cap h]
  · rw [ite_eq_right (not_le.mpr h),upperSigned_gradient_outer h]
lemma upperFlux_eventually_eq {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≠1) :
    upperFlux =ᶠ[𝓝 p] upperCalibration := by
  have hn:∀ᶠ z:Space 7×ℝ in 𝓝 p,U z.1<z.2:=
    (U_continuous.continuousAt.comp continuous_fst.continuousAt).eventually_lt
      continuous_snd.continuousAt hp
  have hl:upperParameter p.1 p.2≠0:=(upperParameter_spec hp).1.ne'
  have hc:ContinuousAt (fun z:Space 7×ℝ=>
      Cylindrical.radiusSq axis ((upperParameter z.1 z.2)⁻¹ • z.1)) p:=
    (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt.comp
      (((upperParameter_contDiffAt hp hq).continuousAt.inv₀ hl).smul continuous_fst.continuousAt)
  filter_upwards [hn,hc.eventually_ne hq] with z hz hzq
  exact upperFlux_eq_calibration hz hzq
lemma upperParameter_measurable : Measurable (fun z:Space 7×ℝ=>upperParameter z.1 z.2) := by
  let S:Set (Space 7×ℝ):={z|U z.1<z.2}
  have hS:IsOpen S:=isOpen_lt (U_continuous.comp continuous_fst) continuous_snd
  have hh:Measurable (S.piecewise (fun z=>upperParameter z.1 z.2) (fun _=>0)):=
    upperParameter_continuousOn.measurable_piecewise continuousOn_const hS.measurableSet
  convert hh using 1
  ext z
  by_cases hz:U z.1<z.2
  · simp [S,hz]
  · simp [S,hz,upperParameter]
lemma upperFlux_measurable : Measurable upperFlux := by
  have hi:Measurable (fun z:Space 7×ℝ=>(upperParameter z.1 z.2)⁻¹ • z.1):=
    upperParameter_measurable.inv.smul measurable_fst
  have hq:Measurable (fun z:Space 7×ℝ=>Cylindrical.radiusSq axis ((upperParameter z.1 z.2)⁻¹ • z.1)):=
    (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.measurable.comp hi
  have h1:MeasurableSet {z:Space 7×ℝ|U z.1<z.2}:=
    measurableSet_lt (U_continuous.measurable.comp measurable_fst) measurable_snd
  have h2:MeasurableSet {z:Space 7×ℝ|Cylindrical.radiusSq axis ((upperParameter z.1 z.2)⁻¹ • z.1)≤1}:=
    measurableSet_le hq measurable_const
  exact ((LipschitzSobolev.measurable_gradient.comp hi).ite h2
    (LipschitzSobolev.measurable_gradient.comp hi)).const_smul κ |>.ite h1 measurable_const

/-- The height primitive is integrable and has linear growth, using the actual
field's uniform bound, independently of seam choices. -/
lemma upperFlux_intervalIntegrable (x:Space 7) (a b:ℝ) :
    IntervalIntegrable (fun s:ℝ=>upperFlux (x,s)) MeasureTheory.volume a b := by
  obtain ⟨C,hC,hbound⟩:=upperFlux_uniform_bound
  rw [intervalIntegrable_iff]
  apply MeasureTheory.Integrable.mono' (g:=fun _:ℝ=>C)
    (intervalIntegrable_const (a:=a) (b:=b) (c:=C)).def'
  · exact (upperFlux_measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun s=>hbound (x,s)
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.CapExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

lemma upperFamily_eq_cap {x:Space 7} {l:ℝ} (hl:0<l)
    (hp:0<upperFamily l x) (hq:Cylindrical.radiusSq axis (l⁻¹ • x)≤1) :
    upperFamily l x=κ*l*smoothCap (l⁻¹ • x) := by
  have hh:0 < max (upperSigned (l⁻¹ • x)) 0:=
    pos_of_mul_pos_right hp (mul_nonneg κ_pos.le hl.le)
  have hs:0<upperSigned (l⁻¹ • x):=by simpa using hh
  rw [upperFamily,max_eq_left hs.le,upperSigned_cap hq]

/-- Smooth signed extensions of the inverse cap parameter through the actual
cap/exterior interface, obtained by IFT with local uniqueness. -/
lemma capParameter_local_extension {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≤1) :
    ∃ψ:Space 7×ℝ→ℝ,ContDiffAt ℝ ∞ ψ p ∧ ψ p=upperParameter p.1 p.2 ∧
      ∀ᶠ z in 𝓝 p, U z.1<z.2 →
        Cylindrical.radiusSq axis ((upperParameter z.1 z.2)⁻¹ • z.1)≤1 →
        ψ z=upperParameter z.1 z.2 := by
  let l:=upperParameter p.1 p.2
  have hl:0<l:=(upperParameter_spec hp).1
  have he:upperFamily l p.1=p.2:=(upperParameter_spec hp).2
  have hpos:0<upperFamily l p.1:=he.symm ▸ (U_nonneg p.1).trans_lt hp
  have hc:ContDiffAt ℝ ∞ smoothCap (l⁻¹ • p.1):=smoothCap_contDiffAt hq
  have hpc:0<smoothCap (l⁻¹ • p.1):=by
    rw [←upperSigned_cap hq]
    exact upperParameter_signed_pos hp
  let F:(Space 7×ℝ)×ℝ→ℝ:=fun z=>κ*z.2*smoothCap (z.2⁻¹ • z.1.1)-z.1.2
  have hi:ContDiffAt ℝ ∞ (fun z:(Space 7×ℝ)×ℝ=>z.2⁻¹ • z.1.1) (p,l):=
    (contDiffAt_snd.inv hl.ne').smul (contDiffAt_fst.fst)
  have hF:ContDiffAt ℝ ∞ F (p,l):=
    ((contDiffAt_const.mul contDiffAt_snd).mul (hc.comp (p,l) hi)).sub contDiffAt_fst.snd
  let ρ:=κ*(smoothCap (l⁻¹ • p.1)-inner ℝ (l⁻¹ • p.1) (gradient smoothCap (l⁻¹ • p.1)))
  have hρ:0<ρ:=mul_pos κ_pos (smoothCap_radial_defect_pos hq hpc)
  have hd:HasDerivAt (fun s:ℝ=>F (p,s)) ρ l := by
    have hh:=((Foliation.hasDerivAt_dilate p.1 hl.ne'
      (hc.differentiableAt (by simp))).const_mul κ).sub_const p.2
    simpa only [F,mul_assoc] using hh
  obtain ⟨ψ,hψ,hψ0,hψeq,huniq⟩:=Foliation.scalar_implicit_unique hF hd hρ.ne'
  refine ⟨ψ,hψ,hψ0,?_⟩
  have hF0:F (p,l)=0:=by
    dsimp [F]
    rw [←upperFamily_eq_cap hl hpos hq,he,sub_self]
  have ht:Tendsto (fun z:Space 7×ℝ=>(z,upperParameter z.1 z.2)) (𝓝 p) (𝓝 (p,l)):=
    tendsto_id.prodMk_nhds (upperParameter_continuousAt hp)
  filter_upwards [ht.eventually huniq] with z hz hzp hzq
  apply hz.mp
  rw [hF0]
  dsimp [F]
  have hzpos:0<upperFamily (upperParameter z.1 z.2) z.1:=
    (upperParameter_spec hzp).2.symm ▸ (U_nonneg z.1).trans_lt hzp
  rw [←upperFamily_eq_cap (upperParameter_spec hzp).1 hzpos hzq,
    (upperParameter_spec hzp).2,sub_self]

lemma gradient_smoothCap_contDiffAt {x:Space 7} (hq:Cylindrical.radiusSq axis x≤1) :
    ContDiffAt ℝ ∞ (gradient smoothCap) x := by
  exact (toDual ℝ (Space 7)).symm.contDiff.contDiffAt.comp x
    ((smoothCap_contDiffAt hq).fderiv_right (by simp))

/-- The actual one-sided cap flux admits a smooth germ even at the seam.
No regularity of the discontinuous full flux is asserted. -/
theorem upperFlux_cap_local_extension {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≤1) :
    ∃B:Space 7×ℝ→Space 7,ContDiffAt ℝ ∞ B p ∧ B p=upperFlux p ∧
      ∀ᶠ z in 𝓝 p,U z.1<z.2 →
        Cylindrical.radiusSq axis ((upperParameter z.1 z.2)⁻¹ • z.1)≤1 → B z=upperFlux z := by
  obtain ⟨ψ,hψ,hψ0,he⟩:=capParameter_local_extension hp hq
  let B:Space 7×ℝ→Space 7:=fun z=>κ • gradient smoothCap ((ψ z)⁻¹ • z.1)
  have hψp:ψ p≠0:=by rw [hψ0]; exact (upperParameter_spec hp).1.ne'
  have hn:ContDiffAt ℝ ∞ (fun z:Space 7×ℝ=>(ψ z)⁻¹ • z.1) p:=
    (hψ.inv hψp).smul contDiffAt_fst
  have hg:ContDiffAt ℝ ∞ (gradient smoothCap) ((ψ p)⁻¹ • p.1):=by
    rw [hψ0]; exact gradient_smoothCap_contDiffAt hq
  refine ⟨B,(hg.comp p hn).const_smul κ,?_,?_⟩
  · simp only [B,hψ0,upperFlux,ite_eq_left hp,ite_eq_left hq]
  · filter_upwards [he] with z hz hzp hzq
    simp only [B,hz hzp hzq,upperFlux,ite_eq_left hzp,ite_eq_left hzq]
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.SeamHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

lemma seamHeight_formula (x:Space 7):
    seamHeight x=κ*Real.sqrt (Cylindrical.radiusSq axis x)*
      capH (Cylindrical.axis axis x/Real.sqrt (Cylindrical.radiusSq axis x)) := by
  simp only [seamHeight,Cylindrical.lift,div_eq_mul_inv,mul_assoc]
lemma seamHeight_contDiffAt {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    ContDiffAt ℝ ∞ seamHeight x := by
  have hs:ContDiffAt ℝ ∞ Real.sqrt (Cylindrical.radiusSq axis x):=Real.contDiffAt_sqrt hq.ne'
  have hL:ContDiffAt ℝ ∞ (Cylindrical.lift axis Real.sqrt (fun q:ℝ=>(Real.sqrt q)⁻¹) capH) x :=
    Cylindrical.contDiffAt_lift hs (hs.inv (Real.sqrt_pos.mpr hq).ne') capH_contDiff.contDiffAt
  exact contDiffAt_const.mul hL
lemma transverse_smul (a:ℝ) (x:Space 7):
    Cylindrical.transverse axis (a • x)=a • Cylindrical.transverse axis x := by
  rw [Cylindrical.transverse,Cylindrical.transverse,Cylindrical.axis_smul]
  module
lemma gradient_seamHeight {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    gradient seamHeight x=κ • seamGradient ((Real.sqrt (Cylindrical.radiusSq axis x))⁻¹ • x) := by
  let q:=Cylindrical.radiusSq axis x
  let r:=Real.sqrt q
  let z:=Cylindrical.axis axis x
  have hr:0<r:=Real.sqrt_pos.mpr hq
  have hs:HasDerivAt Real.sqrt (1/(2*r)) q := Real.hasDerivAt_sqrt hq.ne'
  have hi:HasDerivAt (fun q:ℝ=>(Real.sqrt q)⁻¹) (-(1/(2*r))/r^2) q:=hs.inv hr.ne'
  have hh:=hasDerivAt_capH (z*r⁻¹)
  have hl:=Cylindrical.gradient_lift (e:=axis) hs.differentiableAt hi.differentiableAt hh.differentiableAt
  change gradient (fun y=>κ*Cylindrical.lift axis Real.sqrt (fun q:ℝ=>(Real.sqrt q)⁻¹) capH y) x=_
  have hL:DifferentiableAt ℝ (Cylindrical.lift axis Real.sqrt (fun q:ℝ=>(Real.sqrt q)⁻¹) capH) x :=
    (Cylindrical.contDiffAt_lift (Real.contDiffAt_sqrt hq.ne' : ContDiffAt ℝ 1 Real.sqrt q)
      ((Real.contDiffAt_sqrt hq.ne').inv hr.ne') (capH_contDiff.of_le (by simp)).contDiffAt).differentiableAt (by norm_num)
  rw [gradient_const_mul κ hL,hl]
  congr 1
  rw [hs.deriv,hi.deriv,hh.deriv]
  simp only [seamGradient,Cylindrical.axis_smul,transverse_smul]
  change (2*(1/(2*r))*capH (z*r⁻¹)) • Cylindrical.transverse axis x+
    (r*capHP (z*r⁻¹)) • (r⁻¹ • axis+(2*z*(-(1/(2*r))/r^2)) • Cylindrical.transverse axis x)=
      capHP (r⁻¹*z) • axis+(capH (r⁻¹*z)-r⁻¹*z*capHP (r⁻¹*z)) • (r⁻¹ • Cylindrical.transverse axis x)
  rw [mul_comm z r⁻¹]
  simp only [smul_add,smul_smul]
  have he1:r*capHP (r⁻¹*z)*r⁻¹=capHP (r⁻¹*z):=by field_simp
  have he2:2*(1/(2*r))*capH (r⁻¹*z)+r*capHP (r⁻¹*z)*(2*z*(-(1/(2*r))/r^2))=
      (capH (r⁻¹*z)-r⁻¹*z*capHP (r⁻¹*z))*r⁻¹:=by field_simp; ring
  rw [he1]
  calc
    _=capHP (r⁻¹*z) • axis+
      (2*(1/(2*r))*capH (r⁻¹*z)+r*capHP (r⁻¹*z)*(2*z*(-(1/(2*r))/r^2))) • Cylindrical.transverse axis x := by module
    _=_:=by rw [he2]

lemma normalized_radius_seam {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    Cylindrical.radiusSq axis ((Real.sqrt (Cylindrical.radiusSq axis x))⁻¹ • x)=1 := by
  rw [Cylindrical.radiusSq_smul,inv_pow,Real.sq_sqrt hq.le,inv_mul_cancel₀ hq.ne']

lemma upperFamily_at_seam {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    upperFamily (Real.sqrt (Cylindrical.radiusSq axis x)) x=max (seamHeight x) 0 := by
  have hr:0<Real.sqrt (Cylindrical.radiusSq axis x):=Real.sqrt_pos.mpr hq
  have he:=normalized_radius_seam hq
  rw [upperFamily,upperSigned_cap he.le,smoothCap_at_seam he,seamHeight_formula,
    Cylindrical.axis_smul,←div_eq_inv_mul]
  rw [mul_max_of_nonneg _ _ (mul_nonneg κ_pos.le hr.le),mul_zero]

lemma upperParameter_seam_iff {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:0<Cylindrical.radiusSq axis p.1) :
    Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≤1 ↔ seamHeight p.1≤p.2 := by
  let r:=Real.sqrt (Cylindrical.radiusSq axis p.1)
  let l:=upperParameter p.1 p.2
  have hr:0<r:=Real.sqrt_pos.mpr hq
  have hl:0<l:=(upperParameter_spec hp).1
  have hle:Cylindrical.radiusSq axis (l⁻¹ • p.1)≤1 ↔ r≤l := by
    rw [Cylindrical.radiusSq_smul,inv_pow,←div_eq_inv_mul,div_le_iff₀ (sq_pos_of_pos hl),one_mul]
    have he:r^2=Cylindrical.radiusSq axis p.1:=Real.sq_sqrt hq.le
    rw [←he]
    exact sq_le_sq₀ hr.le hl.le
  rw [hle,←not_lt,upperParameter_lt_iff hp hr,upperFamily_at_seam hq,not_lt]
  exact max_le_iff.trans (and_iff_left ((U_nonneg _).trans hp.le))
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.ClosedGermExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uG

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold
namespace Bernoulli.LocalExtension
variable {E : Type uE} {G : Type uG} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
/-- C1 germs agreeing on a closed subset glue to a global C1 extension.
This is an application of the actual smooth partition of unity, not a Whitney
extension premise. -/
lemma exists_contDiff_one_of_closed_germs {S:Set E} (hS:IsClosed S) {F:E→G}
    (hg:∀x∈S,∃B:E→G,ContDiffAt ℝ 1 B x ∧ ∀ᶠ y in 𝓝 x,y∈S→B y=F y) :
    ∃B:E→G,ContDiff ℝ 1 B ∧ EqOn B F S := by
  classical
  let t:E→Set G:=fun x=>if x∈S then {F x} else univ
  have ht(x:E):Convex ℝ (t x):=by
    by_cases hx:x∈S
    · simpa only [t,ite_eq_left hx] using convex_singleton (F x)
    · simpa only [t,ite_eq_right hx] using (convex_univ : Convex ℝ (univ:Set G))
  have hl(x:E):∃U∈𝓝 x,∃g:E→G,ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,G) 1 g U ∧
      ∀y∈U,g y∈t y := by
    by_cases hx:x∈S
    · obtain ⟨g,hgc,hge⟩:=hg x hx
      obtain ⟨V,hV,hgV⟩:=hgc.contDiffOn le_rfl (by norm_num)
      refine ⟨V∩{y|y∈S → g y=F y},inter_mem hV hge,g,?_,?_⟩
      · exact (hgV.mono inter_subset_left).contMDiffOn
      · intro y hy
        by_cases hyS:y∈S
        · simp only [t,ite_eq_left hyS,mem_singleton_iff]
          exact hy.2 hyS
        · simp only [t,ite_eq_right hyS,mem_univ]
    · refine ⟨Sᶜ,hS.isOpen_compl.mem_nhds hx,fun _=>0,contMDiffOn_const,?_⟩
      intro y hy
      simp only [t,ite_eq_right hy,mem_univ]
  obtain ⟨B,hB⟩:=exists_contMDiffMap_forall_mem_convex_of_local 𝓘(ℝ,E) ht hl
  refine ⟨B,B.contMDiff.contDiff,?_⟩
  intro x hx
  simpa only [t,ite_eq_left hx,mem_singleton_iff] using hB x
end Bernoulli.LocalExtension

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.SmoothLocalizedExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uG

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold
namespace Bernoulli.LocalExtension
variable {E : Type uE} {G : Type uG} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
lemma exists_cutoff {K D:Set E} (hK:IsCompact K) (hD:IsOpen D) (hKD:K⊆D) :
    ∃φ:E→ℝ,ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ⊆D ∧
      (∀ᶠ x in 𝓝ˢ K,φ x=1) := by
  obtain ⟨δ,hδ,hδD⟩:=hK.exists_thickening_subset_open hD hKD
  have hki:K⊆interior (Metric.cthickening (δ/2) K):=
    (Metric.self_subset_thickening (half_pos hδ) _).trans
      (Metric.thickening_subset_interior_cthickening _ _)
  obtain ⟨φ,hφ1,hφ0,hφb⟩:=exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,E)) (n:=⊤) hK.isClosed hki
  refine ⟨φ,φ.contMDiff.contDiff,HasCompactSupport.intro hK.cthickening hφ0,?_,hφ1⟩
  have hs:tsupport (φ:E→ℝ)⊆Metric.cthickening (δ/2) K:=by
    apply closure_minimal _ Metric.isClosed_cthickening
    intro x hx
    by_contra hn
    exact hx (hφ0 x hn)
  exact hs.trans ((Metric.cthickening_subset_thickening' hδ (by linarith) _).trans hδD)

/-- A compact part of a genuinely smooth open domain admits a global smooth
representative. This permits use of global calculus only after verifying the
actual local hypotheses. -/
lemma exists_contDiff_extension {n:ℕ∞} {F:E→G} {K D:Set E}
    (hK:IsCompact K) (hD:IsOpen D) (hKD:K⊆D) (hF:ContDiffOn ℝ n F D) :
    ∃B:E→G,ContDiff ℝ n B ∧ B =ᶠ[𝓝ˢ K] F := by
  obtain ⟨φ,hφ,hφc,hφD,hφ1⟩:=exists_cutoff hK hD hKD
  refine ⟨fun x=>φ x • F x,?_,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx:x∈D
    · exact (hφ.of_le (m:=n) (by exact_mod_cast (le_top : n≤⊤))).contDiffAt.smul (hF.contDiffAt (hD.mem_nhds hx))
    · have hxt:x∉tsupport φ:=fun h=>hx (hφD h)
      apply (contDiffAt_const (c:=(0:G))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxt] with y hy
      simp [hy]
  · filter_upwards [hφ1] with x hx
    simp [hx]
end Bernoulli.LocalExtension

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.LocalFluxExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison

lemma exteriorFlux_contDiffAt {p:Space 7×ℝ} (hq:0<Cylindrical.radiusSq axis p.1) :
    ContDiffAt ℝ ∞ exteriorFlux p := by
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hq
  have hZ:ContDiffAt ℝ ∞ Zsigned p.1:=signed_contDiffAt hx ha
  have hK:ContDiffAt ℝ ∞ KSup p.1:=KSup_contDiffAt hx ha
  have hgZ:ContDiffAt ℝ ∞ (gradient Zsigned) p.1:=
    (toDual ℝ (Space 7)).symm.contDiff.contDiffAt.comp p.1 (hZ.fderiv_right (by simp))
  have hgK:ContDiffAt ℝ ∞ (gradient KSup) p.1:=
    (toDual ℝ (Space 7)).symm.contDiff.contDiffAt.comp p.1 (hK.fderiv_right (by simp))
  exact ((hgZ.comp p contDiffAt_fst).const_smul κ).add
    (((contDiffAt_snd.sub (contDiffAt_const.mul (hZ.comp p contDiffAt_fst))).div
      (hK.comp p contDiffAt_fst) (KSup_pos hx ha).ne').smul (hgK.comp p contDiffAt_fst))
lemma upperFlux_eq_exterior {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:0<Cylindrical.radiusSq axis p.1) (ht:p.2<seamHeight p.1) :
    upperFlux p=exteriorFlux p := by
  have hqn:¬Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≤1:=
    fun h=>not_lt.mpr ((upperParameter_seam_iff hp hq).mp h) ht
  have hqs:(upperParameter p.1 p.2)^2<Cylindrical.radiusSq axis p.1:=by
    have hl:0<upperParameter p.1 p.2:=(upperParameter_spec hp).1
    have hh:1<Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1):=not_le.mp hqn
    rw [Cylindrical.radiusSq_smul,inv_pow,←div_eq_inv_mul,lt_div_iff₀ (sq_pos_of_pos hl),one_mul] at hh
    exact hh
  rw [upperFlux_eq_calibration hp (ne_of_gt (not_le.mp hqn)),upperCalibration_outer_affine hp hqs]
  rfl

/-- The actual two branch fields have global C1 representatives on any compact
positive-height tube away from the axis. Only the cap-side field is extended
from a one-sided region; the full discontinuous flux is never declared smooth. -/
theorem compact_branch_extensions {K:Set (Space 7×ℝ)} (hK:IsCompact K)
    (hp:∀p∈K,U p.1<p.2) (hq:∀p∈K,0<Cylindrical.radiusSq axis p.1) :
    ∃A B:Space 7×ℝ→Space 7,ContDiff ℝ 1 A ∧ ContDiff ℝ 1 B ∧
      EqOn A exteriorFlux K ∧
      ∀p∈K,seamHeight p.1≤p.2 → B p=upperFlux p := by
  let D:Set (Space 7×ℝ):={p|0<Cylindrical.radiusSq axis p.1}
  have hD:IsOpen D:=isOpen_lt continuous_const
    ((Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.comp continuous_fst)
  have hKD:K⊆D:=hq
  obtain ⟨A,hA,hAe⟩:=LocalExtension.exists_contDiff_extension (n:=1) hK hD hKD
    (fun p hpd=>(exteriorFlux_contDiffAt hpd).of_le (by simp) |>.contDiffWithinAt)
  let S:Set (Space 7×ℝ):={p∈K|seamHeight p.1≤p.2}
  have hσ:ContinuousOn (fun p:Space 7×ℝ=>seamHeight p.1) K:=by
    intro p hpk
    exact ((seamHeight_contDiffAt (hq p hpk)).continuousAt.comp continuous_fst.continuousAt).continuousWithinAt
  have hS:IsClosed S:=hK.isClosed.isClosed_le hσ continuousOn_snd
  obtain ⟨B,hB,hBe⟩:=LocalExtension.exists_contDiff_one_of_closed_germs hS (F:=upperFlux) (by
    intro p hps
    have hqp:=((upperParameter_seam_iff (hp p hps.1) (hq p hps.1)).mpr hps.2)
    obtain ⟨C,hC,hCp,hCe⟩:=upperFlux_cap_local_extension (hp p hps.1) hqp
    refine ⟨C,hC.of_le (by simp),?_⟩
    filter_upwards [hCe] with y hy hys
    exact hy (hp y hys.1) ((upperParameter_seam_iff (hp y hys.1) (hq y hys.1)).mpr hys.2))
  refine ⟨A,B,hA,hB,?_,?_⟩
  · intro p hpk
    exact (hAe.filter_mono (nhds_le_nhdsSet hpk)).self_of_nhds
  · intro p hpk hpt
    exact hBe ⟨hpk,hpt⟩
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.JointIntervalIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uG

section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Bernoulli.ParametricIntegral
variable {E : Type uE} {G : Type uG} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

omit [CompleteSpace G] in
/-- A compact-interval parameter derivative, with domination obtained from C1
on an actual compact product. No derivative bound is an extra premise. -/
theorem fixed_hasFDerivAt {F:E×ℝ→G} (hF:ContDiff ℝ 1 F) (x:E) (a b:ℝ) :
    HasFDerivAt (fun y:E=>∫t in a..b,F (y,t))
      (∫t in a..b,fderiv ℝ F (x,t) ∘L ContinuousLinearMap.inl ℝ E ℝ) x := by
  let D:E×ℝ→E→L[ℝ] G:=fun p=>fderiv ℝ F p ∘L ContinuousLinearMap.inl ℝ E ℝ
  have hD:Continuous D:=(hF.continuous_fderiv (by norm_num)).clm_comp continuous_const
  have hc:IsCompact ((Metric.closedBall x 1)×ˢ(uIcc a b)):=
    (isCompact_closedBall x 1).prod isCompact_uIcc
  obtain ⟨C,hC⟩:=hc.exists_bound_of_continuousOn hD.continuousOn
  have hFu (y:E):Continuous (fun t:ℝ=>F (y,t)):=hF.continuous.comp (continuous_const.prodMk continuous_id)
  have hDu (y:E):Continuous (fun t:ℝ=>D (y,t)):=hD.comp (continuous_const.prodMk continuous_id)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F:=fun y t=>F (y,t)) (F':=fun y t=>D (y,t))
    (s:=Metric.closedBall x 1) (bound:=fun _=>C) (Metric.closedBall_mem_nhds x (by norm_num))
  · exact .of_forall fun y=>(hFu y).aestronglyMeasurable
  · exact (hFu x).intervalIntegrable a b
  · exact (hDu x).aestronglyMeasurable
  · exact ae_of_all _ fun t ht y hy=>hC (y,t) ⟨hy,uIoc_subset_uIcc ht⟩
  · exact intervalIntegrable_const
  · exact ae_of_all _ fun t _ y _=>by
      have hi:HasFDerivAt (fun z:E=>(z,t)) (ContinuousLinearMap.inl ℝ E ℝ) y := by
        simpa only [ContinuousLinearMap.inl,id_eq] using
          (hasFDerivAt_id (𝕜:=ℝ) y).prodMk (hasFDerivAt_const t y)
      exact ((hF.differentiable (by norm_num)) (y,t)).hasFDerivAt.comp y hi

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [CompleteSpace G] in
lemma heightPrimitive_rescale (F:E×ℝ→G) (p:E×ℝ) :
    heightPrimitive F p=∫s in (0:ℝ)..1,p.2 • F (p.1,s*p.2) := by
  by_cases ht:p.2=0
  · simp [heightPrimitive,ht]
  · rw [intervalIntegral.integral_smul]
    have hh:=intervalIntegral.integral_comp_mul_right (a:=0) (b:=1) (fun s:ℝ=>F (p.1,s)) ht
    rw [hh]
    simp only [zero_mul,one_mul,smul_smul,mul_inv_cancel₀ ht,one_smul,heightPrimitive]

omit [CompleteSpace G] in
/-- Joint differentiability is proved, rather than inferred from separate
partial derivatives. Rescaling to [0,1] gives a compact dominated derivative. -/
theorem heightPrimitive_differentiable [CompleteSpace G] {F:E×ℝ→G} (hF:ContDiff ℝ 1 F) :
    Differentiable ℝ (heightPrimitive F) := by
  let B:(E×ℝ)×ℝ→G:=fun z=>z.1.2 • F (z.1.1,z.2*z.1.2)
  have hB:ContDiff ℝ 1 B:=by
    have hm:ContDiff ℝ 1 (fun z:(E×ℝ)×ℝ=>(z.1.1,z.2*z.1.2)):=by fun_prop
    exact (contDiff_fst.snd).smul (hF.comp hm)
  intro p
  have hd: DifferentiableAt ℝ (fun y:E×ℝ=>∫s in (0:ℝ)..1,B (y,s)) p :=
    (fixed_hasFDerivAt hB p 0 1).differentiableAt
  exact hd.congr_of_eventuallyEq (.of_forall fun q=>heightPrimitive_rescale F q)

omit [NormedSpace ℝ E] [ProperSpace E] in
lemma heightPrimitive_height {F:E×ℝ→G} (hF:Continuous F) (p:E×ℝ) :
    HasDerivAt (fun t:ℝ=>heightPrimitive F (p.1,t)) (F p) p.2 := by
  have hc:Continuous (fun t:ℝ=>F (p.1,t)):=hF.comp (continuous_const.prodMk continuous_id)
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 p.2)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
lemma heightPrimitive_fderiv {F:E×ℝ→G} (hF:ContDiff ℝ 1 F) (p:E×ℝ) (v:E) (r:ℝ) :
    fderiv ℝ (heightPrimitive F) p (v,r)=
      (∫s in (0:ℝ)..p.2,fderiv ℝ F (p.1,s) (v,0))+r • F p := by
  have hd:HasFDerivAt (heightPrimitive F) (fderiv ℝ (heightPrimitive F) p) p:=
    (heightPrimitive_differentiable hF p).hasFDerivAt
  have hi:HasFDerivAt (fun y:E=>(y,p.2)) (ContinuousLinearMap.inl ℝ E ℝ) p.1:=by
    simpa only [ContinuousLinearMap.inl,id_eq] using
      (hasFDerivAt_id (𝕜:=ℝ) p.1).prodMk (hasFDerivAt_const p.2 p.1)
  have he: fderiv ℝ (heightPrimitive F) p ∘L ContinuousLinearMap.inl ℝ E ℝ=
      ∫s in (0:ℝ)..p.2,fderiv ℝ F (p.1,s) ∘L ContinuousLinearMap.inl ℝ E ℝ :=
    (HasFDerivAt.comp (g:=heightPrimitive F) (f:=fun y:E=>(y,p.2)) p.1 hd hi).unique
      (fixed_hasFDerivAt hF p.1 0 p.2)
  have hx:=congrArg (fun L:E→L[ℝ] G=>L v) he
  have hDc:Continuous (fun s:ℝ=>fderiv ℝ F (p.1,s) ∘L ContinuousLinearMap.inl ℝ E ℝ):=
    ((hF.continuous_fderiv (by norm_num)).comp (continuous_const.prodMk continuous_id)).clm_comp continuous_const
  rw [ContinuousLinearMap.intervalIntegral_apply (hDc.intervalIntegrable 0 p.2)] at hx
  have hh:=hd.comp_hasDerivAt p.2 ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  have ht:fderiv ℝ (heightPrimitive F) p (0,1)=F p:=hh.unique (heightPrimitive_height hF.continuous p)
  calc
    _=fderiv ℝ (heightPrimitive F) p ((v,0)+r • ((0:E),(1:ℝ))) := by congr 1; ext <;> simp
    _=fderiv ℝ (heightPrimitive F) p (v,0)+r • fderiv ℝ (heightPrimitive F) p (0,1) := by rw [map_add,map_smul]
    _=_ := by rw [ht]; exact congrArg (·+r • F p) hx

lemma graph_fderiv {F:E×ℝ→G} (hF:ContDiff ℝ 1 F) {u:E→ℝ} {x:E}
    (hu:DifferentiableAt ℝ u x) (v:E) :
    fderiv ℝ (fun y:E=>heightPrimitive F (y,u y)) x v=
      (∫s in (0:ℝ)..u x,fderiv ℝ F (x,s) (v,0))+fderiv ℝ u x v • F (x,u x) := by
  have hh:HasFDerivAt (fun y:E=>heightPrimitive F (y,u y))
      (fderiv ℝ (heightPrimitive F) (x,u x) ∘L
        (ContinuousLinearMap.id ℝ E).prod (fderiv ℝ u x)) x :=
    HasFDerivAt.comp (g:=heightPrimitive F) (f:=fun y:E=>(y,u y)) x
      (heightPrimitive_differentiable hF (x,u x)).hasFDerivAt
      ((hasFDerivAt_id x).prodMk hu.hasFDerivAt)
  rw [hh.fderiv]
  exact heightPrimitive_fderiv hF (x,u x) v (fderiv ℝ u x v)
end Bernoulli.ParametricIntegral

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.FoliationGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.Foliation
open ParametricIntegral
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
lemma divergence_graph_primitive {A:E×ℝ→E} (hA:ContDiff ℝ 1 A)
    {u:E→ℝ} {x:E} (hu:DifferentiableAt ℝ u x) :
    divergence (fun y:E=>heightPrimitive A (y,u y)) x=
      (∫s in (0:ℝ)..u x,divergence (fun y:E=>A (y,s)) x)+
        inner ℝ (A (x,u x)) (gradient u x) := by
  let e:=stdOrthonormalBasis ℝ E
  have hc:Continuous (fun s:ℝ=>fderiv ℝ A (x,s)):=
    (hA.continuous_fderiv (by norm_num)).comp (continuous_const.prodMk continuous_id)
  have hci (i):Continuous (fun s:ℝ=>inner ℝ (e i) (fderiv ℝ A (x,s) (e i,0))):=
    continuous_const.inner (hc.clm_apply continuous_const)
  have hi (s:ℝ) (v:E):fderiv ℝ (fun y:E=>A (y,s)) x v=fderiv ℝ A (x,s) (v,0):=by
    rw [(sliceLeft_hasFDerivAt ((hA.differentiable (by norm_num)) (x,s))).fderiv]
    simp
  have he (v:E):inner ℝ v (∫s in (0:ℝ)..u x,fderiv ℝ A (x,s) (v,0))=
      ∫s in (0:ℝ)..u x,inner ℝ v (fderiv ℝ A (x,s) (v,0)) :=
    ((innerSL ℝ v).intervalIntegral_comp_comm
      ((hc.clm_apply continuous_const).intervalIntegrable 0 (u x))).symm
  rw [divergence]
  simp_rw [graph_fderiv hA hu,inner_add_right,real_inner_smul_right,he]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [←intervalIntegral.integral_finsetSum (fun i _=>(hci i).intervalIntegrable 0 (u x))]
    apply intervalIntegral.integral_congr
    intro s _
    simp only [divergence,hi]
    rfl
  · simp_rw [←inner_gradient_left]
    rw [(stdOrthonormalBasis ℝ E).sum_inner_mul_inner]
    exact real_inner_comm _ _
lemma continuous_spatial_divergence {A:E×ℝ→E} (hA:ContDiff ℝ 1 A) (x:E) :
    Continuous (fun s:ℝ=>divergence (fun y:E=>A (y,s)) x) := by
  have hc:Continuous (fun s:ℝ=>fderiv ℝ A (x,s)):=
    (hA.continuous_fderiv (by norm_num)).comp (continuous_const.prodMk continuous_id)
  have hi (s:ℝ) (v:E):fderiv ℝ (fun y:E=>A (y,s)) x v=fderiv ℝ A (x,s) (v,0):=by
    rw [(sliceLeft_hasFDerivAt ((hA.differentiable (by norm_num)) (x,s))).fderiv]
    simp
  simp only [divergence,hi]
  exact continuous_finsetSum _ (fun i _=>continuous_const.inner (hc.clm_apply continuous_const))

/-- Integrating the nonlinear bulk inequality gives exactly the flux difference.
This is FTC and parameter differentiation, not a postulated graph comparison. -/
lemma integrated_bulk {A:E×ℝ→E} (hA:ContDiff ℝ 1 A) (x:E) {a b:ℝ} (hab:a≤b)
    (hbulk:∀s∈Icc a b,divergence (fun y:E=>A (y,s)) x+
      inner ℝ (A (x,s)) (deriv (fun t:ℝ=>A (x,t)) s)≤0) :
    2*(∫s in a..b,divergence (fun y:E=>A (y,s)) x)≤‖A (x,a)‖^2-‖A (x,b)‖^2 := by
  have hAC:ContDiff ℝ 1 (fun s:ℝ=>A (x,s)):=hA.comp (contDiff_const.prodMk contDiff_id)
  have hDC:Continuous (deriv (fun t:ℝ=>A (x,t))) := hAC.continuous_deriv (by norm_num)
  have hAD(s:ℝ):HasDerivAt (fun t:ℝ=>A (x,t)) (deriv (fun t:ℝ=>A (x,t)) s) s:=
    (hAC.differentiable (by norm_num) s).hasDerivAt
  have hN(s:ℝ):HasDerivAt (fun t:ℝ=>‖A (x,t)‖^2)
      (2*inner ℝ (A (x,s)) (deriv (fun t:ℝ=>A (x,t)) s)) s:=by
    simpa only [real_inner_self_eq_norm_sq,real_inner_comm (deriv (fun t:ℝ=>A (x,t)) s),two_mul] using
      (hAD s).inner ℝ (hAD s)
  have hc:Continuous (fun s:ℝ=>2*inner ℝ (A (x,s)) (deriv (fun t:ℝ=>A (x,t)) s)):=
    continuous_const.mul (hAC.continuous.inner hDC)
  have hFTC:(∫s in a..b,2*inner ℝ (A (x,s)) (deriv (fun t:ℝ=>A (x,t)) s))=
      ‖A (x,b)‖^2-‖A (x,a)‖^2:=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _=>hN s) (hc.intervalIntegrable a b)
  have hi:IntervalIntegrable (fun s:ℝ=>2*divergence (fun y:E=>A (y,s)) x) volume a b:=
    (continuous_const.mul (continuous_spatial_divergence hA x)).intervalIntegrable a b
  have hle:(∫s in a..b,2*divergence (fun y:E=>A (y,s)) x+
      2*inner ℝ (A (x,s)) (deriv (fun t:ℝ=>A (x,t)) s))≤0 := by
    have hh:=intervalIntegral.integral_mono_on hab (hi.add (hc.intervalIntegrable a b))
      (intervalIntegrable_const (c:=(0:ℝ))) (fun s hs=>by linarith [hbulk s hs])
    simpa using hh
  rw [intervalIntegral.integral_add hi (hc.intervalIntegrable a b),hFTC,
    intervalIntegral.integral_const_mul] at hle
  linarith
lemma divergence_smul_sub {f g:E→E} {x:E}
    (hf:DifferentiableAt ℝ f x) (hg:DifferentiableAt ℝ g x) (c:ℝ) :
    divergence (fun y=>c • (f y-g y)) x=c*(divergence f x-divergence g x) := by
  have hh:HasFDerivAt (fun y=>c • (f y-g y)) (c • (fderiv ℝ f x-fderiv ℝ g x)) x:=
    (hf.hasFDerivAt.sub hg.hasFDerivAt).const_smul c
  rw [divergence,hh.fderiv]
  simp only [smul_apply,sub_apply,
    real_inner_smul_right,inner_sub_right,Finset.mul_sum,Finset.sum_sub_distrib,divergence,mul_sub]

lemma graph_potential_identity {A:E×ℝ→E} (hA:ContDiff ℝ 1 A)
    {u v:E→ℝ} {x:E} (hu:DifferentiableAt ℝ u x) (hv:DifferentiableAt ℝ v x) :
    divergence (graphPotential A u v) x=
      2*(∫s in u x..v x,divergence (fun y:E=>A (y,s)) x)+
        2*inner ℝ (A (x,v x)) (gradient v x)-2*inner ℝ (A (x,u x)) (gradient u x) := by
  have hd(w:E→ℝ)(hw:DifferentiableAt ℝ w x):
      DifferentiableAt ℝ (fun y:E=>heightPrimitive A (y,w y)) x:=
    DifferentiableAt.comp (f:=fun y:E=>(y,w y)) (g:=heightPrimitive A) x
      (heightPrimitive_differentiable hA (x,w x)) (differentiableAt_id.prodMk hw)
  unfold graphPotential
  rw [divergence_smul_sub (hd v hv) (hd u hu),
    divergence_graph_primitive hA hv,divergence_graph_primitive hA hu]
  have hi:=intervalIntegral.integral_interval_sub_left (μ:=volume)
    ((continuous_spatial_divergence hA x).intervalIntegrable 0 (v x))
    ((continuous_spatial_divergence hA x).intervalIntegrable 0 (u x))
  rw [←hi]
  ring

end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.PiecewiseFoliationGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma divergence_add {f g:E→E} {x:E}
    (hf:DifferentiableAt ℝ f x) (hg:DifferentiableAt ℝ g x) :
    divergence (fun y=>f y+g y) x=divergence f x+divergence g x := by
  have hd : fderiv ℝ (fun y=>f y+g y) x = fderiv ℝ f x + fderiv ℝ g x :=
    (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv
  rw [divergence,hd]
  simp only [add_apply,inner_add_right,Finset.sum_add_distrib,divergence]
lemma graphPotential_differentiableAt {A:E×ℝ→E} (hA:ContDiff ℝ 1 A)
    {u v:E→ℝ} {x:E} (hu:DifferentiableAt ℝ u x) (hv:DifferentiableAt ℝ v x) :
    DifferentiableAt ℝ (graphPotential A u v) x := by
  have hd(w:E→ℝ)(hw:DifferentiableAt ℝ w x):
      DifferentiableAt ℝ (fun y:E=>ParametricIntegral.heightPrimitive A (y,w y)) x:=
    DifferentiableAt.comp (f:=fun y:E=>(y,w y)) (g:=ParametricIntegral.heightPrimitive A) x
      (ParametricIntegral.heightPrimitive_differentiable hA (x,w x)) (differentiableAt_id.prodMk hw)
  exact ((hd v hv).sub (hd u hu)).const_smul 2

end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.ClampedFoliationGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma le_clampedHeight [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (u σ v:E→ℝ) (x:E):u x≤clampedHeight u σ v x:=le_max_left _ _
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma clampedHeight_le [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {u σ v:E→ℝ} {x:E} (h:u x≤v x):clampedHeight u σ v x≤v x:=
  max_le h (min_le_left _ _)
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma below_clampedHeight [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {u σ v:E→ℝ} {x:E} {t:ℝ}
    (hl:u x<t) (ht:t<clampedHeight u σ v x):t<σ x := by
  have hh:=lt_max_iff.mp ht
  rcases hh with h|h
  · exact False.elim ((not_lt.mpr hl.le) h)
  · exact h.trans_le (min_le_right _ _)
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma above_clampedHeight [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {u σ v:E→ℝ} {x:E} {t:ℝ}
    (hu:clampedHeight u σ v x<t) (ht:t<v x):σ x<t := by
  have hh:min (v x) (σ x)<t:=(le_max_right _ _).trans_lt hu
  exact (min_lt_iff.mp hh).resolve_left (not_lt.mpr ht.le)

omit [FiniteDimensional ℝ E] in
lemma graphPotential_eq_integral [FiniteDimensional ℝ E]
    {A:E×ℝ→E} (hA:Continuous A) (u v:E→ℝ) (x:E) :
    graphPotential A u v x=(2:ℝ) • (∫s in u x..v x,A (x,s)) := by
  have hc:Continuous (fun s:ℝ=>A (x,s)):=hA.comp (continuous_const.prodMk continuous_id)
  unfold graphPotential ParametricIntegral.heightPrimitive
  rw [←intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable 0 (v x))
    (hc.intervalIntegrable 0 (u x))]

lemma clamped_integral_identity {F A B:E×ℝ→E} (hA:Continuous A) (hB:Continuous B)
    {u σ v:E→ℝ} {x:E} (huv:u x≤v x)
    (hFi:∀a b:ℝ,IntervalIntegrable (fun t:ℝ=>F (x,t)) volume a b)
    (hAe:∀t∈Ioo (u x) (v x),t<σ x → F (x,t)=A (x,t))
    (hBe:∀t∈Ioo (u x) (v x),σ x<t → F (x,t)=B (x,t)) :
    (2:ℝ) • (∫s in u x..v x,F (x,s))=
      splitGraphPotential A B u (clampedHeight u σ v) v x := by
  let w:=clampedHeight u σ v x
  have huw:u x≤w:=le_clampedHeight u σ v x
  have hwv:w≤v x:=clampedHeight_le huv
  have heA:(∫s in u x..w,F (x,s))=∫s in u x..w,A (x,s):=
    intervalIntegral.integral_congr_Ioo_of_le huw (fun t ht=>hAe t ⟨ht.1,ht.2.trans_le hwv⟩
      (below_clampedHeight ht.1 ht.2))
  have heB:(∫s in w..v x,F (x,s))=∫s in w..v x,B (x,s):=
    intervalIntegral.integral_congr_Ioo_of_le hwv (fun t ht=>hBe t ⟨huw.trans_lt ht.1,ht.2⟩
      (above_clampedHeight ht.1 ht.2))
  rw [splitGraphPotential,graphPotential_eq_integral hA,graphPotential_eq_integral hB]
  rw [←intervalIntegral.integral_add_adjacent_intervals (hFi (u x) w) (hFi w (v x)),heA,heB,smul_add]

lemma integrated_bulk_open {A:E×ℝ→E} (hA:ContDiff ℝ 1 A) (x:E) {a b:ℝ} (hab:a≤b)
    (hbulk:∀s∈Ioo a b,divergence (fun y:E=>A (y,s)) x+
      inner ℝ (A (x,s)) (deriv (fun t:ℝ=>A (x,t)) s)≤0) :
    2*(∫s in a..b,divergence (fun y:E=>A (y,s)) x)≤‖A (x,a)‖^2-‖A (x,b)‖^2 := by
  rcases hab.eq_or_lt with he|hlt
  · subst b; simp
  · apply integrated_bulk hA x hab
    have hAC:ContDiff ℝ 1 (fun s:ℝ=>A (x,s)):=hA.comp (contDiff_const.prodMk contDiff_id)
    have hc:Continuous (fun s:ℝ=>divergence (fun y:E=>A (y,s)) x+
        inner ℝ (A (x,s)) (deriv (fun t:ℝ=>A (x,t)) s)):=
      (continuous_spatial_divergence hA x).add (hAC.continuous.inner (hAC.continuous_deriv (by norm_num)))
    exact fun s hs=>le_on_closure hbulk hc.continuousOn continuousOn_const (by rwa [closure_Ioo hlt.ne])

end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.VerticalGraphLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma real_interval_combination {a b s:ℝ} (hab:a≤b) (hs:s∈Icc a b) :
    ∃t∈Icc (0:ℝ) 1,s=(1-t)*a+t*b := by
  rcases hab.eq_or_lt with he|hl
  · subst b
    exact ⟨0,by norm_num,by have hh:=le_antisymm hs.2 hs.1; simpa using hh⟩
  · refine ⟨(s-a)/(b-a),⟨div_nonneg (sub_nonneg.mpr hs.1) (sub_pos.mpr hl).le,?_⟩,?_⟩
    · exact (div_le_one (sub_pos.mpr hl)).mpr (sub_le_sub_right hs.2 a)
    · field_simp; ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma eventually_vertical_segment [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {u v:E→ℝ} {x:E} (hu:ContinuousAt u x) (hv:ContinuousAt v x)
    (huv:u x≤v x) {V:Set (E×ℝ)} (hV:V∈𝓝ˢ ({x}×ˢ Icc (u x) (v x))) :
    ∀ᶠ y in 𝓝 x,u y≤v y → ∀s∈Icc (u y) (v y),(y,s)∈V := by
  have hh:∀ᶠ y in 𝓝 x,∀t∈Icc (0:ℝ) 1,(y,(1-t)*u y+t*v y)∈V:=by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hc:ContinuousAt (fun p:E×ℝ=>(p.1,(1-p.2)*u p.1+p.2*v p.1)) (x,t):=by
      exact continuous_fst.continuousAt.prodMk
        (((continuousAt_const.sub continuous_snd.continuousAt).mul (hu.comp continuous_fst.continuousAt)).add
          (continuous_snd.continuousAt.mul (hv.comp continuous_fst.continuousAt)))
    have hp:(x,(1-t)*u x+t*v x)∈({x}×ˢ Icc (u x) (v x)):=by
      refine ⟨rfl,?_,?_⟩
      · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr huv)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr huv)]
    exact hc.eventually ((nhds_le_nhdsSet hp) hV)
  filter_upwards [hh] with y hy hyuv s hs
  obtain ⟨t,ht,rfl⟩:=real_interval_combination hyuv hs
  exact hy t ht

end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.PrimitiveLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.DeSilvaJerison
open Foliation

lemma above_U_isOpen : IsOpen {p:Space 7×ℝ|U p.1<p.2}:=
  isOpen_lt (U_continuous.comp continuous_fst) continuous_snd

lemma upperFlux_compact_tube {x:Space 7} {a b:ℝ} (hua:U x<a)
    (hqx:0<Cylindrical.radiusSq axis x) :
    ∃K:Set (Space 7×ℝ),IsCompact K ∧ ({x}×ˢ Icc a b)⊆interior K ∧
      (∀p∈K,U p.1<p.2) ∧ (∀p∈K,0<Cylindrical.radiusSq axis p.1) := by
  let D:Set (Space 7×ℝ):={p|U p.1<p.2 ∧ 0<Cylindrical.radiusSq axis p.1}
  have hD:IsOpen D:=above_U_isOpen.inter (isOpen_lt continuous_const
    ((Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.comp continuous_fst))
  have hk:({x}×ˢ Icc a b)⊆D:=by
    intro p hp
    have hpx:p.1=x:=hp.1
    exact ⟨by rw [hpx]; exact hua.trans_le hp.2.1,by rwa [hpx]⟩
  obtain ⟨K,hK,hKi,hKD⟩:=exists_compact_between (isCompact_singleton.prod isCompact_Icc) hD hk
  exact ⟨K,hK,hKi,fun p hp=>(hKD hp).1,fun p hp=>(hKD hp).2⟩

end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.FoliationBulkGerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
lemma bulkExpression_congr {A B:E×ℝ→E} {p:E×ℝ} (he:A =ᶠ[𝓝 p] B) :
    bulkExpression A p=bulkExpression B p := by
  have hx:(fun x=>A (x,p.2)) =ᶠ[𝓝 p.1] (fun x=>B (x,p.2)):=
    he.comp_tendsto (continuousAt_id.prodMk continuousAt_const)
  have ht:(fun t=>A (p.1,t)) =ᶠ[𝓝 p.2] (fun t=>B (p.1,t)):=
    he.comp_tendsto (continuousAt_const.prodMk continuousAt_id)
  unfold bulkExpression divergence
  rw [hx.fderiv_eq,he.self_of_nhds,ht.deriv_eq]
end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.FluxBulk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison
open Foliation
lemma normalized_radius_eq_one_iff {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:0<Cylindrical.radiusSq axis p.1) :
    Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)=1 ↔ seamHeight p.1=p.2 := by
  let l:=upperParameter p.1 p.2
  let r:=Real.sqrt (Cylindrical.radiusSq axis p.1)
  have hl:0<l:=(upperParameter_spec hp).1
  have hr:0<r:=Real.sqrt_pos.mpr hq
  have hr2:r^2=Cylindrical.radiusSq axis p.1:=Real.sq_sqrt hq.le
  have hrl:Cylindrical.radiusSq axis (l⁻¹ • p.1)=1 ↔ l=r:=by
    rw [Cylindrical.radiusSq_smul,inv_pow,←div_eq_inv_mul,div_eq_one_iff_eq (pow_ne_zero 2 hl.ne'),←hr2]
    exact (sq_eq_sq₀ hr.le hl.le).trans eq_comm
  rw [hrl]
  constructor
  · intro he
    have hh:upperFamily r p.1=p.2:=by simpa only [←he] using (upperParameter_spec hp).2
    rw [upperFamily_at_seam hq] at hh
    have ht:0<p.2:=(U_nonneg _).trans_lt hp
    have hs:0<seamHeight p.1:=by
      by_contra hn
      rw [max_eq_right (le_of_not_gt hn)] at hh
      linarith
    rwa [max_eq_left hs.le] at hh
  · intro he
    exact upperParameter_unique hp hr (by rw [upperFamily_at_seam hq,he,max_eq_left ((U_nonneg _).trans hp.le)])

lemma upperFlux_bulk {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)≠1) :
    bulkExpression upperFlux p≤0 := by
  rw [bulkExpression_congr (upperFlux_eventually_eq hp hq)]
  exact upperCalibration_bulk hp hq

lemma upperFlux_bulk_off_seam {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:0<Cylindrical.radiusSq axis p.1) (hs:seamHeight p.1≠p.2) :
    bulkExpression upperFlux p≤0 :=
  upperFlux_bulk hp (fun h=>hs ((normalized_radius_eq_one_iff hp hq).mp h))

lemma exteriorFlux_eventually_eq {p:Space 7×ℝ} (hp:U p.1<p.2)
    (hq:0<Cylindrical.radiusSq axis p.1) (hs:p.2<seamHeight p.1) :
    exteriorFlux =ᶠ[𝓝 p] upperFlux := by
  have hqn:∀ᶠ z:Space 7×ℝ in 𝓝 p,0<Cylindrical.radiusSq axis z.1:=
    ((Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt.comp continuous_fst.continuousAt).eventually (lt_mem_nhds hq)
  have hsn:∀ᶠ z:Space 7×ℝ in 𝓝 p,z.2<seamHeight z.1:=
    continuous_snd.continuousAt.eventually_lt ((seamHeight_contDiffAt hq).continuousAt.comp continuous_fst.continuousAt) hs
  filter_upwards [above_U_isOpen.mem_nhds hp,hqn,hsn] with z hz hzq hzs
  exact (upperFlux_eq_exterior hz hzq hzs).symm
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.FluxSeam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace Bernoulli.DeSilvaJerison
lemma outerSigned_dilation_formula {x:Space 7} {l:ℝ} (hl:0<l)
    (hq:0<Cylindrical.radiusSq axis x) :
    κ*l*outerSigned (l⁻¹ • x)=κ*(Zsigned x+capAmplitude*l^3*KSup x) := by
  rw [outerSigned,Zsigned_smul x (inv_pos.mpr hl),KSup_smul hq (inv_pos.mpr hl)]
  norm_num only [zpow_neg,zpow_ofNat,inv_inv]
  field_simp

lemma outerSigned_dilation_gradient {x:Space 7} {l:ℝ} (hl:0<l)
    (hq:0<Cylindrical.radiusSq axis x) :
    κ • gradient outerSigned (l⁻¹ • x)=κ • gradient Zsigned x+
      (κ*capAmplitude*l^3) • gradient KSup x := by
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hq
  have hqy:0<Cylindrical.radiusSq axis (l⁻¹ • x):=by rw [Cylindrical.radiusSq_smul]; positivity
  obtain ⟨hyn,hya⟩:=radiusSq_pos_data hqy
  have hdz:DifferentiableAt ℝ Zsigned x:=(signed_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  have hdk:DifferentiableAt ℝ KSup x:=(KSup_contDiffAt (n:=1) hx ha).differentiableAt (by norm_num)
  have he:(fun y=>κ*l*outerSigned (l⁻¹ • y)) =ᶠ[𝓝 x]
      (fun y=>κ*(Zsigned y+capAmplitude*l^3*KSup y)):=by
    filter_upwards [((Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt).eventually (lt_mem_nhds hq)] with y hy
    exact outerSigned_dilation_formula hl hy
  rw [←gradient_dilation hl.ne' ((outerSigned_contDiffAt (n:=1) hyn hya).differentiableAt (by simp)),gradient,he.fderiv_eq]
  change gradient (fun y=>κ*(Zsigned y+capAmplitude*l^3*KSup y)) x=_
  have hdf:DifferentiableAt ℝ (fun y=>Zsigned y+capAmplitude*l^3*KSup y) x:=
    hdz.add (hdk.const_mul (capAmplitude*l^3))
  rw [gradient_const_mul κ hdf,gradient_add' hdz (hdk.const_mul (capAmplitude*l^3)),
    gradient_const_mul (capAmplitude*l^3) hdk,smul_add,smul_smul]
  congr 2
  ring

lemma seamHeight_signed_dilation {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    seamHeight x=κ*Real.sqrt (Cylindrical.radiusSq axis x)*
      outerSigned ((Real.sqrt (Cylindrical.radiusSq axis x))⁻¹ • x) := by
  rw [outerSigned_at_seam (normalized_radius_seam hq),seamHeight_formula,Cylindrical.axis_smul,div_eq_mul_inv,mul_comm (Cylindrical.axis axis x)]

lemma exteriorFlux_at_seam {x:Space 7} (hq:0<Cylindrical.radiusSq axis x) :
    exteriorFlux (x,seamHeight x)=
      κ • gradient outerSigned ((Real.sqrt (Cylindrical.radiusSq axis x))⁻¹ • x) := by
  let l:=Real.sqrt (Cylindrical.radiusSq axis x)
  have hl:0<l:=Real.sqrt_pos.mpr hq
  obtain ⟨hx,ha⟩:=radiusSq_pos_data hq
  have he:seamHeight x=κ*(Zsigned x+capAmplitude*l^3*KSup x):=by
    rw [seamHeight_signed_dilation hq]
    exact outerSigned_dilation_formula hl hq
  rw [outerSigned_dilation_gradient hl hq]
  unfold exteriorFlux
  dsimp only
  rw [he]
  congr 1
  congr 1
  apply (div_eq_iff (KSup_pos hx ha).ne').mpr
  ring

lemma upperParameter_at_seam {x:Space 7} (hq:0<Cylindrical.radiusSq axis x)
    (hp:U x<seamHeight x) : upperParameter x (seamHeight x)=Real.sqrt (Cylindrical.radiusSq axis x) := by
  exact (upperParameter_unique hp (Real.sqrt_pos.mpr hq)
    ((upperFamily_at_seam hq).trans (max_eq_left ((U_nonneg x).trans hp.le))))

lemma upperFlux_at_seam {x:Space 7} (hq:0<Cylindrical.radiusSq axis x)
    (hp:U x<seamHeight x) : upperFlux (x,seamHeight x)=
      κ • gradient smoothCap ((Real.sqrt (Cylindrical.radiusSq axis x))⁻¹ • x) := by
  rw [upperFlux,ite_eq_left hp,upperParameter_at_seam hq hp,
    ite_eq_left (normalized_radius_seam hq).le]

theorem upperFlux_seam_jump {x:Space 7} (hq:0<Cylindrical.radiusSq axis x)
    (hp:U x<seamHeight x) :
    ‖upperFlux (x,seamHeight x)‖^2-‖exteriorFlux (x,seamHeight x)‖^2-
      2*inner ℝ (upperFlux (x,seamHeight x)-exteriorFlux (x,seamHeight x)) (gradient seamHeight x)≤0 := by
  rw [upperFlux_at_seam hq hp,exteriorFlux_at_seam hq,gradient_seamHeight hq]
  apply upperCalibration_seam (normalized_radius_seam hq)
  have hh:0<seamHeight x:=(U_nonneg x).trans_lt hp
  rw [seamHeight_signed_dilation hq,←upper_seam_agreement (normalized_radius_seam hq)] at hh
  exact pos_of_mul_pos_right hh (mul_nonneg κ_pos.le (Real.sqrt_nonneg _))
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.ClampedGraphBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma gradient_eq_of_order_contact {u v:E→ℝ} {x:E}
    (hu:DifferentiableAt ℝ u x) (hv:DifferentiableAt ℝ v x)
    (hle:∀y,u y≤v y) (he:u x=v x) : gradient u x=gradient v x := by
  have hm:IsLocalMin (fun y=>v y-u y) x:=by
    filter_upwards [] with y
    change v x-u x≤v y-u y
    rw [←he,sub_self]
    exact sub_nonneg.mpr (hle y)
  have hh:=hm.hasFDerivAt_eq_zero (hv.hasFDerivAt.sub hu.hasFDerivAt)
  exact congrArg ((toDual ℝ E).symm) (sub_eq_zero.mp hh).symm

lemma graph_divergence_zero_contact {A:E×ℝ→E} (hA:ContDiff ℝ 1 A)
    {u v:E→ℝ} {x:E} (hu:DifferentiableAt ℝ u x) (hv:DifferentiableAt ℝ v x)
    (hle:∀y,u y≤v y) (he:u x=v x) : divergence (graphPotential A u v) x=0 := by
  rw [graph_potential_identity hA hu hv,he,gradient_eq_of_order_contact hu hv hle he]
  simp

lemma graph_potential_bulk_bound_open {A:E×ℝ→E} (hA:ContDiff ℝ 1 A)
    {u v:E→ℝ} {x:E} (hu:DifferentiableAt ℝ u x) (hv:DifferentiableAt ℝ v x)
    (huv:u x≤v x)
    (hbulk:∀s∈Ioo (u x) (v x),divergence (fun y:E=>A (y,s)) x+
      inner ℝ (A (x,s)) (deriv (fun t:ℝ=>A (x,t)) s)≤0) :
    divergence (graphPotential A u v) x≤‖gradient v x‖^2+
      ‖A (x,u x)‖^2-2*inner ℝ (A (x,u x)) (gradient u x) := by
  have hi:=integrated_bulk_open hA x huv hbulk
  have hs:0≤‖gradient v x-A (x,v x)‖^2:=sq_nonneg _
  have he:inner ℝ (gradient v x) (A (x,v x))=inner ℝ (A (x,v x)) (gradient v x):=real_inner_comm _ _
  rw [norm_sub_sq_real,he] at hs
  rw [graph_potential_identity hA hu hv]
  linarith

/-- The clamped primitive only needs a jump condition when the seam lies
strictly between the endpoint graphs. On contact sets the two gradients
agree, so the spurious branch cancels exactly. -/
lemma split_graph_bound_open {A B:E×ℝ→E} (hA:ContDiff ℝ 1 A) (hB:ContDiff ℝ 1 B)
    {u w v:E→ℝ} {x:E} (hu:DifferentiableAt ℝ u x) (hw:DifferentiableAt ℝ w x)
    (hv:DifferentiableAt ℝ v x) (huw:∀y,u y≤w y) (hwv:∀y,w y≤v y)
    (hbulkA:∀s∈Ioo (u x) (w x),divergence (fun y:E=>A (y,s)) x+
      inner ℝ (A (x,s)) (deriv (fun t:ℝ=>A (x,t)) s)≤0)
    (hbulkB:∀s∈Ioo (w x) (v x),divergence (fun y:E=>B (y,s)) x+
      inner ℝ (B (x,s)) (deriv (fun t:ℝ=>B (x,t)) s)≤0)
    (hjump:u x<w x → w x<v x → ‖B (x,w x)‖^2-‖A (x,w x)‖^2-
      2*inner ℝ (B (x,w x)-A (x,w x)) (gradient w x)≤0) :
    divergence (splitGraphPotential A B u w v) x≤‖gradient v x‖^2+
      ‖(if u x=w x then B else A) (x,u x)‖^2-
        2*inner ℝ ((if u x=w x then B else A) (x,u x)) (gradient u x) := by
  have hd:divergence (splitGraphPotential A B u w v) x=
      divergence (graphPotential A u w) x+divergence (graphPotential B w v) x:=
    divergence_add (graphPotential_differentiableAt hA hu hw) (graphPotential_differentiableAt hB hw hv)
  by_cases heu:u x=w x
  · rw [ite_eq_left heu,hd,graph_divergence_zero_contact hA hu hw huw heu,zero_add]
    have heG:=gradient_eq_of_order_contact hu hw huw heu
    simpa only [←heu,←heG] using graph_potential_bulk_bound_open hB hw hv (hwv x) hbulkB
  · rw [ite_eq_right heu]
    by_cases hev:w x=v x
    · rw [hd,graph_divergence_zero_contact hB hw hv hwv hev,add_zero]
      have heG:=gradient_eq_of_order_contact hw hv hwv hev
      simpa only [heG] using graph_potential_bulk_bound_open hA hu hw (huw x) hbulkA
    · have hiA:=integrated_bulk_open hA x (huw x) hbulkA
      have hiB:=integrated_bulk_open hB x (hwv x) hbulkB
      have hj:=hjump (lt_of_le_of_ne (huw x) heu) (lt_of_le_of_ne (hwv x) hev)
      rw [inner_sub_left] at hj
      have hs:0≤‖gradient v x-B (x,v x)‖^2:=sq_nonneg _
      have he:inner ℝ (gradient v x) (B (x,v x))=inner ℝ (B (x,v x)) (gradient v x):=real_inner_comm _ _
      rw [norm_sub_sq_real,he] at hs
      rw [hd,graph_potential_identity hA hu hw,graph_potential_identity hB hw hv]
      linarith
end Bernoulli.Foliation

end
end

end OAI
end

section
-- module Solutions.OAIQW_BernoulliCone.PrimitiveBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.DeSilvaJerison
open Foliation

lemma cap_extension_eventually_eq {K:Set (Space 7×ℝ)} {B:Space 7×ℝ→Space 7}
    (hB:∀p∈K,seamHeight p.1≤p.2 → B p=upperFlux p)
    {p:Space 7×ℝ} (hp:p∈interior K) (hq:0<Cylindrical.radiusSq axis p.1)
    (hs:seamHeight p.1<p.2) : B =ᶠ[𝓝 p] upperFlux := by
  have hn:∀ᶠ z:Space 7×ℝ in 𝓝 p,seamHeight z.1<z.2:=
    ((seamHeight_contDiffAt hq).continuousAt.comp continuous_fst.continuousAt).eventually_lt
      continuous_snd.continuousAt hs
  filter_upwards [mem_interior_iff_mem_nhds.mp hp,hn] with z hz hzs
  exact hB z hz hzs.le

lemma clamped_interior_seam {u v:Space 7→ℝ} {x:Space 7}
    (huw:u x<clampedHeight u seamHeight v x)
    (hwv:clampedHeight u seamHeight v x<v x) :
    u x<seamHeight x ∧ seamHeight x<v x ∧ clampedHeight u seamHeight v x=seamHeight x := by
  have hs:seamHeight x<v x:=by
    by_contra hn
    have he:clampedHeight u seamHeight v x=max (u x) (v x):=by
      rw [clampedHeight,min_eq_left (not_lt.mp hn)]
    have hh:=le_max_right (u x) (v x)
    rw [←he] at hh
    exact not_lt.mpr hh hwv
  have he:clampedHeight u seamHeight v x=max (u x) (seamHeight x):=by
    rw [clampedHeight,min_eq_right hs.le]
  have hu:u x<seamHeight x:=by
    rw [he] at huw
    exact (lt_max_iff.mp huw).resolve_left (lt_irrefl _)
  exact ⟨hu,hs,by rw [he,max_eq_right hu.le]⟩

lemma clamped_seam_gradient {u v:Space 7→ℝ} {x:Space 7}
    (hu:ContinuousAt u x) (hv:ContinuousAt v x) (hq:0<Cylindrical.radiusSq axis x)
    (huw:u x<clampedHeight u seamHeight v x)
    (hwv:clampedHeight u seamHeight v x<v x) :
    gradient (clampedHeight u seamHeight v) x=gradient seamHeight x := by
  obtain ⟨h1,h2,h3⟩:=clamped_interior_seam huw hwv
  have hc:ContinuousAt seamHeight x:=(seamHeight_contDiffAt hq).continuousAt
  have he:clampedHeight u seamHeight v =ᶠ[𝓝 x] seamHeight:=by
    filter_upwards [hu.eventually_lt hc h1,hc.eventually_lt hv h2] with y hy1 hy2
    rw [clampedHeight,min_eq_right hy2.le,max_eq_right hy1.le]
  unfold gradient
  rw [he.fderiv_eq]

lemma primitive_eq_split_germ {u v:Space 7→ℝ} {x:Space 7}
    (hu:ContinuousAt u x) (hv:ContinuousAt v x) (huv:∀y,u y≤v y)
    {K:Set (Space 7×ℝ)} (hKi:({x}×ˢ Icc (u x) (v x))⊆interior K)
    (hKp:∀p∈K,U p.1<p.2) (hKq:∀p∈K,0<Cylindrical.radiusSq axis p.1)
    {A B:Space 7×ℝ→Space 7} (hA:Continuous A) (hB:Continuous B)
    (hAe:EqOn A exteriorFlux K) (hBe:∀p∈K,seamHeight p.1≤p.2 → B p=upperFlux p) :
    verticalPotential upperFlux u v =ᶠ[𝓝 x]
      splitGraphPotential A B u (clampedHeight u seamHeight v) v := by
  have hn:=eventually_vertical_segment hu hv (huv x) (subset_interior_iff_mem_nhdsSet.mp hKi)
  filter_upwards [hn] with y hy
  apply clamped_integral_identity hA hB (huv y) (upperFlux_intervalIntegrable y)
  · intro t ht hts
    have hp:(y,t)∈K:=hy (huv y) t ⟨ht.1.le,ht.2.le⟩
    rw [hAe hp,upperFlux_eq_exterior (hKp _ hp) (hKq _ hp) hts]
  · intro t ht hst
    have hp:(y,t)∈K:=hy (huv y) t ⟨ht.1.le,ht.2.le⟩
    exact (hBe _ hp hst.le).symm

lemma exterior_extension_bulk {K:Set (Space 7×ℝ)} {A:Space 7×ℝ→Space 7}
    (hAe:EqOn A exteriorFlux K) {p:Space 7×ℝ} (hp:p∈interior K)
    (hu:U p.1<p.2) (hq:0<Cylindrical.radiusSq axis p.1) (hs:p.2<seamHeight p.1) :
    bulkExpression A p≤0 := by
  have hn:∀ᶠ z in 𝓝 p,z∈K:=mem_interior_iff_mem_nhds.mp hp
  have he:A =ᶠ[𝓝 p] exteriorFlux:=hn.mono fun _ hz=>hAe hz
  rw [bulkExpression_congr (he.trans (exteriorFlux_eventually_eq hu hq hs))]
  exact upperFlux_bulk_off_seam hu hq (ne_of_gt hs)

lemma cap_extension_bulk {K:Set (Space 7×ℝ)} {B:Space 7×ℝ→Space 7}
    (hBe:∀p∈K,seamHeight p.1≤p.2 → B p=upperFlux p)
    {p:Space 7×ℝ} (hp:p∈interior K) (hu:U p.1<p.2)
    (hq:0<Cylindrical.radiusSq axis p.1) (hs:seamHeight p.1<p.2) :
    bulkExpression B p≤0 := by
  rw [bulkExpression_congr (cap_extension_eventually_eq hBe hp hq hs)]
  exact upperFlux_bulk_off_seam hu hq hs.ne

lemma clamped_extension_jump {u v:Space 7→ℝ} {x:Space 7}
    (hu:ContinuousAt u x) (hv:ContinuousAt v x) (huU:U x<u x)
    (hq:0<Cylindrical.radiusSq axis x)
    {A B:Space 7×ℝ→Space 7} {K:Set (Space 7×ℝ)}
    (hAe:EqOn A exteriorFlux K) (hBe:∀p∈K,seamHeight p.1≤p.2 → B p=upperFlux p)
    (hp:(x,clampedHeight u seamHeight v x)∈K)
    (h1:u x<clampedHeight u seamHeight v x) (h2:clampedHeight u seamHeight v x<v x) :
    ‖B (x,clampedHeight u seamHeight v x)‖^2-‖A (x,clampedHeight u seamHeight v x)‖^2-
      2*inner ℝ (B (x,clampedHeight u seamHeight v x)-A (x,clampedHeight u seamHeight v x))
        (gradient (clampedHeight u seamHeight v) x)≤0 := by
  obtain ⟨hs1,hs2,hwσ⟩:=clamped_interior_seam h1 h2
  rw [hBe _ hp (by rw [hwσ]),hAe hp,clamped_seam_gradient hu hv hq h1 h2,hwσ]
  exact upperFlux_seam_jump hq (huU.trans hs1)

lemma clamped_extension_bottom {u v:Space 7→ℝ} {x:Space 7}
    (huU:U x<u x) (hq:0<Cylindrical.radiusSq axis x) (hlt:u x<v x)
    {A B:Space 7×ℝ→Space 7} {K:Set (Space 7×ℝ)}
    (hAe:EqOn A exteriorFlux K) (hBe:∀p∈K,seamHeight p.1≤p.2 → B p=upperFlux p)
    (hp:(x,u x)∈K) :
    (if u x=clampedHeight u seamHeight v x then B else A) (x,u x)=upperFlux (x,u x) := by
  by_cases ht:u x=clampedHeight u seamHeight v x
  · rw [ite_eq_left ht]
    apply hBe _ hp
    by_contra hn
    have hsw:u x<clampedHeight u seamHeight v x:=by
      change u x < max (u x) (min (v x) (seamHeight x))
      exact (lt_min hlt (not_le.mp hn)).trans_le (le_max_right _ _)
    exact hsw.ne ht
  · rw [ite_eq_right ht,hAe hp]
    apply (upperFlux_eq_exterior (p:=(x,u x)) huU hq _).symm
    have hh:u x < max (u x) (min (v x) (seamHeight x)):=
      lt_of_le_of_ne (le_clampedHeight u seamHeight v x) ht
    exact ((lt_max_iff.mp hh).resolve_left (lt_irrefl _)).trans_le (min_le_right _ _)

/-- Pointwise differential comparison for the genuine discontinuous upper
flux primitive, away from the null axis and at differentiability points of
its three Lipschitz endpoint graphs. -/
theorem upperFlux_primitive_bound_oai {u v:Space 7→ℝ} {x:Space 7}
    (hu:ContinuousAt u x) (hv:ContinuousAt v x) (huv:∀y,u y≤v y)
    (huU:U x<u x) (hqx:0<Cylindrical.radiusSq axis x)
    (hdu:DifferentiableAt ℝ u x) (hdv:DifferentiableAt ℝ v x)
    (hdw:DifferentiableAt ℝ (clampedHeight u seamHeight v) x) :
    divergence (verticalPotential upperFlux u v) x≤
      if u x<v x then ‖gradient v x‖^2+‖upperFlux (x,u x)‖^2-
        2*inner ℝ (upperFlux (x,u x)) (gradient u x) else 0 := by
  obtain ⟨K,hK,hKi,hKp,hKq⟩:=upperFlux_compact_tube (b:=v x) huU hqx
  obtain ⟨A,B,hA,hB,hAe,hBe⟩:=compact_branch_extensions hK hKp hKq
  have he:=primitive_eq_split_germ hu hv huv hKi hKp hKq hA.continuous hB.continuous hAe hBe
  have hed:divergence (verticalPotential upperFlux u v) x=
      divergence (splitGraphPotential A B u (clampedHeight u seamHeight v) v) x:=by
    unfold divergence; rw [he.fderiv_eq]
  rw [hed]
  let w:=clampedHeight u seamHeight v
  have huw:∀y,u y≤w y:=le_clampedHeight u seamHeight v
  have hwv:∀y,w y≤v y:=fun y=>clampedHeight_le (huv y)
  have hpoint (t:ℝ) (ht:t∈Icc (u x) (v x)):(x,t)∈interior K:=hKi ⟨rfl,ht⟩
  by_cases hlt:u x<v x
  · rw [ite_eq_left hlt]
    have hbA:∀s∈Ioo (u x) (w x),bulkExpression A (x,s)≤0:=by
      intro s hs
      exact exterior_extension_bulk hAe
        (hpoint s ⟨hs.1.le,hs.2.le.trans (hwv x)⟩) (huU.trans hs.1) hqx
        (below_clampedHeight hs.1 hs.2)
    have hbB:∀s∈Ioo (w x) (v x),bulkExpression B (x,s)≤0:=by
      intro s hs
      exact cap_extension_bulk hBe
        (hpoint s ⟨(huw x).trans hs.1.le,hs.2.le⟩)
        (huU.trans_le ((huw x).trans hs.1.le)) hqx (above_clampedHeight hs.1 hs.2)
    have hj:u x<w x → w x<v x → ‖B (x,w x)‖^2-‖A (x,w x)‖^2-
        2*inner ℝ (B (x,w x)-A (x,w x)) (gradient w x)≤0:=
      clamped_extension_jump hu hv huU hqx hAe hBe
        (interior_subset (hpoint (w x) ⟨huw x,hwv x⟩))
    have hbottom:(if u x=w x then B else A) (x,u x)=upperFlux (x,u x):=
      clamped_extension_bottom huU hqx hlt hAe hBe
        (interior_subset (hpoint (u x) ⟨le_rfl,hlt.le⟩))
    have hh:=split_graph_bound_open hA hB hdu hdw hdv huw hwv hbA hbB hj
    rwa [hbottom] at hh
  · rw [ite_eq_right hlt]
    have huvx:u x=v x:=le_antisymm (huv x) (not_lt.mp hlt)
    have hux:u x=w x:=le_antisymm (huw x) (by rw [huvx]; exact hwv x)
    have hwx:w x=v x:=hux.symm.trans huvx
    change divergence (fun y=>graphPotential A u w y+graphPotential B w v y) x≤0
    change DifferentiableAt ℝ w x at hdw
    rw [divergence_add (graphPotential_differentiableAt hA hdu hdw) (graphPotential_differentiableAt hB hdw hdv),
      graph_divergence_zero_contact hA hdu hdw huw hux,graph_divergence_zero_contact hB hdw hdv hwv hwx]
    norm_num
end Bernoulli.DeSilvaJerison

end
end

end OAI
end

theorem solution : type_of% @OAI.Bernoulli.DeSilvaJerison.upperFlux_primitive_bound_oai := @OAI.Bernoulli.DeSilvaJerison.upperFlux_primitive_bound_oai
