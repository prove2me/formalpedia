-- Prove2me | solution 1 for OAI.AffineBernstein.normalized_model_positive_log_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:21:39.413966+00:00
-- url     : https://prove2.me/submissions/23442bf4-112b-4f41-9e20-958c0a6468d6

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_invariant_tube_positive
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_product_fiber_area_bound
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_whole_graph_area_bound
import Theorems.Thm_OAI_AffineBernstein_normalized_model_positive_face_mass

section
-- module Solutions.OAIQ22_AB.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_WeightedDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section WeightedDivergence

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem contDiffAt_dirDeriv {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (v : E) :
    ContDiffAt ℝ ∞ (dirDeriv v f) x :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

end WeightedDivergence

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_DeterminantVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

/-- Expansion in the frozen Euclidean coordinate vectors. -/
theorem sum_coordinateVector {n : ℕ} (v : Space n) :
    (∑ i, (v i) • coordinateVector n i) = v := by
  ext j
  simp [coordinateVector, Pi.single_apply]

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_CapCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

theorem hessian_eq_second {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (i j : Fin n) :
    hessian u x i j =
      fderiv ℝ (fderiv ℝ u) x (coordinateVector n i) (coordinateVector n j) := by
  have hd := ((hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have he := hd.clm_apply (hasFDerivAt_const (coordinateVector n j) x)
  unfold hessian
  rw [he.fderiv]
  simp

theorem second_fderiv_eq_sum {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (v : Space n) :
    fderiv ℝ (fderiv ℝ u) x v v =
    ∑ i, ∑ j, v i * hessian u x i j * v j := by
  calc
    _ = fderiv ℝ (fderiv ℝ u) x (∑ i, v i • coordinateVector n i)
        (∑ j, v j • coordinateVector n j) := by rw [sum_coordinateVector]
    _ = _ := by
      simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hessian_eq_second hu,
        hu.isSymmSndFDerivAt (by simp)
          (coordinateVector n j) (coordinateVector n i)]
      ring

theorem second_fderiv_nonneg {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosSemidef) (v : Space n) :
    0 ≤ fderiv ℝ (fderiv ℝ u) x v v := by
  rw [second_fderiv_eq_sum hu]
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    using hp.dotProduct_mulVec_nonneg (fun i => v i)

theorem second_fderiv_pos {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) {v : Space n} (hv : v ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ u) x v v := by
  rw [second_fderiv_eq_sum hu]
  have hv' : (fun i => v i) ≠ 0 := fun he => hv (by ext i; exact congrFun he i)
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    using hp.dotProduct_mulVec_pos hv'

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ConvexGradientBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- Holder interpolation, with weights rather than reciprocal exponents.
The endpoint masses may be infinite; no hidden integrability premise is used. -/
lemma lintegral_geometric_mean_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {f g : X → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, f x ^ p * g x ^ (1-p) ∂μ) ≤
      (∫⁻ x, f x ∂μ)^p * (∫⁻ x, g x ∂μ)^(1-p) := by
  have hconj : p⁻¹.HolderConjugate (1-p)⁻¹ := by
    apply Real.holderConjugate_iff.mpr
    exact ⟨(one_lt_inv₀ hp).mpr hp1,by simp⟩
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj (hf.pow_const p) (hg.pow_const (1-p))
  have hq : 1-p ≠ 0 := (sub_pos.mpr hp1).ne'
  simpa only [← ENNReal.rpow_mul,mul_inv_cancel₀ hp.ne',mul_inv_cancel₀ hq,
    ENNReal.rpow_one,one_div,inv_inv,Pi.mul_apply] using hh

/-- Real positive densities can be interpolated before or after `ofReal`. -/
lemma lintegral_ofReal_geometric_mean_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {f g : X → ℝ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hfp : ∀ᵐ x ∂μ, 0 ≤ f x) (hgp : ∀ᵐ x ∂μ, 0 ≤ g x) :
    (∫⁻ x, ENNReal.ofReal ((f x)^p * (g x)^(1-p)) ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal (f x) ∂μ)^p *
      (∫⁻ x, ENNReal.ofReal (g x) ∂μ)^(1-p) := by
  convert lintegral_geometric_mean_le μ hp hp1 hf.ennreal_ofReal hg.ennreal_ofReal using 1
  all_goals try with_reducible_and_instances rfl
  apply lintegral_congr_ae
  filter_upwards [hfp,hgp] with x hx hy
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hx _),ENNReal.ofReal_rpow_of_nonneg hx hp.le,
    ENNReal.ofReal_rpow_of_nonneg hy (sub_pos.mpr hp1).le]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GraphPatchArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- The standing positive-Hessian hypothesis implies genuine convexity on
 the original open convex domain; this is not an additional hypothesis. -/
theorem convexOn_of_hessian_posSemidef {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosSemidef) :
    ConvexOn ℝ Ω u := by
  refine ⟨hcv, ?_⟩
  intro x hx y hy a b ha hb hab
  let γ : ℝ → Space n := fun t => x + t • (y - x)
  let d : ℝ → ℝ := fun t => fderiv ℝ u (γ t) (y - x)
  let dd : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ u) (γ t) (y - x) (y - x)
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ Ω :=
    hcv.add_smul_mem hx (by simpa using hy) ht
  have hγ : ContDiff ℝ ∞ γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hγd (t : ℝ) : HasDerivAt γ (y - x) t := by
    simpa [γ] using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have hf : ContinuousOn (u ∘ γ) (Icc (0 : ℝ) 1) :=
    hu.continuousOn.comp hγ.continuous.continuousOn hseg
  have hdf (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) :
      HasDerivWithinAt (u ∘ γ) (d t) (interior (Icc (0 : ℝ) 1)) t :=
    (((hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht)))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t (hγd t)).hasDerivWithinAt
  have hdd (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) :
      HasDerivWithinAt d (dd t) (interior (Icc (0 : ℝ) 1)) t := by
    have hd := (((hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht)))).fderiv_right
      (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
    have he := hd.clm_apply (hasFDerivAt_const (y - x) (γ t))
    have hc := he.comp_hasDerivAt t (hγd t)
    simpa only [d, dd, Function.comp_def, ContinuousLinearMap.comp_zero,
      zero_add, ContinuousLinearMap.flip_apply] using
      hc.hasDerivWithinAt (s := interior (Icc (0 : ℝ) 1))
  have hc : ConvexOn ℝ (Icc (0 : ℝ) 1) (u ∘ γ) :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _) hf hdf hdd
      (fun t ht => second_fderiv_nonneg
        (hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht))))
        (hp _ (hseg t (interior_subset ht))) (y - x))
  have he := hc.2 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) ha hb hab
  have heq : γ b = a • x + b • y := by
    dsimp [γ]
    rw [smul_sub]
    have ha' : a = 1 - b := by linarith
    rw [ha', sub_smul, one_smul]
    abel
  simpa [Function.comp_def, γ, heq, smul_eq_mul] using he

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SupportGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

section CompleteSphericalDependencies
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section SupportGeometry
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- The literal support value, not a freely chosen support coordinate. -/
theorem convex_first_order {W : Set E} {F : E → ℝ} (hF : ConvexOn ℝ W F)
    {x y : E} (hx : x ∈ W) (hy : y ∈ W) (hd : DifferentiableAt ℝ F x) :
    fderiv ℝ F x (y - x) ≤ F y - F x := by
  let γ : ℝ →ᵃ[ℝ] E :=
    { toFun := fun t => x + t • (y - x)
      linear := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (y - x)
      map_vadd' := by intro t s; simp [add_smul]; abel }
  have hc := hF.comp_affineMap γ
  have hdγ : HasDerivAt γ (y - x) 0 := by
    change HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hdx : HasFDerivAt F (fderiv ℝ F x) (γ 0) := by
    simpa [γ] using hd.hasFDerivAt
  have hs := hc.le_slope_of_hasDerivAt (x := 0) (y := 1)
    (by simpa [γ] using hx) (by simpa [γ] using hy) (by norm_num)
    (by simpa [γ] using hdx.comp_hasDerivAt 0 hdγ)
  simpa [slope_def_field, γ] using hs

/- A nonzero linear functional cannot attain its sublevel maximum below the level. -/
theorem sublevel_max_on_level {W : Set E} (hW : IsOpen W) {F : E → ℝ}
    {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) {z : E} (hz : z ∈ W)
    (hzF : F z ≤ 0) (hc : ContinuousAt F z)
    (hmax : IsMaxOn ℓ {y | y ∈ W ∧ F y ≤ 0} z) : F z = 0 := by
  by_contra hn
  have ht : F z < 0 := lt_of_le_of_ne hzF hn
  have hm : IsLocalMax ℓ z := by
    filter_upwards [hW.mem_nhds hz, hc.eventually (eventually_lt_nhds ht)] with y hy hyF
    exact hmax ⟨hy, hyF.le⟩
  exact hℓ (by simpa using hm.fderiv_eq_zero)

/- The support maximum of a compact smooth convex sublevel has a positive
Lagrange multiplier. This includes dimension one without a sphere convention. -/
theorem exists_support_multiplier [CompleteSpace E] {W : Set E} (hW : IsOpen W) {F : E → ℝ}
    (hcv : ConvexOn ℝ W F) (hF : ContDiffOn ℝ ∞ F W)
    {x₀ : E} (hx₀ : x₀ ∈ W) (hneg : F x₀ < 0)
    (hK : IsCompact {y | y ∈ W ∧ F y ≤ 0})
    {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    ∃ z ∈ W, F z = 0 ∧ ∃ lam : ℝ, 0 < lam ∧
      fderiv ℝ F z = lam • ℓ ∧
      (∀ y ∈ W, F y ≤ 0 → ℓ y ≤ ℓ z) ∧
      supportValue {y | y ∈ W ∧ F y ≤ 0} ℓ = ℓ z := by
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn ⟨x₀, hx₀, hneg.le⟩ ℓ.continuous.continuousOn
  have hd := hF.contDiffAt (hW.mem_nhds hz.1)
  have hzF := sublevel_max_on_level hW hℓ hz.1 hz.2 hd.continuousAt hmax
  have he : IsLocalExtrOn ℓ {y | F y = F z} z := by
    apply Or.inr
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hz.1)]
      with y hy hyW
    exact hmax ⟨hyW, by simp [hy, hzF]⟩
  obtain ⟨a, b, hab, heq⟩ := he.exists_multipliers_of_hasStrictFDerivAt_1d
    (hd.hasStrictFDerivAt (by simp)) ℓ.hasStrictFDerivAt
  have ha : a ≠ 0 := by
    intro ha
    have hb : b ≠ 0 := by simpa [ha] using hab
    simp only [ha, zero_smul, zero_add] at heq
    exact hℓ ((smul_eq_zero.mp heq).resolve_left hb)
  let lam := -b / a
  have hder : fderiv ℝ F z = lam • ℓ := by
    ext v
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) heq
    simp only [add_apply, smul_apply, zero_apply, smul_eq_mul] at hh ⊢
    dsimp [lam]
    field_simp
    nlinarith
  have hi := convex_first_order hcv hz.1 hx₀ (hd.differentiableAt (by simp))
  rw [hder, smul_apply, smul_eq_mul, hzF, sub_zero] at hi
  have hlin : ℓ (x₀ - z) ≤ 0 := by
    rw [map_sub, sub_nonpos]
    exact hmax ⟨hx₀, hneg.le⟩
  have hlam : 0 < lam := by
    by_contra ht
    have hh := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt ht) hlin
    linarith
  refine ⟨z, hz.1, hzF, lam, hlam, hder, ?_, ?_⟩
  · intro y hy hyF
    exact hmax ⟨hy, hyF⟩
  · unfold supportValue
    refine csSup_eq_of_forall_le_of_forall_lt_exists_gt (s := ℓ '' {y | y ∈ W ∧ F y ≤ 0}) ?_ ?_ ?_
    · exact ⟨ℓ z, z, hz, rfl⟩
    · rintro v ⟨y, hy, rfl⟩; exact hmax hy
    · intro b hb
      exact ⟨ℓ z, ⟨z, hz, rfl⟩, hb⟩

/- Linearization of the actual support equations `F(y)=0`, `DF(y)=lam*ell`. -/
theorem supportJacobian_injective {d : E →L[ℝ] ℝ}
    {H : E →L[ℝ] (E →L[ℝ] ℝ)} {ℓ : E →L[ℝ] ℝ} {lam : ℝ}
    (hℓ : ℓ ≠ 0) (hlam : lam ≠ 0) (hd : d = lam • ℓ)
    (hH : ∀ v : E, v ≠ 0 → 0 < H v v) :
    Function.Injective (supportJacobian d H ℓ) := by
  apply (injective_iff_map_eq_zero (supportJacobian d H ℓ)).mpr
  rintro ⟨v, a⟩ hv
  change (d v, H v - a • ℓ) = (0, 0) at hv
  have hv1 : d v = 0 := congrArg Prod.fst hv
  have hv2 : H v = a • ℓ := sub_eq_zero.mp (congrArg Prod.snd hv)
  have hlv : ℓ v = 0 := by
    simpa [hd, hlam] using hv1
  have hv0 : v = 0 := by
    by_contra hn
    have hh := hH v hn
    rw [hv2] at hh
    simp [hlv] at hh
  have ha0 : a = 0 := by
    rw [hv0, map_zero] at hv2
    exact (smul_eq_zero.mp hv2.symm).resolve_right hℓ
  simp [hv0, ha0]

theorem supportJacobian_isInvertible [FiniteDimensional ℝ E]
    {d : E →L[ℝ] ℝ} {H : E →L[ℝ] (E →L[ℝ] ℝ)}
    {ℓ : E →L[ℝ] ℝ} {lam : ℝ} (hℓ : ℓ ≠ 0) (hlam : lam ≠ 0)
    (hd : d = lam • ℓ) (hH : ∀ v : E, v ≠ 0 → 0 < H v v) :
    (supportJacobian d H ℓ).IsInvertible := by
  have hi := supportJacobian_injective hℓ hlam hd hH
  have hf : Module.finrank ℝ (E × ℝ) = Module.finrank ℝ (ℝ × (E →L[ℝ] ℝ)) := by
    rw [Module.finrank_prod, Module.finrank_prod,
      ← (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq,
      Subspace.dual_finrank_eq]
    omega
  let e := (supportJacobian d H ℓ).toLinearMap.linearEquivOfInjective hi hf
  refine ⟨e.toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  rfl

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

/- Fiber derivatives of the actual defining function. -/

theorem contDiffAt_fiberGradient {F : S × E → ℝ} {p : S × E}
    (hF : ContDiffAt ℝ ∞ F p) : ContDiffAt ℝ ∞ (fiberGradient F) p := by
  apply ContDiffAt.fderiv (n := ∞) (g := Prod.snd) _ contDiffAt_snd (by simp)
  exact hF.comp (p, p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)

theorem contDiffAt_supportEquations {F : S × E → ℝ} {s : S} {y : E}
    {ℓ : E →L[ℝ] ℝ} {lam : ℝ} (hF : ContDiffAt ℝ ∞ F (s, y)) :
    ContDiffAt ℝ ∞ (supportEquations F) ((s, ℓ), (y, lam)) := by
  have he : ContDiffAt ℝ ∞ (fun q : (S × (E →L[ℝ] ℝ)) × (E × ℝ) =>
      (q.1.1, q.2.1)) ((s, ℓ), (y, lam)) :=
    contDiffAt_fst.fst.prodMk contDiffAt_snd.fst
  have hc1 : ContDiffAt ℝ ∞ (fun q : (S × (E →L[ℝ] ℝ)) × (E × ℝ) =>
      F (q.1.1, q.2.1)) ((s, ℓ), (y, lam)) := hF.comp ((s, ℓ), (y, lam)) he
  have hc2 : ContDiffAt ℝ ∞ (fun q : (S × (E →L[ℝ] ℝ)) × (E × ℝ) =>
      fiberGradient F (q.1.1, q.2.1)) ((s, ℓ), (y, lam)) := by
    have hh := (contDiffAt_fiberGradient (F := F) (p := (s, y)) hF).comp ((s, ℓ), (y, lam)) he
    exact hh
  exact hc1.prodMk (hc2.sub (contDiffAt_snd.snd.smul contDiffAt_fst.snd))

theorem supportEquations_partial {F : S × E → ℝ} {s : S} {y : E}
    {ℓ : E →L[ℝ] ℝ} {lam : ℝ} (hF : ContDiffAt ℝ ∞ F (s, y)) :
    fderiv ℝ (supportEquations F) ((s, ℓ), (y, lam)) ∘L
      ContinuousLinearMap.inr ℝ (S × (E →L[ℝ] ℝ)) (E × ℝ) =
    supportJacobian (fderiv ℝ (fun z => F (s, z)) y)
      (fderiv ℝ (fderiv ℝ (fun z => F (s, z))) y) ℓ := by
  have hfu : ContDiffAt ℝ ∞ (fun z => F (s, z)) y :=
    hF.comp y (contDiffAt_const.prodMk contDiffAt_id)
  have hdu := hfu.differentiableAt (by simp)
  have h2u := (hfu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hp : HasFDerivAt (fun q : E × ℝ => supportEquations F ((s, ℓ), q))
      (supportJacobian (fderiv ℝ (fun z => F (s, z)) y)
        (fderiv ℝ (fderiv ℝ (fun z => F (s, z))) y) ℓ) (y, lam) := by
    exact (hdu.hasFDerivAt.comp (y, lam) (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt).prodMk
      ((h2u.hasFDerivAt.comp (y, lam) (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt).sub
        ((ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt.smul_const ℓ))
  have hi : HasFDerivAt (fun q : E × ℝ => ((s, ℓ), q))
      (ContinuousLinearMap.inr ℝ (S × (E →L[ℝ] ℝ)) (E × ℝ)) (y, lam) := by
    convert (hasFDerivAt_const (s, ℓ) (y, lam)).prodMk (hasFDerivAt_id (y, lam)) using 1 <;>
      ext <;> simp
  exact (((contDiffAt_supportEquations (ℓ := ℓ) (lam := lam) hF).differentiableAt
    (by simp)).hasFDerivAt.comp (y, lam) hi).unique hp

/- A solution of the support equations with positive multiplier is a global,
not merely local, support point. -/
theorem supportValue_of_equations {W : Set E} {F : E → ℝ}
    (hcv : ConvexOn ℝ W F) {z : E} (hz : z ∈ W) (hzF : F z = 0)
    (hd : DifferentiableAt ℝ F z) {ℓ : E →L[ℝ] ℝ} {lam : ℝ}
    (hlam : 0 < lam) (he : fderiv ℝ F z = lam • ℓ) :
    supportValue {y | y ∈ W ∧ F y ≤ 0} ℓ = ℓ z := by
  unfold supportValue
  have hmax (y : E) (hy : y ∈ W ∧ F y ≤ 0) : ℓ y ≤ ℓ z := by
    have hh := convex_first_order hcv hz hy.1 hd
    simp only [he, smul_apply, smul_eq_mul, map_sub, hzF, sub_zero] at hh
    have hh' : lam * (ℓ y - ℓ z) ≤ 0 := by simpa [mul_sub] using hh.trans hy.2
    nlinarith
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt (s := ℓ '' {y | y ∈ W ∧ F y ≤ 0}) ?_ ?_ ?_
  · exact ⟨ℓ z, z, ⟨hz, hzF.le⟩, rfl⟩
  · rintro v ⟨y, hy, rfl⟩; exact hmax y hy
  · intro a ha; exact ⟨ℓ z, ⟨z, ⟨hz, hzF.le⟩, rfl⟩, ha⟩

/- Smooth dependence of the literal support value on base and conormal.
The IFT is applied to the actual defining function and its actual Hessian. -/
theorem contDiffAt_supportValue_fibers [FiniteDimensional ℝ E] [CompleteSpace S]
    {B : Set S} (hB : IsOpen B) {W : Set (S × E)} (hW : IsOpen W)
    {F : S × E → ℝ} (hF : ContDiffOn ℝ ∞ F W)
    (hcv : ∀ s ∈ B, ConvexOn ℝ {y | (s, y) ∈ W} (fun y => F (s, y)))
    {s : S} (hs : s ∈ B) {x₀ : E} (hx₀ : (s, x₀) ∈ W) (hneg : F (s, x₀) < 0)
    (hK : IsCompact {y | (s, y) ∈ W ∧ F (s, y) ≤ 0})
    (hH : ∀ y, (s, y) ∈ W → F (s, y) = 0 → ∀ v : E, v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun z => F (s, z))) y v v)
    {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : S × (E →L[ℝ] ℝ) =>
      supportValue {y | (q.1, y) ∈ W ∧ F (q.1, y) ≤ 0} q.2) (s, ℓ) := by
  have hWs : IsOpen {y | (s, y) ∈ W} := hW.preimage (by fun_prop)
  have hFs : ContDiffOn ℝ ∞ (fun y => F (s, y)) {y | (s, y) ∈ W} :=
    hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h)
  obtain ⟨z, hz, hzF, lam, hlam, hder, -, hsup⟩ :=
    exists_support_multiplier hWs (hcv s hs) hFs hx₀ hneg hK hℓ
  have hcF := hF.contDiffAt (hW.mem_nhds hz)
  have hg := contDiffAt_supportEquations (ℓ := ℓ) (lam := lam) hcF
  have hinv : (fderiv ℝ (supportEquations F) ((s, ℓ), (z, lam)) ∘L
      ContinuousLinearMap.inr ℝ (S × (E →L[ℝ] ℝ)) (E × ℝ)).IsInvertible := by
    rw [supportEquations_partial hcF]
    exact supportJacobian_isInvertible hℓ hlam.ne' hder (hH z hz hzF)
  let ψ := hg.implicitFunction (by simp) hinv
  have hψ : ContDiffAt ℝ ∞ ψ (s, ℓ) := hg.contDiffAt_implicitFunction (by simp) hinv
  have hψ₀ : ψ (s, ℓ) = (z, lam) := hg.implicitFunction_apply_self (by simp) hinv
  have hge : ∀ᶠ q in 𝓝 (s, ℓ), supportEquations F (q, ψ q) = 0 := by
    have hh := hg.eventually_apply_implicitFunction (by simp) hinv
    have hg0 : supportEquations F ((s, ℓ), (z, lam)) = 0 := by
      simp [supportEquations, fiberGradient, hzF, hder]
    simpa only [hg0, ψ] using hh
  have hnearW : ∀ᶠ q in 𝓝 (s, ℓ), (q.1, (ψ q).1) ∈ W := by
    apply (continuousAt_fst.prodMk hψ.continuousAt.fst).eventually
      (hW.mem_nhds (show ((s, ℓ).1, (ψ (s, ℓ)).1) ∈ W by simpa [hψ₀] using hz))
  have hnearL : ∀ᶠ q in 𝓝 (s, ℓ), 0 < (ψ q).2 := by
    exact hψ.continuousAt.snd.eventually (eventually_gt_nhds (by simpa [hψ₀] using hlam))
  have hnearB : ∀ᶠ q in 𝓝 (s, ℓ), q.1 ∈ B :=
    continuousAt_fst.eventually (hB.mem_nhds hs)
  have heq : (fun q : S × (E →L[ℝ] ℝ) =>
      supportValue {y | (q.1, y) ∈ W ∧ F (q.1, y) ≤ 0} q.2) =ᶠ[𝓝 (s, ℓ)]
      (fun q => q.2 ((ψ q).1)) := by
    filter_upwards [hge, hnearW, hnearL, hnearB] with q hq hqW hqL hqB
    have hzero : F (q.1, (ψ q).1) = 0 := congrArg Prod.fst hq
    have hgrad : fiberGradient F (q.1, (ψ q).1) = (ψ q).2 • q.2 :=
      sub_eq_zero.mp (congrArg Prod.snd hq)
    apply supportValue_of_equations (hcv q.1 hqB) hqW hzero _ hqL hgrad
    exact ((hF.contDiffAt (hW.mem_nhds hqW)).comp _
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  exact (contDiffAt_snd.clm_apply hψ.fst).congr_of_eventuallyEq heq

/- Finiteness of the literal support value on a compact fiber. -/
theorem le_supportValue {K : Set E} (hK : IsCompact K) {z : E} (hz : z ∈ K)
    (ℓ : E →L[ℝ] ℝ) : ℓ z ≤ supportValue K ℓ := by
  exact le_csSup (hK.image ℓ.continuous).bddAbove ⟨z, hz, rfl⟩

/- The envelope identity recovers the Gauss parametrization from the literal
support function; no choice of a surrogate support coordinate is involved. -/

theorem supportValue_pos [FiniteDimensional ℝ E] {K : Set E} (hK : IsCompact K)
    (hzero : (0 : E) ∈ interior K) {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    0 < supportValue K ℓ := by
  have hex : ∃ v : E, ℓ v ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hℓ
    ext v
    exact hn v
  obtain ⟨v, hv⟩ := hex
  let w := (ℓ v) • v
  have hw : 0 < ℓ w := by simp only [w, map_smul, smul_eq_mul]; exact mul_self_pos.mpr hv
  have hw0 : w ≠ 0 := by intro hh; simp [hh] at hw
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzero)
  let t := r / (2 * ‖w‖)
  have ht : 0 < t := div_pos hr (by positivity)
  have htw : t • w ∈ K := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    have hh : r / (2 * ‖w‖) * ‖w‖ = r / 2 := by field_simp
    rw [hh]
    linarith
  have hp : 0 < ℓ (t • w) := by simpa using mul_pos ht hw
  exact hp.trans_le (le_supportValue hK htw ℓ)

end SupportGeometry

/- Coordinate entries coincide with the actual second Fréchet differential. -/
/- The standing positive-Hessian hypothesis implies genuine convexity on
 the original open convex domain; this is not an additional hypothesis. -/

end CompleteSphericalDependencies

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AffineSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- A genuine affine slice of the original epigraph, in arbitrary transverse
coordinates. -/
theorem affineEpigraphFiber_no_vertical {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {x : Space n} {z : ℝ} {A : E →L[ℝ] Space n}
    {b : E →L[ℝ] ℝ} (hK : IsCompact (affineEpigraphFiber Ω u x z A b))
    (hne : (affineEpigraphFiber Ω u x z A b).Nonempty)
    {v : E} (hv : A v = 0) : b v = 0 := by
  by_contra hb
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨M, hM⟩ := (hK.image b.continuous).bddAbove
  let r := max M (u (x + A y₀) - z) + 1
  let t := (r - b y₀) / b v
  have hbase : x + A (y₀ + t • v) = x + A y₀ := by simp [hv]
  have hheight : b (y₀ + t • v) = r := by
    simp only [map_add, map_smul, smul_eq_mul, t]
    field_simp
    ring
  have hy : y₀ + t • v ∈ affineEpigraphFiber Ω u x z A b := by
    refine ⟨by rw [hbase]; exact hy₀.1, ?_⟩
    rw [hbase, hheight]
    have hh := le_max_right M (u (x + A y₀) - z)
    dsimp [r]
    linarith
  have hh := hM (show b (y₀ + t • v) ∈ b '' affineEpigraphFiber Ω u x z A b from
    ⟨_, hy, rfl⟩)
  rw [hheight] at hh
  have hh' := le_max_left M (u (x + A y₀) - z)
  dsimp [r] at hh
  linarith

/- For an affine coordinate isomorphism compact fibers force injectivity of
its horizontal linear part. -/
theorem affineEpigraphFiber_injective {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {x : Space n} {z : ℝ} {A : E →L[ℝ] Space n}
    {b : E →L[ℝ] ℝ} (hK : IsCompact (affineEpigraphFiber Ω u x z A b))
    (hne : (affineEpigraphFiber Ω u x z A b).Nonempty)
    (hi : Function.Injective (fun y => (A y, b y))) : Function.Injective A := by
  intro v w hvw
  have hav : A (v - w) = 0 := by simpa [map_sub] using sub_eq_zero.mpr hvw
  have hb := affineEpigraphFiber_no_vertical hK hne hav
  have hbw : b v = b w := sub_eq_zero.mp (by simpa [map_sub] using hb)
  exact hi (Prod.ext hvw hbw)

/- Chain rule for the actual second differential of an affine epigraph slice. -/
theorem affineSlice_second {n : ℕ} {u : Space n → ℝ} {x : Space n} {z : ℝ}
    {A : E →L[ℝ] Space n} {b : E →L[ℝ] ℝ} {y : E}
    (hu : ContDiffAt ℝ ∞ u (x + A y)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun q => u (x + A q) - (z + b q))) y v w =
      fderiv ℝ (fderiv ℝ u) (x + A y) (A v) (A w) := by
  have he : fderiv ℝ (fun q => u (x + A q) - (z + b q)) =ᶠ[𝓝 y]
      (fun q => (fderiv ℝ u (x + A q)).comp A - b) := by
    have hne : ∀ᶠ q in 𝓝 y, DifferentiableAt ℝ u (x + A q) := by
      apply (continuous_const.add A.continuous).continuousAt.eventually
      have hh : ∀ᶠ p in 𝓝 (x + A y), ContDiffAt ℝ 1 u p :=
        (hu.of_le (by simp)).eventually (by simp)
      exact hh.mono (fun p hp => hp.differentiableAt (by simp))
    filter_upwards [hne] with q hq
    exact ((hq.hasFDerivAt.comp q (A.hasFDerivAt.const_add x)).sub
      (b.hasFDerivAt.const_add z)).fderiv
  rw [he.fderiv_eq]
  have hd := ((hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hc := (hd.comp y (A.hasFDerivAt.const_add x)).clm_comp (hasFDerivAt_const A y)
  have heq := (hc.sub_const b).fderiv
  simp only [Function.comp_def] at heq
  rw [heq]
  simp

/- An interior point of a convex sublevel is a strict sublevel point whenever
its actual Hessian is positive definite. -/
theorem sublevel_interior_strict [Nontrivial E] {W : Set E} {F : E → ℝ}
    (hcv : ConvexOn ℝ W F) {z : E}
    (hz : z ∈ interior {y | y ∈ W ∧ F y ≤ 0})
    (hd : DifferentiableAt ℝ F z)
    (hH : ∀ v : E, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ F) z v v) : F z < 0 := by
  have hzK := interior_subset hz
  by_contra hn
  have hz0 : F z = 0 := le_antisymm hzK.2 (le_of_not_gt hn)
  have hnK : {y | y ∈ W ∧ F y ≤ 0} ∈ 𝓝 z := mem_interior_iff_mem_nhds.mp hz
  have hm : IsLocalMax F z := by
    filter_upwards [hnK] with y hy
    simpa [hz0] using hy.2
  have hdz := hm.fderiv_eq_zero
  have he : F =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnK] with y hy
    have hh := convex_first_order hcv hzK.1 hy.1 hd
    simp only [hdz, zero_apply, hz0, sub_zero] at hh
    exact le_antisymm hy.2 hh
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hh := hH v hv
  rw [he.fderiv.fderiv_eq] at hh
  simp at hh

/- Convexity survives the actual affine slice and subtraction of its height. -/
theorem convexOn_affineSlice {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hcv : ConvexOn ℝ Ω u) (x : Space n) (z : ℝ)
    (A : E →L[ℝ] Space n) (b : E →L[ℝ] ℝ) :
    ConvexOn ℝ {y | x + A y ∈ Ω} (fun y => u (x + A y) - (z + b y)) := by
  let g : E →ᵃ[ℝ] Space n :=
    { toFun := fun y => x + A y
      linear := A.toLinearMap
      map_vadd' := by
        intro v p
        change x + A (p + v) = A p + (x + A v)
        rw [map_add]
        abel }
  have hc := hcv.comp_affineMap g
  have hb := (b.toLinearMap.concaveOn hc.1).add_const z
  have hh := hc.sub hb
  change ConvexOn ℝ {y | x + A y ∈ Ω} (fun y => u (x + A y) - (b y + z)) at hh
  simpa only [add_comm (b _) z] using hh

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

/- The literal inverse image of the original epigraph under affine coordinates. -/

theorem affine_coordinates_split {n : ℕ} (a : Space n × ℝ)
    (L : (S × E) ≃L[ℝ] (Space n × ℝ)) (s : S) (y : E) :
    a + L (s, y) = ((a + L (s, 0)).1 + affineFiberHorizontal L y,
      (a + L (s, 0)).2 + affineFiberHeight L y) := by
  have hh : L (s, y) = L (s, 0) + L (0, y) := by rw [← map_add]; simp
  rw [hh]
  ext <;> simp [affineFiberHorizontal, affineFiberHeight, add_assoc]

theorem affineEpigraphPullback_fiber {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ)) (s : S) :
    {y | (s, y) ∈ affineEpigraphPullback Ω u a L} =
      affineEpigraphFiber Ω u (a + L (s, 0)).1 (a + L (s, 0)).2
        (affineFiberHorizontal L) (affineFiberHeight L) := by
  ext y
  change ((a + L (s, y)).1 ∈ Ω ∧ u (a + L (s, y)).1 ≤ (a + L (s, y)).2) ↔ _
  rw [affine_coordinates_split a L s y]
  rfl

theorem affineFiberHorizontal_injective {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {a : Space n × ℝ} {L : (S × E) ≃L[ℝ] (Space n × ℝ)} {s : S}
    (hK : IsCompact {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    (hne : {y | (s, y) ∈ affineEpigraphPullback Ω u a L}.Nonempty) :
    Function.Injective (affineFiberHorizontal L) := by
  rw [affineEpigraphPullback_fiber] at hK hne
  apply affineEpigraphFiber_injective hK hne
  intro v w hvw
  have hh : L (0, v) = L (0, w) := hvw
  exact congrArg Prod.snd (L.injective hh)

variable [CompleteSpace S]

/- The principal support-coordinate regularity assertion in tubes.tex:39–60,
for actual affine images of the standing epigraph, not abstract smooth bodies.
The transverse dimension is nonzero, as in the manuscript (m=n+1-k≥1). -/
theorem affineEpigraph_support_smooth [FiniteDimensional ℝ E] [Nontrivial E]
    {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ B) {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : S × (E →L[ℝ] ℝ) =>
      supportValue {y | (q.1, y) ∈ affineEpigraphPullback Ω u a L} q.2) (s, ℓ) ∧
    0 < supportValue {y | (s, y) ∈ affineEpigraphPullback Ω u a L} ℓ := by
  let W : Set (S × E) := {p | (a + L p).1 ∈ Ω}
  let F : S × E → ℝ := fun p => u (a + L p).1 - (a + L p).2
  have hbase : ContDiff ℝ ∞ (fun p : S × E => (a + L p).1) :=
    (contDiff_const.add L.contDiff).fst
  have hheight : ContDiff ℝ ∞ (fun p : S × E => (a + L p).2) :=
    (contDiff_const.add L.contDiff).snd
  have hW : IsOpen W := hΩ.preimage hbase.continuous
  have hF : ContDiffOn ℝ ∞ F W :=
    (hu.comp hbase.contDiffOn (fun _ h => h)).sub hheight.contDiffOn
  have hFu : ConvexOn ℝ Ω u :=
    convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hFeq (r : S) : (fun q => F (r, q)) = (fun q =>
      u ((a + L (r, 0)).1 + affineFiberHorizontal L q) -
        ((a + L (r, 0)).2 + affineFiberHeight L q)) := by
    funext q
    change u (a + L (r, q)).1 - (a + L (r, q)).2 = _
    rw [affine_coordinates_split a L r q]
  have hWeq (r : S) : {y | (r, y) ∈ W} =
      {y | (a + L (r, 0)).1 + affineFiberHorizontal L y ∈ Ω} := by
    ext y
    change (a + L (r, y)).1 ∈ Ω ↔ _
    rw [affine_coordinates_split a L r y]
    rfl
  have hcvF (r : S) : ConvexOn ℝ {y | (r, y) ∈ W} (fun y => F (r, y)) := by
    rw [hFeq, hWeq]
    exact convexOn_affineSlice hFu (a + L (r, 0)).1 (a + L (r, 0)).2
      (affineFiberHorizontal L) (affineFiberHeight L)
  have hKeq (r : S) : {y | (r, y) ∈ W ∧ F (r, y) ≤ 0} =
      {y | (r, y) ∈ affineEpigraphPullback Ω u a L} := by
    ext y
    simp only [W, F, affineEpigraphPullback, mem_ofPred_eq, sub_nonpos]
  have hK' : IsCompact {y | (s, y) ∈ W ∧ F (s, y) ≤ 0} := by rw [hKeq]; exact hK s hs
  have hzero' : (0 : E) ∈ interior {y | (s, y) ∈ W ∧ F (s, y) ≤ 0} := by
    rw [hKeq]; exact hzero s hs
  have hA : Function.Injective (affineFiberHorizontal L) :=
    affineFiberHorizontal_injective (hK s hs) ⟨0, interior_subset (hzero s hs)⟩
  have hH (y : E) (hy : (s, y) ∈ W) (v : E) (hv : v ≠ 0) :
      0 < fderiv ℝ (fderiv ℝ (fun q => F (s, q))) y v v := by
    have huc := hu.contDiffAt (hΩ.mem_nhds hy)
    have hx : (a + L (s, y)).1 = (a + L (s, 0)).1 + affineFiberHorizontal L y :=
      congrArg Prod.fst (affine_coordinates_split a L s y)
    rw [hFeq, affineSlice_second (by rw [← hx]; exact huc)]
    exact second_fderiv_pos (by rw [← hx]; exact huc)
      (by rw [← hx]; exact hp _ hy)
      (fun hh => hv (hA (by simpa using hh)))
  have hzW : (s, (0 : E)) ∈ W := (interior_subset hzero').1
  have hzF : F (s, 0) < 0 := sublevel_interior_strict (hcvF s) hzero'
    (((hF.contDiffAt (hW.mem_nhds hzW)).comp 0
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)) (hH 0 hzW)
  have hh := contDiffAt_supportValue_fibers hB hW hF (fun r _ => hcvF r)
    hs hzW hzF hK' (fun y hy _ => hH y hy) hℓ
  refine ⟨?_, supportValue_pos (hK s hs) (hzero s hs) hℓ⟩
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext q
  rw [hKeq]

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GaussCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/- The one-homogeneous extension of the literal spherical support function. -/

theorem homogeneousSupport_le {K : Set E} (hK : IsCompact K)
    {z : E} (hz : z ∈ K) (e : E) : inner ℝ e z ≤ homogeneousSupport K e :=
  le_supportValue hK hz (InnerProductSpace.toDual ℝ E e)

theorem homogeneousSupport_eq_of_max {K : Set E} {e z : E}
    (hz : z ∈ K) (hm : IsMaxOn (fun y => inner ℝ e y) K z) :
    homogeneousSupport K e = inner ℝ e z := by
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · exact ⟨inner ℝ e z, z, hz, rfl⟩
  · rintro r ⟨y, hy, rfl⟩; exact hm hy
  · intro r hr; exact ⟨inner ℝ e z, ⟨z, hz, rfl⟩, hr⟩

theorem gaussPoint_eq_of_max {K : Set E} (hK : IsCompact K)
    {e z : E} (hz : z ∈ K) (hm : homogeneousSupport K e = inner ℝ e z)
    (hd : DifferentiableAt ℝ (homogeneousSupport K) e) : gaussPoint K e = z := by
  have hl : IsLocalMin (fun q => homogeneousSupport K q - inner ℝ z q) e := by
    apply Eventually.of_forall
    intro q
    have hh := homogeneousSupport_le hK hz q
    simpa [real_inner_comm z, hm] using sub_nonneg.mpr hh
  have hder := hd.hasFDerivAt.sub (InnerProductSpace.toDual ℝ E z).hasFDerivAt
  have hh : fderiv ℝ (homogeneousSupport K) e - InnerProductSpace.toDual ℝ E z = 0 := by
    rw [← hder.fderiv]
    exact hl.fderiv_eq_zero
  unfold gaussPoint gradient
  rw [sub_eq_zero.mp hh]
  simp

theorem gaussPoint_mem_support {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {e : E} (hd : DifferentiableAt ℝ (homogeneousSupport K) e) :
    gaussPoint K e ∈ K ∧
      homogeneousSupport K e = inner ℝ e (gaussPoint K e) := by
  obtain ⟨z, hz, hm⟩ := hK.exists_isMaxOn hne (InnerProductSpace.toDual ℝ E e).continuous.continuousOn
  have he := homogeneousSupport_eq_of_max hz hm
  rw [gaussPoint_eq_of_max hK hz he hd]
  exact ⟨hz, he⟩

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]

omit [CompleteSpace S] in
theorem contDiffAt_gaussPoint_fibers {K : S → Set E} {s : S} {e : E}
    (hh : ContDiffAt ℝ ∞ (fun p : S × E => homogeneousSupport (K p.1) p.2) (s,e)) :
    ContDiffAt ℝ ∞ (fun p : S × E => gaussPoint (K p.1) p.2) (s,e) := by
  exact ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt).comp
    (s,e) (contDiffAt_fiberGradient hh)

omit [CompleteSpace S] in
theorem contDiffAt_homogeneousSupport_fibers {K : S → Set E} {s : S} {e : E}
    (hh : ContDiffAt ℝ ∞ (fun q : S × (E →L[ℝ] ℝ) => supportValue (K q.1) q.2)
      (s, InnerProductSpace.toDual ℝ E e)) :
    ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) := by
  have hc : ContDiffAt ℝ ∞ (fun q : S × E =>
      (q.1, InnerProductSpace.toDual ℝ E q.2)) (s,e) :=
    contDiffAt_fst.prodMk
      ((InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.contDiff.contDiffAt.comp
        (s,e) contDiffAt_snd)
  have ht := hh.comp (s,e) hc
  exact ht

/- Actual smooth Gauss coordinates of each affine epigraph tube. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualTubeSecond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma homogeneousSupport_fibers_angular {K : S → Set E} {x : S × E}
    (hH : DifferentiableAt ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2) x)
    (w : E) :
    fderiv ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2) x (0,w) =
      inner ℝ (gaussPoint (K x.1) x.2) w := by
  have hd := hH.hasFDerivAt.comp (f := fun y : E => (x.1,y)) x.2
    ((hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2))
  have he : fderiv ℝ (homogeneousSupport (K x.1)) x.2 w =
      fderiv ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2) x (0,w) := by
    change fderiv ℝ ((fun q : S × E => homogeneousSupport (K q.1) q.2) ∘
      (fun y : E => (x.1,y))) x.2 w = _
    rw [hd.fderiv]
    rfl
  rw [← he]
  simp [gaussPoint]

lemma homogeneousSupport_fibers_euler {K : S → Set E} {x : S × E}
    (hK : IsCompact (K x.1)) (hne : (K x.1).Nonempty)
    (hH : DifferentiableAt ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2) x) :
    homogeneousSupport (K x.1) x.2 = inner ℝ x.2 (gaussPoint (K x.1) x.2) := by
  exact (gaussPoint_mem_support hK hne
    (hH.comp (f := fun y : E => (x.1,y)) x.2 (differentiableAt_const x.1 |>.prodMk differentiableAt_id))).2

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualTubeArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma affineEpigraph_support_jets {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ B) {e : E} (he : e ≠ 0) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    ContDiffAt ℝ ∞ H (s,e) ∧ ContDiffAt ℝ ∞ Y (s,e) ∧
      H =ᶠ[𝓝 (s,e)] (fun q => inner ℝ q.2 (Y q)) ∧
      ∀ᶠ q in 𝓝 (s,e), ∀ w : E, fderiv ℝ H q (0,w) = inner ℝ (Y q) w := by
  let K : S → Set E := fun r => {y | (r,y) ∈ affineEpigraphPullback Ω u a L}
  let H : S × E → ℝ := fun q => homogeneousSupport (K q.1) q.2
  let Y : S × E → E := fun q => gaussPoint (K q.1) q.2
  have hℓ : InnerProductSpace.toDual ℝ E e ≠ 0 := by
    intro hz; apply he
    exact (InnerProductSpace.toDual ℝ E).injective (hz.trans (map_zero _).symm)
  have hH : ContDiffAt ℝ ∞ H (s,e) := contDiffAt_homogeneousSupport_fibers
    (K := K) (affineEpigraph_support_smooth hΩ hcv hu hp a L hB hK hzero hs hℓ).1
  refine ⟨hH, contDiffAt_gaussPoint_fibers (K := K) hH, ?_, ?_⟩
  · filter_upwards [(continuous_fst.continuousAt.preimage_mem_nhds (hB.mem_nhds hs)),
      (hH.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)]
      with q hqs hq
    exact homogeneousSupport_fibers_euler (hK q.1 hqs) ⟨0, interior_subset (hzero q.1 hqs)⟩
      (hq.differentiableAt (by norm_num))
  · filter_upwards [(hH.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)]
      with q hq
    exact homogeneousSupport_fibers_angular (hq.differentiableAt (by norm_num))

/- Both matrices in the actual tube area formula are positive definite,
including an empty angular matrix. This is derived from the original graph,
not imposed as an additional curvature assumption. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualBaseMinors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open scoped Matrix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
lemma homogeneousSupport_abs_le_of_radius {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) {e : E} (he : ‖e‖ = 1) {M : ℝ}
    (hM : ∀ y ∈ K, ‖y‖ ≤ M) : |homogeneousSupport K e| ≤ M := by
  obtain ⟨y,hy,hmax⟩ := hK.exists_isMaxOn hne
    (InnerProductSpace.toDual ℝ E e).continuous.continuousOn
  rw [homogeneousSupport_eq_of_max hy hmax]
  exact (abs_real_inner_le_norm e y).trans (by simpa only [he,one_mul] using hM y hy)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatBlockCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma contDiffAt_adjugate_entries {A : E → Matrix ι ι ℝ} {x : E}
    (hA : ContDiffAt ℝ ∞ (fun y i j => A y i j) x) (i j : ι) :
    ContDiffAt ℝ ∞ (fun y => (A y).adjugate i j) x := by
  simp only [Matrix.adjugate_apply]
  change ContDiffAt ℝ ∞ (fun y => continuousDetRows (fun l m => (A y).updateRow j (Pi.single i 1) l m)) x
  apply (continuousDetRows (ι := ι)).contDiff.contDiffAt.comp x
  apply contDiffAt_pi.mpr
  intro l
  by_cases hl : l = j
  · subst l
    simpa only [Matrix.updateRow_self] using (contDiffAt_const (c := (Pi.single i (1 : ℝ) : ι → ℝ)))
  · simp only [Matrix.updateRow_ne hl]
    exact (contDiffAt_pi.mp hA) l

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeInvariantSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
open scoped Matrix
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [CompleteSpace E] [DecidableEq ι] in
lemma contDiffAt_tubeFullRadiusMatrix {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    ContDiffAt ℝ ∞ (fun y i j => tubeFullRadiusMatrix H y b i j) q := by
  have hh := (hH.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  exact contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
    (hh.clm_apply contDiffAt_const).clm_apply contDiffAt_const))

omit [CompleteSpace E] [DecidableEq ι] in
lemma contDiffAt_tubeBaseMatrix {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : Module.Basis ι ℝ S) :
    ContDiffAt ℝ ∞ (fun y i j => tubeBaseMatrix H y b i j) q := by
  have hh := (hH.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  exact contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
    ((hh.clm_apply contDiffAt_const).clm_apply contDiffAt_const).neg))

omit [CompleteSpace E] in
lemma contDiffAt_tubeAngularDensity {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    ContDiffAt ℝ ∞ (fun y => tubeAngularDensity H y b) q := by
  change ContDiffAt ℝ ∞ (fun y => ∑ i, (tubeFullRadiusMatrix H y b).adjugate i i) q
  apply ContDiffAt.sum
  intro i _
  exact contDiffAt_adjugate_entries (contDiffAt_tubeFullRadiusMatrix hH b) i i

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeWeightAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/- Literal invariant tube measure coefficient with respect to `ds dω`. -/

lemma tubeMeasureCoefficient_pos {n : ℕ} {h B Q : ℝ}
    (hh : 0 < h) (hB : 0 < B) (hQ : 0 < Q) :
    0 < tubeMeasureCoefficient n h B Q :=
  mul_pos (Real.rpow_pos_of_pos hh _) (Real.sqrt_pos.2 (mul_pos hB hQ))

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricVariationAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma contDiff_adjugate_entry (i j : ι) :
    ContDiff ℝ ∞ (fun A : ι → ι → ℝ => Matrix.adjugate (Matrix.of A) i j) := by
  simp only [Matrix.adjugate_apply]
  change ContDiff ℝ ∞ (continuousDetRows ∘ fun A : ι → ι → ℝ =>
    fun l m => Matrix.updateRow (Matrix.of A) j (Pi.single i 1) l m)
  apply (continuousDetRows (ι := ι)).contDiff.comp
  apply contDiff_pi.mpr
  intro l
  by_cases hl : l = j
  · subst l
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simp only [Matrix.updateRow_ne hl, Matrix.of_apply]
    fun_prop

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricSmoothness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma contDiffAt_inverse_matrix_entry_param {P ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype ι] [DecidableEq ι]
    {A : P → Matrix ι ι ℝ} {p : P}
    (hA : ContDiffAt ℝ ∞ (fun q i j => A q i j) p) (hd : (A p).det ≠ 0) (i j : ι) :
    ContDiffAt ℝ ∞ (fun q => (A q)⁻¹ i j) p := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  exact (((continuousDetRows (ι := ι)).contDiff.contDiffAt.comp p hA).inv hd).mul
    ((contDiff_adjugate_entry i j).contDiffAt.comp p hA)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_JointTubeMetrics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section JointTubeMetrics
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [CompleteSpace E] in
lemma contDiffAt_tubeBasePair {H f g : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (hf : ContDiffAt ℝ ∞ f q) (hg : ContDiffAt ℝ ∞ g q)
    (b : Module.Basis ι ℝ S) (hd : (tubeBaseMatrix H q b).det ≠ 0) :
    ContDiffAt ℝ ∞ (tubeBasePair H b f g) q := by
  apply hH.mul
  unfold flatInversePair
  exact ContDiffAt.sum fun j _ => ContDiffAt.sum fun i _ =>
    ((contDiffAt_inverse_matrix_entry_param (contDiffAt_tubeBaseMatrix hH b) hd i j).mul
      (contDiffAt_dirDeriv hf _)).mul (contDiffAt_dirDeriv hg _)

omit [CompleteSpace E] in
lemma continuousAt_tubeMeasureDensity {n : ℕ} {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hh : 0 < H q) : ContinuousAt (tubeMeasureDensity n H bS bE) q := by
  unfold tubeMeasureDensity tubeMeasureCoefficient
  apply (hH.continuousAt.rpow_const (Or.inl hh.ne')).mul
  exact (((continuousDetRows (ι := ι)).contDiff.contDiffAt.comp q
    (contDiffAt_tubeBaseMatrix hH bS)).continuousAt.mul
      (contDiffAt_tubeAngularDensity hH bE).continuousAt).sqrt

end JointTubeMetrics

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_MatrixMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma inverseMatrixPair_eq_dot (A : Matrix ι ι ℝ) (x y : ι → ℝ) :
    inverseMatrixPair A x y = y ⬝ᵥ A⁻¹.mulVec x := by
  simp only [inverseMatrixPair,dotProduct,Matrix.mulVec,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma inverseMatrixPair_self_nonneg {A : Matrix ι ι ℝ} (hA : A.PosDef) (x : ι → ℝ) :
    0 ≤ inverseMatrixPair A x x := by
  rw [inverseMatrixPair_eq_dot]
  simpa using hA.inv.posSemidef.dotProduct_mulVec_nonneg x

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeCompactIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {S E : Type*} [NormedAddCommGroup S]
  [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [μ.IsAddHaarMeasure]

omit [MeasurableSpace S] [BorelSpace S]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
lemma continuous_tubeLift : Continuous (tubeLift (S := S) (E := E)) :=
  continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)

omit [NormedAddCommGroup S]
  [MeasurableSpace S] [BorelSpace S] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma tubeLift_mem {D : Set S} (q : S × sphere (0:E) 1) (h : q.1 ∈ D) :
    tubeLift q ∈ tubeOpenSet D := by
  refine ⟨h,?_⟩
  have hh : ‖(q.2:E)‖ = 1 := mem_sphere_zero_iff_norm.1 q.2.property
  intro hz
  change (q.2:E) = 0 at hz
  simp [hz] at hh

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeMetricPositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma tubeBasePair_nonneg {H : S × E → ℝ} {q : S × E} (b : Module.Basis ι ℝ S)
    (hh : 0 ≤ H q) (hB : (tubeBaseMatrix H q b).PosDef) (f : S × E → ℝ) :
    0 ≤ tubeBasePair H b f f q := mul_nonneg hh (inverseMatrixPair_self_nonneg hB _)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeCombination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma expSpace_logSpace {k : ℕ} {s : Space k} (hs : s ∈ positiveOrthant k) :
    expSpace (logSpace s) = s := by
  ext i
  exact Real.exp_log (hs i)

lemma contDiff_expSpace {k : ℕ} : ContDiff ℝ ∞ (expSpace : Space k → Space k) := by
  apply (EuclideanSpace.equiv (Fin k) ℝ).symm.contDiff.comp
  exact contDiff_pi.mpr fun i => (EuclideanSpace.proj i).contDiff.exp

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_LogTubeMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {k : ℕ} {μ : Measure (Space k)}

lemma measurable_logSpace : Measurable (logSpace : Space k → Space k) := by
  apply (EuclideanSpace.equiv (Fin k) ℝ).symm.continuous.measurable.comp
  exact Measurable.of_eval fun index =>
    Real.measurable_log.comp (EuclideanSpace.proj index).continuous.measurable

/- The actual logarithmic pushforward of a tube density, restricted to its
positive base domain. Only the nonnegative part outside that domain is discarded. -/

lemma logTubeMeasure_compact_lt_top [μ.IsAddHaarMeasure]
    {D : Set (Space k)} (hDpos : D ⊆ positiveOrthant k) {F : Space k × E → ℝ}
    (hF : ContinuousOn F (tubeOpenSet D))
    {K : Set (Space k)} (hK : IsCompact K) (hKD : K ⊆ logSpace '' D) :
    logTubeMeasure μ D F K < ⊤ := by
  have hmap : Measurable (fun q : Space k × sphere (0:E) 1 => logSpace q.1) :=
    measurable_logSpace.comp measurable_fst
  have hEK : IsCompact (expSpace '' K) := hK.image contDiff_expSpace.continuous
  have hED : expSpace '' K ⊆ D := by
    rintro s ⟨t,ht,rfl⟩
    obtain ⟨y,hy,rfl⟩ := hKD ht
    simpa only [expSpace_logSpace (hDpos hy)] using hy
  have hset : (fun q : Space k × sphere (0:E) 1 => logSpace q.1) ⁻¹' K ∩ (D ×ˢ Set.univ) =
      (expSpace '' K) ×ˢ Set.univ := by
    ext q
    constructor
    · rintro ⟨hq,hDq,-⟩
      exact ⟨⟨logSpace q.1,hq,expSpace_logSpace (hDpos hDq)⟩,Set.mem_univ _⟩
    · rintro ⟨⟨s,hs,he⟩,-⟩
      have ht : q.1 ∈ expSpace '' K := ⟨s,hs,he⟩
      refine ⟨?_,hED ht,Set.mem_univ _⟩
      change logSpace q.1 ∈ K
      rw [← he,logSpace_expSpace]
      exact hs
  rw [logTubeMeasure,Measure.map_apply hmap hK.measurableSet,
    withDensity_apply _ (hK.measurableSet.preimage hmap),
    Measure.restrict_restrict (hK.measurableSet.preimage hmap),hset]
  have hi : IntegrableOn (fun q : Space k × sphere (0:E) 1 => F (tubeLift q))
      ((expSpace '' K) ×ˢ Set.univ) (μ.prod volume.toSphere) :=
    ContinuousOn.integrableOn_compact (hEK.prod isCompact_univ)
      (hF.comp continuous_tubeLift.continuousOn (fun q hq => tubeLift_mem q (hED hq.1)))
  exact (lintegral_ofReal_le_lintegral_enorm _).trans_lt hi.2

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualLogMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [MeasurableSpace E] [BorelSpace E] in
lemma affineEpigraph_logWeight_regular {n k : ℕ}
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (Space k × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set (Space k)} (hD : IsOpen D) (hDpos : D ⊆ positiveOrthant k)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let M := tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE
    let T := tubeLogMassWeight H
    ContinuousOn M (tubeOpenSet D) ∧ ContinuousOn T (tubeOpenSet D) ∧
      ∀ s ∈ D, ∀ e : E, ‖e‖ = 1 → 0 ≤ M (s,e) ∧ 0 ≤ T (s,e) := by
  dsimp only
  let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let A := fun (i : Fin k) (q : Space k × E) => Real.log (q.1 i)
  have hH (q : Space k × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ H q :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hq.1 hq.2).1
  have hpos (q : Space k × E) (hq : q ∈ tubeOpenSet D) :=
    affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hq.1 hq.2 b bE
  have hA (i : Fin k) (q : Space k × E) (hq : q ∈ tubeOpenSet D) : ContDiffAt ℝ ∞ (A i) q := by
    have hpj : ContDiff ℝ ∞ (fun s : Space k => s i) := (EuclideanSpace.proj i : Space k →L[ℝ] ℝ).contDiff
    have hh : ContDiffAt ℝ ∞ (fun z : Space k × E => z.1 i) q := (hpj.comp contDiff_fst).contDiffAt
    exact hh.log (hDpos hq.1 i).ne'
  refine ⟨?_,?_,?_⟩
  · intro q hq
    exact (continuousAt_tubeMeasureDensity (hH q hq) b bE (hpos q hq).2.2).continuousWithinAt
  · apply continuousOn_const.add
    apply continuousOn_finsetSum
    intro i _ q hq
    exact (contDiffAt_tubeBasePair (hH q hq) (hA i q hq) (hA i q hq) b
      (hpos q hq).1.det_pos.ne').continuousAt.continuousWithinAt
  · intro s hs e he
    have hen : e ≠ 0 := by intro hz; simp [hz] at he
    have hz := hpos (s,e) ⟨hs,hen⟩
    refine ⟨(tubeMeasureCoefficient_pos hz.2.2 hz.1.det_pos hz.2.1).le,?_⟩
    apply add_nonneg zero_le_one
    exact Finset.sum_nonneg fun i _ => tubeBasePair_nonneg b hz.2.2.le hz.1 (A i)

/- The paper's sigma measure, pushed to logarithmic coordinates. This definition
uses the actual affine epigraph support function, not an abstract model metric. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_MassInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma tube_area_factorization {n : ℕ} {h B Q : ℝ}
    (hh : 0 < h) (hB : 0 < B) (hQ : 0 < Q) :
    B ^ (1/((n:ℝ)+2)) * Q ^ (1-1/((n:ℝ)+2)) =
      (tubeMeasureCoefficient n h B Q)^(2/((n:ℝ)+2)) *
        h ^ ((n:ℝ)/((n:ℝ)+2)) * Q ^ (1-2/((n:ℝ)+2)) := by
  have hN : (n:ℝ)+2 ≠ 0 := by positivity
  have hμ := tubeMeasureCoefficient_pos (n := n) hh hB hQ
  apply Real.log_injOn_pos
  · change (0:ℝ) < _
    positivity
  · change (0:ℝ) < _
    positivity
  rw [Real.log_mul (Real.rpow_pos_of_pos hB _).ne' (Real.rpow_pos_of_pos hQ _).ne',
    Real.log_rpow hB,Real.log_rpow hQ,
    Real.log_mul (mul_pos (Real.rpow_pos_of_pos hμ _) (Real.rpow_pos_of_pos hh _)).ne'
      (Real.rpow_pos_of_pos hQ _).ne',
    Real.log_mul (Real.rpow_pos_of_pos hμ _).ne' (Real.rpow_pos_of_pos hh _).ne',
    Real.log_rpow hμ,Real.log_rpow hh,Real.log_rpow hQ]
  unfold tubeMeasureCoefficient
  rw [Real.log_mul (Real.rpow_pos_of_pos hh _).ne' (Real.sqrt_pos.2 (mul_pos hB hQ)).ne',
    Real.log_rpow hh,Real.log_sqrt (mul_pos hB hQ).le,Real.log_mul hB.ne' hQ.ne']
  field_simp
  ring

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_MassIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/- The exact inverse-Hessian interpolation used in the source cell bound.
The two controlling integrals are the cap identity term and the true large
principal-minor term; no bound on the weighted integral is presumed. -/
lemma lintegral_tube_area_le_mass {n : ℕ} (hn : 1 ≤ n)
    {h B Q : X → ℝ} (hh : AEMeasurable h μ) (hB : AEMeasurable B μ)
    (hQ : AEMeasurable Q μ) (hhp : ∀ᵐ x ∂μ, 0 < h x)
    (hBp : ∀ᵐ x ∂μ, 0 < B x) (hQp : ∀ᵐ x ∂μ, 0 < Q x)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ x ∂μ, h x ≤ M) :
    (∫⁻ x, ENNReal.ofReal (B x ^ (1/((n:ℝ)+2)) * Q x ^ (1-1/((n:ℝ)+2))) ∂μ) ≤
      ENNReal.ofReal (M ^ ((n:ℝ)/((n:ℝ)+2))) *
      (∫⁻ x, ENNReal.ofReal (tubeMeasureCoefficient n (h x) (B x) (Q x)) ∂μ)^(2/((n:ℝ)+2)) *
      (∫⁻ x, ENNReal.ofReal (Q x) ∂μ)^(1-2/((n:ℝ)+2)) := by
  let p : ℝ := 2/((n:ℝ)+2)
  let W := fun x => tubeMeasureCoefficient n (h x) (B x) (Q x)
  have hp : 0 < p := by dsimp [p]; positivity
  have hp1 : p < 1 := by
    dsimp [p]
    apply (div_lt_one (by positivity)).2
    have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hW : AEMeasurable W μ :=
    (hh.pow_const (-(n:ℝ)/2)).mul ((hB.mul hQ).sqrt)
  have hWp : ∀ᵐ x ∂μ, 0 ≤ W x := by
    filter_upwards [hhp,hBp,hQp] with x hx hy hz
    exact (tubeMeasureCoefficient_pos hx hy hz).le
  have hQn := hQp.mono fun _ hx => hx.le
  have hholder := lintegral_ofReal_geometric_mean_le μ hp hp1 hW hQ hWp hQn
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (M ^ ((n:ℝ)/((n:ℝ)+2))) *
        ENNReal.ofReal ((W x)^p*(Q x)^(1-p)) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hhp,hBp,hQp,hbound] with x hx hy hz hb
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hM _)]
      apply ENNReal.ofReal_le_ofReal
      rw [tube_area_factorization hx hy hz]
      have hm : (h x)^((n:ℝ)/((n:ℝ)+2)) ≤ M^((n:ℝ)/((n:ℝ)+2)) :=
        Real.rpow_le_rpow hx.le hb (by positivity)
      change (W x)^p * (h x)^((n:ℝ)/((n:ℝ)+2)) * (Q x)^(1-p) ≤ _
      calc
        _ ≤ (W x)^p * M^((n:ℝ)/((n:ℝ)+2)) * (Q x)^(1-p) := by
          have hw : 0 ≤ W x := (tubeMeasureCoefficient_pos hx hy hz).le
          gcongr
        _ = _ := by ring
    _ = ENNReal.ofReal (M ^ ((n:ℝ)/((n:ℝ)+2))) *
        ∫⁻ x, ENNReal.ofReal ((W x)^p*(Q x)^(1-p)) ∂μ := by
      rw [lintegral_const_mul']
      exact ENNReal.ofReal_ne_top
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_right hholder
        (ENNReal.ofReal (M ^ ((n:ℝ)/((n:ℝ)+2))))

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualAreaMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The literal spherical affine area is bounded in terms of the actual weighted
sigma density, by Holder and the actual fiber support height. -/
theorem affineEpigraph_area_le_sigma {n k : ℕ} (hn : 1 ≤ n)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (Space k × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set (Space k)} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {Q : Set (Space k)} (hQ : MeasurableSet Q) (hQD : Q ⊆ D) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ s ∈ Q, ∀ y : E, (s,y) ∈ affineEpigraphPullback Ω u a L → ‖y‖ ≤ M) :
    let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    let μ := (volume.restrict Q).prod (volume : Measure E).toSphere
    (∫⁻ s in Q, ∫⁻ v : Metric.sphere (0:E) 1,
      ENNReal.ofReal ((tubeBaseMatrix H (s,v) b).det ^ (1/((n:ℝ)+2)) *
        (tubeAngularDensity H (s,v) bE)^(1-1/((n:ℝ)+2))) ∂volume.toSphere) ≤
    ENNReal.ofReal (M^((n:ℝ)/((n:ℝ)+2))) *
      (∫⁻ q, ENNReal.ofReal (tubeMeasureDensity n H b bE (q.1,q.2) *
        tubeLogMassWeight H (q.1,q.2)) ∂μ)^(2/((n:ℝ)+2)) *
      (∫⁻ q, ENNReal.ofReal (tubeAngularDensity H (q.1,q.2) bE) ∂μ)^(1-2/((n:ℝ)+2)) := by
  let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let μ := (volume.restrict Q).prod (volume : Measure E).toSphere
  let B := fun q : Space k × Metric.sphere (0:E) 1 => (tubeBaseMatrix H (q.1,q.2) b).det
  let A := fun q : Space k × Metric.sphere (0:E) 1 => tubeAngularDensity H (q.1,q.2) bE
  have hmap : Continuous (fun q : Space k × Metric.sphere (0:E) 1 => (q.1,(q.2:E))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have he (e : Metric.sphere (0:E) 1) : ‖(e:E)‖ = 1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using e.property
  have he0 (e : Metric.sphere (0:E) 1) : (e:E) ≠ 0 := Metric.ne_of_mem_sphere e.property one_ne_zero
  have hj (q : Space k × Metric.sphere (0:E) 1) (hq : q.1 ∈ Q) : ContDiffAt ℝ ∞ H (q.1,q.2) :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero (hQD hq) (he0 q.2)).1
  have hpq (q : Space k × Metric.sphere (0:E) 1) (hq : q.1 ∈ Q) :=
    affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero (hQD hq) (he0 q.2) b bE
  have haemeas {F : Space k × E → ℝ}
      (hF : ∀ q : Space k × Metric.sphere (0:E) 1, q.1 ∈ Q → ContinuousAt F (q.1,q.2)) :
      AEMeasurable (fun q : Space k × Metric.sphere (0:E) 1 => F (q.1,q.2)) μ := by
    change AEMeasurable _ ((volume.restrict Q).prod (volume : Measure E).toSphere)
    rw [Measure.restrict_prod_eq_prod_univ]
    apply ContinuousOn.aemeasurable _ (hQ.prod MeasurableSet.univ)
    intro q hq
    exact ((hF q hq.1).comp (f := fun z : Space k × Metric.sphere (0:E) 1 => (z.1,(z.2:E)))
      (x := q) hmap.continuousAt).continuousWithinAt
  have hHae := haemeas (F := H) (fun q hq => (hj q hq).continuousAt)
  have hBae : AEMeasurable B μ := haemeas (F := fun z => (tubeBaseMatrix H z b).det) (fun q hq =>
    (((continuousDetRows (ι := Fin k)).contDiff.contDiffAt.comp (q.1,(q.2:E))
      (contDiffAt_tubeBaseMatrix (hj q hq) b))).continuousAt)
  have hAae : AEMeasurable A μ := haemeas (F := fun z => tubeAngularDensity H z bE) (fun q hq =>
    (contDiffAt_tubeAngularDensity (hj q hq) bE).continuousAt)
  have hqa : ∀ᵐ q ∂μ, q.1 ∈ Q := by
    change ∀ᵐ q ∂(volume.restrict Q).prod (volume : Measure E).toSphere, q.1 ∈ Q
    rw [Measure.restrict_prod_eq_prod_univ]
    filter_upwards [ae_restrict_mem (μ := volume.prod (volume : Measure E).toSphere)
      (hQ.prod MeasurableSet.univ)] with q hq
    exact hq.1
  have hholder := lintegral_tube_area_le_mass hn hHae hBae hAae
    (hqa.mono fun q hq => (hpq q hq).2.2)
    (hqa.mono fun q hq => (hpq q hq).1.det_pos)
    (hqa.mono fun q hq => (hpq q hq).2.1) hM
    (hqa.mono fun q hq => (le_abs_self _).trans
      (homogeneousSupport_abs_le_of_radius (hK q.1 (hQD hq))
      ⟨0,interior_subset (hzero q.1 (hQD hq))⟩ (he q.2) (hbound q.1 hq)))
  have hareaMeas : AEMeasurable (fun q => ENNReal.ofReal
      (B q ^ (1/((n:ℝ)+2)) * A q ^ (1-1/((n:ℝ)+2)))) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((hBae.pow_const (1/((n:ℝ)+2))).mul (hAae.pow_const (1-1/((n:ℝ)+2))))
  dsimp only
  change (∫⁻ s in Q, ∫⁻ v : Metric.sphere (0:E) 1,
    ENNReal.ofReal (B (s,v) ^ (1/((n:ℝ)+2)) * A (s,v) ^ (1-1/((n:ℝ)+2))) ∂volume.toSphere) ≤ _
  rw [← lintegral_prod _ hareaMeas]
  refine hholder.trans ?_
  apply mul_le_mul_left
  apply mul_le_mul_right
  apply ENNReal.rpow_le_rpow _ (by positivity)
  apply lintegral_mono_ae
  filter_upwards [hqa] with q hq
  apply ENNReal.ofReal_le_ofReal
  have hw : 1 ≤ tubeLogMassWeight H (q.1,q.2) := by
    change 1 ≤ 1+∑ i : Fin k, _
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ =>
      tubeBasePair_nonneg b (hpq q hq).2.2.le (hpq q hq).1 _)
  change tubeMeasureDensity n H b bE (q.1,q.2) ≤ _
  exact le_mul_of_one_le_right (tubeMeasureCoefficient_pos (hpq q hq).2.2
    (hpq q hq).1.det_pos (hpq q hq).2.1).le hw

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

/- Coordinate Hessian. On the open domain it depends only on the restriction of `u`.
The order of the two differentiations is immaterial under the smoothness hypothesis. -/
/- The coefficient U^{ij} = det(D²u) (D²u)^{-1}_{ij}. -/
/- The classical determinant weight; in particular, this is not a generalized exponent. -/
/- Length on [0,1] for g_x(v,v) = ‖v‖² + (Du_x v)², the metric induced
by the Euclidean graph embedding x ↦ (x,u(x)). The product norm on Lean's ordinary
product type is NOT used (it would be the maximum norm). -/
/- The intrinsic extended distance: infimum of lengths of C¹ paths in the domain.
Using a single C¹ path gives the same intrinsic distance as piecewise C¹ paths,
by smooth endpoint reparameterization and concatenation. -/
/- Sequential completeness for the induced Euclidean path metric. This states
that every intrinsic Cauchy sequence of points in Ω has an intrinsic limit in Ω.
It imposes no growth condition and no completeness condition on the affine metric. -/
/- The graph, regarded as an affine subset of R^{n+1}. -/
/-!
The first missing differential identity in `sections/area.tex`, Stationarity:
the cofactor of an actual Hessian is divergence-free.  The proof below uses
multilinearity of the determinant and symmetry of second derivatives (Piola).
-/

/- The determinant, as a continuous map multilinear in its rows. -/
/- Exchanging two independently replaced rows reverses the determinant. -/
/- Expand one determinant row in the coordinate vectors. -/
/- Symmetric coefficients contract to zero with an alternating pair of rows. -/
/- The algebraic cancellation underlying the Piola identity. -/

/- Rows of the derivative of a list of scalar functions, in fixed directions. -/
/- Differentiate a cofactor by differentiating each of its unfrozen rows. -/
/- Piola's identity in fixed directions; it uses only equality of mixed partials. -/

/- Smoothness through order three suffices for the cofactor cancellation. -/
/- For an invertible Hessian, the manuscript's definition is exactly the adjugate. -/
/- The Hessian cofactor is symmetric under the standing positivity hypothesis. -/
/- Both divergences of the actual coefficient matrix vanish on the original domain. -/

/- The frozen coordinate Hessian has smooth entries at every interior smooth point. -/
/- Determinants of the actual Hessian are smooth, by row multilinearity. -/
/- Polynomial cofactor entries are smooth even before invertibility is used. -/
/- Smoothness of U on its actual open domain, with no extension hypothesis. -/
/- The real determinant weight has its original exponent throughout the proof. -/

/- A fixed-direction derivative, used only as notation for the actual Fréchet derivative. -/
/- The differential part of the double integration by parts. Both zero
cofactor divergences are used; they will be supplied by the proved Piola identity. -/

/- The exact maximal-graph operator is the double divergence of its variational coefficient. -/

/- Integrability uses continuity only on a compact set containing the support. -/
/- Compact support of the test function removes any global regularity requirement
on the coefficient. This is the integration-by-parts form used on the original Ω. -/
/- Two integrations by parts, without an artificial globally smooth coefficient. -/
/- Global smoothness of a fixed-direction derivative. -/
/- The weak double-divergence formula with precisely a compactly supported test. -/

/- Graph-direction stationarity for the source's equation and actual coefficient.
All regularity of `u` is needed only on the original open domain. -/
/- The density of affine area in the original graph coordinates. -/
/- The variation coefficient has exactly the exponent in the manuscript. -/
/- `wU` is not a surrogate for the affine-area coefficient. -/
/- The source's first-variation integral, over its original open domain. -/

/- Jacobi's formula without assuming invertibility of the varied matrix. -/
/- Pointwise first variation of the actual affine-area density. -/

/- Away from topological support the test is locally zero, so no extension
of a smooth coefficient across the original boundary is necessary. -/
/- Commuting fixed-direction differentiation with evaluation of a derivative. -/
/- Symmetry of the second derivative in fixed directions. -/
/- The support-plane height `ν(o-X)` in original graph coordinates. -/
/- Smoothness holds only locally; the eventual zero argument handles tests. -/
/- The derivative of the radial gradient, including its moving vector argument. -/
/- The cancellation `D Z = H(x-o)` with no coordinate or global extension assumption. -/
/- The exact second derivative of the support-plane height. -/

/- The coordinate version used in the trace of the cap test. -/
/- Jacobi's formula in arbitrary fixed directions, for the actual entries. -/
/- Smoothness of the area density on the original domain. -/
/- The exact differential of the affine area coefficient. -/
/- Trace of the identity, in the entry convention used in the manuscript. -/
/- Weighted radial trace, avoiding a logarithm at points outside the domain. -/
/- Expansion in the frozen Euclidean coordinate vectors. -/
/- Linear functionals are recovered exactly by coordinates. -/
/- The radial vector derivative is the sum of its coordinate derivatives. -/
/- A second derivative product rule on the actual open domain. -/
/- Scalar composition by its actual one-dimensional derivative. -/
/- The second chain rule used by a cap test. -/
/- Restriction of an arbitrary ambient affine function to the original graph. -/
/- Coordinate pairing equals the ordinary matrix-vector contraction. -/
/- Symmetry of the covector contraction, with the literal matrix coefficients. -/
/- Exact inverse contraction for a radial vector and a covector. -/
/- The radial support gradient cancels exactly against the inverse Hessian. -/
/- Product trace in coordinates. -/
/- Chain trace in coordinates. -/
/- Positivity fixes the inverse-Hessian symmetry employed in a cap test. -/
/- Pointwise first-variation integrand of the source cap test. -/
/- Cancellation of the affine coefficients in the first variation. -/
/- The actual coordinate functional through the Euclidean-space equivalence. -/
/- A smooth compact test makes a merely locally smooth coefficient globally smooth. -/
/- Integral of a derivative of a smooth compactly supported scalar field. -/
/- Radial integration by parts with a compact test and no global extension of `f`.
This formulation gives integrability as well as the identity. -/
/- Zero-extension of a compactly supported local test is genuinely smooth on the
ambient coordinate space; no extension theorem for the graph is needed. -/
/- Hessians depend only on the germ of a function, also with the total derivative
convention at points outside the domain. -/
/- The actual first-variation density is integrable for a compact local test. -/
/- The cap identity in the original graph coordinates (source `area.tex`,
Lemma Cap identity). The source assumes compact support of all three displayed
scalar compositions; this proof in fact only needs the first support condition.
The measure here is precisely affine area density times Lebesgue measure. -/

/- Weighted arithmetic-geometric mean for the eigenvalues, with the unused
weight placed at 1. This is the determinant-power supporting inequality at I. -/
/- Congruence by the inverse positive square root converts the determinant
ratio and the mixed trace to the same positive semidefinite matrix. -/
/- Concavity in its precise tangent form, for all exponents in [0,1/n]. -/

/- On an open set the Hessian is additive; no extension outside that set is used. -/
/- The actual determinant density obeys its supporting-hyperplane inequality. -/
/- Density differences for a compactly supported perturbation really are
integrable, although each area on an unbounded domain could be infinite. -/
/- Local maximization of graph affine area: the integrated form used in
`bounds.tex:99–126`. It is deduced from the PDE, not assumed as stability. -/
/- The affine pullback uses the continuous map associated with the actual
matrix, so its determinant and nonsingularity have their usual meanings. -/
/- First derivative of composition with an affine base change. -/
/- The Hessian chain rule, retaining the exact order Bᵀ H B. -/
/- Multiplying heights by a scalar multiplies the actual Hessian by it. -/
/- Nonsingular congruence and positive scalar multiplication preserve strict
ellipticity. The condition on B is exactly invertibility, not orthogonality. -/
/- Exact determinant normalization used for rescaled sections. -/
/- The trace contraction is invariant under simultaneous congruence, with the
exact scalar ratio. This is the algebra behind covariance of the affine PDE. -/
/- The classical PDE is equivalent to the inverse-Hessian trace formulation
wherever its coefficients are the actual positive-definite Hessian. -/
/- Change of base variables, positive vertical scaling, and arbitrary affine
height correction. This includes the normalization of sections in rigidity. -/
/- The actual determinant weight transforms by its exact positive constant. -/
/- Hessians are local, including their inner derivative. -/
/- Exact, classical affine-maximal PDE covariance for section normalization.
No transformed PDE is assumed: it follows from the original one by the actual
Hessian and determinant chain rules. -/

/- The exact quadratics used in the positive-cap comparison. -/

/- A genuine compact smooth convex-cap replacement, with no stationarity or
area conclusion assumed. This supplies source bounds.tex:88–110. -/

/- Local weak maximization and a smooth convex replacement give the cap
comparison on its actual open base. -/
/- The graph-coordinate positive cap estimate, with a quantitative uniform
constant. The original PDE, not an area lower bound, is the hypothesis. -/
/- Uniform nonvanishing in uniformly bounded graph caps, exactly the smooth
comparison portion of bounds.tex:88–126. No assumptions on boundary regularity
or uniform Hessian bounds enter. -/

/- A bounded cap quantitatively separates a unit recession direction from
its horizontal hyperplane. This is the ray argument in bounds.tex:45–59. -/
/- The normalized vertical has uniformly bounded norm. -/
/- Compactness of a closed graph sublevel follows from compactness of the
entire epigraph cap, without a boundary regularity hypothesis. -/
/- The ambient ball supplies the graph's base ball at the center's height. -/
/- A cap radius bounds distances to the center in its base. -/

/- A shear does not change height and straightens an upward vector. -/
/- The induced invertible horizontal map of a triangular ambient affine map. -/

/- The manuscript's epigraph; the domain is not silently replaced by all of space. -/
/- The affine image is literally the epigraph of the derived graph; no new
solution or geometric stationary surrogate is assumed. -/

/- Affine area of the actual cap, in the original global graph chart.
The determinant exponent is the one proved for the literal parametric density. -/
/- The true cap integral is identical in the sheared graph coordinates. -/

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ConvexLocalLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open scoped Topology NNReal

open Filter Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/- The local distance-function topology used in geometry.tex:70–101. Sets
are separately required to be nonempty and closed when those properties enter. -/

omit [NormedSpace ℝ E] in
theorem LocalDistanceConverges.pointwise {Cj : ℕ → Set E} {C : Set E}
    (h : LocalDistanceConverges Cj C) (x : E) :
    Tendsto (fun j => infDist x (Cj j)) atTop (𝓝 (infDist x C)) := by
  exact ((tendstoLocallyUniformly_iff_forall_isCompact.mp h) {x}
    (isCompact_singleton)).tendsto_at (mem_singleton x)

/- Every point of a local limit has an actual sequence of nearby points
in the approximating closed convex bodies (convexity is not needed here). -/
omit [NormedSpace ℝ E] in
theorem LocalDistanceConverges.exists_approximating {Cj : ℕ → Set E} {C : Set E}
    (h : LocalDistanceConverges Cj C) (hcl : ∀ j, IsClosed (Cj j))
    (hne : ∀ j, (Cj j).Nonempty) {x : E} (hx : x ∈ C) :
    ∃ xj : ℕ → E, (∀ j, xj j ∈ Cj j) ∧ Tendsto xj atTop (𝓝 x) := by
  choose xj hmem heq using fun j => (hcl j).exists_infDist_eq_dist (hne j) x
  refine ⟨xj, hmem, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [dist_comm, ← heq, infDist_zero_of_mem hx] using h.pointwise x

/- Local convergence prevents approximants from meeting any fixed compact
set disjoint from the closed limit. -/
omit [NormedSpace ℝ E] in
theorem LocalDistanceConverges.eventually_disjoint_compact
    {Cj : ℕ → Set E} {C S : Set E} (h : LocalDistanceConverges Cj C)
    (hcl : IsClosed C) (hne : C.Nonempty) (hS : IsCompact S)
    (hdis : Disjoint C S) : ∀ᶠ j in atTop, Disjoint (Cj j) S := by
  rcases S.eq_empty_or_nonempty with rfl | hSn
  · simp
  obtain ⟨x, hx, hmin⟩ := hS.exists_isMinOn hSn (continuous_infDist_pt C).continuousOn
  have hxnot : x ∉ C := fun hc => Set.disjoint_left.mp hdis hc hx
  have hδ : 0 < infDist x C := (hcl.notMem_iff_infDist_pos hne).mp hxnot
  have hU := tendstoLocallyUniformly_iff_forall_isCompact.mp h S hS
  have he := Metric.tendstoUniformlyOn_iff.mp hU (infDist x C) hδ
  filter_upwards [he] with j hj
  rw [Set.disjoint_left]
  intro y hyC hyS
  have hd := hj y hyS
  have hmin' : infDist x C ≤ infDist y C := hmin hyS
  rw [infDist_zero_of_mem hyC, dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg infDist_nonneg] at hd
  linarith

/- Limits of convergent points of approximants belong to the local limit. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_InteriorLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter Metric
open scoped Topology Pointwise

/- The geometric conditions of a k-model, in its distinguished coordinates.
Membership in the affine local-limit family is separate from these conditions. -/
theorem closed_convex_add_of_ray {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (hc : IsClosed C) (hv : Convex ℝ C) {x v : E}
    (hx : x ∈ C) (hray : ∀ t : ℝ, 0 ≤ t → t • v ∈ C) : x + v ∈ C := by
  have htend : Tendsto (fun t : ℝ => (1 - t) • x + v) (𝓝[>] 0) (𝓝 (x + v)) := by
    have hc : Continuous (fun t : ℝ => (1 - t) • x + v) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply hc.mem_of_tendsto htend
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht ht1
  have ht0 : 0 < t := ht
  have h := hv hx (hray t⁻¹ (inv_nonneg.mpr ht0.le))
    (show 0 ≤ 1 - t by linarith) ht0.le (by ring)
  simpa only [smul_smul, mul_inv_cancel₀ ht0.ne', one_smul] using h

namespace IsModelShape

variable {k m : ℕ} {C : Set (Space k × Space m)} (h : IsModelShape C)
include h

theorem zero_mem : (0 : Space k × Space m) ∈ C := by
  exact h.orthant 0 (by simp)

theorem add_nonnegative_base {s v : Space k} {y : Space m}
    (hy : (s, y) ∈ C) (hv : ∀ i, 0 ≤ v i) : (s + v, y) ∈ C := by
  have hh := closed_convex_add_of_ray h.closed h.convex hy (v := (v, 0)) (by
    intro t ht
    simpa only [Prod.smul_mk, smul_zero] using
      h.orthant (t • v) (fun i => mul_nonneg ht (hv i)))
  simpa using hh

theorem fiber_mono {s t : Space k} (hst : ∀ i, s i ≤ t i) :
    modelFiber C s ⊆ modelFiber C t := by
  intro y hy
  have hh := h.add_nonnegative_base hy (v := t - s) (by intro i; exact sub_nonneg.mpr (hst i))
  simpa only [add_sub_cancel, modelFiber, mem_ofPred_eq] using hh

theorem fiber_contract {s : Space k} {a : ℝ} (ha : 1 ≤ a) :
    modelFiber C (a • s) ⊆ a • modelFiber C s := by
  have hp : 0 < a := by linarith
  intro y hy
  have hh := h.convex.smul_mem_of_zero_mem h.zero_mem hy
    (show a⁻¹ ∈ Icc (0 : ℝ) 1 from ⟨inv_nonneg.mpr hp.le, inv_le_one_of_one_le₀ ha⟩)
  have hm : a⁻¹ • y ∈ modelFiber C s := by
    simpa only [modelFiber, mem_ofPred_eq, Prod.smul_mk, smul_smul,
      inv_mul_cancel₀ hp.ne', one_smul] using hh
  exact Set.mem_smul_set.mpr ⟨a⁻¹ • y, hm, by simp [smul_smul, hp.ne']⟩

/- Every strictly positive fiber is full dimensional; this proof also covers
m=0, using the ordinary topology of the zero-dimensional space. -/
theorem fiber_box_bound {R T : ℝ} (hT : 1 ≤ T)
    (hR : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))) ⊆ Metric.closedBall 0 R)
    {s : Space k} (hs : ∀ i, s i ≤ T) {y : Space m} (hy : y ∈ modelFiber C s) :
    ‖y‖ ≤ T * R := by
  have hp : 0 < T := by linarith
  have hmono : y ∈ modelFiber C (T • WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))) :=
    h.fiber_mono (fun i => by simpa using hs i) hy
  obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.mp (h.fiber_contract hT hmono)
  have hzR : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hR hz
  simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hp] using mul_le_mul_of_nonneg_left hzR hp.le

end IsModelShape

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_AffineFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter Metric
open scoped Topology Pointwise

open scoped Pointwise

/- The coordinate action of the actual matrix linear equivalence. -/
theorem norm_le_sqrt_card_of_coordinate_le {n : ℕ} (x : Space n)
    (hx : ∀ i, |x i| ≤ 1) : ‖x‖ ≤ Real.sqrt n := by
  have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) x
  have hs : ‖x‖ ^ 2 ≤ (n : ℝ) := by
    rw [hn]
    calc
      _ ≤ ∑ i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        have := hx i
        rw [Real.norm_eq_abs]
        nlinarith [sq_nonneg (|x i| - 1), abs_nonneg (x i)]
      _ = n := by simp
  exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    (by rwa [Real.sq_sqrt (Nat.cast_nonneg n)])

/- A compact body's column determinant has a maximizer, with nonzero value
whenever the body contains a ball about zero. -/

open scoped Pointwise

/- Exact centered normalization in geometry.tex (2/(C+1), 2n), proved
without importing John's theorem: first normalize the symmetric difference
body, then use the actual balance inclusion. -/

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NormedInteriorLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Filter Metric
open scoped Topology Pointwise
open scoped Pointwise
open scoped Pointwise

open Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/- Normed-space inner containment. In particular this applies to the literal
product coordinates used for the epigraph, whose norm is not a Hilbert norm. -/
omit [ProperSpace E] in
theorem normed_ball_subset_of_infDist_lt {K : Set E} (hcl : IsClosed K)
    (hcv : Convex ℝ K) (hne : K.Nonempty) (a : E) {r : ℝ} (hr : 0 < r)
    (happ : ∀ y ∈ Metric.closedBall a r, infDist y K < r/4) :
    Metric.ball a (r/4) ⊆ K := by
  intro x hx
  by_contra hxn
  obtain ⟨f,s,hsep,hfx⟩ := geometric_hahn_banach_closed_point hcv hcl hxn
  have hf : 0 < ‖f‖ := by
    apply norm_pos_iff.mpr
    intro he
    obtain ⟨z,hz⟩ := hne
    have hh := (hsep z hz).trans hfx
    simp [he] at hh
  obtain ⟨v,hv,hfv⟩ := f.exists_lt_apply_of_lt_opNorm (show ‖f‖/2 < ‖f‖ by linarith)
  obtain ⟨v,hv,hfv⟩ : ∃ v : E, ‖v‖ < 1 ∧ ‖f‖/2 < f v := by
    by_cases hh : 0 ≤ f v
    · exact ⟨v,hv,by simpa only [Real.norm_eq_abs,abs_of_nonneg hh] using hfv⟩
    · exact ⟨-v,by simpa using hv,by simpa only [map_neg,Real.norm_eq_abs,abs_of_neg (lt_of_not_ge hh)] using hfv⟩
  let y := a+r • v
  have hy : y ∈ Metric.closedBall a r := by
    rw [Metric.mem_closedBall,dist_eq_norm]
    simpa only [y,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hr,mul_one]
      using (mul_le_mul_of_nonneg_left hv.le hr.le)
  obtain ⟨z,hz,hyz⟩ := (infDist_lt_iff hne).mp (happ y hy)
  have hyz' : ‖y-z‖ < r/4 := by simpa only [dist_eq_norm] using hyz
  have hx' : ‖x-a‖ < r/4 := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
  have hfxy : f y-f x ≤ ‖f‖*‖y-z‖ := by
    have hb : f y-f z ≤ ‖f‖*‖y-z‖ := by
      rw [← map_sub]
      exact (le_abs_self _).trans (f.le_opNorm (y-z))
    linarith [hsep z hz]
  have hfxa : f x-f a ≤ ‖f‖*‖x-a‖ := by
    rw [← map_sub]
    exact (le_abs_self _).trans (f.le_opNorm (x-a))
  have hfy : f y = f a+r*f v := by simp only [y,map_add,map_smul,smul_eq_mul]
  have h1 := mul_lt_mul_of_pos_left hyz' hf
  have h2 := mul_lt_mul_of_pos_left hx' hf
  have h3 := mul_lt_mul_of_pos_left hfv hr
  nlinarith

theorem LocalDistanceConverges.eventually_normed_ball_subset
    {Cj : ℕ → Set E} {C : Set E} (h : LocalDistanceConverges Cj C)
    (hclj : ∀ j, IsClosed (Cj j)) (hcvj : ∀ j, Convex ℝ (Cj j))
    (hnej : ∀ j, (Cj j).Nonempty) {a : E} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall a r ⊆ C) :
    ∀ᶠ j in atTop, Metric.ball a (r/4) ⊆ Cj j := by
  have hU := tendstoLocallyUniformly_iff_forall_isCompact.mp h (Metric.closedBall a r)
    (isCompact_closedBall a r)
  have he := Metric.tendstoUniformlyOn_iff.mp hU (r/4) (by positivity)
  filter_upwards [he] with j hj
  apply normed_ball_subset_of_infDist_lt (hclj j) (hcvj j) (hnej j) a hr
  intro y hy
  have he := hj y hy
  rw [infDist_zero_of_mem (hball hy),dist_zero_left,Real.norm_eq_abs,
    abs_of_nonneg infDist_nonneg] at he
  exact he

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NormedCompactInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Filter Metric
open scoped Topology Pointwise
open scoped Pointwise
open scoped Pointwise

section NormedCompactInterior
open Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/- Compact inner containment for the literal (possibly non-Hilbert) ambient
norm. In particular the product coordinate norm creates no hidden instance. -/
theorem LocalDistanceConverges.eventually_normed_compact_subset
    {Cj : ℕ → Set E} {C S : Set E} (h : LocalDistanceConverges Cj C)
    (hclj : ∀ j, IsClosed (Cj j)) (hcvj : ∀ j, Convex ℝ (Cj j))
    (hnej : ∀ j, (Cj j).Nonempty) (hS : IsCompact S)
    (hSC : S ⊆ interior C) : ∀ᶠ j in atTop, S ⊆ Cj j := by
  classical
  have hex : ∀ x : S, ∃ r > 0, Metric.closedBall (x : E) r ⊆ C := by
    intro x
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior (x : E) (hSC x.2)
    exact ⟨r / 2, half_pos hr, (Metric.closedBall_subset_ball (by linarith)).trans
      (hball.trans interior_subset)⟩
  choose r hr hball using hex
  obtain ⟨t, ht⟩ := hS.elim_nhds_subcover' (fun x hx => Metric.ball x (r ⟨x, hx⟩ / 4))
    (fun x hx => Metric.ball_mem_nhds x (div_pos (hr ⟨x,hx⟩) (by norm_num)))
  have he : ∀ x ∈ t, ∀ᶠ j in atTop, Metric.ball (x : E) (r x / 4) ⊆ Cj j :=
    fun x _ => h.eventually_normed_ball_subset hclj hcvj hnej (hr x) (hball x)
  filter_upwards [(t.eventually_all).mpr he] with j hj
  intro x hx
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht hx)
  exact hj y hyt hxy
end NormedCompactInterior
open Filter Metric
open scoped Topology Pointwise

/- The lower inclusion in geometry.tex (normalized-fiber-box), with the
source's exact radius a*r. It is a convexity/recession consequence. -/
lemma IsModelShape.fiber_small_ball {k m : ℕ} {C : Set (Space k × Space m)}
    (hC : IsModelShape C) {r a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hin : closedBall (0 : Space m) r ⊆
      modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))
    {s : Space k} (hs : ∀ i, a ≤ s i) :
    closedBall (0 : Space m) (a*r) ⊆ modelFiber C s := by
  intro y hy
  have hny : ‖y‖ ≤ a*r := by simpa only [mem_closedBall,dist_zero_right] using hy
  have hz : a⁻¹ • y ∈ closedBall (0 : Space m) r := by
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]
    exact (inv_mul_le_iff₀ ha).mpr hny
  have hc := hC.convex.smul_mem_of_zero_mem hC.zero_mem (hin hz) ⟨ha.le,ha1⟩
  have hc' : y ∈ modelFiber C (a • WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) := by
    simpa only [modelFiber,mem_ofPred_eq,Prod.smul_mk,smul_smul,
      mul_inv_cancel₀ ha.ne',one_smul] using hc
  exact hC.fiber_mono (fun i => by simpa using hs i) hc'

lemma IsModelShape.normalized_fiber_interior {k m : ℕ} {C : Set (Space k × Space m)}
    (hC : IsModelShape C) {r a : ℝ} (hr : 0 < r) (ha : 0 < a) (ha1 : a ≤ 1)
    (hin : closedBall (0 : Space m) r ⊆
      modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))
    {s : Space k} (hs : ∀ i, a ≤ s i) {y : Space m} (hy : ‖y‖ ≤ a*r/2) :
    (s,y) ∈ interior C := by
  let U : Set (Space k × Space m) := {p | (∀ i, 3*a/4 < p.1 i) ∧ ‖p.2‖ < 3*a*r/4}
  have hU : IsOpen U := by
    have hi (i : Fin k) : IsOpen {p : Space k × Space m | 3*a/4 < p.1 i} :=
      isOpen_lt continuous_const
        ((PiLp.continuous_apply 2 (fun _ : Fin k => ℝ) i).comp continuous_fst)
    have he : U = (⋂ i : Fin k, {p : Space k × Space m | 3*a/4 < p.1 i}) ∩
        {p : Space k × Space m | ‖p.2‖ < 3*a*r/4} := by ext p; simp [U]
    rw [he]
    exact (isOpen_iInter_of_finite hi).inter
      (isOpen_lt (continuous_snd.norm) continuous_const)
  have hz : (s,y) ∈ U := by
    refine ⟨fun i => by dsimp; linarith [hs i],?_⟩
    dsimp
    nlinarith
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hU.mem_nhds hz)
  intro p hp
  exact hC.fiber_small_ball (a := 3*a/4) (by positivity) (by linarith) hin
    (fun i => (hp.1 i).le) (mem_closedBall_zero_iff.mpr (by nlinarith [hp.2]))

/- Centering gives the exact normalization constants before the model and
positive fiber are selected. No compactness modulus or analytic estimate is
assumed. This is the first part of the manuscript's normalized-fibers corollary. -/
theorem LocalDistanceConverges.eventually_normalized_fiber_inner
    {k m : ℕ} {Cj : ℕ → Set (Space k × Space m)} {C : Set (Space k × Space m)}
    (h : LocalDistanceConverges Cj C) (hC : IsModelShape C)
    (hclj : ∀ j, IsClosed (Cj j)) (hcvj : ∀ j, Convex ℝ (Cj j))
    (hnej : ∀ j, (Cj j).Nonempty) {r a b : ℝ}
    (hr : 0 < r) (ha : 0 < a) (ha1 : a ≤ 1)
    (hin : closedBall (0 : Space m) r ⊆
      modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ)))) :
    ∀ᶠ j in atTop, ∀ s : Space k, (∀ i, s i ∈ Icc a b) →
      closedBall (0 : Space m) (a*r/2) ⊆ modelFiber (Cj j) s := by
  let Q : Set (Space k) := {s | ∀ i, s i ∈ Icc a b}
  have hQ : IsCompact Q := by
    convert! (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).isCompact_preimage.mpr
      (isCompact_univ_pi fun _ : Fin k => (isCompact_Icc : IsCompact (Icc a b))) using 1
    all_goals try with_reducible_and_instances rfl
    ext s
    simp only [Q, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_univ_pi, Set.mem_Icc]
    rfl
  have hi : Q ×ˢ closedBall (0 : Space m) (a*r/2) ⊆ interior C := by
    rintro ⟨s,y⟩ ⟨hs,hy⟩
    exact hC.normalized_fiber_interior hr ha ha1 hin (fun i => (hs i).1)
      (mem_closedBall_zero_iff.mp hy)
  filter_upwards [h.eventually_normed_compact_subset hclj hcvj hnej
    (hQ.prod (isCompact_closedBall _ _)) hi] with j hj s hs y hy
  exact hj ⟨hs,hy⟩

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NormalizedCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Filter Metric
open scoped Topology Pointwise
open scoped Pointwise
open scoped Pointwise

open Filter Metric
open scoped Topology Pointwise

/- Quantitative cap transfer: a given limit radius costs only one unit.
The constant does not depend on the sequence or its limit set. -/
theorem LocalDistanceConverges.eventually_caps_radius
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {Cj : ℕ → Set E} {C : Set E} (h : LocalDistanceConverges Cj C)
    (hcl : IsClosed C) (hclj : ∀ j, IsClosed (Cj j))
    (hcvj : ∀ j, Convex ℝ (Cj j)) (hnej : ∀ j, (Cj j).Nonempty)
    (ell : E →L[ℝ] ℝ) (b R : ℝ)
    (hcap : C ∩ {x | ell x ≤ b} ⊆ closedBall 0 R)
    {q : E} (hq : q ∈ C) (hqb : ell q < b) :
    ∀ᶠ j in atTop, Cj j ∩ {x | ell x ≤ b} ⊆ ball 0 (R+1) := by
  have hqR : ‖q‖ < R+1 := by
    have := mem_closedBall_zero_iff.mp (hcap ⟨hq,hqb.le⟩)
    linarith
  let S : Set E := sphere (0 : E) (R+1) ∩ {x | ell x ≤ b}
  have hSc : IsCompact S := (isCompact_sphere (0 : E) (R+1)).inter_right
    (isClosed_le ell.continuous continuous_const)
  have hSd : Disjoint C S := by
    rw [Set.disjoint_left]
    intro x hx hxs
    have he : ‖x‖ = R+1 := mem_sphere_zero_iff_norm.mp hxs.1
    have hl := mem_closedBall_zero_iff.mp (hcap ⟨hx,hxs.2⟩)
    linarith
  obtain ⟨qj,hqj,hqjt⟩ := h.exists_approximating hclj hnej hq
  have hqjR : ∀ᶠ j in atTop, ‖qj j‖ < R+1 := hqjt.norm.eventually_lt_const hqR
  have hqjb : ∀ᶠ j in atTop, ell (qj j) < b :=
    (ell.continuous.tendsto q |>.comp hqjt).eventually_lt_const hqb
  filter_upwards [h.eventually_disjoint_compact hcl ⟨q,hq⟩ hSc hSd,hqjR,hqjb]
    with j hj hqRj hqbj
  intro p hp
  by_contra hn
  have hpR : R+1 ≤ ‖p‖ := by simpa [Metric.mem_ball,dist_zero_right,not_lt] using hn
  let f : ℝ → E := fun t => (1-t) • qj j+t • p
  have hf : Continuous f := by fun_prop
  have hf0 : f 0 = qj j := by simp [f]
  have hf1 : f 1 = p := by simp [f]
  have hRim : R+1 ∈ (fun t => ‖f t‖) '' Icc (0 : ℝ) 1 :=
    intermediate_value_Icc (by norm_num) hf.norm.continuousOn (by simp [hf0,hf1,hqRj.le,hpR])
  obtain ⟨t,ht,htR⟩ := hRim
  have hft : f t ∈ Cj j := hcvj j (hqj j) hp.1 (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hfb : ell (f t) ≤ b := by
    dsimp [f]
    simp only [map_add,map_smul,smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left hqbj.le (sub_nonneg.mpr ht.2)
    have h2 := mul_le_mul_of_nonneg_left hp.2 ht.1
    nlinarith
  exact Set.disjoint_left.mp hj hft ⟨mem_sphere_zero_iff_norm.mpr htR,hfb⟩

/- The positive base functional occurring in normalized model caps. -/

lemma norm_le_sqrt_card_mul_of_coord_le {k : ℕ} {x : Space k} {T : ℝ}
    (hT : 0 < T) (hx : ∀ i, |x i| ≤ T) : ‖x‖ ≤ Real.sqrt k*T := by
  have hh := norm_le_sqrt_card_of_coordinate_le (T⁻¹ • x) (fun i => by
    change |T⁻¹ * x i| ≤ 1
    rw [abs_mul,abs_of_pos (inv_pos.mpr hT)]
    exact (inv_mul_le_iff₀ hT).mpr (by simpa using hx i))
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hT)] at hh
  exact (inv_mul_le_iff₀ hT).mp hh |>.trans_eq (mul_comm _ _)

lemma IsModelShape.normalized_cap_box {k m : ℕ} {C : Set (Space k × Space m)}
    (hC : IsModelShape C) {R B α : ℝ} {a : Fin k → ℝ}
    (hα : 0 < α) (ha : ∀ i, α ≤ a i)
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R) :
    C ∩ {p | positiveBaseForm a p ≤ B} ⊆
      {s : Space k | ∀ i, s i ∈ Icc 0 (max 1 (B/α))} ×ˢ
      closedBall (0 : Space m) (max 1 (B/α)*R) := by
  rintro ⟨s,y⟩ ⟨hp,hcap⟩
  have hs := hC.support (s,y) hp
  have hb (i : Fin k) : s i ≤ max 1 (B/α) := by
    have hi : α*s i ≤ B := calc
      _ ≤ a i*s i := mul_le_mul_of_nonneg_right (ha i) (hs i)
      _ ≤ ∑ j, a j*s j := Finset.single_le_sum (fun j _ => mul_nonneg (hα.le.trans (ha j)) (hs j)) (Finset.mem_univ i)
      _ ≤ B := by simpa using hcap
    exact ((le_div_iff₀ hα).mpr (by simpa [mul_comm] using hi)).trans (le_max_right _ _)
  exact ⟨fun i => ⟨hs i,hb i⟩,mem_closedBall_zero_iff.mpr
    (hC.fiber_box_bound (le_max_left _ _) hout hb hp)⟩

lemma IsModelShape.normalized_cap_radius {k m : ℕ} {C : Set (Space k × Space m)}
    (hC : IsModelShape C) {R B α : ℝ} {a : Fin k → ℝ}
    (hα : 0 < α) (ha : ∀ i, α ≤ a i)
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R) :
    C ∩ {p | positiveBaseForm a p ≤ B} ⊆
      closedBall 0 (max (Real.sqrt k * max 1 (B/α)) (max 1 (B/α)*R)) := by
  intro p hp
  have hh := hC.normalized_cap_box hα ha hout hp
  rw [mem_closedBall_zero_iff,Prod.norm_def]
  apply max_le_max
  · exact norm_le_sqrt_card_mul_of_coord_le (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (fun i => by rw [abs_of_nonneg (hh.1 i).1]; exact (hh.1 i).2)
  · exact mem_closedBall_zero_iff.mp hh.2

/- Uniform interior ball about (1,0), with an explicit positive radius. -/
theorem LocalDistanceConverges.eventually_normalized_cap_radius
    {k m : ℕ} {Cj : ℕ → Set (Space k × Space m)} {C : Set (Space k × Space m)}
    (h : LocalDistanceConverges Cj C) (hC : IsModelShape C)
    (hclj : ∀ j, IsClosed (Cj j)) (hcvj : ∀ j, Convex ℝ (Cj j))
    (hnej : ∀ j, (Cj j).Nonempty) {R B α : ℝ} {a : Fin k → ℝ}
    (hB : 0 < B) (hα : 0 < α) (ha : ∀ i, α ≤ a i)
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R) :
    ∀ᶠ j in atTop, Cj j ∩ {p | positiveBaseForm a p ≤ B} ⊆
      ball 0 (max (Real.sqrt k * max 1 (B/α)) (max 1 (B/α)*R)+1) := by
  exact h.eventually_caps_radius hC.closed hclj hcvj hnej (positiveBaseForm a) B _
    (hC.normalized_cap_radius hα ha hout) hC.zero_mem (by simpa using hB)

/- Uniform outer fiber bounds on an entire fixed positive box. A single
containing cap gives one index, rather than using pointwise convergence. -/
theorem LocalDistanceConverges.eventually_normalized_fiber_outer
    {k m : ℕ} {Cj : ℕ → Set (Space k × Space m)} {C : Set (Space k × Space m)}
    (h : LocalDistanceConverges Cj C) (hC : IsModelShape C)
    (hclj : ∀ j, IsClosed (Cj j)) (hcvj : ∀ j, Convex ℝ (Cj j))
    (hnej : ∀ j, (Cj j).Nonempty) {R a b : ℝ} (hb : 1 ≤ b)
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R) :
    ∀ᶠ j in atTop, ∀ s : Space k, (∀ i, s i ∈ Icc a b) →
      modelFiber (Cj j) s ⊆ closedBall 0
        (max (Real.sqrt k * max 1 (k*b+1)) (max 1 (k*b+1)*R)+1) := by
  have hB : 0 < (k:ℝ)*b+1 := by
    have : 0 ≤ (k:ℝ)*b := mul_nonneg (Nat.cast_nonneg k) (by linarith)
    linarith
  filter_upwards [h.eventually_normalized_cap_radius hC hclj hcvj hnej
    (a := fun _ => (1:ℝ)) hB zero_lt_one (fun _ => le_rfl) hout]
    with j hj s hs y hy
  have hc : positiveBaseForm (fun _ : Fin k => (1:ℝ)) (s,y) ≤ (k:ℝ)*b+1 := by
    simp only [positiveBaseForm_apply,one_mul]
    have he : ∑ i : Fin k, s i ≤ (k:ℝ)*b := by
      calc
        _ ≤ ∑ _i : Fin k, b := Finset.sum_le_sum (fun i _ => (hs i).2)
        _ = _ := by simp
    linarith
  have hh := mem_ball.mp (hj ⟨hy,hc⟩)
  rw [mem_closedBall_zero_iff]
  exact le_trans (le_max_right ‖s‖ ‖y‖) (by simpa only [div_one,dist_zero_right,Prod.norm_def] using hh.le)

/- Simultaneous two-sided bounds and nonempty fiber interiors. The parameters
in the radii are fixed before an approximating index is chosen. -/
theorem LocalDistanceConverges.eventually_normalized_fibers
    {k m : ℕ} {Cj : ℕ → Set (Space k × Space m)} {C : Set (Space k × Space m)}
    (h : LocalDistanceConverges Cj C) (hC : IsModelShape C)
    (hclj : ∀ j, IsClosed (Cj j)) (hcvj : ∀ j, Convex ℝ (Cj j))
    (hnej : ∀ j, (Cj j).Nonempty) {r R a b : ℝ}
    (hr : 0 < r) (ha : 0 < a) (ha1 : a ≤ 1) (hb : 1 ≤ b)
    (hin : closedBall (0 : Space m) r ⊆
      modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R) :
    ∀ᶠ j in atTop, ∀ s : Space k, (∀ i, s i ∈ Icc a b) →
      closedBall (0 : Space m) (a*r/2) ⊆ modelFiber (Cj j) s ∧
      0 ∈ interior (modelFiber (Cj j) s) ∧
      modelFiber (Cj j) s ⊆ closedBall 0
        (max (Real.sqrt k * max 1 (k*b+1)) (max 1 (k*b+1)*R)+1) := by
  filter_upwards [h.eventually_normalized_fiber_inner hC hclj hcvj hnej hr ha ha1 hin,
    h.eventually_normalized_fiber_outer hC hclj hcvj hnej hb hout] with j hji hjo s hs
  refine ⟨hji s hs,?_,hjo s hs⟩
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset (closedBall_mem_nhds (0 : Space m) (by positivity)) (hji s hs)

/- One explicit interior ball survives in every large approximant. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_RegularFiberDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section RegularFiberDomain
open Metric Filter

lemma regularPositiveFiberDomain_isOpen {k m : ℕ} (C : Set (Space k × Space m)) :
    IsOpen (regularPositiveFiberDomain C) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro s ⟨U,hU,hpos,hs,hreg⟩
  apply Filter.mem_of_superset (hU.mem_nhds hs)
  intro t ht
  exact ⟨U,hU,hpos,ht,hreg⟩

lemma regularPositiveFiberDomain_positive {k m : ℕ} (C : Set (Space k × Space m)) :
    regularPositiveFiberDomain C ⊆ positiveOrthant k := by
  rintro s ⟨_,_,hpos,hs,_⟩
  exact hpos hs

lemma regularPositiveFiberDomain_compact {k m : ℕ} (C : Set (Space k × Space m))
    {s : Space k} (hs : s ∈ regularPositiveFiberDomain C) : IsCompact (modelFiber C s) := by
  obtain ⟨_,_,_,hs,hreg⟩ := hs
  exact (hreg s hs).1

lemma regularPositiveFiberDomain_zero {k m : ℕ} (C : Set (Space k × Space m))
    {s : Space k} (hs : s ∈ regularPositiveFiberDomain C) :
    (0:Space m) ∈ interior (modelFiber C s) := by
  obtain ⟨_,_,_,hs,hreg⟩ := hs
  exact (hreg s hs).2

lemma openBox_subset_regularPositiveFiberDomain {k m : ℕ}
    {C : Set (Space k × Space m)} (hC : IsClosed C) {a b R : ℝ} (ha : 0 < a)
    (hreg : ∀ s : Space k, (∀ i, s i ∈ Icc a b) →
      (0:Space m) ∈ interior (modelFiber C s) ∧ modelFiber C s ⊆ closedBall 0 R) :
    {s : Space k | ∀ i, a < s i ∧ s i < b} ⊆ regularPositiveFiberDomain C := by
  intro s hs
  refine ⟨{s : Space k | ∀ i, a < s i ∧ s i < b},?_,?_,hs,?_⟩
  · rw [Set.ofPred_forall]
    apply isOpen_iInter_of_finite fun i => ?_
    exact (isOpen_lt continuous_const (EuclideanSpace.proj i).continuous).inter
      (isOpen_lt (EuclideanSpace.proj i).continuous continuous_const)
  · intro t ht i
    exact ha.trans (ht i).1
  · intro t ht
    have hh := hreg t (fun i => ⟨(ht i).1.le,(ht i).2.le⟩)
    refine ⟨(isCompact_closedBall _ _).of_isClosed_subset ?_ hh.2,hh.1⟩
    exact hC.preimage (continuous_const.prodMk continuous_id)

/-- Every fixed logarithmic box is eventually available in a normalized-model
approximation. The regular domains are produced from the actual fibers. -/
theorem LocalDistanceConverges.eventually_regular_logBox
    {k m : ℕ} {Cj : ℕ → Set (Space k × Space m)} {C : Set (Space k × Space m)}
    (h : LocalDistanceConverges Cj C) (hC : IsModelShape C)
    (hclj : ∀ j, IsClosed (Cj j)) (hcvj : ∀ j, Convex ℝ (Cj j))
    (hnej : ∀ j, (Cj j).Nonempty) {r R : ℝ} (hr : 0 < r)
    (hin : closedBall (0 : Space m) r ⊆
      modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R)
    (T : ℕ) : ∀ᶠ j in atTop,
      logarithmicBox k T ⊆ logSpace '' regularPositiveFiberDomain (Cj j) := by
  have ha : 0 < Real.exp (-(T:ℝ)-1) := Real.exp_pos _
  have ha1 : Real.exp (-(T:ℝ)-1) ≤ 1 := Real.exp_le_one_iff.mpr (by have : (0:ℝ) ≤ T := Nat.cast_nonneg T; linarith)
  have hb : 1 ≤ Real.exp ((T:ℝ)+1) := Real.one_le_exp_iff.mpr (by positivity)
  have hh := h.eventually_normalized_fibers hC hclj hcvj hnej hr ha ha1 hb hin hout
  filter_upwards [hh] with j hj
  intro t ht
  refine ⟨expSpace t,?_,logSpace_expSpace t⟩
  apply openBox_subset_regularPositiveFiberDomain (hclj j) ha
    (fun s hs => (hj s hs).2)
  intro i
  obtain ⟨hl,hu⟩ := abs_le.mp (ht i)
  change Real.exp (-(T:ℝ)-1) < Real.exp (t i) ∧ Real.exp (t i) < Real.exp ((T:ℝ)+1)
  exact ⟨Real.exp_lt_exp.mpr (by linarith),Real.exp_lt_exp.mpr (by linarith)⟩
end RegularFiberDomain

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualLogMeasureFurther
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Filter Metric
open scoped Topology

/- The quantifier order in bounds.tex: every finite box has its own eventual
index. No common threshold for infinitely many boxes is needed. -/

theorem logarithmicBox_isClosed (k : ℕ) (L : ℝ) : IsClosed (logarithmicBox k L) := by
  convert isClosed_iInter (fun i : Fin k => isClosed_le ((EuclideanSpace.proj i).continuous.abs)
    (show Continuous (fun _ : Space k => L) from continuous_const)) using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp [logarithmicBox]

theorem logarithmicBox_isCompact (k : ℕ) (L : ℝ) : IsCompact (logarithmicBox k L) := by
  have h : IsCompact (Set.pi univ (fun _ : Fin k => Icc (-L) L)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have he : logarithmicBox k L = (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)) ⁻¹'
      (Set.pi univ (fun _ : Fin k => Icc (-L) L)) := by
    ext x
    simp only [logarithmicBox,mem_ofPred_eq,mem_preimage,Set.mem_pi,mem_univ,true_implies,mem_Icc]
    exact forall_congr' (fun i => abs_le)
  rw [he]
  exact (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).isCompact_preimage.mpr h

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualLogGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter Metric
open scoped Topology

open Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

lemma affineEpigraphLogMeasure_box_finite {n k : ℕ}
    {μ : Measure (Space k)} [μ.IsAddHaarMeasure]
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (Space k × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set (Space k)} (hD : IsOpen D) (hDpos : D ⊆ positiveOrthant k)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) {R : ℝ}
    (hR : logarithmicBox k R ⊆ logSpace '' D) :
    affineEpigraphLogMeasure μ D Ω u a L bE (logarithmicBox k R) ≠ ⊤ := by
  obtain ⟨hM,hT,-⟩ := affineEpigraph_logWeight_regular hΩ hcv hu hp a L hD hDpos hK hzero bE
  exact (logTubeMeasure_compact_lt_top hDpos (hM.mul hT)
    (logarithmicBox_isCompact k R) hR).ne

/- The growth contradiction is now specialized to genuine affine-maximal
approximate graphs. Only the two remaining quantitative model bounds are inputs:
positive mass on one fixed box and a uniform polynomial upper bound. Every
Poincare estimate and local finiteness assertion is derived here. -/

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_UniformSphericalCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open intervalIntegral
open scoped Pointwise

open Filter
open scoped Topology
/- Every admissible graph path has at least the Euclidean length of its
base displacement. This uses the literal C¹-path definition of completeness. -/
theorem enorm_sub_le_graphEDist {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (x y : Space n) : ‖y - x‖ₑ ≤ graphEDist Ω u x y := by
  apply le_iInf
  intro γ
  apply le_iInf
  intro hγ
  apply le_iInf
  intro hγΩ
  apply le_iInf
  intro hγ0
  apply le_iInf
  intro hγ1
  have hl := enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hγ (show (0 : ℝ) ≤ 1 by norm_num)
  rw [hγ1, hγ0] at hl
  apply hl.trans
  apply lintegral_mono
  intro t
  dsimp only
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    (le_add_of_nonneg_right (sq_nonneg _))

/- A straight base segment has constant velocity, including its endpoints
for the closed-interval derivative used in the metric. -/
theorem derivWithin_baseSegment {n : ℕ} (x v : Space n) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    derivWithin (fun s : ℝ => x + s • v) (Icc (0 : ℝ) 1) t = v := by
  have hd := ((hasDerivAt_id t).smul_const v).const_add x
  simpa using hd.hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num) t ht)

/- Length estimate on a segment on which the graph height is nondecreasing. -/
theorem graphEDist_le_of_segment_deriv_nonneg {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (x y : Space n) (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ Ω)
    (hp : ∀ t ∈ Icc (0 : ℝ) 1,
      0 ≤ fderiv ℝ u (x + t • (y - x)) (y - x)) :
    graphEDist Ω u x y ≤ ENNReal.ofReal (‖y - x‖ + (u y - u x)) := by
  let γ : ℝ → Space n := fun t => x + t • (y - x)
  let d : ℝ → ℝ := fun t => fderiv ℝ u (γ t) (y - x)
  have hγ : ContDiff ℝ ∞ γ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hγd (t : ℝ) : HasDerivAt γ (y - x) t := by
    simpa [γ] using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have hdu (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (u ∘ γ) (d t) t :=
    ((hu.contDiffAt (hΩ.mem_nhds (hseg t ht))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (hγd t)
  have hd : ContinuousOn d (Icc (0 : ℝ) 1) := by
    intro t ht
    have hc : ContinuousAt (fderiv ℝ u) (γ t) :=
      ((hu.contDiffAt (hΩ.mem_nhds (hseg t ht))).fderiv_right
        (m := ∞) (by simp)).continuousAt
    have hc' : ContinuousAt (fun t => fderiv ℝ u (γ t)) t :=
      hc.comp hγ.continuous.continuousAt
    exact (hc'.clm_apply continuousAt_const).continuousWithinAt
  have hid : IntegrableOn d (Icc (0 : ℝ) 1) := hd.integrableOn_Icc
  have hic : IntegrableOn (fun _ : ℝ => ‖y - x‖) (Icc (0 : ℝ) 1) :=
    continuousOn_const.integrableOn_Icc
  have hi : IntegrableOn (fun t => ‖y - x‖ + d t) (Icc (0 : ℝ) 1) :=
    hic.add hid
  have hftc : ∫ t in Icc (0 : ℝ) 1, d t = u y - u x := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
      (fun t ht => hdu t (by simpa using ht))
      ((by simpa using hd : ContinuousOn d (uIcc (0 : ℝ) 1)).intervalIntegrable)
    simpa [γ, Function.comp_def] using he
  have hl : graphPathLength u γ ≤ ENNReal.ofReal (‖y - x‖ + (u y - u x)) := by
    unfold graphPathLength
    calc
      _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (‖y - x‖ + d t) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        rw [show derivWithin γ (Icc (0 : ℝ) 1) t = y - x from derivWithin_baseSegment x (y - x) ht]
        apply ENNReal.ofReal_le_ofReal
        dsimp only [d, γ]
        apply Real.sqrt_le_iff.mpr
        constructor
        · exact add_nonneg (norm_nonneg _) (hp t ht)
        · nlinarith [norm_nonneg (y - x), hp t ht]
      _ = ENNReal.ofReal (∫ t in Icc (0 : ℝ) 1, (‖y - x‖ + d t)) := by
        symm
        apply ofReal_integral_eq_lintegral_ofReal hi
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact add_nonneg (norm_nonneg _) (hp t ht)
      _ = _ := by
        rw [integral_add hic hid,
          setIntegral_const, hftc]
        simp
  have hdist : graphEDist Ω u x y ≤ graphPathLength u γ := by
    unfold graphEDist
    exact iInf_le_of_le γ (iInf_le_of_le (hγ.of_le (by simp)).contDiffOn
      (iInf_le_of_le hseg (iInf_le_of_le (by simp [γ])
        (iInf_le_of_le (by simp [γ]) le_rfl))))
  exact hdist.trans hl

/- Coordinate entries coincide with the actual second Fréchet differential. -/
/- The standing positive-Hessian hypothesis implies genuine convexity on
 the original open convex domain; this is not an additional hypothesis. -/
theorem graphEDist_le_segment_monotone {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (x y : Space n) (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ Ω)
    (hm : MonotoneOn (fun t : ℝ => u (x + t • (y - x))) (Icc (0 : ℝ) 1)) :
    graphEDist Ω u x y ≤ ENNReal.ofReal (‖y - x‖ + |u y - u x|) := by
  apply (graphEDist_le_of_segment_deriv_nonneg hΩ hu x y hseg ?_).trans
  · exact ENNReal.ofReal_le_ofReal (add_le_add_right (le_abs_self _) _)
  · intro t ht
    have hd : HasDerivAt (fun t : ℝ => u (x + t • (y - x)))
        (fderiv ℝ u (x + t • (y - x)) (y - x)) t := by
      have hγ : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) t := by
        simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
      exact ((hu.contDiffAt (hΩ.mem_nhds (hseg t ht))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hγ
    rw [← hd.hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1) t ht)]
    exact hm.derivWithin_nonneg

theorem graphEDist_le_segment_antitone {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (x y : Space n) (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ Ω)
    (hm : AntitoneOn (fun t : ℝ => u (x + t • (y - x))) (Icc (0 : ℝ) 1)) :
    graphEDist Ω u x y ≤ ENNReal.ofReal (‖y - x‖ + |u y - u x|) := by
  have he := graphEDist_le_segment_monotone hΩ hu.neg x y hseg hm.neg
  change graphEDist Ω (-u) x y ≤ ENNReal.ofReal
    (‖y - x‖ + |(-u) y - (-u) x|) at he
  simpa only [graphEDist_neg, Pi.neg_apply, neg_sub_neg, abs_sub_comm] using he

open Filter
open scoped Topology

/- Intrinsic convergence always entails convergence of base points. -/
theorem tendsto_of_graphEDist {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    {x : ℕ → Space n} {a : Space n}
    (ha : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N,
      graphEDist Ω u (x i) a < ENNReal.ofReal ε) :
    Tendsto x atTop (𝓝 a) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  refine ⟨N, fun i hi => ?_⟩
  have h := (enorm_sub_le_graphEDist Ω u (x i) a).trans_lt (hN i hi)
  rw [← ofReal_norm] at h
  have h' := (ENNReal.ofReal_lt_ofReal_iff hε).mp h
  simpa [dist_eq_norm, norm_sub_rev] using h'

/- Completeness prevents a finite base endpoint from being lost when graph
paths make a sequence intrinsically Cauchy. -/
theorem mem_of_complete_graph_cauchy {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hc : EuclideanGraphComplete Ω u) {x : ℕ → Space n} {a : Space n}
    (hx : ∀ i, x i ∈ Ω) (ha : Tendsto x atTop (𝓝 a))
    (hC : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      graphEDist Ω u (x i) (x j) < ENNReal.ofReal ε) : a ∈ Ω := by
  obtain ⟨b, hb, hxb⟩ := hc x hx hC
  exact (tendsto_nhds_unique ha (tendsto_of_graphEDist hxb)) ▸ hb

/- A chord bound along a family of segments turns ordinary Cauchy control of
base and height into control for the actual graph metric. -/
theorem graph_cauchy_of_segment_bound {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    {x : ℕ → Space n} (hx : CauchySeq x) (hu : CauchySeq (u ∘ x))
    (hbound : ∀ i j, graphEDist Ω u (x i) (x j) ≤
      ENNReal.ofReal (‖x j - x i‖ + |u (x j) - u (x i)|)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      graphEDist Ω u (x i) (x j) < ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hx (ε / 2) (half_pos hε)
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff.mp hu (ε / 2) (half_pos hε)
  refine ⟨max N M, fun i hi j hj => (hbound i j).trans_lt ?_⟩
  apply (ENNReal.ofReal_lt_ofReal_iff hε).mpr
  have hx' : ‖x j - x i‖ < ε / 2 := by
    simpa [dist_eq_norm] using hN j (le_trans (le_max_left _ _) hj) i
      (le_trans (le_max_left _ _) hi)
  have hu' : |u (x j) - u (x i)| < ε / 2 := by
    simpa [Function.comp_def, Real.dist_eq] using hM j
      (le_trans (le_max_right _ _) hj) i (le_trans (le_max_right _ _) hi)
  linarith

/- Restricting a monotone-height ray to any oriented subsegment gives the
uniform chord bound used to exhibit an intrinsic Cauchy tail. -/
theorem graphEDist_le_on_monotone_ray {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (a v : Space n) (q : ℝ)
    (hseg : ∀ t ∈ Ico q 1, a + t • v ∈ Ω)
    (hm : MonotoneOn (fun t : ℝ => u (a + t • v)) (Ico q 1) ∨
      AntitoneOn (fun t : ℝ => u (a + t • v)) (Ico q 1))
    {s r : ℝ} (hs : s ∈ Ico q 1) (hr : r ∈ Ico q 1) :
    graphEDist Ω u (a + s • v) (a + r • v) ≤
      ENNReal.ofReal (‖(a + r • v) - (a + s • v)‖ +
        |u (a + r • v) - u (a + s • v)|) := by
  have heq (t : ℝ) : (a + s • v) + t • ((a + r • v) - (a + s • v)) =
      a + (s + t * (r - s)) • v := by module
  have hmap (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : s + t * (r - s) ∈ Ico q 1 := by
    simpa [smul_eq_mul] using (convex_Ico q (1 : ℝ)).add_smul_mem hs
      (by simpa using hr) ht
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (a + s • v) + t • ((a + r • v) - (a + s • v)) ∈ Ω := by
    rw [heq]
    exact hseg _ (hmap t ht)
  rcases hm with hm | hm
  · by_cases hsr : s ≤ r
    · apply graphEDist_le_segment_monotone hΩ hu _ _ hpath
      intro t ht w hw htw
      simp only [heq]
      apply hm (hmap t ht) (hmap w hw)
      nlinarith
    · apply graphEDist_le_segment_antitone hΩ hu _ _ hpath
      intro t ht w hw htw
      simp only [heq]
      apply hm (hmap w hw) (hmap t ht)
      nlinarith
  · by_cases hsr : s ≤ r
    · apply graphEDist_le_segment_antitone hΩ hu _ _ hpath
      intro t ht w hw htw
      simp only [heq]
      apply hm (hmap t ht) (hmap w hw)
      nlinarith
    · apply graphEDist_le_segment_monotone hΩ hu _ _ hpath
      intro t ht w hw htw
      simp only [heq]
      apply hm (hmap w hw) (hmap t ht)
      nlinarith

/- A bounded ray with monotone graph height cannot end at a missing finite
base point of a complete graph. This proves the metric step rather than
assuming properness of the embedding. -/
theorem endpoint_mem_of_bounded_monotone_ray {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hc : EuclideanGraphComplete Ω u) (a b : Space n) {q : ℝ} (hq : q < 1)
    (hseg : ∀ t ∈ Ico q 1, a + t • (b - a) ∈ Ω)
    (hm : MonotoneOn (fun t : ℝ => u (a + t • (b - a))) (Ico q 1) ∨
      AntitoneOn (fun t : ℝ => u (a + t • (b - a))) (Ico q 1))
    (hbdd : ∃ C : ℝ, ∀ t ∈ Ico q 1, |u (a + t • (b - a))| ≤ C) : b ∈ Ω := by
  obtain ⟨t, htm, htmem, htlim⟩ := exists_seq_strictMono_tendsto' hq
  have ht (i : ℕ) : t i ∈ Ico q 1 := ⟨(htmem i).1.le, (htmem i).2⟩
  let x : ℕ → Space n := fun i => a + t i • (b - a)
  have hx (i : ℕ) : x i ∈ Ω := hseg _ (ht i)
  have hxlim : Tendsto x atTop (𝓝 b) := by
    have he := (tendsto_const_nhds (x := a)).add (htlim.smul_const (b - a))
    simpa [x] using he
  obtain ⟨C, hC⟩ := hbdd
  have hxheight : CauchySeq (u ∘ x) := by
    rcases hm with hm | hm
    · have hmono : Monotone (u ∘ x) := fun i j hij => hm (ht i) (ht j) (htm.monotone hij)
      have hbounded : BddAbove (range (u ∘ x)) := by
        refine ⟨C, ?_⟩
        rintro v ⟨i, rfl⟩
        exact (le_abs_self _).trans (hC _ (ht i))
      exact (tendsto_atTop_ciSup hmono hbounded).cauchySeq
    · have hanti : Antitone (u ∘ x) := fun i j hij => hm (ht i) (ht j) (htm.monotone hij)
      have hbounded : BddBelow (range (u ∘ x)) := by
        refine ⟨-C, ?_⟩
        rintro v ⟨i, rfl⟩
        exact (neg_le_neg (hC _ (ht i))).trans (neg_abs_le _)
      exact (tendsto_atTop_ciInf hanti hbounded).cauchySeq
  apply mem_of_complete_graph_cauchy hc hx hxlim
  apply graph_cauchy_of_segment_bound hxlim.cauchySeq hxheight
  intro i j
  exact graphEDist_le_on_monotone_ray hΩ hu a (b - a) q hseg hm (ht i) (ht j)

/- A differentiable convex function on a finite half-open interval has a
monotone tail (in one of the two orientations). -/
theorem convexOn_monotone_tail {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ico (0 : ℝ) 1) f)
    (hd : ∀ t ∈ Ico (0 : ℝ) 1, DifferentiableAt ℝ f t) :
    ∃ q ∈ Ico (0 : ℝ) 1, MonotoneOn f (Ico q 1) ∨ AntitoneOn f (Ico q 1) := by
  by_cases hex : ∃ q ∈ Ico (0 : ℝ) 1, 0 ≤ deriv f q
  · obtain ⟨q, hq, hqp⟩ := hex
    refine ⟨q, hq, Or.inl ?_⟩
    have hsub : Ico q 1 ⊆ Ico (0 : ℝ) 1 := fun t ht => ⟨hq.1.trans ht.1, ht.2⟩
    apply monotoneOn_of_deriv_nonneg (convex_Ico _ _)
      (fun t ht => (hd t (hsub ht)).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (hsub (interior_subset ht))).differentiableWithinAt)
    intro t ht
    exact hqp.trans (hf.monotoneOn_deriv hd hq (hsub (interior_subset ht))
      (interior_subset ht).1)
  · refine ⟨0, by norm_num, Or.inr ?_⟩
    apply antitoneOn_of_deriv_nonpos (convex_Ico _ _)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).differentiableWithinAt)
    intro t ht
    exact le_of_lt (lt_of_not_ge (fun h => hex ⟨t, interior_subset ht, h⟩))

/- The tangent line at the initial point bounds a convex ray from below,
so an upper bound on a finite ray implies a two-sided bound. -/
theorem convexOn_bounded_ray {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ico (0 : ℝ) 1) f)
    (hd : DifferentiableAt ℝ f 0) {A : ℝ} (hA : ∀ t ∈ Ico (0 : ℝ) 1, f t ≤ A) :
    ∃ C : ℝ, ∀ t ∈ Ico (0 : ℝ) 1, |f t| ≤ C := by
  refine ⟨|A| + |f 0| + |deriv f 0|, ?_⟩
  intro t ht
  have hs : f 0 + t * deriv f 0 ≤ f t := by
    rcases eq_or_lt_of_le ht.1 with he | he
    · subst t
      simp
    · have h := hf.le_slope_of_hasDerivAt (by norm_num) ht he hd.hasDerivAt
      simp only [slope_def_field, sub_zero] at h
      have h' := (le_div_iff₀ he).mp h
      linarith
  have hp : -|deriv f 0| ≤ t * deriv f 0 := by
    calc
      _ ≤ t * (-|deriv f 0|) := by nlinarith [abs_nonneg (deriv f 0), ht.2]
      _ ≤ _ := mul_le_mul_of_nonneg_left (neg_abs_le _) ht.1
  apply abs_le.mpr
  constructor
  · have h0 := neg_abs_le (f 0)
    have hAA := abs_nonneg A
    linarith
  · exact (hA t ht).trans (by linarith [le_abs_self A, abs_nonneg (f 0), abs_nonneg (deriv f 0)])

/- Completeness forbids any bounded convex ray from reaching a missing finite
endpoint. Convexity and two-sided variation, not a growth hypothesis, produce
the required metric Cauchy sequence. -/
theorem endpoint_mem_of_bounded_convex_ray {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hcv : ConvexOn ℝ Ω u) (hc : EuclideanGraphComplete Ω u) (a b : Space n)
    (hseg : ∀ t ∈ Ico (0 : ℝ) 1, a + t • (b - a) ∈ Ω)
    (hbounded : ∃ A : ℝ, ∀ t ∈ Ico (0 : ℝ) 1, u (a + t • (b - a)) ≤ A) : b ∈ Ω := by
  let f : ℝ → ℝ := fun t => u (a + t • (b - a))
  have hfc : ConvexOn ℝ (Ico (0 : ℝ) 1) f := by
    have hh := (hcv.comp_affineMap (AffineMap.lineMap a b)).subset
      (s := Ico (0 : ℝ) 1) (fun t ht => ?_) (convex_Ico _ _)
    · simpa [f, Function.comp_def, AffineMap.lineMap_apply, add_comm] using hh
    · simpa [AffineMap.lineMap_apply, add_comm] using hseg t ht
  have hfd (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : DifferentiableAt ℝ f t := by
    have hγ : HasDerivAt (fun t : ℝ => a + t • (b - a)) (b - a) t := by
      simpa using ((hasDerivAt_id t).smul_const (b - a)).const_add a
    exact (((hu.contDiffAt (hΩ.mem_nhds (hseg t ht))).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hγ).differentiableAt
  obtain ⟨A, hA⟩ := hbounded
  obtain ⟨C, hC⟩ := convexOn_bounded_ray hfc (hfd 0 (by norm_num)) hA
  obtain ⟨q, hq, hm⟩ := convexOn_monotone_tail hfc hfd
  have hsub : Ico q 1 ⊆ Ico (0 : ℝ) 1 := fun t ht => ⟨hq.1.trans ht.1, ht.2⟩
  exact endpoint_mem_of_bounded_monotone_ray hΩ hu hc a b hq.2
    (fun t ht => hseg t (hsub ht)) hm ⟨C, fun t ht => hC t (hsub ht)⟩

/- The metric obstruction applied to an arbitrary bounded-height sequence,
not merely points already lying on a fixed ray. This is the core boundary
properness argument in geometry.tex:36–55. -/
theorem mem_of_bounded_graph_sequence {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hcv : ConvexOn ℝ Ω u) (hc : EuclideanGraphComplete Ω u)
    {a : Space n} (ha : a ∈ Ω) {x : ℕ → Space n} {b : Space n}
    (hx : ∀ i, x i ∈ Ω) (hlim : Tendsto x atTop (𝓝 b))
    {A : ℝ} (hA : ∀ i, u (x i) ≤ A) : b ∈ Ω := by
  have hb : b ∈ closure Ω := mem_closure_iff_seq_limit.mpr ⟨x, hx, hlim⟩
  have hseg (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : a + t • (b - a) ∈ Ω := by
    have hh := hcv.1.combo_interior_closure_mem_interior
      (show a ∈ interior Ω by simpa [hΩ.interior_eq] using ha) hb
      (sub_pos.mpr ht.2) ht.1 (show (1 - t) + t = 1 by ring)
    have he : (1 - t) • a + t • b = a + t • (b - a) := by module
    rw [he, hΩ.interior_eq] at hh
    exact hh
  apply endpoint_mem_of_bounded_convex_ray hΩ hu hcv hc a b hseg
  refine ⟨max (u a) A, ?_⟩
  intro t ht
  have hzlim : Tendsto (fun i => a + t • (x i - a)) atTop
      (𝓝 (a + t • (b - a))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.smul (hlim.sub tendsto_const_nhds))
  have hulim := (hu.continuousOn.continuousAt (hΩ.mem_nhds (hseg t ht))).tendsto.comp hzlim
  apply le_of_tendsto' hulim
  intro i
  have hv := hcv.2 ha (hx i) (sub_nonneg.mpr ht.2.le) ht.1
    (show (1 - t) + t = 1 by ring)
  have he : (1 - t) • a + t • x i = a + t • (x i - a) := by module
  rw [he] at hv
  calc
    _ ≤ (1 - t) * u a + t * u (x i) := hv
    _ ≤ (1 - t) * max (u a) A + t * max (u a) A :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr ht.2.le))
        (mul_le_mul_of_nonneg_left ((hA i).trans (le_max_right _ _)) ht.1)
    _ = _ := by ring

/- Actual height sublevels are closed in the ambient base space. No convex
extension of u to missing boundary points is used. -/
theorem isClosed_epigraph_of_complete {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hcv : ConvexOn ℝ Ω u)
    (hc : EuclideanGraphComplete Ω u) :
    IsClosed {p : Space n × ℝ | p.1 ∈ Ω ∧ u p.1 ≤ p.2} := by
  apply isClosed_of_closure_subset
  intro p hp
  obtain ⟨z, hz, hlim⟩ := mem_closure_iff_seq_limit.mp hp
  obtain ⟨a, ha⟩ := hne
  obtain ⟨A, hA⟩ := hlim.snd_nhds.bddAbove_range
  have hpΩ : p.1 ∈ Ω := mem_of_bounded_graph_sequence hΩ hu hcv hc ha
    (fun i => (hz i).1) hlim.fst_nhds (fun i => (hz i).2.trans (hA (mem_range_self i)))
  refine ⟨hpΩ, ?_⟩
  apply le_of_tendsto_of_tendsto
    ((hu.continuousOn.continuousAt (hΩ.mem_nhds hpΩ)).tendsto.comp hlim.fst_nhds) hlim.snd_nhds
  exact Eventually.of_forall fun i => (hz i).2

-- END

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_CompletePositiveCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open intervalIntegral
open scoped Pointwise
open Filter
open scoped Topology
open Filter
open scoped Topology

section CompletePositiveCap

lemma sourceEpigraph_convex {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef) :
    Convex ℝ (sourceEpigraph Ω u) :=
  (convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)).convex_epigraph

lemma sourceEpigraph_closed {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) : IsClosed (sourceEpigraph Ω u) :=
  isClosed_epigraph_of_complete hΩ hne hu
    (convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)) hc

end CompletePositiveCap

open Metric
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma affineEpigraphPullback_isClosed {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hc : IsClosed (sourceEpigraph Ω u)) (a : Space n × ℝ)
    (L : (S × E) ≃L[ℝ] (Space n × ℝ)) : IsClosed (affineEpigraphPullback Ω u a L) :=
  hc.preimage (continuous_const.add L.continuous)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_PositiveMassAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

lemma ofReal_integral_le_lintegral_of_nonneg {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} (hf : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hi : Integrable f μ
  · exact (ofReal_integral_eq_lintegral_ofReal hi hf).le
  · simp [integral_undef hi]

lemma exists_pos_lower_of_rpow {B : ℝ≥0∞} (hB : B ≠ ⊤) {c p : ℝ}
    (hc : 0 < c) (hp : 0 < p) :
    ∃ δ > 0, ∀ M : ℝ≥0∞, ENNReal.ofReal c ≤ B * M^p → ENNReal.ofReal δ ≤ M := by
  let b : ℝ := B.toReal+1
  have hb : 0 < b := by dsimp [b]; positivity
  have hBb : B ≤ ENNReal.ofReal b := by
    rw [← ENNReal.ofReal_toReal hB]
    exact ENNReal.ofReal_le_ofReal (by dsimp [b]; linarith)
  refine ⟨(c/b)^p⁻¹,Real.rpow_pos_of_pos (div_pos hc hb) _,?_⟩
  intro M hM
  rw [← ENNReal.ofReal_rpow_of_pos (div_pos hc hb),ENNReal.rpow_inv_le_iff hp]
  rw [ENNReal.ofReal_div_of_pos hb]
  apply (ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hb)) (by simp)).mpr
  exact hM.trans ((mul_le_mul_left hBb _).trans_eq (mul_comm _ _))

lemma logTubeMeasure_cell_le_apply {k : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure (Space k)) [SFinite μ] (D : Set (Space k)) (F : Space k × E → ℝ)
    {K Q : Set (Space k)} (hK : MeasurableSet K)
    (hsub : Q ⊆ D ∩ logSpace ⁻¹' K) :
    (∫⁻ q : Space k × Metric.sphere (0:E) 1, ENNReal.ofReal (F (tubeLift q))
        ∂(μ.restrict Q).prod (volume : Measure E).toSphere) ≤ logTubeMeasure μ D F K := by
  have hmap : Measurable (fun q : Space k × Metric.sphere (0:E) 1 => logSpace q.1) :=
    measurable_logSpace.comp measurable_fst
  rw [logTubeMeasure,Measure.map_apply hmap hK,
    withDensity_apply _ (hK.preimage hmap),Measure.restrict_restrict (hK.preimage hmap),
    Measure.restrict_prod_eq_prod_univ]
  apply lintegral_mono_set
  rintro q ⟨hq,-⟩
  exact ⟨(hsub hq).2,(hsub hq).1,Set.mem_univ _⟩

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

/- Coordinate Hessian. On the open domain it depends only on the restriction of `u`.
The order of the two differentiations is immaterial under the smoothness hypothesis. -/
/- The coefficient U^{ij} = det(D²u) (D²u)^{-1}_{ij}. -/
/- The classical determinant weight; in particular, this is not a generalized exponent. -/
/- Length on [0,1] for g_x(v,v) = ‖v‖² + (Du_x v)², the metric induced
by the Euclidean graph embedding x ↦ (x,u(x)). The product norm on Lean's ordinary
product type is NOT used (it would be the maximum norm). -/
/- The intrinsic extended distance: infimum of lengths of C¹ paths in the domain.
Using a single C¹ path gives the same intrinsic distance as piecewise C¹ paths,
by smooth endpoint reparameterization and concatenation. -/
/- Sequential completeness for the induced Euclidean path metric. This states
that every intrinsic Cauchy sequence of points in Ω has an intrinsic limit in Ω.
It imposes no growth condition and no completeness condition on the affine metric. -/
/- The graph, regarded as an affine subset of R^{n+1}. -/
/-!
The first missing differential identity in `sections/area.tex`, Stationarity:
the cofactor of an actual Hessian is divergence-free.  The proof below uses
multilinearity of the determinant and symmetry of second derivatives (Piola).
-/

/- The determinant, as a continuous map multilinear in its rows. -/
/- Exchanging two independently replaced rows reverses the determinant. -/
/- Expand one determinant row in the coordinate vectors. -/
/- Symmetric coefficients contract to zero with an alternating pair of rows. -/
/- The algebraic cancellation underlying the Piola identity. -/

/- Rows of the derivative of a list of scalar functions, in fixed directions. -/
/- Differentiate a cofactor by differentiating each of its unfrozen rows. -/
/- Piola's identity in fixed directions; it uses only equality of mixed partials. -/

/- Smoothness through order three suffices for the cofactor cancellation. -/
/- For an invertible Hessian, the manuscript's definition is exactly the adjugate. -/
/- The Hessian cofactor is symmetric under the standing positivity hypothesis. -/
/- Both divergences of the actual coefficient matrix vanish on the original domain. -/

/- The frozen coordinate Hessian has smooth entries at every interior smooth point. -/
/- Determinants of the actual Hessian are smooth, by row multilinearity. -/
/- Polynomial cofactor entries are smooth even before invertibility is used. -/
/- Smoothness of U on its actual open domain, with no extension hypothesis. -/
/- The real determinant weight has its original exponent throughout the proof. -/

/- A fixed-direction derivative, used only as notation for the actual Fréchet derivative. -/
/- The differential part of the double integration by parts. Both zero
cofactor divergences are used; they will be supplied by the proved Piola identity. -/

/- The exact maximal-graph operator is the double divergence of its variational coefficient. -/

/- Integrability uses continuity only on a compact set containing the support. -/
/- Compact support of the test function removes any global regularity requirement
on the coefficient. This is the integration-by-parts form used on the original Ω. -/
/- Two integrations by parts, without an artificial globally smooth coefficient. -/
/- Global smoothness of a fixed-direction derivative. -/
/- The weak double-divergence formula with precisely a compactly supported test. -/

/- Graph-direction stationarity for the source's equation and actual coefficient.
All regularity of `u` is needed only on the original open domain. -/
/- The density of affine area in the original graph coordinates. -/
/- The variation coefficient has exactly the exponent in the manuscript. -/
/- `wU` is not a surrogate for the affine-area coefficient. -/
/- The source's first-variation integral, over its original open domain. -/

/- Jacobi's formula without assuming invertibility of the varied matrix. -/
/- Pointwise first variation of the actual affine-area density. -/

/- Away from topological support the test is locally zero, so no extension
of a smooth coefficient across the original boundary is necessary. -/
/- Commuting fixed-direction differentiation with evaluation of a derivative. -/
/- Symmetry of the second derivative in fixed directions. -/
/- The support-plane height `ν(o-X)` in original graph coordinates. -/
/- Smoothness holds only locally; the eventual zero argument handles tests. -/
/- The derivative of the radial gradient, including its moving vector argument. -/
/- The cancellation `D Z = H(x-o)` with no coordinate or global extension assumption. -/
/- The exact second derivative of the support-plane height. -/

/- The coordinate version used in the trace of the cap test. -/
/- Jacobi's formula in arbitrary fixed directions, for the actual entries. -/
/- Smoothness of the area density on the original domain. -/
/- The exact differential of the affine area coefficient. -/
/- Trace of the identity, in the entry convention used in the manuscript. -/
/- Weighted radial trace, avoiding a logarithm at points outside the domain. -/
/- Expansion in the frozen Euclidean coordinate vectors. -/
/- Linear functionals are recovered exactly by coordinates. -/
/- The radial vector derivative is the sum of its coordinate derivatives. -/
/- A second derivative product rule on the actual open domain. -/
/- Scalar composition by its actual one-dimensional derivative. -/
/- The second chain rule used by a cap test. -/
/- Restriction of an arbitrary ambient affine function to the original graph. -/
/- Coordinate pairing equals the ordinary matrix-vector contraction. -/
/- Symmetry of the covector contraction, with the literal matrix coefficients. -/
/- Exact inverse contraction for a radial vector and a covector. -/
/- The radial support gradient cancels exactly against the inverse Hessian. -/
/- Product trace in coordinates. -/
/- Chain trace in coordinates. -/
/- Positivity fixes the inverse-Hessian symmetry employed in a cap test. -/
/- Pointwise first-variation integrand of the source cap test. -/
/- Cancellation of the affine coefficients in the first variation. -/
/- The actual coordinate functional through the Euclidean-space equivalence. -/
/- A smooth compact test makes a merely locally smooth coefficient globally smooth. -/
/- Integral of a derivative of a smooth compactly supported scalar field. -/
/- Radial integration by parts with a compact test and no global extension of `f`.
This formulation gives integrability as well as the identity. -/
/- Zero-extension of a compactly supported local test is genuinely smooth on the
ambient coordinate space; no extension theorem for the graph is needed. -/
/- Hessians depend only on the germ of a function, also with the total derivative
convention at points outside the domain. -/
/- The actual first-variation density is integrable for a compact local test. -/
/- The cap identity in the original graph coordinates (source `area.tex`,
Lemma Cap identity). The source assumes compact support of all three displayed
scalar compositions; this proof in fact only needs the first support condition.
The measure here is precisely affine area density times Lebesgue measure. -/

/- Weighted arithmetic-geometric mean for the eigenvalues, with the unused
weight placed at 1. This is the determinant-power supporting inequality at I. -/
/- Congruence by the inverse positive square root converts the determinant
ratio and the mixed trace to the same positive semidefinite matrix. -/
/- Concavity in its precise tangent form, for all exponents in [0,1/n]. -/

/- On an open set the Hessian is additive; no extension outside that set is used. -/
/- The actual determinant density obeys its supporting-hyperplane inequality. -/
/- Density differences for a compactly supported perturbation really are
integrable, although each area on an unbounded domain could be infinite. -/
/- Local maximization of graph affine area: the integrated form used in
`bounds.tex:99–126`. It is deduced from the PDE, not assumed as stability. -/
/- The affine pullback uses the continuous map associated with the actual
matrix, so its determinant and nonsingularity have their usual meanings. -/
/- First derivative of composition with an affine base change. -/
/- The Hessian chain rule, retaining the exact order Bᵀ H B. -/
/- Multiplying heights by a scalar multiplies the actual Hessian by it. -/
/- Nonsingular congruence and positive scalar multiplication preserve strict
ellipticity. The condition on B is exactly invertibility, not orthogonality. -/
/- Exact determinant normalization used for rescaled sections. -/
/- The trace contraction is invariant under simultaneous congruence, with the
exact scalar ratio. This is the algebra behind covariance of the affine PDE. -/
/- The classical PDE is equivalent to the inverse-Hessian trace formulation
wherever its coefficients are the actual positive-definite Hessian. -/
/- Change of base variables, positive vertical scaling, and arbitrary affine
height correction. This includes the normalization of sections in rigidity. -/
/- The actual determinant weight transforms by its exact positive constant. -/
/- Hessians are local, including their inner derivative. -/
/- Exact, classical affine-maximal PDE covariance for section normalization.
No transformed PDE is assumed: it follows from the original one by the actual
Hessian and determinant chain rules. -/

/- The conormal for the genuine variation (x+t a(x),u(x)+t beta(x)),
written in its first jets, is (-q(t),1). -/
/- The second form for that conormal. H,B are the Hessians of u,beta;
C k is the Hessian of the kth horizontal displacement. -/

/- The actual first derivative of the horizontal component, in graph coordinates. -/
/- The graph's normal component of an arbitrary parametrized velocity. -/
/- The vertical velocity reconstructed from its normal part and horizontal part. -/
/- Actual affine-area density of the variation, in its exact graph jets. -/

/- The tangential part of the exact parametrized first-variation density is
an ordinary divergence; the remaining part is the genuine graph variation. -/

/- Every compact smooth parametric velocity has a genuinely smooth compact
normal graph component, without extending the original graph smoothly. -/
/- The exact pointwise first variation under every compact smooth parametric
velocity is integrable and has zero integral. The density uses the actual
varying conormal and horizontal Jacobian. -/

/- The augmented tangent frame, with its transverse column last. -/
/- The literal second form with a conormal frozen at the point in question. -/
/- Source (affine-area), using a fixed ambient volume basis. -/
/- Full ambient affine covariance, not restricted to fiber-preserving maps. -/

/- The abstract conormal formula is exactly the literal graph-variation density. -/

/- The literal arbitrary affine image of a parametrized graph variation. -/
/- Stationarity is genuinely preserved by every ambient affine transformation.
The integrand is the derivative of the actual transformed parametric density.
No equation for the affine image is assumed. -/

/- At a critical point the Hessian chain rule has no second derivative of the
coordinate change. Here it is proved for the actual Fréchet derivatives. -/

/- Exact density change of variables; its Jacobian has exponent one. -/

/- Invariance under positive rescaling of the conormal and reciprocal scaling
of the transverse vector. Both are actual multilinear expressions. -/
/- A tangent vector can be added to the transverse column without changing
its affine volume. -/

/- Differentiation over a fixed compact set from smoothness in a neighbourhood
of the zero-parameter slice. The uniform bound is obtained by compactness. -/

/- Actual differentiation of the compact affine-area functional, not just
an integrated pointwise derivative. -/
/- The compact affine-area functional of every arbitrary affine image is
stationary. All derivatives and integrals are the literal geometric density. -/

/- The stationarity functional in any smooth nonsingular injective coordinate
chart. The change of variables uses the literal Lebesgue Jacobian, and positivity
for the full parameter family is derived uniformly from the original Hessian. -/

/- Push a compactly supported smooth local velocity through a genuine smooth
coordinate inverse and extend by zero. Smoothness at the chart boundary is
proved, not an extra assumption on the transported velocity. -/
/- Every compact smooth ambient velocity in a local chart is a genuine
compact smooth graph velocity. This removes the extension requirement from
the coordinate stationarity theorem. -/

/- The literal affine area is independent of both allowed choices of
conormal and transverse vector. All transversality and orientation properties
are explicit; no intrinsic-area object is postulated. -/

/- The ambient conormal/transverse choices in the local chart stationarity
functional may be replaced by any other inward normalized choices. -/

/- Literal affine area is stationary for every compact smooth local ambient
variation, with any continuous inward normalized conormal/transverse choices.
The equation on the original graph, not an ambient stationary axiom, is used. -/

/- The graph projection of a smooth immersed parametrization of a graph
has nonsingular derivative. This is the differential input to the local
chart used in the support-coordinate stationarity calculation. -/

/- Local stationarity on an arbitrary immersed parametrization of the actual
solution graph. The smooth inverse chart is produced by the inverse function
theorem, not included among the hypotheses. -/

/- The literal support value, not a freely chosen support coordinate. -/
/- A supporting first-order inequality for an arbitrary differentiable convex function. -/
/- A nonzero linear functional cannot attain its sublevel maximum below the level. -/
/- The support maximum of a compact smooth convex sublevel has a positive
Lagrange multiplier. This includes dimension one without a sphere convention. -/
/- Linearization of the actual support equations `F(y)=0`, `DF(y)=lam*ell`. -/
/- Positive curvature gives the missing transversality of the support equations. -/

/- Fiber derivatives of the actual defining function. -/
/- A solution of the support equations with positive multiplier is a global,
not merely local, support point. -/
/- Smooth dependence of the literal support value on base and conormal.
The IFT is applied to the actual defining function and its actual Hessian. -/
/- Finiteness of the literal support value on a compact fiber. -/
/- The envelope identity recovers the Gauss parametrization from the literal
support function; no choice of a surrogate support coordinate is involved. -/

/- Coordinate entries coincide with the actual second Fréchet differential. -/
/- The standing positive-Hessian hypothesis implies genuine convexity on
 the original open convex domain; this is not an additional hypothesis. -/

/- A genuine affine slice of the original epigraph, in arbitrary transverse
coordinates. -/
/- A compact nonempty affine epigraph fiber has no vertical direction. -/
/- For an affine coordinate isomorphism compact fibers force injectivity of
its horizontal linear part. -/
/- Chain rule for the actual second differential of an affine epigraph slice. -/
/- An interior point of a convex sublevel is a strict sublevel point whenever
its actual Hessian is positive definite. -/
/- Convexity survives the actual affine slice and subtraction of its height. -/

/- The literal inverse image of the original epigraph under affine coordinates. -/
/- The principal support-coordinate regularity assertion in tubes.tex:39–60,
for actual affine images of the standing epigraph, not abstract smooth bodies.
The transverse dimension is nonzero, as in the manuscript (m=n+1-k≥1). -/

/- The one-homogeneous extension of the literal spherical support function. -/
/- The actual support point, reconstructed by the derivative of the support value. -/
/- Euler's identity differentiates to the radial null direction of the support
Hessian. This is the ambient version of the spherical radius matrix. -/

/- Actual smooth Gauss coordinates of each affine epigraph tube. -/

/- Orthogonal tangential projection when `e` is a unit vector. -/
/- The ambient extension of the spherical gradient of a degree-one support function. -/
/- The round covariant derivative, using tangential projection of the ambient derivative. -/
/- The spherical Hessian evaluated on tangent vectors. -/
/- `∇²_S h + h Id` is the restriction of the ambient Hessian of the
one-homogeneous support function. -/
/- The standard projected local extension of a tangent vector. At a unit `e`,
its round covariant derivative vanishes if `v` is tangent at `e`. -/
/- The covariant derivative of an ambient two-tensor restricted to the sphere.
The arguments `u,v,w` are tangent at the unit point of evaluation. The projected
constant extensions of `v,w` have zero covariant derivative there. -/
/- Codazzi for the radius tensor of a smooth one-homogeneous support function.
The radial Hessian identity is precisely the derivative of Euler's identity;
there is no assumed Codazzi equation. -/

/- Cofactor divergence vanishes for every differentiable Codazzi matrix field,
including size one and the empty angular block. No invertibility is required. -/

/- Radius matrix in projected constant tangent frames. At a unit `e` and an
orthonormal tangent frame this is exactly `∇²_S h + h Id`; its first derivatives
are the round covariant derivatives in a normal frame. -/
/- The angular cofactor divergence identity, derived from the actual Hessian
and Euler radial identity, not assumed as a stationarity hypothesis. -/

/- Local differential form of strict curvature duality: the Hessian of a
one-homogeneous support is positive on every nonzero tangent vector. -/
/- Strict positivity of the actual homogeneous support Hessian on tangent
vectors. The multiplier is constructed from the actual Gauss point, not given
as a differential identity hypothesis. -/

/- Positive angular radius comes from the actual original graph Hessian,
after any invertible affine change of coordinates with compact centered fibers. -/

/- Second derivative under a fixed continuous linear functional. -/

/- Strict curvature of the actual level hypersurface forces strict concavity
of its support value in the base variables. -/

/- The genuine defining function for any affine coordinates of the graph. -/
/- Positive curvature on the tangent hyperplane, including affine maps that
mix the original vertical direction with the new base and fiber coordinates. -/

/- The actual support point is on the original graph and its fiber conormal is
positive. No Gauss inverse or support-equation hypotheses are assumed. -/
/- Strict negativity of the base Hessian of the literal support function. This
is the other positive block of the genuine tube second fundamental form. -/

/- Euler and the angular gradient identity give the genuine tangent conormal. -/
/- Raw Gauss parametrization, before restricting the angular variable to a chart. -/
/- Differentiating the two literal support identities eliminates both mixed
blocks. No stationarity or curvature formula is assumed. -/
/- Source (tube-second-form), as an identity of actual conormal second jets.
It is valid before angular chart restriction, including the radial null line. -/

/- The raw affine tube has the conormal and block second form asserted in the
manuscript. All differential identities have been obtained from its actual
supremum support; the only geometric assumptions are the stated compact
centered fibers of the original affine epigraph. -/

/- The actual second-jet affine-area density in the base and orthonormal
angular directions; the transverse column is (0,-e). -/

/- Literal Jacobi first variation of the tube density, including empty
angular matrices. This is the integrand needed in source (tube-euler). -/

/- Both matrices in the actual tube area formula are positive definite,
including an empty angular matrix. This is derived from the original graph,
not imposed as an additional curvature assumption. -/
/- Source tube-area, for the literal supremum/Gauss parametrization of the
original affine epigraph under an arbitrary ambient affine isomorphism. -/

/- In a flat normal chart the final normal coordinate is one, and the
transverse column is the fixed negative final basis vector. -/
/- Literal flat-normal-chart area density. No sphere measure change is
required to obtain the local variational equation in these coordinates. -/

/- Positivity of the flat-normal-chart Hessian blocks follows from the actual
strictly convex affine epigraph, not from a surrogate support-function class. -/

/- A flat normal parametrization of the actual affine-epigraph boundary is
smooth and immersed; it lies on the original solution graph. The local graph
inverse is therefore available without a geometric chart hypothesis. -/

/- Literal local affine stationarity in any ambient vector coordinates.
The reference volume basis is transported exactly, not replaced by a
coordinate-free area axiom. -/

/- The literal support conormal is inward relative to the original solution
 graph, even after a general ambient affine change of variables. -/

/- The literal PDE supplies stationarity on every actual flat-normal support
chart. The chart inverse and conormal orientation are derived, not assumed. -/

/- Homogeneous extension of an actual test function off the affine normal chart. -/

/- Every actual smooth compact flat support variation is stationary. Its
homogeneous lifting, compact support, conormal and transverse fields are
constructed explicitly rather than supplied as stationarity hypotheses. -/

/- The exact tube density can be differentiated under its compact integral;
positivity is required only on the zero-parameter slice and is then uniform
for the compactly supported variation by the tube lemma. -/

/- The original affine-maximal PDE gives the literal flat tube weak Euler
identity. Both Hessian blocks, the support variation and the local stationary
chart are produced from the actual affine epigraph. -/

/- The fundamental variational lemma applied to two independent flat Hessian
blocks. No pointwise PDE is an assumption. -/

/- Two true integrations by parts and Piola cancellation convert flat tube
stationarity to the pointwise Euler equation. -/

/- The pointwise flat-normal tube Euler equation, derived from the original
PDE by actual support variations and two compact integrations by parts. -/

/- Exact logarithmic form of the two-block Euler equation. -/

/- The exact local flat-chart f equation. At the center of the flat normal
chart its angular terms equal the spherical covariant terms; no derivative
of a determinant or scalar density has been omitted. -/

/- Actual original PDE implies the support tube f equation in every flat normal chart. -/

/- A symmetric form with radial null vector has its full adjugate equal to
its transverse principal minor times the radial outer product. This includes
all empty transverse blocks and needs no invertibility of the full matrix. -/

/- The full cofactor trace recovers the transverse determinant in every flat
normal chart. No unit-normal constraint is imposed away from the chart center. -/

/- The invariant angular determinant is strictly positive on every actual
nonzero fiber conormal, independently of the fixed orthonormal frame. -/

/- An actual flat-normal coordinate injection with a continuous linear left
inverse. These chart data are produced from the frames, not postulated. -/

/- The invariant support f-equation, with all flat-normal chart data produced
from the actual frames. At a unit normal it is the round-sphere equation,
since the actual invariant scalar has zero radial derivative. -/

/- The penultimate Newton tensor, defined polynomially, not using an inverse. -/

/- A twice differentiated eigenvector equation, still valid at a singular
matrix and in dimension one. -/

/- A radial null vector of the Hessian is an eigenvector of its Newton
polynomial. No nonsingularity, division by a determinant, or limiting inverse
is used. -/

/- The linearized Piola cancellation is the divergence identity for the
penultimate Newton tensor. -/

/- Newton divergence for a genuine differentiable Codazzi field in constant
coordinates. Its sole tensor hypothesis is the third derivative symmetry. -/

/- The action of a genuine orthogonal coordinate change on the unit sphere. -/
/- The round measure, defined by ordinary Euclidean polar coordinates, is
orthogonally invariant in every dimension, including the two-point sphere. -/
/- The infinitesimal generator of rotation in the oriented `u,v` plane. -/
/- A genuine orthogonal rotation; its formula is the usual two-plane rotation,
not an assumed measure-invariant flow. -/
/- Differentiation under a finite measure on a compact parameter space.
The uniform bound is proved, rather than supplied as an analytic assumption. -/
/- Infinitesimal orthogonal invariance of the actual round measure. This is
proved by differentiating the genuine rotation, with a compact-sphere bound. -/

/- Ambient expression for the round divergence of the restriction to the unit sphere. -/
/- Contraction of the rotation derivatives is divergence minus the normal correction. -/

/- No angular boundary term: the round divergence of an actual smooth tangent
vector field integrates to zero, including the two-point and empty spheres. -/
/- Product rule for the actual round divergence, with no coordinate frame
extension assumed. The only cancellation is actual tangency on the sphere. -/
/- One genuine spherical integration by parts; all integrability follows from
smoothness near the compact sphere. -/

/- Derivatives of the radial eigenspace remain radial in the radial direction.
The polynomial identity avoids differentiating an arbitrarily chosen eigenvalue. -/

/- Tangential divergence of the restricted Newton tensor. Both normal
corrections vanish by genuine radial invariance, not as an IBP assumption. -/

/- Full ambient Hessian in a constant orthonormal basis. -/
/- Global polynomial tensor whose tangential restriction is the angular cofactor. -/
/- The genuinely differentiated angular divergence identity for a smooth
one-homogeneous support extension. Its only analytic input is the actual
radial Hessian identity; flat Piola and both normal cancellations are proved. -/

/- In every orthonormal frame adapted to the unit normal, the global tensor
is EXACTLY the cofactor of the tangential ambient Hessian. The empty tangential
block causes no exception. -/

/- The flux of the angular tensor acting on the projected vector field.
Written in a fixed ambient basis, so no unspecified moving-frame derivatives appear. -/
/- Intrinsic round Hessian contraction, formed from ambient derivatives and
orthogonal projection. It is independent of the extension off the sphere. -/

/- Weighted spherical tensor integration by parts, for the literal round measure.
All smoothness and integrability statements are derived on a neighborhood of the
compact sphere. -/
/- The exact twofold angular IBP needed by the tube Euler equation. -/
/- For the actual Newton/cofactor of a radial homogeneous Hessian, both tensor
hypotheses of angular integration by parts are PRODUCED, not postulated. -/

/- The coordinate-free round-sphere f-equation for the actual affine epigraph.
All analytic and cofactor terms are the genuine support objects; no tube PDE is assumed. -/

/- Literal invariant tube measure coefficient with respect to `ds dω`. -/

/- The manuscript's invariant density `μ₀` on base times unit normals. -/

/- Base cofactor integration by parts. Only smoothness near the compact test
support is needed; no boundary regularity or global coefficient extension is assumed. -/

/- Base identity for the exact exponential weight and a squared compact test.
It is valid without global smooth extensions of the support function. -/

/- Pointwise logarithmic Hessian identity plus genuine base integration by
parts gives the source p-identity. Its density is exactly `W detB/H`. -/

/- Actual base cofactor identity for either f, log h, or any smooth tube
scalar. The derivative coefficients are the Hessian cofactors of the literal
support function, and the exponential is the exact invariant measure weight. -/

/- The actual logarithmic base identity with the manuscript's literal μ₀.
All contractions use the actual positive base Hessian of support. -/

/- The genuine base integration formula, now with literal μ₀ and inverse-base metric. -/

/- Partial fiber gradient, represented through the derivative of the joint scalar. -/
/- Partial angular derivative of the gradient, represented without slice-dependent differentiation. -/

/- Cauchy--Schwarz for a positive definite inverse matrix, including zero vectors. -/

/- Exact angular weighted integration by parts for the source exponential
weight. The cofactor divergence and radial cancellations are proved by the
Newton calculus, not included as additional hypotheses. -/
/- The angular drift coefficient after integration is exactly `1-c`.
At `c=(n+2)/2` this is `-n/2`, as in tubes.tex. -/

/- The actual angular weighted drift integrates to exactly `-n/2` times
its nonnegative angular energy. No angular PDE or integration formula is assumed. -/

/- The actual angular weighted drift integrates to exactly `-n/2` times
its nonnegative angular energy. No angular PDE or integration formula is assumed. -/

/- The unrestricted product integral of a cutoff times a tube coefficient. -/

/- Compact product base IBP on the actual tube, rather than a formal drift identity. -/

/- The actual p-identity, with all compact product integrations justified. -/

/- A two-dimensional positive-semidefinite quadratic form, stated in
terms of the actual squared lengths and cross inner product. -/
/- A fixed explicit lower coercivity constant for the exact source range.
In particular it is independent of the number of directions k >= 2. -/
/- Cauchy--Schwarz followed by Young, with no choice of orthonormal frame. -/
/- The exact coefficients on the right of the source coercive identity. -/
/- Quantitative absorption in the exact coercive identity, with constants
uniform for every n in [3,9] and every tube direction count. -/
/- Exact cancellation of the two stationarity identities in tubes.tex.
The symbols are their actual integrals; this is just their linear combination. -/

/- Absorption with the literal compact-product density, requiring positivity only
on the actual unit-normal tube. The identity is an input here and will be supplied
by the actual affine-maximal equation. -/

/- Compact product base IBP on the actual tube, rather than a formal drift identity. -/

/- The coordinate-log Young estimate, with constants uniform for 3≤n≤9. -/

/- Cauchy--Schwarz for an arbitrary finite linear combination in the literal inverse metric. -/

/- The manuscript's positive base orthant. -/
/- Extension by zero of a compact test in logarithmic coordinates; a negative
coordinate must not be silently sent through Real.log. -/

/- Euclidean norm squared of the gradient, written in the fixed orthonormal coordinate basis. -/

/- Proposition log-inequality for the actual affine-epigraph tube. The positive-
orthant pullback is extended by zero, and both sides are literal product integrals
with the source logarithmic density. No tube-metric completeness is required. -/

/- The actual logarithmic pushforward of a tube density, restricted to its
positive base domain. Only the nonnegative part outside that domain is discarded. -/

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SigmaCapHelpers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section SigmaCapHelpers
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ]

omit [CompleteSpace E] in
lemma tubeAngularDensity_reindex (H : S × E → ℝ) (q : S × E)
    (b : OrthonormalBasis ι ℝ E) (e : ι ≃ τ) :
    tubeAngularDensity H q (b.reindex e) = tubeAngularDensity H q b := by
  unfold tubeAngularDensity
  have hm : tubeFullRadiusMatrix H q (b.reindex e) =
      (tubeFullRadiusMatrix H q b).submatrix e.symm e.symm := by
    ext i j
    simp [tubeFullRadiusMatrix,OrthonormalBasis.reindex_apply]
  rw [hm,Matrix.adjugate_submatrix_equiv_self]
  exact e.symm.sum_comp (fun i => (tubeFullRadiusMatrix H q b).adjugate i i)

end SigmaCapHelpers

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FaceSigmaTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section FaceSigmaTransport
open Metric
/-- The original graph affine area over any compact-fiber rectangle is controlled
by the actual weighted sigma mass. The multiplicity constant is fixed before
all epigraphs and affine coordinates. -/
theorem affineEpigraph_face_sigma_transport {n k m d : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
    (f : WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m) :
    ∃ CA > 0, ∀ {Ω : Set (Space n)}, IsOpen Ω → Convex ℝ Ω →
    ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω → (∀ x ∈ Ω, (hessian u x).PosDef) →
    ∀ (a : Space n × ℝ) (L : (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
      {D : Set (Space k)}, IsOpen D →
    (∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) →
    (∀ s ∈ D, (0:Space m) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) →
    ∀ {Q : Set (Space k)}, MeasurableSet Q → Q ⊆ D → ∀ {M : ℝ}, 0 ≤ M →
    (∀ s ∈ Q, ∀ y : Space m, (s,y) ∈ affineEpigraphPullback Ω u a L → ‖y‖ ≤ M) →
    ∀ {K : Set (Space n)}, K ⊆ Ω → (∀ x ∈ K, (L.symm ((x,u x)-a)).1 ∈ Q) →
    let bE := (EuclideanSpace.basisFun (Fin m) ℝ).reindex eE
    let H := fun q : Space k × Space m => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let μ := (volume.restrict Q).prod (volume : Measure (Space m)).toSphere
    let F := ((m:ℝ≥0∞)^2 * volume (closedBall (0:Space m) (M+1))) * volume Q
    ENNReal.ofReal (Real.rpow |(productAmbientBasis bE e).det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
        ((n:ℝ)/((n:ℝ)+2)) * ∫ x in K, affineAreaDensity u x) ≤
      (ENNReal.ofReal CA * ENNReal.ofReal (M^((n:ℝ)/((n:ℝ)+2))) * F^(1-2/((n:ℝ)+2))) *
      (∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
        ENNReal.ofReal (tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE (q.1,q.2)*
          tubeLogMassWeight H (q.1,q.2)) ∂μ)^(2/((n:ℝ)+2)) := by
  let : NeZero m := ⟨by omega⟩
  let bS := EuclideanSpace.basisFun (Fin k) ℝ
  let bF := EuclideanSpace.basisFun (Fin d) ℝ
  let bE := (EuclideanSpace.basisFun (Fin m) ℝ).reindex eE
  obtain ⟨CA,hCA,hwhole⟩ := affineEpigraph_whole_graph_area_bound bS bF bE f e
  refine ⟨CA,hCA,?_⟩
  intro Ω hΩ hcv u hu hp a L D hD hK hzero Q hQ hQD M hM hbound K hKO hKQ
  dsimp only
  let H := fun q : Space k × Space m => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let μ := (volume.restrict Q).prod (volume : Measure (Space m)).toSphere
  let σ : ℝ≥0∞ := ∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
    ENNReal.ofReal (tubeMeasureDensity n H bS.toBasis bE (q.1,q.2)*tubeLogMassWeight H (q.1,q.2)) ∂μ
  let F : ℝ≥0∞ := ((m:ℝ≥0∞)^2 * volume (closedBall (0:Space m) (M+1))) * volume Q
  have hfarea : (∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
      ENNReal.ofReal (tubeAngularDensity H (q.1,q.2) bE) ∂μ) ≤ F := by
    have hh := affineEpigraph_product_fiber_area_bound hm hΩ hcv hu hp a L hD hK hzero hQ hQD hbound
    simpa only [bE,tubeAngularDensity_reindex] using hh
  have hw := hwhole hΩ hcv hu hp a L hD hK hzero hQ hQD hKO hKQ
  dsimp only at hw
  have hjhold := affineEpigraph_area_le_sigma hn hΩ hcv hu hp a L hD hK hzero bE hQ hQD hM hbound
  dsimp only at hjhold
  have hncard : n = k+d := by
    have hh := Fintype.card_congr e
    simpa only [Fintype.card_fin,Fintype.card_sum] using hh
  have hdim : (Fintype.card (Fin k):ℝ)+Fintype.card (Fin d)+2 = (n:ℝ)+2 := by
    simp only [Fintype.card_fin,hncard,Nat.cast_add]
  rw [hdim] at hw
  have hnn : 0 ≤ᵐ[volume.restrict K] affineAreaDensity u := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hKO (ae_restrict_mem hΩ.measurableSet)] with x hx
    exact Real.rpow_nonneg (hp x hx).det_pos.le _
  have hy : 0 ≤ 1-2/((n:ℝ)+2) := by
    have hh : 2/((n:ℝ)+2) ≤ 1 := (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    linarith
  have hcoef : 0 ≤ Real.rpow |(productAmbientBasis bE e).det
        ((graphAmbientBasis n).map L.symm.toLinearEquiv)| ((n:ℝ)/((n:ℝ)+2)) :=
      Real.rpow_nonneg (abs_nonneg _) _
  rw [ENNReal.ofReal_mul hcoef]
  refine (mul_le_mul_right (ofReal_integral_le_lintegral_of_nonneg hnn) _).trans (hw.trans ?_)
  calc
    _ ≤ ENNReal.ofReal CA *
      (ENNReal.ofReal (M^((n:ℝ)/((n:ℝ)+2))) * σ^(2/((n:ℝ)+2)) * F^(1-2/((n:ℝ)+2))) := by
      apply mul_le_mul_right
      exact hjhold.trans (mul_le_mul_right (ENNReal.rpow_le_rpow hfarea hy) _)
    _ = _ := by
      change ENNReal.ofReal CA * (ENNReal.ofReal (M^((n:ℝ)/((n:ℝ)+2))) *
        σ^(2/((n:ℝ)+2)) * F^(1-2/((n:ℝ)+2))) =
        (ENNReal.ofReal CA * ENNReal.ofReal (M^((n:ℝ)/((n:ℝ)+2))) * F^(1-2/((n:ℝ)+2))) * σ^(2/((n:ℝ)+2))
      ac_rfl
end FaceSigmaTransport


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ModelPositiveSigma
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section ModelPositiveSigma
open Metric Filter

lemma isCompact_positiveClosedRectangle {k : ℕ} (a b : ℝ) :
    IsCompact (positiveClosedRectangle (k := k) a b) := by
  convert! (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi fun _ : Fin k => (isCompact_Icc : IsCompact (Icc a b))) using 1
  all_goals try with_reducible_and_instances rfl
  ext s
  simp only [positiveClosedRectangle,Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_univ_pi,Set.mem_Icc]
  rfl

/-- The face mass cannot disappear in the true weighted sigma measure. This is
an eventual lower bound on one fixed physical rectangle, derived from the
original PDE and Euclidean graph completeness, not a mass premise. -/
theorem normalized_model_positive_sigma_rectangle {n k m d : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hm : 1 ≤ m) (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
    (f : WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmP : AffineMaximalOn Ω u)
    (hcomplete : EuclideanGraphComplete Ω u)
    (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
    {C : Set (Space k × Space m)} (hC : IsModelShape C)
    (hlim : LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L j)) C)
    {r R₀ : ℝ} (hr : 0 < r)
    (hin : closedBall (0:Space m) r ⊆ modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R₀) :
    ∃ α > 0, ∃ β, 1 ≤ β ∧ ∃ c > 0, ∀ᶠ j in atTop,
      positiveClosedRectangle (k := k) α β ⊆ regularPositiveFiberDomain (affineEpigraphPullback Ω u (a j) (L j)) ∧
      let H := fun q : Space k × Space m => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u (a j) (L j)} q.2
      ENNReal.ofReal c ≤ ∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
        ENNReal.ofReal (tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
          ((EuclideanSpace.basisFun (Fin m) ℝ).reindex eE) (q.1,q.2)*tubeLogMassWeight H (q.1,q.2))
          ∂(volume.restrict (positiveClosedRectangle α β)).prod (volume : Measure (Space m)).toSphere := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨CA,hCA,htransport⟩ := affineEpigraph_face_sigma_transport hn hm e eE f
  obtain ⟨R,hR,ε,hε,c,hc,hface⟩ := normalized_model_positive_face_mass hn hk hm e eE
    hΩ hne hcv hu hp hmP hcomplete a L hC hlim hr hin hout
  let α := min ε 1 / 2
  let β := max R 1 + 1
  have hα : 0 < α := by dsimp [α]; positivity
  have hα1 : α ≤ 1 := by dsimp [α]; linarith [min_le_right ε (1:ℝ)]
  have hαε : α ≤ ε := by dsimp [α]; linarith [min_le_left ε (1:ℝ)]
  have hβ : 1 ≤ β := by dsimp [β]; linarith [le_max_right R (1:ℝ)]
  have hRβ : R ≤ β := by dsimp [β]; linarith [le_max_left R (1:ℝ)]
  let Q : Set (Space k) := positiveClosedRectangle α β
  have hQ : MeasurableSet Q := (isCompact_positiveClosedRectangle α β).measurableSet
  have hQfin : volume Q ≠ ⊤ := (isCompact_positiveClosedRectangle α β).measure_ne_top
  let Cj := fun j => affineEpigraphPullback Ω u (a j) (L j)
  let D := fun j => regularPositiveFiberDomain (Cj j)
  have hclosed := sourceEpigraph_closed hΩ hne hcv hu hp hcomplete
  have hclj j : IsClosed (Cj j) := affineEpigraphPullback_isClosed hclosed _ _
  have hcvj j : Convex ℝ (Cj j) :=
    ((sourceEpigraph_convex hΩ hcv hu hp).translate_preimage_right (a j)).linear_preimage (L j).toLinearMap
  have hnej j : (Cj j).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    refine ⟨(L j).symm ((x,u x)-a j),?_⟩
    change (a j + (L j) ((L j).symm ((x,u x)-a j))).1 ∈ Ω ∧ _
    simp [hx]
  let M : ℝ := max (Real.sqrt k * max 1 (k*(2*β)+1)) (max 1 (k*(2*β)+1)*R₀)+1
  have hM : 0 ≤ M := by
    have hh : 0 ≤ Real.sqrt k * max 1 ((k:ℝ)*(2*β)+1) := mul_nonneg (Real.sqrt_nonneg _) (by positivity)
    dsimp only [M]
    linarith [le_max_left (Real.sqrt k * max 1 ((k:ℝ)*(2*β)+1)) (max 1 ((k:ℝ)*(2*β)+1)*R₀)]
  have hfib := hlim.eventually_normalized_fibers hC hclj hcvj hnej hr
    (half_pos hα) (show α/2 ≤ 1 by linarith) (show 1 ≤ 2*β by linarith) hin hout
  let F : ℝ≥0∞ := ((m:ℝ≥0∞)^2 * volume (closedBall (0:Space m) (M+1))) * volume Q
  have hF : F ≠ ⊤ := by
    dsimp [F]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp)
      ((isCompact_closedBall (0:Space m) (M+1)).measure_ne_top)) hQfin
  let B : ℝ≥0∞ := ENNReal.ofReal CA * ENNReal.ofReal (M^((n:ℝ)/((n:ℝ)+2))) * F^(1-2/((n:ℝ)+2))
  have hy : 0 ≤ 1-2/((n:ℝ)+2) := by
    have hh : 2/((n:ℝ)+2) ≤ 1 := (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    linarith
  have hB : B ≠ ⊤ := by
    dsimp only [B]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg hy hF)
  obtain ⟨δ,hδ,hδlower⟩ := exists_pos_lower_of_rpow hB hc (show 0 < 2/((n:ℝ)+2) by positivity)
  refine ⟨α,hα,β,hβ,δ,hδ,?_⟩
  filter_upwards [hface,hfib] with j hj hf
  have hQbox (s : Space k) (hs : s ∈ Q) : ∀ i, s i ∈ Icc (α/2) (2*β) := by
    intro i
    have hi := hs i
    exact ⟨by linarith [hi.1],by linarith [hi.2]⟩
  have hQD : Q ⊆ D j := by
    apply Set.Subset.trans (b := {s : Space k | ∀ i, α/2 < s i ∧ s i < 2*β})
    · intro s hs i
      have hi := hs i
      exact ⟨by linarith [hi.1],by linarith [hi.2]⟩
    · exact openBox_subset_regularPositiveFiberDomain (hclj j) (half_pos hα)
        (fun s hs => (hf s hs).2)
  have hDj : IsOpen (D j) := regularPositiveFiberDomain_isOpen _
  have hKj : ∀ s ∈ D j, IsCompact {y | (s,y) ∈ Cj j} := fun _ hs => regularPositiveFiberDomain_compact _ hs
  have hzero : ∀ s ∈ D j, (0:Space m) ∈ interior {y | (s,y) ∈ Cj j} := fun _ hs => regularPositiveFiberDomain_zero _ hs
  have hbound : ∀ s ∈ Q, ∀ y : Space m, (s,y) ∈ Cj j → ‖y‖ ≤ M := by
    intro s hs y hy
    exact mem_closedBall_zero_iff.mp ((hf s (hQbox s hs)).2.2 hy)
  obtain ⟨K,hKO,hKQ,harea⟩ := hj
  have hKQ' : ∀ x ∈ K, ((L j).symm ((x,u x)-a j)).1 ∈ Q := by
    intro x hx i
    exact ⟨hαε.trans (hKQ x hx i).1,(hKQ x hx i).2.trans hRβ⟩
  refine ⟨hQD,hδlower _ ?_⟩
  exact (ENNReal.ofReal_le_ofReal harea).trans
    (htransport hΩ hcv hu hp (a j) (L j) hDj hKj hzero hQ hQD hM hbound hKO hKQ')
end ModelPositiveSigma


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ModelPositiveLogMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section ModelPositiveLogMass
open Metric Filter
lemma positiveClosedRectangle_sub_logBox {k : ℕ} {α β : ℝ} (hα : 0 < α) :
    ∃ T : ℕ, positiveClosedRectangle (k := k) α β ⊆ logSpace ⁻¹' logarithmicBox k T := by
  obtain ⟨T,hT⟩ := exists_nat_gt (max |Real.log α| |Real.log β|)
  refine ⟨T,?_⟩
  intro s hs i
  rw [logSpace_apply]
  apply abs_le.mpr
  have h1 : |Real.log α| ≤ (T:ℝ) := (le_max_left _ _).trans hT.le
  have h2 : |Real.log β| ≤ (T:ℝ) := (le_max_right _ _).trans hT.le
  have hsi := (hs i)
  have hlogs := Real.log_le_log hα hsi.1
  have hlogt := Real.log_le_log (hα.trans_le hsi.1) hsi.2
  exact ⟨(neg_le_neg h1).trans ((neg_abs_le _).trans hlogs),hlogt.trans ((le_abs_self _).trans h2)⟩

/-- A fixed log box has strictly positive actual sigma mass, uniformly along
any normalized actual epigraph approximation. Local finiteness is proved from
smooth compact fibers, and the positive mass is produced from the original PDE. -/
theorem normalized_model_positive_log_mass_oai {n k m d : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hm : 1 ≤ m) (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
    (f : WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmP : AffineMaximalOn Ω u)
    (hcomplete : EuclideanGraphComplete Ω u)
    (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
    {C : Set (Space k × Space m)} (hC : IsModelShape C)
    (hlim : LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L j)) C)
    {r R₀ : ℝ} (hr : 0 < r)
    (hin : closedBall (0:Space m) r ⊆ modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R₀) :
    ∃ T : ℕ, ∃ c > 0, ∀ᶠ j in atTop,
      c ≤ (affineEpigraphLogMeasure volume
        (regularPositiveFiberDomain (affineEpigraphPullback Ω u (a j) (L j))) Ω u (a j) (L j)
        ((EuclideanSpace.basisFun (Fin m) ℝ).reindex eE)).real (logarithmicBox k T) := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨α,hα,β,hβ,c,hc,hrect⟩ := normalized_model_positive_sigma_rectangle hn hk hm e eE f
    hΩ hne hcv hu hp hmP hcomplete a L hC hlim hr hin hout
  obtain ⟨T,hT⟩ := positiveClosedRectangle_sub_logBox (k := k) (β := β) hα
  have hclosed := sourceEpigraph_closed hΩ hne hcv hu hp hcomplete
  have hclj j : IsClosed (affineEpigraphPullback Ω u (a j) (L j)) := affineEpigraphPullback_isClosed hclosed _ _
  have hcvj j : Convex ℝ (affineEpigraphPullback Ω u (a j) (L j)) :=
    ((sourceEpigraph_convex hΩ hcv hu hp).translate_preimage_right (a j)).linear_preimage (L j).toLinearMap
  have hnej j : (affineEpigraphPullback Ω u (a j) (L j)).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    refine ⟨(L j).symm ((x,u x)-a j),?_⟩
    change (a j + (L j) ((L j).symm ((x,u x)-a j))).1 ∈ Ω ∧ _
    simp [hx]
  have havail := hlim.eventually_regular_logBox hC hclj hcvj hnej hr hin hout T
  refine ⟨T,c,hc,?_⟩
  filter_upwards [hrect,havail] with j hj ha
  let Cj := affineEpigraphPullback Ω u (a j) (L j)
  let D := regularPositiveFiberDomain Cj
  let H := fun q : Space k × Space m => homogeneousSupport {y | (q.1,y) ∈ Cj} q.2
  let bE := (EuclideanSpace.basisFun (Fin m) ℝ).reindex eE
  let W := fun q => tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE q * tubeLogMassWeight H q
  have hmass : ENNReal.ofReal c ≤ affineEpigraphLogMeasure volume D Ω u (a j) (L j) bE (logarithmicBox k T) := by
    refine hj.2.trans (logTubeMeasure_cell_le_apply volume D W
      (logarithmicBox_isClosed k T).measurableSet ?_)
    exact fun s hs => ⟨hj.1 hs,hT hs⟩
  have hfin := affineEpigraphLogMeasure_box_finite (μ := volume) hΩ hcv hu hp (a j) (L j)
    (regularPositiveFiberDomain_isOpen Cj) (regularPositiveFiberDomain_positive Cj)
    (fun _ hs => regularPositiveFiberDomain_compact Cj hs)
    (fun _ hs => regularPositiveFiberDomain_zero Cj hs) bE ha
  exact (ENNReal.toReal_ofReal hc.le).symm.trans_le (ENNReal.toReal_mono hfin hmass)
end ModelPositiveLogMass


end
end AffineBernstein
end

end OAI
end

theorem solution : type_of% @OAI.AffineBernstein.normalized_model_positive_log_mass_oai := @OAI.AffineBernstein.normalized_model_positive_log_mass_oai
