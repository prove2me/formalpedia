-- Prove2me | solution 1 for OAI.AffineBernstein.normalized_model_uniform_actual_sigma
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:21:40.650243+00:00
-- url     : https://prove2.me/submissions/c36bd80e-c746-46b9-a3fb-8d3c2002443b

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_invariant_tube_positive
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_product_fiber_area_bound
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_product_minors_bound
import Theorems.Thm_OAI_AffineBernstein_complete_affineMaximal_uniform_spherical_cap_bound

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

omit [FiniteDimensional ℝ E] [Nontrivial E] in
lemma homogeneousSupport_ge_of_ball {K : Set E} (hK : IsCompact K)
    {e : E} (he : ‖e‖ = 1) {r : ℝ} (hr : 0 ≤ r)
    (hball : Metric.closedBall (0:E) r ⊆ K) : r ≤ homogeneousSupport K e := by
  have hmem : r • e ∈ K := hball (by
    simp only [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg hr,he,mul_one,le_refl])
  have hi := homogeneousSupport_le hK hmem e
  simpa only [inner_smul_right,real_inner_self_eq_norm_sq,he,one_pow,mul_one] using hi

/- Fully geometric formulation of the actual large-minor estimate: only the
fibers' position in a fixed ball and a base collar are needed. -/

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

lemma inverseMatrixPair_add_left (A : Matrix ι ι ℝ) (x y z : ι → ℝ) :
    inverseMatrixPair A (fun i => x i+y i) z = inverseMatrixPair A x z+inverseMatrixPair A y z := by
  simp only [inverseMatrixPair,mul_add,add_mul,Finset.sum_add_distrib]

lemma inverseMatrixPair_add_right (A : Matrix ι ι ℝ) (x y z : ι → ℝ) :
    inverseMatrixPair A x (fun i => y i+z i) = inverseMatrixPair A x y+inverseMatrixPair A x z := by
  simp only [inverseMatrixPair,mul_add,Finset.sum_add_distrib]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_LogMassWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

section DependencyScope
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section LogMassWeight
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Exact coordinate formula for the true inverse-block logarithmic norm. -/
lemma tubeBasePair_coordinate_log {k : ℕ} (H : Space k × E → ℝ) (q : Space k × E)
    (i : Fin k) (hq : q.1 i ≠ 0) :
    tubeBasePair H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
      (fun z => Real.log (z.1 i)) (fun z => Real.log (z.1 i)) q =
      H q*(tubeBaseMatrix H q (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)⁻¹ i i/(q.1 i)^2 := by
  let ℓ : (Space k × E) →L[ℝ] ℝ := (EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ (Space k) E)
  have hd : HasFDerivAt (fun z : Space k × E => Real.log (z.1 i)) ((q.1 i)⁻¹ • ℓ) q :=
    ℓ.hasFDerivAt.log hq
  have hv (j : Fin k) : dirDeriv ((EuclideanSpace.basisFun (Fin k) ℝ) j,(0:E))
      (fun z : Space k × E => Real.log (z.1 i)) q = (q.1 i)⁻¹*(if i=j then 1 else 0) := by
    rw [dirDeriv,hd.fderiv]
    simp [ℓ,EuclideanSpace.basisFun_apply]
  simp only [tubeBasePair,flatInversePair,OrthonormalBasis.coe_toBasis,hv]
  simp only [mul_ite,ite_mul,mul_one,mul_zero,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  field_simp [hq]

/- On a positive base collar, the manuscript's sigma weight is bounded by
one plus the actual inverse-Hessian trace, with the exact support-height factor. -/
lemma tubeLogMassWeight_le_trace {k : ℕ} (H : Space k × E → ℝ) (q : Space k × E)
    {r M : ℝ} (hr : 0 < r) (hs : ∀ i, r ≤ q.1 i)
    (hh : 0 ≤ H q) (hhM : H q ≤ M)
    (hB : (tubeBaseMatrix H q (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).PosDef) :
    tubeLogMassWeight H q ≤ 1 + (M/r^2)*(tubeBaseMatrix H q
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)⁻¹.trace := by
  unfold tubeLogMassWeight
  refine add_le_add le_rfl ?_
  rw [Matrix.trace,Finset.mul_sum]
  simp only [Matrix.diag_apply]
  apply Finset.sum_le_sum
  intro i _
  rw [tubeBasePair_coordinate_log H q i (ne_of_gt (hr.trans_le (hs i)))]
  have hb : 0 ≤ (tubeBaseMatrix H q (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)⁻¹ i i :=
    hB.inv.posSemidef.diag_nonneg
  have hden : r^2 ≤ (q.1 i)^2 := sq_le_sq₀ hr.le (hr.le.trans (hs i)) |>.mpr (hs i)
  calc
    _ ≤ (M * (tubeBaseMatrix H q (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)⁻¹ i i)/r^2 :=
      div_le_div₀ (mul_nonneg (hh.trans hhM) hb) (mul_le_mul_of_nonneg_right hhM hb) (sq_pos_of_pos hr) hden
    _ = _ := by ring
end LogMassWeight

/- Real positive densities can be interpolated before or after `ofReal`. -/

end DependencyScope

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

lemma weighted_tube_interpolation {n : ℕ} {B Q t : ℝ}
    (hB : 0 < B) (hQ : 0 < Q) (ht : 0 < t) :
    Real.sqrt (B*Q)*t =
      (B ^ (1/((n:ℝ)+2)) * Q ^ (1-1/((n:ℝ)+2))*t) ^
        (((n:ℝ)+2)/(2*((n:ℝ)+1))) *
      (B*t) ^ (1-((n:ℝ)+2)/(2*((n:ℝ)+1))) := by
  have hN : (n:ℝ)+2 ≠ 0 := by positivity
  have hP : (n:ℝ)+1 ≠ 0 := by positivity
  have hI : 0 < B ^ (1/((n:ℝ)+2)) * Q ^ (1-1/((n:ℝ)+2)) := by positivity
  apply Real.log_injOn_pos
  · change (0:ℝ) < _
    positivity
  · change (0:ℝ) < _
    positivity
  rw [Real.log_mul (Real.sqrt_pos.2 (mul_pos hB hQ)).ne' ht.ne',
    Real.log_sqrt (mul_pos hB hQ).le,Real.log_mul hB.ne' hQ.ne',
    Real.log_mul (Real.rpow_pos_of_pos (mul_pos hI ht) _).ne'
      (Real.rpow_pos_of_pos (mul_pos hB ht) _).ne',
    Real.log_rpow (mul_pos hI ht),Real.log_rpow (mul_pos hB ht),
    Real.log_mul hI.ne' ht.ne',Real.log_mul hB.ne' ht.ne',
    Real.log_mul (Real.rpow_pos_of_pos hB _).ne' (Real.rpow_pos_of_pos hQ _).ne',
    Real.log_rpow hB,Real.log_rpow hQ]
  field_simp
  ring

lemma weighted_tube_exponent {n : ℕ} (hn : 1 ≤ n) :
    0 < ((n:ℝ)+2)/(2*((n:ℝ)+1)) ∧ ((n:ℝ)+2)/(2*((n:ℝ)+1)) < 1 := by
  have h : (1:ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · positivity
  · apply (div_lt_one (by positivity)).2
    linarith

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
lemma lintegral_weighted_tube_interpolation {n : ℕ} (hn : 1 ≤ n)
    {B Q t : X → ℝ} (hB : AEMeasurable B μ) (hQ : AEMeasurable Q μ)
    (ht : AEMeasurable t μ) (hBp : ∀ᵐ x ∂μ, 0 < B x)
    (hQp : ∀ᵐ x ∂μ, 0 < Q x) (htp : ∀ᵐ x ∂μ, 0 < t x) :
    (∫⁻ x, ENNReal.ofReal (Real.sqrt (B x*Q x)*t x) ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal (B x ^ (1/((n:ℝ)+2)) * Q x ^ (1-1/((n:ℝ)+2))*t x) ∂μ) ^
        (((n:ℝ)+2)/(2*((n:ℝ)+1))) *
      (∫⁻ x, ENNReal.ofReal (B x*t x) ∂μ) ^ (1-((n:ℝ)+2)/(2*((n:ℝ)+1))) := by
  have hp := weighted_tube_exponent hn
  have hf := ((hB.pow_const (1/((n:ℝ)+2))).mul (hQ.pow_const (1-1/((n:ℝ)+2)))).mul ht
  have hfp : ∀ᵐ x ∂μ, 0 ≤ B x ^ (1/((n:ℝ)+2))*Q x ^ (1-1/((n:ℝ)+2))*t x := by
    filter_upwards [hBp,hQp,htp] with x hx hy hz
    positivity
  have hgp : ∀ᵐ x ∂μ, 0 ≤ B x*t x := by
    filter_upwards [hBp,htp] with x hx hy
    positivity
  calc
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hBp,hQp,htp] with x hx hy hz
      rw [weighted_tube_interpolation (n := n) hx hy hz]
    _ ≤ _ := by
      simpa only [Pi.mul_apply] using
        lintegral_ofReal_geometric_mean_le μ hp.1 hp.2 hf (hB.mul ht) hfp hgp

/- Controlling the fiber area and the support height converts a positive
amount of affine area into a lower bound on the true invariant tube mass. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_MassUpper
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

/- The source's unweighted tube mass estimate from support height and the two
actual determinant integrals. A positive angular determinant is not needed for
this upper estimate: the real square root already discards its negative part. -/
lemma lintegral_tube_mass_le {n : ℕ} {h B Q : X → ℝ}
    (hB : AEMeasurable B μ) (hQ : AEMeasurable Q μ)
    (hBp : ∀ᵐ x ∂μ, 0 ≤ B x) {r : ℝ} (hr : 0 < r)
    (hbound : ∀ᵐ x ∂μ, r ≤ h x) :
    (∫⁻ x, ENNReal.ofReal (tubeMeasureCoefficient n (h x) (B x) (Q x)) ∂μ) ≤
      ENNReal.ofReal (r ^ (-(n:ℝ)/2)) *
        (∫⁻ x, ENNReal.ofReal (B x) ∂μ) ^ (1/(2:ℝ)) *
        (∫⁻ x, ENNReal.ofReal (Q x) ∂μ) ^ (1/(2:ℝ)) := by
  let Qp := fun x => max (Q x) 0
  have hQp : AEMeasurable Qp μ := hQ.max aemeasurable_const
  have hpos : ∀ᵐ x ∂μ, 0 ≤ Qp x := Filter.Eventually.of_forall fun _ => le_max_right _ _
  have hh := lintegral_ofReal_geometric_mean_le μ (p := (1/(2:ℝ))) (by norm_num)
    (by norm_num) hB hQp hBp hpos
  have hqint : (∫⁻ x, ENNReal.ofReal (Qp x) ∂μ) = ∫⁻ x, ENNReal.ofReal (Q x) ∂μ := by
    congr 1
    funext x
    simp [Qp]
  norm_num only [show (1:ℝ)-1/2 = 1/2 by norm_num] at hh
  rw [hqint] at hh
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (r ^ (-(n:ℝ)/2)) *
        ENNReal.ofReal ((B x)^(1/(2:ℝ)) * (Qp x)^(1/(2:ℝ))) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hBp,hbound] with x hbx hhx
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
      apply ENNReal.ofReal_le_ofReal
      unfold tubeMeasureCoefficient
      have hrp : (h x)^(-(n:ℝ)/2) ≤ r^(-(n:ℝ)/2) :=
        Real.rpow_le_rpow_of_nonpos hr hhx (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (by norm_num))
      have hs : Real.sqrt (B x*Q x) ≤ (B x)^(1/(2:ℝ)) * (Qp x)^(1/(2:ℝ)) := by
        rw [Real.sqrt_mul hbx,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (le_max_left _ _)) (Real.sqrt_nonneg _)
      exact mul_le_mul hrp hs (Real.sqrt_nonneg _) (Real.rpow_nonneg hr.le _)
    _ = ENNReal.ofReal (r ^ (-(n:ℝ)/2)) *
        ∫⁻ x, ENNReal.ofReal ((B x)^(1/(2:ℝ)) * (Qp x)^(1/(2:ℝ))) ∂μ := by
      rw [lintegral_const_mul']
      exact ENNReal.ofReal_ne_top
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_right hh (ENNReal.ofReal (r ^ (-(n:ℝ)/2)))

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_WeightedMassUpper
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

/- The determinant interpolation controls the genuine tube mass with inverse
trace weight after using only the normalized positive support-height bound. -/
lemma lintegral_weighted_tube_mass_le {n : ℕ} (hn : 1 ≤ n)
    {h B Q t : X → ℝ} (hB : AEMeasurable B μ) (hQ : AEMeasurable Q μ)
    (ht : AEMeasurable t μ) (hBp : ∀ᵐ x ∂μ, 0 < B x)
    (hQp : ∀ᵐ x ∂μ, 0 < Q x) (htp : ∀ᵐ x ∂μ, 0 < t x)
    {r : ℝ} (hr : 0 < r) (hbound : ∀ᵐ x ∂μ, r ≤ h x) :
    (∫⁻ x, ENNReal.ofReal (tubeMeasureCoefficient n (h x) (B x) (Q x)*t x) ∂μ) ≤
      ENNReal.ofReal (r^(-(n:ℝ)/2)) *
      (∫⁻ x, ENNReal.ofReal (B x ^ (1/((n:ℝ)+2)) * Q x ^ (1-1/((n:ℝ)+2))*t x) ∂μ) ^
        (((n:ℝ)+2)/(2*((n:ℝ)+1))) *
      (∫⁻ x, ENNReal.ofReal (B x*t x) ∂μ) ^ (1-((n:ℝ)+2)/(2*((n:ℝ)+1))) := by
  have hI := lintegral_weighted_tube_interpolation hn hB hQ ht hBp hQp htp
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (r^(-(n:ℝ)/2))*
        ENNReal.ofReal (Real.sqrt (B x*Q x)*t x) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hbound,htp] with x hx htx
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
      apply ENNReal.ofReal_le_ofReal
      unfold tubeMeasureCoefficient
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.sqrt_nonneg _) htx.le)
      exact Real.rpow_le_rpow_of_nonpos hr hx
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (by norm_num))
    _ = ENNReal.ofReal (r^(-(n:ℝ)/2))*
        ∫⁻ x, ENNReal.ofReal (Real.sqrt (B x*Q x)*t x) ∂μ := by
      rw [lintegral_const_mul']
      exact ENNReal.ofReal_ne_top
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_right hI (ENNReal.ofReal (r^(-(n:ℝ)/2)))

/- Full sigma mass estimate. The inputs are the source determinant, fiber
area, cap inverse-energy, and principal-minor integrals, not an assumed sigma
bound. This is manuscript bounds.tex322–351 before geometric normalization. -/
lemma lintegral_sigma_mass_le {n : ℕ} (hn : 1 ≤ n)
    {h B Q t W : X → ℝ} (hh : AEMeasurable h μ)
    (hB : AEMeasurable B μ) (hQ : AEMeasurable Q μ) (ht : AEMeasurable t μ)
    (hBp : ∀ᵐ x ∂μ, 0 < B x) (hQp : ∀ᵐ x ∂μ, 0 < Q x)
    (htp : ∀ᵐ x ∂μ, 0 < t x)
    {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hbound : ∀ᵐ x ∂μ, r ≤ h x) (hW : ∀ᵐ x ∂μ, W x ≤ 1+K*t x) :
    (∫⁻ x, ENNReal.ofReal (tubeMeasureCoefficient n (h x) (B x) (Q x)*W x) ∂μ) ≤
      ENNReal.ofReal (r^(-(n:ℝ)/2)) *
        (∫⁻ x, ENNReal.ofReal (B x) ∂μ)^(1/(2:ℝ)) *
        (∫⁻ x, ENNReal.ofReal (Q x) ∂μ)^(1/(2:ℝ)) +
      ENNReal.ofReal K * (ENNReal.ofReal (r^(-(n:ℝ)/2)) *
        (∫⁻ x, ENNReal.ofReal (B x ^ (1/((n:ℝ)+2)) * Q x ^ (1-1/((n:ℝ)+2))*t x) ∂μ) ^
          (((n:ℝ)+2)/(2*((n:ℝ)+1))) *
        (∫⁻ x, ENNReal.ofReal (B x*t x) ∂μ) ^ (1-((n:ℝ)+2)/(2*((n:ℝ)+1)))) := by
  let F : X → ℝ := fun x => tubeMeasureCoefficient n (h x) (B x) (Q x)
  have hF : AEMeasurable F μ := (hh.pow_const _).mul ((hB.mul hQ).sqrt)
  have hFp : ∀ᵐ x ∂μ, 0 ≤ F x := by
    filter_upwards [hbound,hBp,hQp] with x hx hb hq
    exact (tubeMeasureCoefficient_pos (hr.trans_le hx) hb hq).le
  have he : (∫⁻ x, ENNReal.ofReal (F x)* (1+ENNReal.ofReal K*ENNReal.ofReal (t x)) ∂μ) =
      (∫⁻ x, ENNReal.ofReal (F x) ∂μ)+ENNReal.ofReal K*(∫⁻ x, ENNReal.ofReal (F x*t x) ∂μ) := by
    simp_rw [mul_add,mul_one,mul_left_comm (ENNReal.ofReal (F _)) (ENNReal.ofReal K)]
    rw [lintegral_add_left' (hF.ennreal_ofReal),lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 2
    apply lintegral_congr_ae
    filter_upwards [hFp] with x hx
    exact (ENNReal.ofReal_mul hx).symm
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (F x)*(1+ENNReal.ofReal K*ENNReal.ofReal (t x)) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hFp,htp,hW] with x hf ht hw
      rw [← ENNReal.ofReal_mul hK]
      rw [← ENNReal.ofReal_one]
      rw [← ENNReal.ofReal_add zero_le_one (mul_nonneg hK ht.le),
        ← ENNReal.ofReal_mul hf]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hw hf)
    _ = _ := he
    _ ≤ _ := add_le_add (lintegral_tube_mass_le hB hQ (hBp.mono fun _ hx => hx.le) hr hbound)
      (mul_le_mul_right (lintegral_weighted_tube_mass_le hn hB hQ ht hBp hQp htp hr hbound) _)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualSigmaInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

/- The genuine sigma density is controlled by exactly the three source
geometric integrals: fiber area, large base minors, and cap inverse energy.
No upper bound on sigma or on inverse energy is assumed. -/
theorem affineEpigraph_sigma_interpolation {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (Space k × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set (Space k)} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {Q : Set (Space k)} (hQ : MeasurableSet Q) (hQD : Q ⊆ D)
    (ν : Measure (Metric.sphere (0:E) 1)) [SFinite ν] {r ρ M : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hM : 0 ≤ M) (hbase : ∀ s ∈ Q, ∀ i, r ≤ s i)
    (hinner : ∀ s ∈ Q, Metric.closedBall (0:E) ρ ⊆ {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (houter : ∀ s ∈ Q, ∀ y : E, (s,y) ∈ affineEpigraphPullback Ω u a L → ‖y‖ ≤ M) :
    let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let B := fun q : Space k × Metric.sphere (0:E) 1 =>
      tubeBaseMatrix H (q.1,q.2) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    let A := fun q : Space k × Metric.sphere (0:E) 1 => tubeAngularDensity H (q.1,q.2) bE
    let μ := (volume.restrict Q).prod ν
    (∫⁻ q, ENNReal.ofReal (tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE (q.1,q.2) *
      tubeLogMassWeight H (q.1,q.2)) ∂μ) ≤
      ENNReal.ofReal (ρ^(-(n:ℝ)/2)) *
        (∫⁻ q, ENNReal.ofReal (B q).det ∂μ)^(1/(2:ℝ)) *
        (∫⁻ q, ENNReal.ofReal (A q) ∂μ)^(1/(2:ℝ)) +
      ENNReal.ofReal (M/r^2) * (ENNReal.ofReal (ρ^(-(n:ℝ)/2)) *
        (∫⁻ q, ENNReal.ofReal ((B q).det ^ (1/((n:ℝ)+2)) * (A q) ^ (1-1/((n:ℝ)+2))*(B q)⁻¹.trace) ∂μ) ^
          (((n:ℝ)+2)/(2*((n:ℝ)+1))) *
        (∫⁻ q, ENNReal.ofReal ((B q).det*(B q)⁻¹.trace) ∂μ) ^ (1-((n:ℝ)+2)/(2*((n:ℝ)+1)))) := by
  let : NeZero k := ⟨by omega⟩
  let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let B := fun q : Space k × Metric.sphere (0:E) 1 => tubeBaseMatrix H (q.1,q.2) b
  let A := fun q : Space k × Metric.sphere (0:E) 1 => tubeAngularDensity H (q.1,q.2) bE
  let μ := (volume.restrict Q).prod ν
  have hmap : Continuous (fun q : Space k × Metric.sphere (0:E) 1 => (q.1,(q.2:E))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have he (e : Metric.sphere (0:E) 1) : ‖(e:E)‖ = 1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using e.property
  have he0 (e : Metric.sphere (0:E) 1) : (e:E) ≠ 0 := Metric.ne_of_mem_sphere e.property one_ne_zero
  have hj (q : Space k × Metric.sphere (0:E) 1) (hq : q.1 ∈ Q) : ContDiffAt ℝ ∞ H (q.1,q.2) :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero (hQD hq) (he0 q.2)).1
  have hpq (q : Space k × Metric.sphere (0:E) 1) (hq : q.1 ∈ Q) :=
    affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero (hQD hq) (he0 q.2) b bE
  have hc {f : Space k × E → ℝ}
      (hf : ∀ q : Space k × Metric.sphere (0:E) 1, q.1 ∈ Q → ContinuousAt f (q.1,q.2)) :
      AEMeasurable (fun q : Space k × Metric.sphere (0:E) 1 => f (q.1,q.2)) μ := by
    change AEMeasurable _ ((volume.restrict Q).prod ν)
    rw [Measure.restrict_prod_eq_prod_univ]
    apply ContinuousOn.aemeasurable _ (hQ.prod MeasurableSet.univ)
    intro q hq
    exact ((hf q hq.1).comp (f := fun z : Space k × Metric.sphere (0:E) 1 => (z.1,(z.2:E)))
      (x := q) hmap.continuousAt).continuousWithinAt
  have hHae := hc (f := H) (fun q hq => (hj q hq).continuousAt)
  have hBae := hc (f := fun z => (tubeBaseMatrix H z b).det) (fun q hq =>
    (((continuousDetRows (ι := Fin k)).contDiff.contDiffAt.comp (q.1,(q.2:E))
      (contDiffAt_tubeBaseMatrix (hj q hq) b))).continuousAt)
  have hAae := hc (f := fun z => tubeAngularDensity H z bE) (fun q hq =>
    (contDiffAt_tubeAngularDensity (hj q hq) bE).continuousAt)
  have htae := hc (f := fun z => (tubeBaseMatrix H z b)⁻¹.trace) (by
    intro q hq
    change ContinuousAt (fun z => ∑ i, (tubeBaseMatrix H z b)⁻¹ i i) (q.1,q.2)
    have ht : ContDiffAt ℝ ∞ (fun z => ∑ i, (tubeBaseMatrix H z b)⁻¹ i i) (q.1,q.2) :=
      ContDiffAt.sum fun i _ => contDiffAt_inverse_matrix_entry_param
        (contDiffAt_tubeBaseMatrix (hj q hq) b) (hpq q hq).1.det_pos.ne' i i
    exact ht.continuousAt)
  have hqa : ∀ᵐ q ∂μ, q.1 ∈ Q := by
    change ∀ᵐ q ∂(volume.restrict Q).prod ν, q.1 ∈ Q
    rw [Measure.restrict_prod_eq_prod_univ]
    filter_upwards [ae_restrict_mem (μ := volume.prod ν) (hQ.prod MeasurableSet.univ)] with q hq
    exact hq.1
  apply lintegral_sigma_mass_le hn hHae hBae hAae htae
    (hqa.mono fun q hq => (hpq q hq).1.det_pos)
    (hqa.mono fun q hq => (hpq q hq).2.1)
    (hqa.mono fun q hq => (hpq q hq).1.inv.trace_pos) hρ (div_nonneg hM (sq_nonneg r))
  · filter_upwards [hqa] with q hq
    exact homogeneousSupport_ge_of_ball (hK q.1 (hQD hq)) (he q.2) hρ.le (hinner q.1 hq)
  · filter_upwards [hqa] with q hq
    apply tubeLogMassWeight_le_trace H (q.1,q.2) hr (hbase q.1 hq) (hpq q hq).2.2.le
    · exact (le_abs_self _).trans (homogeneousSupport_abs_le_of_radius (hK q.1 (hQD hq))
        ⟨0,interior_subset (hzero q.1 (hQD hq))⟩ (he q.2) (houter q.1 hq))
    · exact (hpq q hq).1

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

variable [FiniteDimensional ℝ S] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ S] in
/-- A cap containing a base fiber gives compactness of that actual fiber. -/
lemma affineEpigraphPullback_fiber_isCompact {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hc : IsClosed (sourceEpigraph Ω u))
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ)) (ℓ : S →L[ℝ] ℝ)
    {b R : ℝ}
    (hcap : ∀ p ∈ affineEpigraphPullback Ω u a L, ℓ p.1 ≤ b → ‖p‖ ≤ R)
    {s : S} (hs : ℓ s ≤ b) : IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L} := by
  apply isCompact_iff_isClosed_bounded.mpr
  refine ⟨(affineEpigraphPullback_isClosed hc a L).preimage
    (continuous_const.prodMk continuous_id),?_⟩
  apply (Metric.isBounded_closedBall (x := (0:E)) (r := R)).subset
  intro y hy
  exact mem_closedBall_zero_iff.mpr ((norm_snd_le (s,y)).trans (hcap (s,y) hy hs))

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
lemma IsModelShape.normalized_center_ball {k m : ℕ} {C : Set (Space k × Space m)}
    (hC : IsModelShape C) {r : ℝ} (hr : 0 < r)
    (hin : closedBall (0 : Space m) r ⊆
      modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ)))) :
    closedBall ((WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))), (0 : Space m))
      (min (1/4) (r/4)) ⊆ interior C := by
  rintro ⟨s,y⟩ hp
  have hd := mem_closedBall.mp hp
  have hs : ‖s - WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))‖ ≤ min (1/4) (r/4) := by
    rw [← dist_eq_norm]
    exact le_trans (le_max_left _ _) hd
  have hy : ‖y‖ ≤ min (1/4) (r/4) := by
    simpa only [dist_zero_right] using le_trans (le_max_right _ _) hd
  apply hC.normalized_fiber_interior hr (a := 1/2) (by norm_num) (by norm_num) hin
  · intro i
    have hi := (PiLp.norm_apply_le (s - WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) i).trans hs
    change |s i-1| ≤ min (1/4) (r/4) at hi
    linarith [le_abs_self (-(s i-1)),abs_neg (s i-1),min_le_left (1/4:ℝ) (r/4)]
  · linarith [hy.trans (min_le_right (1/4:ℝ) (r/4))]

/- Eventual cap bounds with constants fixed before the approximating sequence. -/
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
theorem LocalDistanceConverges.eventually_normalized_center_ball
    {k m : ℕ} {Cj : ℕ → Set (Space k × Space m)} {C : Set (Space k × Space m)}
    (h : LocalDistanceConverges Cj C) (hC : IsModelShape C)
    (hclj : ∀ j, IsClosed (Cj j)) (hcvj : ∀ j, Convex ℝ (Cj j))
    (hnej : ∀ j, (Cj j).Nonempty) {r : ℝ} (hr : 0 < r)
    (hin : closedBall (0 : Space m) r ⊆
      modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ)))) :
    ∀ᶠ j in atTop, closedBall
      ((WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))), (0 : Space m))
      (min (1/4) (r/4)) ⊆ Cj j := by
  exact h.eventually_normed_compact_subset hclj hcvj hnej
    (isCompact_closedBall _ _) (hC.normalized_center_ball hr hin)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TiltedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- Every coefficient of these covectors is positive, so their affine caps
are uniformly bounded in the orthant model. -/

lemma inverse_trace_tilted_identity (A : Matrix ι ι ℝ) :
    (∑ r, inverseMatrixPair A (capTiltedCovector r) (capTiltedCovector r)) =
      A⁻¹.trace + ((Fintype.card ι:ℝ)+2)*inverseMatrixPair A (fun _ => 1) (fun _ => 1) := by
  have hd (r : ι) : inverseMatrixPair A (Pi.single r 1) (Pi.single r 1) = A⁻¹ r r := by
    simp [inverseMatrixPair,Pi.single_apply]
  have hl (r : ι) : inverseMatrixPair A (fun _ => 1) (Pi.single r 1) = ∑ j, A⁻¹ r j := by
    simp [inverseMatrixPair,Pi.single_apply]
  have hr (r : ι) : inverseMatrixPair A (Pi.single r 1) (fun _ => 1) = ∑ i, A⁻¹ i r := by
    simp [inverseMatrixPair,Pi.single_apply]
  have hone : inverseMatrixPair A (fun _ => 1) (fun _ => 1) = ∑ j, ∑ i, A⁻¹ i j := by
    simp [inverseMatrixPair]
  have hx (r : ι) : inverseMatrixPair A (capTiltedCovector r) (capTiltedCovector r) =
      inverseMatrixPair A (fun _ => 1) (fun _ => 1) + (∑ j, A⁻¹ r j) +
        ((∑ i, A⁻¹ i r) + A⁻¹ r r) := by
    change inverseMatrixPair A (fun i => (fun _ : ι => (1:ℝ)) i + (Pi.single r 1 : ι → ℝ) i)
      (fun i => (fun _ : ι => (1:ℝ)) i + (Pi.single r 1 : ι → ℝ) i) = _
    rw [inverseMatrixPair_add_left A (fun _ => 1) (Pi.single r 1),
      inverseMatrixPair_add_right A (fun _ => 1) (fun _ => 1) (Pi.single r 1),
      inverseMatrixPair_add_right A (Pi.single r 1) (fun _ => 1) (Pi.single r 1),hl,hr,hd]
  simp_rw [hx]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [show (∑ r, ∑ j, A⁻¹ r j) = ∑ j, ∑ i, A⁻¹ i j by rw [Finset.sum_comm],← hone]
  change _ = (∑ i, A⁻¹ i i)+_
  ring

/- The literal trace of the inverse Hessian is controlled by the finite
family of tilted cap energies, with sharp coefficient one. -/
lemma inverse_trace_le_tilted {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    A⁻¹.trace ≤ ∑ r, inverseMatrixPair A (capTiltedCovector r) (capTiltedCovector r) := by
  rw [inverse_trace_tilted_identity]
  exact le_add_of_nonneg_right (mul_nonneg (by positivity)
    (inverseMatrixPair_self_nonneg hA _))

lemma inverse_trace_nonneg {A : Matrix ι ι ℝ} (hA : A.PosDef) : 0 ≤ A⁻¹.trace := by
  exact Finset.sum_nonneg (fun i _ => hA.inv.posSemidef.diag_nonneg (i := i))

/- Integration of the preceding finite-family estimate. This closes the
last purely algebraic summation step after actual cap transport. -/

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

/-- The unnormalized support conormal has norm at least one at every unit normal.
This is independent of graph stationarity and uses the product norm literally. -/
lemma one_le_norm_supportConormal (H : S × E → ℝ) (s : S) {e : E} (he : ‖e‖ = 1) :
    1 ≤ ‖supportConormal H (s,e)‖ := by
  have hv : supportConormal H (s,e) (0,e) = -1 := by
    have hz : (fderiv ℝ H (s,e)) (0,0) = 0 := map_zero _
    simp [supportConormal,he,hz]
  have hn := (supportConormal H (s,e)).le_opNorm ((0:S),e)
  simpa [hv,Prod.norm_def,he] using hn

end SigmaCapHelpers

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NormalizedCellGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
section NormalizedSigmaDependencies

section NormalizedCellGeometry
open Metric

lemma isOpen_normalizedCellDomain (k : ℕ) : IsOpen (normalizedCellDomain k) := by
  have he : normalizedCellDomain k = ⋂ i : Fin k, {s : Space k | s i ∈ Ioo (1/4) 4} := by
    ext s; simp [normalizedCellDomain]
  rw [he]
  exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (PiLp.continuous_apply 2 _ i))

lemma convex_normalizedCellDomain (k : ℕ) : Convex ℝ (normalizedCellDomain k) := by
  intro x hx y hy a b ha hb hab i
  change 1/4 < a*x i+b*y i ∧ a*x i+b*y i < 4
  exact (convex_Ioo (1/4:ℝ) 4) (hx i) (hy i) ha hb hab

lemma isCompact_normalizedCell (k : ℕ) : IsCompact (normalizedCell k) := by
  convert! (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi fun _ : Fin k => (isCompact_Icc : IsCompact (Icc (1/2:ℝ) 2))) using 1
  all_goals try with_reducible_and_instances rfl
  ext s
  simp only [normalizedCell,Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_univ_pi,Set.mem_Icc]
  rfl

lemma normalizedCell_subset_domain (k : ℕ) : normalizedCell k ⊆ normalizedCellDomain k := by
  intro s hs i
  have := hs i
  constructor <;> linarith [this.1,this.2]

lemma normalizedCell_margin {k : ℕ} {s : Space k} (hs : s ∈ normalizedCell k) :
    closedBall s (1/8:ℝ) ⊆ normalizedCellDomain k := by
  intro t ht i
  have hdist : |t i-s i| ≤ 1/8 := by
    have hh := (PiLp.norm_apply_le (t-s) i).trans (mem_closedBall.mp ht)
    simpa only [dist_eq_norm,PiLp.sub_apply,Real.norm_eq_abs] using hh
  obtain ⟨hl,hu⟩ := abs_le.mp hdist
  have hh := hs i
  constructor <;> linarith [hh.1,hh.2]

lemma capTiltedForm_eq_sum {k : ℕ} (j : Fin k) (s : Space k) :
    capTiltedForm j s = (∑ i, s i) + s j := by
  simp only [capTiltedForm_apply,capTiltedCovector,add_mul,one_mul,Finset.sum_add_distrib]
  simp [Pi.single_apply,ite_mul]

lemma capTiltedForm_coord_bound {k : ℕ} {s : Space k} {b : ℝ}
    (hs : ∀ i, s i ≤ b) (j : Fin k) : capTiltedForm j s ≤ ((k:ℝ)+1)*b := by
  rw [capTiltedForm_eq_sum]
  have hh : (∑ i : Fin k, s i) ≤ (k:ℝ)*b := by
    calc
      _ ≤ ∑ _i : Fin k, b := Finset.sum_le_sum (fun i _ => hs i)
      _ = _ := by simp
  linarith [hs j]

lemma capTiltedForm_center {k : ℕ} (j : Fin k) :
    capTiltedForm j (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) = (k:ℝ)+1 := by
  rw [capTiltedForm_eq_sum]
  simp

lemma capTiltedCovector_one_le {k : ℕ} (j i : Fin k) : 1 ≤ capTiltedCovector j i := by
  by_cases he : i=j <;> simp [capTiltedCovector,he]
end NormalizedCellGeometry



end NormalizedSigmaDependencies
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TiltedLIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section TiltedLIntegral
open MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- The tilted-cap trace estimate for nonnegative integrals, with no a priori
integrability assumption on the trace being bounded. -/
lemma lintegral_inverse_trace_le_tilted {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {B : α → Matrix ι ι ℝ} {I : α → ℝ}
    (hB : ∀ᵐ x ∂μ, (B x).PosDef) (hI : 0 ≤ᵐ[μ] I)
    (hc : ∀ r, AEMeasurable (fun x => ENNReal.ofReal (I x*inverseMatrixPair (B x)
      (capTiltedCovector r) (capTiltedCovector r))) μ) :
    (∫⁻ x, ENNReal.ofReal (I x*(B x)⁻¹.trace) ∂μ) ≤
      ∑ r, ∫⁻ x, ENNReal.ofReal (I x*inverseMatrixPair (B x)
        (capTiltedCovector r) (capTiltedCovector r)) ∂μ := by
  rw [← lintegral_finsetSum' _ (fun r _ => hc r)]
  apply lintegral_mono_ae
  filter_upwards [hB,hI] with x hx hIx
  rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ => mul_nonneg hIx
    (inverseMatrixPair_self_nonneg hx _)),← Finset.mul_sum]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (inverse_trace_le_tilted hx) hIx)
end TiltedLIntegral

section ActualSigmaCaps
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

/- The genuine sigma density is controlled by exactly the three source
geometric integrals: fiber area, large base minors, and cap inverse energy.
No upper bound on sigma or on inverse energy is assumed. -/
theorem affineEpigraph_sigma_cap_interpolation {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (Space k × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set (Space k)} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {Q : Set (Space k)} (hQ : MeasurableSet Q) (hQD : Q ⊆ D)
    (ν : Measure (Metric.sphere (0:E) 1)) [SFinite ν] {r ρ M : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hM : 0 ≤ M) (hbase : ∀ s ∈ Q, ∀ i, r ≤ s i)
    (hinner : ∀ s ∈ Q, Metric.closedBall (0:E) ρ ⊆ {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (houter : ∀ s ∈ Q, ∀ y : E, (s,y) ∈ affineEpigraphPullback Ω u a L → ‖y‖ ≤ M) :
    let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let B := fun q : Space k × Metric.sphere (0:E) 1 =>
      tubeBaseMatrix H (q.1,q.2) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    let A := fun q : Space k × Metric.sphere (0:E) 1 => tubeAngularDensity H (q.1,q.2) bE
    let μ := (volume.restrict Q).prod ν
    (∫⁻ q, ENNReal.ofReal (tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE (q.1,q.2) *
      tubeLogMassWeight H (q.1,q.2)) ∂μ) ≤
      ENNReal.ofReal (ρ^(-(n:ℝ)/2)) *
        (∫⁻ q, ENNReal.ofReal (B q).det ∂μ)^(1/(2:ℝ)) *
        (∫⁻ q, ENNReal.ofReal (A q) ∂μ)^(1/(2:ℝ)) +
      ENNReal.ofReal (M/r^2) * (ENNReal.ofReal (ρ^(-(n:ℝ)/2)) *
        (∑ j, ∫⁻ q, ENNReal.ofReal ((B q).det ^ (1/((n:ℝ)+2)) * (A q) ^ (1-1/((n:ℝ)+2))*inverseMatrixPair (B q) (capTiltedCovector j) (capTiltedCovector j)) ∂μ) ^
          (((n:ℝ)+2)/(2*((n:ℝ)+1))) *
        (∫⁻ q, ENNReal.ofReal ((B q).det*(B q)⁻¹.trace) ∂μ) ^ (1-((n:ℝ)+2)/(2*((n:ℝ)+1)))) := by
  let : NeZero k := ⟨by omega⟩
  let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let B := fun q : Space k × Metric.sphere (0:E) 1 => tubeBaseMatrix H (q.1,q.2) b
  let A := fun q : Space k × Metric.sphere (0:E) 1 => tubeAngularDensity H (q.1,q.2) bE
  let μ := (volume.restrict Q).prod ν
  have hmap : Continuous (fun q : Space k × Metric.sphere (0:E) 1 => (q.1,(q.2:E))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have he (e : Metric.sphere (0:E) 1) : ‖(e:E)‖ = 1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using e.property
  have he0 (e : Metric.sphere (0:E) 1) : (e:E) ≠ 0 := Metric.ne_of_mem_sphere e.property one_ne_zero
  have hj (q : Space k × Metric.sphere (0:E) 1) (hq : q.1 ∈ Q) : ContDiffAt ℝ ∞ H (q.1,q.2) :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero (hQD hq) (he0 q.2)).1
  have hpq (q : Space k × Metric.sphere (0:E) 1) (hq : q.1 ∈ Q) :=
    affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero (hQD hq) (he0 q.2) b bE
  have hc {f : Space k × E → ℝ}
      (hf : ∀ q : Space k × Metric.sphere (0:E) 1, q.1 ∈ Q → ContinuousAt f (q.1,q.2)) :
      AEMeasurable (fun q : Space k × Metric.sphere (0:E) 1 => f (q.1,q.2)) μ := by
    change AEMeasurable _ ((volume.restrict Q).prod ν)
    rw [Measure.restrict_prod_eq_prod_univ]
    apply ContinuousOn.aemeasurable _ (hQ.prod MeasurableSet.univ)
    intro q hq
    exact ((hf q hq.1).comp (f := fun z : Space k × Metric.sphere (0:E) 1 => (z.1,(z.2:E)))
      (x := q) hmap.continuousAt).continuousWithinAt
  have hHae := hc (f := H) (fun q hq => (hj q hq).continuousAt)
  have hBae := hc (f := fun z => (tubeBaseMatrix H z b).det) (fun q hq =>
    (((continuousDetRows (ι := Fin k)).contDiff.contDiffAt.comp (q.1,(q.2:E))
      (contDiffAt_tubeBaseMatrix (hj q hq) b))).continuousAt)
  have hAae := hc (f := fun z => tubeAngularDensity H z bE) (fun q hq =>
    (contDiffAt_tubeAngularDensity (hj q hq) bE).continuousAt)
  have htae := hc (f := fun z => (tubeBaseMatrix H z b)⁻¹.trace) (by
    intro q hq
    change ContinuousAt (fun z => ∑ i, (tubeBaseMatrix H z b)⁻¹ i i) (q.1,q.2)
    have ht : ContDiffAt ℝ ∞ (fun z => ∑ i, (tubeBaseMatrix H z b)⁻¹ i i) (q.1,q.2) :=
      ContDiffAt.sum fun i _ => contDiffAt_inverse_matrix_entry_param
        (contDiffAt_tubeBaseMatrix (hj q hq) b) (hpq q hq).1.det_pos.ne' i i
    exact ht.continuousAt)
  have hqa : ∀ᵐ q ∂μ, q.1 ∈ Q := by
    change ∀ᵐ q ∂(volume.restrict Q).prod ν, q.1 ∈ Q
    rw [Measure.restrict_prod_eq_prod_univ]
    filter_upwards [ae_restrict_mem (μ := volume.prod ν) (hQ.prod MeasurableSet.univ)] with q hq
    exact hq.1
  let I : Space k × Metric.sphere (0:E) 1 → ℝ := fun q =>
    (B q).det ^ (1/((n:ℝ)+2)) * (A q) ^ (1-1/((n:ℝ)+2))
  have hIae : AEMeasurable I μ := (hBae.pow_const _).mul (hAae.pow_const _)
  have hinv (i j : Fin k) : AEMeasurable (fun q => (B q)⁻¹ i j) μ :=
    hc (f := fun z => (tubeBaseMatrix H z b)⁻¹ i j) (fun q hq =>
      (contDiffAt_inverse_matrix_entry_param (contDiffAt_tubeBaseMatrix (hj q hq) b)
        (hpq q hq).1.det_pos.ne' i j).continuousAt)
  have hcap (j : Fin k) : AEMeasurable (fun q => ENNReal.ofReal
      (I q*inverseMatrixPair (B q) (capTiltedCovector j) (capTiltedCovector j))) μ := by
    apply AEMeasurable.ennreal_ofReal
    apply hIae.mul
    unfold inverseMatrixPair
    apply Finset.aemeasurable_fun_sum
    intro l _
    apply Finset.aemeasurable_fun_sum
    intro i _
    exact ((hinv i l).mul_const _).mul_const _
  have htrace := lintegral_inverse_trace_le_tilted
    (hqa.mono fun q hq => (hpq q hq).1)
    (hqa.mono fun q hq => mul_nonneg (Real.rpow_nonneg (hpq q hq).1.det_pos.le _)
      (Real.rpow_nonneg (hpq q hq).2.1.le _)) hcap
  have hs := affineEpigraph_sigma_interpolation hn hk hΩ hcv hu hp a L hD hK hzero bE
    hQ hQD ν hr hρ hM hbase hinner houter
  refine hs.trans ?_
  have hα : 0 ≤ ((n:ℝ)+2)/(2*((n:ℝ)+1)) := by positivity
  gcongr
end ActualSigmaCaps

-- END

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_UniformSigmaCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/-- A uniform weighted actual-sigma bound in a normalized positive cell.
The cap energy, large minors and fiber area are all PRODUCED from literal geometry
and the unchanged complete original PDE. In particular no integrability or energy
bound is an assumption. All constants precede the varying graph and normalization. -/
theorem complete_affineMaximal_uniform_sigma_bound {n k m d : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
    (f : WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m)
    {D Q : Set (Space k)} (hD : IsOpen D) (hDc : Convex ℝ D)
    (hQ : IsCompact Q) (hQD : Q ⊆ D)
    (o : Space k × Space m) {ε r₀ r₁ α ρ M R T RQ : ℝ}
    (hε : 0 < ε) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hα : 0 < α) (hρ : 0 < ρ)
    (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hogap : ∀ j : Fin k, capTiltedForm j o.1 < T+ε)
    (hDheight : ∀ j : Fin k, ∀ s ∈ D, capTiltedForm j s ≤ T+ε)
    (hQheight : ∀ j : Fin k, ∀ s ∈ Q, capTiltedForm j s ≤ T-ε)
    (hbase : ∀ s ∈ Q, ∀ i, α ≤ s i)
    (hmargin : ∀ s ∈ Q, Metric.closedBall s r₁ ⊆ D)
    (hRQ : ∀ s ∈ Q, ‖s‖ ≤ RQ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ {Ω : Set (Space n)}, IsOpen Ω → Ω.Nonempty → Convex ℝ Ω →
      ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
      (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u → EuclideanGraphComplete Ω u →
      ∀ (a : Space n × ℝ) (L : (Space k × Space m) ≃L[ℝ] (Space n × ℝ)),
      (∀ j : Fin k, ∀ p ∈ affineEpigraphPullback Ω u a L,
        capTiltedForm j p.1 ≤ T+ε → ‖p‖ ≤ R) →
      Metric.closedBall o r₀ ⊆ affineEpigraphPullback Ω u a L →
      (∀ s ∈ D, Metric.closedBall (0:Space m) ρ ⊆
        {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) →
      (∀ s ∈ D, ∀ y : Space m, (s,y) ∈ affineEpigraphPullback Ω u a L → ‖y‖ ≤ M) →
      let H := fun q : Space k × Space m =>
        homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
      let bE := (EuclideanSpace.basisFun (Fin m) ℝ).reindex eE
      (∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
        ENNReal.ofReal (tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE
          (q.1,q.2) * tubeLogMassWeight H (q.1,q.2))
        ∂(volume.restrict Q).prod (volume : Measure (Space m)).toSphere) ≤ C := by
  let : NeZero k := ⟨by omega⟩
  let : NeZero m := ⟨by omega⟩
  let bS := EuclideanSpace.basisFun (Fin k) ℝ
  let bF := EuclideanSpace.basisFun (Fin d) ℝ
  let bE := (EuclideanSpace.basisFun (Fin m) ℝ).reindex eE
  choose C hC hc using fun j : Fin k =>
    complete_affineMaximal_uniform_spherical_cap_bound bS bF bE f e
      (capTiltedForm j) o hε hr₀ hR T (hogap j)
  let ν : Measure (Metric.sphere (0:Space m) 1) := volume.toSphere
  let μ : Measure (Space k × Metric.sphere (0:Space m) 1) := (volume.restrict Q).prod ν
  let Cm : ℝ≥0∞ := (((k:ℝ≥0∞)+1)*volume (Metric.closedBall (0:Space k) (2*M/r₁+RQ))) * ν Set.univ
  let Ca : ℝ≥0∞ := ((m:ℝ≥0∞)^2 * volume (Metric.closedBall (0:Space m) (M+1))) * volume Q
  let Ce : ℝ≥0∞ := ∑ j, ENNReal.ofReal (C j)
  let γ : ℝ := ((n:ℝ)+2)/(2*((n:ℝ)+1))
  have hγ : 0 ≤ γ := by dsimp [γ]; positivity
  have hγ' : 0 ≤ 1-γ := by
    dsimp [γ]
    have hd : 0 < 2*((n:ℝ)+1) := by positivity
    have hh : ((n:ℝ)+2)/(2*((n:ℝ)+1)) ≤ 1 := (div_le_one hd).mpr (by linarith)
    linarith
  let Cσ : ℝ≥0∞ := ENNReal.ofReal (ρ^(-(n:ℝ)/2)) * Cm^(1/(2:ℝ)) * Ca^(1/(2:ℝ)) +
    ENNReal.ofReal (M/α^2) * (ENNReal.ofReal (ρ^(-(n:ℝ)/2)) * Ce^γ * Cm^(1-γ))
  have hCm : Cm ≠ ⊤ := by
    dsimp [Cm, ν]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp)
      (isCompact_closedBall _ _).measure_ne_top) (measure_ne_top _ _)
  have hCa : Ca ≠ ⊤ := by
    dsimp [Ca]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp)
      (isCompact_closedBall _ _).measure_ne_top) hQ.measure_ne_top
  have hCe : Ce ≠ ⊤ := by dsimp [Ce]; simp
  refine ⟨Cσ, ?_, ?_⟩
  · dsimp [Cσ]
    finiteness
  intro Ω hΩ hne hcv u hu hp hmP hcomplete a L hcaps hball hinter houter
  let H := fun q : Space k × Space m =>
    homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let B := fun q : Space k × Metric.sphere (0:Space m) 1 => tubeBaseMatrix H (q.1,q.2) bS.toBasis
  let A := fun q : Space k × Metric.sphere (0:Space m) 1 => tubeAngularDensity H (q.1,q.2) bE
  have hclosed := sourceEpigraph_closed hΩ hne hcv hu hp hcomplete
  have hK (s : Space k) (hs : s ∈ D) : IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L} :=
    affineEpigraphPullback_fiber_isCompact hclosed a L (capTiltedForm (0 : Fin k))
      (hcaps 0) (hDheight 0 s hs)
  have hzero (s : Space k) (hs : s ∈ D) : (0 : Space m) ∈
      interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L} :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 hρ)
      (hinter s hs))
  have hqa : ∀ᵐ q ∂μ, q.1 ∈ Q := by
    dsimp [μ]
    rw [Measure.restrict_prod_eq_prod_univ]
    filter_upwards [ae_restrict_mem (μ := volume.prod ν) (hQ.measurableSet.prod MeasurableSet.univ)] with q hq
    exact hq.1
  have he (q : Metric.sphere (0:Space m) 1) : ‖(q : Space m)‖ = 1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using q.property
  have he0 (q : Metric.sphere (0:Space m) 1) : (q : Space m) ≠ 0 :=
    Metric.ne_of_mem_sphere q.property one_ne_zero
  have hpos (q : Space k × Metric.sphere (0:Space m) 1) (hq : q.1 ∈ Q) :=
    affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero (hQD hq) (he0 q.2) bS.toBasis bE
  have hmin := affineEpigraph_product_minors_bound hm hΩ hcv hu hp a L hD hDc hK hzero
    hQ.measurableSet hQD hr₁ hM hmargin houter hRQ
  change (∫⁻ q, ENNReal.ofReal ((B q).det*(1+(B q)⁻¹.trace)) ∂μ) ≤ Cm at hmin
  have hdet : (∫⁻ q, ENNReal.ofReal (B q).det ∂μ) ≤ Cm := by
    apply le_trans (lintegral_mono_ae ?_) hmin
    filter_upwards [hqa] with q hq
    apply ENNReal.ofReal_le_ofReal
    have hd := (hpos q hq).1.det_pos.le
    have ht := inverse_trace_nonneg (hpos q hq).1
    nlinarith
  have htrace : (∫⁻ q, ENNReal.ofReal ((B q).det * (B q)⁻¹.trace) ∂μ) ≤ Cm := by
    apply le_trans (lintegral_mono_ae ?_) hmin
    filter_upwards [hqa] with q hq
    apply ENNReal.ofReal_le_ofReal
    have hd := (hpos q hq).1.det_pos.le
    nlinarith
  have harea : (∫⁻ q, ENNReal.ofReal (A q) ∂μ) ≤ Ca := by
    have ha := affineEpigraph_product_fiber_area_bound hm hΩ hcv hu hp a L hD hK hzero
      hQ.measurableSet hQD (fun s hs y hy => houter s (hQD hs) y hy)
    simpa only [A,bE,tubeAngularDensity_reindex] using ha
  have hncard : (Fintype.card (Fin k):ℝ)+Fintype.card (Fin d) = n := by
    have hh := Fintype.card_congr e
    simp only [Fintype.card_fin,Fintype.card_sum] at hh
    simp only [Fintype.card_fin]
    exact_mod_cast hh.symm
  have henergy (j : Fin k) :
      (∫⁻ q, ENNReal.ofReal ((B q).det^(1/((n:ℝ)+2)) * (A q)^(1-1/((n:ℝ)+2)) *
        inverseMatrixPair (B q) (capTiltedCovector j) (capTiltedCovector j)) ∂μ) ≤ ENNReal.ofReal (C j) := by
    have hb := hc j hΩ hne hcv hu hp hmP hcomplete a L hD (hDheight j) hzero (hcaps j) hball
      hQ.measurableSet hQD (hQheight j)
    simp only [hncard,bS,capTiltedForm_basis] at hb
    apply le_trans (lintegral_mono_ae ?_) hb
    filter_upwards [hqa] with q hq
    apply ENNReal.ofReal_le_ofReal
    have hn := one_le_norm_supportConormal H q.1 (he q.2)
    have hi := inverseMatrixPair_self_nonneg (hpos q hq).1 (capTiltedCovector j)
    have hI : 0 ≤ (B q).det^(1/((n:ℝ)+2)) * (A q)^(1-1/((n:ℝ)+2)) :=
      mul_nonneg (Real.rpow_nonneg (hpos q hq).1.det_pos.le _)
        (Real.rpow_nonneg (hpos q hq).2.1.le _)
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hi hn) hI
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => henergy j)
  have hs := affineEpigraph_sigma_cap_interpolation hn hk hΩ hcv hu hp a L hD hK hzero bE
    hQ.measurableSet hQD ν hα hρ hM hbase (fun s hs => hinter s (hQD hs))
      (fun s hs => houter s (hQD hs))
  apply hs.trans
  change _ ≤ Cσ
  dsimp only [Cσ]
  gcongr

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

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NormalizedSigma
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Metric Filter

/-- A normalized maximal model and local convergence produce the full literal
geometric hypotheses of the sigma-cell estimate. The uniform constant is fixed
before the model, original solution or approximating affine coordinates. -/
theorem normalized_model_uniform_actual_sigma_oai {n k m d : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
    (f : WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m)
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    ∃ Cσ : ℝ≥0∞, Cσ ≠ ⊤ ∧ ∀ {Ω : Set (Space n)}, IsOpen Ω → Ω.Nonempty → Convex ℝ Ω →
      ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
      (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u → EuclideanGraphComplete Ω u →
      ∀ (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
      (C : Set (Space k × Space m)), IsModelShape C →
      closedBall 0 r ⊆ modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) →
      modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R →
      LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L j)) C →
      ∀ᶠ j in atTop,
      let H := fun q : Space k × Space m =>
        homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u (a j) (L j)} q.2
      let bE := (EuclideanSpace.basisFun (Fin m) ℝ).reindex eE
      (∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
        ENNReal.ofReal (tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE
          (q.1,q.2) * tubeLogMassWeight H (q.1,q.2))
        ∂(volume.restrict (normalizedCell k)).prod (volume : Measure (Space m)).toSphere) ≤ Cσ := by
  let : NeZero k := ⟨by omega⟩
  let : NeZero m := ⟨by omega⟩
  let T : ℝ := 5*((k:ℝ)+1)
  let B : ℝ := T+1
  let Rcap : ℝ := max (Real.sqrt k * max 1 B) (max 1 B*R)+1
  let M : ℝ := max (Real.sqrt k * max 1 ((k:ℝ)*4+1)) (max 1 ((k:ℝ)*4+1)*R)+1
  let o : Space k × Space m := (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ)),0)
  have hRc : 0 ≤ Rcap := by
    dsimp [Rcap]
    exact add_nonneg
      ((mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hR).trans (le_max_right _ _))
      zero_le_one
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hT : 0 < B := by dsimp [B,T]; positivity
  have hogap (j : Fin k) : capTiltedForm j o.1 < T+1 := by
    rw [show o.1 = WithLp.toLp 2 (fun _ : Fin k => (1:ℝ)) from rfl,capTiltedForm_center]
    dsimp [T]
    have hk0 : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  have hDh (j : Fin k) (s : Space k) (hs : s ∈ normalizedCellDomain k) : capTiltedForm j s ≤ T+1 := by
    have hh := capTiltedForm_coord_bound (fun i => (hs i).2.le) j
    dsimp [T]
    have hk0 : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  have hQh (j : Fin k) (s : Space k) (hs : s ∈ normalizedCell k) : capTiltedForm j s ≤ T-1 := by
    have hh := capTiltedForm_coord_bound (fun i => (hs i).2) j
    dsimp [T]
    have hk0 : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  obtain ⟨Cσ,hCσ,hprod⟩ := complete_affineMaximal_uniform_sigma_bound hn hk hm e eE f
    (isOpen_normalizedCellDomain k) (convex_normalizedCellDomain k) (isCompact_normalizedCell k)
    (normalizedCell_subset_domain k) o (ε:=1) (r₀:=min (1/4) (r/4)) (r₁:=1/8) (α:=1/2)
    (ρ:=r/8) (M:=M) (R:=Rcap) (T:=T) (RQ:=Real.sqrt k*2)
    (by norm_num) (lt_min (by norm_num) (by positivity)) (by norm_num) (by norm_num)
    (by positivity) hM hRc hogap hDh hQh (fun s hs i => (hs i).1)
    (fun s hs => normalizedCell_margin hs)
    (fun s hs => norm_le_sqrt_card_mul_of_coord_le (by norm_num : (0:ℝ)<2)
      (fun i => by rw [abs_of_nonneg (by linarith [(hs i).1])]; exact (hs i).2))
  refine ⟨Cσ,hCσ,?_⟩
  intro Ω hΩ hne hcv u hu hp hmP hcomplete a L C hC hin hout hlim
  have hclj (j : ℕ) : IsClosed (affineEpigraphPullback Ω u (a j) (L j)) :=
    affineEpigraphPullback_isClosed (sourceEpigraph_closed hΩ hne hcv hu hp hcomplete) (a j) (L j)
  have hcvj (j : ℕ) : Convex ℝ (affineEpigraphPullback Ω u (a j) (L j)) :=
    ((sourceEpigraph_convex hΩ hcv hu hp).translate_preimage_right (a j)).linear_preimage
      (L j).toLinearMap
  have hnej (j : ℕ) : (affineEpigraphPullback Ω u (a j) (L j)).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    refine ⟨(L j).symm ((x,u x)-a j),?_⟩
    change (a j + (L j) ((L j).symm ((x,u x)-a j))).1 ∈ Ω ∧ _
    simp [hx]
  have hcaps : ∀ᶠ j in atTop, ∀ i : Fin k, ∀ p ∈ affineEpigraphPullback Ω u (a j) (L j),
      capTiltedForm i p.1 ≤ T+1 → ‖p‖ ≤ Rcap := by
    apply (Filter.eventually_all.mpr (fun i => hlim.eventually_normalized_cap_radius hC hclj hcvj hnej
      (a:=capTiltedCovector i) (α:=1) hT zero_lt_one (capTiltedCovector_one_le i) hout)).mono
    intro j hj i p hp hb
    have he : positiveBaseForm (capTiltedCovector i) p = capTiltedForm i p.1 := by
      simp only [positiveBaseForm_apply,capTiltedForm_apply]
    have hh := hj i (show p ∈ affineEpigraphPullback Ω u (a j) (L j) ∩
      {p | positiveBaseForm (capTiltedCovector i) p ≤ B} from ⟨hp,by change positiveBaseForm (capTiltedCovector i) p ≤ B; simpa only [he,B] using hb⟩)
    have hh' : ‖p‖ < Rcap := by simpa only [div_one,Metric.mem_ball,dist_zero_right,Rcap] using hh
    exact hh'.le
  have hballs := hlim.eventually_normalized_center_ball hC hclj hcvj hnej hr hin
  have hfibers := hlim.eventually_normalized_fibers hC hclj hcvj hnej hr
    (by norm_num : (0:ℝ)<1/4) (by norm_num : (1/4:ℝ)≤1) (by norm_num : (1:ℝ)≤4) hin hout
  filter_upwards [hcaps,hballs,hfibers] with j hcj hbj hfj
  apply hprod hΩ hne hcv hu hp hmP hcomplete (a j) (L j) hcj hbj
  · intro s hs
    have hh := (hfj s (fun i => ⟨(hs i).1.le,(hs i).2.le⟩)).1
    simpa only [show (1/4:ℝ)*r/2 = r/8 by ring,modelFiber] using hh
  · intro s hs y hy
    exact mem_closedBall_zero_iff.mp ((hfj s (fun i => ⟨(hs i).1.le,(hs i).2.le⟩)).2.2 hy)

/- A symmetric form with radial null vector has its full adjugate equal to
its transverse principal minor times the radial outer product. This includes
all empty transverse blocks and needs no invertibility of the full matrix. -/

/- The full cofactor trace recovers the transverse determinant in every flat
normal chart. No unit-normal constraint is imposed away from the chart center. -/

end AffineBernstein

end

end OAI
end

theorem solution : type_of% @OAI.AffineBernstein.normalized_model_uniform_actual_sigma_oai := @OAI.AffineBernstein.normalized_model_uniform_actual_sigma_oai
