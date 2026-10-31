-- Prove2me | solution 1 for OAI.AffineBernstein.affineEpigraph_flat_chart_global_area_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:46:58.051297+00:00
-- url     : https://prove2.me/submissions/b2162f66-18b7-43ba-a907-bef1f1469be5

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_flat_graph_injective
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_flat_parametrization
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_flat_tube_positive
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_supportConormal_inward
import Theorems.Thm_OAI_AffineBernstein_graph_chart_weighted_affineArea_lintegral

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

section RadialCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Commuting fixed-direction differentiation with evaluation of a derivative. -/
theorem dirDeriv_eq_second {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (v z : E) :
    dirDeriv v (dirDeriv z f) x = fderiv ℝ (fderiv ℝ f) x v z := by
  have hd := ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have he := hd.clm_apply (hasFDerivAt_const z x)
  change fderiv ℝ (fun y => fderiv ℝ f y z) x v = _
  rw [he.fderiv]
  simp

end RadialCalculus

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
-- module Solutions.OAIQ22_AB.AffineBernstein_JetCalculus
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
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem second_fderiv_comp {f : F → G} {g : E → F} {x : E}
    (hf : ContDiffAt ℝ ∞ f (g x)) (hg : ContDiffAt ℝ ∞ g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (f ∘ g)) x v w =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w) +
        fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x v w) := by
  have hdf := hf.differentiableAt (by simp)
  have hdg := hg.differentiableAt (by simp)
  have hddf := (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hddg := (hg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hdfg := (((hf.comp x hg).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
  have hleft := hdfg.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have hright := (hddf.hasFDerivAt.comp x hdg.hasFDerivAt).clm_apply
    (hddg.hasFDerivAt.clm_apply (hasFDerivAt_const w x))
  have heq : (fun q => fderiv ℝ (f ∘ g) q w) =ᶠ[𝓝 x]
      (fun q => fderiv ℝ f (g q) (fderiv ℝ g q w)) := by
    have hfg : ∀ᶠ q in 𝓝 x, ContDiffAt ℝ 1 f (g q) := hg.continuousAt.eventually
      ((hf.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp))
    filter_upwards [hfg,
      (hg.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)]
      with q hqf hqg
    rw [fderiv_comp q (hqf.differentiableAt (by norm_num)) (hqg.differentiableAt (by norm_num))]
    rfl
  have he := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  have hh := congrArg (fun L : E →L[ℝ] G => L v) he
  simpa [add_comm] using hh

theorem second_fderiv_clm_comp (L : F →L[ℝ] G) {Y : E → F} {x : E}
    (hY : ContDiffAt ℝ ∞ Y x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun q => L (Y q))) x v w =
      L (fderiv ℝ (fderiv ℝ Y) x v w) := by
  have hh := second_fderiv_comp L.contDiff.contDiffAt hY v w
  have hdL : fderiv ℝ (L : F → G) = (fun _ => L) := funext (fun _ => L.fderiv)
  rw [hdL] at hh
  simpa only [fderiv_const_apply, zero_apply, zero_add, Function.comp_def] using hh

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeSecondForm
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

/- Euler and the angular gradient identity give the genuine tangent conormal. -/
omit [CompleteSpace E] in
lemma support_tangent_identity {H : S × E → ℝ} {Y : S × E → E} {x : S × E}
    (hH : DifferentiableAt ℝ H x) (hY : DifferentiableAt ℝ Y x)
    (heul : H =ᶠ[𝓝 x] (fun q => inner ℝ q.2 (Y q)))
    (hgrad : ∀ w : E, fderiv ℝ H x (0,w) = inner ℝ (Y x) w) (v : S × E) :
    inner ℝ x.2 (fderiv ℝ Y x v) = fderiv ℝ H x (v.1,0) := by
  have hd := (hasFDerivAt_snd (p := x)).inner ℝ hY.hasFDerivAt
  have hh := (hd.congr_of_eventuallyEq heul).unique hH.hasFDerivAt
  have he := congrArg (fun A : (S × E) →L[ℝ] ℝ => A v) hh
  have he' : inner ℝ x.2 (fderiv ℝ Y x v) + inner ℝ v.2 (Y x) = fderiv ℝ H x v := by
    simpa using he
  have hs : fderiv ℝ H x v = fderiv ℝ H x (v.1,0) + inner ℝ (Y x) v.2 := by
    rw [← hgrad, ← map_add]
    simp
  rw [hs, real_inner_comm v.2] at he'
  linarith

/- Raw Gauss parametrization, before restricting the angular variable to a chart. -/

omit [CompleteSpace E] in
lemma supportParam_fderiv {Y : S × E → E} {x : S × E}
    (hY : DifferentiableAt ℝ Y x) (v : S × E) :
    fderiv ℝ (supportParam Y) x v = (v.1, fderiv ℝ Y x v) := by
  unfold supportParam
  rw [((hasFDerivAt_fst (p := x)).prodMk hY.hasFDerivAt).fderiv]
  rfl

omit [CompleteSpace E] in
lemma supportParam_second {Y : S × E → E} {x : S × E}
    (hY : ContDiffAt ℝ ∞ Y x) (v w : S × E) :
    fderiv ℝ (fderiv ℝ (supportParam Y)) x v w =
      (0, fderiv ℝ (fderiv ℝ Y) x v w) := by
  have hX : ContDiffAt ℝ ∞ (supportParam Y) x := contDiffAt_fst.prodMk hY
  have hl := ((hX.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.clm_apply
    (hasFDerivAt_const w x)
  have hr := (hasFDerivAt_const w.1 x).prodMk
    (((hY.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.clm_apply
      (hasFDerivAt_const w x))
  have heq : (fun q => fderiv ℝ (supportParam Y) q w) =ᶠ[𝓝 x]
      (fun q => (w.1, fderiv ℝ Y q w)) := by
    filter_upwards [(hY.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)]
      with q hq
    exact supportParam_fderiv (hq.differentiableAt (by norm_num)) w
  have he := (hl.congr_of_eventuallyEq heq.symm).unique hr
  simpa using congrArg (fun A : (S × E) →L[ℝ] (S × E) => A v) he

lemma supportConormal_tangent {H : S × E → ℝ} {Y : S × E → E} {x : S × E}
    (hH : DifferentiableAt ℝ H x) (hY : DifferentiableAt ℝ Y x)
    (heul : H =ᶠ[𝓝 x] (fun q => inner ℝ q.2 (Y q)))
    (hgrad : ∀ w : E, fderiv ℝ H x (0,w) = inner ℝ (Y x) w) (v : S × E) :
    supportConormal H x (fderiv ℝ (supportParam Y) x v) = 0 := by
  rw [supportParam_fderiv hY]
  change fderiv ℝ H x (v.1,0) - inner ℝ x.2 (fderiv ℝ Y x v) = 0
  rw [support_tangent_identity hH hY heul hgrad, sub_self]

/- Differentiating the two literal support identities eliminates both mixed
blocks. No stationarity or curvature formula is assumed. -/
omit [CompleteSpace E] in
lemma support_second_inner {H : S × E → ℝ} {Y : S × E → E} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (hY : ContDiffAt ℝ ∞ Y x)
    (heul : H =ᶠ[𝓝 x] (fun q => inner ℝ q.2 (Y q)))
    (hgrad : ∀ᶠ q in 𝓝 x, ∀ w : E, fderiv ℝ H q (0,w) = inner ℝ (Y q) w)
    (v w : S × E) :
    inner ℝ x.2 (fderiv ℝ (fderiv ℝ Y) x v w) =
      fderiv ℝ (fderiv ℝ H) x (v.1,0) (w.1,0) -
        fderiv ℝ (fderiv ℝ H) x (0,v.2) (0,w.2) := by
  have hddH := (hH.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hddY := (hY.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have htan : (fun q => inner ℝ q.2 (fderiv ℝ Y q w)) =ᶠ[𝓝 x]
      (fun q => fderiv ℝ H q (w.1,0)) := by
    filter_upwards [eventually_eventually_nhds.mpr heul, hgrad,
      (hH.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp),
      (hY.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)]
      with q hqe hqg hqH hqY
    exact support_tangent_identity (hqH.differentiableAt (by norm_num))
      (hqY.differentiableAt (by norm_num)) hqe hqg w
  have hl := (hasFDerivAt_snd (p := x)).inner ℝ
    (hddY.hasFDerivAt.clm_apply (hasFDerivAt_const w x))
  have hr := hddH.hasFDerivAt.clm_apply (hasFDerivAt_const (w.1,0) x)
  have h1 := congrArg (fun A : (S × E) →L[ℝ] ℝ => A v)
    ((hl.congr_of_eventuallyEq htan.symm).unique hr)
  have h1' : inner ℝ x.2 (fderiv ℝ (fderiv ℝ Y) x v w) +
      inner ℝ v.2 (fderiv ℝ Y x w) = fderiv ℝ (fderiv ℝ H) x v (w.1,0) := by
    simpa using h1
  have hg : (fun q => fderiv ℝ H q (0,v.2)) =ᶠ[𝓝 x]
      (fun q => inner ℝ (Y q) v.2) := hgrad.mono (fun q hq => hq v.2)
  have hl2 := hddH.hasFDerivAt.clm_apply (hasFDerivAt_const (0,v.2) x)
  have hr2 := (hY.differentiableAt (by simp)).hasFDerivAt.inner ℝ (hasFDerivAt_const v.2 x)
  have h2 := congrArg (fun A : (S × E) →L[ℝ] ℝ => A w)
    ((hl2.congr_of_eventuallyEq hg.symm).unique hr2)
  have h2' : fderiv ℝ (fderiv ℝ H) x w (0,v.2) = inner ℝ v.2 (fderiv ℝ Y x w) := by
    simpa [real_inner_comm] using h2
  have hsym := hH.isSymmSndFDerivAt (by simp)
  have hsplit1 : fderiv ℝ (fderiv ℝ H) x v (w.1,0) =
      fderiv ℝ (fderiv ℝ H) x (v.1,0) (w.1,0) +
        fderiv ℝ (fderiv ℝ H) x (0,v.2) (w.1,0) := by
    rw [← add_apply, ← map_add]
    simp
  have hsplit2 : fderiv ℝ (fderiv ℝ H) x w (0,v.2) =
      fderiv ℝ (fderiv ℝ H) x (0,v.2) (w.1,0) +
        fderiv ℝ (fderiv ℝ H) x (0,v.2) (0,w.2) := by
    rw [hsym.eq w (0,v.2), ← map_add]
    simp
  rw [hsplit1] at h1'
  rw [hsplit2] at h2'
  linarith

/- Source (tube-second-form), as an identity of actual conormal second jets.
It is valid before angular chart restriction, including the radial null line. -/
lemma supportConormal_second {H : S × E → ℝ} {Y : S × E → E} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (hY : ContDiffAt ℝ ∞ Y x)
    (heul : H =ᶠ[𝓝 x] (fun q => inner ℝ q.2 (Y q)))
    (hgrad : ∀ᶠ q in 𝓝 x, ∀ w : E, fderiv ℝ H q (0,w) = inner ℝ (Y q) w)
    (v w : S × E) :
    supportConormal H x (fderiv ℝ (fderiv ℝ (supportParam Y)) x v w) =
      -fderiv ℝ (fderiv ℝ H) x (v.1,0) (w.1,0) +
        fderiv ℝ (fderiv ℝ H) x (0,v.2) (0,w.2) := by
  rw [supportParam_second hY]
  change fderiv ℝ H x (0,0) - inner ℝ x.2 (fderiv ℝ (fderiv ℝ Y) x v w) = _
  rw [show ((0,0) : S × E) = 0 from rfl, map_zero,
    support_second_inner hH hY heul hgrad]
  ring

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
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeFrame
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
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [CompleteSpace E] in
lemma support_angular_derivative {H : S × E → ℝ} {Y : S × E → E} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (hY : DifferentiableAt ℝ Y x)
    (hgrad : ∀ᶠ q in 𝓝 x, ∀ z : E, fderiv ℝ H q (0,z) = inner ℝ (Y q) z)
    (v : S × E) (w : E) : inner ℝ w (fderiv ℝ Y x v) =
      fderiv ℝ (fderiv ℝ H) x v (0,w) := by
  have hg : (fun q => fderiv ℝ H q (0,w)) =ᶠ[𝓝 x]
      (fun q => inner ℝ (Y q) w) := hgrad.mono (fun q hq => hq w)
  have hdH := (hH.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hl := hdH.hasFDerivAt.clm_apply (hasFDerivAt_const (0,w) x)
  have hr := hY.hasFDerivAt.inner ℝ (hasFDerivAt_const w x)
  have he := congrArg (fun A : (S × E) →L[ℝ] ℝ => A v)
    ((hl.congr_of_eventuallyEq hg.symm).unique hr)
  simpa [real_inner_comm] using he.symm

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma tubeSecondForm_blocks {H : S × E → ℝ} {Y : S × E → E} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (hY : ContDiffAt ℝ ∞ Y x)
    (heul : H =ᶠ[𝓝 x] (fun q => inner ℝ q.2 (Y q)))
    (hgrad : ∀ᶠ q in 𝓝 x, ∀ z : E, fderiv ℝ H q (0,z) = inner ℝ (Y q) z)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    (Matrix.of fun i j : ι ⊕ κ => supportConormal H x
      (fderiv ℝ (fderiv ℝ (supportParam Y)) x (tubeTangent bS bE i) (tubeTangent bS bE j))) =
      Matrix.fromBlocks (tubeBaseMatrix H x bS) 0 0 (tubeRadiusMatrix H x bE) := by
  ext i j
  simp only [Matrix.of_apply, supportConormal_second hH hY heul hgrad]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [tubeTangent, tubeBaseMatrix, tubeRadiusMatrix, Matrix.fromBlocks,
      show ((0,0) : S × E) = 0 from rfl]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeDensityVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Matrix
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

lemma second_fderiv_affine_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : F → G} (L : S →L[ℝ] F) (a : F)
    {x : S} (hf : ContDiffAt ℝ ∞ f (a + L x)) (v w : S) :
    fderiv ℝ (fderiv ℝ (fun z => f (a + L z))) x v w =
      fderiv ℝ (fderiv ℝ f) (a + L x) (L v) (L w) := by
  have hd (z : S) : fderiv ℝ (fun z => a + L z) z = L := by
    exact ((L.hasFDerivAt).const_add a).fderiv
  have hdd : fderiv ℝ (fderiv ℝ (fun z => a + L z)) x = 0 := by
    rw [show fderiv ℝ (fun z => a + L z) = (fun _ => L) from funext hd]
    simp
  change fderiv ℝ (fderiv ℝ (f ∘ (fun z => a + L z))) x v w = _
  rw [second_fderiv_comp (g := fun z => a + L z) hf (contDiffAt_const.add L.contDiff.contDiffAt), hd, hdd]
  simp

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
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatTubeArea
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
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- In a flat normal chart the final normal coordinate is one, and the
transverse column is the fixed negative final basis vector. -/

omit [CompleteSpace E] [Fintype ι] in
lemma flatTubeFrame_matrix {H : S × E → ℝ} {Y : S × E → E} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (hY : ContDiffAt ℝ ∞ Y x)
    (hgrad : ∀ᶠ q in nhds x, ∀ z : E, fderiv ℝ H q (0,z) = inner ℝ (Y q) z)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    (bS.prod bE.toBasis).toMatrix (flatTubeFrame Y x bS bE) =
      Matrix.fromBlocks 1 0
        (Matrix.of fun i j => bE.repr (fderiv ℝ Y x (bS j,0)) i)
        (Matrix.fromBlocks (tubeRadiusMatrix H x bE) 0
          (Matrix.of fun (_ : Unit) j => bE.repr (fderiv ℝ Y x (0,bE (Sum.inl j))) (Sum.inr ()))
          (-1 : Matrix Unit Unit ℝ)) := by
  have hy := hY.differentiableAt (by simp)
  have hs := hH.isSymmSndFDerivAt (by simp)
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [Module.Basis.toMatrix_apply,flatTubeFrame,supportParam_fderiv hy,
      Matrix.fromBlocks,Matrix.one_apply,Finsupp.single_apply,eq_comm]
  · rcases j with j | ⟨⟩ <;>
      simp [Module.Basis.toMatrix_apply,flatTubeFrame,supportParam_fderiv hy,Matrix.fromBlocks]
  · simp [Module.Basis.toMatrix_apply,flatTubeFrame,supportParam_fderiv hy,Matrix.fromBlocks]
  · rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩
    · simpa [Module.Basis.toMatrix_apply,flatTubeFrame,supportParam_fderiv hy,
        Matrix.fromBlocks,OrthonormalBasis.repr_apply_apply,tubeRadiusMatrix] using
        (support_angular_derivative hH hy hgrad (0,bE (Sum.inl j)) (bE (Sum.inl i))).trans
          (hs.eq (0,bE (Sum.inl j)) (0,bE (Sum.inl i)))
    · simp [Module.Basis.toMatrix_apply,flatTubeFrame,Matrix.fromBlocks]
    · simp [Module.Basis.toMatrix_apply,flatTubeFrame,supportParam_fderiv hy,Matrix.fromBlocks]
    · simp [Module.Basis.toMatrix_apply,flatTubeFrame,Matrix.fromBlocks]

omit [CompleteSpace E] in
lemma flatTubeFrame_det {H : S × E → ℝ} {Y : S × E → E} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (hY : ContDiffAt ℝ ∞ Y x)
    (hgrad : ∀ᶠ q in nhds x, ∀ z : E, fderiv ℝ H q (0,z) = inner ℝ (Y q) z)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    (bS.prod bE.toBasis).det (flatTubeFrame Y x bS bE) = -(tubeRadiusMatrix H x bE).det := by
  rw [Module.Basis.det_apply,flatTubeFrame_matrix hH hY hgrad bS bE,
    Matrix.det_fromBlocks_zero₁₂,Matrix.det_fromBlocks_zero₁₂]
  simp

omit [DecidableEq κ] in
lemma flat_supportConormal_transverse {H : S × E → ℝ} {x : S × E}
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (hx : inner ℝ x.2 (bE (Sum.inr ())) = 1) :
    supportConormal H x ((0 : S),-bE (Sum.inr ())) = 1 := by
  simp [supportConormal,hx,show ((0,0) : S × E) = 0 from rfl]

lemma flatTubeAffineAreaJet_eq {H : S × E → ℝ} {Y : S × E → E} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (hY : ContDiffAt ℝ ∞ Y x)
    (heul : H =ᶠ[nhds x] (fun q => inner ℝ q.2 (Y q)))
    (hgrad : ∀ᶠ q in nhds x, ∀ z : E, fderiv ℝ H q (0,z) = inner ℝ (Y q) z)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hB : 0 < (tubeBaseMatrix H x bS).det) (hR : 0 < (tubeRadiusMatrix H x bE).det) :
    flatTubeAffineAreaJet H Y x bS bE = tubeAreaDensity (tubeBaseMatrix H x bS)
      (tubeRadiusMatrix H x bE) (1/((Fintype.card ι : ℝ)+Fintype.card κ+2)) := by
  unfold flatTubeAffineAreaJet tubeAreaDensity
  dsimp only
  simp only [Real.rpow_eq_pow]
  rw [tubeSecondForm_blocks hH hY heul hgrad,Matrix.det_fromBlocks_zero₁₂,
    flatTubeFrame_det hH hY hgrad,abs_neg,abs_of_pos hR,
    Real.mul_rpow hB.le hR.le,mul_assoc,← Real.rpow_add hR]
  congr 2
  have hh : (0 : ℝ) < (Fintype.card ι : ℝ)+Fintype.card κ+2 := by positivity
  field_simp
  ring

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_FlatParametricArea
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
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma parametricAreaDensity_flatSupport {n : ℕ}
    {H : S × E → ℝ} {Y : S × E → E} (q₀ : S × E)
    (J : Space n →L[ℝ] (S × E)) {x : Space n}
    (hY : ContDiffAt ℝ ∞ Y (q₀+J x))
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (e : Fin n ≃ ι ⊕ κ)
    (hJ : ∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i)) :
    let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
    parametricAreaDensity ((bS.prod bE.toBasis).reindex eA.symm)
      (fun y => supportParam Y (q₀+J y)) (supportConormal H (q₀+J x))
      (0,-bE (Sum.inr ())) x = flatTubeAffineAreaJet H Y (q₀+J x) bS bE := by
  let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
  let X := fun y => supportParam Y (q₀+J y)
  let ν := supportConormal H (q₀+J x)
  have hp : ContDiffAt ℝ ∞ (supportParam Y) (q₀+J x) := contDiffAt_fst.prodMk hY
  have hf : parametricFrame X (0,-bE (Sum.inr ())) x =
      flatTubeFrame Y (q₀+J x) bS bE ∘ eA := by
    funext i
    rcases i with i | ⟨⟩
    · have hd := (hp.differentiableAt (by simp)).hasFDerivAt.comp x (J.hasFDerivAt.const_add q₀)
      change fderiv ℝ X x (coordinateVector n i) = _
      have hdf : fderiv ℝ X x = _ := hd.fderiv
      rw [hdf]
      change fderiv ℝ (supportParam Y) (q₀+J x) (J (coordinateVector n i)) = _
      rw [hJ]
      rcases hei : e i with j | j <;> simp [eA,flatTubeFrame,tubeTangent,hei]
    · rfl
  let M : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := Matrix.of fun i j => ν
    (fderiv ℝ (fderiv ℝ (supportParam Y)) (q₀+J x) (tubeTangent bS bE i) (tubeTangent bS bE j))
  have hm : parametricSecondForm X ν x = M.submatrix e e := by
    ext i j
    change dirDeriv (coordinateVector n i) (dirDeriv (coordinateVector n j)
      (fun y => ν (supportParam Y (q₀+J y)))) x =
        ν (fderiv ℝ (fderiv ℝ (supportParam Y)) (q₀+J x)
          (tubeTangent bS bE (e i)) (tubeTangent bS bE (e j)))
    have hνp : ContDiffAt ℝ ∞ (fun q => ν (supportParam Y q)) (q₀+J x) :=
      ν.contDiff.contDiffAt.comp (q₀+J x) hp
    have hq : ContDiffAt ℝ ∞ (fun y => q₀+J y) x :=
      contDiffAt_const.add J.contDiff.contDiffAt
    have hh : ContDiffAt ℝ ∞ (fun y => ν (supportParam Y (q₀+J y))) x :=
      hνp.comp (f := fun y => q₀+J y) x hq
    rw [dirDeriv_eq_second hh]
    rw [second_fderiv_affine_comp J q₀ hνp]
    rw [second_fderiv_clm_comp ν hp]
    simp [hJ]
  have hn : n = Fintype.card ι+Fintype.card κ := by
    simpa using Fintype.card_congr e
  change Real.rpow _ _ * Real.rpow _ _ = _
  rw [hm,Matrix.det_submatrix_equiv_self,hf,Module.Basis.det_reindex_symm]
  simp only [flatTubeAffineAreaJet,hn,Nat.cast_add]
  rfl

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SmoothGraphChart
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

lemma exists_smooth_local_diffeomorph {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V) {f : E → E}
    (hf : ContDiffOn ℝ ∞ f U) {x : E} (hx : x ∈ U) (hfx : f x ∈ V)
    (e : E ≃L[ℝ] E) (he : fderiv ℝ f x = e.toContinuousLinearMap) :
    ∃ φ : OpenPartialHomeomorph E E, x ∈ φ.source ∧ φ.source ⊆ U ∧
      φ.target ⊆ V ∧ (φ : E → E) = f ∧ ContDiffOn ℝ ∞ φ φ.source ∧
      ContDiffOn ℝ ∞ φ.symm φ.target := by
  have hfa := hf.contDiffAt (hU.mem_nhds hx)
  have hd : HasFDerivAt f e.toContinuousLinearMap x := by
    rw [← he]
    exact hfa.differentiableAt (by simp) |>.hasFDerivAt
  let φ₀ := hfa.toOpenPartialHomeomorph f hd (by simp)
  have hx₀ : x ∈ φ₀.source := hfa.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hn : ∀ᶠ y in nhds x, ∃ e' : E ≃L[ℝ] E, e'.toContinuousLinearMap = fderiv ℝ f y := by
    have hc : ContinuousAt (fderiv ℝ f) x := hfa.continuousAt_fderiv (by simp)
    exact hc.preimage_mem_nhds (by rw [he]; exact e.nhds)
  obtain ⟨N,hN,hNo,hxN⟩ := mem_nhds_iff.mp
    (inter_mem (hU.mem_nhds hx) (inter_mem (hfa.continuousAt.preimage_mem_nhds (hV.mem_nhds hfx)) hn))
  let φ := φ₀.restrOpen N hNo
  have hφf : (φ : E → E) = f := rfl
  have hs : φ.source ⊆ U := fun y hy => (hN hy.2).1
  refine ⟨φ,⟨hx₀,hxN⟩,hs,?_,hφf,?_,?_⟩
  · intro y hy
    have hys := φ.map_target hy
    have hh := (hN hys.2).2.1
    change f (φ.symm y) ∈ V at hh
    simpa only [← hφf,φ.right_inv hy] using hh
  · simpa only [hφf] using hf.mono hs
  · intro y hy
    have hys := φ.map_target hy
    obtain ⟨e',he'⟩ := (hN hys.2).2.2
    have hg : ContDiffAt ℝ ∞ f (φ.symm y) := hf.contDiffAt (hU.mem_nhds (hs hys))
    apply (φ.contDiffAt_symm hy (f₀' := e') ?_ ?_).contDiffWithinAt
    · rw [hφf,he']
      exact hg.differentiableAt (by simp) |>.hasFDerivAt
    · simpa only [hφf] using hg

/- The graph projection of a smooth immersed parametrization of a graph
has nonsingular derivative. This is the differential input to the local
chart used in the support-coordinate stationarity calculation. -/
lemma graph_projection_derivative_bijective {n : ℕ} {U Ω : Set (Space n)}
    (hU : IsOpen U) (hΩ : IsOpen Ω) {X : Space n → Space n × ℝ}
    {u : Space n → ℝ} (hX : ContDiffOn ℝ ∞ X U) (hu : ContDiffOn ℝ ∞ u Ω)
    (him : ∀ y ∈ U, (X y).1 ∈ Ω ∧ (X y).2 = u (X y).1)
    {x : Space n} (hx : x ∈ U) (hi : Function.Injective (fderiv ℝ X x)) :
    Function.Bijective (fderiv ℝ (fun y => (X y).1) x) := by
  have hXa := hX.contDiffAt (hU.mem_nhds hx)
  have hd := hXa.differentiableAt (by simp)
  have he : X =ᶠ[nhds x] (fun y => ((X y).1,u (X y).1)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact Prod.ext rfl (him y hy).2
  have hu' := (hu.contDiffAt (hΩ.mem_nhds (him x hx).1)).differentiableAt (by simp)
  have heD := he.fderiv_eq (𝕜 := ℝ)
  have hg : fderiv ℝ X x =
      (fderiv ℝ (fun y => (X y).1) x).prod
        ((fderiv ℝ u (X x).1).comp (fderiv ℝ (fun y => (X y).1) x)) := by
    rw [heD]
    exact ((hd.fst.hasFDerivAt).prodMk (hu'.hasFDerivAt.comp x hd.fst.hasFDerivAt)).fderiv
  have hinj : Function.Injective (fderiv ℝ (fun y => (X y).1) x) := by
    intro v w hvw
    apply hi
    rw [hg]
    simp only [ContinuousLinearMap.prod_apply,ContinuousLinearMap.comp_apply,hvw]
  exact ⟨hinj,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj⟩

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GlobalGraphChart
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

/- A one-to-one smooth local diffeomorphism on an open set gives a single
global smooth partial chart. -/
lemma exists_smooth_global_diffeomorph {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {f : E → E} (hf : ContDiffOn ℝ ∞ f U) (him : MapsTo f U V)
    (hi : Set.InjOn f U) (hd : ∀ x ∈ U, Function.Bijective (fderiv ℝ f x)) :
    ∃ φ : OpenPartialHomeomorph E E, φ.source = U ∧ φ.target = f '' U ∧
      φ.target ⊆ V ∧ (φ : E → E) = f ∧ ContDiffOn ℝ ∞ φ φ.source ∧
      ContDiffOn ℝ ∞ φ.symm φ.target := by
  have hlocal (x : E) (hx : x ∈ U) :
      ∃ ψ : OpenPartialHomeomorph E E, x ∈ ψ.source ∧ ψ.source ⊆ U ∧
        ψ.target ⊆ V ∧ (ψ : E → E) = f ∧ ContDiffOn ℝ ∞ ψ ψ.source ∧
        ContDiffOn ℝ ∞ ψ.symm ψ.target := by
    let e := (LinearEquiv.ofBijective (fderiv ℝ f x).toLinearMap (hd x hx)).toContinuousLinearEquiv
    exact exists_smooth_local_diffeomorph hU hV hf hx (him hx) e rfl
  have ho : IsOpenMap (U.domRestrict f) := by
    intro W hW
    have hW' : IsOpen (Subtype.val '' W : Set E) := hU.isOpenMap_subtype_val _ hW
    apply isOpen_iff_mem_nhds.mpr
    rintro z ⟨x,hx,rfl⟩
    obtain ⟨ψ,hxψ,hs,ht,he,hψ,hψi⟩ := hlocal x x.property
    have hN : IsOpen (ψ '' ((Subtype.val '' W : Set E) ∩ ψ.source)) :=
      ψ.isOpen_image_of_subset_source (hW'.inter ψ.open_source) inter_subset_right
    have hxN : f x ∈ ψ '' ((Subtype.val '' W : Set E) ∩ ψ.source) :=
      ⟨x,⟨⟨x,hx,rfl⟩,hxψ⟩,by rw [he]⟩
    apply mem_of_superset (hN.mem_nhds hxN)
    rintro z ⟨y,⟨⟨x',hx',rfl⟩,hy⟩,rfl⟩
    exact ⟨x',hx',by rw [he]; rfl⟩
  let pe := hi.toPartialEquiv f U
  let φ := OpenPartialHomeomorph.ofContinuousOpenRestrict pe hf.continuousOn ho hU
  have hs : φ.source = U := rfl
  have ht : φ.target = f '' U := rfl
  have he : (φ : E → E) = f := rfl
  refine ⟨φ,hs,ht,?_,he,?_,?_⟩
  · rintro y ⟨x,hx,rfl⟩
    exact him hx
  · exact hf
  · intro y hy
    have hx : φ.symm y ∈ U := φ.map_target hy
    have hfa : ContDiffAt ℝ ∞ f (φ.symm y) := hf.contDiffAt (hU.mem_nhds hx)
    let e := (LinearEquiv.ofBijective (fderiv ℝ f (φ.symm y)).toLinearMap
      (hd _ hx)).toContinuousLinearEquiv
    apply (φ.contDiffAt_symm hy (f₀' := e) ?_ ?_).contDiffWithinAt
    · exact hfa.differentiableAt (by simp) |>.hasFDerivAt
    · exact hfa

/- A globally injective immersion into an actual graph admits a global
smooth graph chart on its entire open parameter domain. -/
theorem exists_smooth_global_graph_chart {n : ℕ} {U Ω : Set (Space n)}
    (hU : IsOpen U) (hΩ : IsOpen Ω) {X : Space n → Space n × ℝ}
    {u : Space n → ℝ} (hX : ContDiffOn ℝ ∞ X U) (hu : ContDiffOn ℝ ∞ u Ω)
    (him : ∀ y ∈ U, (X y).1 ∈ Ω ∧ (X y).2 = u (X y).1)
    (hi : Set.InjOn (fun x => (X x).1) U)
    (hd : ∀ x ∈ U, Function.Injective (fderiv ℝ X x)) :
    ∃ φ : OpenPartialHomeomorph (Space n) (Space n), φ.source = U ∧
      φ.target ⊆ Ω ∧ (∀ y ∈ U, X y = (φ y,u (φ y))) ∧
      ContDiffOn ℝ ∞ φ φ.source ∧ ContDiffOn ℝ ∞ φ.symm φ.target := by
  obtain ⟨φ,hs,ht,hΩφ,he,hφ,hψ⟩ := exists_smooth_global_diffeomorph hU hΩ hX.fst
    (fun x hx => (him x hx).1) hi
    (fun x hx => graph_projection_derivative_bijective hU hΩ hX hu him hx (hd x hx))
  refine ⟨φ,hs,hΩφ,?_,hφ,hψ⟩
  intro y hy
  rw [he]
  exact Prod.ext rfl (him y hy).2

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_GlobalFlatAreaLIntegral
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

/- Global exact inverse-second-form area transport on the entire literal flat support chart.
All metric and parametrization data are derived from the original strictly
convex graph. Neither stationarity nor a measure-transport law is assumed. -/
theorem affineEpigraph_flat_chart_global_area_lintegral_oai {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (q₀ : S × E) (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hd : inner ℝ q₀.2 (bE (Sum.inr ())) = 1)
    (J : Space n →L[ℝ] (S × E)) (hi : Function.Injective J)
    (hJ : ∀ v, inner ℝ (J v).2 (bE (Sum.inr ())) = 0)
    (e : Fin n ≃ ι ⊕ κ) (hJe : ∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i))
    :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let X := fun x : Space n => supportParam Y (q₀+J x)
    let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
    let b := (bS.prod bE.toBasis).reindex eA.symm
    ∃ φ : OpenPartialHomeomorph (Space n) (Space n),
      φ.source = {x | (q₀+J x).1 ∈ B} ∧ φ.target ⊆ Ω ∧
      ContDiffOn ℝ ∞ φ φ.source ∧ ContDiffOn ℝ ∞ φ.symm φ.target ∧
      (∀ x ∈ φ.source, a+L (X x) = (φ x,u (φ x))) ∧
      ∀ (K : Set (Space n)), MeasurableSet K → K ⊆ φ.source →
      ∀ (w : Space n → ℝ≥0∞),
      (∫⁻ x in K, ENNReal.ofReal (tubeAreaDensity (tubeBaseMatrix H (q₀+J x) bS)
        (tubeRadiusMatrix H (q₀+J x) bE) (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))) * w (φ x)) =
        ENNReal.ofReal (Real.rpow |b.det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
          ((n : ℝ)/((n : ℝ)+2))) * ∫⁻ y in φ '' K, ENNReal.ofReal (affineAreaDensity u y) * w y := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let X := fun x : Space n => supportParam Y (q₀+J x)
  let U := {x : Space n | (q₀+J x).1 ∈ B}
  let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
  let b := (bS.prod bE.toBasis).reindex eA.symm
  obtain ⟨hU,hLX,him,hiLX⟩ := affineEpigraph_flat_parametrization hΩ hcv hu hp a L hB hK hzero
    q₀ (bE (Sum.inr ())) hd J hi hJ
  have he : (fun x => L.symm ((a+L (X x))-a)) = X := by funext x; simp
  have hX : ContDiffOn ℝ ∞ X U := by
    rw [← he]
    exact L.symm.contDiff.comp_contDiffOn (hLX.sub contDiffOn_const)
  obtain ⟨φ,hsource,ht,heφ₀,hφ,hψ⟩ := exists_smooth_global_graph_chart hU hΩ hLX hu him
    (affineEpigraph_flat_graph_injective hΩ hcv hu hp a L hB hK hzero q₀ (bE (Sum.inr ())) hd J hi hJ) hiLX
  have hs : φ.source ⊆ U := fun x hx => by rwa [hsource] at hx
  have heφ : ∀ x ∈ φ.source, a+L (X x) = (φ x,u (φ x)) :=
    fun x hx => heφ₀ x (hs hx)
  change ∃ φ, _
  refine ⟨φ,hsource,ht,hφ,hψ,heφ,?_⟩
  intro K hKc hKW w
  have hq (x : Space n) : inner ℝ (q₀+J x).2 (bE (Sum.inr ())) = 1 := by
    simp [inner_add_left,hd,hJ]
  have hne (x : Space n) : (q₀+J x).2 ≠ 0 := by intro hz; simpa [hz] using hq x
  have hj (x : Space n) (hx : x ∈ U) :=
    affineEpigraph_support_jets hΩ hcv hu hp a L hB hK hzero hx (hne x)
  have hνx (x : Space n) (hx : x ∈ K) :
      (supportConormal H (q₀+J x)).comp (fderiv ℝ X x) = 0 := by
    obtain ⟨hHs,hYs,heul,hgrad⟩ := hj x (hs (hKW hx))
    have hsp : ContDiffAt ℝ ∞ (supportParam Y) (q₀+J x) := contDiffAt_fst.prodMk hYs
    have hcomp := (hsp.differentiableAt (by simp)).hasFDerivAt.comp x
      (J.hasFDerivAt.const_add q₀)
    have hdX : fderiv ℝ X x = (fderiv ℝ (supportParam Y) (q₀+J x)).comp J := hcomp.fderiv
    rw [hdX]
    ext w
    exact supportConormal_tangent (hHs.differentiableAt (by simp))
      (hYs.differentiableAt (by simp)) heul hgrad.self_of_nhds (J w)
  have hh := graph_chart_weighted_affineArea_lintegral hU hΩ hX hu hp a L φ hs ht hφ hψ heφ
    b hKc hKW (fun x => supportConormal H (q₀+J x))
    (fun _ => (0,-bE (Sum.inr ()))) hνx
    (fun x _ => flat_supportConormal_transverse bE (hq x))
    (fun x hx => affineEpigraph_supportConormal_inward hΩ hcv hu hp a L hB hK hzero
      (hs (hKW hx)) (hne x)) w
  rw [← hh]
  apply setLIntegral_congr_fun hKc
  intro x hx
  apply congrArg (fun r : ℝ => ENNReal.ofReal r * w (φ x))
  obtain ⟨hHs,hYs,heul,hgrad⟩ := hj x (hs (hKW hx))
  change tubeAreaDensity (tubeBaseMatrix H (q₀+J x) bS)
    (tubeRadiusMatrix H (q₀+J x) bE) _ =
    parametricAreaDensity ((bS.prod bE.toBasis).reindex eA.symm)
      (fun y => supportParam Y (q₀+J y)) (supportConormal H (q₀+J x))
      (0,-bE (Sum.inr ())) x
  rw [parametricAreaDensity_flatSupport q₀ J hYs bS bE e hJe]
  obtain ⟨hBp,hRp⟩ := affineEpigraph_flat_tube_positive hΩ hcv hu hp a L hB hK hzero
    (e := (q₀+J x).2) (hs (hKW hx)) bS bE (by rw [hq x]; norm_num)
  exact (flatTubeAffineAreaJet_eq hHs hYs heul hgrad bS bE hBp.det_pos hRp.det_pos).symm

end AffineBernstein
end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.AffineBernstein.affineEpigraph_flat_chart_global_area_lintegral_oai.{u_1, u_2, u_3, u_4} := @OAI.AffineBernstein.affineEpigraph_flat_chart_global_area_lintegral_oai.{u_1, u_2, u_3, u_4}
