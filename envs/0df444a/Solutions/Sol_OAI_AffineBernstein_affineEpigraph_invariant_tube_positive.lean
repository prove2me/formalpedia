-- Prove2me | solution 1 for OAI.AffineBernstein.affineEpigraph_invariant_tube_positive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:52:04.177407+00:00
-- url     : https://prove2.me/submissions/2c6069a8-7107-475c-943e-7cc5b38d3c3f

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_flat_tube_positive

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

theorem homogeneousSupport_euler {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {e : E} (hd : DifferentiableAt ℝ (homogeneousSupport K) e) :
    fderiv ℝ (homogeneousSupport K) e e = homogeneousSupport K e := by
  have hh := (gaussPoint_mem_support hK hne hd).2
  rw [real_inner_comm] at hh
  simpa [gaussPoint, gradient] using hh.symm

/- Euler's identity differentiates to the radial null direction of the support
Hessian. This is the ambient version of the spherical radius matrix. -/
theorem homogeneousSupport_hessian_radial {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) {e : E} (hh : ContDiffAt ℝ ∞ (homogeneousSupport K) e)
    (v : E) : fderiv ℝ (fderiv ℝ (homogeneousSupport K)) e v e = 0 := by
  have hd := hh.differentiableAt (by simp)
  have hdd := (hh.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have he : (fun q => fderiv ℝ (homogeneousSupport K) q q) =ᶠ[𝓝 e]
      homogeneousSupport K := by
    filter_upwards [(hh.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)]
      with q hq
    exact homogeneousSupport_euler hK hne (hq.differentiableAt (by norm_num))
  have hr := hdd.hasFDerivAt.clm_apply (hasFDerivAt_id e)
  have heq := (hr.congr_of_eventuallyEq he.symm).unique hd.hasFDerivAt
  have hev := congrArg (fun f : E →L[ℝ] ℝ => f v) heq
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply, id_eq] at hev
  linarith

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

lemma second_fderiv_prod_right {H : S × E → ℝ} {s : S} {e : E}
    (hH : ContDiffAt ℝ ∞ H (s,e)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => H (s,y))) e v w =
      fderiv ℝ (fderiv ℝ H) (s,e) (0,v) (0,w) := by
  simpa using second_fderiv_affine_comp (ContinuousLinearMap.inr ℝ S E) (s,0) (by simpa using hH) v w

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
-- module Solutions.OAIQ22_AB.AffineBernstein_BlockNewton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section BlockNewton
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma adjugate_fromBlocks_scalar (A : Matrix ι ι ℝ) (t : ℝ) (i j : ι) :
    (Matrix.fromBlocks A 0 0 (t • (1 : Matrix Unit Unit ℝ))).adjugate
      (Sum.inl i) (Sum.inl j) = t * A.adjugate i j := by
  rw [Matrix.adjugate_apply, Matrix.adjugate_apply]
  have hh : (Matrix.fromBlocks A 0 0 (t • (1 : Matrix Unit Unit ℝ))).updateRow
      (Sum.inl j) (Pi.single (Sum.inl i) 1) =
      Matrix.fromBlocks (A.updateRow j (Pi.single i 1)) 0 0 (t • (1 : Matrix Unit Unit ℝ)) := by
    ext l m
    cases l with
    | inl l =>
      cases m with
      | inl m => simp [Matrix.updateRow_apply, Pi.single_apply, Matrix.fromBlocks]
      | inr m => simp [Matrix.updateRow_apply, Matrix.fromBlocks]
    | inr l =>
      cases m <;> simp [Matrix.updateRow_apply, Matrix.fromBlocks]
  rw [hh, Matrix.det_fromBlocks_zero₂₁]
  simp [mul_comm]

end BlockNewton
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma adjugate_eq_det_smul_transpose {Q : Matrix ι ι ℝ} (hQ : Q * Qᵀ = 1) :
    Q.adjugate = Q.det • Qᵀ := by
  calc
    Q.adjugate = Q.adjugate * (Q * Qᵀ) := by rw [hQ, Matrix.mul_one]
    _ = (Q.adjugate * Q) * Qᵀ := (Matrix.mul_assoc _ _ _).symm
    _ = Q.det • Qᵀ := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]

lemma adjugate_conjugate_orthogonal {Q : Matrix ι ι ℝ}
    (hQ : Q * Qᵀ = 1) (hQt : Qᵀ * Q = 1) (A : Matrix ι ι ℝ) :
    (Qᵀ * A * Q).adjugate = Qᵀ * A.adjugate * Q := by
  have hd : Q.det * Q.det = 1 := by
    have hh := congrArg Matrix.det hQ
    simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] using hh
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
    adjugate_eq_det_smul_transpose hQ,
    adjugate_eq_det_smul_transpose (Q := Qᵀ) (by simpa using hQt),
    Matrix.transpose_transpose, Matrix.det_transpose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hd, one_smul, Matrix.mul_assoc]

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_RadialAdjugate
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma adjugate_block_radial (R : Matrix ι ι ℝ) :
    (Matrix.fromBlocks R 0 0 (0 : Matrix Unit Unit ℝ)).adjugate =
      Matrix.fromBlocks 0 0 0 (R.det • (1 : Matrix Unit Unit ℝ)) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have hh := adjugate_fromBlocks_scalar R 0 i j
      simpa using hh
    | inr j =>
      cases j
      rw [Matrix.adjugate_apply]
      apply Matrix.det_eq_zero_of_column_eq_zero (Sum.inr ())
      intro l
      cases l <;> simp [Matrix.updateRow_apply,Matrix.fromBlocks]
  | inr i =>
    cases i
    cases j with
    | inl j =>
      rw [Matrix.adjugate_apply]
      apply Matrix.det_eq_zero_of_row_eq_zero (Sum.inr ())
      intro l
      cases l <;> simp [Matrix.updateRow_apply,Matrix.fromBlocks]
    | inr j =>
      cases j
      rw [Matrix.adjugate_apply]
      have hh : (Matrix.fromBlocks R 0 0 (0 : Matrix Unit Unit ℝ)).updateRow
          (Sum.inr ()) (Pi.single (Sum.inr ()) 1) = Matrix.fromBlocks R 0 0 (1 : Matrix Unit Unit ℝ) := by
        ext l m
        cases l <;> cases m <;> simp [Matrix.updateRow_apply,Matrix.fromBlocks]
      rw [hh,Matrix.det_fromBlocks_zero₂₁]
      simp

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NewtonBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section NewtonBasis
open scoped Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CompleteSpace E] in
lemma orthogonalChange_transpose_mul (b c : OrthonormalBasis ι ℝ E) :
    (orthogonalChange b c)ᵀ * orthogonalChange b c = 1 := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,orthogonalChange,Matrix.of_apply,Matrix.one_apply]
  calc
    ∑ k, inner ℝ (b k) (c i) * inner ℝ (b k) (c j) = inner ℝ (c i) (c j) := by
      convert b.sum_inner_mul_inner (c i) (c j) using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro k _
      rw [real_inner_comm (b k) (c i)]
    _ = _ := orthonormal_iff_ite.mp c.orthonormal i j

omit [CompleteSpace E] in
lemma orthogonalChange_mul_transpose (b c : OrthonormalBasis ι ℝ E) :
    orthogonalChange b c * (orthogonalChange b c)ᵀ = 1 := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,orthogonalChange,Matrix.of_apply,Matrix.one_apply]
  calc
    ∑ k, inner ℝ (b i) (c k) * inner ℝ (b j) (c k) = inner ℝ (b i) (b j) := by
      convert c.sum_inner_mul_inner (b i) (b j) using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro k _
      rw [real_inner_comm (b j) (c k)]
    _ = _ := orthonormal_iff_ite.mp b.orthonormal i j

end NewtonBasis
open scoped Matrix
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [CompleteSpace E] [DecidableEq ι] in
lemma tubeFullRadiusMatrix_change (H : S × E → ℝ) (q : S × E)
    (b c : OrthonormalBasis ι ℝ E) :
    tubeFullRadiusMatrix H q c =
      (orthogonalChange b c)ᵀ * tubeFullRadiusMatrix H q b * orthogonalChange b c := by
  have hre (v : E) : ((0:S),v) = ∑ i, b.repr v i • (0,b i) := by
    apply Prod.ext
    · simp [Prod.fst_sum]
    · simpa [Prod.snd_sum,OrthonormalBasis.repr_apply_apply] using (b.sum_repr' v).symm
  ext i j
  simp only [tubeFullRadiusMatrix,Matrix.of_apply,Matrix.mul_apply,Matrix.transpose_apply,
    orthogonalChange,Finset.sum_mul]
  conv_lhs => rw [hre (c i),hre (c j)]
  simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,Finset.mul_sum,
    OrthonormalBasis.repr_apply_apply]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [CompleteSpace E] in
lemma tubeAngularDensity_basis_independent (H : S × E → ℝ) (q : S × E)
    (b c : OrthonormalBasis ι ℝ E) : tubeAngularDensity H q c = tubeAngularDensity H q b := by
  rw [tubeAngularDensity,tubeFullRadiusMatrix_change H q b c,
    adjugate_conjugate_orthogonal (orthogonalChange_mul_transpose b c)
      (orthogonalChange_transpose_mul b c),Matrix.trace_mul_cycle,
      orthogonalChange_mul_transpose,Matrix.one_mul]
  rfl

omit [CompleteSpace E] [DecidableEq ι] in
lemma tubeFullRadiusMatrix_symm {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    (tubeFullRadiusMatrix H q b).IsSymm := by
  have hh := hH.isSymmSndFDerivAt (by simp)
  ext i j
  exact hh.eq _ _

omit [CompleteSpace E] in
lemma tubeAngularDensity_of_last_null {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hr : ∀ v : E, fderiv ℝ (fderiv ℝ H) q (0,v) (0,b (Sum.inr ())) = 0) :
    tubeAngularDensity H q b = (tubeRadiusMatrix H q b).det := by
  have hs := tubeFullRadiusMatrix_symm hH b
  have hb : tubeFullRadiusMatrix H q b =
      Matrix.fromBlocks (tubeRadiusMatrix H q b) 0 0 (0 : Matrix Unit Unit ℝ) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => rfl
      | inr j => cases j; exact hr _
    | inr i =>
      cases i
      cases j with
      | inl j => rw [← hs.apply]; exact hr _
      | inr j => cases j; exact hr _
  rw [tubeAngularDensity,hb,adjugate_block_radial]
  simp [Matrix.trace,Fintype.sum_sum_type,Matrix.fromBlocks]

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

omit [CompleteSpace E] in
lemma exists_orthonormalBasis_last [FiniteDimensional ℝ E]
    (b : OrthonormalBasis (κ ⊕ Unit) ℝ E) {e : E} (he : ‖e‖ = 1) :
    ∃ c : OrthonormalBasis (κ ⊕ Unit) ℝ E, c (Sum.inr ()) = e := by
  let v : κ ⊕ Unit → E := fun _ => e
  let A : Set (κ ⊕ Unit) := {Sum.inr ()}
  have hv : Orthonormal ℝ (A.domRestrict v) := by
    apply orthonormal_iff_ite.mpr
    intro i j
    have hij : i = j := by
      apply Subtype.ext
      exact (Set.mem_singleton_iff.mp i.property).trans (Set.mem_singleton_iff.mp j.property).symm
    simp [hij,A,v,Set.domRestrict,he]
  obtain ⟨c,hc⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (Module.finrank_eq_card_basis b.toBasis) hv
  exact ⟨c,hc _ (by simp [A])⟩

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualInvariantTube
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

lemma affineEpigraph_support_radial {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) {e : E} (he : e ≠ 0) (v : E) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    fderiv ℝ (fderiv ℝ H) (s,e) (0,v) (0,e) = 0 := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  have hh := (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs he).1
  change ContDiffAt ℝ ∞ H (s,e) at hh
  change fderiv ℝ (fderiv ℝ H) (s,e) (0,v) (0,e) = 0
  rw [← second_fderiv_prod_right hh]
  exact homogeneousSupport_hessian_radial (hK s hs) ⟨0,interior_subset (hzero s hs)⟩
    (hh.comp e (contDiffAt_const.prodMk contDiffAt_id)) v

/- The invariant angular determinant is strictly positive on every actual
nonzero fiber conormal, independently of the fixed orthonormal frame. -/
omit [DecidableEq ι] in
theorem affineEpigraph_invariant_tube_positive_oai {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) {e : E} (he : e ≠ 0)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    (tubeBaseMatrix H (s,e) bS).PosDef ∧ 0 < tubeAngularDensity H (s,e) bE ∧ 0 < H (s,e) := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  have hn : 0 < ‖e‖ := norm_pos_iff.mpr he
  have hunit : ‖‖e‖⁻¹ • e‖ = 1 := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  obtain ⟨c,hc⟩ := exists_orthonormalBasis_last bE hunit
  have hinner : inner ℝ e (c (Sum.inr ())) ≠ 0 := by
    rw [hc,real_inner_smul_right]
    exact mul_ne_zero (inv_ne_zero hn.ne') (real_inner_self_pos.mpr he).ne'
  have hpos := affineEpigraph_flat_tube_positive hΩ hcv hu hp a L hD hK hzero hs bS c hinner
  have hh := (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs he).1
  change ContDiffAt ℝ ∞ H (s,e) at hh
  refine ⟨hpos.1,?_,?_⟩
  · rw [← tubeAngularDensity_basis_independent H (s,e) bE c]
    rw [tubeAngularDensity_of_last_null hh c]
    · exact hpos.2.det_pos
    · intro v
      have hr := affineEpigraph_support_radial hΩ hcv hu hp a L hD hK hzero hs he v
      change fderiv ℝ (fderiv ℝ H) (s,e) (0,v) (0,e) = 0 at hr
      rw [hc]
      have heq : ((0:S),‖e‖⁻¹ • e) = ‖e‖⁻¹ • ((0:S),e) := by simp
      rw [heq,map_smul,hr,smul_zero]
  · apply supportValue_pos (hK s hs) (hzero s hs)
    intro hz
    apply he
    exact (InnerProductSpace.toDual ℝ E).injective (hz.trans (map_zero _).symm)

end AffineBernstein
end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.AffineBernstein.affineEpigraph_invariant_tube_positive_oai.{u_1, u_2, u_3, u_4} := @OAI.AffineBernstein.affineEpigraph_invariant_tube_positive_oai.{u_1, u_2, u_3, u_4}
