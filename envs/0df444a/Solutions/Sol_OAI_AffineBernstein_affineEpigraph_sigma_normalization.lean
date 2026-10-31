-- Prove2me | solution 1 for OAI.AffineBernstein.affineEpigraph_sigma_normalization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:55:09.649887+00:00
-- url     : https://prove2.me/submissions/f6d415fd-ae32-4953-9ab4-b0b4f952ae82

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_invariant_tube_positive

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

lemma radialShear_det (e : ι ⊕ Unit → ℝ) : (radialShear e).det = 1 := by
  rw [radialShear,Matrix.det_fromBlocks_zero₂₁]
  simp

omit [Fintype ι] in
lemma radialShear_last (e : ι ⊕ Unit → ℝ) (he : e (Sum.inr ()) = 1) (i : ι ⊕ Unit) :
    radialShear e i (Sum.inr ()) = e i := by
  cases i <;> simp [radialShear,Matrix.fromBlocks,he]

lemma mul_radialShear_left (A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ)
    (e : ι ⊕ Unit → ℝ) (i : ι ⊕ Unit) (j : ι) :
    (A * radialShear e) i (Sum.inl j) = A i (Sum.inl j) := by
  simp [Matrix.mul_apply,Fintype.sum_sum_type,radialShear,Matrix.fromBlocks,Matrix.one_apply]

lemma transpose_radialShear_mul_left (A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ)
    (e : ι ⊕ Unit → ℝ) (i : ι) (j : ι ⊕ Unit) :
    ((radialShear e)ᵀ * A) (Sum.inl i) j = A (Sum.inl i) j := by
  simp [Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_sum_type,radialShear,
    Matrix.fromBlocks,Matrix.one_apply]

lemma mul_radialShear_last (A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ)
    (e : ι ⊕ Unit → ℝ) (he : e (Sum.inr ()) = 1) (i : ι ⊕ Unit) :
    (A * radialShear e) i (Sum.inr ()) = (A *ᵥ e) i := by
  simp only [Matrix.mul_apply,radialShear_last e he,Matrix.mulVec, dotProduct]

lemma radialShear_conjugate {A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ}
    (hA : A.IsSymm) (e : ι ⊕ Unit → ℝ) (he : e (Sum.inr ()) = 1)
    (hz : A *ᵥ e = 0) :
    (radialShear e)ᵀ * A * radialShear e =
      Matrix.fromBlocks (A.submatrix Sum.inl Sum.inl) 0 0 (0 : Matrix Unit Unit ℝ) := by
  have hs : ((radialShear e)ᵀ * A * radialShear e).IsSymm := by
    simp only [Matrix.IsSymm,Matrix.transpose_mul,Matrix.transpose_transpose,hA.eq,Matrix.mul_assoc]
  have hlast (i : ι ⊕ Unit) : ((radialShear e)ᵀ * A * radialShear e) i (Sum.inr ()) = 0 := by
    rw [Matrix.mul_assoc,Matrix.mul_apply]
    simp [mul_radialShear_last A e he,hz]
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      rw [Matrix.mul_assoc,transpose_radialShear_mul_left,mul_radialShear_left]
      rfl
    | inr j => cases j; exact hlast _
  | inr i =>
    cases i
    cases j with
    | inl j => rw [← hs.apply]; exact hlast _
    | inr j => cases j; exact hlast _

/- A symmetric form with radial null vector has its full adjugate equal to
its transverse principal minor times the radial outer product. This includes
all empty transverse blocks and needs no invertibility of the full matrix. -/
theorem radial_adjugate {A : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ}
    (hA : A.IsSymm) (e : ι ⊕ Unit → ℝ) (he : e (Sum.inr ()) = 1)
    (hz : A *ᵥ e = 0) (i j : ι ⊕ Unit) :
    A.adjugate i j = (A.submatrix Sum.inl Sum.inl).det * e i * e j := by
  let P := radialShear e
  let d := (A.submatrix Sum.inl Sum.inl).det
  have hP : P.det = 1 := radialShear_det e
  have hp : P * P.adjugate = 1 := by rw [Matrix.mul_adjugate,hP,one_smul]
  have hpt : (Pᵀ).adjugate * Pᵀ = 1 := by
    rw [Matrix.adjugate_mul,Matrix.det_transpose,hP,one_smul]
  have hh := congrArg Matrix.adjugate (radialShear_conjugate hA e he hz)
  rw [adjugate_block_radial,Matrix.adjugate_mul_distrib,Matrix.adjugate_mul_distrib] at hh
  have hmul := congrArg (fun M : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ => P*M*Pᵀ) hh
  change P * (P.adjugate * (A.adjugate * (Pᵀ).adjugate)) * Pᵀ =
    P*Matrix.fromBlocks 0 0 0 (d • (1 : Matrix Unit Unit ℝ))*Pᵀ at hmul
  have heq : A.adjugate = P*Matrix.fromBlocks 0 0 0 (d • (1 : Matrix Unit Unit ℝ))*Pᵀ := by
    calc
      _ = (P*P.adjugate)*A.adjugate*((Pᵀ).adjugate*Pᵀ) := by rw [hp,hpt,Matrix.one_mul,Matrix.mul_one]
      _ = _ := by simpa only [Matrix.mul_assoc] using hmul
  rw [heq]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_sum_type]
  simp only [Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,mul_zero,zero_mul,Finset.sum_const_zero,zero_add,
    Fintype.sum_unique,Matrix.smul_apply,Matrix.one_apply,ite_true,smul_eq_mul,mul_one]
  change (P i (Sum.inr ()) * d)*P j (Sum.inr ()) = _
  dsimp only [P,d]
  rw [radialShear_last e he,radialShear_last e he]
  ring

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SupportHomogeneity
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma homogeneousSupport_smul {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (e : E) {c : ℝ} (hc : 0 < c) :
    homogeneousSupport K (c • e) = c * homogeneousSupport K e := by
  obtain ⟨z,hz,hm⟩ := hK.exists_isMaxOn hne
    (InnerProductSpace.toDual ℝ E e).continuous.continuousOn
  rw [homogeneousSupport_eq_of_max hz hm]
  have hmc : IsMaxOn (fun y => inner ℝ (c • e) y) K z := by
    intro y hy
    change inner ℝ (c • e) y ≤ inner ℝ (c • e) z
    simp only [real_inner_smul_left]
    exact mul_le_mul_of_nonneg_left (hm hy) hc.le
  rw [homogeneousSupport_eq_of_max hz hmc,real_inner_smul_left]

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

omit [CompleteSpace E] in
lemma second_fderiv_const_mul {H : S × E → ℝ} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (c : ℝ) (v w : S × E) :
    fderiv ℝ (fderiv ℝ (fun q => c * H q)) x v w =
      c * fderiv ℝ (fderiv ℝ H) x v w := by
  have hh : (fun q => c * H q) = (c • ContinuousLinearMap.id ℝ ℝ) ∘ H := by
    ext q
    simp
  rw [hh]
  simpa [Function.comp_def] using second_fderiv_clm_comp
    (c • ContinuousLinearMap.id ℝ ℝ) hH v w

lemma homogeneous_fiber_hessian_scale {K : S → Set E} {s : S} {e : E}
    {D : Set S} (hD : IsOpen D) (hs : s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    {c : ℝ} (hc : 0 < c)
    (hH : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hHc : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e))
    (v w : S × E) :
    fderiv ℝ (fderiv ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2))
      (s,c • e) (normalScale c v) (normalScale c w) =
    c * fderiv ℝ (fderiv ℝ (fun q : S × E => homogeneousSupport (K q.1) q.2)) (s,e) v w := by
  let H := fun q : S × E => homogeneousSupport (K q.1) q.2
  have he : (fun q => H (normalScale c q)) =ᶠ[𝓝 (s,e)] (fun q => c * H q) := by
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (hD.mem_nhds hs)] with q hq
    exact homogeneousSupport_smul (hK _ hq) (hne _ hq) q.2 hc
  have hh := congrArg (fun A : (S × E) →L[ℝ] (S × E) →L[ℝ] ℝ => A v w)
    ((he.fderiv (𝕜 := ℝ)).fderiv_eq)
  rw [second_fderiv_const_mul hH] at hh
  have hj := second_fderiv_affine_comp (normalScale (S := S) c) (0 : S × E)
    (x := (s,e)) (by simpa using hHc) v w
  simp only [zero_add] at hj
  exact hj.symm.trans hh

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

open scoped Matrix
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [CompleteSpace E] [DecidableEq ι] in
lemma tubeFullRadiusMatrix_symm {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (b : OrthonormalBasis ι ℝ E) :
    (tubeFullRadiusMatrix H q b).IsSymm := by
  have hh := hH.isSymmSndFDerivAt (by simp)
  ext i j
  exact hh.eq _ _

omit [CompleteSpace E] [DecidableEq ι] in
lemma tubeFullRadiusMatrix_radial {H : S × E → ℝ} {q : S × E}
    (b : OrthonormalBasis ι ℝ E)
    (hr : ∀ v : E, fderiv ℝ (fderiv ℝ H) q (0,v) (0,q.2) = 0) :
    tubeFullRadiusMatrix H q b *ᵥ (b.repr q.2) = 0 := by
  ext i
  have hh := hr (b i)
  have he : ((0:S),q.2) = ∑ j, b.repr q.2 j • (0,b j) := by
    apply Prod.ext
    · simp [Prod.fst_sum]
    · simpa [Prod.snd_sum,OrthonormalBasis.repr_apply_apply] using (b.sum_repr' q.2).symm
  rw [he] at hh
  simp only [map_sum,map_smul,smul_eq_mul] at hh
  simpa [Matrix.mulVec,dotProduct,tubeFullRadiusMatrix,map_sum,map_smul,mul_comm] using hh

/- The full cofactor trace recovers the transverse determinant in every flat
normal chart. No unit-normal constraint is imposed away from the chart center. -/

omit [Fintype ι] [DecidableEq ι] in
lemma homogeneous_tubeBaseMatrix_scale {K : S → Set E} {s : S} {e : E}
    {D : Set S} (hD : IsOpen D) (hs : s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    {c : ℝ} (hc : 0 < c)
    (hH : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hHc : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e))
    (b : Module.Basis ι ℝ S) :
    tubeBaseMatrix (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e) b =
      c • tubeBaseMatrix (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) b := by
  ext i j
  have hh := homogeneous_fiber_hessian_scale hD hs hK hne hc hH hHc (b i,0) (b j,0)
  simp only [normalScale_apply,smul_zero] at hh
  simp only [tubeBaseMatrix,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul,hh,mul_neg]

omit [DecidableEq ι] in
lemma homogeneous_tubeFullRadiusMatrix_scale {K : S → Set E} {s : S} {e : E}
    {D : Set S} (hD : IsOpen D) (hs : s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    {c : ℝ} (hc : 0 < c)
    (hH : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hHc : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e))
    (b : OrthonormalBasis ι ℝ E) :
    tubeFullRadiusMatrix (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e) b =
      c⁻¹ • tubeFullRadiusMatrix (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) b := by
  ext i j
  let H := fun q : S × E => homogeneousSupport (K q.1) q.2
  have hh := homogeneous_fiber_hessian_scale hD hs hK hne hc hH hHc (0,b i) (0,b j)
  have hscale (v : E) : normalScale c ((0:S),v) = c • ((0:S),v) := by simp
  rw [hscale,hscale] at hh
  change fderiv ℝ (fderiv ℝ H) (s,c • e) (c • ((0:S),b i)) (c • ((0:S),b j)) =
    c * fderiv ℝ (fderiv ℝ H) (s,e) (0,b i) (0,b j) at hh
  simp only [map_smul,smul_apply,smul_eq_mul] at hh
  change fderiv ℝ (fderiv ℝ H) (s,c • e) (0,b i) (0,b j) =
    c⁻¹ * fderiv ℝ (fderiv ℝ H) (s,e) (0,b i) (0,b j)
  apply (mul_left_cancel₀ hc.ne')
  rw [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul]
  apply (mul_left_cancel₀ hc.ne')
  exact hh

lemma homogeneous_tubeAngularDensity_scale {K : S → Set E} {s : S} {e : E}
    {D : Set S} (hD : IsOpen D) (hs : s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    {c : ℝ} (hc : 0 < c)
    (hH : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hHc : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e))
    (b : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    tubeAngularDensity (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e) b =
      (c⁻¹)^Fintype.card κ *
        tubeAngularDensity (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) b := by
  simp only [tubeAngularDensity,homogeneous_tubeFullRadiusMatrix_scale hD hs hK hne hc hH hHc,
    Matrix.adjugate_smul,Matrix.trace_smul,smul_eq_mul,Fintype.card_sum,Fintype.card_unit,
    Nat.add_sub_cancel]

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

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_RadialAdjugateGL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
section DependencyScope
open Filter
open scoped Topology

section RadialAdjugateGL
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- The cofactor tensor of a symmetric matrix with any nonzero radial null
vector is a scalar multiple of its radial outer product. No rank or positive
definiteness assumption is needed, including an empty transverse block. -/
lemma radial_adjugate_exists_scalar {K : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ}
    (hK : K.IsSymm) {v : ι ⊕ Unit → ℝ} (hv : v ≠ 0) (hz : K *ᵥ v = 0) :
    ∃ c : ℝ, K.adjugate = c • Matrix.vecMulVec v v := by
  obtain ⟨j,hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  let e := Equiv.swap (Sum.inr ()) j
  let w : ι ⊕ Unit → ℝ := (v j)⁻¹ • (v ∘ e)
  let B := K.submatrix e e
  have hB : B.IsSymm := by
    ext a b
    exact hK.apply (e a) (e b)
  have hw : w (Sum.inr ()) = 1 := by simp [w,e,Function.comp_def,hj]
  have hzB : B *ᵥ w = 0 := by
    dsimp only [B,w]
    rw [Matrix.mulVec_smul,Matrix.submatrix_mulVec_equiv]
    have hc : (v ∘ e) ∘ e.symm = v := by funext i; simp
    rw [hc,hz]
    simp
  let c : ℝ := (B.submatrix Sum.inl Sum.inl).det * ((v j)⁻¹)^2
  refine ⟨c,?_⟩
  ext a b
  have hh := radial_adjugate hB w hw hzB (e.symm a) (e.symm b)
  dsimp only [B] at hh
  rw [Matrix.adjugate_submatrix_equiv_self] at hh
  simp only [Matrix.submatrix_apply,Equiv.apply_symm_apply,w,Pi.smul_apply,smul_eq_mul,
    Function.comp_apply] at hh
  rw [hh]
  simp only [Matrix.smul_apply,Matrix.vecMulVec_apply,smul_eq_mul,c]
  ring

lemma adjugate_congruence_radial {κ : Type*} [Fintype κ] [DecidableEq κ]
    (P K : Matrix κ κ ℝ) (v : κ → ℝ) (c : ℝ)
    (hK : K.adjugate = c • Matrix.vecMulVec (P *ᵥ v) (P *ᵥ v)) :
    (Pᵀ * K * P).adjugate = (c*P.det^2) • Matrix.vecMulVec v v := by
  rw [Matrix.adjugate_mul_distrib,Matrix.adjugate_mul_distrib,hK,
    ← Matrix.mul_assoc,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,← Matrix.adjugate_transpose,
    Matrix.vecMul_transpose,Matrix.mulVec_mulVec,Matrix.adjugate_mul,
    Matrix.smul_mulVec,Matrix.one_mulVec]
  ext i j
  simp only [Matrix.smul_apply,Matrix.vecMulVec_apply,Pi.smul_apply,smul_eq_mul]
  ring

lemma adjugate_congruence_trace_radial {κ : Type*} [Fintype κ] [DecidableEq κ]
    (P K : Matrix κ κ ℝ) (v : κ → ℝ) (c : ℝ)
    (hK : K.adjugate = c • Matrix.vecMulVec (P *ᵥ v) (P *ᵥ v))
    (hv : (∑ i, v i*v i) = 1) :
    (Pᵀ * K * P).adjugate.trace = c*P.det^2 := by
  rw [adjugate_congruence_radial P K v c hK,Matrix.trace_smul,Matrix.trace_vecMulVec]
  change (c*P.det^2)*(∑ i, v i*v i) = _
  rw [hv,mul_one]

end RadialAdjugateGL


end DependencyScope
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeLinearTransform
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
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma tubeFullRadiusMatrix_linear_comp (B : S →L[ℝ] S) (A : E →L[ℝ] E)
    {H : S × E → ℝ} {q : S × E} (hH : ContDiffAt ℝ ∞ H (B q.1,A q.2))
    (b : OrthonormalBasis κ ℝ E) :
    let P := LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap
    tubeFullRadiusMatrix (fun z => H (B z.1,A z.2)) q b =
      Pᵀ * tubeFullRadiusMatrix H (B q.1,A q.2) b * P := by
  dsimp only
  have hre (v : E) : ((0:S),v) = ∑ i, b.repr v i • (0,b i) := by
    apply Prod.ext
    · simp [Prod.fst_sum]
    · simpa only [Prod.snd_sum,Prod.smul_snd,OrthonormalBasis.repr_apply_apply] using (b.sum_repr' v).symm
  ext i j
  change fderiv ℝ (fderiv ℝ (fun z => H (B z.1,A z.2))) q (0,b i) (0,b j) = _
  have hh := second_fderiv_affine_comp (B.prodMap A) (0:S × E)
    (x:=q) (by simpa only [zero_add,ContinuousLinearMap.coe_prodMap',Prod.map] using hH) ((0:S),b i) ((0:S),b j)
  simp only [zero_add,ContinuousLinearMap.coe_prodMap',Prod.map,map_zero] at hh
  rw [hh,hre (A (b i)),hre (A (b j))]
  simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,Finset.mul_sum,
    Matrix.mul_apply,Matrix.transpose_apply,LinearMap.toMatrix_apply,Finset.sum_mul,
    tubeFullRadiusMatrix,Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  simp only [OrthonormalBasis.coe_toBasis,OrthonormalBasis.coe_toBasis_repr_apply,
    ContinuousLinearMap.coe_coe]
  ring

lemma tubeBaseMatrix_linear_comp (B : S →L[ℝ] S) (A : E →L[ℝ] E)
    {H : S × E → ℝ} {q : S × E} (hH : ContDiffAt ℝ ∞ H (B q.1,A q.2))
    (b : Module.Basis ι ℝ S) :
    let P := LinearMap.toMatrix b b B.toLinearMap
    tubeBaseMatrix (fun z => H (B z.1,A z.2)) q b =
      Pᵀ * tubeBaseMatrix H (B q.1,A q.2) b * P := by
  dsimp only
  have hre (v : S) : (v,(0:E)) = ∑ i, b.repr v i • (b i,0) := by
    apply Prod.ext
    · simpa only [Prod.fst_sum,Prod.smul_fst] using (b.sum_repr v).symm
    · simp [Prod.snd_sum]
  ext i j
  change -fderiv ℝ (fderiv ℝ (fun z => H (B z.1,A z.2))) q (b i,0) (b j,0) = _
  have hh := second_fderiv_affine_comp (B.prodMap A) (0:S × E)
    (x:=q) (by simpa only [zero_add,ContinuousLinearMap.coe_prodMap',Prod.map] using hH) (b i,(0:E)) (b j,(0:E))
  simp only [zero_add,ContinuousLinearMap.coe_prodMap',Prod.map,map_zero] at hh
  rw [hh,hre (B (b i)),hre (B (b j))]
  simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,Finset.mul_sum,
    Matrix.mul_apply,Matrix.transpose_apply,LinearMap.toMatrix_apply,Finset.sum_mul,
    tubeBaseMatrix,Matrix.of_apply,← Finset.sum_neg_distrib,neg_mul,mul_neg]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  simp only [ContinuousLinearMap.coe_coe]
  ring

lemma tubeAngularDensity_linear_comp (B : S →L[ℝ] S) (A : E ≃L[ℝ] E)
    {H : S × E → ℝ} {q : S × E} (hH : ContDiffAt ℝ ∞ H (B q.1,A q.2))
    (b : OrthonormalBasis (κ ⊕ Unit) ℝ E) (he : ‖q.2‖ = 1)
    (hr : ∀ v : E, fderiv ℝ (fderiv ℝ H) (B q.1,A q.2) (0,v) (0,A q.2) = 0) :
    tubeAngularDensity (fun z => H (B z.1,A z.2)) q b =
      A.toLinearMap.det^2 / ‖A q.2‖^2 * tubeAngularDensity H (B q.1,A q.2) b := by
  let P := LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap
  let K := tubeFullRadiusMatrix H (B q.1,A q.2) b
  let v : κ ⊕ Unit → ℝ := b.repr q.2
  have hv : (∑ i, v i*v i) = 1 := by
    dsimp only [v]
    rw [show (∑ i, b.repr q.2 i*b.repr q.2 i) = inner ℝ q.2 q.2 by
      simpa only [OrthonormalBasis.repr_apply_apply,real_inner_comm q.2] using b.sum_inner_mul_inner q.2 q.2]
    simp [he]
  have hw : P *ᵥ v = b.repr (A q.2) := LinearMap.toMatrix_mulVec_repr b.toBasis b.toBasis A.toLinearMap q.2
  have he0 : q.2 ≠ 0 := by intro hz; simp [hz] at he
  have hw0 : (P *ᵥ v) ≠ 0 := by
    rw [hw]
    intro hz
    have hz' : A q.2 = 0 := b.repr.injective (by simpa using hz)
    exact he0 (A.injective (by simpa using hz'))
  have hrad : K *ᵥ (P *ᵥ v) = 0 := by
    rw [hw]
    exact tubeFullRadiusMatrix_radial b hr
  obtain ⟨c,hc⟩ := radial_adjugate_exists_scalar (tubeFullRadiusMatrix_symm hH b) hw0 hrad
  have ht := adjugate_congruence_trace_radial P K v c hc hv
  have htr : K.adjugate.trace = c * ‖A q.2‖^2 := by
    rw [hc,Matrix.trace_smul,Matrix.trace_vecMulVec,hw]
    change c * (∑ i, b.repr (A q.2) i*b.repr (A q.2) i) = _
    have hh : (∑ i, b.repr (A q.2) i*b.repr (A q.2) i) = inner ℝ (A q.2) (A q.2) := by
      simpa only [OrthonormalBasis.repr_apply_apply,real_inner_comm (A q.2)] using
        b.sum_inner_mul_inner (A q.2) (A q.2)
    rw [hh,real_inner_self_eq_norm_sq]
  have hnorm : ‖A q.2‖ ≠ 0 := norm_ne_zero_iff.mpr (fun hz => he0 (A.injective (by simpa using hz)))
  unfold tubeAngularDensity
  have hM : tubeFullRadiusMatrix (fun z => H (B z.1,A z.2)) q b = Pᵀ*K*P :=
    tubeFullRadiusMatrix_linear_comp B A.toContinuousLinearMap hH b
  rw [hM]
  change (Pᵀ*K*P).adjugate.trace = A.toLinearMap.det^2 / ‖A q.2‖^2 * K.adjugate.trace
  rw [ht,htr]
  have hdet : P.det = A.toLinearMap.det := (LinearMap.det_toMatrix b.toBasis _)
  rw [hdet]
  field_simp

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_DensityTransform
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

section DensityTransform
open scoped Matrix
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma tubeMeasureCoefficient_congruence (n : ℕ) (h B Q d e t : ℝ) (ht : 0 < t) :
    tubeMeasureCoefficient n h (d^2*B) (e^2/t^2*Q) =
      (|d| *|e|/t)*tubeMeasureCoefficient n h B Q := by
  unfold tubeMeasureCoefficient
  have heq : d^2*B*(e^2/t^2*Q) = (d*e/t)^2*(B*Q) := by ring
  rw [heq,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_div,abs_mul,abs_of_pos ht]
  ring

omit [CompleteSpace E] in
lemma tubeMeasureDensity_linear_comp {n : ℕ} (B : S →L[ℝ] S) (A : E ≃L[ℝ] E)
    {H : S × E → ℝ} {q : S × E} (hH : ContDiffAt ℝ ∞ H (B q.1,A q.2))
    (bS : Module.Basis ι ℝ S) (b : OrthonormalBasis (κ ⊕ Unit) ℝ E) (he : ‖q.2‖ = 1)
    (hr : ∀ v : E, fderiv ℝ (fderiv ℝ H) (B q.1,A q.2) (0,v) (0,A q.2) = 0) :
    tubeMeasureDensity n (fun z => H (B z.1,A z.2)) bS b q =
      (|B.toLinearMap.det| *|A.toLinearMap.det|/‖A q.2‖)*
        tubeMeasureDensity n H bS b (B q.1,A q.2) := by
  have he0 : q.2 ≠ 0 := by intro hz; simp [hz] at he
  have ha0 : 0 < ‖A q.2‖ := norm_pos_iff.mpr (fun hz => he0 (A.injective (by simpa using hz)))
  have hb : (tubeBaseMatrix (fun z => H (B z.1,A z.2)) q bS).det =
      B.toLinearMap.det^2*(tubeBaseMatrix H (B q.1,A q.2) bS).det := by
    have hm : tubeBaseMatrix (fun z => H (B z.1,A z.2)) q bS =
      (LinearMap.toMatrix bS bS B.toLinearMap)ᵀ*tubeBaseMatrix H (B q.1,A q.2) bS*
        LinearMap.toMatrix bS bS B.toLinearMap :=
      tubeBaseMatrix_linear_comp B A.toContinuousLinearMap hH bS
    rw [hm,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,LinearMap.det_toMatrix]
    ring
  unfold tubeMeasureDensity
  rw [hb,tubeAngularDensity_linear_comp B A hH b he hr]
  exact tubeMeasureCoefficient_congruence _ _ _ _ _ _ _ ha0

lemma tubeMeasureCoefficient_homogeneous {k m : ℕ} {h B Q c : ℝ}
    (hh : 0 < h) (_hB : 0 < B) (_hQ : 0 < Q) (hc : 0 < c) :
    tubeMeasureCoefficient (k+m) (c*h) (c^k*B) ((c⁻¹)^m*Q) =
      (c⁻¹)^m*tubeMeasureCoefficient (k+m) h B Q := by
  unfold tubeMeasureCoefficient
  rw [Real.mul_rpow hc.le hh.le]
  have hprod : c^k*B*((c⁻¹)^m*Q) = (c^k*(c⁻¹)^m)*(B*Q) := by ring
  rw [hprod,← Real.rpow_natCast c k,← Real.rpow_natCast c⁻¹ m,
    Real.inv_rpow hc.le,← Real.rpow_neg hc.le,
    ← Real.rpow_add hc,Real.sqrt_mul (Real.rpow_nonneg hc.le _),Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul hc.le]
  have he : -(↑(k+m):ℝ)/2+((k:ℝ)-(m:ℝ))*(1/2) = -(m:ℝ) := by push_cast; ring_nf
  have hp : c^(-(↑(k+m):ℝ)/2)*c^(((k:ℝ)-(m:ℝ))*(1/2)) = (c⁻¹)^m := by
    rw [← Real.rpow_add hc,he,Real.rpow_neg hc.le,Real.rpow_natCast,inv_pow]
  calc
    _ = (c^(-(↑(k+m):ℝ)/2)*c^(((k:ℝ)-(m:ℝ))*(1/2)))*
        (h^(-(↑(k+m):ℝ)/2)*Real.sqrt (B*Q)) := by ring_nf
    _ = _ := by rw [hp,Real.rpow_neg hc.le,Real.rpow_natCast,inv_pow]

lemma homogeneous_tubeMeasureDensity_scale {K : S → Set E} {s : S} {e : E}
    {D : Set S} (hD : IsOpen D) (hs : s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    {c : ℝ} (hc : 0 < c)
    (hH : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hHc : ContDiffAt ℝ ∞ (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,c • e))
    (bS : Module.Basis ι ℝ S) (b : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hh : 0 < homogeneousSupport (K s) e)
    (hB : 0 < (tubeBaseMatrix (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) bS).det)
    (hQ : 0 < tubeAngularDensity (fun q : S × E => homogeneousSupport (K q.1) q.2) (s,e) b) :
    tubeMeasureDensity (Fintype.card ι+Fintype.card κ)
      (fun q : S × E => homogeneousSupport (K q.1) q.2) bS b (s,c • e) =
    (c⁻¹)^Fintype.card κ*tubeMeasureDensity (Fintype.card ι+Fintype.card κ)
      (fun q : S × E => homogeneousSupport (K q.1) q.2) bS b (s,e) := by
  unfold tubeMeasureDensity
  dsimp only
  rw [homogeneousSupport_smul (hK s hs) (hne s hs) e hc,
    homogeneous_tubeBaseMatrix_scale hD hs hK hne hc hH hHc,
    Matrix.det_smul,homogeneous_tubeAngularDensity_scale hD hs hK hne hc hH hHc]
  exact tubeMeasureCoefficient_homogeneous hh hB hQ hc
end DensityTransform

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ProjectiveCone
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

lemma sphere_lintegral_mul_radial_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ≥0∞}
    (hf : Measurable (fun e : Metric.sphere (0:E) 1 => f e))
    (hscale : ∀ (e : Metric.sphere (0:E) 1) (r : ℝ), 0 < r → r < 1 → f e = f (r • (e:E))) :
    (∫⁻ e : Metric.sphere (0:E) 1, f e ∂μ.toSphere) *
      ENNReal.ofReal (1 / ((Module.finrank ℝ E - 1 + 1 : ℕ):ℝ)) =
        ∫⁻ x in Metric.ball (0:E) 1 \ {0}, f x ∂μ := by
  let Φ := homeomorphUnitSphereProd E
  let ν := Measure.volumeIoiPow (Module.finrank ℝ E - 1)
  let r₁ : Ioi (0:ℝ) := ⟨1,by change (0:ℝ) < 1; exact one_pos⟩
  let U : Set (Metric.sphere (0:E) 1 × Ioi (0:ℝ)) := univ ×ˢ Iio r₁
  have hU : MeasurableSet U := MeasurableSet.univ.prod measurableSet_Iio
  have hmp := μ.measurePreserving_homeomorphUnitSphereProd
  have hprod : (∫⁻ q in U, f q.1 ∂μ.toSphere.prod ν) =
      (∫⁻ e : Metric.sphere (0:E) 1, f e ∂μ.toSphere) *
        ENNReal.ofReal (1 / ((Module.finrank ℝ E - 1 + 1 : ℕ):ℝ)) := by
    dsimp only [U]
    rw [setLIntegral_prod (fun q : Metric.sphere (0:E) 1 × Ioi (0:ℝ) => f q.1)
      ((hf.comp measurable_fst).aemeasurable)]
    simp only [lintegral_const,Measure.restrict_apply_univ,Measure.restrict_univ]
    rw [lintegral_mul_const _ hf]
    simp [ν,r₁,Measure.volumeIoiPow_apply_Iio]
  have hsub : Subtype.val '' (Φ ⁻¹' U) = Metric.ball (0:E) 1 \ {0} := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨?_,z.property⟩
      rw [Metric.mem_ball,dist_zero_right]
      have hz2 : ((Φ z).2:ℝ) < 1 := hz.2
      simpa [Φ,homeomorphUnitSphereProd_apply_snd_coe] using hz2
    · intro hx
      refine ⟨⟨x,hx.2⟩,?_,rfl⟩
      change True ∧ ((Φ ⟨x,hx.2⟩).2:ℝ) < 1
      exact ⟨trivial,by simpa [Φ,homeomorphUnitSphereProd_apply_snd_coe,
        Metric.mem_ball,dist_zero_right] using hx.1⟩
  have heq : (∫⁻ q in U, f ((Φ.symm q):E) ∂μ.toSphere.prod ν) =
      ∫⁻ x in Metric.ball (0:E) 1 \ {0}, f x ∂μ := by
    rw [← hmp.setLIntegral_comp_preimage_emb Φ.measurableEmbedding
      (fun q => f ((Φ.symm q):E)) U]
    simp only [Φ,Homeomorph.symm_apply_apply]
    rw [setLIntegral_subtype (measurableSet_singleton (0:E)).compl,hsub]
  rw [← hprod,← heq]
  apply setLIntegral_congr_fun hU
  intro q hq
  have hr : (q.2:ℝ) < 1 := hq.2
  simpa only [Φ,homeomorphUnitSphereProd_symm_apply_coe] using hscale q.1 q.2 q.2.property hr

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_LinearSphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
section DependencyScope
open Filter
open scoped Topology

section LinearSphere
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma linear_cone_lintegral (μ : Measure E) [μ.IsAddHaarMeasure]
    (A : E ≃L[ℝ] E) (f : E → ℝ≥0∞) (hf : Measurable f)
    (hscale : ∀ (x : E) (r : ℝ), 0 < r → f (r • x) = f x) :
    (∫⁻ x in A ⁻¹' (Metric.ball (0:E) 1 \ {0}), f (A x) ∂μ) =
    ∫⁻ e : Metric.sphere (0:E) 1, f (A e) *
      ENNReal.ofReal ((‖A e‖⁻¹)^((Module.finrank ℝ E - 1)+1) /
        (((Module.finrank ℝ E - 1)+1:ℕ):ℝ)) ∂μ.toSphere := by
  let Φ := homeomorphUnitSphereProd E
  let ν := Measure.volumeIoiPow (Module.finrank ℝ E - 1)
  let U : Set (Metric.sphere (0:E) 1 × Ioi (0:ℝ)) :=
    {q | (q.2:ℝ) * ‖A (q.1:E)‖ < 1}
  have hU : MeasurableSet U := by
    apply measurableSet_lt _ measurable_const
    exact (measurable_subtype_coe.comp measurable_snd).mul
      (A.continuous.measurable.comp (measurable_subtype_coe.comp measurable_fst)).norm
  have hnorm (z : ↑(({0}:Set E)ᶜ)) :
      ‖A z‖ = ((Φ z).2:ℝ) * ‖A ((Φ z).1:E)‖ := by
    have hz : (z:E) = ((Φ z).2:ℝ) • ((Φ z).1:E) := by
      simpa only [Φ,homeomorphUnitSphereProd_symm_apply_coe] using
        (congrArg Subtype.val (Φ.symm_apply_apply z)).symm
    conv_lhs => rw [hz]
    rw [map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (Φ z).2.property]
  have hsub : Subtype.val '' (Φ ⁻¹' U) = A ⁻¹' (Metric.ball (0:E) 1 \ {0}) := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨?_,?_⟩
      · rw [Metric.mem_ball,dist_zero_right,hnorm]
        exact hz
      · intro hz0
        have hzero : (z:E) = 0 := A.injective (by simpa using hz0)
        exact z.property hzero
    · intro hx
      have hx0 : x ≠ 0 := by
        intro hx0
        apply hx.2
        simp [hx0]
      refine ⟨⟨x,hx0⟩,?_,rfl⟩
      change ((Φ ⟨x,hx0⟩).2:ℝ) * ‖A ((Φ ⟨x,hx0⟩).1:E)‖ < 1
      rw [← hnorm]
      simpa only [Metric.mem_ball,dist_zero_right] using hx.1
  have heq : (∫⁻ q in U, f (A ((Φ.symm q):E)) ∂μ.toSphere.prod ν) =
      ∫⁻ x in A ⁻¹' (Metric.ball (0:E) 1 \ {0}), f (A x) ∂μ := by
    rw [← μ.measurePreserving_homeomorphUnitSphereProd.setLIntegral_comp_preimage_emb
      Φ.measurableEmbedding (fun q => f (A ((Φ.symm q):E))) U]
    simp only [Φ,Homeomorph.symm_apply_apply]
    rw [setLIntegral_subtype (measurableSet_singleton (0:E)).compl _ (fun x : E => f (A x)),hsub]
  rw [← heq]
  have hg : Measurable (fun q : Metric.sphere (0:E) 1 × Ioi (0:ℝ) => f (A q.1)) :=
    hf.comp (A.continuous.measurable.comp (measurable_subtype_coe.comp measurable_fst))
  have hreplace : (∫⁻ q in U, f (A ((Φ.symm q):E)) ∂μ.toSphere.prod ν) =
      ∫⁻ q in U, f (A q.1) ∂μ.toSphere.prod ν := by
    apply setLIntegral_congr_fun hU
    intro q _
    simp only [Φ,homeomorphUnitSphereProd_symm_apply_coe,map_smul]
    exact hscale _ _ q.2.property
  rw [hreplace,← lintegral_indicator hU,lintegral_prod _ ((hg.indicator hU).aemeasurable)]
  apply lintegral_congr
  intro e
  have he0 : (e:E) ≠ 0 := by
    intro he0
    simpa [he0] using e.property
  have ha : 0 < ‖A e‖ := norm_pos_iff.mpr (fun hz => he0 (A.injective (by simpa using hz)))
  let ar : Ioi (0:ℝ) := ⟨‖A e‖⁻¹,inv_pos.mpr ha⟩
  have hind : (fun t : Ioi (0:ℝ) => U.indicator (fun q => f (A q.1)) (e,t)) =
      (Iio ar).indicator (fun _ => f (A e)) := by
    funext t
    simp only [Set.indicator,Set.mem_ofPred_eq,Set.mem_Iio,U,ar]
    congr 1
    change ((t:ℝ)*‖A e‖ < 1) = ((t:ℝ) < ‖A e‖⁻¹)
    apply propext
    rw [inv_eq_one_div,lt_div_iff₀ ha]
  rw [hind,lintegral_indicator measurableSet_Iio,lintegral_const,
    Measure.restrict_apply_univ]
  simp only [ν,Measure.volumeIoiPow_apply_Iio,ar,Nat.cast_add,Nat.cast_one]


/- Exact projective change of variables on Haar-normalized sphere area. The
Jacobian is derived from the linear volume determinant and polar coordinates.
The ambient integrand is homogeneous of degree zero; no integrability is assumed. -/
lemma sphere_lintegral_linear_jacobian (μ : Measure E) [μ.IsAddHaarMeasure]
    [Nontrivial E] (A : E ≃L[ℝ] E) (f : E → ℝ≥0∞) (hf : Measurable f)
    (hscale : ∀ (x : E) (r : ℝ), 0 < r → f (r • x) = f x) :
    (∫⁻ e : Metric.sphere (0:E) 1, f e ∂μ.toSphere) =
    ENNReal.ofReal |A.toLinearMap.det| *
      ∫⁻ e : Metric.sphere (0:E) 1,
        f (A e) * ENNReal.ofReal ((‖A e‖⁻¹)^(Module.finrank ℝ E)) ∂μ.toSphere := by
  have hd : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hdim : Module.finrank ℝ E - 1 + 1 = Module.finrank ℝ E := Nat.sub_add_cancel hd
  let S := Metric.ball (0:E) 1 \ {0}
  have hS : MeasurableSet (A ⁻¹' S) :=
    (Metric.isOpen_ball.measurableSet.diff (measurableSet_singleton 0)).preimage A.continuous.measurable
  have hj := lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ:=μ) hS
    (fun x _ => A.hasFDerivAt.hasFDerivWithinAt) A.injective.injOn f
  rw [Set.image_preimage_eq _ A.surjective] at hj
  change (∫⁻ x in S, f x ∂μ) =
    ∫⁻ x in A ⁻¹' S, ENNReal.ofReal |A.toLinearMap.det| * f (A x) ∂μ at hj
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hj
  have hr := sphere_lintegral_mul_radial_eq μ
    (hf.comp measurable_subtype_coe) (fun e r hr _ => (hscale e r hr).symm)
  rw [hdim] at hr
  have hc := linear_cone_lintegral μ A f hf hscale
  rw [hdim] at hc
  have hsplit : (∫⁻ e : Metric.sphere (0:E) 1, f (A e) *
      ENNReal.ofReal (‖A e‖⁻¹ ^ Module.finrank ℝ E / (Module.finrank ℝ E:ℝ)) ∂μ.toSphere) =
      (∫⁻ e : Metric.sphere (0:E) 1,
        f (A e) * ENNReal.ofReal (‖A e‖⁻¹ ^ Module.finrank ℝ E) ∂μ.toSphere) *
        ENNReal.ofReal (1 / (Module.finrank ℝ E:ℝ)) := by
    have he (e : Metric.sphere (0:E) 1) :
        ENNReal.ofReal (‖A e‖⁻¹ ^ Module.finrank ℝ E / (Module.finrank ℝ E:ℝ)) =
        ENNReal.ofReal (‖A e‖⁻¹ ^ Module.finrank ℝ E) *
          ENNReal.ofReal (1 / (Module.finrank ℝ E:ℝ)) := by
      rw [← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _)]
      congr 1
      ring
    simp_rw [he,← mul_assoc]
    exact lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
  apply (ENNReal.mul_left_inj (by positivity : ENNReal.ofReal (1 / (Module.finrank ℝ E:ℝ)) ≠ 0)
    ENNReal.ofReal_ne_top).mp
  rw [hr,hj,hc,hsplit,mul_assoc]

end LinearSphere

end DependencyScope
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_HomogeneousSphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
section DependencyScope
open Filter
open scoped Topology

section HomogeneousSphere
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/- The projective sphere Jacobian cancels a homogeneous density of degree
`-(dim E - 1)`, leaving precisely one inverse norm. -/
lemma sphere_lintegral_homogeneous_linear (μ : Measure E) [μ.IsAddHaarMeasure]
    (A : E ≃L[ℝ] E) (f : E → ℝ≥0∞) (hf : Measurable f)
    (hscale : ∀ (x : E), x ≠ 0 → ∀ (r : ℝ), 0 < r →
      f (r • x) = ENNReal.ofReal ((r⁻¹)^(Module.finrank ℝ E - 1)) * f x) :
    (∫⁻ e : Metric.sphere (0:E) 1, f e ∂μ.toSphere) =
      ENNReal.ofReal |A.toLinearMap.det| *
        ∫⁻ e : Metric.sphere (0:E) 1,
          f (A e) * ENNReal.ofReal (‖A e‖⁻¹) ∂μ.toSphere := by
  let g : E → ℝ≥0∞ := fun x => f (‖x‖⁻¹ • x)
  have hg : Measurable g := hf.comp (measurable_norm.inv.smul measurable_id)
  have hgscale (x : E) (r : ℝ) (hr : 0 < r) : g (r • x) = g x := by
    dsimp [g]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,mul_inv_rev,smul_smul]
    congr 2
    field_simp
  have htrans := sphere_lintegral_linear_jacobian μ A g hg hgscale
  have hn (e : Metric.sphere (0:E) 1) : ‖(e:E)‖ = 1 := by
    simp
  have hgs (e : Metric.sphere (0:E) 1) : g e = f e := by simp [g,hn]
  have heq (e : Metric.sphere (0:E) 1) :
      g (A e) * ENNReal.ofReal (‖A e‖⁻¹ ^ Module.finrank ℝ E) =
        f (A e) * ENNReal.ofReal (‖A e‖⁻¹) := by
    have he : (e:E) ≠ 0 := by intro h; simpa [h] using hn e
    have ha : 0 < ‖A e‖ := norm_pos_iff.mpr (fun h => he (A.injective (by simpa using h)))
    dsimp [g]
    rw [hscale (A e) (norm_ne_zero_iff.mp ha.ne') _ (inv_pos.mpr ha),inv_inv]
    have hp : ‖A e‖ ^ (Module.finrank ℝ E - 1) *
        (‖A e‖⁻¹ ^ Module.finrank ℝ E) = ‖A e‖⁻¹ := by
      have hd := Nat.sub_add_cancel (Module.finrank_pos (R:=ℝ) (M:=E))
      conv_lhs => arg 2; rw [← hd,pow_succ]
      rw [← mul_assoc,← mul_pow,mul_inv_cancel₀ ha.ne',one_pow,one_mul]
    calc
      _ = f (A e) * (ENNReal.ofReal (‖A e‖ ^ (Module.finrank ℝ E - 1)) *
        ENNReal.ofReal (‖A e‖⁻¹ ^ Module.finrank ℝ E)) := by ring
      _ = _ := by rw [← ENNReal.ofReal_mul (pow_nonneg (norm_nonneg _) _),hp]
  simpa only [hgs,heq] using htrans
end HomogeneousSphere



end DependencyScope
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
end LogMassWeight

/- Real positive densities can be interpolated before or after `ofReal`. -/

end DependencyScope

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_WeightTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
section DependencyScope
open Filter
open scoped Topology

section WeightTransform
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma tubeLogMassWeight_eq {k : ℕ} (H : Space k × E → ℝ) (q : Space k × E)
    (hs : ∀ i, q.1 i ≠ 0) :
    tubeLogMassWeight H q = 1 + ∑ i, H q *
      (tubeBaseMatrix H q (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)⁻¹ i i/(q.1 i)^2 := by
  simp only [tubeLogMassWeight,tubeBasePair_coordinate_log H q _ (hs _)]

lemma matrix_inverse_diagonal_congruence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (d : ι → ℝ) (hd : ∀ i, d i ≠ 0) (i j : ι) :
    (Matrix.diagonal d*A*Matrix.diagonal d)⁻¹ i j = (d i)⁻¹*A⁻¹ i j*(d j)⁻¹ := by
  have hi : (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun i => (d i)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    simp [Matrix.diagonal_mul_diagonal,hd]
  rw [Matrix.mul_inv_rev,Matrix.mul_inv_rev,hi]
  simp [Matrix.diagonal_mul,Matrix.mul_diagonal,mul_assoc]

omit [CompleteSpace E] in
lemma tubeLogMassWeight_diagonal_comp {k : ℕ} (B : Space k →L[ℝ] Space k) (A : E →L[ℝ] E)
    (d : Fin k → ℝ) (hd : ∀ i, d i ≠ 0) (hBd : ∀ s i, B s i = d i*s i)
    {H : Space k × E → ℝ} {q : Space k × E}
    (hH : ContDiffAt ℝ ∞ H (B q.1,A q.2)) (hs : ∀ i, q.1 i ≠ 0) :
    tubeLogMassWeight (fun z => H (B z.1,A z.2)) q =
      tubeLogMassWeight H (B q.1,A q.2) := by
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have hM : LinearMap.toMatrix b b B.toLinearMap = Matrix.diagonal d := by
    ext i j
    simp [b,LinearMap.toMatrix_apply,EuclideanSpace.basisFun_repr,hBd,
      EuclideanSpace.basisFun_apply,PiLp.single_apply,Matrix.diagonal_apply]
  have hb : tubeBaseMatrix (fun z => H (B z.1,A z.2)) q b =
      Matrix.diagonal d*tubeBaseMatrix H (B q.1,A q.2) b*Matrix.diagonal d := by
    rw [tubeBaseMatrix_linear_comp B A hH b,hM,Matrix.diagonal_transpose]
  rw [tubeLogMassWeight_eq _ q hs,tubeLogMassWeight_eq _ (B q.1,A q.2)
    (fun i => by dsimp; rw [hBd]; exact mul_ne_zero (hd i) (hs i))]
  change 1 + ∑ i, H (B q.1,A q.2) * (tubeBaseMatrix (fun z => H (B z.1,A z.2)) q b)⁻¹ i i / (q.1 i)^2 = _
  rw [hb]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [matrix_inverse_diagonal_congruence _ d hd]
  dsimp only
  rw [hBd]
  field_simp
  rfl

lemma tubeLogMassWeight_homogeneous {k : ℕ} {K : Space k → Set E} {s : Space k} {e : E}
    {D : Set (Space k)} (hD : IsOpen D) (hs : s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    {c : ℝ} (hc : 0 < c)
    (hH : ContDiffAt ℝ ∞ (fun q : Space k × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hHc : ContDiffAt ℝ ∞ (fun q : Space k × E => homogeneousSupport (K q.1) q.2) (s,c • e))
    (hs0 : ∀ i, s i ≠ 0)
    (hB : (tubeBaseMatrix (fun q : Space k × E => homogeneousSupport (K q.1) q.2) (s,e)
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det ≠ 0) :
    tubeLogMassWeight (fun q : Space k × E => homogeneousSupport (K q.1) q.2) (s,c • e) =
      tubeLogMassWeight (fun q : Space k × E => homogeneousSupport (K q.1) q.2) (s,e) := by
  let : Invertible c := invertibleOfNonzero hc.ne'
  rw [tubeLogMassWeight_eq _ _ hs0,tubeLogMassWeight_eq _ _ hs0]
  dsimp only
  rw [homogeneousSupport_smul (hK s hs) (hne s hs) e hc,
    homogeneous_tubeBaseMatrix_scale hD hs hK hne hc hH hHc,
    Matrix.inv_smul _ _ (isUnit_iff_ne_zero.mpr hB),invOf_eq_inv]
  simp only [Matrix.smul_apply,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  field_simp
end WeightTransform





end DependencyScope
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SigmaTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
section DependencyScope
open Filter
open scoped Topology

section SigmaTransform
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma continuousAt_tubeLogMassWeight_fixed {k : ℕ} {H : Space k × E → ℝ}
    {s : Space k} {e : E} (hH : ContDiffAt ℝ ∞ H (s,e))
    (hs : ∀ i, s i ≠ 0)
    (hd : (tubeBaseMatrix H (s,e) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det ≠ 0) :
    ContinuousAt (fun y => tubeLogMassWeight H (s,y)) e := by
  simp_rw [tubeLogMassWeight_eq H (s,_) hs]
  apply continuousAt_const.add
  apply tendsto_finsetSum
  intro i _
  have hM := contDiffAt_tubeBaseMatrix hH (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have hi : ContinuousAt (fun q => (tubeBaseMatrix H q
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)⁻¹ i i) (s,e) := by
    simp only [Matrix.inv_def,Matrix.smul_apply,smul_eq_mul,Ring.inverse_eq_inv]
    exact ((((continuousDetRows (ι:=Fin k)).contDiff.contDiffAt.comp _ hM).continuousAt.inv₀ hd).mul
      (contDiffAt_adjugate_entries hM i i).continuousAt)
  exact ((hH.continuousAt.mul hi).comp (continuousAt_const.prodMk continuousAt_id)).div_const _

/- Exact covariance of the actual weighted density integrated over all normal
directions, with its transverse GL Jacobian cancelled by the sphere measure. -/
lemma sphere_sigma_density_linear_comp {k d : ℕ}
    (bE : OrthonormalBasis (Fin d ⊕ Unit) ℝ E)
    (B : Space k ≃L[ℝ] Space k) (A : E ≃L[ℝ] E)
    (a : Fin k → ℝ) (ha : ∀ i, a i ≠ 0) (hBa : ∀ s i, B s i = a i*s i)
    {K : Space k → Set E} {D : Set (Space k)} (hD : IsOpen D) {s : Space k} (hsD : B s ∈ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    (hs : ∀ i, s i ≠ 0)
    (hH : ∀ e : E, e ≠ 0 → ContDiffAt ℝ ∞
      (fun q : Space k × E => homogeneousSupport (K q.1) q.2) (B s,e))
    (hr : ∀ e : E, e ≠ 0 → ∀ v : E, fderiv ℝ
      (fderiv ℝ (fun q : Space k × E => homogeneousSupport (K q.1) q.2)) (B s,e) (0,v) (0,e) = 0)
    (hp : ∀ e : E, e ≠ 0 → 0 < homogeneousSupport (K (B s)) e ∧
      0 < (tubeBaseMatrix (fun q : Space k × E => homogeneousSupport (K q.1) q.2) (B s,e)
        (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det ∧
      0 < tubeAngularDensity (fun q : Space k × E => homogeneousSupport (K q.1) q.2) (B s,e) bE) :
    let H := fun q : Space k × E => homogeneousSupport (K q.1) q.2
    let H' := fun q : Space k × E => H (B q.1,A q.2)
    let bS := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    (∫⁻ e : Metric.sphere (0:E) 1,
      ENNReal.ofReal (tubeMeasureDensity (k+d) H' bS bE (s,e)*tubeLogMassWeight H' (s,e))
      ∂(volume : Measure E).toSphere) =
    ENNReal.ofReal |B.toLinearMap.det| * ∫⁻ e : Metric.sphere (0:E) 1,
      ENNReal.ofReal (tubeMeasureDensity (k+d) H bS bE (B s,e)*tubeLogMassWeight H (B s,e))
      ∂(volume : Measure E).toSphere := by
  let H := fun q : Space k × E => homogeneousSupport (K q.1) q.2
  let bS := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let f : E → ℝ≥0∞ := fun e =>
    ENNReal.ofReal (tubeMeasureDensity (k+d) H bS bE (B s,e)*tubeLogMassWeight H (B s,e))
  have hdE : Module.finrank ℝ E = d+1 := by
    simpa using Module.finrank_eq_card_basis bE.toBasis
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ E)
  have hBs (i : Fin k) : B s i ≠ 0 := by rw [hBa]; exact mul_ne_zero (ha i) (hs i)
  have hf : Measurable f := by
    apply ContinuousOn.measurable_of_countable_compl (s:=({0}:Set E)ᶜ)
    · intro e he
      have h0 : e ≠ 0 := he
      apply ContinuousAt.continuousWithinAt
      apply ENNReal.continuous_ofReal.continuousAt.comp
      exact ((continuousAt_tubeMeasureDensity (hH e h0) bS bE (hp e h0).1).comp
        (continuousAt_const.prodMk continuousAt_id)).mul
        (continuousAt_tubeLogMassWeight_fixed (hH e h0) hBs (hp e h0).2.1.ne')
    · simp only [compl_compl]; exact countable_singleton 0
  have hscale (e : E) (he : e ≠ 0) (r : ℝ) (hr0 : 0 < r) :
      f (r • e) = ENNReal.ofReal (r⁻¹ ^ (Module.finrank ℝ E-1))*f e := by
    have hre : r • e ≠ 0 := smul_ne_zero hr0.ne' he
    have hμ := homogeneous_tubeMeasureDensity_scale hD hsD hK hne hr0 (hH e he) (hH _ hre)
      bS bE (hp e he).1 (hp e he).2.1 (hp e he).2.2
    simp only [Fintype.card_fin] at hμ
    dsimp only [f]
    rw [hμ,tubeLogMassWeight_homogeneous hD hsD hK hne hr0 (hH e he) (hH _ hre)
      hBs (hp e he).2.1.ne',hdE,Nat.add_sub_cancel_right,mul_assoc,
      ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hr0.le) _)]
  have htrans := sphere_lintegral_homogeneous_linear (volume : Measure E) A f hf hscale
  dsimp only
  rw [htrans,← mul_assoc,← lintegral_const_mul' _ _
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  apply lintegral_congr
  intro e
  have he : (e:E) ≠ 0 := Metric.ne_of_mem_sphere e.property one_ne_zero
  have hae : A e ≠ 0 := fun h => he (A.injective (by simpa using h))
  have hen : ‖(e:E)‖ = 1 := by simp
  change ENNReal.ofReal (tubeMeasureDensity (k+d) (fun z => H (B.toContinuousLinearMap z.1,A z.2)) bS bE (s,(e:E)) *
    tubeLogMassWeight (fun z => H (B.toContinuousLinearMap z.1,A z.2)) (s,(e:E))) = _
  rw [tubeMeasureDensity_linear_comp (n:=k+d) B.toContinuousLinearMap A
      (H:=H) (q:=(s,(e:E))) (hH _ hae) bS bE hen (hr _ hae)]
  have hw : tubeLogMassWeight (fun z => H (B.toContinuousLinearMap z.1,A z.2)) (s,(e:E)) =
      tubeLogMassWeight H (B s,A e) :=
    tubeLogMassWeight_diagonal_comp B.toContinuousLinearMap A.toContinuousLinearMap a ha hBa
      (H:=H) (q:=(s,(e:E))) (hH _ hae) hs
  rw [hw]
  change ENNReal.ofReal ((|B.toLinearMap.det| * |A.toLinearMap.det| / ‖A e‖) *
    tubeMeasureDensity (k+d) H bS bE (B s,A e) * tubeLogMassWeight H (B s,A e)) = _
  rw [mul_assoc,ENNReal.ofReal_mul (by positivity :
    0 ≤ |B.toLinearMap.det| * |A.toLinearMap.det| / ‖A e‖)]
  dsimp only [f]
  rw [div_eq_mul_inv,ENNReal.ofReal_mul (by positivity :
    0 ≤ |B.toLinearMap.det| * |A.toLinearMap.det|),ENNReal.ofReal_mul (abs_nonneg _)]
  ring
end SigmaTransform



end DependencyScope
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SigmaBaseTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
section DependencyScope
open Filter
open scoped Topology

section SigmaBaseTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma continuousAt_tubeLogMassWeight {k : ℕ} {H : Space k × E → ℝ}
    {q : Space k × E} (hH : ContDiffAt ℝ ∞ H q)
    (hs : ∀ i, q.1 i ≠ 0)
    (hd : (tubeBaseMatrix H q (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det ≠ 0) :
    ContinuousAt (tubeLogMassWeight H) q := by
  let bS := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have hM := contDiffAt_tubeBaseMatrix hH bS
  have hi (i : Fin k) : ContinuousAt (fun z => (tubeBaseMatrix H z bS)⁻¹ i i) q := by
    simp only [Matrix.inv_def,Matrix.smul_apply,smul_eq_mul,Ring.inverse_eq_inv]
    exact ((((continuousDetRows (ι:=Fin k)).contDiff.contDiffAt.comp _ hM).continuousAt.inv₀ hd).mul
      (contDiffAt_adjugate_entries hM i i).continuousAt)
  have hcoord (i : Fin k) : ContinuousAt (fun z : Space k × E => z.1 i) q := by fun_prop
  have hc : ContinuousAt (fun z => 1 + ∑ i, H z*(tubeBaseMatrix H z bS)⁻¹ i i/(z.1 i)^2) q := by
    apply continuousAt_const.add
    apply tendsto_finsetSum
    intro i _
    exact (hH.continuousAt.mul (hi i)).div ((hcoord i).pow 2) (pow_ne_zero _ (hs i))
  apply hc.congr_of_eventuallyEq
  have he : ∀ᶠ z in 𝓝 q, ∀ i, z.1 i ≠ 0 :=
    Filter.eventually_all.mpr (fun i => (hcoord i).eventually_ne (hs i))
  filter_upwards [he] with z hz
  exact tubeLogMassWeight_eq H z hz

omit [CompleteSpace E] in
lemma aemeasurable_tube_sigma {n k d : ℕ} (H : Space k × E → ℝ)
    (bE : OrthonormalBasis (Fin d ⊕ Unit) ℝ E)
    {Q : Set (Space k)} (hQ : MeasurableSet Q)
    (hbase : ∀ s ∈ Q, ∀ i, s i ≠ 0)
    (hH : ∀ s ∈ Q, ∀ e : E, e ≠ 0 → ContDiffAt ℝ ∞ H (s,e))
    (hp : ∀ s ∈ Q, ∀ e : E, e ≠ 0 → 0 < H (s,e) ∧
      (tubeBaseMatrix H (s,e) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det ≠ 0) :
    AEMeasurable (fun q : Space k × Metric.sphere (0:E) 1 =>
      ENNReal.ofReal (tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE
        (q.1,q.2)*tubeLogMassWeight H (q.1,q.2)))
      ((volume.restrict Q).prod (volume : Measure E).toSphere) := by
  rw [Measure.restrict_prod_eq_prod_univ]
  apply ContinuousOn.aemeasurable _ (hQ.prod MeasurableSet.univ)
  intro q hq
  have he : (q.2:E) ≠ 0 := Metric.ne_of_mem_sphere q.2.property one_ne_zero
  have hm : Continuous (fun q : Space k × Metric.sphere (0:E) 1 => (q.1,(q.2:E))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hpcont : ContinuousAt (fun z : Space k × E =>
      tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE z *
        tubeLogMassWeight H z) (q.1,(q.2:E)) :=
    (continuousAt_tubeMeasureDensity (hH q.1 hq.1 _ he) _ bE
      (hp q.1 hq.1 _ he).1).mul
        (continuousAt_tubeLogMassWeight (hH q.1 hq.1 _ he) (hbase q.1 hq.1)
          (hp q.1 hq.1 _ he).2)
  exact (ENNReal.continuous_ofReal.continuousAt.comp
    (ContinuousAt.comp (f:=fun z : Space k × Metric.sphere (0:E) 1 => (z.1,(z.2:E)))
      (g:=fun z : Space k × E => tubeMeasureDensity n H
        (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE z * tubeLogMassWeight H z)
      hpcont hm.continuousAt)).continuousWithinAt


/- Full base-and-normal covariance of actual sigma: positive diagonal base
normalization and an arbitrary transverse GL change preserve its cell mass.
The assumptions describe local regularity and convexity of the support function,
not an integral bound or a transport law. -/
lemma sigma_cell_linear_comp {k d : ℕ}
    (bE : OrthonormalBasis (Fin d ⊕ Unit) ℝ E)
    (B : Space k ≃L[ℝ] Space k) (A : E ≃L[ℝ] E)
    (a : Fin k → ℝ) (ha : ∀ i, a i ≠ 0) (hBa : ∀ s i, B s i = a i*s i)
    {K : Space k → Set E} {D : Set (Space k)} (hD : IsOpen D)
    {Q : Set (Space k)} (hQ : MeasurableSet Q) (hQD : B '' Q ⊆ D)
    (hK : ∀ y ∈ D, IsCompact (K y)) (hne : ∀ y ∈ D, (K y).Nonempty)
    (hs : ∀ s ∈ Q, ∀ i, s i ≠ 0)
    (hH : ∀ s ∈ D, ∀ e : E, e ≠ 0 → ContDiffAt ℝ ∞
      (fun q : Space k × E => homogeneousSupport (K q.1) q.2) (s,e))
    (hr : ∀ s ∈ D, ∀ e : E, e ≠ 0 → ∀ v : E, fderiv ℝ
      (fderiv ℝ (fun q : Space k × E => homogeneousSupport (K q.1) q.2)) (s,e) (0,v) (0,e) = 0)
    (hp : ∀ s ∈ D, ∀ e : E, e ≠ 0 → 0 < homogeneousSupport (K s) e ∧
      0 < (tubeBaseMatrix (fun q : Space k × E => homogeneousSupport (K q.1) q.2) (s,e)
        (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det ∧
      0 < tubeAngularDensity (fun q : Space k × E => homogeneousSupport (K q.1) q.2) (s,e) bE) :
    let H := fun q : Space k × E => homogeneousSupport (K q.1) q.2
    let H' := fun q : Space k × E => H (B q.1,A q.2)
    let bS := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    (∫⁻ q : Space k × Metric.sphere (0:E) 1,
      ENNReal.ofReal (tubeMeasureDensity (k+d) H' bS bE (q.1,q.2)*tubeLogMassWeight H' (q.1,q.2))
      ∂(volume.restrict Q).prod (volume : Measure E).toSphere) =
    (∫⁻ q : Space k × Metric.sphere (0:E) 1,
      ENNReal.ofReal (tubeMeasureDensity (k+d) H bS bE (q.1,q.2)*tubeLogMassWeight H (q.1,q.2))
      ∂(volume.restrict (B '' Q)).prod (volume : Measure E).toSphere) := by
  let H := fun q : Space k × E => homogeneousSupport (K q.1) q.2
  let H' := fun q : Space k × E => H (B q.1,A q.2)
  let bS := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let f : Space k × Metric.sphere (0:E) 1 → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (tubeMeasureDensity (k+d) H bS bE (q.1,q.2)*tubeLogMassWeight H (q.1,q.2))
  let f' : Space k × Metric.sphere (0:E) 1 → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (tubeMeasureDensity (k+d) H' bS bE (q.1,q.2)*tubeLogMassWeight H' (q.1,q.2))
  have hBs (s : Space k) (hsQ : s ∈ Q) : B s ∈ D := hQD ⟨s,hsQ,rfl⟩
  have heA (e : E) (he : e ≠ 0) : A e ≠ 0 := fun h => he (A.injective (by simpa using h))
  have hh' (s : Space k) (hsQ : s ∈ Q) (e : E) (he : e ≠ 0) : ContDiffAt ℝ ∞ H' (s,e) := by
    have hh : ContDiffAt ℝ ∞ H (B s,A e) := hH _ (hBs s hsQ) _ (heA e he)
    have hm : ContDiffAt ℝ ∞ (fun q : Space k × E => (B q.1,A q.2)) (s,e) :=
      (B.contDiff.contDiffAt.comp _ contDiffAt_fst).prodMk (A.contDiff.contDiffAt.comp _ contDiffAt_snd)
    exact ContDiffAt.comp (f:=fun q : Space k × E => (B q.1,A q.2)) (g:=H) (s,e) hh hm
  have hp' (s : Space k) (hsQ : s ∈ Q) (e : E) (he : e ≠ 0) :
      0 < H' (s,e) ∧ (tubeBaseMatrix H' (s,e) bS).det ≠ 0 := by
    refine ⟨(hp _ (hBs s hsQ) _ (heA e he)).1,?_⟩
    have hm := tubeBaseMatrix_linear_comp B.toContinuousLinearMap A.toContinuousLinearMap
      (H:=H) (q:=(s,e)) (hH _ (hBs s hsQ) _ (heA e he)) bS
    change (tubeBaseMatrix (fun z => H (B.toContinuousLinearMap z.1,A.toContinuousLinearMap z.2)) (s,e) bS).det ≠ 0
    rw [hm,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,LinearMap.det_toMatrix]
    exact mul_ne_zero (mul_ne_zero B.toLinearEquiv.isUnit_det'.ne_zero
      (hp _ (hBs s hsQ) _ (heA e he)).2.1.ne') B.toLinearEquiv.isUnit_det'.ne_zero
  have hf' : AEMeasurable f' ((volume.restrict Q).prod (volume : Measure E).toSphere) :=
    aemeasurable_tube_sigma H' bE hQ hs hh' hp'
  have hBQ : MeasurableSet (B '' Q) := B.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hQ
  have hf : AEMeasurable f ((volume.restrict (B '' Q)).prod (volume : Measure E).toSphere) :=
    aemeasurable_tube_sigma H bE hBQ
      (by rintro _ ⟨s,hsQ,rfl⟩ i; rw [hBa]; exact mul_ne_zero (ha i) (hs s hsQ i))
      (fun s hsQ => hH s (hQD hsQ))
      (fun s hsQ e he => ⟨(hp s (hQD hsQ) e he).1,(hp s (hQD hsQ) e he).2.1.ne'⟩)
  change (∫⁻ q, f' q ∂(volume.restrict Q).prod (volume : Measure E).toSphere) =
    ∫⁻ q, f q ∂(volume.restrict (B '' Q)).prod (volume : Measure E).toSphere
  rw [lintegral_prod f' hf',lintegral_prod f hf]
  have hj := lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ:=volume) hQ
    (fun _ _ => B.hasFDerivAt.hasFDerivWithinAt) B.injective.injOn
    (fun s => ∫⁻ e, f (s,e) ∂(volume : Measure E).toSphere)
  rw [hj]
  apply setLIntegral_congr_fun hQ
  intro s hsQ
  exact sphere_sigma_density_linear_comp bE B A a ha hBa hD (hBs s hsQ) hK hne (hs s hsQ)
    (hH _ (hBs s hsQ)) (hr _ (hBs s hsQ)) (hp _ (hBs s hsQ))
end SigmaBaseTransport



end DependencyScope
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SigmaNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
section DependencyScope
open Filter
open scoped Topology

section SigmaNormalization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- The genuine adjoint equivalence of a transverse linear normalization. -/

lemma homogeneousSupport_linear_image (A : E ≃L[ℝ] E) (K : Set E) (e : E) :
    homogeneousSupport (A '' K) e = homogeneousSupport K (adjointEquiv A e) := by
  unfold homogeneousSupport supportValue
  congr 1
  rw [Set.image_image]
  congr 1
  funext y
  exact (ContinuousLinearMap.adjoint_inner_left A.toContinuousLinearMap y e).symm

lemma adjointEquiv_inv_apply (A : E ≃L[ℝ] E) (e : E) :
    adjointEquiv A (adjointEquiv A.symm e) = e := by
  change (A.toContinuousLinearMap.adjoint.comp A.symm.toContinuousLinearMap.adjoint) e = e
  rw [← ContinuousLinearMap.adjoint_comp]
  have h : A.symm.toContinuousLinearMap.comp A.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ E := by ext x; simp
  rw [h,ContinuousLinearMap.adjoint_id,ContinuousLinearMap.id_apply]

omit [CompleteSpace E] in
lemma prod_image_fiber {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    (B : S ≃L[ℝ] S) (A : E ≃L[ℝ] E) (C : Set (S × E)) (s : S) :
    {y | (s,y) ∈ (B.prodCongr A) '' C} = A '' {y | (B.symm s,y) ∈ C} := by
  ext y
  constructor
  · rintro ⟨⟨t,z⟩,hz,he⟩
    have ht : B t = s := congrArg Prod.fst he
    have hy : A z = y := congrArg Prod.snd he
    refine ⟨z,?_,hy⟩
    simpa only [Set.mem_ofPred_eq,← ht,B.symm_apply_apply] using hz
  · rintro ⟨z,hz,rfl⟩
    exact ⟨(B.symm s,z),hz,by simp⟩

/- The support of the actual normalized fiber, pulled back by inverse-adjoint
normal variables, is the original support. No fiber hypothesis is used. -/
lemma support_normalized_pullback {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    (B : S ≃L[ℝ] S) (A : E ≃L[ℝ] E) (C : Set (S × E)) :
    (fun q : S × E => homogeneousSupport {y | (B q.1,y) ∈ (B.prodCongr A) '' C}
      (adjointEquiv A.symm q.2)) =
    (fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ C} q.2) := by
  funext q
  rw [prod_image_fiber,homogeneousSupport_linear_image,adjointEquiv_inv_apply,B.symm_apply_apply]
end SigmaNormalization


end DependencyScope


end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NormalizedSigmaTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section NormalizedSigmaTransport
open Filter Metric

lemma affineEpigraphPullback_normalize {n k m : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (a : Space n × ℝ) (L : (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
    (N : (Space k × Space m) ≃L[ℝ] (Space k × Space m)) :
    affineEpigraphPullback Ω u a (N.symm.trans L) = N '' affineEpigraphPullback Ω u a L := by
  ext q
  constructor
  · intro h
    exact ⟨N.symm q,h,N.apply_symm_apply q⟩
  · rintro ⟨p,hp,rfl⟩
    simpa only [affineEpigraphPullback,Set.mem_ofPred_eq,ContinuousLinearEquiv.trans_apply,
      N.symm_apply_apply] using hp

/-- Actual sigma in any diagonal-base/transverse GL normalization. All support
smoothness and determinant positivity are produced by the positive Hessian of
the original graph, not assumed as sigma identities. -/
theorem affineEpigraph_sigma_normalization_oai {n k m d : ℕ} (hm : 1 ≤ m)
    (hn : n = k+d) (bE : OrthonormalBasis (Fin d ⊕ Unit) ℝ (Space m))
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
    (B : Space k ≃L[ℝ] Space k) (A : Space m ≃L[ℝ] Space m)
    (coeff : Fin k → ℝ) (hcoeff : ∀ i, coeff i ≠ 0) (hB : ∀ s i, B s i = coeff i*s i)
    {D : Set (Space k)} (hD : IsOpen D)
    {Q : Set (Space k)} (hQ : MeasurableSet Q) (hQD : B '' Q ⊆ D)
    (hs : ∀ s ∈ Q, ∀ i, s i ≠ 0)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈
      affineEpigraphPullback Ω u a ((B.prodCongr A).symm.trans L)})
    (hzero : ∀ s ∈ D, (0 : Space m) ∈ interior {y | (s,y) ∈
      affineEpigraphPullback Ω u a ((B.prodCongr A).symm.trans L)}) :
    let H := fun q : Space k × Space m =>
      homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let H' := fun q : Space k × Space m => homogeneousSupport {y | (q.1,y) ∈
      affineEpigraphPullback Ω u a ((B.prodCongr A).symm.trans L)} q.2
    let bS := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    (∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
      ENNReal.ofReal (tubeMeasureDensity n H bS bE (q.1,q.2)*tubeLogMassWeight H (q.1,q.2))
      ∂(volume.restrict Q).prod (volume : Measure (Space m)).toSphere) =
    (∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
      ENNReal.ofReal (tubeMeasureDensity n H' bS bE (q.1,q.2)*tubeLogMassWeight H' (q.1,q.2))
      ∂(volume.restrict (B '' Q)).prod (volume : Measure (Space m)).toSphere) := by
  let : NeZero m := ⟨by omega⟩
  let L' := (B.prodCongr A).symm.trans L
  let K := fun s : Space k => {y | (s,y) ∈ affineEpigraphPullback Ω u a L'}
  let H' := fun q : Space k × Space m => homogeneousSupport (K q.1) q.2
  have hh (s : Space k) (hsD : s ∈ D) (e : Space m) (he : e ≠ 0) :
      ContDiffAt ℝ ∞ H' (s,e) :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L' hD hK hzero hsD he).1
  have hrad (s : Space k) (hsD : s ∈ D) (e : Space m) (he : e ≠ 0) :=
    affineEpigraph_support_radial hΩ hcv hu hp a L' hD hK hzero hsD he
  have hpos (s : Space k) (hsD : s ∈ D) (e : Space m) (he : e ≠ 0) :=
    affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L' hD hK hzero hsD he
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE
  have ht := sigma_cell_linear_comp bE B (adjointEquiv A.symm) coeff hcoeff hB hD hQ hQD
    hK (fun s hs => ⟨0,interior_subset (hzero s hs)⟩) hs hh hrad
    (fun s hs e he => ⟨(hpos s hs e he).2.2,(hpos s hs e he).1.det_pos,(hpos s hs e he).2.1⟩)
  have heq : (fun q : Space k × Space m => H' (B q.1,adjointEquiv A.symm q.2)) =
      (fun q : Space k × Space m =>
        homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2) := by
    dsimp only [H',K,L']
    rw [affineEpigraphPullback_normalize]
    exact support_normalized_pullback B A _
  dsimp only at ht ⊢
  rw [heq] at ht
  simpa only [hn,H',K,L'] using ht
end NormalizedSigmaTransport


end AffineBernstein
end

end OAI
end

theorem solution : type_of% @OAI.AffineBernstein.affineEpigraph_sigma_normalization_oai := @OAI.AffineBernstein.affineEpigraph_sigma_normalization_oai
