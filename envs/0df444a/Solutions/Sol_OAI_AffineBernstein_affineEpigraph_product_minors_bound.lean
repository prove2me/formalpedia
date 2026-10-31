-- Prove2me | solution 1 for OAI.AffineBernstein.affineEpigraph_product_minors_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:54:00.548377+00:00
-- url     : https://prove2.me/submissions/8afa1de5-130e-41ec-8f14-107ae347d99a

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000

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
-- module Solutions.OAIQ22_AB.AffineBernstein_PositiveDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
theorem contDiffAt_gradient {H : E → ℝ} {e : E} (hh : ContDiffAt ℝ ∞ H e) :
    ContDiffAt ℝ ∞ (gradient H) e :=
  (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp
    e (hh.fderiv_right (by simp))

theorem inner_fderiv_gradient {H : E → ℝ} {e : E} (hh : ContDiffAt ℝ ∞ H e)
    (v w : E) : inner ℝ (fderiv ℝ (gradient H) e v) w =
      fderiv ℝ (fderiv ℝ H) e v w := by
  have hd := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.hasFDerivAt.comp
    e ((hh.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  change inner ℝ (fderiv ℝ (fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ H x)) e v) w = _
  change HasFDerivAt (fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ H x)) _ e at hd
  rw [hd.fderiv]
  simp

end
section PositiveDerivative
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Positive-definiteness of the derivative makes a map injective on a convex
set, by strict monotonicity along every segment. -/
lemma injOn_of_positive_derivative {S : Set E} (hS : Convex ℝ S) {G : E → E}
    (hG : ∀ x ∈ S, DifferentiableAt ℝ G x)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < inner ℝ (fderiv ℝ G x v) v) :
    Set.InjOn G S := by
  intro x hx y hy he
  by_contra hxy
  let v := y-x
  have hv : v ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  let γ := fun t : ℝ => x+t • v
  let f := fun t : ℝ => inner ℝ (G (γ t)) v
  have hγ (t : ℝ) : HasDerivAt γ v t := by
    simpa [γ] using ((hasDerivAt_id t).smul_const v).const_add x
  have hγS (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : γ t ∈ S :=
    hS.add_smul_sub_mem hx hy ht
  have hf (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivAt f (inner ℝ (fderiv ℝ G (γ t) v) v) t := by
    simpa [f] using ((hG (γ t) (hγS t ht)).hasFDerivAt.comp_hasDerivAt t (hγ t)).inner ℝ
      (hasDerivAt_const t v)
  have hmono : StrictMonoOn f (Icc (0:ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
    · intro t ht
      exact (hf t ht).continuousAt.continuousWithinAt
    · intro t ht
      have ht' := interior_subset ht
      rw [(hf t ht').deriv]
      exact hpos (γ t) (hγS t ht') v hv
  have hh := hmono (show (0:ℝ) ∈ Icc 0 1 by norm_num)
    (show (1:ℝ) ∈ Icc 0 1 by norm_num) (by norm_num : (0:ℝ)<1)
  have h0 : f 0 = inner ℝ (G x) v := by simp [f,γ]
  have h1 : f 1 = inner ℝ (G y) v := by simp [f,γ,v]
  rw [h0,h1,he] at hh
  exact lt_irrefl _ hh
end PositiveDerivative

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

section ConvexGradientBound
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma convex_fderiv_support {Ω : Set E} {f : E → ℝ} (hc : ConvexOn ℝ Ω f)
    {x y : E} (hx : x ∈ Ω) (hy : y ∈ Ω) (hd : DifferentiableAt ℝ f x) :
    fderiv ℝ f x (y-x) ≤ f y-f x := by
  have hh := hc.comp_affineMap (AffineMap.lineMap (k := ℝ) x y)
  have hγ : HasDerivAt (fun t : ℝ => t • (y-x)+x) (y-x) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y-x)).add_const x
  have hdf : HasDerivAt (f ∘ AffineMap.lineMap (k := ℝ) x y) (fderiv ℝ f x (y-x)) 0 := by
    have hd' : HasFDerivAt f (fderiv ℝ f x) ((0:ℝ) • (y-x)+x) := by
      simpa using hd.hasFDerivAt
    simpa only [AffineMap.lineMap_apply_module',Function.comp_def] using
      hd'.comp_hasDerivAt 0 hγ
  have h0 : (0:ℝ) ∈ AffineMap.lineMap (k := ℝ) x y ⁻¹' Ω := by simpa
  have h1 : (1:ℝ) ∈ AffineMap.lineMap (k := ℝ) x y ⁻¹' Ω := by simpa
  have hs := hh.le_slope_of_hasDerivAt h0 h1 (by norm_num) hdf
  simpa only [slope_def_field,sub_zero,div_one,Function.comp_apply,
    AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one] using hs

end ConvexGradientBound

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
theorem affineEpigraph_gauss_smooth [FiniteDimensional ℝ E] [Nontrivial E]
    {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ B) {e : E} (he : e ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : S × E =>
      gaussPoint {y | (q.1, y) ∈ affineEpigraphPullback Ω u a L} q.2) (s,e) := by
  have hℓ : InnerProductSpace.toDual ℝ E e ≠ 0 := by
    intro hz
    apply he
    exact (InnerProductSpace.toDual ℝ E).injective (hz.trans (map_zero _).symm)
  apply contDiffAt_gaussPoint_fibers
    (K := fun r => {y | (r,y) ∈ affineEpigraphPullback Ω u a L})
  apply contDiffAt_homogeneousSupport_fibers
    (K := fun r => {y | (r,y) ∈ affineEpigraphPullback Ω u a L})
  exact (affineEpigraph_support_smooth hΩ hcv hu hp a L hB hK hzero hs hℓ).1

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualAngularSupport
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gaussPoint_sublevel_equations {W : Set E} (hW : IsOpen W) {F : E → ℝ}
    (hcv : ConvexOn ℝ W F) (hF : ContDiffOn ℝ ∞ F W)
    {x₀ : E} (hx₀ : x₀ ∈ W) (hneg : F x₀ < 0)
    (hK : IsCompact {y | y ∈ W ∧ F y ≤ 0}) {e : E} (he : e ≠ 0)
    (hh : DifferentiableAt ℝ (homogeneousSupport {y | y ∈ W ∧ F y ≤ 0}) e) :
    let Y := gaussPoint {y | y ∈ W ∧ F y ≤ 0} e
    Y ∈ W ∧ F Y = 0 ∧ ∃ lam : ℝ, 0 < lam ∧
      fderiv ℝ F Y = lam • InnerProductSpace.toDual ℝ E e := by
  have hℓ : InnerProductSpace.toDual ℝ E e ≠ 0 := by
    intro hz; apply he
    exact (InnerProductSpace.toDual ℝ E).injective (hz.trans (map_zero _).symm)
  obtain ⟨z, hz, hzF, lam, hlam, hder, -, hsup⟩ :=
    exists_support_multiplier hW hcv hF hx₀ hneg hK hℓ
  have heq := gaussPoint_eq_of_max hK ⟨hz, hzF.le⟩ hsup hh
  dsimp only
  rw [heq]
  exact ⟨hz, hzF, lam, hlam, hder⟩

/- Local differential form of strict curvature duality: the Hessian of a
one-homogeneous support is positive on every nonzero tangent vector. -/

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

theorem graphMap_fderiv {Y : E → F} {x : E} (hY : DifferentiableAt ℝ Y x) (v : E) :
    fderiv ℝ (fun q => (q, Y q)) x v = (v, fderiv ℝ Y x v) := by
  have hd := (hasFDerivAt_id x).prodMk hY.hasFDerivAt
  change HasFDerivAt (fun q => (q,Y q)) _ x at hd
  rw [hd.fderiv]
  rfl

theorem graphMap_second {Y : E → F} {x : E} (hY : ContDiffAt ℝ ∞ Y x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun q => (q,Y q))) x v w =
      (0, fderiv ℝ (fderiv ℝ Y) x v w) := by
  have hX : ContDiffAt ℝ ∞ (fun q => (q,Y q)) x := contDiffAt_id.prodMk hY
  have hl := ((hX.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.clm_apply
    (hasFDerivAt_const w x)
  have hr := (hasFDerivAt_const w x).prodMk
    (((hY.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.clm_apply
      (hasFDerivAt_const w x))
  have heq : (fun q => fderiv ℝ (fun r => (r,Y r)) q w) =ᶠ[𝓝 x]
      (fun q => (w, fderiv ℝ Y q w)) := by
    filter_upwards [(hY.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)]
      with q hq
    exact graphMap_fderiv (hq.differentiableAt (by norm_num)) w
  have he := (hl.congr_of_eventuallyEq heq.symm).unique hr
  simpa using congrArg (fun L : E →L[ℝ] (E × F) => L v) he

/- Second derivative under a fixed continuous linear functional. -/
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
-- module Solutions.OAIQ22_AB.AffineBernstein_BaseConcavity
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

/- Strict curvature of the actual level hypersurface forces strict concavity
of its support value in the base variables. -/
theorem support_base_hessian_neg {F : S × E → ℝ} {Y : S → E} {s : S} {e : E} {lam : ℝ}
    (hF : ContDiffAt ℝ ∞ F (s,Y s)) (hY : ContDiffAt ℝ ∞ Y s)
    (hlevel : (fun r => F (r,Y r)) =ᶠ[𝓝 s] (fun _ => (0 : ℝ)))
    (hlam : 0 < lam)
    (hconormal : ∀ z : E, fderiv ℝ F (s,Y s) (0,z) = lam * inner ℝ e z)
    (hcurv : ∀ z : S × E, z ≠ 0 → fderiv ℝ F (s,Y s) z = 0 →
      0 < fderiv ℝ (fderiv ℝ F) (s,Y s) z z)
    {v : S} (hv : v ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun r => inner ℝ e (Y r))) s v v < 0 := by
  let X : S → S × E := fun r => (r,Y r)
  have hX : ContDiffAt ℝ ∞ X s := contDiffAt_id.prodMk hY
  let z : S × E := (v, fderiv ℝ Y s v)
  have hz : z ≠ 0 := fun hc => hv (congrArg Prod.fst hc)
  have hD : fderiv ℝ F (s,Y s) z = 0 := by
    have he := hlevel.fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ (F ∘ X) s = _ at he
    rw [fderiv_comp s (hF.differentiableAt (by simp)) (hX.differentiableAt (by simp))] at he
    have hh := congrArg (fun L : S →L[ℝ] ℝ => L v) he
    simpa only [ContinuousLinearMap.comp_apply, fderiv_const_apply, zero_apply,
      graphMap_fderiv (hY.differentiableAt (by simp)), X, z] using hh
  have hD2 := (hlevel.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  have he := congrArg (fun L : S →L[ℝ] (S →L[ℝ] ℝ) => L v v) hD2
  have hchain := second_fderiv_comp (g := X) (x := s) hF hX v v
  change fderiv ℝ (fderiv ℝ (fun r => F (r,Y r))) s v v = _ at hchain
  rw [hchain, graphMap_fderiv (hY.differentiableAt (by simp)),
    graphMap_second hY, hconormal] at he
  have hs := second_fderiv_clm_comp (InnerProductSpace.toDual ℝ E e) hY v v
  change fderiv ℝ (fderiv ℝ (fun r => inner ℝ e (Y r))) s v v =
    inner ℝ e (fderiv ℝ (fderiv ℝ Y) s v v) at hs
  have hc := hcurv z hz hD
  have hzero : fderiv ℝ (fun _ : S => (0 : ℝ)) = (fun _ => 0) :=
    funext (fun _ => fderiv_const_apply 0)
  rw [hzero, fderiv_const_apply] at he
  simp only [zero_apply] at he
  change 0 < fderiv ℝ (fderiv ℝ F) (X s) (v, fderiv ℝ Y s v) (v, fderiv ℝ Y s v) at hc
  rw [hs]
  nlinarith

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualBaseCurvature
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
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/- The genuine defining function for any affine coordinates of the graph. -/

theorem affineDefining_deriv {n : ℕ} {u : Space n → ℝ} (a : Space n × ℝ)
    (L : V ≃L[ℝ] (Space n × ℝ)) {p : V}
    (hu : ContDiffAt ℝ ∞ u (a + L p).1) (v : V) :
    fderiv ℝ (affineDefining u a L) p v =
      fderiv ℝ u (a + L p).1 (L v).1 - (L v).2 := by
  let A := (ContinuousLinearMap.fst ℝ (Space n) ℝ).comp L.toContinuousLinearMap
  let b := (ContinuousLinearMap.snd ℝ (Space n) ℝ).comp L.toContinuousLinearMap
  have hd := ((hu.differentiableAt (by simp)).hasFDerivAt.comp p
    (A.hasFDerivAt.const_add a.1)).sub (b.hasFDerivAt.const_add a.2)
  change HasFDerivAt (affineDefining u a L) _ p at hd
  rw [hd.fderiv]
  rfl

theorem affineDefining_second {n : ℕ} {u : Space n → ℝ} (a : Space n × ℝ)
    (L : V ≃L[ℝ] (Space n × ℝ)) {p : V}
    (hu : ContDiffAt ℝ ∞ u (a + L p).1) (v w : V) :
    fderiv ℝ (fderiv ℝ (affineDefining u a L)) p v w =
      fderiv ℝ (fderiv ℝ u) (a + L p).1 (L v).1 (L w).1 := by
  let A := (ContinuousLinearMap.fst ℝ (Space n) ℝ).comp L.toContinuousLinearMap
  let b := (ContinuousLinearMap.snd ℝ (Space n) ℝ).comp L.toContinuousLinearMap
  exact affineSlice_second (A := A) (b := b) (z := a.2) hu v w

/- Positive curvature on the tangent hyperplane, including affine maps that
mix the original vertical direction with the new base and fiber coordinates. -/
theorem affineDefining_tangent_curvature {n : ℕ} {u : Space n → ℝ} (a : Space n × ℝ)
    (L : V ≃L[ℝ] (Space n × ℝ)) {p : V}
    (hu : ContDiffAt ℝ ∞ u (a + L p).1) (hp : (hessian u (a + L p).1).PosDef)
    {v : V} (hv : v ≠ 0) (ht : fderiv ℝ (affineDefining u a L) p v = 0) :
    0 < fderiv ℝ (fderiv ℝ (affineDefining u a L)) p v v := by
  rw [affineDefining_deriv a L hu] at ht
  have hhor : (L v).1 ≠ 0 := by
    intro hz
    rw [hz, map_zero, zero_sub, neg_eq_zero] at ht
    apply hv
    apply L.injective
    exact (Prod.ext hz ht).trans (map_zero L).symm
  rw [affineDefining_second a L hu]
  exact second_fderiv_pos hu hp hhor

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- The actual support point is on the original graph and its fiber conormal is
positive. No Gauss inverse or support-equation hypotheses are assumed. -/
theorem affineEpigraph_gauss_equations [FiniteDimensional ℝ E] [Nontrivial E]
    {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ B) {e : E} (he : e ≠ 0) :
    let Y := gaussPoint {y | (s,y) ∈ affineEpigraphPullback Ω u a L} e
    (a + L (s,Y)).1 ∈ Ω ∧ affineDefining u a L (s,Y) = 0 ∧
      ∃ lam : ℝ, 0 < lam ∧ fderiv ℝ (fun y => affineDefining u a L (s,y)) Y =
        lam • InnerProductSpace.toDual ℝ E e := by
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

  have hℓ : InnerProductSpace.toDual ℝ E e ≠ 0 := by
    intro hz; apply he
    exact (InnerProductSpace.toDual ℝ E).injective (hz.trans (map_zero _).symm)
  have hsupp := contDiffAt_homogeneousSupport_fibers
    (K := fun r => {y | (r,y) ∈ affineEpigraphPullback Ω u a L})
    (affineEpigraph_support_smooth hΩ hcv hu hp a L hB hK hzero hs hℓ).1
  have hh : ContDiffAt ℝ ∞ (homogeneousSupport
      {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) e :=
    hsupp.comp e (contDiffAt_const.prodMk contDiffAt_id)
  have hh' : ContDiffAt ℝ ∞ (homogeneousSupport {y | (s,y) ∈ W ∧ F (s,y) ≤ 0}) e := by
    rw [hKeq]; exact hh
  have hresult := gaussPoint_sublevel_equations
    (W := {y | (s,y) ∈ W}) (F := fun y => F (s,y))
    (hW.preimage (by fun_prop)) (hcvF s)
    (hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h))
    hzW hzF hK' he (hh'.differentiableAt (by simp))
  simp only [mem_ofPred_eq] at hresult
  rw [hKeq] at hresult
  exact hresult

/- Strict negativity of the base Hessian of the literal support function. This
is the other positive block of the genuine tube second fundamental form. -/
theorem affineEpigraph_base_hessian_negative [FiniteDimensional ℝ E] [Nontrivial E]
    {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ B) {e : E} (he : e ≠ 0) {v : S} (hv : v ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun r => homogeneousSupport
      {y | (r,y) ∈ affineEpigraphPullback Ω u a L} e)) s v v < 0 := by
  let K : S → Set E := fun r => {y | (r,y) ∈ affineEpigraphPullback Ω u a L}
  let Y : S → E := fun r => gaussPoint (K r) e
  let F := affineDefining u a L
  have hY : ContDiffAt ℝ ∞ Y s :=
    (affineEpigraph_gauss_smooth hΩ hcv hu hp a L hB hK hzero hs he).comp
      (f := fun r : S => (r,e)) s (contDiffAt_id.prodMk contDiffAt_const)
  obtain ⟨hbase, hlevel0, lam, hlam, hnorm⟩ :=
    affineEpigraph_gauss_equations hΩ hcv hu hp a L hB hK hzero hs he
  change (a + L (s,Y s)).1 ∈ Ω at hbase
  have huc := hu.contDiffAt (hΩ.mem_nhds hbase)
  have hF : ContDiffAt ℝ ∞ F (s,Y s) :=
    (huc.comp (s,Y s) ((contDiffAt_const.add L.contDiff.contDiffAt).fst)).sub
      ((contDiffAt_const.add L.contDiff.contDiffAt).snd)
  have hlevel : (fun r => F (r,Y r)) =ᶠ[𝓝 s] (fun _ => 0) := by
    filter_upwards [hB.mem_nhds hs] with r hr
    exact (affineEpigraph_gauss_equations hΩ hcv hu hp a L hB hK hzero hr he).2.1
  have hnormal (z : E) : fderiv ℝ F (s,Y s) (0,z) = lam * inner ℝ e z := by
    have hd := (hF.differentiableAt (by simp)).hasFDerivAt.comp (Y s)
      ((hasFDerivAt_const s (Y s)).prodMk (hasFDerivAt_id (Y s)))
    have hh := congrArg (fun A : E →L[ℝ] ℝ => A z) hnorm
    change fderiv ℝ (F ∘ Prod.mk s) (Y s) z = _ at hh
    rw [hd.fderiv] at hh
    exact hh
  have hneg := support_base_hessian_neg hF hY hlevel hlam hnormal
    (fun z hz ht => affineDefining_tangent_curvature a L huc (hp _ hbase) hz ht) hv
  have heq : (fun r => homogeneousSupport (K r) e) =ᶠ[𝓝 s]
      (fun r => inner ℝ e (Y r)) := by
    filter_upwards [hB.mem_nhds hs] with r hr
    have hℓ : InnerProductSpace.toDual ℝ E e ≠ 0 := by
      intro hz; apply he
      exact (InnerProductSpace.toDual ℝ E).injective (hz.trans (map_zero _).symm)
    have hsup := contDiffAt_homogeneousSupport_fibers
      (K := K) (affineEpigraph_support_smooth hΩ hcv hu hp a L hB hK hzero hr hℓ).1
    have hd : DifferentiableAt ℝ (homogeneousSupport (K r)) e :=
      (hsup.comp e (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    exact (gaussPoint_mem_support (hK r hr) ⟨0, interior_subset (hzero r hr)⟩ hd).2
  rw [(heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]
  exact hneg

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

lemma second_fderiv_prod_left {H : S × E → ℝ} {s : S} {e : E}
    (hH : ContDiffAt ℝ ∞ H (s,e)) (v w : S) :
    fderiv ℝ (fderiv ℝ (fun y => H (y,e))) s v w =
      fderiv ℝ (fderiv ℝ H) (s,e) (v,0) (w,0) := by
  simpa using second_fderiv_affine_comp (ContinuousLinearMap.inl ℝ S E) (0,e) (by simpa using hH) v w

lemma bilinear_matrix_posDef {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : F →L[ℝ] F →L[ℝ] ℝ) (b : ι → F)
    (hb : LinearIndependent ℝ b) (hsym : ∀ v w, A v w = A w v)
    (hp : ∀ z : ι → ℝ, (∑ i, z i • b i) ≠ 0 →
      0 < A (∑ i, z i • b i) (∑ i, z i • b i)) :
    (Matrix.of fun i j => A (b i) (b j)).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, fun z hz => ?_⟩
  · rw [Matrix.IsHermitian]
    ext i j
    simpa [Matrix.conjTranspose_apply] using hsym (b j) (b i)
  · have hne : (∑ i, z i • b i) ≠ 0 := by
      intro he
      apply hz
      funext i
      exact (Fintype.linearIndependent_iff.mp hb z he) i
    have h := hp z hne
    simpa [dotProduct, Matrix.mulVec, map_sum, map_smul, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm, hsym] using h

lemma tubeBaseMatrix_posDef {H : S × E → ℝ} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (bS : Module.Basis ι ℝ S)
    (hneg : ∀ v : S, v ≠ 0 → fderiv ℝ (fderiv ℝ H) x (v,0) (v,0) < 0) :
    (tubeBaseMatrix H x bS).PosDef := by
  let A := -(fderiv ℝ (fderiv ℝ H) x)
  have hb : LinearIndependent ℝ (fun i => (bS i, (0:E))) :=
    bS.linearIndependent.map' (ContinuousLinearMap.inl ℝ S E).toLinearMap (by
      apply LinearMap.ker_eq_bot.mpr
      intro x y h; exact congrArg Prod.fst h)
  have hs := hH.isSymmSndFDerivAt (by simp)
  apply bilinear_matrix_posDef A _ hb (fun v w => by simp [A,hs.eq v w])
  intro z hz
  have he : (∑ i, z i • (bS i,(0:E))) = ((∑ i, z i • bS i),0) := by
    apply Prod.ext <;> simp [Prod.fst_sum, Prod.snd_sum]
  rw [he] at hz ⊢
  have hn : (∑ i, z i • bS i) ≠ 0 := by simpa using hz
  exact neg_pos.mpr (hneg _ hn)

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
-- module Solutions.OAIQ22_AB.AffineBernstein_MatrixShiftBound
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

private lemma adjugate_eq_det_smul_transpose' {Q : Matrix ι ι ℝ} (hQ : Q * Qᵀ = 1) :
    Q.adjugate = Q.det • Qᵀ := by
  calc
    Q.adjugate = Q.adjugate * (Q * Qᵀ) := by rw [hQ, Matrix.mul_one]
    _ = (Q.adjugate * Q) * Qᵀ := (Matrix.mul_assoc _ _ _).symm
    _ = Q.det • Qᵀ := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]

private lemma adjugate_conjugate_orthogonal' {Q : Matrix ι ι ℝ}
    (hQ : Q * Qᵀ = 1) (hQt : Qᵀ * Q = 1) (A : Matrix ι ι ℝ) :
    (Qᵀ * A * Q).adjugate = Qᵀ * A.adjugate * Q := by
  have hd : Q.det * Q.det = 1 := by
    have hh := congrArg Matrix.det hQ
    simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] using hh
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
    adjugate_eq_det_smul_transpose' hQ,
    adjugate_eq_det_smul_transpose' (Q := Qᵀ) (by simpa using hQt),
    Matrix.transpose_transpose, Matrix.det_transpose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hd, one_smul, Matrix.mul_assoc]

/- A coarse uniform bound for the sum of all principal cofactors by the
Jacobian of the identity-shifted positive semidefinite map. -/
lemma trace_adjugate_le_card_mul_det_add_one {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) :
    A.adjugate.trace ≤ (Fintype.card ι : ℝ) * (A + 1).det := by
  let Q : Matrix ι ι ℝ := hA.1.eigenvectorUnitary
  let d : ι → ℝ := hA.1.eigenvalues
  have hQ : Q * Qᵀ = 1 := by
    simpa only [Q, Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using (Unitary.coe_mul_star_self hA.1.eigenvectorUnitary)
  have hQt : Qᵀ * Q = 1 := by
    simpa only [Q, Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using (Unitary.coe_star_mul_self hA.1.eigenvectorUnitary)
  have hspec : A = Q * Matrix.diagonal d * Qᵀ := by
    simpa [Q,d,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hA.1.spectral_theorem
  have hdetQ : Q.det * Q.det = 1 := by
    have hh := congrArg Matrix.det hQ
    simpa only [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one] using hh
  have htrace : A.adjugate.trace = ∑ i, ∏ j ∈ Finset.univ.erase i, d j := by
    rw [hspec]
    have had := adjugate_conjugate_orthogonal' (Q := Qᵀ) (by simpa using hQt) (by simpa using hQ) (Matrix.diagonal d)
    simp only [Matrix.transpose_transpose] at had
    rw [had]
    rw [Matrix.trace_mul_cycle,hQt,Matrix.one_mul,Matrix.adjugate_diagonal,Matrix.trace_diagonal]
  have hdet : (A + 1).det = ∏ i, (d i + 1) := by
    have hsum : A + 1 = Q * Matrix.diagonal (fun i => d i + 1) * Qᵀ := by
      have hdadd : Matrix.diagonal (fun i => d i + 1) = Matrix.diagonal d + 1 := by
        ext i j
        by_cases hij : i = j <;> simp [Matrix.diagonal,hij]
      rw [hdadd,Matrix.mul_add,Matrix.add_mul,Matrix.mul_one,← hspec,hQ]
    rw [hsum,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,Matrix.det_diagonal]
    calc
      Q.det * (∏ i, (d i + 1)) * Q.det = (Q.det * Q.det) * ∏ i, (d i + 1) := by ring
      _ = _ := by rw [hdetQ,one_mul]
  rw [htrace,hdet]
  calc
    (∑ i, ∏ j ∈ Finset.univ.erase i, d j) ≤ ∑ _i : ι, ∏ j, (d j + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        (∏ j ∈ Finset.univ.erase i, d j) ≤ ∏ j ∈ Finset.univ.erase i, (d j + 1) := by
          exact Finset.prod_le_prod (fun index _ => hA.eigenvalues_nonneg index)
            (fun _ _ => by linarith)
        _ ≤ (d i + 1) * ∏ j ∈ Finset.univ.erase i, (d j + 1) := by
          have hp := Finset.prod_nonneg (s := Finset.univ.erase i)
            (fun j _ => add_nonneg (hA.eigenvalues_nonneg j) zero_le_one)
          nlinarith [hA.eigenvalues_nonneg i]
        _ = ∏ j, (d j + 1) := Finset.mul_prod_erase Finset.univ (fun j => d j + 1) (Finset.mem_univ i)
    _ = _ := by simp

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_MatrixShiftDet
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

lemma det_le_det_add_one {A : Matrix ι ι ℝ} (hA : A.PosSemidef) : A.det ≤ (A+1).det := by
  let Q : Matrix ι ι ℝ := hA.1.eigenvectorUnitary
  let d : ι → ℝ := hA.1.eigenvalues
  have hQ : Q*Qᵀ = 1 := by
    simpa only [Q,Unitary.coe_star,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Unitary.coe_mul_star_self hA.1.eigenvectorUnitary)
  have hspec : A = Q * Matrix.diagonal d * Qᵀ := by
    simpa [Q,d,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hA.1.spectral_theorem
  have hdetQ : Q.det * Q.det = 1 := by
    have hh := congrArg Matrix.det hQ
    simpa only [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one] using hh
  have hsum : A+1 = Q * Matrix.diagonal (fun i => d i+1) * Qᵀ := by
    have he : Matrix.diagonal (fun i => d i+1) = Matrix.diagonal d+1 := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal,hij]
    rw [he,Matrix.mul_add,Matrix.add_mul,Matrix.mul_one,← hspec,hQ]
  rw [hsum,hspec,Matrix.det_mul,Matrix.det_mul,Matrix.det_mul,Matrix.det_mul,
    Matrix.det_transpose,Matrix.det_diagonal,Matrix.det_diagonal]
  have he (a : ℝ) : Q.det * a * Q.det = a := by
    calc
      _ = (Q.det*Q.det)*a := by ring
      _ = a := by rw [hdetQ,one_mul]
  rw [he,he]
  exact Finset.prod_le_prod (fun index _ => hA.eigenvalues_nonneg index)
    (fun _ _ => by linarith)

lemma det_mul_one_add_trace_inv_le {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    A.det * (1 + A⁻¹.trace) ≤ ((Fintype.card ι:ℝ)+1)*(A+1).det := by
  have hne := hA.det_pos.ne'
  have he : A.det * A⁻¹.trace = A.adjugate.trace := by
    rw [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.trace_smul,
      smul_eq_mul,← mul_assoc,mul_inv_cancel₀ hne,one_mul]
  rw [mul_add,mul_one,he]
  have h1 := det_le_det_add_one hA.posSemidef
  have h2 := trace_adjugate_le_card_mul_det_add_one hA.posSemidef
  linarith

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SupportAnnulus
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

variable {n : ℕ}

lemma toMatrix_fderiv_gradient_eq_hessian_transpose {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (fderiv ℝ (gradient u) x).toLinearMap =
      (hessian u x).transpose := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change (OrthonormalBasis.repr (EuclideanSpace.basisFun (Fin n) ℝ)
    (fderiv ℝ (gradient u) x ((EuclideanSpace.basisFun (Fin n) ℝ) j))) i = _
  rw [OrthonormalBasis.repr_apply_apply,real_inner_comm,
    inner_fderiv_gradient hu,EuclideanSpace.basisFun_apply,EuclideanSpace.basisFun_apply]
  exact (hessian_eq_second hu j i).symm

lemma det_fderiv_shiftedGradient {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) :
    (fderiv ℝ (fun x => gradient u x + x) x).det = (hessian u x + 1).det := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have he : (fderiv ℝ (fun x => gradient u x + x) x).toLinearMap =
      (fderiv ℝ (gradient u) x).toLinearMap + LinearMap.id := by
    change (fderiv ℝ (fun y => gradient u y + id y) x).toLinearMap = _
    rw [fderiv_fun_add ((contDiffAt_gradient hu).differentiableAt (by simp)) differentiableAt_id,
      fderiv_id]
    rfl
  rw [ContinuousLinearMap.det,← LinearMap.det_toMatrix b,he,map_add,
    toMatrix_fderiv_gradient_eq_hessian_transpose hu,LinearMap.toMatrix_id]
  have ht : (hessian u x).transpose + (1 : Matrix (Fin n) (Fin n) ℝ) =
      (hessian u x + 1).transpose := by
    ext i j
    simp only [Matrix.add_apply,Matrix.transpose_apply,Matrix.one_apply]
    by_cases hij : i = j <;> simp [hij,Ne.symm]
  rw [ht,Matrix.det_transpose]

/- On any bounded measurable annular set, the cofactor trace of the literal
support Hessian has a bound depending only on the radius of the convex fiber.
The proof uses the injective shifted Gauss map and genuine change of variables. -/

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_HessianMinors
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

variable {n : ℕ}

lemma shiftedGradient_injOn_of_hessian_posSemidef {Ω : Set (Space n)}
    (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ∀ x ∈ Ω, ContDiffAt ℝ ∞ u x)
    (hp : ∀ x ∈ Ω, (hessian u x).PosSemidef) :
    Set.InjOn (fun x => gradient u x + x) Ω := by
  apply injOn_of_positive_derivative hcv
  · intro x hx
    exact ((contDiffAt_gradient (hu x hx)).differentiableAt (by simp)).add differentiableAt_id
  · intro x hx v hv
    change 0 < inner ℝ (fderiv ℝ (fun y => gradient u y + id y) x v) v
    rw [fderiv_fun_add ((contDiffAt_gradient (hu x hx)).differentiableAt (by simp))
      differentiableAt_id,fderiv_id]
    simp only [add_apply,ContinuousLinearMap.id_apply,inner_add_left,
      inner_fderiv_gradient (hu x hx)]
    exact add_pos_of_nonneg_of_pos (second_fderiv_nonneg (hu x hx) (hp x hx) v)
      (real_inner_self_pos.mpr hv)

/- One genuine change of variables for the shifted convex gradient bounds
all the large principal minors at once. This is an alternative proof of the
source principal-minor estimate, with every quantity the actual Hessian.
It does not posit any Hessian or determinant bound. -/
theorem lintegral_hessian_minors_le_ball {Ω : Set (Space n)}
    (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ∀ x ∈ Ω, ContDiffAt ℝ ∞ u x)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {D : Set (Space n)} (hD : MeasurableSet D) (hDO : D ⊆ Ω)
    {G R : ℝ} (hG : ∀ x ∈ D, ‖gradient u x‖ ≤ G)
    (hR : ∀ x ∈ D, ‖x‖ ≤ R) :
    (∫⁻ x in D, ENNReal.ofReal ((hessian u x).det * (1 + (hessian u x)⁻¹.trace))) ≤
      ((n:ℝ≥0∞)+1) * volume (Metric.closedBall (0:Space n) (G+R)) := by
  let F := fun x => gradient u x + x
  have hd (x : Space n) (hx : x ∈ D) : DifferentiableAt ℝ F x :=
    ((contDiffAt_gradient (hu x (hDO hx))).differentiableAt (by simp)).add differentiableAt_id
  have hi : Set.InjOn F D :=
    (shiftedGradient_injOn_of_hessian_posSemidef hcv hu (fun x hx => (hp x hx).posSemidef)).mono hDO
  have hj := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hD
    (fun x hx => (hd x hx).hasFDerivAt.hasFDerivWithinAt) hi (fun _ : Space n => (1:ℝ≥0∞))
  simp only [lintegral_const,Measure.restrict_apply_univ,mul_one,one_mul] at hj
  have himage : F '' D ⊆ Metric.closedBall 0 (G+R) := by
    rintro _ ⟨x,hx,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (norm_add_le _ _).trans (add_le_add (hG x hx) (hR x hx))
  calc
    _ ≤ ∫⁻ x in D, ((n:ℝ≥0∞)+1)*ENNReal.ofReal |(fderiv ℝ F x).det| := by
      apply setLIntegral_mono' hD
      intro x hx
      have hp' := hp x (hDO hx)
      have hdpos := (hp'.posSemidef.add Matrix.PosSemidef.one).det_nonneg
      rw [show F = (fun x => gradient u x+x) from rfl,
        det_fderiv_shiftedGradient (hu x (hDO hx)),abs_of_nonneg hdpos]
      have hc : ((n:ℝ≥0∞)+1) = ENNReal.ofReal ((n:ℝ)+1) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
        simp
      rw [hc,← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      simpa only [Fintype.card_fin] using det_mul_one_add_trace_inv_le hp'
    _ = ((n:ℝ≥0∞)+1) * ∫⁻ x in D, ENNReal.ofReal |(fderiv ℝ F x).det| := by
      rw [lintegral_const_mul']
      simp
    _ ≤ _ := by
      rw [← hj]
      exact mul_le_mul_right (measure_mono (μ := volume) himage) _

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

section ConvexGradientBound
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- A bounded convex function on a full larger ball has bounded actual
Euclidean gradient at its center. No derivative estimate is assumed. -/
lemma norm_gradient_le_of_convex_bounded {Ω : Set E} {f : E → ℝ}
    (hc : ConvexOn ℝ Ω f) {x : E} (hx : x ∈ Ω) (hd : DifferentiableAt ℝ f x)
    {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hball : Metric.closedBall x r ⊆ Ω) (hb : ∀ y ∈ Ω, |f y| ≤ M) :
    ‖gradient f x‖ ≤ 2*M/r := by
  by_cases hg : gradient f x = 0
  · simp only [hg,norm_zero]
    positivity
  have hgp : 0 < ‖gradient f x‖ := norm_pos_iff.mpr hg
  let y := x + (r/‖gradient f x‖) • gradient f x
  have hdist : dist y x = r := by
    rw [dist_eq_norm]
    dsimp [y]
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hr hgp),
      div_mul_cancel₀ _ hgp.ne']
  have hy : y ∈ Ω := hball (by rw [Metric.mem_closedBall,hdist])
  have hs := convex_fderiv_support hc hx hy hd
  have he : fderiv ℝ f x (y-x) = r*‖gradient f x‖ := by
    dsimp [y]
    rw [add_sub_cancel_left,map_smul,smul_eq_mul,← inner_gradient_left,
      real_inner_self_eq_norm_sq]
    field_simp
  rw [he] at hs
  have hfx := (abs_le.mp (hb x hx)).1
  have hfy := (abs_le.mp (hb y hy)).2
  apply (le_div_iff₀ hr).mpr
  nlinarith

end ConvexGradientBound
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]

lemma hessian_neg {k : ℕ} (f : Space k → ℝ) (x : Space k) :
    hessian (fun y => -f y) x = -hessian f x := by
  ext i j
  simp only [hessian,fderiv_fun_neg,neg_apply,Matrix.neg_apply]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma tubeBaseMatrix_basisFun {k : ℕ} {H : Space k × E → ℝ}
    {s : Space k} {e : E} (hH : ContDiffAt ℝ ∞ H (s,e)) :
    tubeBaseMatrix H (s,e) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis =
      hessian (fun x => -H (x,e)) s := by
  have hh : ContDiffAt ℝ ∞ (fun x => H (x,e)) s :=
    hH.comp s (contDiffAt_id.prodMk contDiffAt_const)
  rw [hessian_neg]
  ext i j
  simp only [tubeBaseMatrix,Matrix.of_apply,Matrix.neg_apply]
  rw [hessian_eq_second hh,second_fderiv_prod_left hH]
  simp only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,coordinateVector]

/- The uniform large-principal-minor bound for the actual negative support
of an affine epigraph. The larger base domain supplies the gradient bound;
hence no derivative or determinant bound is added as a hypothesis. -/
theorem affineEpigraph_base_minors_bound {n k : ℕ}
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (Space k × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set (Space k)} (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {e : E} (he : e ≠ 0) {Q : Set (Space k)} (hQ : MeasurableSet Q) (hQD : Q ⊆ D)
    {r M R : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hball : ∀ s ∈ Q, Metric.closedBall s r ⊆ D)
    (hbound : ∀ s ∈ D,
      |homogeneousSupport {y | (s,y) ∈ affineEpigraphPullback Ω u a L} e| ≤ M)
    (hR : ∀ s ∈ Q, ‖s‖ ≤ R) :
    let H := fun q : Space k × E =>
      homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let B := fun s => tubeBaseMatrix H (s,e) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    (∫⁻ s in Q, ENNReal.ofReal ((B s).det * (1 + (B s)⁻¹.trace))) ≤
      ((k:ℝ≥0∞)+1) * volume (Metric.closedBall (0:Space k) (2*M/r+R)) := by
  let H := fun q : Space k × E =>
    homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let f : Space k → ℝ := fun s => -H (s,e)
  have hh (s : Space k) (hs : s ∈ D) : ContDiffAt ℝ ∞ H (s,e) :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs he).1
  have hf (s : Space k) (hs : s ∈ D) : ContDiffAt ℝ ∞ f s :=
    ((hh s hs).comp s (contDiffAt_id.prodMk contDiffAt_const)).neg
  have hpf (s : Space k) (hs : s ∈ D) : (hessian f s).PosDef := by
    rw [← tubeBaseMatrix_basisFun (hh s hs)]
    apply tubeBaseMatrix_posDef (hh s hs)
    intro v hv
    rw [← second_fderiv_prod_left (hh s hs)]
    exact affineEpigraph_base_hessian_negative hΩ hcv hu hp a L hD hK hzero hs he hv
  have hfD : ContDiffOn ℝ ∞ f D := fun s hs => (hf s hs).contDiffWithinAt
  have hcf := convexOn_of_hessian_posSemidef hD hcD hfD (fun s hs => (hpf s hs).posSemidef)
  have hg (s : Space k) (hs : s ∈ Q) : ‖gradient f s‖ ≤ 2*M/r := by
    apply norm_gradient_le_of_convex_bounded hcf (hQD hs)
      ((hf s (hQD hs)).differentiableAt (by simp)) hr hM (hball s hs)
    intro x hx
    simpa only [f,abs_neg] using hbound x hx
  have hb := lintegral_hessian_minors_le_ball hcD hf hpf hQ hQD hg hR
  change (∫⁻ s in Q, ENNReal.ofReal
    ((tubeBaseMatrix H (s,e) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det *
      (1+(tubeBaseMatrix H (s,e) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)⁻¹.trace))) ≤ _
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  apply setLIntegral_congr_fun hQ
  intro s hs
  dsimp only
  rw [tubeBaseMatrix_basisFun (hh s (hQD hs))]

/- A compact fiber radius controls the literal support function in all unit
normal directions. -/
omit [FiniteDimensional ℝ E] [Nontrivial E] in
lemma homogeneousSupport_abs_le_of_radius {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) {e : E} (he : ‖e‖ = 1) {M : ℝ}
    (hM : ∀ y ∈ K, ‖y‖ ≤ M) : |homogeneousSupport K e| ≤ M := by
  obtain ⟨y,hy,hmax⟩ := hK.exists_isMaxOn hne
    (InnerProductSpace.toDual ℝ E e).continuous.continuousOn
  rw [homogeneousSupport_eq_of_max hy hmax]
  exact (abs_real_inner_le_norm e y).trans (by simpa only [he,one_mul] using hM y hy)

theorem affineEpigraph_base_minors_of_fiber_radius {n k : ℕ}
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (Space k × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set (Space k)} (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {e : E} (he : ‖e‖ = 1) {Q : Set (Space k)} (hQ : MeasurableSet Q) (hQD : Q ⊆ D)
    {r M R : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hball : ∀ s ∈ Q, Metric.closedBall s r ⊆ D)
    (hbound : ∀ s ∈ D, ∀ y : E, (s,y) ∈ affineEpigraphPullback Ω u a L → ‖y‖ ≤ M)
    (hR : ∀ s ∈ Q, ‖s‖ ≤ R) :
    let H := fun q : Space k × E =>
      homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let B := fun s => tubeBaseMatrix H (s,e) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    (∫⁻ s in Q, ENNReal.ofReal ((B s).det * (1 + (B s)⁻¹.trace))) ≤
      ((k:ℝ≥0∞)+1) * volume (Metric.closedBall (0:Space k) (2*M/r+R)) := by
  have he0 : e ≠ 0 := fun h => by simp [h] at he
  apply affineEpigraph_base_minors_bound hΩ hcv hu hp a L hD hcD hK hzero he0 hQ hQD hr hM hball
  · intro s hs
    exact homogeneousSupport_abs_le_of_radius (hK s hs)
      ⟨0,interior_subset (hzero s hs)⟩ he (hbound s hs)
  · exact hR

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualProductBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open scoped Matrix

/- Integrating the actual large-principal-minor bound over all unit fiber
normals. This is the product-measure bound in bounds.tex (hessian-minor-bound),
including base dimension zero. No polynomial determinant bound is assumed. -/
theorem affineEpigraph_product_minors_bound_oai {n k m : ℕ} (hm : 1 ≤ m)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
    {D : Set (Space k)} (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0:Space m) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {Q : Set (Space k)} (hQ : MeasurableSet Q) (hQD : Q ⊆ D)
    {r M R : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hball : ∀ s ∈ Q, Metric.closedBall s r ⊆ D)
    (hbound : ∀ s ∈ D, ∀ y : Space m, (s,y) ∈ affineEpigraphPullback Ω u a L → ‖y‖ ≤ M)
    (hR : ∀ s ∈ Q, ‖s‖ ≤ R) :
    let H := fun q : Space k × Space m =>
      homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let B := fun q : Space k × Metric.sphere (0:Space m) 1 =>
      tubeBaseMatrix H (q.1,q.2) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    (∫⁻ q, ENNReal.ofReal ((B q).det * (1+(B q)⁻¹.trace))
      ∂(volume.restrict Q).prod (volume : Measure (Space m)).toSphere) ≤
      (((k:ℝ≥0∞)+1) * volume (Metric.closedBall (0:Space k) (2*M/r+R))) *
        (volume : Measure (Space m)).toSphere Set.univ := by
  let : NeZero m := ⟨by omega⟩
  let H := fun q : Space k × Space m =>
    homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let f := fun q : Space k × Metric.sphere (0:Space m) 1 => ENNReal.ofReal
    ((tubeBaseMatrix H (q.1,q.2) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det *
      (1+(tubeBaseMatrix H (q.1,q.2) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)⁻¹.trace))
  let ν : Measure (Metric.sphere (0:Space m) 1) := volume.toSphere
  let C : ℝ≥0∞ := ((k:ℝ≥0∞)+1) * volume (Metric.closedBall (0:Space k) (2*M/r+R))
  change (∫⁻ q, f q ∂(volume.restrict Q).prod ν) ≤ C * ν Set.univ
  calc
    _ = ∫⁻ q, f q.swap ∂ν.prod (volume.restrict Q) := (lintegral_prod_swap f).symm
    _ ≤ ∫⁻ e, (∫⁻ s in Q, f (s,e)) ∂ν := lintegral_prod_le _
    _ ≤ ∫⁻ _e, C ∂ν := by
      apply lintegral_mono
      intro e
      have he : ‖(e : Space m)‖ = 1 := by
        simpa only [Metric.mem_sphere,dist_zero_right] using e.property
      exact affineEpigraph_base_minors_of_fiber_radius hΩ hcv hu hp a L hD hcD hK hzero
        (e := (e : Space m)) he hQ hQD hr hM hball hbound hR
    _ = _ := by simp

/- The literal fiber cofactor density integrated over a bounded base set.
The transverse dimension-one endpoint is retained. -/
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

end AffineBernstein

end

end OAI
end

theorem solution : type_of% @OAI.AffineBernstein.affineEpigraph_product_minors_bound_oai := @OAI.AffineBernstein.affineEpigraph_product_minors_bound_oai
