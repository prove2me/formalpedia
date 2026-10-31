-- Prove2me | solution 1 for OAI.AffineBernstein.affineMaximal_flat_tube_weak_euler
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:01:21.953485+00:00
-- url     : https://prove2.me/submissions/01a4e0da-0c52-4e87-ad70-a81d57b9f533

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_flat_tube_positive
import Theorems.Thm_OAI_AffineBernstein_affineMaximal_flatSupport_local_stationary

section
-- module Solutions.OAIQ22_AB.AffineBernstein_PiolaAlgebra
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

/-- Expand one determinant row in the coordinate vectors. -/
theorem det_updateRow_sum (A : Matrix ι ι ℝ) (l : ι) (v : ι → ℝ) :
    (A.updateRow l v).det = ∑ m, v m * (A.updateRow l (Pi.single m 1)).det := by
  have hv : v = ∑ m, v m • Pi.single m (1 : ℝ) := by
    ext k
    simp [Pi.single_apply, Finset.sum_apply]
  calc
    (A.updateRow l v).det =
        ∑ m, (A.updateRow l (v m • Pi.single m 1)).det := by
      conv_lhs => rw [hv]
      exact (Matrix.detRowAlternating : (ι → ℝ) [⋀^ι]→ₗ[ℝ] ℝ).map_update_sum
        Finset.univ l (fun m => v m • Pi.single m (1 : ℝ)) (fun k => A k)
    _ = _ := Finset.sum_congr rfl fun m _ => Matrix.det_updateRow_smul A l (v m) _

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

section DeterminantVariation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Jacobi's formula without assuming invertibility of the varied matrix. -/
theorem hasDerivAt_det_line (A B : Matrix ι ι ℝ) :
    HasDerivAt (fun t : ℝ => (A + t • B).det)
      (∑ i, ∑ j, A.adjugate j i * B i j) 0 := by
  have hline := ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const (fun i j => B i j)).const_add
    (fun i j => A i j)
  have hc := (((continuousDetRows (ι := ι)).hasFDerivAt
    ((fun i j => A i j) + (0 : ℝ) • (fun i j => B i j))).comp 0 hline).hasDerivAt
  simp only [zero_smul, add_zero, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, one_smul] at hc
  have hd : continuousDetRows.linearDeriv (fun i j => A i j) (fun i j => B i j) =
      ∑ i, ∑ j, A.adjugate j i * B i j := by
    rw [ContinuousMultilinearMap.linearDeriv_apply]
    apply Finset.sum_congr rfl
    intro i hi
    change (A.updateRow i (B i)).det = _
    rw [det_updateRow_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Matrix.adjugate_apply, mul_comm]
  rw [hd] at hc
  exact hc

/-- Pointwise first variation of the actual affine-area density. -/
theorem hasDerivAt_affineArea_matrix (A B : Matrix ι ι ℝ) (hA : A.PosDef) (δ : ℝ) :
    HasDerivAt (fun t : ℝ => Real.rpow (A + t • B).det δ)
      (δ * Real.rpow A.det (δ - 1) * (∑ i, ∑ j, A.adjugate j i * B i j)) 0 := by
  have hd := (hasDerivAt_det_line A B).rpow_const (p := δ) (Or.inl (by simpa using ne_of_gt hA.det_pos))
  simp only [zero_smul, add_zero] at hd
  simp only [Real.rpow_eq_pow]
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  ring

end DeterminantVariation

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
-- module Solutions.OAIQ22_AB.AffineBernstein_CompactDifferentiation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {μ : Measure E} [IsLocallyFiniteMeasure μ]

/- Differentiation over a fixed compact set from smoothness in a neighbourhood
of the zero-parameter slice. The uniform bound is obtained by compactness. -/
theorem hasDerivAt_setIntegral_compact {K : Set E} (hK : IsCompact K)
    {U : Set (ℝ × E)} (hU : IsOpen U) (h0K : {0} ×ˢ K ⊆ U)
    {F : ℝ × E → ℝ} (hF : ContDiffOn ℝ ∞ F U) :
    HasDerivAt (fun t : ℝ => ∫ x in K, F (t,x) ∂μ)
      (∫ x in K, fderiv ℝ F (0,x) (1,0) ∂μ) 0 := by
  obtain ⟨V,W,hV,hW,h0V,hKW,hVW⟩ := generalized_tube_lemma isCompact_singleton hK hU h0K
  have hv : V ∈ nhds (0 : ℝ) := hV.mem_nhds (h0V (by simp))
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp hv
  let I : Set ℝ := Icc (-ε / 2) (ε / 2)
  have hIV : I ⊆ V := by
    intro t ht
    apply hεV
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt]
    exact ⟨by dsimp [I] at ht; linarith [ht.1], by dsimp [I] at ht; linarith [ht.2]⟩
  have hIU : I ×ˢ K ⊆ U := fun p hp => hVW ⟨hIV hp.1, hKW hp.2⟩
  have hI0 : (0 : ℝ) ∈ I := by
    change -ε / 2 ≤ 0 ∧ 0 ≤ ε / 2
    constructor <;> linarith
  have hIn : I ∈ nhds (0 : ℝ) := Icc_mem_nhds (by linarith) (by linarith)
  let D : ℝ × E → ℝ := fun p => fderiv ℝ F p (1,0)
  have hDc : ContinuousOn D U := by
    intro p hp
    exact (((hF.contDiffAt (hU.mem_nhds hp)).continuousAt_fderiv (by simp)).clm_apply
      continuousAt_const).continuousWithinAt
  have hFt (t : ℝ) (ht : t ∈ I) : ContinuousOn (fun x => F (t,x)) K :=
    hF.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => hIU ⟨ht,hx⟩)
  have hDt (t : ℝ) (ht : t ∈ I) : ContinuousOn (fun x => D (t,x)) K :=
    hDc.comp (continuous_const.prodMk continuous_id).continuousOn (fun x hx => hIU ⟨ht,hx⟩)
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn (hDc.mono hIU)
  have hder (x : E) (hx : x ∈ K) (t : ℝ) (ht : t ∈ I) :
      HasDerivAt (fun r => F (r,x)) (D (t,x)) t := by
    have hh := ((hF.contDiffAt (hU.mem_nhds (hIU ⟨ht,hx⟩))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
  have hi : IntegrableOn (fun _ : E => C) K μ := continuousOn_const.integrableOn_compact hK
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ.restrict K) (F := fun t x => F (t,x)) (F' := fun t x => D (t,x))
    (s := I) (bound := fun _ => C) hIn
    (Filter.eventually_of_mem hIn (fun t ht => ((hFt t ht).integrableOn_compact hK).aestronglyMeasurable))
    ((hFt 0 hI0).integrableOn_compact hK)
    ((hDt 0 hI0).integrableOn_compact hK).aestronglyMeasurable
    (ae_restrict_mem hK.measurableSet |>.mono (fun x hx t ht => hC (t,x) ⟨ht,hx⟩))
    hi (ae_restrict_mem hK.measurableSet |>.mono (fun x hx t ht => hder x hx t ht))).2

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ParametricTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma eventually_uniform_compact_zero {E : Type*} [TopologicalSpace E]
    {K : Set E} (hK : IsCompact K) {P : ℝ × E → Prop}
    (hP : ∀ x ∈ K, {q | P q} ∈ nhds (0,x)) :
    ∀ᶠ t : ℝ in nhds 0, ∀ x ∈ K, P (t,x) := by
  have hs : {0} ×ˢ K ⊆ interior {q | P q} := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    simp only [mem_singleton_iff] at ht
    subst t
    exact mem_interior_iff_mem_nhds.mpr (hP x hx)
  obtain ⟨V,W,hV,hW,h0V,hKW,hVW⟩ := generalized_tube_lemma isCompact_singleton hK isOpen_interior hs
  filter_upwards [hV.mem_nhds (h0V (by simp))] with t ht
  intro x hx
  exact interior_subset (hVW ⟨ht,hKW hx⟩)

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

section TubeDensityVariation
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma hasDerivAt_tubeAreaDensity (B D : Matrix ι ι ℝ) (R T : Matrix κ κ ℝ)
    (hB : B.PosDef) (hR : R.PosDef) (δ : ℝ) :
    HasDerivAt (fun t : ℝ => tubeAreaDensity (B + t • D) (R + t • T) δ)
      (δ * Real.rpow B.det (δ-1) * Real.rpow R.det (1-δ) *
        (∑ i, ∑ j, B.adjugate j i * D i j) +
       (1-δ) * Real.rpow B.det δ * Real.rpow R.det (-δ) *
        (∑ i, ∑ j, R.adjugate j i * T i j)) 0 := by
  have hd := (hasDerivAt_affineArea_matrix B D hB δ).mul
    (hasDerivAt_affineArea_matrix R T hR (1-δ))
  simp only [zero_smul, add_zero] at hd
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [show 1-δ-1 = -δ by ring, Real.rpow_eq_pow]
  ring

end TubeDensityVariation

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
-- module Solutions.OAIQ22_AB.AffineBernstein_SupportVariation
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
variable {S E F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/- Homogeneous extension of an actual test function off the affine normal chart. -/

omit [CompleteSpace E] in
lemma contDiffAt_flatNormalProjection (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) {q : S × E} (hne : ℓ q.2 ≠ 0) :
    ContDiffAt ℝ ∞ (flatNormalProjection ℓ q₀ C) q := by
  apply C.contDiff.contDiffAt.comp q
  exact (contDiffAt_fst.prodMk
    (((ℓ.contDiff.contDiffAt.comp q contDiffAt_snd).inv hne).smul contDiffAt_snd)).sub contDiffAt_const

omit [CompleteSpace E] in
lemma contDiffAt_flatSupportVariation (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) {η : F → ℝ} (hη : ContDiff ℝ ∞ η)
    {q : S × E} (hne : ℓ q.2 ≠ 0) :
    ContDiffAt ℝ ∞ (flatSupportVariation ℓ q₀ C η) q := by
  exact (ℓ.contDiff.contDiffAt.comp q contDiffAt_snd).mul
    (hη.contDiffAt.comp q (contDiffAt_flatNormalProjection ℓ q₀ C hne))

lemma contDiffAt_supportGradient {H : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) : ContDiffAt ℝ ∞ (supportGradient H) q := by
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp q
    (contDiffAt_fiberGradient hH)

lemma supportGradient_angular {H : S × E → ℝ} {q : S × E}
    (hH : DifferentiableAt ℝ H q) (v : E) :
    fderiv ℝ H q (0,v) = inner ℝ (supportGradient H q) v := by
  have hd := hH.hasFDerivAt.comp (f := fun y : E => (q.1,y)) q.2
    ((hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2))
  change _ = (InnerProductSpace.toDual ℝ E (supportGradient H q)) v
  simp only [supportGradient, LinearIsometryEquiv.apply_symm_apply]
  change _ = fderiv ℝ (fun y => H (q.1,y)) q.2 v
  exact (congrArg (fun A : E →L[ℝ] ℝ => A v) hd.fderiv).symm

omit [CompleteSpace E] in
lemma flatNormalProjection_smul (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) (q : S × E) {t : ℝ} (ht : t ≠ 0) :
    flatNormalProjection ℓ q₀ C (q.1,t • q.2) = flatNormalProjection ℓ q₀ C q := by
  unfold flatNormalProjection
  congr 3
  simp only [map_smul,smul_eq_mul,mul_inv_rev,smul_smul]
  rw [mul_assoc,inv_mul_cancel₀ ht,mul_one]

omit [CompleteSpace E] in
lemma flatSupportVariation_smul (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) (η : F → ℝ) (q : S × E) {t : ℝ} (ht : t ≠ 0) :
    flatSupportVariation ℓ q₀ C η (q.1,t • q.2) = t * flatSupportVariation ℓ q₀ C η q := by
  simp only [flatSupportVariation,flatNormalProjection_smul ℓ q₀ C q ht,map_smul,smul_eq_mul]
  ring

lemma flatSupportVariation_euler (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) {η : F → ℝ} (hη : ContDiff ℝ ∞ η)
    {q : S × E} (hne : ℓ q.2 ≠ 0) :
    flatSupportVariation ℓ q₀ C η q = inner ℝ q.2
      (supportGradient (flatSupportVariation ℓ q₀ C η) q) := by
  let G := flatSupportVariation ℓ q₀ C η
  have hG : DifferentiableAt ℝ G q :=
    (contDiffAt_flatSupportVariation ℓ q₀ C hη hne).differentiableAt (by simp)
  have hp : HasDerivAt (fun t : ℝ => (q.1,t • q.2)) (0,q.2) 1 := by
    simpa using (hasDerivAt_const (1 : ℝ) q.1).prodMk ((hasDerivAt_id (1 : ℝ)).smul_const q.2)
  have hg : HasDerivAt (fun t : ℝ => G (q.1,t • q.2))
      (fderiv ℝ G q (0,q.2)) 1 := by
    have hG' : HasFDerivAt G (fderiv ℝ G q) (q.1, (1 : ℝ) • q.2) := by
      simpa using hG.hasFDerivAt
    exact hG'.comp_hasDerivAt 1 hp
  have he : (fun t : ℝ => G (q.1,t • q.2)) =ᶠ[𝓝 1] (fun t => t * G q) := by
    filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)] with t ht
    exact flatSupportVariation_smul ℓ q₀ C η q ht
  have hh := (hg.congr_of_eventuallyEq he.symm).unique ((hasDerivAt_id (1 : ℝ)).mul_const (G q))
  have hx := supportGradient_angular hG q.2
  rw [real_inner_comm]
  change G q = _
  simpa using hh.symm.trans hx

omit [CompleteSpace E] in
lemma flatNormalProjection_on_chart (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) (J : F →L[ℝ] S × E)
    (hℓ : ℓ q₀.2 = 1) (hJ : ∀ x, ℓ (J x).2 = 0)
    (hC : ∀ x, C (J x) = x) (x : F) :
    flatNormalProjection ℓ q₀ C (q₀+J x) = x := by
  have hh : ℓ (q₀+J x).2 = 1 := by simp [hℓ,hJ]
  unfold flatNormalProjection
  rw [hh,inv_one,one_smul]
  change C ((q₀+J x)-q₀) = x
  simpa using hC x

lemma supportGradient_flatVariation_eq_zero (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) (J : F →L[ℝ] S × E)
    (hℓ : ℓ q₀.2 = 1) (hJ : ∀ x, ℓ (J x).2 = 0)
    (hC : ∀ x, C (J x) = x) (η : F → ℝ) {x : F} (hx : x ∉ tsupport η) :
    supportGradient (flatSupportVariation ℓ q₀ C η) (q₀+J x) = 0 := by
  let q := q₀+J x
  have hq : ℓ q.2 = 1 := by simp [q,hℓ,hJ]
  have hp := (contDiffAt_flatNormalProjection ℓ q₀ C (by rw [hq]; norm_num)).continuousAt
  have heP := flatNormalProjection_on_chart ℓ q₀ C J hℓ hJ hC x
  have ht : Tendsto (flatNormalProjection ℓ q₀ C) (𝓝 q) (𝓝 x) := by
    simpa only [ContinuousAt,q,heP] using hp
  have heη : η =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have heG : flatSupportVariation ℓ q₀ C η =ᶠ[𝓝 q] (fun _ => 0) := by
    filter_upwards [ht.eventually heη] with y hy
    simp [flatSupportVariation,hy]
  have heF : (fun y => flatSupportVariation ℓ q₀ C η (q.1,y)) =ᶠ[𝓝 q.2] (fun _ => 0) :=
    heG.comp_tendsto (continuousAt_const.prodMk continuousAt_id)
  change (InnerProductSpace.toDual ℝ E).symm
      (fderiv ℝ (fun y => flatSupportVariation ℓ q₀ C η (q.1,y)) q.2) = 0
  rw [heF.fderiv_eq]
  simp

lemma tsupport_flatSupportVelocity_subset (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) (J : F →L[ℝ] S × E)
    (hℓ : ℓ q₀.2 = 1) (hJ : ∀ x, ℓ (J x).2 = 0)
    (hC : ∀ x, C (J x) = x) (η : F → ℝ) :
    tsupport (fun x => ((0 : S),supportGradient (flatSupportVariation ℓ q₀ C η) (q₀+J x))) ⊆
      tsupport η := by
  apply closure_minimal _ (isClosed_tsupport η)
  intro x hx
  by_contra hn
  have hh := supportGradient_flatVariation_eq_zero ℓ q₀ C J hℓ hJ hC η hn
  exact hx (by simp [hh])

lemma contDiff_flatSupportVelocity (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) (J : F →L[ℝ] S × E)
    (hℓ : ℓ q₀.2 = 1) (hJ : ∀ x, ℓ (J x).2 = 0)
    {η : F → ℝ} (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (fun x => ((0 : S),supportGradient (flatSupportVariation ℓ q₀ C η) (q₀+J x))) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hq : ℓ (q₀+J x).2 = 1 := by simp [hℓ,hJ]
  have hG := contDiffAt_flatSupportVariation ℓ q₀ C hη (by rw [hq]; norm_num)
  exact contDiffAt_const.prodMk ((contDiffAt_supportGradient hG).comp
    (f := fun x => q₀+J x) x (contDiffAt_const.add J.contDiff.contDiffAt))

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SupportVariationJets
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
variable {S E F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [CompleteSpace E] in
lemma support_identities_variation {H G : S × E → ℝ} {Y Z : S × E → E} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (hG : ContDiffAt ℝ ∞ G q)
    (heH : H =ᶠ[𝓝 q] (fun p => inner ℝ p.2 (Y p)))
    (heG : G =ᶠ[𝓝 q] (fun p => inner ℝ p.2 (Z p)))
    (hgH : ∀ᶠ p in 𝓝 q, ∀ v : E, fderiv ℝ H p (0,v) = inner ℝ (Y p) v)
    (hgG : ∀ᶠ p in 𝓝 q, ∀ v : E, fderiv ℝ G p (0,v) = inner ℝ (Z p) v)
    (t : ℝ) :
    (fun p => H p+t*G p) =ᶠ[𝓝 q] (fun p => inner ℝ p.2 (Y p+t • Z p)) ∧
    ∀ᶠ p in 𝓝 q, ∀ v : E, fderiv ℝ (fun r => H r+t*G r) p (0,v) =
      inner ℝ (Y p+t • Z p) v := by
  constructor
  · filter_upwards [heH,heG] with p hpH hpG
    simp [hpH,hpG,inner_add_right,real_inner_smul_right]
  · filter_upwards [hgH,hgG,
      (hH.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp),
      (hG.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)] with p hpH hpG hdH hdG v
    have hh := hdH.differentiableAt (by norm_num)
    have hg := hdG.differentiableAt (by norm_num)
    rw [fderiv_fun_add hh (hg.const_mul t),fderiv_const_mul hg t]
    simp [hpH v,hpG v,inner_add_left,real_inner_smul_left]

lemma flatSupportVariation_support_identities (ℓ : E →L[ℝ] ℝ) (q₀ : S × E)
    (C : (S × E) →L[ℝ] F) {η : F → ℝ} (hη : ContDiff ℝ ∞ η)
    {q : S × E} (hne : ℓ q.2 ≠ 0) :
    flatSupportVariation ℓ q₀ C η =ᶠ[𝓝 q]
      (fun p => inner ℝ p.2 (supportGradient (flatSupportVariation ℓ q₀ C η) p)) ∧
    ∀ᶠ p in 𝓝 q, ∀ v : E, fderiv ℝ (flatSupportVariation ℓ q₀ C η) p (0,v) =
      inner ℝ (supportGradient (flatSupportVariation ℓ q₀ C η) p) v := by
  have hn : ∀ᶠ p in 𝓝 q, ℓ p.2 ≠ 0 :=
    ((ℓ.continuous.comp continuous_snd).continuousAt.preimage_mem_nhds
      (isOpen_compl_singleton.mem_nhds hne))
  constructor
  · filter_upwards [hn] with p hp
    exact flatSupportVariation_euler ℓ q₀ C hη hp
  · filter_upwards [hn] with p hp v
    exact supportGradient_angular
      ((contDiffAt_flatSupportVariation ℓ q₀ C hη hp).differentiableAt (by simp)) v

omit [CompleteSpace E] in
lemma supportParam_variation (Y Z : S × E → E) (t : ℝ) (q : S × E) :
    supportParam (fun p => Y p+t • Z p) q = supportParam Y q+t • ((0 : S),Z q) := by
  simp [supportParam]

lemma supportConormal_variation_continuous {H G : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (hG : ContDiffAt ℝ ∞ G q) (t : ℝ) (v : S × E) :
    ContinuousAt (fun p : ℝ × (S × E) => supportConormal
      (fun r => H r+p.1*G r) p.2 v) (t,q) := by
  have hF : ContDiffAt ℝ ∞ (fun p : ℝ × (S × E) => H p.2+p.1*G p.2) (t,q) :=
    (hH.comp (t,q) contDiffAt_snd).add
      (contDiffAt_fst.mul (hG.comp (t,q) contDiffAt_snd))
  have hd := contDiffAt_fiberGradient hF
  have ha := (hd.clm_apply (contDiffAt_const (c := (v.1,0)))).continuousAt
  have hb : ContinuousAt (fun p : ℝ × (S × E) => inner ℝ p.2.2 v.2) (t,q) :=
    continuousAt_snd.snd.inner continuousAt_const
  exact ha.sub hb

lemma supportConormal_flat_transverse {H : S × E → ℝ} {q : S × E} {d : E}
    (hd : inner ℝ q.2 d = 1) : supportConormal H q ((0 : S),-d) = 1 := by
  simp [supportConormal,show ((0,0) : S × E) = 0 from rfl,hd]

lemma supportConormal_flat_variation_tangent {H G : S × E → ℝ} {Y Z : S × E → E}
    (q₀ : S × E) (J : F →L[ℝ] S × E) {x : F}
    (hH : ContDiffAt ℝ ∞ H (q₀+J x)) (hG : ContDiffAt ℝ ∞ G (q₀+J x))
    (hY : ContDiffAt ℝ ∞ Y (q₀+J x)) (hZ : ContDiffAt ℝ ∞ Z (q₀+J x))
    (heH : H =ᶠ[𝓝 (q₀+J x)] (fun p => inner ℝ p.2 (Y p)))
    (heG : G =ᶠ[𝓝 (q₀+J x)] (fun p => inner ℝ p.2 (Z p)))
    (hgH : ∀ᶠ p in 𝓝 (q₀+J x), ∀ v : E, fderiv ℝ H p (0,v) = inner ℝ (Y p) v)
    (hgG : ∀ᶠ p in 𝓝 (q₀+J x), ∀ v : E, fderiv ℝ G p (0,v) = inner ℝ (Z p) v)
    (t : ℝ) :
    (supportConormal (fun r => H r+t*G r) (q₀+J x)).comp
      (fderiv ℝ (fun y => supportParam Y (q₀+J y)+t • ((0 : S),Z (q₀+J y))) x) = 0 := by
  obtain ⟨he,hg⟩ := support_identities_variation hH hG heH heG hgH hgG t
  have hHt : ContDiffAt ℝ ∞ (fun r => H r+t*G r) (q₀+J x) := hH.add (contDiffAt_const.mul hG)
  have hYt : ContDiffAt ℝ ∞ (fun r => Y r+t • Z r) (q₀+J x) := hY.add (hZ.const_smul t)
  have heq : (fun y => supportParam Y (q₀+J y)+t • ((0 : S),Z (q₀+J y))) =
      (fun y => supportParam (fun r => Y r+t • Z r) (q₀+J y)) := by
    funext y
    exact (supportParam_variation Y Z t _).symm
  rw [heq]
  have hpY : ContDiffAt ℝ ∞ (supportParam (fun r => Y r+t • Z r)) (q₀+J x) :=
    contDiffAt_fst.prodMk hYt
  have hp := (hpY.differentiableAt (by simp)).hasFDerivAt.comp
    (f := fun y => q₀+J y) x (J.hasFDerivAt.const_add q₀)
  have hdf : fderiv ℝ (fun y => supportParam (fun r => Y r+t • Z r) (q₀+J y)) x = _ := hp.fderiv
  rw [hdf]
  ext v
  exact supportConormal_tangent (hHt.differentiableAt (by simp))
    (hYt.differentiableAt (by simp)) he hg.self_of_nhds (J v)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualSupportVariation
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

/- Every actual smooth compact flat support variation is stationary. Its
homogeneous lifting, compact support, conormal and transverse fields are
constructed explicitly rather than supplied as stationarity hypotheses. -/
theorem affineMaximal_compact_flat_support_variation {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (q₀ : S × E) (d : E) (hd : inner ℝ q₀.2 d = 1)
    (J : Space n →L[ℝ] (S × E)) (hi : Function.Injective J)
    (hJ : ∀ v, inner ℝ (J v).2 d = 0)
    (C : (S × E) →L[ℝ] Space n) (hC : ∀ x, C (J x) = x)
    (b : Module.Basis (Fin n ⊕ Unit) ℝ (S × E))
    {x₀ : Space n} (hx₀ : (q₀+J x₀).1 ∈ B) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let ℓ := InnerProductSpace.toDual ℝ E d
    ∃ W : Set (Space n), IsOpen W ∧ x₀ ∈ W ∧ W ⊆ {x | (q₀+J x).1 ∈ B} ∧
      ∀ (K : Set (Space n)), IsCompact K → K ⊆ W →
      ∀ (η : Space n → ℝ), ContDiff ℝ ∞ η → tsupport η ⊆ K →
      let G := flatSupportVariation ℓ q₀ C η
      let Z := supportGradient G
      HasDerivAt (fun t : ℝ => ∫ x in K, parametricAreaDensity b
        (fun y => supportParam (fun q => Y q+t • Z q) (q₀+J y))
        (supportConormal (fun q => H q+t*G q) (q₀+J x)) (0,-d) x) 0 0 := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let ℓ := InnerProductSpace.toDual ℝ E d
  have hℓ : ℓ q₀.2 = 1 := by simpa [ℓ,real_inner_comm] using hd
  have hℓJ (x : Space n) : ℓ (J x).2 = 0 := by simpa [ℓ,real_inner_comm] using hJ x
  obtain ⟨W,hW,hxW,hWU,hstat⟩ := affineMaximal_flatSupport_local_stationary hΩ hcv hu hp hm
    a L hB hK hzero q₀ d hd J hi hJ b hx₀
  change ∃ W, _
  refine ⟨W,hW,hxW,hWU,?_⟩
  intro K hKc hKW η hη hηK
  let G := flatSupportVariation ℓ q₀ C η
  let Z := supportGradient G
  let V := fun x : Space n => ((0 : S),Z (q₀+J x))
  let ν := fun t : ℝ => fun x : Space n => supportConormal (fun q => H q+t*G q) (q₀+J x)
  have hq (x : Space n) : inner ℝ (q₀+J x).2 d = 1 := by simp [inner_add_left,hd,hJ]
  have hne (x : Space n) : (q₀+J x).2 ≠ 0 := by
    intro hz
    simpa [hz] using hq x
  have hℓne (x : Space n) : ℓ (q₀+J x).2 ≠ 0 := by simp [hℓ,hℓJ]
  have hj (x : Space n) (hx : x ∈ W) :=
    affineEpigraph_support_jets hΩ hcv hu hp a L hB hK hzero (hWU hx) (hne x)
  have hG (x : Space n) : ContDiffAt ℝ ∞ G (q₀+J x) :=
    contDiffAt_flatSupportVariation ℓ q₀ C hη (hℓne x)
  have hg (x : Space n) := flatSupportVariation_support_identities ℓ q₀ C hη (hℓne x)
  have hV : ContDiffOn ℝ ∞ V W :=
    (contDiff_flatSupportVelocity ℓ q₀ C J hℓ hℓJ hη).contDiffOn
  have hsV : tsupport V ⊆ K :=
    (tsupport_flatSupportVelocity_subset ℓ q₀ C J hℓ hℓJ hC η).trans hηK
  have hν (t : ℝ) (x : Space n) (hx : x ∈ W) :
      (ν t x).comp (fderiv ℝ (fun y => supportParam Y (q₀+J y)+t • V y) x) = 0 := by
    exact supportConormal_flat_variation_tangent q₀ J (hj x hx).1 (hG x)
      (hj x hx).2.1 (contDiffAt_supportGradient (hG x))
      (hj x hx).2.2.1 (hg x).1 (hj x hx).2.2.2 (hg x).2 t
  have hξ (t : ℝ) (x : Space n) (_ : x ∈ W) : ν t x (0,-d) = 1 :=
    supportConormal_flat_transverse (hq x)
  have hν0 (x : Space n) (_ : x ∈ K) : ν 0 x = supportConormal H (q₀+J x) := by
    simp [ν]
  have hcν (x : Space n) (hx : x ∈ K) :
      ContinuousAt (fun p : ℝ × Space n => ν p.1 p.2 (L.symm ((0 : Space n),1))) (0,x) := by
    have hh := supportConormal_variation_continuous (hj x (hKW hx)).1 (hG x) 0
      (L.symm ((0 : Space n),1))
    have he : ContinuousAt (fun p : ℝ × Space n => (p.1,q₀+J p.2)) (0,x) :=
      continuousAt_fst.prodMk
        (continuousAt_const.add (J.continuous.continuousAt.comp continuousAt_snd))
    exact ContinuousAt.comp (f := fun p : ℝ × Space n => (p.1,q₀+J p.2))
      (x := (0,x)) hh he
  have ht := hstat K hKc hKW V hV hsV ν (fun _ _ => (0,-d)) hν hξ hν0 hcν
  have heX (t : ℝ) : (fun y => supportParam Y (q₀+J y)+t • V y) =
      (fun y => supportParam (fun q => Y q+t • Z q) (q₀+J y)) := by
    funext y
    exact (supportParam_variation Y Z t _).symm
  change HasDerivAt (fun t : ℝ => ∫ x in K, parametricAreaDensity b
    (fun y => supportParam (fun q => Y q+t • Z q) (q₀+J y)) (ν t x) (0,-d) x) 0 0
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  congr 1
  funext x
  rw [heX t]

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
-- module Solutions.OAIQ22_AB.AffineBernstein_HessianVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section HessianVariation
open Filter
open scoped Topology
variable {P Q R : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup R] [NormedSpace ℝ R]

lemma second_fderiv_add_const_smul {F G : P → Q} {x : P}
    (hF : ContDiffAt ℝ ∞ F x) (hG : ContDiffAt ℝ ∞ G x) (t : ℝ) :
    fderiv ℝ (fderiv ℝ (fun y => F y+t • G y)) x =
      fderiv ℝ (fderiv ℝ F) x+t • fderiv ℝ (fderiv ℝ G) x := by
  have he : fderiv ℝ (fun y => F y+t • G y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ F y+t • fderiv ℝ G y) := by
    filter_upwards [(hF.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp),
      (hG.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)] with y hf hg
    simpa only [Pi.smul_def,Pi.add_def] using
      ((hf.differentiableAt (by norm_num)).hasFDerivAt.add
        ((hg.differentiableAt (by norm_num)).hasFDerivAt.const_smul t)).fderiv
  rw [he.fderiv_eq]
  have hf := (hF.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hg := (hG.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  simpa only [Pi.smul_def,Pi.add_def] using (hf.hasFDerivAt.add (hg.hasFDerivAt.const_smul t)).fderiv

lemma contDiffAt_partialSecond {F : P × Q → R} {p : P × Q}
    (hF : ContDiffAt ℝ ∞ F p) :
    ContDiffAt ℝ ∞ (fun r : P × Q =>
      fderiv ℝ (fderiv ℝ (fun y : Q => F (r.1,y))) r.2) p := by
  have hd : ContDiffAt ℝ ∞ (fun r : P × Q =>
      fderiv ℝ (fun y => F (r.1,y)) r.2) p := by
    apply ContDiffAt.fderiv (n := ∞) (g := Prod.snd) _ contDiffAt_snd (by simp)
    exact hF.comp (p,p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  apply ContDiffAt.fderiv (n := ∞) (g := Prod.snd) _ contDiffAt_snd (by simp)
  exact hd.comp (p,p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)

end HessianVariation

open Filter
open scoped Topology
variable {S E F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] in
lemma tubeBaseMatrix_variation {H G : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (hG : ContDiffAt ℝ ∞ G q)
    (bS : Module.Basis ι ℝ S) (t : ℝ) :
    tubeBaseMatrix (fun r => H r+t*G r) q bS =
      tubeBaseMatrix H q bS+t • tubeBaseMatrix G q bS := by
  ext i j
  have hh := congrArg (fun A : (S × E) →L[ℝ] (S × E) →L[ℝ] ℝ => A (bS i,0) (bS j,0))
    (second_fderiv_add_const_smul hH hG t)
  simp only [add_apply,smul_apply,smul_eq_mul] at hh
  change -fderiv ℝ (fderiv ℝ (fun r => H r+t*G r)) q (bS i,0) (bS j,0) =
    -fderiv ℝ (fderiv ℝ H) q (bS i,0) (bS j,0)+
      t * (-fderiv ℝ (fderiv ℝ G) q (bS i,0) (bS j,0))
  rw [hh]
  ring

omit [DecidableEq κ] in
lemma tubeRadiusMatrix_variation {H G : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (hG : ContDiffAt ℝ ∞ G q)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (t : ℝ) :
    tubeRadiusMatrix (fun r => H r+t*G r) q bE =
      tubeRadiusMatrix H q bE+t • tubeRadiusMatrix G q bE := by
  ext i j
  exact congrArg (fun A : (S × E) →L[ℝ] (S × E) →L[ℝ] ℝ =>
    A (0,bE (Sum.inl i)) (0,bE (Sum.inl j))) (second_fderiv_add_const_smul hH hG t)

omit [DecidableEq ι] [DecidableEq κ] in
lemma contDiffAt_tubeMatrices_variation {H G : S × E → ℝ}
    (q₀ : S × E) (J : F →L[ℝ] (S × E)) {p : ℝ × F}
    (hH : ContDiffAt ℝ ∞ H (q₀+J p.2)) (hG : ContDiffAt ℝ ∞ G (q₀+J p.2))
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    ContDiffAt ℝ ∞ (fun r : ℝ × F => fun i j => tubeBaseMatrix (fun q => H q+r.1*G q) (q₀+J r.2) bS i j) p ∧
    ContDiffAt ℝ ∞ (fun r : ℝ × F => fun i j => tubeRadiusMatrix (fun q => H q+r.1*G q) (q₀+J r.2) bE i j) p := by
  have hF : ContDiffAt ℝ ∞ (fun r : ℝ × (S × E) => H r.2+r.1*G r.2) (p.1,q₀+J p.2) :=
    (hH.comp (f := Prod.snd) (p.1,q₀+J p.2) contDiffAt_snd).add
      (contDiffAt_fst.mul (hG.comp (f := Prod.snd) (p.1,q₀+J p.2) contDiffAt_snd))
  have hD := (contDiffAt_partialSecond hF).comp
    (f := fun r : ℝ × F => (r.1,q₀+J r.2)) p
    (contDiffAt_fst.prodMk (contDiffAt_const.add (J.contDiff.contDiffAt.comp p contDiffAt_snd)))
  constructor
  · exact contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
      ((hD.clm_apply contDiffAt_const).clm_apply contDiffAt_const).neg))
  · exact contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
      (hD.clm_apply contDiffAt_const).clm_apply contDiffAt_const))

lemma hasDerivAt_tubeDensity_variation {H G : S × E → ℝ} {q : S × E}
    (hH : ContDiffAt ℝ ∞ H q) (hG : ContDiffAt ℝ ∞ G q)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hB : (tubeBaseMatrix H q bS).PosDef) (hR : (tubeRadiusMatrix H q bE).PosDef) (δ : ℝ) :
    HasDerivAt (fun t : ℝ => tubeAreaDensity
      (tubeBaseMatrix (fun r => H r+t*G r) q bS)
      (tubeRadiusMatrix (fun r => H r+t*G r) q bE) δ)
      (tubeAreaFirstVariation (tubeBaseMatrix H q bS) (tubeBaseMatrix G q bS)
        (tubeRadiusMatrix H q bE) (tubeRadiusMatrix G q bE) δ) 0 := by
  simp_rw [tubeBaseMatrix_variation hH hG,tubeRadiusMatrix_variation hH hG]
  exact hasDerivAt_tubeAreaDensity _ _ _ _ hB hR δ

lemma contDiffAt_tubeDensity_variation {H G : S × E → ℝ}
    (q₀ : S × E) (J : F →L[ℝ] (S × E)) {p : ℝ × F}
    (hH : ContDiffAt ℝ ∞ H (q₀+J p.2)) (hG : ContDiffAt ℝ ∞ G (q₀+J p.2))
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hB : (tubeBaseMatrix (fun q => H q+p.1*G q) (q₀+J p.2) bS).det ≠ 0)
    (hR : (tubeRadiusMatrix (fun q => H q+p.1*G q) (q₀+J p.2) bE).det ≠ 0) (δ : ℝ) :
    ContDiffAt ℝ ∞ (fun r : ℝ × F => tubeAreaDensity
      (tubeBaseMatrix (fun q => H q+r.1*G q) (q₀+J r.2) bS)
      (tubeRadiusMatrix (fun q => H q+r.1*G q) (q₀+J r.2) bE) δ) p := by
  obtain ⟨hb,hr⟩ := contDiffAt_tubeMatrices_variation q₀ J hH hG bS bE
  exact (((continuousDetRows (ι := ι)).contDiff.contDiffAt.comp p hb).rpow_const_of_ne hB).mul
    (((continuousDetRows (ι := κ)).contDiff.contDiffAt.comp p hr).rpow_const_of_ne hR)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_TubeDensityIntegralCompact
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
variable {S E F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  {μ : Measure F} [IsLocallyFiniteMeasure μ]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- The exact tube density can be differentiated under its compact integral;
positivity is required only on the zero-parameter slice and is then uniform
for the compactly supported variation by the tube lemma. -/
lemma hasDerivAt_integral_tubeDensity_variation
    {H G : S × E → ℝ} (q₀ : S × E) (J : F →L[ℝ] (S × E))
    {W K : Set F} (hW : IsOpen W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hH : ∀ x ∈ W, ContDiffAt ℝ ∞ H (q₀+J x))
    (hG : ∀ x ∈ W, ContDiffAt ℝ ∞ G (q₀+J x))
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hB : ∀ x ∈ K, (tubeBaseMatrix H (q₀+J x) bS).PosDef)
    (hR : ∀ x ∈ K, (tubeRadiusMatrix H (q₀+J x) bE).PosDef) (δ : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x in K, tubeAreaDensity
      (tubeBaseMatrix (fun r => H r+t*G r) (q₀+J x) bS)
      (tubeRadiusMatrix (fun r => H r+t*G r) (q₀+J x) bE) δ ∂μ)
      (∫ x in K, tubeAreaFirstVariation (tubeBaseMatrix H (q₀+J x) bS)
        (tubeBaseMatrix G (q₀+J x) bS) (tubeRadiusMatrix H (q₀+J x) bE)
        (tubeRadiusMatrix G (q₀+J x) bE) δ ∂μ) 0 := by
  let DB := fun p : ℝ × F => (tubeBaseMatrix (fun q => H q+p.1*G q) (q₀+J p.2) bS).det
  let DR := fun p : ℝ × F => (tubeRadiusMatrix (fun q => H q+p.1*G q) (q₀+J p.2) bE).det
  let U := {p : ℝ × F | p.2 ∈ W ∧ 0 < DB p ∧ 0 < DR p}
  have hc (p : ℝ × F) (hp : p.2 ∈ W) : ContinuousAt DB p ∧ ContinuousAt DR p := by
    obtain ⟨hb,hr⟩ := contDiffAt_tubeMatrices_variation q₀ J (hH _ hp) (hG _ hp) bS bE
    exact ⟨((continuousDetRows (ι := ι)).contDiff.contDiffAt.comp p hb).continuousAt,
      ((continuousDetRows (ι := κ)).contDiff.contDiffAt.comp p hr).continuousAt⟩
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hw : ∀ᶠ r : ℝ × F in 𝓝 p, r.2 ∈ W :=
      continuous_snd.continuousAt.preimage_mem_nhds (hW.mem_nhds hp.1)
    have hb := continuousAt_const.eventually_lt (hc p hp.1).1 hp.2.1
    have hr := continuousAt_const.eventually_lt (hc p hp.1).2 hp.2.2
    exact (hw.and (hb.and hr))
  have h0 (x : F) (hx : x ∈ K) : (0,x) ∈ U := by
    refine ⟨hKW hx,?_,?_⟩
    · simpa [DB] using (hB x hx).det_pos
    · simpa [DR] using (hR x hx).det_pos
  let Fd := fun p : ℝ × F => tubeAreaDensity
    (tubeBaseMatrix (fun q => H q+p.1*G q) (q₀+J p.2) bS)
    (tubeRadiusMatrix (fun q => H q+p.1*G q) (q₀+J p.2) bE) δ
  have hFd (p : ℝ × F) (hp : p ∈ U) : ContDiffAt ℝ ∞ Fd p :=
    contDiffAt_tubeDensity_variation q₀ J (hH _ hp.1) (hG _ hp.1) bS bE
      (ne_of_gt hp.2.1) (ne_of_gt hp.2.2) δ
  have hd := hasDerivAt_setIntegral_compact (μ := μ) hK hU
    (by rintro ⟨t,x⟩ ⟨ht,hx⟩; rcases ht with rfl; exact h0 x hx)
    (F := Fd) (fun p hp => (hFd p hp).contDiffWithinAt)
  have he (x : F) (hx : x ∈ K) : fderiv ℝ Fd (0,x) (1,0) =
      tubeAreaFirstVariation (tubeBaseMatrix H (q₀+J x) bS)
        (tubeBaseMatrix G (q₀+J x) bS) (tubeRadiusMatrix H (q₀+J x) bE)
        (tubeRadiusMatrix G (q₀+J x) bE) δ := by
    have h1 := (((hFd (0,x) (h0 x hx)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
      (f := fun t : ℝ => (t,x)) 0 ((hasDerivAt_id 0).prodMk (hasDerivAt_const 0 x)))
    exact h1.unique (hasDerivAt_tubeDensity_variation (hH x (hKW hx)) (hG x (hKW hx))
      bS bE (hB x hx) (hR x hx) δ)
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  exact setIntegral_congr_fun hK.measurableSet (fun x hx => (he x hx).symm)

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualFlatWeakEuler
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

/- The original affine-maximal PDE gives the literal flat tube weak Euler
identity. Both Hessian blocks, the support variation and the local stationary
chart are produced from the actual affine epigraph. -/
theorem affineMaximal_flat_tube_weak_euler_oai {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (q₀ : S × E) (hd : inner ℝ q₀.2 (bE (Sum.inr ())) = 1)
    (J : Space n →L[ℝ] (S × E)) (hi : Function.Injective J)
    (hJ : ∀ v, inner ℝ (J v).2 (bE (Sum.inr ())) = 0)
    (C : (S × E) →L[ℝ] Space n) (hC : ∀ x, C (J x) = x)
    (e : Fin n ≃ ι ⊕ κ)
    (hJb : ∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i))
    {x₀ : Space n} (hx₀ : (q₀+J x₀).1 ∈ B) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let ℓ := InnerProductSpace.toDual ℝ E (bE (Sum.inr ()))
    let δ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
    ∃ W : Set (Space n), IsOpen W ∧ x₀ ∈ W ∧ W ⊆ {x | (q₀+J x).1 ∈ B} ∧
      ∀ (K : Set (Space n)), IsCompact K → K ⊆ W →
      ∀ (η : Space n → ℝ), ContDiff ℝ ∞ η → tsupport η ⊆ K →
      let G := flatSupportVariation ℓ q₀ C η
      (∫ x in K, tubeAreaFirstVariation (tubeBaseMatrix H (q₀+J x) bS)
        (tubeBaseMatrix G (q₀+J x) bS) (tubeRadiusMatrix H (q₀+J x) bE)
        (tubeRadiusMatrix G (q₀+J x) bE) δ) = 0 := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let d := bE (Sum.inr ())
  let ℓ := InnerProductSpace.toDual ℝ E d
  let δ : ℝ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
  let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
  let b := (bS.prod bE.toBasis).reindex eA.symm
  obtain ⟨W,hW,hxW,hWU,hstat⟩ := affineMaximal_compact_flat_support_variation hΩ hcv hu hp hm
    a L hB hK hzero q₀ d hd J hi hJ C hC b hx₀
  refine ⟨W,hW,hxW,hWU,?_⟩
  intro K hKc hKW η hη hηK
  let G := flatSupportVariation ℓ q₀ C η
  let Z := supportGradient G
  have hℓ : ℓ q₀.2 = 1 := by simpa [ℓ,real_inner_comm] using hd
  have hℓJ (x : Space n) : ℓ (J x).2 = 0 := by simpa [ℓ,real_inner_comm] using hJ x
  have hq (x : Space n) : inner ℝ (q₀+J x).2 d = 1 := by simp [inner_add_left,hd,hJ,d]
  have hne (x : Space n) : (q₀+J x).2 ≠ 0 := by
    intro hz
    simpa [hz] using hq x
  have hℓne (x : Space n) : ℓ (q₀+J x).2 ≠ 0 := by simp [hℓ,hℓJ]
  have hj (x : Space n) (hx : x ∈ W) :=
    affineEpigraph_support_jets hΩ hcv hu hp a L hB hK hzero (hWU hx) (hne x)
  have hg (x : Space n) := flatSupportVariation_support_identities ℓ q₀ C hη (hℓne x)
  have hG (x : Space n) : ContDiffAt ℝ ∞ G (q₀+J x) :=
    contDiffAt_flatSupportVariation ℓ q₀ C hη (hℓne x)
  have hpos (x : Space n) (hx : x ∈ W) :=
    affineEpigraph_flat_tube_positive hΩ hcv hu hp a L hB hK hzero (hWU hx) (e := (q₀+J x).2) bS bE
      (by rw [hq x]; norm_num)
  have hD := hasDerivAt_integral_tubeDensity_variation (μ := volume) q₀ J hW hKc hKW
    (fun x hx => (hj x hx).1) (fun x _ => hG x) bS bE
    (fun x hx => (hpos x (hKW hx)).1) (fun x hx => (hpos x (hKW hx)).2) δ
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ x ∈ K,
      0 < (tubeBaseMatrix (fun q => H q+t*G q) (q₀+J x) bS).det ∧
      0 < (tubeRadiusMatrix (fun q => H q+t*G q) (q₀+J x) bE).det := by
    apply eventually_uniform_compact_zero (P := fun r : ℝ × Space n =>
      0 < (tubeBaseMatrix (fun q => H q+r.1*G q) (q₀+J r.2) bS).det ∧
      0 < (tubeRadiusMatrix (fun q => H q+r.1*G q) (q₀+J r.2) bE).det) hKc
    intro x hx
    obtain ⟨hb,hr⟩ := contDiffAt_tubeMatrices_variation q₀ J
      (p := (0,x)) (hj x (hKW hx)).1 (hG x) bS bE
    have hdb := ((continuousDetRows (ι := ι)).contDiff.contDiffAt.comp (0,x) hb).continuousAt
    have hdr := ((continuousDetRows (ι := κ)).contDiff.contDiffAt.comp (0,x) hr).continuousAt
    change ContinuousAt (fun p : ℝ × Space n =>
      (tubeBaseMatrix (fun q => H q+p.1*G q) (q₀+J p.2) bS).det) (0,x) at hdb
    change ContinuousAt (fun p : ℝ × Space n =>
      (tubeRadiusMatrix (fun q => H q+p.1*G q) (q₀+J p.2) bE).det) (0,x) at hdr
    exact (continuousAt_const.eventually_lt hdb (by simpa only [zero_mul,add_zero] using (hpos x (hKW hx)).1.det_pos)).and
      (continuousAt_const.eventually_lt hdr (by simpa only [zero_mul,add_zero] using (hpos x (hKW hx)).2.det_pos))
  have heq : (fun t : ℝ => ∫ x in K, parametricAreaDensity b
      (fun y => supportParam (fun q => Y q+t • Z q) (q₀+J y))
      (supportConormal (fun q => H q+t*G q) (q₀+J x)) (0,-d) x) =ᶠ[𝓝 0]
      (fun t : ℝ => ∫ x in K, tubeAreaDensity
        (tubeBaseMatrix (fun q => H q+t*G q) (q₀+J x) bS)
        (tubeRadiusMatrix (fun q => H q+t*G q) (q₀+J x) bE) δ) := by
    filter_upwards [hev] with t ht
    apply setIntegral_congr_fun hKc.measurableSet
    intro x hx
    have hHt : ContDiffAt ℝ ∞ (fun q => H q+t*G q) (q₀+J x) :=
      (hj x (hKW hx)).1.add (contDiffAt_const.mul (hG x))
    have hYt : ContDiffAt ℝ ∞ (fun q => Y q+t • Z q) (q₀+J x) :=
      (hj x (hKW hx)).2.1.add ((contDiffAt_supportGradient (hG x)).const_smul t)
    have hid := support_identities_variation (hj x (hKW hx)).1 (hG x)
      (hj x (hKW hx)).2.2.1 (hg x).1 (hj x (hKW hx)).2.2.2 (hg x).2 t
    dsimp only [b,eA,d]
    rw [parametricAreaDensity_flatSupport q₀ J hYt bS bE e hJb]
    exact flatTubeAffineAreaJet_eq hHt hYt hid.1 hid.2 bS bE (ht x hx).1 (ht x hx).2
  have hS := hstat K hKc hKW η hη hηK
  have hS' := hS.congr_of_eventuallyEq heq.symm
  exact hD.unique hS'

end AffineBernstein
end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.AffineBernstein.affineMaximal_flat_tube_weak_euler_oai.{u_1, u_2, u_3, u_4} := @OAI.AffineBernstein.affineMaximal_flat_tube_weak_euler_oai.{u_1, u_2, u_3, u_4}
