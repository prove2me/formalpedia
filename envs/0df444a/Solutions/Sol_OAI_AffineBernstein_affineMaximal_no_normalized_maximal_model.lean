-- Prove2me | solution 1 for OAI.AffineBernstein.affineMaximal_no_normalized_maximal_model
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:04:52.22973+00:00
-- url     : https://prove2.me/submissions/f8a2c22f-eb89-4129-81ee-7615dea0db62

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_affineEpigraph_sigma_normalization
import Theorems.Thm_OAI_AffineBernstein_affineMaximal_no_polynomial_logMeasure
import Theorems.Thm_OAI_AffineBernstein_normalized_model_positive_log_mass
import Theorems.Thm_OAI_AffineBernstein_normalized_model_uniform_actual_sigma

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
omit [NormedSpace ℝ E] in
theorem LocalDistanceConverges.mem_of_tendsto
    {Cj : ℕ → Set E} {C : Set E} (h : LocalDistanceConverges Cj C)
    (hcl : IsClosed C) (hne : C.Nonempty) {xj : ℕ → E}
    (hmem : ∀ j, xj j ∈ Cj j) {x : E} (hx : Tendsto xj atTop (𝓝 x)) : x ∈ C := by
  apply (hcl.mem_iff_infDist_zero hne).mpr
  have hle : ∀ j, infDist x (Cj j) ≤ dist x (xj j) :=
    fun j => infDist_le_dist_of_mem (hmem j)
  have hd : Tendsto (fun j => dist x (xj j)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).dist hx
  exact le_antisymm (le_of_tendsto_of_tendsto (h.pointwise x) hd (Filter.Eventually.of_forall hle))
    infDist_nonneg

/- Uniform cap compactness, geometry.tex:104–125. The proof traps a chord
on a fixed compact sphere, rather than choosing escaping directions. -/
omit [NormedSpace ℝ E] [ProperSpace E] in
theorem isCompact_nonneg_unitLipschitz (R : ℝ) :
    IsCompact {f : C(E, ℝ) | LipschitzWith 1 f ∧ f 0 ≤ R ∧ ∀ x, 0 ≤ f x} := by
  classical
  let P : Set (E → ℝ) := {f | LipschitzWith 1 f ∧ f 0 ≤ R ∧ ∀ x, 0 ≤ f x}
  have hPcl : IsClosed P := by
    have hnonneg : IsClosed {f : E → ℝ | ∀ x, 0 ≤ f x} := by
      simpa only [Set.ofPred_forall] using
        (isClosed_iInter fun x : E => isClosed_le (continuous_const : Continuous (fun _ : E → ℝ => (0 : ℝ)))
          (continuous_apply x))
    exact (isClosed_setOfPred_lipschitzWith (1 : ℝ≥0)).inter
      ((isClosed_le (continuous_apply 0) continuous_const).inter hnonneg)
  have hPc : IsCompact P := by
    apply (isCompact_univ_pi fun x : E => isCompact_Icc (a := (0 : ℝ)) (b := ‖x‖ + R)).of_isClosed_subset hPcl
    intro f hf x _
    refine ⟨hf.2.2 x, ?_⟩
    have he := hf.1.dist_le_mul x 0
    simp only [NNReal.coe_one, one_mul, dist_zero_right, Real.dist_eq] at he
    have hfup := (abs_le.mp he).2
    linarith [hf.2.1]
  apply ArzelaAscoli.isCompact_of_equicontinuous
  · have him : ContinuousMap.toFun ''
        {f : C(E, ℝ) | LipschitzWith 1 f ∧ f 0 ≤ R ∧ ∀ x, 0 ≤ f x} = P := by
      ext f
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact hg
      · intro hf
        exact ⟨⟨f, hf.1.continuous⟩, hf, rfl⟩
    rwa [him]
  · exact (LipschitzWith.uniformEquicontinuous _ 1 (fun f => f.2.1)).equicontinuous

/- Extract locally uniformly convergent distance functions. At this stage
we do not yet assert that the limit is a distance function. -/
omit [NormedSpace ℝ E] in
theorem exists_distance_function_subsequence {Cj : ℕ → Set E}
    {R : ℝ} (hbound : ∀ j, infDist (0 : E) (Cj j) ≤ R) :
    ∃ (f : C(E, ℝ)) (φ : ℕ → ℕ), StrictMono φ ∧
      LipschitzWith 1 f ∧ (∀ x, 0 ≤ f x) ∧
      TendstoLocallyUniformly (fun j x => infDist x (Cj (φ j))) f atTop := by
  let dj : ℕ → C(E, ℝ) := fun j => ⟨fun x => infDist x (Cj j), continuous_infDist_pt _⟩
  obtain ⟨f, hf, φ, hφ, hconv⟩ := (isCompact_nonneg_unitLipschitz (E := E) R).tendsto_subseq
    (x := dj) (fun j => ⟨lipschitz_infDist_pt _, hbound j, fun _ => infDist_nonneg⟩)
  exact ⟨f, φ, hφ, hf.1, hf.2.2, ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hconv⟩

/- A pointwise limit of nonnegative unit-Lipschitz distance functions of
nonempty closed sets, on a proper space, is itself their zero-set's distance
function. Nearest points supply the nonempty zero set and attain the distance. -/
omit [NormedSpace ℝ E] in
theorem distance_function_limit_representation {Cj : ℕ → Set E} {f : E → ℝ}
    (hcl : ∀ j, IsClosed (Cj j)) (hne : ∀ j, (Cj j).Nonempty)
    (hlip : LipschitzWith 1 f) (hpos : ∀ x, 0 ≤ f x)
    (hpt : ∀ x, Tendsto (fun j => infDist x (Cj j)) atTop (𝓝 (f x))) :
    ∃ C : Set E, IsClosed C ∧ C.Nonempty ∧ ∀ x, infDist x C = f x := by
  let C : Set E := {x | f x = 0}
  have hCc : IsClosed C := isClosed_eq hlip.continuous continuous_const
  have hnear : ∀ x : E, ∃ y ∈ C, dist x y = f x := by
    intro x
    choose pj hpj heq using fun j => (hcl j).exists_infDist_eq_dist (hne j) x
    have hev : ∀ᶠ j in atTop, pj j ∈ Metric.closedBall x (f x + 1) := by
      filter_upwards [(hpt x).eventually_lt_const (lt_add_one (f x))] with j hj
      simpa only [Metric.mem_closedBall, dist_comm, ← heq] using hj.le
    obtain ⟨y, hy, φ, hφ, hφy⟩ := (isCompact_closedBall x (f x + 1)).tendsto_subseq' hev.frequently
    have hzero : f y = 0 := by
      apply le_antisymm _ (hpos y)
      have hd : Tendsto (fun j => dist y (pj (φ j))) atTop (𝓝 0) := by
        simpa only [dist_self, Function.comp_def] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y)).dist hφy
      exact le_of_tendsto_of_tendsto ((hpt y).comp hφ.tendsto_atTop) hd
        (Eventually.of_forall fun j => infDist_le_dist_of_mem (hpj (φ j)))
    have hd1 : Tendsto (fun j => dist x (pj (φ j))) atTop (𝓝 (dist x y)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).dist hφy
    have hd2 : Tendsto (fun j => dist x (pj (φ j))) atTop (𝓝 (f x)) := by
      simpa only [Function.comp_def, ← heq] using (hpt x).comp hφ.tendsto_atTop
    exact ⟨y, hzero, tendsto_nhds_unique hd1 hd2⟩
  have hCne : C.Nonempty := let ⟨y, hy, _⟩ := hnear 0; ⟨y, hy⟩
  refine ⟨C, hCc, hCne, fun x => ?_⟩
  obtain ⟨y, hy, heq⟩ := hnear x
  apply le_antisymm (heq ▸ infDist_le_dist_of_mem hy)
  rw [Metric.le_infDist hCne]
  intro z hz
  have he := hlip.dist_le_mul x z
  have hfz : f z = 0 := hz
  simpa only [Real.dist_eq, hfz, sub_zero, abs_of_nonneg (hpos x), NNReal.coe_one, one_mul] using he

/- Local compactness of nonempty closed convex sets meeting a fixed bounded
set, the extraction used in geometry.tex:70–101. The topology and the limit
are literal sets and Euclidean distance functions. -/
theorem exists_convex_local_limit {Cj : ℕ → Set E}
    (hcl : ∀ j, IsClosed (Cj j)) (hcv : ∀ j, Convex ℝ (Cj j))
    (hne : ∀ j, (Cj j).Nonempty) {R : ℝ}
    (hbound : ∀ j, infDist (0 : E) (Cj j) ≤ R) :
    ∃ (C : Set E) (φ : ℕ → ℕ), StrictMono φ ∧ IsClosed C ∧ C.Nonempty ∧
      Convex ℝ C ∧ LocalDistanceConverges (fun j => Cj (φ j)) C := by
  obtain ⟨f, φ, hφ, hfL, hfpos, hconv⟩ := exists_distance_function_subsequence hbound
  have hpt : ∀ x, Tendsto (fun j => infDist x (Cj (φ j))) atTop (𝓝 (f x)) := fun x =>
    ((tendstoLocallyUniformly_iff_forall_isCompact.mp hconv) {x} isCompact_singleton).tendsto_at
      (mem_singleton x)
  obtain ⟨C, hCc, hCne, heq⟩ := distance_function_limit_representation
    (fun j => hcl (φ j)) (fun j => hne (φ j)) hfL hfpos hpt
  have hloc : LocalDistanceConverges (fun j => Cj (φ j)) C := by
    unfold LocalDistanceConverges
    simpa only [heq] using hconv
  refine ⟨C, φ, hφ, hCc, hCne, ?_, hloc⟩
  intro x hx y hy a b ha hb hab
  obtain ⟨xj, hxj, hxt⟩ := hloc.exists_approximating (fun j => hcl (φ j)) (fun j => hne (φ j)) hx
  obtain ⟨yj, hyj, hyt⟩ := hloc.exists_approximating (fun j => hcl (φ j)) (fun j => hne (φ j)) hy
  exact hloc.mem_of_tendsto hCc hCne
    (fun j => hcv (φ j) (hxj j) (hyj j) ha hb hab)
    ((hxt.const_smul a).add (hyt.const_smul b))

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

section InteriorLimits
open Filter Metric
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Quantitative inner containment from distance-function closeness. This is
an actual projection argument for convex bodies, not an assumed stability axiom. -/
theorem ball_subset_of_infDist_lt {K : Set E} (hK : IsClosed K)
    (hcv : Convex ℝ K) (hne : K.Nonempty) (a : E) {r : ℝ} (hr : 0 < r)
    (happ : ∀ y ∈ Metric.closedBall a r, infDist y K < r / 2) :
    Metric.ball a (r / 2) ⊆ K := by
  intro x hx
  by_contra hxn
  obtain ⟨p, hp, hpx⟩ := hK.exists_infDist_eq_dist hne x
  have hd : 0 < ‖x - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (by rintro rfl; exact hxn hp))
  have hproj : ∀ z ∈ K, ⟪x - p, z - p⟫_ℝ ≤ 0 := by
    apply (norm_eq_iInf_iff_real_inner_le_zero hcv hp).mp
    simpa only [infDist_eq_iInf, dist_eq_norm] using hpx.symm
  let v : E := ‖x - p‖⁻¹ • (x - p)
  have hvn : ‖v‖ = 1 := by simp [v, norm_smul, hd.ne']
  have hvp : ⟪v, x - p⟫_ℝ = ‖x - p‖ := by
    simp only [v, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have hvproj : ∀ z ∈ K, ⟪v, z - p⟫_ℝ ≤ 0 := by
    intro z hz
    simp only [v, real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hd.le) (hproj z hz)
  let y : E := x + (r / 2) • v
  have hxa : ‖x - a‖ < r / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hx
  have hy : y ∈ Metric.closedBall a r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : y - a = (x - a) + (r / 2) • v := by dsimp [y]; abel
    rw [heq]
    calc
      _ ≤ ‖x - a‖ + ‖(r / 2) • v‖ := norm_add_le _ _
      _ ≤ r := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hr), hvn]; linarith
  obtain ⟨z, hz, hzdist⟩ := hK.exists_infDist_eq_dist hne y
  have hyz : ‖y - z‖ < r / 2 := by simpa [hzdist, dist_eq_norm] using happ y hy
  have hei : ⟪v, y - z⟫_ℝ = ‖x - p‖ + r / 2 - ⟪v, z - p⟫_ℝ := by
    have heq : y - z = (x - p) + (r / 2) • v - (z - p) := by dsimp [y]; abel
    rw [heq, inner_sub_right, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hvp, hvn]
    ring
  have hCS : ⟪v, y - z⟫_ℝ ≤ ‖y - z‖ := by simpa [hvn] using real_inner_le_norm v (y - z)
  have he := hvproj z hz
  rw [hei] at hCS
  linarith

/- An interior ball of the limit has a fixed smaller ball lying in the
interiors of all late approximants. -/

end InteriorLimits

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

theorem fiber_zero {s : Space k} (hs : ∀ i, 0 ≤ s i) : (0 : Space m) ∈ modelFiber C s :=
  h.orthant s hs

theorem fiber_convex (s : Space k) : Convex ℝ (modelFiber C s) := by
  intro x hx y hy a b ha hb hab
  have hh := h.convex hx hy ha hb hab
  change (s, a • x + b • y) ∈ C
  simpa only [Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul] using hh

theorem fiber_closed (s : Space k) : IsClosed (modelFiber C s) :=
  h.closed.preimage (continuous_const.prodMk continuous_id)

theorem fiber_compact {s : Space k} (hs : ∀ i, 0 ≤ s i) : IsCompact (modelFiber C s) := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨h.fiber_closed s, ?_⟩
  have hc := (h.compact_cap (∑ i, s i) (Finset.sum_nonneg fun i _ => hs i)).image continuous_snd
  apply hc.isBounded.subset
  intro y hy
  exact ⟨(s, y), ⟨hy, show ∑ i, s i ≤ ∑ i, s i from le_rfl⟩, rfl⟩

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
theorem fiber_interior_nonempty {s : Space k} (hs : ∀ i, 0 < s i) :
    (interior (modelFiber C s)).Nonempty := by
  obtain ⟨p, hp⟩ := h.interior_nonempty
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
  have hfit : ∀ i : Fin k, ∀ᶠ t : ℝ in 𝓝[>] 0, t * p.1 i < s i := by
    intro i
    exact ((continuous_id.mul continuous_const).tendsto 0 |>.mono_left nhdsWithin_le_nhds).eventually_lt_const
      (by simpa using hs i)
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t ≤ 1 :=
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht0, ht1, hti⟩ := (hpos.and (hsmall.and (Filter.eventually_all.mpr hfit))).exists
  have ht : 0 < t := ht0
  have hsub : Metric.ball (t • p.2) (t * r) ⊆ modelFiber C s := by
    intro y hy
    have hyr : dist (t⁻¹ • y) p.2 < r := by
      have he : t⁻¹ • y - p.2 = t⁻¹ • (y - t • p.2) := by simp [smul_sub, smul_smul, ht.ne']
      rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht), ← dist_eq_norm]
      have hy' : dist y (t • p.2) < t * r := hy
      exact (inv_mul_lt_iff₀ ht).mpr hy'
    have hmem : (p.1, t⁻¹ • y) ∈ C := hball (by simpa [Prod.dist_eq] using hyr)
    have hc := h.convex.smul_mem_of_zero_mem h.zero_mem hmem ⟨ht.le, ht1⟩
    have hc' : (t • p.1, y) ∈ C := by simpa [Prod.smul_mk, smul_smul, ht.ne'] using hc
    have hh := h.add_nonnegative_base hc' (v := s - t • p.1) (by intro i; exact sub_nonneg.mpr (hti i).le)
    simpa [modelFiber] using hh
  exact ⟨t • p.2, mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (Metric.ball_mem_nhds _ (mul_pos ht hr)) hsub)⟩

/- Monotonicity and homothety turn a bound on the distinguished fiber into
a uniform bound on every fixed base box. -/
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
-- module Solutions.OAIQ22_AB.AffineBernstein_ModelLimit
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

open Filter Metric
open scoped Topology Pointwise

variable {k m : ℕ} {Cj : ℕ → Set (Space k × Space m)} {C : Set (Space k × Space m)}

/- Normalized model limits retain the genuine geometric model conditions.
The fixed inner balls prevent collapse; the distinguished-fiber outer bound
controls every cap by the already proved recession/fiber inequalities. -/
theorem LocalDistanceConverges.isModelShape_of_normalized
    (h : LocalDistanceConverges Cj C) (hj : ∀ j, IsModelShape (Cj j))
    (hclosed : IsClosed C) (hconvex : Convex ℝ C) (hne : C.Nonempty)
    {cj : ℕ → Space m} {c : Space m} (hc : Tendsto cj atTop (𝓝 c))
    {R : ℝ}
    (hinner : ∀ j, closedBall (cj j) 1 ⊆ modelFiber (Cj j)
      (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))))
    (houter : ∀ j, modelFiber (Cj j) (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))) ⊆ closedBall 0 R) :
    IsModelShape C := by
  let e : Space k := WithLp.toLp 2 (fun _ => 1)
  have hsupp : ∀ p ∈ C, ∀ i, 0 ≤ p.1 i := by
    intro p hp i
    obtain ⟨pj, hpj, hpt⟩ := h.exists_approximating (fun j => (hj j).closed)
      (fun j => ⟨0, (hj j).zero_mem⟩) hp
    have ht : Tendsto (fun j => (pj j).1 i) atTop (𝓝 (p.1 i)) := by
      exact (((PiLp.continuous_apply 2 (fun _ : Fin k => ℝ) i).comp continuous_fst).tendsto p).comp hpt
    exact ge_of_tendsto ht (Eventually.of_forall fun j => (hj j).support _ (hpj j) i)
  refine ⟨hclosed, hconvex, ?_, ?_, hsupp, ?_⟩
  · have hball : ball (2 • e, c) (1 / 2 : ℝ) ⊆ C := by
      intro q hq
      have hd : dist q.1 (2 • e) < (1 / 2 : ℝ) ∧ dist q.2 c < (1 / 2 : ℝ) := by
        simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using hq
      have hbase : ∀ i, e i ≤ q.1 i := by
        intro i
        have hn := PiLp.norm_apply_le (q.1 - 2 • e) i
        have hi : |q.1 i - 2| < (1 / 2 : ℝ) := by
          have hn' : |q.1 i - 2| ≤ ‖q.1 - 2 • e‖ := by simpa [e, Real.norm_eq_abs] using hn
          exact hn'.trans_lt (by simpa [dist_eq_norm] using hd.1)
        simpa [e] using (by linarith [(abs_lt.mp hi).1] : (1 : ℝ) ≤ q.1 i)
      have hm : ∀ j, (q.1, cj j + (q.2 - c)) ∈ Cj j := by
        intro j
        apply (hj j).fiber_mono hbase
        apply hinner j
        have hn' : ‖q.2 - c‖ ≤ (1 / 2 : ℝ) := by simpa [dist_eq_norm] using hd.2.le
        simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left] using
          hn'.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)
      apply h.mem_of_tendsto hclosed hne hm
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => q.1) atTop (𝓝 q.1)).prodMk_nhds
        (hc.add_const (q.2 - c))
    exact ⟨(2 • e, c), mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 2)) hball)⟩
  · intro s hs
    exact h.mem_of_tendsto hclosed hne (fun j => (hj j).orthant s hs) tendsto_const_nhds
  · intro T hT
    let B : Set (Space k) := (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).symm ''
      Icc (fun _ : Fin k => (0 : ℝ)) (fun _ => T)
    have hB : IsCompact B := isCompact_Icc.image (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).symm.continuous
    have hcapclosed : IsClosed (C ∩ {p | ∑ i, p.1 i ≤ T}) := hclosed.inter
      (isClosed_le (by fun_prop) continuous_const)
    apply (hB.prod (isCompact_closedBall (0 : Space m) ((T + 1) * R))).of_isClosed_subset hcapclosed
    rintro p ⟨hp, hpT⟩
    have hsT : ∀ i, p.1 i ≤ T := by
      intro i
      exact (Finset.single_le_sum (fun a _ => hsupp p hp a) (Finset.mem_univ i)).trans hpT
    refine ⟨?_, ?_⟩
    · refine ⟨fun i => p.1 i, ⟨(fun i => hsupp p hp i), (fun i => hsT i)⟩, ?_⟩
      rfl
    · obtain ⟨pj, hpj, hpt⟩ := h.exists_approximating (fun j => (hj j).closed)
        (fun j => ⟨0, (hj j).zero_mem⟩) hp
      have hcoord : ∀ i : Fin k, ∀ᶠ j in atTop, (pj j).1 i ≤ T + 1 := by
        intro i
        have ht : Tendsto (fun j => (pj j).1 i) atTop (𝓝 (p.1 i)) :=
          (((PiLp.continuous_apply 2 (fun _ : Fin k => ℝ) i).comp continuous_fst).tendsto p).comp hpt
        exact ht.eventually_le_const (by linarith [hsT i])
      have hb : ∀ᶠ j in atTop, ‖(pj j).2‖ ≤ (T + 1) * R := by
        filter_upwards [Filter.eventually_all.mpr hcoord] with j hbase
        exact (hj j).fiber_box_bound (by linarith) (houter j) hbase (hpj j)
      have ht := (((continuous_snd.tendsto p).comp hpt).norm)
      simpa only [mem_closedBall, dist_zero_right] using le_of_tendsto ht hb

/- The shrinking factor avoids any positivity assumption on approximating
base coordinates. It tends to one and contracts each coordinate below one. -/
theorem model_base_contraction (s : Space k) (i : Fin k) :
    (1 + ‖s - WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))‖)⁻¹ * s i ≤ 1 := by
  have hn := PiLp.norm_apply_le (s - WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))) i
  have hi : s i - 1 ≤ ‖s - WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))‖ :=
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hn)
  apply (inv_mul_le_iff₀ (by positivity : 0 < 1 + ‖s - WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))‖)).mpr
  linarith

/- Exact-fiber approximation in geometry.tex:285–300. The actual contracting
points are used, not an assumed commutation of slicing with local limits. -/
theorem LocalDistanceConverges.exists_exact_fiber_approximating
    (h : LocalDistanceConverges Cj C) (hj : ∀ j, IsModelShape (Cj j))
    {y : Space m} (hy : y ∈ modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)))) :
    ∃ yj : ℕ → Space m,
      (∀ j, yj j ∈ modelFiber (Cj j) (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)))) ∧
      Tendsto yj atTop (𝓝 y) := by
  let e : Space k := WithLp.toLp 2 (fun _ => 1)
  obtain ⟨pj, hpj, hpt⟩ := h.exists_approximating (fun j => (hj j).closed)
    (fun j => ⟨0, (hj j).zero_mem⟩) hy
  let a : ℕ → ℝ := fun j => (1 + ‖(pj j).1 - e‖)⁻¹
  have ha0 : ∀ j, 0 < a j := fun j => inv_pos.mpr (by positivity)
  have ha1 : ∀ j, a j ≤ 1 := fun j => inv_le_one_of_one_le₀ (by linarith [norm_nonneg ((pj j).1 - e)])
  refine ⟨fun j => a j • (pj j).2, ?_, ?_⟩
  · intro j
    have hh := (hj j).convex.smul_mem_of_zero_mem (hj j).zero_mem (hpj j) ⟨(ha0 j).le, ha1 j⟩
    have hbase : ∀ i, (a j • (pj j).1) i ≤ e i := by
      intro i
      simpa [a, e] using model_base_contraction (pj j).1 i
    exact (hj j).fiber_mono hbase hh
  · have hp1 : Tendsto (fun j => (pj j).1 - e) atTop (𝓝 0) := by
      simpa [e] using ((continuous_fst.tendsto _).comp hpt).sub_const e
    have ha : Tendsto a atTop (𝓝 1) := by
      simpa [a, one_div] using ((tendsto_const_nhds.add hp1.norm).inv₀ (by norm_num : (1:ℝ) + ‖(0 : Space k)‖ ≠ 0))
    simpa using ha.smul ((continuous_snd.tendsto _).comp hpt)

/- Uniform reverse Hausdorff inclusion follows by compactness of the actual
positive limit fiber and the preceding exact approximations. -/
theorem LocalDistanceConverges.eventually_infDist_fiber_lt_uniform
    (h : LocalDistanceConverges Cj C) (hj : ∀ j, IsModelShape (Cj j))
    (hC : IsModelShape C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ y ∈ modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))),
      infDist y (modelFiber (Cj j) (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)))) < ε := by
  classical
  let e : Space k := WithLp.toLp 2 (fun _ => 1)
  let F := modelFiber C e
  have hc : IsCompact F := hC.fiber_compact (by simp [e])
  have hat : ∀ y ∈ F, ∀ᶠ j in atTop, infDist y (modelFiber (Cj j) e) < ε / 2 := by
    intro y hy
    obtain ⟨yj, hyj, hyt⟩ := h.exists_exact_fiber_approximating hj hy
    have hd : Tendsto (fun j => dist y (yj j)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y)).dist hyt
    filter_upwards [hd.eventually_lt_const (half_pos hε)] with j hj
    exact (infDist_le_dist_of_mem (hyj j)).trans_lt hj
  obtain ⟨t, htF, ht⟩ := hc.elim_nhds_subcover (fun y => Metric.ball y (ε / 2))
    (fun y _ => Metric.ball_mem_nhds y (half_pos hε))
  filter_upwards [(t.eventually_all).mpr (fun y hy => hat y (htF y hy))] with j hj y hy
  obtain ⟨z, hzt, hyz⟩ := mem_iUnion₂.mp (ht hy)
  have hd : dist y z < ε / 2 := hyz
  exact (infDist_le_infDist_add_dist (x := y) (y := z)).trans_lt (by linarith [hj z hzt])

/- Exact-fiber Hausdorff convergence with a common outer radius. This is
stronger than pointwise local convergence but follows from the model recession
structure; arbitrary slices of arbitrary converging bodies need not converge. -/
theorem LocalDistanceConverges.zero_mem_frontier_fiber_of_asymmetry
    (h : LocalDistanceConverges Cj C) (hj : ∀ j, IsModelShape (Cj j))
    (hC : IsModelShape C) {R : ℝ}
    (hR : ∀ j, modelFiber (Cj j) (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))) ⊆ closedBall 0 R)
    (hfail : ∀ j : ℕ, 1 ≤ j →
      ¬ -(modelFiber (Cj j) (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)))) ⊆
        (j : ℝ) • modelFiber (Cj j) (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)))) :
    (0 : Space m) ∈ frontier (modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)))) := by
  let e : Space k := WithLp.toLp 2 (fun _ => 1)
  let F : Set (Space m) := modelFiber C e
  have hz : (0 : Space m) ∈ F := hC.fiber_zero (by simp [e])
  have hnint : (0 : Space m) ∉ interior F := by
    intro hzi
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior 0 hzi
    have hclosedball : closedBall (0 : Space m) (r / 2) ⊆ F :=
      (closedBall_subset_ball (by linarith)).trans (hball.trans interior_subset)
    have he := h.eventually_infDist_fiber_lt_uniform hj hC (show 0 < r / 4 by linarith)
    have hinner : ∀ᶠ j in atTop, ball (0 : Space m) (r / 4) ⊆ modelFiber (Cj j) e := by
      filter_upwards [he] with j hjdist
      simpa only [div_div, show (2 : ℝ) * 2 = 4 by norm_num] using
        (ball_subset_of_infDist_lt ((hj j).fiber_closed e) ((hj j).fiber_convex e)
          ⟨0, (hj j).fiber_zero (by simp [e])⟩ 0 (half_pos hr)
          (fun y hy => by
            rw [show r / 2 / 2 = r / 4 by ring]
            exact hjdist y (hclosedball hy)))
    obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (4 * R / r))
    obtain ⟨j, hji, hjN⟩ := (hinner.and (eventually_ge_atTop N)).exists
    have hjlarge : max 1 (4 * R / r) < (j : ℝ) := hN.trans_le (by exact_mod_cast hjN)
    have hj1 : 1 ≤ j := by have he := (le_max_left 1 (4 * R / r)).trans_lt hjlarge; exact_mod_cast he.le
    have hjpos : 0 < (j : ℝ) := by
      have hh : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      linarith
    have hmult : 4 * R < (j : ℝ) * r := (div_lt_iff₀ hr).mp
      ((le_max_right 1 (4 * R / r)).trans_lt hjlarge)
    apply hfail j hj1
    intro x hx
    change -x ∈ modelFiber (Cj j) e at hx
    have hynorm : ‖x‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hR j hx
    have hm : (j : ℝ)⁻¹ • x ∈ modelFiber (Cj j) e := by
      apply hji
      rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hjpos)]
      apply (inv_mul_lt_iff₀ hjpos).mpr
      nlinarith
    exact mem_smul_set.mpr ⟨(j : ℝ)⁻¹ • x, hm, by simp [smul_smul, hjpos.ne']⟩
  rw [frontier, (hC.fiber_closed e).closure_eq]
  exact ⟨hz, hnint⟩

/- A fiber support at zero extends to the whole model by the same actual
contraction and recession operation used for exact-fiber approximation. -/
theorem IsModelShape.support_from_fiber (hC : IsModelShape C)
    (ell : Space m →L[ℝ] ℝ)
    (hell : ∀ y ∈ modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))), 0 ≤ ell y) :
    ∀ p ∈ C, 0 ≤ ell p.2 := by
  intro p hp
  let e : Space k := WithLp.toLp 2 (fun _ => 1)
  let a : ℝ := (1 + ‖p.1 - e‖)⁻¹
  have ha : 0 < a := inv_pos.mpr (by positivity)
  have ha1 : a ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg (p.1 - e)])
  have hm := hC.convex.smul_mem_of_zero_mem hC.zero_mem hp ⟨ha.le, ha1⟩
  have hbase : ∀ i, (a • p.1) i ≤ e i := by
    intro i; simpa [a, e] using model_base_contraction p.1 i
  have hs := hell (a • p.2) (hC.fiber_mono hbase hm)
  simpa only [map_smul, smul_eq_mul, mul_nonneg_iff_of_pos_left ha] using hs

/- The nonzero supporting functional whose new positive coordinate is used
in the thin-slice blowup. Hahn–Banach is reused from pinned Mathlib. -/
theorem IsModelShape.exists_global_support_of_zero_boundary (hC : IsModelShape C)
    (hzero : (0 : Space m) ∉ interior (modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ))))) :
    ∃ ell : Space m →L[ℝ] ℝ, ell ≠ 0 ∧ (∀ p ∈ C, 0 ≤ ell p.2) := by
  obtain ⟨f, hf, hF⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (hC.fiber_convex (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)))) hzero
    (hC.fiber_interior_nonempty (by simp))
  refine ⟨-f, neg_ne_zero.mpr hf, hC.support_from_fiber (-f) ?_⟩
  intro y hy
  simpa only [neg_apply, map_zero, neg_nonneg] using hF y hy

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_SupportCoordinates
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

section SupportCoordinates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- A nonzero real functional has full range. -/
theorem real_functional_surjective (ell : E →L[ℝ] ℝ) (hne : ell ≠ 0) :
    Function.Surjective ell := by
  have hx : ∃ x, ell x ≠ 0 := by
    by_contra h
    apply hne
    ext x
    simpa using not_exists.mp h x
  obtain ⟨x, hx⟩ := hx
  intro r
  refine ⟨(r / ell x) • x, ?_⟩
  simp [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx]

/- A nonzero support is strictly positive at every interior point. -/
theorem support_pos_of_interior {F : Set E} (ell : E →L[ℝ] ℝ) (hne : ell ≠ 0)
    (hs : ∀ y ∈ F, 0 ≤ ell y) {w : E} (hw : w ∈ interior F) : 0 < ell w := by
  have hopen : IsOpen (ell '' interior F) :=
    ell.toLinearMap.isOpenMap_of_finiteDimensional (real_functional_surjective ell hne) _ isOpen_interior
  have hi : ell w ∈ interior (Set.Ici (0 : ℝ)) := by
    apply hopen.subset_interior_iff.mpr ?_ ⟨w, hw, rfl⟩
    rintro y ⟨x, hx, rfl⟩
    exact hs x (interior_subset hx)
  simpa only [interior_Ici, Set.mem_Ioi] using hi

variable [FiniteDimensional ℝ E]

/- The literal split along a normalized support vector. The second component
is the kernel of the support; no quotient or degenerate coordinate is used. -/
theorem exists_support_coordinates {m : ℕ} {F : Set (Space m)}
    (hi : (interior F).Nonempty) (ell : Space m →L[ℝ] ℝ) (hne : ell ≠ 0)
    (hs : ∀ y ∈ F, 0 ≤ ell y) :
    ∃ (d : ℕ) (A : Space m ≃L[ℝ] ℝ × Space d),
      m = d + 1 ∧ (∀ y ∈ F, 0 ≤ (A y).1) ∧
      (1, 0) ∈ interior (A '' F) := by
  classical
  obtain ⟨w, hw⟩ := hi
  have hp := support_pos_of_interior ell hne hs hw
  let f : Space m →L[ℝ] ℝ := (ell w)⁻¹ • ell
  have hwf : f w = 1 := by simp [f, hp.ne']
  let d := Module.finrank ℝ f.ker
  let L : f.ker ≃L[ℝ] Space d :=
    (stdOrthonormalBasis ℝ f.ker).repr.toContinuousLinearEquiv
  let A : Space m ≃L[ℝ] ℝ × Space d :=
    (splitFunctionalEquiv f w hwf).trans ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr L)
  have hAw : A w = (1, 0) := by simp [A]
  refine ⟨d, A, ?_, ?_, ?_⟩
  · have he := A.toLinearEquiv.finrank_eq
    simpa [Module.finrank_prod, d, add_comm] using he
  · intro y hy
    change 0 ≤ (ell w)⁻¹ * ell y
    exact mul_nonneg (inv_nonneg.mpr hp.le) (hs y hy)
  · have himage : A w ∈ A.toHomeomorph '' interior F := ⟨w, hw, rfl⟩
    rw [A.toHomeomorph.image_interior] at himage
    simpa [hAw] using himage

end SupportCoordinates

/- Append one real base coordinate, placing it first in Fin (k+1). -/

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

section AffineFamily
open Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/- For distance functions, pointwise convergence is automatically locally
uniform, by the common unit Lipschitz constant and a finite compact cover. -/
omit [NormedSpace ℝ E] in
theorem LocalDistanceConverges.of_pointwise {Cj : ℕ → Set E} {C : Set E}
    (hpt : ∀ x, Tendsto (fun j => infDist x (Cj j)) atTop (𝓝 (infDist x C))) :
    LocalDistanceConverges Cj C := by
  classical
  apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨t, htK, ht⟩ := hK.elim_nhds_subcover (fun x => ball x (ε / 3))
    (fun x _ => ball_mem_nhds x (by positivity))
  have he : ∀ x ∈ t, ∀ᶠ j in atTop, dist (infDist x C) (infDist x (Cj j)) < ε / 3 := by
    intro x hx
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hpt x) (ε / 3) (by positivity)
    filter_upwards [eventually_ge_atTop N] with j hj
    simpa [dist_comm] using hN j hj
  filter_upwards [(t.eventually_all).mpr he] with j hj x hx
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht hx)
  have hd : dist x y < ε / 3 := hxy
  have h1 : dist (infDist x C) (infDist y C) ≤ dist x y := by
    simpa using (lipschitz_infDist_pt C).dist_le_mul x y
  have h2 : dist (infDist y (Cj j)) (infDist x (Cj j)) ≤ dist x y := by
    simpa [dist_comm] using (lipschitz_infDist_pt (Cj j)).dist_le_mul y x
  calc
    dist (infDist x C) (infDist x (Cj j)) ≤
        dist (infDist x C) (infDist y C) + dist (infDist y C) (infDist y (Cj j)) +
          dist (infDist y (Cj j)) (infDist x (Cj j)) := dist_triangle4 _ _ _ _
    _ < ε := by linarith [hj y hyt]

/- Fixed changes of coordinates preserve local set convergence. A proper
homeomorphism suffices: compact preimages supply the lower distance bound and
actual approximating points supply the upper bound. In particular this applies
to every fixed invertible affine change of coordinates. -/
omit [NormedSpace ℝ E] in
theorem LocalDistanceConverges.homeomorph
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
    {Cj : ℕ → Set E} {C : Set E} (h : LocalDistanceConverges Cj C)
    (hcl : IsClosed C) (hne : C.Nonempty)
    (hclj : ∀ j, IsClosed (Cj j)) (hnej : ∀ j, (Cj j).Nonempty)
    (A : E ≃ₜ F) : LocalDistanceConverges (fun j => A '' Cj j) (A '' C) := by
  apply LocalDistanceConverges.of_pointwise
  intro x
  apply tendsto_order.2
  constructor
  · intro a ha
    by_cases haneg : a < 0
    · exact Eventually.of_forall fun j => haneg.trans_le infDist_nonneg
    let S : Set E := A.symm '' closedBall x a
    have hSc : IsCompact S := (isCompact_closedBall x a).image A.symm.continuous
    have hdis : Disjoint C S := by
      rw [Set.disjoint_left]
      rintro y hy ⟨z, hz, rfl⟩
      have he : infDist x (A '' C) ≤ dist x z := by
        apply infDist_le_dist_of_mem
        exact ⟨A.symm z, hy, A.apply_symm_apply z⟩
      have hz' : dist x z ≤ a := by simpa [mem_closedBall, dist_comm] using hz
      linarith
    filter_upwards [h.eventually_disjoint_compact hcl hne hSc hdis] with j hj
    obtain ⟨z, hz, hdist⟩ := (A.isClosedMap _ (hclj j)).exists_infDist_eq_dist ((hnej j).image A) x
    rw [hdist]
    by_contra hn
    obtain ⟨y, hy, rfl⟩ := hz
    apply Set.disjoint_left.mp hj hy
    exact ⟨A y, by simpa [mem_closedBall, dist_comm] using not_lt.mp hn, A.symm_apply_apply y⟩
  · intro b hb
    obtain ⟨z, hz, hdist⟩ := (A.isClosedMap _ hcl).exists_infDist_eq_dist (hne.image A) x
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨yj, hyj, hyt⟩ := h.exists_approximating hclj hnej hy
    have ht : Tendsto (fun j => dist x (A (yj j))) atTop (𝓝 (dist x (A y))) :=
      tendsto_const_nhds.dist ((A.continuous.tendsto y).comp hyt)
    have hb' : dist x (A y) < b := by simpa [hdist] using hb
    filter_upwards [ht.eventually_lt_const hb'] with j hj
    exact (infDist_le_dist_of_mem (s := A '' Cj j) ⟨yj j, hyj j, rfl⟩).trans_lt hj

/- A diagonal choice of approximating bodies. The bounds on the growing
closed balls are the literal metric construction behind the affine-family
closure assertion, not an assumed transitivity of sequential limits. -/
omit [NormedSpace ℝ E] in
theorem LocalDistanceConverges.diagonal
    {Cj : ℕ → Set E} {C : Set E} {D : ℕ → ℕ → Set E}
    (h : LocalDistanceConverges Cj C)
    (hD : ∀ j, LocalDistanceConverges (D j) (Cj j)) :
    ∃ q : ℕ → ℕ, LocalDistanceConverges (fun j => D j (q j)) C := by
  have hgood : ∀ j : ℕ, ∃ q : ℕ, ∀ x ∈ closedBall (0 : E) (j + 1 : ℝ),
      dist (infDist x (Cj j)) (infDist x (D j q)) < (j + 1 : ℝ)⁻¹ := by
    intro j
    have hu := tendstoLocallyUniformly_iff_forall_isCompact.mp (hD j)
      (closedBall (0 : E) (j + 1 : ℝ)) (isCompact_closedBall _ _)
    exact (Metric.tendstoUniformlyOn_iff.mp hu _ (by positivity)).exists
  choose q hq using hgood
  refine ⟨q, LocalDistanceConverges.of_pointwise ?_⟩
  intro x
  have hdist : Tendsto (fun j => dist (infDist x (Cj j)) (infDist x (D j (q j)))) atTop (𝓝 0) := by
    have hsmall : Tendsto (fun j : ℕ => (j + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    have he : ∀ᶠ j in atTop, dist (infDist x (Cj j)) (infDist x (D j (q j))) ≤ (j + 1 : ℝ)⁻¹ := by
      filter_upwards [eventually_ge_atTop N] with j hj
      apply (hq j x ?_).le
      rw [mem_closedBall, dist_zero_right]
      have hn : (N : ℝ) ≤ j := by exact_mod_cast hj
      linarith
    exact squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) he hsmall
  exact (h.pointwise x).congr_dist hdist

/- Literal full-dimensional affine local-limit family of geometry.tex:87.
The affine maps may vary along the approximating sequence. -/

namespace InAffineLimitFamily
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [ProperSpace G]
  {D : Set E} {C : Set F}

omit [ProperSpace E] [ProperSpace F] in
theorem nonempty (h : InAffineLimitFamily D C) : C.Nonempty :=
  h.interior_nonempty.mono interior_subset

omit [ProperSpace E] in
theorem affine_image (h : InAffineLimitFamily D C)
    (hD : IsClosed D) (hneD : D.Nonempty) (B : F ≃ᴬ[ℝ] G) :
    InAffineLimitFamily D (B '' C) := by
  obtain ⟨A, hA⟩ := h.approximation
  refine ⟨B.toHomeomorph.isClosedMap _ h.closed,
    h.convex.affine_image B.toAffineEquiv.toAffineMap, ?_, ?_⟩
  · change (interior (B.toHomeomorph '' C)).Nonempty
    rw [← B.toHomeomorph.image_interior]
    exact h.interior_nonempty.image B.toHomeomorph
  · refine ⟨fun j => (A j).trans B, ?_⟩
    convert hA.homeomorph h.closed h.nonempty
      (fun j => (A j).toHomeomorph.isClosedMap _ hD)
      (fun j => hneD.image (A j)) B.toHomeomorph using 1
    · ext j x
      simp only [Set.mem_image, ContinuousAffineEquiv.trans_apply]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨A j y, ⟨y, hy, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨z, hz, rfl⟩
    · rfl

omit [ProperSpace E] in
theorem diagonal_closure {Cj : ℕ → Set F}
    (hj : ∀ j, InAffineLimitFamily D (Cj j))
    (h : LocalDistanceConverges Cj C) (hc : IsClosed C) (hv : Convex ℝ C)
    (hi : (interior C).Nonempty) : InAffineLimitFamily D C := by
  choose A hA using fun j => (hj j).approximation
  obtain ⟨q, hq⟩ := h.diagonal hA
  exact ⟨hc, hv, hi, fun j => A j (q j), hq⟩

end InAffineLimitFamily

end AffineFamily

open scoped Pointwise

/- The coordinate action of the actual matrix linear equivalence. -/
theorem matrixLinearEquiv_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsUnit A.det) (x : Space n) (i : Fin n) :
    Matrix.toLinearEquiv (EuclideanSpace.basisFun (Fin n) ℝ).toBasis A hA x i =
      A.mulVec x i := by
  simp [Matrix.toLinearEquiv_apply, Matrix.toLin_apply,
    EuclideanSpace.basisFun_apply, Pi.single_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      Matrix.mulVec, dotProduct]

/- A convex combination allowing unused mass at the origin. -/
theorem convex_sum_mem_le_one {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι] {K : Set E} (hK : Convex ℝ K) (h0 : (0 : E) ∈ K)
    (c : ι → ℝ) (v : ι → E) (hc : ∀ i, 0 ≤ c i)
    (hsum : ∑ i, c i ≤ 1) (hv : ∀ i, v i ∈ K) : (∑ i, c i • v i) ∈ K := by
  classical
  have hn : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc i
  by_cases hz : ∑ i, c i = 0
  · have hc0 : ∀ i, c i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hc i)).mp hz i (Finset.mem_univ i)
    simpa [hc0] using h0
  · have hp : 0 < ∑ i, c i := lt_of_le_of_ne hn (Ne.symm hz)
    have hm := hK.centerMass_mem (t := Finset.univ) (w := c) (z := v)
      (fun i _ => hc i) hp (fun i _ => hv i)
    have he := hK.smul_mem_of_zero_mem h0 hm ⟨hn, hsum⟩
    simpa [Finset.centerMass, smul_smul, hz] using he

/- The cross-polytope spanned by any points of a symmetric convex body lies
in that body. This is the inner-inclusion half of max-determinant normalization. -/
theorem symmetric_convex_sum_mem {n : ℕ} {K : Set (Space n)}
    (hK : Convex ℝ K) (h0 : (0 : Space n) ∈ K)
    (hneg : ∀ x ∈ K, -x ∈ K) (v : Fin n → Space n)
    (hv : ∀ i, v i ∈ K) (c : Fin n → ℝ) (hc : ∑ i, |c i| ≤ 1) :
    (∑ i, c i • v i) ∈ K := by
  classical
  let w : Fin n → Space n := fun i => if 0 ≤ c i then v i else -v i
  have hw (i : Fin n) : w i ∈ K := by
    dsimp [w]; split_ifs <;> first | exact hv i | exact hneg _ (hv i)
  have he (i : Fin n) : |c i| • w i = c i • v i := by
    dsimp [w]; split_ifs with hi
    · rw [abs_of_nonneg hi]
    · rw [abs_of_neg (lt_of_not_ge hi), neg_smul, smul_neg, neg_neg]
  simpa only [he] using convex_sum_mem_le_one hK h0 (fun i => |c i|) w
    (fun i => abs_nonneg _) hc hw

/- The exact ℓ¹/Euclidean comparison used for the inner ball. -/
theorem sum_abs_coordinate_le {n : ℕ} (x : Space n) :
    ∑ i, |x i| ≤ Real.sqrt n * ‖x‖ := by
  have he := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i : Fin n => |x i|)
    (fun _ => (1 : ℝ))
  have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) x
  simpa only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, one_mul, ← Real.norm_eq_abs, ← hn, Real.sqrt_sq (norm_nonneg _),
    mul_comm] using he

/- The exact ℓ∞/Euclidean comparison used for the outer ball. -/
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
theorem exists_max_det_columns {n : ℕ} {K : Set (Space n)}
    (hK : IsCompact K) {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall (0 : Space n) r ⊆ K) :
    ∃ v : Fin n → Space n, (∀ i, v i ∈ K) ∧
      (Matrix.det (fun i j => v j i) ≠ 0) ∧
      ∀ w : Fin n → Space n, (∀ i, w i ∈ K) →
        |Matrix.det (fun i j => w j i)| ≤ |Matrix.det (fun i j => v j i)| := by
  classical
  let S : Set (Fin n → Space n) := {v | ∀ i, v i ∈ K}
  have hS : IsCompact S := isCompact_pi_infinite (fun _ => hK)
  let w : Fin n → Space n := fun j => r • EuclideanSpace.single j 1
  have hw : w ∈ S := by
    intro i
    apply hball
    simp [w, Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr]
  have hM : (fun i j => w j i) = (r : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [w, Matrix.one_apply]
  have hd : Matrix.det (fun i j => w j i) ≠ 0 := by rw [hM]; simp [hr.ne']
  obtain ⟨v, hv, hmax⟩ := hS.exists_isMaxOn ⟨w, hw⟩
    (show Continuous (fun v : Fin n → Space n => |Matrix.det (fun i j => v j i)|) by
      fun_prop).continuousOn
  refine ⟨v, hv, ?_, fun w hw => hmax hw⟩
  intro hz
  have hh := hmax hw
  change |Matrix.det (fun i j => w j i)| ≤ |Matrix.det (fun i j => v j i)| at hh
  rw [hz, abs_zero] at hh
  exact hd (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))

/- Maximal determinant makes each inverse coordinate of a body point at most
one. The proof is the literal one-column replacement identity. -/
theorem maxdet_coordinate_bound {n : ℕ} {K : Set (Space n)}
    (v : Fin n → Space n) (hv : ∀ i, v i ∈ K)
    (hd : Matrix.det (fun i j => v j i) ≠ 0)
    (hmax : ∀ w : Fin n → Space n, (∀ i, w i ∈ K) →
      |Matrix.det (fun i j => w j i)| ≤ |Matrix.det (fun i j => v j i)|) :
    ∃ q : Space n ≃ₗ[ℝ] Space n,
      (∀ x : Space n, q x = ∑ i, x i • v i) ∧
      ∀ x ∈ K, ∀ i, |q.symm x i| ≤ 1 := by
  classical
  let M : Matrix (Fin n) (Fin n) ℝ := fun i j => v j i
  let q : Space n ≃ₗ[ℝ] Space n :=
    Matrix.toLinearEquiv (EuclideanSpace.basisFun (Fin n) ℝ).toBasis M
      (isUnit_iff_ne_zero.mpr hd)
  have hq (x : Space n) : q x = ∑ i, x i • v i := by
    ext j
    rw [show q x j = M.mulVec x j from matrixLinearEquiv_apply M _ x j]
    simp [Matrix.mulVec, dotProduct, M, mul_comm]
  refine ⟨q, hq, ?_⟩
  intro x hx j
  have hw : ∀ i, Function.update v j x i ∈ K := by
    intro i
    by_cases h : i = j
    · simpa [h] using hx
    · simpa [Function.update_of_ne h] using hv i
  have hm := hmax (Function.update v j x) hw
  have hcol : (fun i k => Function.update v j x k i) = M.updateCol j x := by
    ext i k
    simp [Matrix.updateCol, M, Function.update_apply]
    split_ifs <;> rfl
  have hsum : (fun k => ∑ i, (q.symm x i) • M k i) = (fun k => x k) := by
    funext k
    have he := congrArg (fun p : Space n => p k) (hq (q.symm x))
    simpa [M, mul_comm] using he.symm
  rw [hcol] at hm
  change |(M.updateCol j (fun k => x k)).det| ≤ |M.det| at hm
  rw [← hsum, Matrix.det_updateCol_sum, smul_eq_mul, abs_mul] at hm
  have hdpos : 0 < |M.det| := abs_pos.mpr hd
  change |q.symm x j| * |M.det| ≤ |M.det| at hm
  exact (mul_le_mul_iff_left₀ hdpos).mp (by simpa using hm)

/- The symmetric max-determinant normalization, with the exact weaker radius
n sufficient for all centered normalizations used in the source. -/
theorem symmetric_body_normalization {n : ℕ} (hn : 1 ≤ n)
    {K : Set (Space n)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (h0 : (0 : Space n) ∈ K) (hneg : ∀ x ∈ K, -x ∈ K)
    {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall (0 : Space n) r ⊆ K) :
    ∃ A : Space n ≃L[ℝ] Space n,
      Metric.closedBall 0 1 ⊆ A '' K ∧ A '' K ⊆ Metric.closedBall 0 n := by
  obtain ⟨v, hv, hd, hmax⟩ := exists_max_det_columns hK hr hball
  obtain ⟨q, hq, hh⟩ := maxdet_coordinate_bound v hv hd hmax
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  let S := LinearEquiv.smulOfNeZero ℝ (Space n) (Real.sqrt n) hspos.ne'
  let A := (q.symm.trans S).toContinuousLinearEquiv
  have hA (x : Space n) : A x = Real.sqrt n • q.symm x := rfl
  refine ⟨A, ?_, ?_⟩
  · intro x hx
    have hxn : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
    let y : Space n := (Real.sqrt n)⁻¹ • x
    have hy : ∑ i, |y i| ≤ 1 := by
      calc
        _ ≤ Real.sqrt n * ‖y‖ := sum_abs_coordinate_le y
        _ = ‖x‖ := by simp [y, norm_smul, Real.norm_eq_abs, abs_of_pos hspos,
          hspos.ne']
        _ ≤ 1 := hxn
    have hmem : q y ∈ K := hq y ▸ symmetric_convex_sum_mem hconv h0 hneg v hv
      (fun i => y i) hy
    refine ⟨q y, hmem, ?_⟩
    rw [hA, LinearEquiv.symm_apply_apply]
    simp [y, smul_smul, hspos.ne']
  · rintro x ⟨y, hy, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, hA, norm_smul,
      Real.norm_eq_abs, abs_of_pos hspos]
    calc
      _ ≤ Real.sqrt n * Real.sqrt n := mul_le_mul_of_nonneg_left
        (norm_le_sqrt_card_of_coordinate_le _ (hh y hy)) hspos.le
      _ = n := Real.mul_self_sqrt hnpos.le

open scoped Pointwise

/- Exact centered normalization in geometry.tex (2/(C+1), 2n), proved
without importing John's theorem: first normalize the symmetric difference
body, then use the actual balance inclusion. -/
theorem centered_body_normalization {n : ℕ} (hn : 1 ≤ n)
    {K : Set (Space n)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hint : (interior K).Nonempty) (h0 : (0 : Space n) ∈ K)
    {C : ℝ} (hC : 1 ≤ C) (hbal : -K ⊆ C • K) :
    ∃ A : Space n ≃L[ℝ] Space n,
      Metric.closedBall 0 (2 / (C + 1)) ⊆ A '' K ∧
      A '' K ⊆ Metric.closedBall 0 (2 * n) := by
  let D := K - K
  have hDeq : D = (fun p : Space n × Space n => p.1 - p.2) '' (K ×ˢ K) := by
    ext x
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  have hDc : IsCompact D := by
    rw [hDeq]
    exact (hK.prod hK).image (continuous_fst.sub continuous_snd)
  have hDv : Convex ℝ D := hconv.sub hconv
  have hD0 : (0 : Space n) ∈ D := ⟨0, h0, 0, h0, sub_self _⟩
  have hDneg : ∀ x ∈ D, -x ∈ D := by
    rintro x ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, hb, a, ha, (neg_sub _ _).symm⟩
  obtain ⟨p, hp⟩ := hint
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (mem_interior_iff_mem_nhds.mp hp)
  have hDb : Metric.closedBall (0 : Space n) r ⊆ D := by
    intro x hx
    have hpx : p + x ∈ K := hball (by simpa [Metric.mem_closedBall, dist_eq_norm] using hx)
    exact ⟨p + x, hpx, p, interior_subset hp, by abel_nf⟩
  obtain ⟨L, hLin, hLout⟩ := symmetric_body_normalization hn hDc hDv hD0 hDneg hr hDb
  have hCp : 0 < C + 1 := by linarith
  have hscale : ∀ d ∈ D, (C + 1)⁻¹ • d ∈ K := by
    rintro d ⟨a, ha, b, hb, rfl⟩
    have hnb : -b ∈ -K := by simpa using hb
    obtain ⟨z, hz, hzb⟩ := Set.mem_smul_set.mp (hbal hnb)
    have h := hconv ha hz (inv_nonneg.mpr hCp.le)
      (div_nonneg (by linarith : 0 ≤ C) hCp.le)
      (show (C + 1)⁻¹ + C / (C + 1) = 1 by field_simp; ring)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rw [smul_sub, sub_eq_add_neg, ← smul_neg, ← hzb, smul_smul]
    congr 1
    simp [div_eq_mul_inv, mul_comm]
  let A := (L.toLinearEquiv.trans
    (LinearEquiv.smulOfNeZero ℝ (Space n) 2 (by norm_num))).toContinuousLinearEquiv
  have hA (x : Space n) : A x = (2 : ℝ) • L x := rfl
  refine ⟨A, ?_, ?_⟩
  · intro x hx
    have hn : ‖x‖ ≤ 2 / (C + 1) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    have hy : ((C + 1) / 2) • x ∈ Metric.closedBall (0 : Space n) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < (C + 1) / 2)]
      have := mul_le_mul_of_nonneg_left hn (show 0 ≤ (C + 1) / 2 by positivity)
      have he : (C + 1) / 2 * (2 / (C + 1)) = 1 := by field_simp
      simpa [he] using this
    obtain ⟨d, hd, he⟩ := hLin hy
    refine ⟨(C + 1)⁻¹ • d, hscale d hd, ?_⟩
    rw [hA, map_smul, he, smul_smul, smul_smul]
    have heq : 2 * ((C + 1)⁻¹ * ((C + 1) / 2)) = 1 := by field_simp
    rw [mul_assoc, heq, one_smul]
  · rintro x ⟨y, hy, rfl⟩
    have hyd : y ∈ D := ⟨y, hy, 0, h0, sub_zero _⟩
    have hn : ‖L y‖ ≤ n := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hLout ⟨y, hyd, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, hA, norm_smul]
    simp only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    linarith

/- A dimension-only inscribed ball in the standard simplex. This allows
noncentered model fibers to be normalized without importing John's theorem. -/
theorem simplex_ball_coordinates {n : ℕ} (hn : 1 ≤ n) (z : Space n)
    (hz : z ∈ Metric.closedBall (WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ) / (n + 1)))
      (1 / ((n : ℝ) + 1) ^ 2)) :
    (∀ i, 0 ≤ z i) ∧ (∑ i, z i) ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hN2 : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
  have hd : ∀ i, |z i - 1 / ((n : ℝ) + 1)| ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
    intro i
    have h := PiLp.norm_apply_le (p := (2 : ENNReal)) (z - WithLp.toLp 2 (fun _ => (1 : ℝ) / (n + 1))) i
    have hz' : ‖z - WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ) / (n + 1))‖ ≤
        1 / ((n : ℝ) + 1) ^ 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hi : |z i - 1 / ((n : ℝ) + 1)| ≤
        ‖z - WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ) / (n + 1))‖ := by
      simpa [Real.norm_eq_abs] using h
    exact hi.trans hz'
  have hr : 1 / ((n : ℝ) + 1) ^ 2 ≤ 1 / ((n : ℝ) + 1) := by
    apply (div_le_div_iff₀ hN2 hN).mpr
    nlinarith
  constructor
  · intro i
    have h := (abs_le.mp (hd i)).1
    linarith
  · have hsum : (∑ i, z i) ≤ ∑ _ : Fin n, (1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) ^ 2) :=
      Finset.sum_le_sum fun i _ => by have h := (abs_le.mp (hd i)).2; linarith
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hbound : (n : ℝ) * (1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) ^ 2) ≤ 1 := by
      apply (mul_le_mul_iff_left₀ hN2).mp
      field_simp
      nlinarith
    exact hsum.trans hbound

/- A linear normalization of an arbitrary full-dimensional compact convex
body containing the distinguished origin. The dimension-only outer radius
is intentionally not John's sharp radius; it suffices for the compactness
argument and does not alter the source's final centered normalization. -/
theorem noncentered_body_normalization {n : ℕ} (hn : 1 ≤ n)
    {K : Set (Space n)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hint : (interior K).Nonempty) (h0 : (0 : Space n) ∈ K) :
    ∃ (A : Space n ≃L[ℝ] Space n) (c : Space n),
      Metric.closedBall c 1 ⊆ A '' K ∧
      A '' K ⊆ Metric.closedBall 0 (2 * ((n : ℝ) + 1) ^ 3) ∧
      ‖c‖ ≤ 2 * ((n : ℝ) + 1) ^ 3 := by
  classical
  obtain ⟨a, ha⟩ := hint
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (mem_interior_iff_mem_nhds.mp ha)
  let K' : Set (Space n) := (fun x => x - a) '' K
  have hK' : IsCompact K' := hK.image (continuous_id.sub continuous_const)
  have hcv' : Convex ℝ K' := hconv.affine_image (AffineMap.id ℝ (Space n) - AffineMap.const ℝ (Space n) a)
  have h0' : (0 : Space n) ∈ K' := ⟨a, interior_subset ha, sub_self _⟩
  have hb : Metric.closedBall (0 : Space n) r ⊆ K' := by
    intro x hx
    refine ⟨x + a, hball ?_, by abel_nf⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  obtain ⟨v, hv, hd, hmax⟩ := exists_max_det_columns hK' hr hb
  obtain ⟨q, hq, hcoord⟩ := maxdet_coordinate_bound v hv hd hmax
  let L := q.symm.toContinuousLinearEquiv
  let N : ℝ := (n : ℝ) + 1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : 0 < N := by dsimp [N]; positivity
  have hsq : Real.sqrt n ≤ (n : ℝ) := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have hbound : ∀ x ∈ K', ‖L x‖ ≤ (n : ℝ) := fun x hx =>
    (norm_le_sqrt_card_of_coordinate_le _ (hcoord x hx)).trans hsq
  have haBound : ‖L a‖ ≤ (n : ℝ) := by
    have hmem : -a ∈ K' := ⟨0, h0, by simp⟩
    simpa only [map_neg, norm_neg] using hbound (-a) hmem
  let A := (L.toLinearEquiv.trans
    (LinearEquiv.smulOfNeZero ℝ (Space n) (N ^ 2) (pow_ne_zero 2 hN.ne'))).toContinuousLinearEquiv
  have hA (x : Space n) : A x = N ^ 2 • L x := rfl
  let w : Space n := WithLp.toLp 2 (fun _ => 1 / N)
  let c : Space n := A a + N ^ 2 • w
  have hin : Metric.closedBall c 1 ⊆ A '' K := by
    intro z hz
    let b : Space n := (N ^ 2)⁻¹ • (z - c) + w
    have hb : b ∈ Metric.closedBall w (1 / N ^ 2) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      simp only [b, add_sub_cancel_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (sq_pos_of_pos hN)), one_div]
      have hdist : ‖z - c‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
      exact (mul_le_mul_of_nonneg_left hdist (inv_nonneg.mpr (sq_nonneg N))).trans_eq (mul_one _)
    obtain ⟨hbpos, hbsum⟩ := simplex_ball_coordinates hn b hb
    have hqb : q b ∈ K' := by
      rw [hq]
      exact convex_sum_mem_le_one hcv' h0' b v hbpos hbsum hv
    obtain ⟨x, hx, hxb⟩ := hqb
    refine ⟨x, hx, ?_⟩
    have hLb : L x = b + L a := by
      have he := congrArg L hxb
      change L (x - a) = q.symm (q b) at he
      rw [map_sub, q.symm_apply_apply] at he
      exact eq_add_of_sub_eq he
    rw [hA, hLb, smul_add, show b = (N ^ 2)⁻¹ • (z - c) + w from rfl,
      smul_add, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hN.ne'), one_smul]
    dsimp [c]
    rw [hA]
    abel
  have hout : A '' K ⊆ Metric.closedBall 0 (2 * ((n : ℝ) + 1) ^ 3) := by
    rintro z ⟨x, hx, rfl⟩
    have hxB := hbound (x - a) ⟨x, hx, rfl⟩
    have hLx : ‖L x‖ ≤ 2 * (n : ℝ) := by
      have he : L x = L (x - a) + L a := by rw [map_sub]; abel
      rw [he]
      exact (norm_add_le _ _).trans (by linarith)
    rw [Metric.mem_closedBall, dist_zero_right, hA, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg N)]
    have he := mul_le_mul_of_nonneg_left hLx (sq_nonneg N)
    dsimp [N] at he ⊢
    nlinarith [sq_nonneg ((n : ℝ) + 1)]
  exact ⟨A, c, hin, hout, by
    simpa [Metric.mem_closedBall, dist_zero_right] using hout (hin (Metric.mem_closedBall_self (by norm_num)))⟩

/- The same intermediate normalization with the zero-dimensional convention
made explicit. Its radii are only used in compactness arguments. -/
theorem noncentered_body_normalization_all {n : ℕ}
    {K : Set (Space n)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hint : (interior K).Nonempty) (h0 : (0 : Space n) ∈ K) :
    ∃ (A : Space n ≃L[ℝ] Space n) (c : Space n),
      Metric.closedBall c 1 ⊆ A '' K ∧
      A '' K ⊆ Metric.closedBall 0 (2 * ((n : ℝ) + 1) ^ 3) ∧
      ‖c‖ ≤ 2 * ((n : ℝ) + 1) ^ 3 := by
  by_cases hn : 1 ≤ n
  · exact noncentered_body_normalization hn hK hconv hint h0
  · have hn0 : n = 0 := by omega
    subst n
    refine ⟨ContinuousLinearEquiv.refl ℝ _, 0, ?_, ?_, by norm_num⟩
    · intro x hx
      have he : x = 0 := Subsingleton.elim _ _
      subst x
      exact ⟨0, h0, rfl⟩
    · intro x hx
      have he : x = 0 := Subsingleton.elim _ _
      simp [he]

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ThinSlices
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
variable {k d : ℕ}

/- Thin slices and rescalings before reordering the k+1 base coordinates. -/

namespace IsSupportedSplitModel
variable {C : Set (Space k × (ℝ × Space d))} (h : IsSupportedSplitModel C)
include h

theorem zero_mem : (0 : Space k × (ℝ × Space d)) ∈ C :=
  h.orthant 0 (by simp)

theorem one_mem : (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)), (1, 0)) ∈ C :=
  (interior_subset (s := {y | (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)), y) ∈ C})) h.interior_one

theorem base_mono {s t : Space k} {y : ℝ × Space d}
    (hst : ∀ i, s i ≤ t i) (hy : (s, y) ∈ C) : (t, y) ∈ C := by
  have hh := closed_convex_add_of_ray h.closed h.convex hy (v := (t - s, 0))
    (fun a ha => by
      simpa only [Prod.smul_mk, smul_zero, Prod.zero_eq_mk] using h.orthant (a • (t - s))
        (by intro i; exact mul_nonneg ha (sub_nonneg.mpr (hst i))))
  simpa using hh

/- Every slice at a sufficiently low positive support level contains a real
ball about zero, obtained by contraction of the interior ball at (1,0). -/
theorem slice_interior_zero {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (0 : Space d) ∈ interior (thinSlice C ε) := by
  let e : Space k := WithLp.toLp 2 (fun _ => 1)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior (1, (0 : Space d)) h.interior_one
  have hb : ball (0 : Space d) (ε * r) ⊆ thinSlice C ε := by
    intro z hz
    have hz' : ‖z‖ < ε * r := by simpa [mem_ball, dist_zero_right] using hz
    have hy : ((1 : ℝ), ε⁻¹ • z) ∈ ball ((1 : ℝ), (0 : Space d)) r := by
      simp only [mem_ball, Prod.dist_eq, dist_self, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε), max_lt_iff]
      exact ⟨hr, (inv_mul_lt_iff₀ hε).mpr hz'⟩
    have hm : (e, (1, ε⁻¹ • z)) ∈ C :=
      (interior_subset (s := {y | (e, y) ∈ C})) (hball hy)
    have hc := h.convex.smul_mem_of_zero_mem h.zero_mem hm ⟨hε.le, hε1⟩
    have hc' : (ε • e, (ε, z)) ∈ C := by
      simpa only [Prod.smul_mk, smul_eq_mul, mul_one, smul_smul, mul_inv_cancel₀ hε.ne', one_smul] using hc
    exact h.base_mono (by intro i; simpa [e] using hε1) hc'
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (ball_mem_nhds _ (mul_pos hε hr)) hb)

theorem slice_closed (ε : ℝ) : IsClosed (thinSlice C ε) :=
  h.closed.preimage (by fun_prop)

theorem slice_convex (ε : ℝ) : Convex ℝ (thinSlice C ε) := by
  intro x hx y hy a b ha hb hab
  have hh := h.convex hx hy ha hb hab
  simpa [thinSlice, ← add_smul, ← add_mul, hab] using hh

theorem slice_compact (ε : ℝ) : IsCompact (thinSlice C ε) := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨h.slice_closed ε, ?_⟩
  have hc := (h.compact_cap k (by positivity)).image (continuous_snd.comp continuous_snd)
  apply hc.isBounded.subset
  intro z hz
  exact ⟨(WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)), (ε, z)), ⟨hz, by simp⟩, rfl⟩

theorem rescaling_closed (ε : ℝ) (A : Space d ≃L[ℝ] Space d) :
    IsClosed (thinRescaling C ε A) := h.closed.preimage (by fun_prop)

theorem rescaling_convex (ε : ℝ) (A : Space d ≃L[ℝ] Space d) :
    Convex ℝ (thinRescaling C ε A) := by
  intro x hx y hy a b ha hb hab
  have hh := h.convex hx hy ha hb hab
  change (a • x.1 + b • y.1, (ε * (a * x.2.1 + b * y.2.1),
    A.symm (a • x.2.2 + b • y.2.2))) ∈ C
  simpa only [Prod.smul_mk, Prod.mk_add_mk, map_add, map_smul,
    smul_eq_mul, mul_add, mul_left_comm ε] using hh

omit h in
theorem rescaling_one_slice (_h : IsSupportedSplitModel C)
    (ε : ℝ) (A : Space d ≃L[ℝ] Space d) :
    {z | (WithLp.toLp 2 (fun _ : Fin k => (1 : ℝ)), (1, z)) ∈ thinRescaling C ε A} =
      A '' thinSlice C ε := by
  ext z
  simp only [thinRescaling, thinSlice, mem_ofPred_eq, mul_one, Set.mem_image]
  constructor
  · intro hz
    exact ⟨A.symm z, hz, A.apply_symm_apply z⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

/- The uniform cap bound has constant 2*T*R for an arbitrary slice outer
radius R (including d=0). -/
theorem rescaling_cap_bound {ε T R : ℝ} (hε : 0 < ε) (hε2 : 2 * ε ≤ 1)
    (A : Space d ≃L[ℝ] Space d) (hT : 1 ≤ T)
    (hR : A '' thinSlice C ε ⊆ closedBall 0 R)
    {s : Space k} {r : ℝ} {z : Space d}
    (hp : (s, (r, z)) ∈ thinRescaling C ε A)
    (hs : ∀ i, s i ≤ T) (hr : r ≤ T) : ‖z‖ ≤ 2 * T * R := by
  let e : Space k := WithLp.toLp 2 (fun _ => 1)
  have hTp : 0 < T := by linarith
  have hr0 : 0 ≤ r := (mul_nonneg_iff_of_pos_left hε).mp (h.new_support _ hp)
  have hm : (T • e, (ε * r, A.symm z)) ∈ C :=
    h.base_mono (by intro i; simpa [e] using hs i) hp
  have hc := h.convex.smul_mem_of_zero_mem h.zero_mem hm
    ⟨inv_nonneg.mpr hTp.le, inv_le_one_of_one_le₀ hT⟩
  have hq : (e, (ε * (r / T), A.symm (T⁻¹ • z))) ∈ C := by
    simpa only [Prod.smul_mk, smul_smul, inv_mul_cancel₀ hTp.ne', one_smul,
      map_smul, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hc
  have hp2 := h.convex.smul_mem_of_zero_mem h.zero_mem h.one_mem
    (show 2 * ε ∈ Icc (0 : ℝ) 1 from ⟨by positivity, hε2⟩)
  have hp2' : (e, (2 * ε, (0 : Space d))) ∈ C := by
    apply h.base_mono (s := (2 * ε) • e) (by intro i; simpa [e] using hε2)
    simpa [Prod.smul_mk, e] using hp2
  let q := r / T
  have hq0 : 0 ≤ q := div_nonneg hr0 hTp.le
  have hq1 : q ≤ 1 := (div_le_one hTp).mpr hr
  let a := (2 - q)⁻¹
  have hd : 0 < 2 - q := by linarith
  have ha : 0 < a := inv_pos.mpr hd
  have ha1 : a ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have ha2 : (1 : ℝ) / 2 ≤ a := by
    simpa [a, one_div] using one_div_le_one_div_of_le hd (by linarith : 2 - q ≤ 2)
  have hcomb := h.convex hq hp2' ha.le (sub_nonneg.mpr ha1) (by ring : a + (1-a) = 1)
  have hrr : a * (ε * q) + (1-a) * (2*ε) = ε := by
    dsimp [a]
    field_simp
    ring
  dsimp [q] at hrr
  have hmem : a • (T⁻¹ • z) ∈ A '' thinSlice C ε := by
    rw [← h.rescaling_one_slice ε A]
    change (e, (ε * 1, A.symm (a • (T⁻¹ • z)))) ∈ C
    rw [mul_one]
    have hb : a • e + (1 - a) • e = e := by rw [← add_smul]; simp
    simpa only [Prod.smul_mk, Prod.mk_add_mk, hb, smul_eq_mul, hrr,
      map_smul, smul_zero, add_zero] using hcomb
  have hn : ‖a • (T⁻¹ • z)‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hR hmem
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos ha, abs_of_pos (inv_pos.mpr hTp)] at hn
  have hmult : a * ‖z‖ ≤ T * R := by
    have hh := mul_le_mul_of_nonneg_left hn hTp.le
    simpa [mul_assoc, mul_left_comm, mul_comm, hTp.ne'] using hh
  nlinarith [mul_nonneg (sub_nonneg.mpr ha2) (norm_nonneg z)]

end IsSupportedSplitModel

/- Eventual membership of a fixed point is sufficient for passage to the
local limit, including initial rescalings on which it is not yet present. -/
theorem LocalDistanceConverges.mem_of_eventually_mem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {Cj : ℕ → Set E} {C : Set E} (h : LocalDistanceConverges Cj C)
    (hc : IsClosed C) (hne : C.Nonempty) {x : E}
    (hx : ∀ᶠ j in atTop, x ∈ Cj j) : x ∈ C := by
  apply (hc.mem_iff_infDist_zero hne).mpr
  have he : (fun j => infDist x (Cj j)) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
    filter_upwards [hx] with j hj
    exact infDist_zero_of_mem hj
  exact tendsto_nhds_unique (h.pointwise x) (tendsto_const_nhds.congr' he.symm)

/- All the geometric properties of the (k+1)-direction model supplied by the
thin-slice limit. The new base is still written (s,r), before reindexing it as
R^(k+1). This theorem includes the zero-dimensional transverse endpoint. -/
theorem LocalDistanceConverges.thin_limit
    {C C₀ : Set (Space k × (ℝ × Space d))} (hC : IsSupportedSplitModel C)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε2 : ∀ j, 2 * ε j ≤ 1)
    (hεt : Tendsto ε atTop (𝓝 0))
    (A : ℕ → (Space d ≃L[ℝ] Space d))
    (h : LocalDistanceConverges (fun j => thinRescaling C (ε j) (A j)) C₀)
    (hclosed : IsClosed C₀) (hconvex : Convex ℝ C₀) (hne : C₀.Nonempty)
    {cj : ℕ → Space d} {c : Space d} (hc : Tendsto cj atTop (𝓝 c)) {R : ℝ}
    (hinner : ∀ j, closedBall (cj j) 1 ⊆ A j '' thinSlice C (ε j))
    (houter : ∀ j, A j '' thinSlice C (ε j) ⊆ closedBall 0 R) :
    (∀ s : Space k, (∀ i, 0 ≤ s i) → ∀ r : ℝ, 0 ≤ r → (s, (r, 0)) ∈ C₀) ∧
    (∀ p ∈ C₀, (∀ i, 0 ≤ p.1 i) ∧ 0 ≤ p.2.1) ∧
    (interior C₀).Nonempty ∧
    (∀ T : ℝ, 0 ≤ T → IsCompact (C₀ ∩ {p | (∑ i, p.1 i) + p.2.1 ≤ T})) := by
  let e : Space k := WithLp.toLp 2 (fun _ => 1)
  have hz : ∀ j, (0 : Space k × (ℝ × Space d)) ∈ thinRescaling C (ε j) (A j) := by
    intro j
    simpa [thinRescaling, Prod.zero_eq_mk] using hC.zero_mem
  have hclj : ∀ j, IsClosed (thinRescaling C (ε j) (A j)) :=
    fun j => hC.rescaling_closed _ _
  have hnej : ∀ j, (thinRescaling C (ε j) (A j)).Nonempty := fun j => ⟨0, hz j⟩
  have hposorth : ∀ s : Space k, (∀ i, 0 < s i) → ∀ r : ℝ, 0 ≤ r → (s, (r, 0)) ∈ C₀ := by
    intro s hs r hr
    apply h.mem_of_eventually_mem hclosed hne
    have ht : Tendsto (fun j => ε j * r) atTop (𝓝 0) := by simpa using hεt.mul_const r
    have hsmall : ∀ i : Fin k, ∀ᶠ j in atTop, ε j * r ≤ s i :=
      fun i => ht.eventually_le_const (hs i)
    filter_upwards [Filter.eventually_all.mpr hsmall, ht.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with j hj hj1
    have hp := hC.convex.smul_mem_of_zero_mem hC.zero_mem hC.one_mem
      (show ε j * r ∈ Icc (0 : ℝ) 1 from ⟨mul_nonneg (hε j).le hr, hj1⟩)
    have hp' : ((ε j * r) • e, (ε j * r, (0 : Space d))) ∈ C := by
      simpa only [Prod.smul_mk, smul_eq_mul, mul_one, smul_zero] using hp
    simpa [thinRescaling] using hC.base_mono (by intro i; simpa [e] using hj i) hp'
  have horth : ∀ s : Space k, (∀ i, 0 ≤ s i) → ∀ r : ℝ, 0 ≤ r → (s, (r, 0)) ∈ C₀ := by
    intro s hs r hr
    have hm : ∀ t : ℝ, 0 < t → (s + t • e, (r, (0 : Space d))) ∈ C₀ := by
      intro t ht
      apply hposorth _ _ r hr
      intro i
      simpa [e] using (add_pos_of_nonneg_of_pos (hs i) ht)
    have ht : Tendsto (fun t : ℝ => (s + t • e, (r, (0 : Space d)))) (𝓝[>] 0) (𝓝 (s, (r, 0))) := by
      have hcont : Continuous (fun t : ℝ => (s + t • e, (r, (0 : Space d)))) := by fun_prop
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    apply hclosed.mem_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hm t ht
  have hsupp : ∀ p ∈ C₀, (∀ i, 0 ≤ p.1 i) ∧ 0 ≤ p.2.1 := by
    intro p hp
    obtain ⟨pj, hpj, hpt⟩ := h.exists_approximating hclj hnej hp
    constructor
    · intro i
      have ht : Tendsto (fun j => (pj j).1 i) atTop (𝓝 (p.1 i)) :=
        (((PiLp.continuous_apply 2 (fun _ : Fin k => ℝ) i).comp continuous_fst).tendsto p).comp hpt
      exact ge_of_tendsto ht (Eventually.of_forall fun j => hC.base_support _ (hpj j) i)
    · have ht : Tendsto (fun j => (pj j).2.1) atTop (𝓝 (p.2.1)) :=
        (((continuous_fst.comp continuous_snd).tendsto p).comp hpt)
      apply ge_of_tendsto ht
      exact Eventually.of_forall fun j =>
        (mul_nonneg_iff_of_pos_left (hε j)).mp (hC.new_support _ (hpj j))
  refine ⟨horth, hsupp, ?_, ?_⟩
  · have hfiber : ∀ z ∈ closedBall c 1, (e, (1, z)) ∈ C₀ := by
      intro z hz'
      have hm : ∀ j, (e, (1, cj j + (z-c))) ∈ thinRescaling C (ε j) (A j) := by
        intro j
        have hh : cj j + (z-c) ∈ A j '' thinSlice C (ε j) := hinner j (by
          simpa [mem_closedBall, dist_eq_norm] using hz')
        rw [← hC.rescaling_one_slice] at hh
        exact hh
      apply h.mem_of_tendsto hclosed hne hm
      have ht := hc.add_const (z-c)
      simpa using tendsto_const_nhds.prodMk_nhds (tendsto_const_nhds.prodMk_nhds ht)
    have hball : ball (2 • e, ((2 : ℝ), c)) (1 / 2 : ℝ) ⊆ C₀ := by
      intro q hq
      have hd : dist q.1 (2 • e) < (1 / 2 : ℝ) ∧
          dist q.2.1 2 < (1 / 2 : ℝ) ∧ dist q.2.2 c < (1 / 2 : ℝ) := by
        simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using hq
      have hbase : ∀ i, e i ≤ q.1 i := by
        intro i
        have hn := PiLp.norm_apply_le (q.1 - 2 • e) i
        have hi : |q.1 i - 2| < (1 / 2 : ℝ) := by
          have hn' : |q.1 i - 2| ≤ ‖q.1 - 2 • e‖ := by simpa [e] using hn
          exact hn'.trans_lt (by simpa [dist_eq_norm] using hd.1)
        simpa [e] using (by linarith [(abs_lt.mp hi).1] : (1 : ℝ) ≤ q.1 i)
      have hr : 1 ≤ q.2.1 := by
        have ht : |q.2.1 - 2| < (1 / 2 : ℝ) := by simpa [Real.dist_eq] using hd.2.1
        linarith [(abs_lt.mp ht).1]
      have hm := hfiber q.2.2 (hd.2.2.le.trans (by norm_num))
      have hh := closed_convex_add_of_ray hclosed hconvex hm
        (v := (q.1 - e, (q.2.1 - 1, (0 : Space d)))) (by
          intro t ht
          simpa only [Prod.smul_mk, smul_eq_mul, smul_zero] using
            horth (t • (q.1 - e)) (fun i => mul_nonneg ht (sub_nonneg.mpr (hbase i)))
              (t * (q.2.1 - 1)) (mul_nonneg ht (sub_nonneg.mpr hr)))
      simpa using hh
    exact ⟨(2 • e, (2, c)), mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1/2)) hball)⟩
  · intro T hT
    let B : Set (Space k) := (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).symm ''
      Icc (fun _ : Fin k => (0 : ℝ)) (fun _ => T)
    have hB : IsCompact B := isCompact_Icc.image (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).symm.continuous
    have hcapclosed : IsClosed (C₀ ∩ {p | (∑ i, p.1 i) + p.2.1 ≤ T}) :=
      hclosed.inter (isClosed_le (by fun_prop) continuous_const)
    apply (hB.prod (isCompact_Icc.prod (isCompact_closedBall (0 : Space d) (2 * (T+1) * R)))).of_isClosed_subset hcapclosed
    rintro p ⟨hp, hpT⟩
    change (∑ i, p.1 i) + p.2.1 ≤ T at hpT
    have hsT : ∀ i, p.1 i ≤ T := by
      intro i
      have hi := Finset.single_le_sum (fun a _ => (hsupp p hp).1 a) (Finset.mem_univ i)
      linarith [(hsupp p hp).2]
    have hrT : p.2.1 ≤ T := by linarith [Finset.sum_nonneg (s := Finset.univ) (fun i _ => (hsupp p hp).1 i)]
    refine ⟨⟨fun i => p.1 i, ⟨(hsupp p hp).1, hsT⟩, rfl⟩, ⟨(hsupp p hp).2, hrT⟩, ?_⟩
    obtain ⟨pj, hpj, hpt⟩ := h.exists_approximating hclj hnej hp
    have hcoord : ∀ i : Fin k, ∀ᶠ j in atTop, (pj j).1 i ≤ T+1 := by
      intro i
      have ht : Tendsto (fun j => (pj j).1 i) atTop (𝓝 (p.1 i)) :=
        (((PiLp.continuous_apply 2 (fun _ : Fin k => ℝ) i).comp continuous_fst).tendsto p).comp hpt
      exact ht.eventually_le_const (by linarith [hsT i])
    have hrcoord : ∀ᶠ j in atTop, (pj j).2.1 ≤ T+1 :=
      (((continuous_fst.comp continuous_snd).tendsto p).comp hpt).eventually_le_const (by change p.2.1 < T+1; linarith)
    have hb : ∀ᶠ j in atTop, ‖(pj j).2.2‖ ≤ 2 * (T+1) * R := by
      filter_upwards [Filter.eventually_all.mpr hcoord, hrcoord] with j hj hjr
      exact hC.rescaling_cap_bound (hε j) (hε2 j) (A j) (by linarith) (houter j) (hpj j) hj hjr
    simpa only [mem_closedBall, dist_zero_right, Function.comp_apply] using
      le_of_tendsto (((continuous_snd.comp continuous_snd).tendsto p).comp hpt).norm hb

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ModelCentering
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
open scoped Pointwise

open Filter Metric
open scoped Topology Pointwise

variable {k m d : ℕ}

/- Transverse coordinate changes preserve the literal model conditions. -/
theorem IsModelShape.transverse_image {C : Set (Space k × Space m)}
    (hC : IsModelShape C) (A : Space m ≃L[ℝ] Space m) :
    IsModelShape (((ContinuousLinearEquiv.refl ℝ (Space k)).prodCongr A) '' C) := by
  let B := (ContinuousLinearEquiv.refl ℝ (Space k)).prodCongr A
  have cap (T : ℝ) : (B '' C) ∩ {p | ∑ i, p.1 i ≤ T} =
      B '' (C ∩ {p | ∑ i, p.1 i ≤ T}) := by
    ext p
    constructor
    · rintro ⟨⟨q, hq, rfl⟩, ht⟩
      exact ⟨q, ⟨hq, ht⟩, rfl⟩
    · rintro ⟨q, ⟨hq, ht⟩, rfl⟩
      exact ⟨⟨q, hq, rfl⟩, ht⟩
  refine ⟨B.toHomeomorph.isClosedMap _ hC.closed,
    hC.convex.linear_image B.toLinearMap, ?_, ?_, ?_, ?_⟩
  · change (interior (B.toHomeomorph '' C)).Nonempty
    rw [← B.toHomeomorph.image_interior]
    exact hC.interior_nonempty.image B
  · intro s hs
    exact ⟨(s, 0), hC.orthant s hs, by simp⟩
  · rintro p ⟨q, hq, rfl⟩
    exact hC.support q hq
  · intro T hT
    change IsCompact ((B '' C) ∩ _)
    rw [cap]
    exact (hC.compact_cap T hT).image B.continuous

theorem IsModelShape.supported_split {C : Set (Space k × Space m)}
    (hC : IsModelShape C) (A : Space m ≃L[ℝ] ℝ × Space d)
    (hs : ∀ p ∈ C, 0 ≤ (A p.2).1)
    (hi : (1,0) ∈ interior (A '' modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))) :
    IsSupportedSplitModel (((ContinuousLinearEquiv.refl ℝ (Space k)).prodCongr A) '' C) := by
  let B := (ContinuousLinearEquiv.refl ℝ (Space k)).prodCongr A
  have cap (T : ℝ) : (B '' C) ∩ {p | ∑ i, p.1 i ≤ T} =
      B '' (C ∩ {p | ∑ i, p.1 i ≤ T}) := by
    ext p
    constructor
    · rintro ⟨⟨q, hq, rfl⟩, ht⟩
      exact ⟨q, ⟨hq, ht⟩, rfl⟩
    · rintro ⟨q, ⟨hq, ht⟩, rfl⟩
      exact ⟨⟨q, hq, rfl⟩, ht⟩
  refine ⟨B.toHomeomorph.isClosedMap _ hC.closed,
    hC.convex.linear_image B.toLinearMap, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact ⟨(s,0), hC.orthant s hs, by simp [Prod.zero_eq_mk]⟩
  · rintro p ⟨q,hq,rfl⟩
    exact hC.support q hq
  · rintro p ⟨q,hq,rfl⟩
    exact hs q hq
  · intro T hT
    change IsCompact ((B '' C) ∩ _)
    rw [cap]
    exact (hC.compact_cap T hT).image B.continuous
  · convert hi using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext y
    constructor
    · rintro ⟨p,hp,he⟩
      have he1 : p.1 = WithLp.toLp 2 (fun _ : Fin k => (1:ℝ)) := congrArg Prod.fst he
      have he2 := congrArg Prod.snd he
      refine ⟨p.2, ?_, he2⟩
      simpa only [modelFiber, mem_ofPred_eq, ← he1, Prod.mk.eta] using hp
    · rintro ⟨z,hz,rfl⟩
      exact ⟨(_,z),hz,rfl⟩

/- The rescaling is genuinely an invertible linear image, not an abstract
limit operation. -/

theorem thinRescaling_eq_image {C : Set (Space k × (ℝ × Space d))}
    {ε : ℝ} (hε : ε ≠ 0) (A : Space d ≃L[ℝ] Space d) :
    thinRescaling C ε A = thinRescalingEquiv k d ε hε A '' C := by
  ext p
  change p ∈ thinRescaling C ε A ↔ p ∈ (thinRescalingEquiv k d ε hε A).toEquiv '' C
  rw [Set.mem_image_equiv]
  rfl

/- Reindexing the limiting (s,r) orthant gives the manuscript's exact
(k+1)-model, including the case of no remaining transverse coordinates. -/
theorem modelShape_reorder {C : Set (Space k × (ℝ × Space d))}
    (hc : IsClosed C) (hv : Convex ℝ C) (hi : (interior C).Nonempty)
    (ho : ∀ s : Space k, (∀ i, 0 ≤ s i) → ∀ r : ℝ, 0 ≤ r → (s,(r,0)) ∈ C)
    (hs : ∀ p ∈ C, (∀ i, 0 ≤ p.1 i) ∧ 0 ≤ p.2.1)
    (hcap : ∀ T : ℝ, 0 ≤ T → IsCompact (C ∩ {p | (∑ i,p.1 i)+p.2.1 ≤ T})) :
    IsModelShape (reorderThinEquiv k d '' C) := by
  let B := reorderThinEquiv k d
  refine ⟨B.toHomeomorph.isClosedMap _ hc, hv.linear_image B.toLinearMap, ?_, ?_, ?_, ?_⟩
  · change (interior (B.toHomeomorph '' C)).Nonempty
    rw [← B.toHomeomorph.image_interior]
    exact hi.image B
  · intro s hs'
    let p := B.symm (s,0)
    have he : B p = (s,0) := B.apply_symm_apply _
    have he0 : p.2.2 = 0 := congrArg Prod.snd he
    have he1 (i : Fin k) : p.1 i = s i.succ := by
      simpa [B] using congrArg (fun q : Space (k+1) × Space d => q.1 i.succ) he
    have he2 : p.2.1 = s 0 := by
      simpa [B] using congrArg (fun q : Space (k+1) × Space d => q.1 0) he
    refine ⟨p, ?_, he⟩
    have hm := ho p.1 (fun i => by rw [he1]; exact hs' _) p.2.1 (by rw [he2]; exact hs' _)
    simpa only [← he0, Prod.mk.eta] using hm
  · rintro p ⟨q,hq,rfl⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (hs q hq).2
    · exact (hs q hq).1 j
  · intro T hT
    have he : (B '' C) ∩ {p | ∑ i,p.1 i ≤ T} =
        B '' (C ∩ {p | (∑ i,p.1 i)+p.2.1 ≤ T}) := by
      ext p
      constructor
      · rintro ⟨⟨q,hq,rfl⟩,ht⟩
        refine ⟨q,⟨hq,?_⟩,rfl⟩
        simpa only [B, mem_ofPred_eq, reorderThin_sum] using ht
      · rintro ⟨q,⟨hq,ht⟩,rfl⟩
        refine ⟨⟨q,hq,rfl⟩,?_⟩
        simpa only [B, mem_ofPred_eq, reorderThin_sum] using ht
    change IsCompact ((B '' C) ∩ _)
    rw [he]
    exact (hcap T hT).image B.continuous

/- A supported thin-slice model produces an actual model with one additional
nonnegative direction in the original affine local-limit family. All normalizers,
subsequences and limiting sets are constructed here. -/
theorem IsSupportedSplitModel.exists_next_model
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {D : Set E} (hD : IsClosed D) (hneD : D.Nonempty)
    {C : Set (Space k × (ℝ × Space d))} (hC : IsSupportedSplitModel C)
    (hf : InAffineLimitFamily D C) :
    ∃ C' : Set (Space (k+1) × Space d), IsModelShape C' ∧ InAffineLimitFamily D C' := by
  classical
  let ε : ℕ → ℝ := fun j => (1 / ((j:ℝ)+1)) / 4
  have hepos : ∀ j, 0 < ε j := by intro j; dsimp [ε]; positivity
  have he2 : ∀ j, 2 * ε j ≤ 1 := by
    intro j
    have hi : 1 / ((j:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
    dsimp [ε]
    linarith
  have he1 : ∀ j, ε j ≤ 1 := fun j => by linarith [he2 j, hepos j]
  have het : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 4
  have hnorm : ∀ j, ∃ (A : Space d ≃L[ℝ] Space d) (c : Space d),
      closedBall c 1 ⊆ A '' thinSlice C (ε j) ∧
      A '' thinSlice C (ε j) ⊆ closedBall 0 (2 * ((d:ℝ)+1)^3) ∧
      ‖c‖ ≤ 2 * ((d:ℝ)+1)^3 := by
    intro j
    have hi := hC.slice_interior_zero (hepos j) (he1 j)
    exact noncentered_body_normalization_all (hC.slice_compact _) (hC.slice_convex _)
      ⟨0,hi⟩ (interior_subset hi)
  choose A cj hin hout hcb using hnorm
  obtain ⟨c,hcB,φ,hφ,hct⟩ := (isCompact_closedBall (0 : Space d) (2*((d:ℝ)+1)^3)).tendsto_subseq
    (x := cj) (fun j => by simpa [mem_closedBall,dist_zero_right] using hcb j)
  let Cj : ℕ → Set (Space k × (ℝ × Space d)) := fun j => thinRescaling C (ε (φ j)) (A (φ j))
  have hz : ∀ j, (0 : Space k × (ℝ × Space d)) ∈ Cj j := by
    intro j
    simpa [Cj,thinRescaling,Prod.zero_eq_mk] using hC.zero_mem
  have hcl : ∀ j, IsClosed (Cj j) := fun j => hC.rescaling_closed _ _
  have hcv : ∀ j, Convex ℝ (Cj j) := fun j => hC.rescaling_convex _ _
  obtain ⟨C₀,ψ,hψ,hclosed,hne,hconv,hlim⟩ := exists_convex_local_limit hcl hcv
    (fun j => ⟨0,hz j⟩) (R := 0) (fun j => by rw [infDist_zero_of_mem (hz j)])
  have hp := hlim.thin_limit hC (fun j => hepos (φ (ψ j))) (fun j => he2 (φ (ψ j)))
    (het.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop)) (fun j => A (φ (ψ j)))
    hclosed hconv hne (hct.comp hψ.tendsto_atTop)
    (fun j => hin (φ (ψ j))) (fun j => hout (φ (ψ j)))
  have hfj : ∀ j, InAffineLimitFamily D (Cj j) := by
    intro j
    have hh := hf.affine_image hD hneD
      (thinRescalingEquiv k d (ε (φ j)) (hepos _).ne' (A (φ j))).toContinuousAffineEquiv
    simpa only [Cj,thinRescaling_eq_image (hepos _).ne',
      ContinuousLinearEquiv.coe_toContinuousAffineEquiv] using hh
  have hf₀ : InAffineLimitFamily D C₀ :=
    InAffineLimitFamily.diagonal_closure (fun j => hfj (ψ j)) hlim hclosed hconv hp.2.2.1
  exact ⟨reorderThinEquiv k d '' C₀,
    modelShape_reorder hclosed hconv hp.2.2.1 hp.1 hp.2.1 hp.2.2.2,
    hf₀.affine_image hD hneD (reorderThinEquiv k d).toContinuousAffineEquiv⟩

/- Boundary zero in the fiber is incompatible with maximality of the number
of model directions: the missing new model is actually produced, not assumed. -/
theorem IsModelShape.exists_next_model_of_zero_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {D : Set E} (hD : IsClosed D) (hneD : D.Nonempty)
    {C : Set (Space k × Space m)} (hC : IsModelShape C) (hf : InAffineLimitFamily D C)
    (hz : (0 : Space m) ∉ interior (modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))) :
    ∃ (d : ℕ) (C' : Set (Space (k+1) × Space d)),
      m = d+1 ∧ IsModelShape C' ∧ InAffineLimitFamily D C' := by
  obtain ⟨ell,hell,hs⟩ := hC.exists_global_support_of_zero_boundary hz
  obtain ⟨d,A,hd,hsA,hiA⟩ := exists_support_coordinates
    (hC.fiber_interior_nonempty (s := WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) (by simp)) ell hell
    (fun y hy => hs (_,y) hy)
  have hsupport : ∀ p ∈ C, 0 ≤ (A p.2).1 := by
    -- Coordinate construction yields the sign globally by contraction into
    -- the exact fiber; this avoids relying on implementation details of A.
    let f : Space m →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ (Space d)).comp A.toContinuousLinearMap
    exact hC.support_from_fiber f hsA
  let B := (ContinuousLinearEquiv.refl ℝ (Space k)).prodCongr A
  obtain ⟨C',hc',hf'⟩ := (hC.supported_split A hsupport hiA).exists_next_model hD hneD
    (hf.affine_image hD hneD B.toContinuousAffineEquiv)
  exact ⟨d,C',hd,hc',hf'⟩

/- Dilation of a convex body containing zero is monotone for nonnegative
radii. This includes a zero inner radius. -/
theorem convex_smul_set_mono {F : Set (Space m)} (hv : Convex ℝ F) (hz : (0 : Space m) ∈ F)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) : a • F ⊆ b • F := by
  rintro x ⟨y,hy,rfl⟩
  refine mem_smul_set.mpr ⟨(a/b) • y, hv.smul_mem_of_zero_mem hz hy
    ⟨div_nonneg ha hb.le,(div_le_one hb).mpr hab⟩, ?_⟩
  rw [smul_smul, mul_div_cancel₀ _ hb.ne']

/- Centering is unaffected by any invertible linear transverse change. -/
theorem centering_image_iff (A : Space m ≃L[ℝ] Space m) (F : Set (Space m)) (a : ℝ) :
    -(A '' F) ⊆ a • (A '' F) ↔ -F ⊆ a • F := by
  constructor
  · intro h x hx
    have hm : A x ∈ -(A '' F) := by
      change -(A x) ∈ A '' F
      exact ⟨-x,hx,by simp⟩
    obtain ⟨y,⟨z,hz,rfl⟩,he⟩ := mem_smul_set.mp (h hm)
    refine mem_smul_set.mpr ⟨z,hz,A.injective ?_⟩
    simpa only [map_smul] using he
  · intro h x hx
    change -x ∈ A '' F at hx
    obtain ⟨y,hy,he⟩ := hx
    have hm : -y ∈ -F := by simpa using hy
    obtain ⟨z,hz,hz'⟩ := mem_smul_set.mp (h hm)
    refine mem_smul_set.mpr ⟨A z,⟨z,hz,rfl⟩,?_⟩
    have hh := congrArg A hz'
    rw [map_smul,map_neg,he] at hh
    simpa using hh

/- Uniform centering for every distinguished fiber in a maximal model
family. The single maximality hypothesis rules out actual (k+1)-models;
it carries no centering estimate and is discharged by choosing maximal k. -/
theorem uniform_centering_at_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {D : Set E} (hD : IsClosed D) (hneD : D.Nonempty)
    (hmax : ∀ (d : ℕ), m = d+1 → ∀ C' : Set (Space (k+1) × Space d),
      IsModelShape C' → InAffineLimitFamily D C' → False) :
    ∃ a : ℝ, 1 ≤ a ∧ ∀ C : Set (Space k × Space m),
      IsModelShape C → InAffineLimitFamily D C →
      -(modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ)))) ⊆
        a • modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) := by
  classical
  let e : Space k := WithLp.toLp 2 (fun _ => 1)
  by_contra h
  push Not at h
  have hbad : ∀ j : ℕ, ∃ C : Set (Space k × Space m), IsModelShape C ∧
      InAffineLimitFamily D C ∧ ¬ -(modelFiber C e) ⊆ ((j:ℝ)+1) • modelFiber C e := by
    intro j
    obtain ⟨C,hC,hf,hfail⟩ := h ((j:ℝ)+1) (by linarith [Nat.cast_nonneg (α := ℝ) j])
    exact ⟨C,hC,hf,hfail⟩
  choose C hC hf hfail using hbad
  have hn : ∀ j, ∃ (A : Space m ≃L[ℝ] Space m) (c : Space m),
      closedBall c 1 ⊆ A '' modelFiber (C j) e ∧
      A '' modelFiber (C j) e ⊆ closedBall 0 (2*((m:ℝ)+1)^3) ∧ ‖c‖ ≤ 2*((m:ℝ)+1)^3 := by
    intro j
    exact noncentered_body_normalization_all
      ((hC j).fiber_compact (s := e) (by simp [e])) ((hC j).fiber_convex e)
      ((hC j).fiber_interior_nonempty (by simp [e])) ((hC j).fiber_zero (by simp [e]))
  choose A cj hin hout hcb using hn
  let Cj : ℕ → Set (Space k × Space m) := fun j =>
    ((ContinuousLinearEquiv.refl ℝ (Space k)).prodCongr (A j)) '' C j
  have hmod : ∀ j, IsModelShape (Cj j) := fun j => (hC j).transverse_image (A j)
  have hfam : ∀ j, InAffineLimitFamily D (Cj j) := fun j =>
    (hf j).affine_image hD hneD ((ContinuousLinearEquiv.refl ℝ (Space k)).prodCongr (A j)).toContinuousAffineEquiv
  have hinner : ∀ j, closedBall (cj j) 1 ⊆ modelFiber (Cj j) e := by
    intro j
    simpa only [Cj,fiber_transverse_image] using hin j
  have houter : ∀ j, modelFiber (Cj j) e ⊆ closedBall 0 (2*((m:ℝ)+1)^3) := by
    intro j
    simpa only [Cj,fiber_transverse_image] using hout j
  have hassym : ∀ j, ¬ -(modelFiber (Cj j) e) ⊆ ((j:ℝ)+1) • modelFiber (Cj j) e := by
    intro j hj
    apply hfail j
    apply (centering_image_iff (A j) _ _).mp
    simpa only [Cj,fiber_transverse_image] using hj
  obtain ⟨c,hcB,φ,hφ,hct⟩ := (isCompact_closedBall (0 : Space m) (2*((m:ℝ)+1)^3)).tendsto_subseq
    (x := cj) (fun j => by simpa [mem_closedBall,dist_zero_right] using hcb j)
  obtain ⟨C₀,ψ,hψ,hclosed,hne,hconv,hlim⟩ := exists_convex_local_limit
    (fun j => (hmod (φ j)).closed) (fun j => (hmod (φ j)).convex)
    (fun j => ⟨0,(hmod (φ j)).zero_mem⟩) (R := 0)
    (fun j => by rw [infDist_zero_of_mem (hmod (φ j)).zero_mem])
  have hmod₀ := hlim.isModelShape_of_normalized (fun j => hmod (φ (ψ j)))
    hclosed hconv hne (hct.comp hψ.tendsto_atTop)
    (fun j => hinner (φ (ψ j))) (fun j => houter (φ (ψ j)))
  have hf₀ : InAffineLimitFamily D C₀ := InAffineLimitFamily.diagonal_closure
    (fun j => hfam (φ (ψ j))) hlim hclosed hconv hmod₀.interior_nonempty
  have hfail' : ∀ j : ℕ, 1 ≤ j →
      ¬ -(modelFiber (Cj (φ (ψ j))) e) ⊆ (j:ℝ) • modelFiber (Cj (φ (ψ j))) e := by
    intro j hj hh
    apply hassym (φ (ψ j))
    apply hh.trans
    apply convex_smul_set_mono ((hmod _).fiber_convex e) ((hmod _).fiber_zero (by simp [e]))
      (Nat.cast_nonneg j) _ (by positivity)
    have hle : j ≤ φ (ψ j) := (hψ.id_le j).trans (hφ.id_le (ψ j))
    have hle' : (j:ℝ) ≤ φ (ψ j) := by exact_mod_cast hle
    linarith
  have hfront := hlim.zero_mem_frontier_fiber_of_asymmetry (fun j => hmod (φ (ψ j)))
    hmod₀ (fun j => houter (φ (ψ j))) hfail'
  have hz : (0 : Space m) ∉ interior (modelFiber C₀ e) := hfront.2
  obtain ⟨d,C',hd,hc',hf'⟩ := hmod₀.exists_next_model_of_zero_boundary hD hneD hf₀ hz
  exact hmax d hd C' hc' hf'

/- The positive diagonal base change sending s to the all-ones base point. -/
theorem IsModelShape.positive_base_image {C : Set (Space k × Space m)}
    (hC : IsModelShape C) (s : Space k) (hs : ∀ i, 0 < s i) :
    IsModelShape (((positiveBaseEquiv s hs).prodCongr (ContinuousLinearEquiv.refl ℝ (Space m))) '' C) := by
  let B := (positiveBaseEquiv s hs).prodCongr (ContinuousLinearEquiv.refl ℝ (Space m))
  refine ⟨B.toHomeomorph.isClosedMap _ hC.closed,
    hC.convex.linear_image B.toLinearMap, ?_, ?_, ?_, ?_⟩
  · change (interior (B.toHomeomorph '' C)).Nonempty
    rw [← B.toHomeomorph.image_interior]
    exact hC.interior_nonempty.image B
  · intro t ht
    refine ⟨((positiveBaseEquiv s hs).symm t,0),hC.orthant _ (fun i => mul_nonneg (hs i).le (ht i)),?_⟩
    simp
  · rintro p ⟨q,hq,rfl⟩ i
    exact div_nonneg (hC.support q hq i) (hs i).le
  · intro T hT
    have hclosed : IsClosed ((B '' C) ∩ {p | ∑ i,p.1 i ≤ T}) :=
      (B.toHomeomorph.isClosedMap _ hC.closed).inter (isClosed_le (by fun_prop) continuous_const)
    have hcompact := (hC.compact_cap ((∑ i,s i)*T)
      (mul_nonneg (Finset.sum_nonneg (fun i _ => (hs i).le)) hT)).image B.continuous
    apply hcompact.of_isClosed_subset hclosed
    rintro p ⟨⟨q,hq,rfl⟩,hTq⟩
    refine ⟨q,⟨hq,?_⟩,rfl⟩
    change ∑ i,q.1 i ≤ (∑ i,s i)*T
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hnon : ∀ j : Fin k, 0 ≤ (B q).1 j := fun j => div_nonneg (hC.support q hq j) (hs j).le
    have hle : (B q).1 i ≤ T :=
      (Finset.single_le_sum (fun j _ => hnon j) (Finset.mem_univ i)).trans hTq
    change q.1 i / s i ≤ T at hle
    exact (div_le_iff₀ (hs i)).mp hle |>.trans_eq (mul_comm _ _)

theorem uniform_centering
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {D : Set E} (hD : IsClosed D) (hneD : D.Nonempty)
    (hmax : ∀ (d : ℕ), m = d+1 → ∀ C' : Set (Space (k+1) × Space d),
      IsModelShape C' → InAffineLimitFamily D C' → False) :
    ∃ a : ℝ, 1 ≤ a ∧ ∀ C : Set (Space k × Space m),
      IsModelShape C → InAffineLimitFamily D C → ∀ s : Space k, (∀ i, 0 < s i) →
      -(modelFiber C s) ⊆ a • modelFiber C s := by
  obtain ⟨a,ha,hcenter⟩ := uniform_centering_at_one hD hneD hmax
  refine ⟨a,ha,?_⟩
  intro C hC hf s hs
  have hh := hcenter _ (hC.positive_base_image s hs)
    (hf.affine_image hD hneD
      ((positiveBaseEquiv s hs).prodCongr (ContinuousLinearEquiv.refl ℝ (Space m))).toContinuousAffineEquiv)
  simpa only [ContinuousLinearEquiv.coe_toContinuousAffineEquiv,fiber_positive_base_image] using hh

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
theorem uniform_model_fiber_normalization {k m : ℕ} (hm : 1 ≤ m)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {D : Set E} (hD : IsClosed D) (hneD : D.Nonempty)
    (hmax : ∀ (d : ℕ), m = d+1 → ∀ C' : Set (Space (k+1) × Space d),
      IsModelShape C' → InAffineLimitFamily D C' → False) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ C : Set (Space k × Space m),
      IsModelShape C → InAffineLimitFamily D C → ∀ s : Space k, ∀ hs : ∀ i, 0 < s i,
      ∃ A : Space m ≃L[ℝ] Space m,
        let C' := ((positiveBaseEquiv s hs).prodCongr A) '' C
        IsModelShape C' ∧ InAffineLimitFamily D C' ∧
        closedBall 0 (2/(c+1)) ⊆ modelFiber C' (WithLp.toLp 2 (fun _ => (1:ℝ))) ∧
        modelFiber C' (WithLp.toLp 2 (fun _ => (1:ℝ))) ⊆ closedBall 0 (2*m) := by
  obtain ⟨c,hc,hcenter⟩ := uniform_centering hD hneD hmax
  refine ⟨c,hc,?_⟩
  intro C hC hf s hs
  obtain ⟨A,hin,hout⟩ := centered_body_normalization hm
    (hC.fiber_compact (fun i => (hs i).le)) (hC.fiber_convex s)
    (hC.fiber_interior_nonempty hs) (hC.fiber_zero (fun i => (hs i).le)) hc
    (hcenter C hC hf s hs)
  refine ⟨A,?_⟩
  let C₁ := ((positiveBaseEquiv s hs).prodCongr (ContinuousLinearEquiv.refl ℝ (Space m))) '' C
  have he : ((ContinuousLinearEquiv.refl ℝ (Space k)).prodCongr A) '' C₁ =
      ((positiveBaseEquiv s hs).prodCongr A) '' C := by
    dsimp only [C₁]
    rw [Set.image_image]
    rfl
  have hfib : modelFiber (((positiveBaseEquiv s hs).prodCongr A) '' C)
      (WithLp.toLp 2 (fun _ => (1:ℝ))) = A '' modelFiber C s := by
    rw [← he,fiber_transverse_image]
    congr 1
    exact fiber_positive_base_image s hs
  refine ⟨?_,hf.affine_image hD hneD
    (((positiveBaseEquiv s hs).prodCongr A).toContinuousAffineEquiv),?_,?_⟩
  · rw [← he]
    exact (hC.positive_base_image s hs).transverse_image A
  · simpa only [hfib] using hin
  · simpa only [hfib] using hout

/- The lower-box bound transfers to every approximant simultaneously over
that box, not separately at each s. The radius is uniform in the model. -/
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

end NormalizedCellGeometry



end NormalizedSigmaDependencies
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

end NormalizedSigmaTransport


end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_UniformActualCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section UniformActualCells
open Filter Metric

lemma multiplicativeCell_eq_image {k : ℕ} (s : Space k) (hs : ∀ i, 0 < s i) :
    multiplicativeCell s = (positiveBaseEquiv s hs).symm '' normalizedCell k := by
  ext x
  constructor
  · intro hx
    refine ⟨positiveBaseEquiv s hs x,?_,by simp⟩
    intro i
    change 1/2 ≤ x i/s i ∧ x i/s i ≤ 2
    constructor
    · apply (le_div_iff₀ (hs i)).mpr
      linarith [(hx i).1]
    · exact (div_le_iff₀ (hs i)).mpr (by linarith [(hx i).2])
  · rintro ⟨y,hy,rfl⟩ i
    change s i/2 ≤ s i*y i ∧ s i*y i ≤ 2*s i
    constructor
    · have hh := mul_le_mul_of_nonneg_left (hy i).1 (hs i).le
      linarith
    · have hh := mul_le_mul_of_nonneg_left (hy i).2 (hs i).le
      linarith

/-- Uniform full actual-sigma mass of every multiplicative cell for a maximal
model. The constant is independent of the model, its approximating coordinates,
and the position of the cell. The eventual threshold may depend on the cell.
This is the missing quantitative geometric producer, not a hypothesis about
sigma mass. The sole maximality condition is the source's selection of the
largest possible number of orthant directions. -/
theorem maximal_model_uniform_actual_cells {n k m d : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
    (f : WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmP : AffineMaximalOn Ω u)
    (hcomplete : EuclideanGraphComplete Ω u)
    (hmax : ∀ d' : ℕ, m = d'+1 → ∀ C' : Set (Space (k+1) × Space d'),
      IsModelShape C' → InAffineLimitFamily (sourceEpigraph Ω u) C' → False) :
    ∃ Cσ : ℝ≥0∞, Cσ ≠ ⊤ ∧
      ∀ (C : Set (Space k × Space m)), IsModelShape C →
      InAffineLimitFamily (sourceEpigraph Ω u) C →
      ∀ (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ)),
      LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L j)) C →
      ∀ s : Space k, (∀ i, 0 < s i) → ∀ᶠ j in atTop,
      let H := fun q : Space k × Space m =>
        homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u (a j) (L j)} q.2
      let bE := (EuclideanSpace.basisFun (Fin m) ℝ).reindex eE
      (∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
        ENNReal.ofReal (tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE
          (q.1,q.2)*tubeLogMassWeight H (q.1,q.2))
        ∂(volume.restrict (multiplicativeCell s)).prod (volume : Measure (Space m)).toSphere) ≤ Cσ := by
  let : NeZero k := ⟨by omega⟩
  let : NeZero m := ⟨by omega⟩
  have hclosed := sourceEpigraph_closed hΩ hne hcv hu hp hcomplete
  have hneE : (sourceEpigraph Ω u).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨(x,u x),hx,le_rfl⟩
  obtain ⟨c,hc,hnorm⟩ := uniform_model_fiber_normalization hm hclosed hneE hmax
  have hr : 0 < 2/(c+1) := div_pos (by norm_num) (by linarith)
  obtain ⟨Cσ,hCσ,hbound⟩ := normalized_model_uniform_actual_sigma hn hk hm e eE f hr
    (show (0:ℝ) ≤ 2*m by positivity)
  refine ⟨Cσ,hCσ,?_⟩
  intro C hC hf a L hlim s hs
  obtain ⟨A,hmod,hfam,hin,hout⟩ := hnorm C hC hf s hs
  let B := positiveBaseEquiv s hs
  let N := B.prodCongr A
  let L' := fun j => N.symm.trans (L j)
  let C' := N '' C
  have heq (j : ℕ) : affineEpigraphPullback Ω u (a j) (L' j) =
      N '' affineEpigraphPullback Ω u (a j) (L j) :=
    affineEpigraphPullback_normalize Ω u (a j) (L j) N
  have hclj (j : ℕ) : IsClosed (affineEpigraphPullback Ω u (a j) (L j)) :=
    affineEpigraphPullback_isClosed hclosed (a j) (L j)
  have hnej (j : ℕ) : (affineEpigraphPullback Ω u (a j) (L j)).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    refine ⟨(L j).symm ((x,u x)-a j),?_⟩
    change (a j + (L j) ((L j).symm ((x,u x)-a j))).1 ∈ Ω ∧ _
    simp [hx]
  have hlim' : LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L' j)) C' := by
    have hh := hlim.homeomorph hC.closed ⟨0,hC.zero_mem⟩ hclj hnej N.toHomeomorph
    change LocalDistanceConverges (fun j => N '' affineEpigraphPullback Ω u (a j) (L j)) C' at hh
    simpa only [heq] using hh
  have hclj' (j : ℕ) : IsClosed (affineEpigraphPullback Ω u (a j) (L' j)) :=
    affineEpigraphPullback_isClosed hclosed (a j) (L' j)
  have hcvj' (j : ℕ) : Convex ℝ (affineEpigraphPullback Ω u (a j) (L' j)) :=
    ((sourceEpigraph_convex hΩ hcv hu hp).translate_preimage_right (a j)).linear_preimage
      (L' j).toLinearMap
  have hnej' (j : ℕ) : (affineEpigraphPullback Ω u (a j) (L' j)).Nonempty := by
    rw [heq]
    exact (hnej j).image N
  have hbnd := hbound hΩ hne hcv hu hp hmP hcomplete a L' C' hmod hin hout hlim'
  have hfib := hlim'.eventually_normalized_fibers hmod hclj' hcvj' hnej' hr
    (by norm_num : (0:ℝ)<1/4) (by norm_num : (1/4:ℝ)≤1) (by norm_num : (1:ℝ)≤4) hin hout
  have hncard : n = k+d := by
    have hh := Fintype.card_congr e
    simpa only [Fintype.card_fin,Fintype.card_sum] using hh
  have hcell : B '' multiplicativeCell s = normalizedCell k := by
    rw [multiplicativeCell_eq_image s hs,Set.image_image]
    simp only [B,ContinuousLinearEquiv.apply_symm_apply,Set.image_id']
  have hQ : MeasurableSet (multiplicativeCell s) := by
    rw [multiplicativeCell_eq_image s hs]
    exact B.symm.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (isCompact_normalizedCell k).measurableSet
  filter_upwards [hbnd,hfib] with j hj hfj
  have hK (t : Space k) (ht : t ∈ normalizedCellDomain k) :
      IsCompact {y | (t,y) ∈ affineEpigraphPullback Ω u (a j) (L' j)} := by
    exact (isCompact_closedBall (0:Space m) _).of_isClosed_subset
      ((hclj' j).preimage (continuous_const.prodMk continuous_id))
      (hfj t (fun i => ⟨(ht i).1.le,(ht i).2.le⟩)).2.2
  have hz (t : Space k) (ht : t ∈ normalizedCellDomain k) :
      (0:Space m) ∈ interior {y | (t,y) ∈ affineEpigraphPullback Ω u (a j) (L' j)} :=
    (hfj t (fun i => ⟨(ht i).1.le,(ht i).2.le⟩)).2.1
  have he := affineEpigraph_sigma_normalization hm hncard
    ((EuclideanSpace.basisFun (Fin m) ℝ).reindex eE) hΩ hcv hu hp (a j) (L j) B A
    (fun i => (s i)⁻¹) (fun i => inv_ne_zero (hs i).ne')
    (fun t i => by simp [B,div_eq_mul_inv,mul_comm])
    (isOpen_normalizedCellDomain k) hQ (by rw [hcell]; exact normalizedCell_subset_domain k)
    (fun t ht i => ne_of_gt (lt_of_lt_of_le (half_pos (hs i)) (ht i).1)) hK hz
  dsimp only at he ⊢
  rw [he,hcell]
  exact hj
end UniformActualCells


end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_UniformLogCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section UniformLogCells
open Metric Filter

/-- A pushforward cell is bounded by any enclosing physical base cell. No
integrability or finiteness assumption on the density is used. -/
lemma logTubeMeasure_apply_le_cell {k : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure (Space k)) [SFinite μ] (D : Set (Space k)) (F : Space k × E → ℝ)
    {K Q : Set (Space k)} (hK : MeasurableSet K)
    (hsub : D ∩ logSpace ⁻¹' K ⊆ Q) :
    logTubeMeasure μ D F K ≤
      ∫⁻ q : Space k × sphere (0:E) 1, ENNReal.ofReal (F (tubeLift q))
        ∂(μ.restrict Q).prod (volume : Measure E).toSphere := by
  have hmap : Measurable (fun q : Space k × sphere (0:E) 1 => logSpace q.1) :=
    measurable_logSpace.comp measurable_fst
  rw [logTubeMeasure,Measure.map_apply hmap hK,
    withDensity_apply _ (hK.preimage hmap),Measure.restrict_restrict (hK.preimage hmap),
    Measure.restrict_prod_eq_prod_univ]
  apply lintegral_mono_set
  rintro q ⟨hq,hDq,-⟩
  exact ⟨hsub ⟨hDq,hq⟩,Set.mem_univ _⟩

lemma isClosed_logarithmicUnitCell (k : ℕ) (z : Fin k → ℤ) :
    IsClosed (logarithmicUnitCell k z) := by
  change IsClosed {x : Space k | ∀ i, (z i:ℝ) ≤ x i ∧ x i ≤ (z i:ℝ)+1}
  rw [Set.ofPred_forall]
  apply isClosed_iInter fun i => ?_
  exact (isClosed_le continuous_const (EuclideanSpace.proj i).continuous).inter
    (isClosed_le (EuclideanSpace.proj i).continuous continuous_const)

/-- A logarithmic unit cell fits in the physical factor-four cell about the
exponential of its midpoint. The quantitative inclusion uses log(2)≥1/2. -/
lemma logarithmicUnitCell_preimage_subset {k : ℕ} (z : Fin k → ℤ) :
    positiveOrthant k ∩ logSpace ⁻¹' logarithmicUnitCell k z ⊆
      multiplicativeCell (expSpace (WithLp.toLp 2 (fun i => (z i:ℝ)+1/2))) := by
  rintro s ⟨hs,hz⟩ i
  have hl2 : (1:ℝ)/2 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢
    exact hh
  have hi : Real.log (s i) ∈ Set.Icc (z i:ℝ) ((z i:ℝ)+1) := hz i
  change Real.exp ((z i:ℝ)+1/2)/2 ≤ s i ∧ s i ≤ 2*Real.exp ((z i:ℝ)+1/2)
  constructor
  · apply (Real.log_le_log_iff (div_pos (Real.exp_pos _) (by norm_num)) (hs i)).mp
    rw [Real.log_div (Real.exp_ne_zero _) (by norm_num),Real.log_exp]
    linarith [hi.1]
  · apply (Real.log_le_log_iff (hs i) (mul_pos (by norm_num) (Real.exp_pos _))).mp
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp]
    linarith [hi.2]

lemma affineEpigraphLogMeasure_unitCell_le {n k m d : ℕ} (hm : 1 ≤ m)
    (D : Set (Space k)) (hD : D ⊆ positiveOrthant k)
    (Ω : Set (Space n)) (u : Space n → ℝ) (a : Space n × ℝ)
    (L : (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
    (bE : OrthonormalBasis (Fin d ⊕ Unit) ℝ (Space m)) (z : Fin k → ℤ) :
    affineEpigraphLogMeasure volume D Ω u a L bE (logarithmicUnitCell k z) ≤
      let H := fun q : Space k × Space m =>
        homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
      ∫⁻ q : Space k × sphere (0:Space m) 1,
        ENNReal.ofReal (tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE
          (q.1,q.2)*tubeLogMassWeight H (q.1,q.2))
        ∂(volume.restrict (multiplicativeCell (expSpace (WithLp.toLp 2 (fun i => (z i:ℝ)+1/2))))).prod
          (volume : Measure (Space m)).toSphere := by
  let : NeZero m := ⟨by omega⟩
  let H := fun q : Space k × Space m =>
    homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let F := fun q : Space k × Space m =>
    tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE q * tubeLogMassWeight H q
  exact logTubeMeasure_apply_le_cell volume D F (isClosed_logarithmicUnitCell k z).measurableSet (by
    intro s hs
    exact logarithmicUnitCell_preimage_subset z ⟨hD hs.1,hs.2⟩)

/-- Uniform actual sigma control in every translated logarithmic unit cell,
from the original PDE, completeness, maximal-model normalization, and true
coordinate covariance. There is no cell-mass hypothesis. Suitable regular
base domains may be supplied later when applying the differential inequality. -/
theorem maximal_model_uniform_log_cells {n k m d : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
    (f : WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmP : AffineMaximalOn Ω u)
    (hcomplete : EuclideanGraphComplete Ω u)
    (hmax : ∀ d' : ℕ, m = d'+1 → ∀ C' : Set (Space (k+1) × Space d'),
      IsModelShape C' → InAffineLimitFamily (sourceEpigraph Ω u) C' → False) :
    ∃ Cσ : ℝ, 0 ≤ Cσ ∧
      ∀ (C : Set (Space k × Space m)), IsModelShape C →
      InAffineLimitFamily (sourceEpigraph Ω u) C →
      ∀ (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ)),
      LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L j)) C →
      ∀ (D : ℕ → Set (Space k)), (∀ j, D j ⊆ positiveOrthant k) →
      ∀ z : Fin k → ℤ, ∀ᶠ j in atTop,
      affineEpigraphLogMeasure volume (D j) Ω u (a j) (L j)
        ((EuclideanSpace.basisFun (Fin m) ℝ).reindex eE)
        (logarithmicUnitCell k z) ≤ ENNReal.ofReal Cσ := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨Cσ,hCσ,hbound⟩ := maximal_model_uniform_actual_cells hn hk hm e eE f
    hΩ hne hcv hu hp hmP hcomplete hmax
  refine ⟨Cσ.toReal,ENNReal.toReal_nonneg,?_⟩
  intro C hC hf a L hlim D hD z
  have hb := hbound C hC hf a L hlim (expSpace (WithLp.toLp 2 (fun i => (z i:ℝ)+1/2)))
    (fun i => Real.exp_pos _)
  filter_upwards [hb] with j hj
  rw [ENNReal.ofReal_toReal hCσ]
  exact (affineEpigraphLogMeasure_unitCell_le hm (D j) (hD j) Ω u (a j) (L j)
    ((EuclideanSpace.basisFun (Fin m) ℝ).reindex eE) z).trans hj
end UniformLogCells


end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_LogCellBound
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
/- Closed unit cells in the actual logarithmic base coordinates. -/
/- A fixed logarithmic box is covered by `(2R+1)^k` translated unit cells,
including its boundary and the zero-dimensional endpoint. -/
lemma logarithmicBox_subset_unitCells (k R : ℕ) :
    logarithmicBox k R ⊆ ⋃ q : Fin k → Fin (2*R+1),
      logarithmicUnitCell k (fun i => ((q i).val : ℤ)-(R:ℤ)) := by
  intro x hx
  have hb (i : Fin k) : 0 ≤ x i+(R:ℝ) ∧ x i+(R:ℝ) ≤ (2*R:ℕ) := by
    obtain ⟨hl,hu⟩ := abs_le.mp (hx i)
    constructor <;> push_cast <;> linarith
  let q : Fin k → Fin (2*R+1) := fun i =>
    ⟨⌊x i+(R:ℝ)⌋₊,by have hh := Nat.floor_le_of_le (hb i).2; omega⟩
  apply mem_iUnion.mpr
  refine ⟨q,?_⟩
  intro i
  have hl := Nat.floor_le (hb i).1
  have hu := Nat.lt_floor_add_one (x i+(R:ℝ))
  change ((⌊x i+(R:ℝ)⌋₊ : ℤ)-(R:ℤ):ℤ) ≤ x i ∧ x i ≤ _
  push_cast
  constructor <;> linarith

/- Uniform nonnegative cell mass implies the exact polynomial box growth
used by the source contradiction. No simultaneous large-box convergence is
required: only finitely many cell estimates are used for each fixed box. -/
theorem measure_logarithmicBox_bound_of_unitCells {k R : ℕ} (μ : Measure (Space k))
    {C : ℝ≥0∞} (_hC : C ≠ ⊤)
    (hcell : ∀ q : Fin k → Fin (2*R+1),
      μ (logarithmicUnitCell k (fun i => ((q i).val : ℤ)-(R:ℤ))) ≤ C) :
    μ (logarithmicBox k R) ≤ ((2*R+1:ℕ):ℝ≥0∞)^k*C := by
  calc
    _ ≤ μ (⋃ q : Fin k → Fin (2*R+1),
      logarithmicUnitCell k (fun i => ((q i).val : ℤ)-(R:ℤ))) :=
        measure_mono (logarithmicBox_subset_unitCells k R)
    _ ≤ ∑ q : Fin k → Fin (2*R+1),
      μ (logarithmicUnitCell k (fun i => ((q i).val : ℤ)-(R:ℤ))) :=
        measure_iUnion_fintype_le μ _
    _ ≤ ∑ _ : Fin k → Fin (2*R+1), C := Finset.sum_le_sum (fun q _ => hcell q)
    _ = _ := by simp

/- Pointwise-eventual cell bounds are sufficient for uniformly polynomial
box mass; the threshold may depend on the box, just as in the manuscript. -/
theorem eventual_logarithmicBox_bound_of_unitCells {k : ℕ} (μ : ℕ → Measure (Space k))
    {C : ℝ} (hC : 0 ≤ C)
    (hcell : ∀ z : Fin k → ℤ, ∀ᶠ j in atTop,
      μ j (logarithmicUnitCell k z) ≤ ENNReal.ofReal C) (R : ℕ) :
    ∀ᶠ j in atTop, (μ j).real (logarithmicBox k R) ≤ (2^k*C)*(R+1:ℝ)^k := by
  have hh : ∀ᶠ j in atTop, ∀ q : Fin k → Fin (2*R+1),
      μ j (logarithmicUnitCell k (fun i => ((q i).val : ℤ)-(R:ℤ))) ≤ ENNReal.ofReal C :=
    Filter.eventually_all.mpr (fun _ => hcell _)
  filter_upwards [hh] with j hj
  have hm := measure_logarithmicBox_bound_of_unitCells (μ j) ENNReal.ofReal_ne_top hj
  have ht : ((2*R+1:ℕ):ℝ≥0∞)^k*ENNReal.ofReal C ≠ ⊤ := by finiteness
  have hr := ENNReal.toReal_mono ht hm
  simp only [Measure.real]
  apply hr.trans
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_natCast,ENNReal.toReal_ofReal hC]
  rw [show (2^k*C)*(R+1:ℝ)^k = (2*((R:ℝ)+1))^k*C by rw [mul_pow]; ring]
  apply mul_le_mul_of_nonneg_right _ hC
  apply pow_le_pow_left₀ (by positivity)
  push_cast
  linarith

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ActualLogCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

section ActualGrowthDependencies
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter Metric
open scoped Topology

section ActualLogCells
open Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

/- The exact analytic log-growth contradiction, reduced to a uniform bound on
each fixed unit cell of the genuine sigma measure. This is an intermediate
criterion: the model geometry must still produce its two mass hypotheses. -/
theorem affineMaximal_no_eventual_bounded_log_cells {n k l₀ : ℕ}
    (hn : 3 ≤ n) (hn9 : n ≤ 9) (hk : 2 ≤ k) (hkn : k ≤ n)
    {μ : Measure (Space k)} [μ.IsAddHaarMeasure]
    (Ω : ℕ → Set (Space n)) (u : ℕ → Space n → ℝ)
    (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × E) ≃L[ℝ] (Space n × ℝ))
    (D : ℕ → Set (Space k)) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hΩ : ∀ j, IsOpen (Ω j)) (hcv : ∀ j, Convex ℝ (Ω j))
    (hu : ∀ j, ContDiffOn ℝ ∞ (u j) (Ω j))
    (hp : ∀ j x, x ∈ Ω j → (hessian (u j) x).PosDef)
    (hm : ∀ j, AffineMaximalOn (Ω j) (u j))
    (hD : ∀ j, IsOpen (D j)) (hDpos : ∀ j, D j ⊆ positiveOrthant k)
    (hK : ∀ j s, s ∈ D j → IsCompact {y | (s,y) ∈ affineEpigraphPullback (Ω j) (u j) (a j) (L j)})
    (hzero : ∀ j s, s ∈ D j →
      (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback (Ω j) (u j) (a j) (L j)})
    (havail : ∀ R : ℕ, l₀ ≤ R → ∀ᶠ j in atTop, logarithmicBox k R ⊆ logSpace '' (D j))
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hpos : ∀ᶠ j in atTop, c ≤
      (affineEpigraphLogMeasure μ (D j) (Ω j) (u j) (a j) (L j) bE).real (logarithmicBox k l₀))
    (hcell : ∀ z : Fin k → ℤ, ∀ᶠ j in atTop,
      affineEpigraphLogMeasure μ (D j) (Ω j) (u j) (a j) (L j) bE
        (logarithmicUnitCell k z) ≤ ENNReal.ofReal C) : False := by
  apply affineMaximal_no_polynomial_logMeasure hn hn9 hk hkn Ω u a L D bE
    hΩ hcv hu hp hm hD hDpos hK hzero havail hc hpos
  intro R _
  exact eventual_logarithmicBox_bound_of_unitCells
    (fun j => affineEpigraphLogMeasure μ (D j) (Ω j) (u j) (a j) (L j) bE) hC hcell R
end ActualLogCells

-- END

end ActualGrowthDependencies

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_NoNormalizedMaximalModel
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

open Metric Filter
/-- The actual analytic contradiction excludes every normalized maximal model
with at least two orthant directions. None of its mass bounds is an assumption. -/
theorem affineMaximal_no_normalized_maximal_model_oai {n k m d : ℕ}
    (hn : 3 ≤ n) (hn9 : n ≤ 9) (hk : 2 ≤ k) (hm : 1 ≤ m)
    (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
    (f : WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmP : AffineMaximalOn Ω u)
    (hcomplete : EuclideanGraphComplete Ω u)
    (hmax : ∀ d' : ℕ, m = d'+1 → ∀ C' : Set (Space (k+1) × Space d'),
      IsModelShape C' → InAffineLimitFamily (sourceEpigraph Ω u) C' → False)
    (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
    {C : Set (Space k × Space m)} (hC : IsModelShape C)
    (hf : InAffineLimitFamily (sourceEpigraph Ω u) C)
    (hlim : LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L j)) C)
    {r R₀ : ℝ} (hr : 0 < r)
    (hin : closedBall (0:Space m) r ⊆ modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R₀) : False := by
  let : NeZero m := ⟨by omega⟩
  have hn1 : 1 ≤ n := by omega
  have hk1 : 1 ≤ k := by omega
  have hkn : k ≤ n := by
    have hh := Fintype.card_congr e
    simp only [Fintype.card_fin,Fintype.card_sum] at hh
    omega
  let D := fun j => regularPositiveFiberDomain (affineEpigraphPullback Ω u (a j) (L j))
  let bE := (EuclideanSpace.basisFun (Fin m) ℝ).reindex eE
  obtain ⟨T,c,hc,hpos⟩ := normalized_model_positive_log_mass hn1 hk1 hm e eE f
    hΩ hne hcv hu hp hmP hcomplete a L hC hlim hr hin hout
  obtain ⟨Cσ,hCσ,hcell⟩ := maximal_model_uniform_log_cells hn1 hk1 hm e eE f
    hΩ hne hcv hu hp hmP hcomplete hmax
  have hclosed := sourceEpigraph_closed hΩ hne hcv hu hp hcomplete
  have hclj j : IsClosed (affineEpigraphPullback Ω u (a j) (L j)) := affineEpigraphPullback_isClosed hclosed _ _
  have hcvj j : Convex ℝ (affineEpigraphPullback Ω u (a j) (L j)) :=
    ((sourceEpigraph_convex hΩ hcv hu hp).translate_preimage_right (a j)).linear_preimage (L j).toLinearMap
  have hnej j : (affineEpigraphPullback Ω u (a j) (L j)).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    refine ⟨(L j).symm ((x,u x)-a j),?_⟩
    change (a j + (L j) ((L j).symm ((x,u x)-a j))).1 ∈ Ω ∧ _
    simp [hx]
  refine affineMaximal_no_eventual_bounded_log_cells hn hn9 hk hkn (fun _ => Ω) (fun _ => u) a L D bE
    (fun _ => hΩ) (fun _ => hcv) (fun _ => hu) (fun _ => hp) (fun _ => hmP)
    (fun _ => regularPositiveFiberDomain_isOpen _)
    (fun _ => regularPositiveFiberDomain_positive _)
    (fun _ _ hs => regularPositiveFiberDomain_compact _ hs)
    (fun _ _ hs => regularPositiveFiberDomain_zero _ hs) (l₀ := T) ?_ hc hCσ hpos ?_
  · intro R _
    exact hlim.eventually_regular_logBox hC hclj hcvj hnej hr hin hout R
  · exact hcell C hC hf a L hlim D (fun _ => regularPositiveFiberDomain_positive _)

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

/- The local distance-function topology used in geometry.tex:70–101. Sets
are separately required to be nonempty and closed when those properties enter. -/
/- Every point of a local limit has an actual sequence of nearby points
in the approximating closed convex bodies (convexity is not needed here). -/
/- Local convergence prevents approximants from meeting any fixed compact
set disjoint from the closed limit. -/
/- Limits of convergent points of approximants belong to the local limit. -/
/- Uniform cap compactness, geometry.tex:104–125. The proof traps a chord
on a fixed compact sphere, rather than choosing escaping directions. -/
/- A point on the top of a limit cap is approximated from strictly below
its top by contracting toward a fixed strict point. -/
/- Reverse Hausdorff inclusion for a compact cap. -/
/- Full Hausdorff cap convergence, geometry.tex:104–125, with no asserted
smoothness of the limiting boundary. -/
/- Compactness of the bounded-at-one-point nonnegative unit-Lipschitz
family in the compact-open topology. This is the actual Arzelà–Ascoli input
for local convex-set compactness. -/
/- Extract locally uniformly convergent distance functions. At this stage
we do not yet assert that the limit is a distance function. -/
/- A pointwise limit of nonnegative unit-Lipschitz distance functions of
nonempty closed sets, on a proper space, is itself their zero-set's distance
function. Nearest points supply the nonempty zero set and attain the distance. -/
/- Local compactness of nonempty closed convex sets meeting a fixed bounded
set, the extraction used in geometry.tex:70–101. The topology and the limit
are literal sets and Euclidean distance functions. -/

/- Quantitative inner containment from distance-function closeness. This is
an actual projection argument for convex bodies, not an assumed stability axiom. -/
/- An interior ball of the limit has a fixed smaller ball lying in the
interiors of all late approximants. -/
/- Compact subsets of the interior are eventually interior subsets of the
approximants, as required by the model normalization argument. -/

open Filter Metric
open scoped Topology Pointwise

/- The geometric conditions of a k-model, in its distinguished coordinates.
Membership in the affine local-limit family is separate from these conditions. -/
/- The transverse fiber, including lower-dimensional and boundary fibers. -/
/- The ray containment recession argument in geometry.tex does not need
full-dimensionality. -/

open scoped Pointwise

/- The coordinate action of the actual matrix linear equivalence. -/
/- A convex combination allowing unused mass at the origin. -/
/- The cross-polytope spanned by any points of a symmetric convex body lies
in that body. This is the inner-inclusion half of max-determinant normalization. -/
/- The exact ℓ¹/Euclidean comparison used for the inner ball. -/
/- The exact ℓ∞/Euclidean comparison used for the outer ball. -/
/- A compact body's column determinant has a maximizer, with nonzero value
whenever the body contains a ball about zero. -/
/- Maximal determinant makes each inverse coordinate of a body point at most
one. The proof is the literal one-column replacement identity. -/
/- The symmetric max-determinant normalization, with the exact weaker radius
n sufficient for all centered normalizations used in the source. -/
open scoped Pointwise

/- Exact centered normalization in geometry.tex (2/(C+1), 2n), proved
without importing John's theorem: first normalize the symmetric difference
body, then use the actual balance inclusion. -/
/- A dimension-only inscribed ball in the standard simplex. This allows
noncentered model fibers to be normalized without importing John's theorem. -/
/- A linear normalization of an arbitrary full-dimensional compact convex
body containing the distinguished origin. The dimension-only outer radius
is intentionally not John's sharp radius; it suffices for the compactness
argument and does not alter the source's final centered normalization. -/
/- The same intermediate normalization with the zero-dimensional convention
made explicit. Its radii are only used in compactness arguments. -/

/- A nonzero real functional has full range. -/
/- A nonzero support is strictly positive at every interior point. -/
/- The literal split along a normalized support vector. The second component
is the kernel of the support; no quotient or degenerate coordinate is used. -/
/- Coordinates which keep the support as the first coordinate and send a
chosen interior point of a convex fiber to (1,0). Scaling the support, rather
than translating the body, preserves the ambient origin and all recession rays. -/

/- Append one real base coordinate, placing it first in Fin (k+1). -/
open Filter Metric
open scoped Topology Pointwise

end AffineBernstein

end

end OAI
end

theorem solution : type_of% @OAI.AffineBernstein.affineMaximal_no_normalized_maximal_model_oai := @OAI.AffineBernstein.affineMaximal_no_normalized_maximal_model_oai
