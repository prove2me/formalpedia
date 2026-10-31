-- Prove2me | solution 1 for OAI.AffineBernstein.affine_bernstein
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:10:13.283915+00:00
-- url     : https://prove2.me/submissions/f560568d-dd67-434c-abff-1e1f3b552606

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000
import Theorems.Thm_OAI_AffineBernstein_affineMaximal_no_normalized_maximal_model
import Theorems.Thm_OAI_AffineBernstein_balanced_constant_hessian
import Theorems.Thm_OAI_AffineBernstein_complete_affineMaximal_model_transverse_pos

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

omit [ProperSpace E] in
theorem of_affine_image (hD : IsClosed D) (hvD : Convex ℝ D)
    (hiD : (interior D).Nonempty) (A : E ≃ᴬ[ℝ] F) :
    InAffineLimitFamily D (A '' D) := by
  refine ⟨A.toHomeomorph.isClosedMap _ hD, hvD.affine_image A.toAffineEquiv.toAffineMap, ?_, ?_⟩
  · change (interior (A.toHomeomorph '' D)).Nonempty
    rw [← A.toHomeomorph.image_interior]
    exact hiD.image A.toHomeomorph
  · exact ⟨fun _ => A, LocalDistanceConverges.of_pointwise (fun _ => tendsto_const_nhds)⟩

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
-- module Solutions.OAIQ22_AB.AffineBernstein_AffineImageCoordinates
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

section AffineImageCoordinates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma continuousAffineEquiv_decomposition (A : E ≃ᴬ[ℝ] F) (x : E) :
    A x = A.toAffineEquiv.linear x + A 0 := by
  have h := A.toAffineEquiv.map_vadd (0:E) x
  simpa only [vadd_eq_add,zero_add,add_zero,ContinuousAffineEquiv.coe_coe] using h

lemma continuousAffineEquiv_inverse_decomposition (A : E ≃ᴬ[ℝ] F) (x : E) :
    A x = A.toAffineEquiv.linear (x-A.symm 0) := by
  have h := continuousAffineEquiv_decomposition A (A.symm 0)
  rw [ContinuousAffineEquiv.apply_symm_apply] at h
  rw [continuousAffineEquiv_decomposition A x, map_sub]
  have hh : A 0 = -A.toAffineEquiv.linear (A.symm 0) := by
    exact eq_neg_of_add_eq_zero_right h.symm
  rw [hh, sub_eq_add_neg]

/-- Rewrite the actual affine-image sequence in the exact pullback coordinates
used throughout the PDE support estimates. -/
theorem InAffineLimitFamily.epigraph_pullback_approximation {n k m : ℕ}
    {Ω : Set (Space n)} {u : Space n → ℝ} {C : Set (Space k × Space m)}
    (hf : InAffineLimitFamily (sourceEpigraph Ω u) C) :
    ∃ a : ℕ → Space n × ℝ, ∃ L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ),
      LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L j)) C := by
  obtain ⟨A,hA⟩ := hf.approximation
  let a := fun j => (A j).symm 0
  let L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ) :=
    fun index =>
      { (A index).toAffineEquiv.linear.symm with
        continuous_toFun := (A index).symm.toContinuousAffineMap.contLinear.continuous
        continuous_invFun := (A index).toContinuousAffineMap.contLinear.continuous }
  refine ⟨a,L,?_⟩
  have he j : affineEpigraphPullback Ω u (a j) (L j) = A j '' sourceEpigraph Ω u := by
    ext p
    constructor
    · intro hp
      refine ⟨a j + L j p,hp,?_⟩
      rw [continuousAffineEquiv_inverse_decomposition]
      change (A j).toAffineEquiv.linear ((a j + L j p)-a j) = p
      rw [add_sub_cancel_left]
      exact (A j).toAffineEquiv.linear.apply_symm_apply p
    · rintro ⟨x,hx,rfl⟩
      have hax : a j + L j (A j x) = x := by
        rw [continuousAffineEquiv_inverse_decomposition]
        change a j + (A j).toAffineEquiv.linear.symm ((A j).toAffineEquiv.linear (x-a j)) = x
        rw [(A j).toAffineEquiv.linear.symm_apply_apply,add_sub_cancel]
      simpa only [affineEpigraphPullback,sourceEpigraph,Set.mem_ofPred_eq,hax] using hx
  simpa only [he] using hA
end AffineImageCoordinates


end
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

lemma sourceEpigraph_closed {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) : IsClosed (sourceEpigraph Ω u) :=
  isClosed_epigraph_of_complete hΩ hne hu
    (convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)) hc

end CompletePositiveCap

open Metric

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_QuadraticIntegration
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The last, purely analytic step of the rescaling argument: a C³ function
with zero third derivative everywhere is exactly its quadratic Taylor polynomial. -/
theorem quadratic_of_third_fderiv_zero (f : E → ℝ) (hf : ContDiff ℝ 3 f)
    (hthird : ∀ x, fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x = 0) :
    ∀ x, f x = (1 / 2 : ℝ) * (fderiv ℝ (fderiv ℝ f) 0 x x) +
      fderiv ℝ f 0 x + f 0 := by
  let B := fderiv ℝ (fderiv ℝ f) 0
  let L := fderiv ℝ f 0
  have hf₂ : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hf₁ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ f)) :=
    hf₂.fderiv_right (by norm_num)
  have hB (x : E) : fderiv ℝ (fderiv ℝ f) x = B :=
    is_const_of_fderiv_eq_zero (hf₁.differentiable (by norm_num)) hthird x 0
  have hL (x : E) : fderiv ℝ f x = B x + L := by
    have hd (y : E) : HasFDerivAt (fun z => fderiv ℝ f z - B z)
        (0 : E →L[ℝ] E →L[ℝ] ℝ) y := by
      convert (((hf₂.differentiable (by norm_num)) y).hasFDerivAt.sub
        (B.hasFDerivAt (x := y))) using 1
      all_goals try with_reducible_and_instances rfl
      rw [hB, sub_self]
    have heq := is_const_of_fderiv_eq_zero (fun y => (hd y).differentiableAt)
      (fun y => (hd y).fderiv) x 0
    simp only [map_zero, sub_zero] at heq
    simpa only [add_comm] using sub_eq_iff_eq_add.mp heq
  have hsym (x y : E) : B x y = B y x := by
    exact (hf.contDiffAt.isSymmSndFDerivAt (by norm_num)) x y
  let q : E → ℝ := fun x => (1 / 2 : ℝ) * (B x x) + L x + f 0
  have hq (x : E) : HasFDerivAt q (B x + L) x := by
    have hBi : HasFDerivAt (fun y => B y y) (B x + B.flip x) x := by
      convert B.hasFDerivAt.clm_apply (hasFDerivAt_id (𝕜 := ℝ) x) using 1 <;>
        rfl
    have hBx : B.flip x = B x := by
      ext y
      exact hsym y x
    have hhalf : (1 / 2 : ℝ) • (B x + B.flip x) = B x := by
      rw [hBx, ← two_smul ℝ (B x), smul_smul]
      norm_num
    convert ((hBi.const_mul (1 / 2 : ℝ)).add (L.hasFDerivAt (x := x))).add_const (f 0)
      using 1
    all_goals try with_reducible_and_instances rfl
    simp only [hhalf]
  have hd (x : E) : HasFDerivAt (fun y => f y - q y) (0 : E →L[ℝ] ℝ) x := by
    convert (((hf.differentiable (by norm_num)) x).hasFDerivAt.sub (hq x)) using 1
    all_goals try with_reducible_and_instances rfl
    rw [hL, sub_self]
  intro x
  have hconst := is_const_of_fderiv_eq_zero (fun y => (hd y).differentiableAt)
    (fun y => (hd y).fderiv) x 0
  simp only [q, map_zero, mul_zero, zero_add, sub_self] at hconst
  exact sub_eq_zero.mp hconst

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ConstantHessianQuadratic
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

section ConstantHessianQuadratic

lemma second_fderiv_bilinear_eq_sum {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (v w : Space n) :
    fderiv ℝ (fderiv ℝ u) x v w = ∑ i, ∑ j, v i*hessian u x i j*w j := by
  calc
    _ = fderiv ℝ (fderiv ℝ u) x (∑ i, v i • coordinateVector n i)
        (∑ j, w j • coordinateVector n j) := by rw [sum_coordinateVector,sum_coordinateVector]
    _ = _ := by
      simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hessian_eq_second hu]
      ring

lemma quadratic_of_constant_hessian {n : ℕ} {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u)
    (hH : ∀ x y, hessian u x=hessian u y) :
    ∀ x, u x = (1/2:ℝ)*(∑ i, ∑ j, x i*hessian u 0 i j*x j)+fderiv ℝ u 0 x+u 0 := by
  have he : fderiv ℝ (fderiv ℝ u) = fun _ => fderiv ℝ (fderiv ℝ u) 0 := by
    funext x
    ext v w
    rw [second_fderiv_bilinear_eq_sum hu.contDiffAt,second_fderiv_bilinear_eq_sum hu.contDiffAt,hH x 0]
  have ht (x : Space n) : fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x=0 := by
    rw [he]
    simp
  intro x
  rw [quadratic_of_third_fderiv_zero u (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)) ht x,second_fderiv_eq_sum hu.contDiffAt]

lemma continuousLinearMap_coordinate_sum {n : ℕ} (L : Space n →L[ℝ] ℝ) (x : Space n) :
    L x=∑ i, L (coordinateVector n i)*x i := by
  calc
    _ = L (∑ i, x i • coordinateVector n i) := by rw [sum_coordinateVector]
    _ = _ := by simp only [map_sum,map_smul,smul_eq_mul,mul_comm]

end ConstantHessianQuadratic


end
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

open Filter Metric
open scoped Topology Pointwise

/- The lower inclusion in geometry.tex (normalized-fiber-box), with the
source's exact radius a*r. It is a convexity/recession consequence. -/
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

end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_ModelCenteringFurther
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
open scoped Topology Pointwise
open scoped Pointwise
open scoped Pointwise

open Filter
open scoped Topology

/- Intrinsic convergence always entails convergence of base points. -/
/- Completeness prevents a finite base endpoint from being lost when graph
paths make a sequence intrinsically Cauchy. -/
/- A chord bound along a family of segments turns ordinary Cauchy control of
base and height into control for the actual graph metric. -/
/- Restricting a monotone-height ray to any oriented subsegment gives the
uniform chord bound used to exhibit an intrinsic Cauchy tail. -/
/- A bounded ray with monotone graph height cannot end at a missing finite
base point of a complete graph. This proves the metric step rather than
assuming properness of the embedding. -/
/- A differentiable convex function on a finite half-open interval has a
monotone tail (in one of the two orientations). -/
/- The tangent line at the initial point bounds a convex ray from below,
so an upper bound on a finite ray implies a two-sided bound. -/
/- Completeness forbids any bounded convex ray from reaching a missing finite
endpoint. Convexity and two-sided variation, not a growth hypothesis, produce
the required metric Cauchy sequence. -/
/- The metric obstruction applied to an arbitrary bounded-height sequence,
not merely points already lying on a fixed ray. This is the core boundary
properness argument in geometry.tex:36–55. -/
/- Actual height sublevels are closed in the ambient base space. No convex
extension of u to missing boundary points is used. -/
/- Finite boundary blow-up, derived from the manuscript's literal Euclidean
intrinsic completeness assumption. -/
/- The epigraph is genuinely closed in Rⁿ × R. Completeness was not
silently replaced by properness of the graph embedding. -/
/- Strict version of the second-derivative test, with specified derivatives. -/
theorem strictConvexOn_of_hasDerivWithinAt2_pos {D : Set ℝ} (hD : Convex ℝ D)
    {f f' f'' : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'' : ∀ x ∈ interior D, HasDerivWithinAt f' (f'' x) (interior D) x)
    (hf''₀ : ∀ x ∈ interior D, 0 < f'' x) : StrictConvexOn ℝ D f := by
  have he : (interior D).EqOn (deriv f) f' := deriv_eqOn isOpen_interior hf'
  refine strictConvexOn_of_deriv2_pos hD hf fun x hx => ?_
  convert hf''₀ x hx using 1
  all_goals try with_reducible_and_instances rfl
  dsimp
  rw [deriv_eqOn isOpen_interior (fun y hy => ?_) hx]
  exact (hf'' _ hy).congr he (by rw [he hy])

/- The standing Hessian hypothesis gives strict convexity on every nonconstant
base segment, with the literal coordinate Hessian, not an abstract Hessian. -/
theorem strictConvexOn_segment {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {x y : Space n} (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : y ≠ x) :
    StrictConvexOn ℝ (Icc (0 : ℝ) 1) (fun t => u (x + t • (y - x))) := by
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
  exact strictConvexOn_of_hasDerivWithinAt2_pos (convex_Icc _ _) hf hdf hdd
    (fun t ht => second_fderiv_pos
      (hu.contDiffAt (hΩ.mem_nhds (hseg t (interior_subset ht))))
      (hp _ (hseg t (interior_subset ht))) (sub_ne_zero.mpr hxy))

/- The tangent-plane height used in all source sections. -/

theorem tangentHeight_pos {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {a x : Space n} (ha : a ∈ Ω) (hx : x ∈ Ω) (hxa : x ≠ a) :
    0 < tangentHeight u a x := by
  have hc := strictConvexOn_segment hΩ hcv hu hp ha hx hxa
  have hd : HasDerivAt (fun t : ℝ => u (a + t • (x - a)))
      (fderiv ℝ u a (x - a)) 0 := by
    have hγ : HasDerivAt (fun t : ℝ => a + t • (x - a)) (x - a) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (x - a)).const_add a
    have hdu : HasFDerivAt u (fderiv ℝ u a) (a + (0 : ℝ) • (x - a)) := by
      simpa using ((hu.contDiffAt (hΩ.mem_nhds ha)).differentiableAt (by simp)).hasFDerivAt
    exact hdu.comp_hasDerivAt 0 hγ
  have hs := hc.lt_slope_of_hasDerivAt (x := 0) (y := 1)
    (by norm_num) (by norm_num) (by norm_num) hd
  simp only [slope_def_field, sub_zero, div_one, zero_smul, add_zero, one_smul,
    add_sub_cancel] at hs
  exact sub_pos.mpr hs

theorem convexOn_tangentHeight {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hcv : ConvexOn ℝ Ω u) (a : Space n) :
    ConvexOn ℝ Ω (tangentHeight u a) := by
  refine ⟨hcv.1, ?_⟩
  intro x hx y hy s t hs ht hst
  have he := hcv.2 hx hy hs ht hst
  have hv : s • x + t • y - a = s • (x - a) + t • (y - a) := by
    rw [smul_sub, smul_sub]
    have heq : s • a + t • a = a := by rw [← add_smul, hst, one_smul]
    calc
      _ = s • x + t • y - (s • a + t • a) := by rw [heq]
      _ = _ := by module
  simp only [tangentHeight, hv, map_add, map_smul, smul_eq_mul]
  simp only [smul_eq_mul] at he
  have heq : s * u a + t * u a = u a := by rw [← add_mul, hst, one_mul]
  nlinarith

theorem continuousOn_tangentHeight {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hu : ContinuousOn u Ω) (a : Space n) :
    ContinuousOn (tangentHeight u a) Ω := by
  exact (hu.sub continuousOn_const).sub
    ((fderiv ℝ u a).continuous.comp (continuous_id.sub continuous_const)).continuousOn

/- Tangent-plane sublevels are closed, by closedness of the actual epigraph.
No implicit completeness-invariance under a shear is needed. -/
theorem isClosed_tangent_sublevel {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hcv : ConvexOn ℝ Ω u)
    (hc : EuclideanGraphComplete Ω u) (a : Space n) (t : ℝ) :
    IsClosed {x | x ∈ Ω ∧ tangentHeight u a x ≤ t} := by
  have he := isClosed_epigraph_of_complete hΩ hne hu hcv hc
  have hf : Continuous (fun x : Space n => (x, u a + fderiv ℝ u a (x - a) + t)) :=
    continuous_id.prodMk ((continuous_const.add
      ((fderiv ℝ u a).continuous.comp (continuous_id.sub continuous_const))).add continuous_const)
  convert he.preimage hf using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_ofPred_eq, mem_preimage, tangentHeight]
  constructor <;> rintro ⟨hx, hh⟩ <;> exact ⟨hx, by linarith⟩

/- A finite-radius positive support gap yields a linear coercivity bound.
This replaces only the choice of constants in geometry.tex:56–67, not any
standing hypothesis or conclusion. -/
theorem tangentHeight_coercive {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {a : Space n} (ha : a ∈ Ω) :
    ∃ r > 0, ∃ m > 0, ∀ x ∈ Ω, r ≤ ‖x - a‖ →
      m * ‖x - a‖ ≤ r * tangentHeight u a x := by
  obtain ⟨R, hR, hRΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds ha)
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hrΩ : Metric.closedBall a r ⊆ Ω :=
    (Metric.closedBall_subset_ball (by dsimp [r]; linarith)).trans hRΩ
  have hcu := convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hcg := convexOn_tangentHeight hcu a
  have hct := continuousOn_tangentHeight hu.continuousOn a
  have hsΩ : Metric.sphere a r ⊆ Ω := Metric.sphere_subset_closedBall.trans hrΩ
  obtain ⟨m, hm, hmlow⟩ : ∃ m : ℝ, 0 < m ∧
      ∀ x ∈ Metric.sphere a r, m ≤ tangentHeight u a x := by
    by_cases hne : (Metric.sphere a r).Nonempty
    · obtain ⟨y, hy, hmin⟩ := (isCompact_sphere a r).exists_isMinOn hne (hct.mono hsΩ)
      refine ⟨tangentHeight u a y, tangentHeight_pos hΩ hcv hu hp ha (hsΩ hy) ?_, hmin⟩
      intro he
      subst y
      have hh : (0 : ℝ) = r := by simpa [Metric.mem_sphere] using hy
      linarith
    · refine ⟨1, zero_lt_one, ?_⟩
      intro x hx
      exact False.elim (hne ⟨x, hx⟩)
  refine ⟨r, hr, m, hm, ?_⟩
  intro x hx hxr
  have hn : 0 < ‖x - a‖ := hr.trans_le hxr
  let q := r / ‖x - a‖
  have hq : 0 < q := div_pos hr hn
  have hq1 : q ≤ 1 := (div_le_one hn).mpr hxr
  let y := a + q • (x - a)
  have hyn : ‖y - a‖ = r := by
    simp only [y, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hq]
    exact div_mul_cancel₀ r hn.ne'
  have hys : y ∈ Metric.sphere a r := by simpa only [Metric.mem_sphere, dist_eq_norm] using hyn
  have hv : (1 - q) • a + q • x = y := by dsimp [y]; module
  have hineq := hcg.2 ha hx (sub_nonneg.mpr hq1) hq.le (show (1 - q) + q = 1 by ring)
  rw [hv, tangentHeight_self] at hineq
  simp only [smul_eq_mul, mul_zero, zero_add] at hineq
  have hmm : m ≤ r / ‖x - a‖ * tangentHeight u a x := (hmlow y hys).trans hineq
  have heq : r / ‖x - a‖ * tangentHeight u a x =
      (r * tangentHeight u a x) / ‖x - a‖ := by ring
  rw [heq] at hmm
  exact (le_div_iff₀ hn).mp hmm

/- The compact tangent sections required throughout the manuscript, proved
from PD Hessian, convexity of the open base, and intrinsic graph completeness. -/
theorem isCompact_tangent_sublevel {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) {a : Space n} (ha : a ∈ Ω) (t : ℝ) :
    IsCompact {x | x ∈ Ω ∧ tangentHeight u a x ≤ t} := by
  have hcu := convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hclosed := isClosed_tangent_sublevel hΩ ⟨a, ha⟩ hu hcu hc a t
  obtain ⟨r, hr, m, hm, hbound⟩ := tangentHeight_coercive hΩ hcv hu hp ha
  apply (isCompact_closedBall a (max r (r * t / m))).of_isClosed_subset hclosed
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  by_cases hxr : r ≤ ‖x - a‖
  · apply le_trans _ (le_max_right _ _)
    apply (le_div_iff₀ hm).mpr
    have hb := (hbound x hx.1 hxr).trans (mul_le_mul_of_nonneg_left hx.2 hr.le)
    simpa [mul_comm] using hb
  · exact (le_of_not_ge hxr).trans (le_max_left _ _)

theorem tangentHeight_nonneg {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {a x : Space n} (ha : a ∈ Ω) (hx : x ∈ Ω) :
    0 ≤ tangentHeight u a x := by
  by_cases hxa : x = a
  · simp [hxa]
  · exact (tangentHeight_pos hΩ hcv hu hp ha hx hxa).le

/- Interior of the epigraph, including the correct restriction to the open
base domain. This is a local continuity fact and needs no completeness. -/
theorem interior_epigraph {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContinuousOn u Ω) :
    interior {p : Space n × ℝ | p.1 ∈ Ω ∧ u p.1 ≤ p.2} =
      {p | p.1 ∈ Ω ∧ u p.1 < p.2} := by
  have hopen : IsOpen {p : Space n × ℝ | p.1 ∈ Ω ∧ u p.1 < p.2} := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have h1 : ∀ᶠ q : Space n × ℝ in 𝓝 p, q.1 ∈ Ω :=
      (continuous_fst.tendsto p) (hΩ.mem_nhds hp.1)
    have hdiff : ContinuousAt (fun q : Space n × ℝ => u q.1 - q.2) p :=
      ((hu.continuousAt (hΩ.mem_nhds hp.1)).comp continuous_fst.continuousAt).sub
        continuous_snd.continuousAt
    filter_upwards [h1, hdiff.tendsto (Iio_mem_nhds (sub_neg.mpr hp.2))] with q hq hqu
    exact ⟨hq, sub_neg.mp hqu⟩
  apply le_antisymm
  · intro p hp
    have hpD := interior_subset hp
    refine ⟨hpD.1, ?_⟩
    have hv : Continuous (fun z : ℝ => (p.1, z)) := continuous_const.prodMk continuous_id
    have hn : Ici (u p.1) ∈ 𝓝 p.2 := by
      have hpre := (hv.tendsto p.2) (mem_interior_iff_mem_nhds.mp hp)
      exact mem_of_superset hpre (fun z hz => hz.2)
    have hh := mem_interior_iff_mem_nhds.mpr hn
    simpa only [interior_Ici, mem_Ioi] using hh
  · exact interior_maximal (fun p hp => ⟨hp.1, hp.2.le⟩) hopen

theorem epigraph_interior_nonempty {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) {u : Space n → ℝ} (hu : ContinuousOn u Ω) :
    (interior {p : Space n × ℝ | p.1 ∈ Ω ∧ u p.1 ≤ p.2}).Nonempty := by
  rw [interior_epigraph hΩ hu]
  obtain ⟨a, ha⟩ := hne
  exact ⟨(a, u a + 1), ha, by simp⟩

/- Compactness of the entire tangent cap, not just its projection. -/
theorem isCompact_tangent_cap {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) {a : Space n} (ha : a ∈ Ω) (t : ℝ) :
    IsCompact {p : Space n × ℝ | p.1 ∈ Ω ∧ u p.1 ≤ p.2 ∧
      p.2 - u a - fderiv ℝ u a (p.1 - a) ≤ t} := by
  let K := {x | x ∈ Ω ∧ tangentHeight u a x ≤ t}
  have hK : IsCompact K := isCompact_tangent_sublevel hΩ hcv hu hp hc ha t
  let Φ : Space n × ℝ → Space n × ℝ :=
    fun q => (q.1, u a + fderiv ℝ u a (q.1 - a) + q.2)
  have hΦ : Continuous Φ := continuous_fst.prodMk
    ((continuous_const.add ((fderiv ℝ u a).continuous.comp
      (continuous_fst.sub continuous_const))).add continuous_snd)
  have hcpt : IsCompact (Φ '' (K ×ˢ Icc (0 : ℝ) t)) :=
    (hK.prod isCompact_Icc).image hΦ
  have hcu := convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hclosed : IsClosed {p : Space n × ℝ | p.1 ∈ Ω ∧ u p.1 ≤ p.2 ∧
      p.2 - u a - fderiv ℝ u a (p.1 - a) ≤ t} := by
    have he := isClosed_epigraph_of_complete hΩ ⟨a, ha⟩ hu hcu hc
    have hf : Continuous (fun p : Space n × ℝ => p.2 - u a - fderiv ℝ u a (p.1 - a)) :=
      (continuous_snd.sub continuous_const).sub
        ((fderiv ℝ u a).continuous.comp (continuous_fst.sub continuous_const))
    convert he.inter (isClosed_le hf continuous_const) using 1
    all_goals try with_reducible_and_instances rfl
    ext p
    simp only [mem_inter_iff, mem_ofPred_eq]
    tauto
  apply hcpt.of_isClosed_subset hclosed
  intro p hp'
  have hga := tangentHeight_nonneg hΩ hcv hu hp ha hp'.1
  dsimp [tangentHeight] at hga
  refine ⟨(p.1, p.2 - u a - fderiv ℝ u a (p.1 - a)), ?_, ?_⟩
  · refine ⟨⟨hp'.1, ?_⟩, ?_, hp'.2.2⟩
    · dsimp [tangentHeight]
      linarith [hp'.2.1, hp'.2.2]
    · linarith [hp'.2.1]
  · dsimp [Φ]
    congr 1
    ring

/- The manuscript's open tangent section. -/
theorem closure_tangentSection {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) {a : Space n} (ha : a ∈ Ω)
    {t : ℝ} (ht : 0 < t) :
    closure (tangentSection Ω u a t) = {x | x ∈ Ω ∧ tangentHeight u a x ≤ t} := by
  have hcu := convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hcg := convexOn_tangentHeight hcu a
  apply le_antisymm
  · refine closure_minimal ?_ (isClosed_tangent_sublevel hΩ ⟨a, ha⟩ hu hcu hc a t)
    intro x hx
    exact ⟨hx.1, hx.2.le⟩
  · intro x hx
    obtain ⟨q, hqm, hqmem, hqlim⟩ := exists_seq_strictMono_tendsto' (show (0 : ℝ) < 1 by norm_num)
    apply mem_closure_iff_seq_limit.mpr
    refine ⟨fun i => a + q i • (x - a), ?_, ?_⟩
    · intro i
      have hqi : q i ∈ Ioo (0 : ℝ) 1 := hqmem i
      refine ⟨hcv.add_smul_mem ha (by simpa using hx.1) ⟨hqi.1.le, hqi.2.le⟩, ?_⟩
      have hv : (1 - q i) • a + q i • x = a + q i • (x - a) := by module
      have he := hcg.2 ha hx.1 (sub_nonneg.mpr hqi.2.le) hqi.1.le
        (show (1 - q i) + q i = 1 by ring)
      rw [hv, tangentHeight_self] at he
      simp only [smul_eq_mul, mul_zero, zero_add] at he
      exact lt_of_le_of_lt (he.trans (mul_le_mul_of_nonneg_left hx.2 hqi.1.le))
        (by nlinarith [ht, hqi.2])
    · have hh := (tendsto_const_nhds (x := a)).add (hqlim.smul_const (x - a))
      simpa using hh

/- Source equation uniform-section-balance, in unshifted coordinates;
equivalently, -ρ(closure S-a) ⊆ closure S-a. -/
theorem sectionBalance_reflection {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) {ρ : ℝ} (hbal : SectionBalance Ω u ρ)
    {a x : Space n} (ha : a ∈ Ω) (hx : x ∈ Ω) :
    a - ρ • (x - a) ∈ Ω ∧
    tangentHeight u a (a - ρ • (x - a)) ≤ tangentHeight u a x := by
  by_cases hxa : x = a
  · simp only [hxa, sub_self, smul_zero, sub_zero, le_refl, and_true]
    exact ha
  · have ht := tangentHeight_pos hΩ hcv hu hp ha hx hxa
    have he := hbal a ha _ ht x (by
      rw [closure_tangentSection hΩ hcv hu hp hc ha ht]
      exact ⟨hx, le_rfl⟩)
    rwa [closure_tangentSection hΩ hcv hu hp hc ha ht] at he

/- An open set containing a point and invariant under one dilation about it
of factor greater than one is the whole vector space. -/
theorem eq_univ_of_dilation {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {a : Space n} (ha : a ∈ Ω) {c : ℝ} (hc : 1 < c)
    (hexpand : ∀ x ∈ Ω, a + c • (x - a) ∈ Ω) : Ω = univ := by
  have hp (k : ℕ) (x : Space n) (hx : x ∈ Ω) : a + c ^ k • (x - a) ∈ Ω := by
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      have he := hexpand _ ih
      simpa [pow_succ, smul_smul, mul_comm] using he
  apply eq_univ_iff_forall.mpr
  intro b
  have hc0 : 0 < c := zero_lt_one.trans hc
  have hq : 0 ≤ c⁻¹ := inv_nonneg.mpr hc0.le
  have hqlt : c⁻¹ < 1 := (inv_lt_one₀ hc0).mpr hc
  have hlim : Tendsto (fun k : ℕ => a + (c⁻¹) ^ k • (b - a)) atTop (𝓝 a) := by
    have he := (tendsto_const_nhds (x := a)).add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq hqlt).smul_const (b - a))
    simpa using he
  obtain ⟨k, hk⟩ := (hlim.eventually_mem (hΩ.mem_nhds ha)).exists
  have he := hp k _ hk
  simpa [smul_smul, ← mul_pow, hc0.ne'] using he

/- The domain-extension conclusion of rigidity.tex:38–87. Uniform reflection
of actual tangent sections, once proved by the model argument, forces all
rays to continue. This lemma does not assume whole-domain solvability. -/
theorem eq_univ_of_sectionBalance {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) {ρ : ℝ} (hρ : 0 < ρ)
    (hbal : SectionBalance Ω u ρ) : Ω = univ := by
  obtain ⟨a, ha⟩ := hne
  apply eq_univ_of_dilation hΩ ha (c := 1 + ρ) (by linarith)
  intro x hx
  have he := (sectionBalance_reflection hΩ hcv hu hp hc hbal hx ha).1
  have hv : x - ρ • (a - x) = a + (1 + ρ) • (x - a) := by module
  rwa [hv] at he

/- The exact gap-doubling constants from rigidity.tex, proved before assuming
that the base is all of Rⁿ. Thus the same calculation supplies ray extension. -/
theorem tangent_epigraph_isModelShape {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) {a : Space n} (ha : a ∈ Ω) :
    IsModelShape (tangentModelEquiv u a '' sourceEpigraph Ω u) := by
  have hv := convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hcl := isClosed_epigraph_of_complete hΩ ⟨a,ha⟩ hu hv hc
  have hi := epigraph_interior_nonempty hΩ ⟨a,ha⟩ hu.continuousOn
  let A := tangentModelEquiv u a
  refine ⟨A.toHomeomorph.isClosedMap _ hcl, hv.convex_epigraph.affine_image A.toAffineEquiv.toAffineMap,
    ?_, ?_, ?_, ?_⟩
  · change (interior (A.toHomeomorph '' sourceEpigraph Ω u)).Nonempty
    rw [← A.toHomeomorph.image_interior]
    exact hi.image A.toHomeomorph
  · intro s hs
    refine ⟨(a,u a+s 0),⟨ha,by linarith [hs 0]⟩,?_⟩
    apply Prod.ext
    · ext i
      simp [tangentModelEquiv_apply,Subsingleton.elim i (0 : Fin 1)]
    · simp [tangentModelEquiv_apply]
  · rintro p ⟨⟨x,z⟩,⟨hx,hz⟩,rfl⟩ i
    rw [tangentModelEquiv_fst]
    have hh := tangentHeight_nonneg hΩ hcv hu hp ha hx
    dsimp [tangentHeight] at hh
    linarith
  · intro T hT
    convert (isCompact_tangent_cap hΩ hcv hu hp hc ha T).image A.continuous using 1
    all_goals try with_reducible_and_instances rfl
    ext p
    constructor
    · rintro ⟨⟨q,hq,rfl⟩,hTq⟩
      refine ⟨q,⟨hq.1,hq.2,?_⟩,rfl⟩
      simpa [A,tangentModelEquiv_apply] using hTq
    · rintro ⟨q,⟨hq,hz,hTq⟩,rfl⟩
      exact ⟨⟨q,⟨hq,hz⟩,rfl⟩,by simpa [A,tangentModelEquiv_apply] using hTq⟩

theorem tangent_epigraph_in_family {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) {a : Space n} (ha : a ∈ Ω) :
    InAffineLimitFamily (sourceEpigraph Ω u) (tangentModelEquiv u a '' sourceEpigraph Ω u) := by
  have hv := convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  exact InAffineLimitFamily.of_affine_image
    (isClosed_epigraph_of_complete hΩ ⟨a,ha⟩ hu hv hc) hv.convex_epigraph
    (epigraph_interior_nonempty hΩ ⟨a,ha⟩ hu.continuousOn) (tangentModelEquiv u a)

theorem model_dimension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {D : Set E} {k m : ℕ} {C : Set (Space k × Space m)}
    (hf : InAffineLimitFamily D C) : k+m = Module.finrank ℝ E := by
  obtain ⟨A,hA⟩ := hf.approximation
  have hh := (A 0).toAffineEquiv.linear.finrank_eq
  simpa [Module.finrank_prod,finrank_euclideanSpace] using hh.symm

/- A maximal direction number exists; this is genuine finite-dimensional
maximality rather than a postulated geometric estimate. -/
theorem exists_maximal_model {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {D : Set E}
    (h1 : ∃ m, ∃ C : Set (Space 1 × Space m), IsModelShape C ∧ InAffineLimitFamily D C) :
    ∃ (k m : ℕ) (C : Set (Space k × Space m)), 1 ≤ k ∧ IsModelShape C ∧
      InAffineLimitFamily D C ∧ ∀ (r d : ℕ) (C' : Set (Space r × Space d)),
      IsModelShape C' → InAffineLimitFamily D C' → r ≤ k := by
  classical
  let S : Set ℕ := {r | ∃ m, ∃ C : Set (Space r × Space m), IsModelShape C ∧ InAffineLimitFamily D C}
  have hbd : BddAbove S := ⟨Module.finrank ℝ E, by
    rintro r ⟨m,C,hC,hf⟩
    have hh := model_dimension hf
    omega⟩
  have hne : S.Nonempty := ⟨1,h1⟩
  let k := sSup S
  have hs : S.Finite := (Set.finite_Iic hbd.choose).subset hbd.choose_spec
  have hk : k ∈ S := hne.csSup_mem hs
  have hmax : ∀ {r}, r ∈ S → r ≤ k := fun hr => le_csSup hbd hr
  obtain ⟨m,C,hC,hf⟩ := hk
  exact ⟨k,m,C,hmax h1,hC,hf,fun r d C' hC' hf' => hmax ⟨d,C',hC',hf'⟩⟩

/- Once the geometric/analytic exclusion of two-direction models is proved,
all tangent sections (all centers and heights) inherit one common balance.
This is a faithful integration lemma, not the main theorem. -/
theorem sectionBalance_of_no_two_model {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u)
    (hno : ∀ (d : ℕ), n = d+1 → ∀ C : Set (Space 2 × Space d),
      IsModelShape C → InAffineLimitFamily (sourceEpigraph Ω u) C → False) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ SectionBalance Ω u ρ := by
  have hv := convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hcl := isClosed_epigraph_of_complete hΩ hne hu hv hc
  have hneD : (sourceEpigraph Ω u).Nonempty := by obtain ⟨a,ha⟩ := hne; exact ⟨(a,u a),ha,le_rfl⟩
  obtain ⟨a,ha,hcenter⟩ := uniform_centering hcl hneD hno
  have hapos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  refine ⟨a⁻¹,inv_pos.mpr hapos,(inv_le_one₀ hapos).mpr ha,?_⟩
  intro x hx t ht y hy
  rw [closure_tangentSection hΩ hcv hu hp hc hx ht] at hy ⊢
  have hmod := tangent_epigraph_isModelShape hΩ hcv hu hp hc hx
  have hf := tangent_epigraph_in_family hΩ hcv hu hp hc hx
  have hh := hcenter _ hmod hf (WithLp.toLp 2 (fun _ : Fin 1 => t)) (by simpa using ht)
  rw [tangent_model_fiber] at hh
  have hm : -(y-x) ∈ -((fun z => z-x) '' {z | z ∈ Ω ∧ tangentHeight u x z ≤ t}) := by
    exact neg_mem_neg.mpr ⟨y,hy,rfl⟩
  obtain ⟨z,⟨w,hw,rfl⟩,hz⟩ := mem_smul_set.mp (hh hm)
  have he : x-a⁻¹ • (y-x) = w := by
    have hz' := congrArg (fun v : Space n => a⁻¹ • v) hz
    simp only [smul_smul, inv_mul_cancel₀ hapos.ne', one_smul, smul_neg] at hz'
    rw [sub_eq_iff_eq_add] at hz'
    simpa only [sub_eq_add_neg, add_comm] using hz'.symm
  simpa only [he] using hw

-- END

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_MaximalModelExclusion
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

section MaximalModelExclusion

/-- Normalization of an actual maximal model, followed by the full sigma
mass/growth contradiction, excludes every maximal direction number at least two. -/
theorem affineMaximal_maximal_model_directions_le_one {n k m : ℕ}
    (hn : 3 ≤ n) (hn9 : n ≤ 9)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmP : AffineMaximalOn Ω u)
    (hcomplete : EuclideanGraphComplete Ω u)
    {C : Set (Space k × Space m)} (hC : IsModelShape C)
    (hf : InAffineLimitFamily (sourceEpigraph Ω u) C)
    (hmax : ∀ r d : ℕ, ∀ C' : Set (Space r × Space d),
      IsModelShape C' → InAffineLimitFamily (sourceEpigraph Ω u) C' → r ≤ k) : k ≤ 1 := by
  by_contra hk
  have hk2 : 2 ≤ k := by omega
  have hm : 1 ≤ m := complete_affineMaximal_model_transverse_pos (by omega)
    hΩ hne hcv hu hp hmP hcomplete hC hf
  let d := m-1
  have hmd : m = d+1 := by dsimp [d]; omega
  have hdim := model_dimension hf
  have hnk : n = k+d := by
    simp only [Module.finrank_prod,finrank_euclideanSpace,Module.finrank_self,Fintype.card_fin] at hdim
    omega
  let e : Fin n ≃ Fin k ⊕ Fin d := Fintype.equivOfCardEq (by simp [hnk])
  let eE : Fin m ≃ Fin d ⊕ Unit := Fintype.equivOfCardEq (by simp [hmd])
  let f := transverseEuclideanIsometry hmd
  have hmax' : ∀ d' : ℕ, m = d'+1 → ∀ C' : Set (Space (k+1) × Space d'),
      IsModelShape C' → InAffineLimitFamily (sourceEpigraph Ω u) C' → False := by
    intro d' _ C' hC' hf'
    have hh := hmax (k+1) d' C' hC' hf'
    omega
  have hcl := sourceEpigraph_closed hΩ hne hcv hu hp hcomplete
  have hned : (sourceEpigraph Ω u).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨(x,u x),hx,le_rfl⟩
  obtain ⟨c,hc,hnorm⟩ := uniform_model_fiber_normalization hm hcl hned hmax'
  let s : Space k := WithLp.toLp 2 (fun _ => (1:ℝ))
  have hs : ∀ i, 0 < s i := by intro i; norm_num [s]
  obtain ⟨A,hC',hf',hin,hout⟩ := hnorm C hC hf s hs
  obtain ⟨a,L,hlim⟩ := hf'.epigraph_pullback_approximation
  exact affineMaximal_no_normalized_maximal_model hn hn9 hk2 hm e eE f
    hΩ hne hcv hu hp hmP hcomplete hmax' a L hC' hf' hlim
    (by positivity : 0 < 2/(c+1)) hin hout

/-- Every actual affine-limit model has at most one orthant direction in n=3,...,9.
This is Proposition one-direction, including the originally missing producers. -/
theorem affineMaximal_model_directions_le_one {n k m : ℕ}
    (hn : 3 ≤ n) (hn9 : n ≤ 9)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmP : AffineMaximalOn Ω u)
    (hcomplete : EuclideanGraphComplete Ω u)
    {C : Set (Space k × Space m)} (hC : IsModelShape C)
    (hf : InAffineLimitFamily (sourceEpigraph Ω u) C) : k ≤ 1 := by
  obtain ⟨x,hx⟩ := hne
  have h1 : ∃ m, ∃ C : Set (Space 1 × Space m), IsModelShape C ∧
      InAffineLimitFamily (sourceEpigraph Ω u) C :=
    ⟨n,_,tangent_epigraph_isModelShape hΩ hcv hu hp hcomplete hx,
      tangent_epigraph_in_family hΩ hcv hu hp hcomplete hx⟩
  obtain ⟨k',m',C',hk',hC',hf',hmax⟩ := exists_maximal_model h1
  exact (hmax k m C hC hf).trans
    (affineMaximal_maximal_model_directions_le_one hn hn9 hΩ ⟨x,hx⟩ hcv
      hu hp hmP hcomplete hC' hf' hmax)

/-- Full uniform section balance, produced from the original hypotheses. -/
theorem affineMaximal_section_balance {n : ℕ} (hn : 3 ≤ n) (hn9 : n ≤ 9)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hc : EuclideanGraphComplete Ω u) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ SectionBalance Ω u ρ := by
  apply sectionBalance_of_no_two_model hΩ hne hcv hu hp hc
  intro d _ C hC hf
  have hh := affineMaximal_model_directions_le_one hn hn9 hΩ hne hcv hu hp hm hc hC hf
  omega
end MaximalModelExclusion


end
end AffineBernstein
end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_EntireAndDoubling
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

section EntireAndDoubling
/-- The global geometric part of the exact main theorem: the nonempty open
convex base is all of Euclidean space, and one section-balance constant works at
all centers and heights. This is not the quadratic-rigidity conclusion. -/
theorem affineMaximal_entire_and_balance {n : ℕ} (hn : 3 ≤ n) (hn9 : n ≤ 9)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hc : EuclideanGraphComplete Ω u) :
    Ω = univ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ SectionBalance univ u ρ := by
  obtain ⟨ρ,hρ,hρ1,hbal⟩ := affineMaximal_section_balance hn hn9 hΩ hne hcv hu hp hm hc
  have hU := eq_univ_of_sectionBalance hΩ hne hcv hu hp hc hρ hbal
  exact ⟨hU,ρ,hρ,hρ1,hU ▸ hbal⟩

end EntireAndDoubling

open Filter
open scoped Topology

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_QuadraticAffineImage
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

open Matrix

lemma posDef_quadratic_linear_equiv {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) : ∃ L : Space n ≃ₗ[ℝ] Space n,
      ∀ x, (∑ i, (L x i)^2) = ∑ i, ∑ j, x i*A i j*x j := by
  open scoped MatrixOrder in
  classical
  let S := CFC.sqrt A
  have hS : S.IsSymm := Matrix.isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have hSS : S*S=A := by simpa only [S,pow_two] using CFC.sq_sqrt A hA.posSemidef.nonneg
  have hSd : IsUnit S.det := by
    apply isUnit_iff_ne_zero.mpr
    intro H
    have hd := congrArg Matrix.det hSS
    rw [Matrix.det_mul,H,zero_mul] at hd
    exact hA.det_pos.ne' hd.symm
  let L := Matrix.toLinearEquiv (EuclideanSpace.basisFun (Fin n) ℝ).toBasis S hSd
  refine ⟨L,fun x => ?_⟩
  have hL : (fun i => L x i) = S*ᵥ (fun i => x i) := funext (matrixLinearEquiv_apply S hSd x)
  calc
    _ = (S*ᵥ (fun i => x i)) ⬝ᵥ (S*ᵥ (fun i => x i)) := by
      rw [← hL]
      simp only [dotProduct,pow_two]
    _ = (fun i => x i) ⬝ᵥ ((S*S)*ᵥ (fun i => x i)) := by
      rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,← Matrix.mulVec_transpose,hS.eq]
      exact dotProduct_comm _ _
    _ = _ := by rw [hSS]; simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]

lemma quadratic_graph_affine_image {n : ℕ} {u : Space n → ℝ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (ℓ : Space n →L[ℝ] ℝ) (c : ℝ)
    (hu : ∀ x, u x=(1/2:ℝ)*(∑ i, ∑ j, x i*A i j*x j)+ℓ x+c) :
    ∃ e : (Space n × ℝ) ≃ᵃ[ℝ] (Space n × ℝ),
      e '' standardParaboloid n=graph univ u := by
  obtain ⟨L,hL⟩ := posDef_quadratic_linear_equiv hA
  let e := (paraboloidLinearEquiv L ℓ).toAffineEquiv.trans
    (AffineEquiv.constVAdd ℝ (Space n × ℝ) ((0:Space n),c))
  have he (p : Space n × ℝ) : e p=(L.symm p.1,(1/2:ℝ)*p.2+ℓ (L.symm p.1)+c) := by
    apply Prod.ext <;> simp [e,paraboloidLinearEquiv,add_comm]
  refine ⟨e,?_⟩
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    change q.2=∑ i, (q.1 i)^2 at hq
    rw [he]
    refine ⟨mem_univ _,?_⟩
    rw [hu,← hL,hq]
    simp
  · intro hp
    have hp' : p.2=u p.1 := hp.2
    refine ⟨(L p.1,∑ i, (L p.1 i)^2),rfl,?_⟩
    rw [he]
    apply Prod.ext
    · simp
    · simp only [LinearEquiv.symm_apply_apply]
      rw [hL,← hu,← hp']

end AffineBernstein

end

end OAI
end

section
-- module Solutions.OAIQ22_AB.AffineBernstein_Main
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


/-- Literal main theorem, with its stated affine-image consequence. -/
theorem affine_bernstein_oai
    (n : ℕ) (hn₃ : 3 ≤ n) (hn₉ : n ≤ 9)
    (Ω : Set (Space n)) (hΩne : Ω.Nonempty) (hΩopen : IsOpen Ω)
    (hΩconvex : Convex ℝ Ω) (u : Space n → ℝ)
    (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hmax : AffineMaximalOn Ω u)
    (hcomplete : EuclideanGraphComplete Ω u) :
    Ω = univ ∧
      (∃ (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) (c : ℝ),
        A.IsSymm ∧ A.PosDef ∧
        ∀ x, u x = (1 / 2 : ℝ) * (∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j)
          + (∑ i : Fin n, b i * x i) + c) ∧
      (∃ e : (Space n × ℝ) ≃ᵃ[ℝ] (Space n × ℝ),
        e '' standardParaboloid n = graph Ω u) := by
  obtain ⟨hU,ρ,hρ,hρ1,hbal⟩ := affineMaximal_entire_and_balance hn₃ hn₉ hΩopen hΩne
    hΩconvex hu hpos hmax hcomplete
  refine ⟨hU,?_⟩
  subst Ω
  have hu' : ContDiff ℝ ∞ u := contDiffOn_univ.mp hu
  have hp' : ∀ x, (hessian u x).PosDef := fun x => hpos x (mem_univ x)
  have hH := balanced_constant_hessian (by omega) hu' hp' hmax hρ hρ1 hbal
  have hq := quadratic_of_constant_hessian hu' hH
  constructor
  · refine ⟨hessian u 0, WithLp.toLp 2 (fun i => fderiv ℝ u 0 (coordinateVector n i)), u 0,
      Matrix.isHermitian_iff_isSymm.mp (hp' 0).isHermitian, hp' 0, ?_⟩
    intro x
    change u x = (1/2:ℝ)*(∑ i, ∑ j, x i*hessian u 0 i j*x j) +
      (∑ i, fderiv ℝ u 0 (coordinateVector n i)*x i) + u 0
    rw [← continuousLinearMap_coordinate_sum]
    exact hq x
  · exact quadratic_graph_affine_image (hp' 0) (fderiv ℝ u 0) (u 0) hq



end
end AffineBernstein

end

end OAI
end

theorem solution : type_of% @OAI.AffineBernstein.affine_bernstein_oai := @OAI.AffineBernstein.affine_bernstein_oai
