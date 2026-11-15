-- Prove2me | solution 1 for LG2021.Algorithm.terminal_regret_of_current_bounds_sharp
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-14T16:28:25.813032+00:00
-- url     : https://prove2.me/submissions/897e09d2-7152-428a-8842-14f138905e7e

import Mathlib
import Definitions.Def_LG2021_Policy
import Definitions.Def_LG2021_RegretRate
import Definitions.Def_BilateralProfitMHR_ConvexBandit
import Definitions.Def_LG2021_CanonicalBandit
import Definitions.Def_LG2021_GaussianEstimators
import Definitions.Def_LG2021_GaussianSeparation
import Definitions.Def_ModernConvex_EllipsoidMethod_EllipsoidMethod
import Definitions.Def_ModernConvex_Ellipsoids_Ellipsoid
import Theorems.Thm_LG2021_nearby_simplex_volume
import Theorems.Thm_LG2021_paper_strong_separation
import Theorems.Thm_LG2021_shallow_ellipsoid_cover
import Theorems.Thm_ModernConvex_Ellipsoids_lowner_fritz_john
import Theorems.Thm_OAI_IndependentProducts_gaussian_integral_fourth
import Theorems.Thm_RandomGradFree_Nonsmooth_smoothing_hasGradient
set_option autoImplicit false
/- LG2021AlgorithmOracle -/
section
/-!
The concrete estimators and stopping rule of Algorithm 1 in Tor Lattimore and
Andras Gyorgy, "Improved regret for zeroth-order stochastic convex bandits",
Proceedings of the 34th Conference on Learning Theory, PMLR 134, 2021.
The positivity test in `eligible` makes the stopping rule total: a zero
lower confidence bound cannot trigger stopping. The moment constants remain
explicit parameters for the formal concentration estimates.
-/
noncomputable section
namespace LG2021.Algorithm
open MeasureTheory Concentration
open scoped Classical
private theorem firstEligible_some_eligible (p : OracleConfig) {u : ℕ} (indices : List (Fin u))
    (m : ℕ) (sums : Fin u → ℝ) {s : Fin u}
    (h : firstEligible p indices m sums = some s) : eligible p m sums s := by
  induction indices with
  | nil => simp [firstEligible] at h
  | cons i rest ih =>
      dsimp [firstEligible] at h
      split_ifs at h with hi
      · cases Option.some.inj h
        exact hi
      · exact ih h
private theorem winner_some_eligible (p : OracleConfig) {u : ℕ} (m : ℕ) (sums : Fin u → ℝ)
    {s : Fin u} (h : winner p m sums = some s) : eligible p m sums s :=
  firstEligible_some_eligible p (List.finRange u) m sums h
private theorem winner_positive (p : OracleConfig) {u : ℕ} (m : ℕ) (sums : Fin u → ℝ)
    {s : Fin u} (h : winner p m sums = some s) : 0 < lowerBound p m sums s :=
  (winner_some_eligible p m sums h).1
/-- The stopping test provides more than the positivity required for division:
within the horizon its certified gap is at least four divided by the horizon. -/
private theorem stopping_gap_margin {m n : ℕ} {θ c r H C : ℝ}
    (hm : 1 ≤ m) (hmn : m ≤ n) (hθ : 0 < θ) (hc : 1 ≤ c) (hr : 1 ≤ r)
    (hH : 1 ≤ H) (hC : 0 < C) (hC1 : C ≤ 1)
    (hstop : (4 * c * r / θ) ^ 2 * H / C ≤ (m : ℝ)) :
    4 / (n : ℝ) ≤ θ := by
  have hCH : C ≤ H := hC1.trans hH
  have hsq : (4 * c * r / θ) ^ 2 ≤ (m : ℝ) := by
    apply le_trans _ hstop
    apply (le_div_iff₀ hC).mpr
    exact mul_le_mul_of_nonneg_left hCH (sq_nonneg _)
  rw [div_pow] at hsq
  have hp : (4 * c * r) ^ 2 ≤ (m : ℝ) * θ ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hθ)).mp hsq
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmnreal : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hnreal : (1 : ℝ) ≤ n := hmreal.trans hmnreal
  have hnm : (m : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hnm (sq_nonneg θ)
  have hcr : 4 ≤ 4 * c * r := by nlinarith
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < n)).mpr
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ n) hθ.le]
/-- Deterministic strict separation margin after the concentration estimates.
This margin permits the small inward rational rounding used by the policy. -/
private theorem oracle_strict_margin {d : ℕ} {v trueGradient x z : Space d}
    {θ certified δ n : ℝ} (hn : 0 < n) (hcert : 0 < certified)
    (hcertθ : certified ≤ θ) (hcertn : 2 / n ≤ certified) (hδ : δ ≤ 1 / (4 * n))
    (htrue : inner ℝ trueGradient (x - z) ≤ δ - θ)
    (herror : inner ℝ (v - trueGradient) (x - z) ≤ 1 / (4 * n) + θ / 2) :
    inner ℝ v (x - z) ≤ -certified / 4 := by
  rw [inner_sub_left] at herror
  have hrecip : 1 / (4 * n) = (2 / n) / 8 := by field_simp; ring
  rw [hrecip] at hδ herror
  linarith
end LG2021.Algorithm
end
end
/- LG2021AlgorithmGeometry -/
section
noncomputable section
namespace LG2021.Algorithm
open MeasureTheory Matrix
open scoped Classical
private theorem isClosed_cutSet {d : ℕ} (cut : Cut d) : IsClosed (cutSet cut) :=
  isClosed_le (by fun_prop) continuous_const
private theorem convex_cutSet {d : ℕ} (cut : Cut d) : Convex ℝ (cutSet cut) :=
  convex_halfSpace_le ⟨(innerSL ℝ cut.1).map_add, (innerSL ℝ cut.1).map_smul⟩ cut.2
private theorem isCompact_activeBody {d p : ℕ} {K : Set (Space d)} (hK : IsCompact K)
    (cuts : Fin p → Cut d) : IsCompact (activeBody K cuts) :=
  hK.inter_right (isClosed_iInter fun i => isClosed_cutSet (cuts i))
private theorem convex_activeBody {d p : ℕ} {K : Set (Space d)} (hK : Convex ℝ K)
    (cuts : Fin p → Cut d) : Convex ℝ (activeBody K cuts) :=
  hK.inter (convex_iInter fun i => convex_cutSet (cuts i))
private theorem zero_cutSet {d : ℕ} : cutSet (0 : Cut d) = Set.univ := by
  ext x
  simp [cutSet]
private theorem matrixAction_add {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (x y : Space d) :
    matrixAction M (x + y) = matrixAction M x + matrixAction M y := by
  simp [matrixAction, mulVec_add]
private theorem matrixAction_sub {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (x y : Space d) :
    matrixAction M (x - y) = matrixAction M x - matrixAction M y := by
  simp [matrixAction, mulVec_sub]
private theorem matrixAction_inverse_left {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : M.det ≠ 0) (x : Space d) : matrixAction M⁻¹ (matrixAction M x) = x := by
  simp only [matrixAction, ContinuousLinearEquiv.apply_symm_apply, mulVec_mulVec,
    nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM), one_mulVec,
    ContinuousLinearEquiv.symm_apply_apply]
private theorem inner_matrixAction_transpose {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (v x : Space d) : inner ℝ (matrixAction M.transpose v) x = inner ℝ v (matrixAction M x) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, matrixAction,
    EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv, PiLp.coe_symm_continuousLinearEquiv,
    WithLp.ofLp_toLp, star_trivial]
  rw [dotProduct_mulVec, vecMul_transpose]
private theorem cutFromEstimate_value {d : ℕ} (F : Frame d) (hF : F.1.det ≠ 0)
    (z v x : Space d) :
    inner ℝ (cutFromEstimate F z v).1 x - (cutFromEstimate F z v).2 =
      inner ℝ v (frameUnapply F x - z) := by
  simp only [cutFromEstimate, inner_matrixAction_transpose, frameApply, frameUnapply,
    matrixAction_add, matrixAction_sub, matrixAction_inverse_left F.1 hF,
    inner_add_right, inner_sub_right]
  ring
end LG2021.Algorithm
end
end
/- LG2021AlgorithmQuantization -/
section
/-!
An explicit countable approximation of halfspace coefficients. This is an
additional algorithm completion, not a statement asserted in Lattimore–Gyorgy.
It permits measurable canonical ellipsoid choices on countable cut histories.
-/
noncomputable section
namespace LG2021.Algorithm
open MeasureTheory
open scoped Classical
private theorem continuous_decodeCut {d : ℕ} : Continuous (decodeCut (d := d)) := by
  unfold decodeCut
  fun_prop
private theorem denseRange_decodeCut {d : ℕ} : DenseRange (decodeCut (d := d)) := by
  have hv : DenseRange (fun v : Fin d → ℚ =>
      (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => (v i : ℝ))) := by
    exact (EuclideanSpace.equiv (Fin d) ℝ).symm.surjective.denseRange.comp
      (DenseRange.piMap (fun _ : Fin d => (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ))))
      (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous
  exact hv.prodMap Rat.denseRange_cast
private theorem enumerateCuts_surjective (d : ℕ) : Function.Surjective (enumerateCuts d) :=
  Classical.choose_spec (exists_surjective_nat (CutCode d))
private theorem denseRange_enumerateCuts (d : ℕ) : DenseRange (fun n => decodeCut (enumerateCuts d n)) :=
  denseRange_decodeCut.comp (enumerateCuts_surjective d).denseRange continuous_decodeCut
private theorem positiveRadius_pos (ε : ℝ) : 0 < positiveRadius ε := by
  unfold positiveRadius
  split_ifs with h
  · exact h
  · norm_num
private theorem exists_close_cut {d : ℕ} (w : Cut d × ℝ) :
    ∃ k : ℕ, dist w.1 (decodeCut (enumerateCuts d k)) < positiveRadius w.2 :=
  (denseRange_enumerateCuts d).exists_dist_lt w.1 (positiveRadius_pos w.2)
private theorem quantizeCut_dist_lt {d : ℕ} (target : Cut d) {ε : ℝ} (hε : 0 < ε) :
    dist target (decodeCut (quantizeCut target ε)) < ε := by
  have h := Nat.find_spec (exists_close_cut (target, ε))
  simpa only [quantizeCut, positiveRadius, if_pos hε] using h
private theorem cutValue_perturbation {d : ℕ} (a b : Cut d) (x : Space d)
    {ε R : ℝ} (hε : 0 ≤ ε) (hR : 0 ≤ R) (hx : ‖x‖ ≤ R)
    (hclose : dist a b ≤ ε) : |cutValue a x - cutValue b x| ≤ ε * (R + 1) := by
  have hn : ‖a.1 - b.1‖ ≤ ε := by
    have h := (le_max_left (dist a.1 b.1) (dist a.2 b.2)).trans hclose
    simpa only [dist_eq_norm] using h
  have hb : |a.2 - b.2| ≤ ε := by
    have h := (le_max_right (dist a.1 b.1) (dist a.2 b.2)).trans hclose
    simpa only [Real.dist_eq] using h
  have hinner : |inner ℝ (a.1 - b.1) x| ≤ ε * R := by
    exact (norm_inner_le_norm (𝕜 := ℝ) (a.1 - b.1) x).trans
      (mul_le_mul hn hx (norm_nonneg x) hε)
  have heq : cutValue a x - cutValue b x = inner ℝ (a.1 - b.1) x - (a.2 - b.2) := by
    simp only [cutValue, inner_sub_left]
    ring
  rw [heq]
  exact (abs_sub _ _).trans (by nlinarith)
private theorem roundedInwardCut_error {d : ℕ} (c : Cut d) {θ R : ℝ}
    (hθ : 0 < θ) (hR : 0 ≤ R) (x : Space d) (hx : ‖x‖ ≤ R) :
    |cutValue (inwardCut c θ) x - cutValue (decodeCut (roundedInwardCut c θ R)) x| ≤ θ / 32 := by
  have hε : 0 < θ / (32 * (R + 1)) := by positivity
  have hdist := (quantizeCut_dist_lt (inwardCut c θ) hε).le
  have h := cutValue_perturbation (inwardCut c θ)
    (decodeCut (roundedInwardCut c θ R)) x hε.le hR hx hdist
  have heq : θ / (32 * (R + 1)) * (R + 1) = θ / 32 := by
    have hne : R + 1 ≠ 0 := by positivity
    field_simp
  simpa only [heq] using h
private theorem roundedInwardCut_preserves_margin {d : ℕ} (c : Cut d) {θ R : ℝ}
    (hθ : 0 < θ) (hR : 0 ≤ R) (x : Space d) (hx : ‖x‖ ≤ R)
    (hmargin : cutValue c x ≤ -θ / 4) :
    x ∈ cutSet (decodeCut (roundedInwardCut c θ R)) := by
  have he := (abs_le.mp (roundedInwardCut_error c hθ hR x hx)).1
  change inner ℝ _ x ≤ _
  dsimp [cutValue, inwardCut] at he hmargin
  linarith
private theorem roundedInwardCut_subset_original {d : ℕ} (c : Cut d) {θ R : ℝ}
    (hθ : 0 < θ) (hR : 0 ≤ R) (x : Space d) (hx : ‖x‖ ≤ R)
    (hmem : x ∈ cutSet (decodeCut (roundedInwardCut c θ R))) : x ∈ cutSet c := by
  have he := (abs_le.mp (roundedInwardCut_error c hθ hR x hx)).2
  change inner ℝ c.1 x ≤ c.2
  change inner ℝ _ x ≤ _ at hmem
  dsimp [cutValue, inwardCut] at he
  linarith
end LG2021.Algorithm
end
end
/- LG2021JohnHelpers -/
section
/-! Small internal adapters reused verbatim from the accepted John-ellipsoid
solution. Their explicit inclusion avoids relying on unexposed helper names in
an external canonical theorem module. The John theorem itself is imported and
reused by its canonical statement. -/
noncomputable section
namespace LG2021.JohnHelpers
open Matrix Finset MeasureTheory ModernConvex.Ellipsoids
open scoped ENNReal
private lemma continuous_dot_self (n : ℕ) : Continuous (fun x : Fin n → ℝ => x ⬝ᵥ x) := by
  unfold dotProduct
  fun_prop
private lemma unitBall_closed (n : ℕ) : IsClosed (unitBall n) :=
  isClosed_le (continuous_dot_self n) continuous_const
private lemma unitBall_coord {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ unitBall n) (i : Fin n) :
    |x i| ≤ 1 := by
  have hs : x i * x i ≤ x ⬝ᵥ x :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
  have hq : x ⬝ᵥ x ≤ 1 := hx
  rw [abs_le]
  constructor <;> nlinarith
private lemma unitBall_bounded (n : ℕ) : Bornology.IsBounded (unitBall n) := by
  apply (show Bornology.IsBounded (Metric.closedBall (0 : Fin n → ℝ) 1) from Metric.isBounded_closedBall).subset
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
    (fun i => by simpa only [Real.norm_eq_abs] using unitBall_coord hx i)
private lemma unitBall_compact (n : ℕ) : IsCompact (unitBall n) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨unitBall_closed n, unitBall_bounded n⟩
private lemma unitBall_interior_nonempty (n : ℕ) : (interior (unitBall n)).Nonempty := by
  refine ⟨0, mem_interior.mpr ?_⟩
  refine ⟨{x : Fin n → ℝ | x ⬝ᵥ x < 1}, ?_,
    isOpen_lt (continuous_dot_self n) continuous_const, ?_⟩
  · intro x hx
    change x ⬝ᵥ x < 1 at hx
    exact hx.le
  · simp
private lemma volume_unitBall_pos (n : ℕ) : 0 < volume (unitBall n) :=
  (isOpen_interior.measure_pos volume (unitBall_interior_nonempty n)).trans_le
    (measure_mono interior_subset)
private lemma volume_unitBall_ne_top (n : ℕ) : volume (unitBall n) ≠ ⊤ :=
  (unitBall_compact n).measure_ne_top
private lemma volume_translate {n : ℕ} (S : Set (Fin n → ℝ)) (c : Fin n → ℝ) :
    volume ((fun x => x+c) '' S) = volume S := by
  have he : (fun x => x+c) '' S = (fun x => x+(-c)) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa using hy
    · intro hx
      exact ⟨x+(-c), hx, by simp⟩
  rw [he, measure_preimage_add_right]
private lemma ellipsoid_image {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    ellipsoid A c = (fun x => x+c) '' (Matrix.toLin' A '' unitBall n) := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨A *ᵥ u, ⟨u,hu,rfl⟩, rfl⟩
  · rintro ⟨v,⟨u,hu,rfl⟩,rfl⟩
    exact ⟨u,hu,rfl⟩
private lemma volume_ellipsoid {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    volume (ellipsoid A c) = ENNReal.ofReal |A.det| * volume (unitBall n) := by
  rw [ellipsoid_image, volume_translate, Measure.addHaar_image_linearMap]
  simp only [LinearMap.det_toLin']
private lemma Vol_ellipsoid {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    Vol (ellipsoid A c) = ENNReal.ofReal |A.det| := by
  unfold Vol
  rw [volume_ellipsoid]
  exact ENNReal.mul_div_cancel_right (volume_unitBall_pos n).ne' (volume_unitBall_ne_top n)
private lemma scalar_dot_self_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ x := by
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
private lemma scalar_unit_cauchy {n : ℕ} (x u : Fin n → ℝ) (hu : u ⬝ᵥ u = 1) :
    (x ⬝ᵥ u) ^ 2 ≤ x ⬝ᵥ x := by
  have h := scalar_dot_self_nonneg (x - (x ⬝ᵥ u) • u)
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, hu, dotProduct_comm u x] at h
  nlinarith
end LG2021.JohnHelpers
end
end
/- LG2021Geometry -/
section
namespace LG2021
open Set ModernConvex.Ellipsoids
open Matrix
private theorem euclidean_unitBall_iff {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace.equiv (Fin m) ℝ x ∈ unitBall m ↔
      x ∈ Metric.closedBall 0 1 := by
  have hdot : (EuclideanSpace.equiv (Fin m) ℝ x) ⬝ᵥ
      (EuclideanSpace.equiv (Fin m) ℝ x) = ‖x‖ ^ 2 := by
    simpa only [EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv, dotProduct, pow_two]
      using (EuclideanSpace.real_norm_sq_eq x).symm
  simp only [ModernConvex.Ellipsoids.unitBall, Set.mem_setOf_eq]
  rw [hdot, Metric.mem_closedBall, dist_zero_right]
  constructor <;> intro h <;> nlinarith [norm_nonneg x]
end LG2021
end
/- LG2021AlgorithmSelector -/
section
/-!
A canonical minimum enclosing ellipsoid is chosen for each finite rational cut
history. The history space is countable, so this choice is measurable without
an additional measurable-selection principle.
The geometric existence and rounding facts reuse the proved Loewner–Fritz John
theorem. The countable-history adapter is an additional algorithm completion.
-/
noncomputable section
namespace LG2021.Algorithm
open MeasureTheory Matrix ModernConvex.Ellipsoids
open scoped Classical
private theorem exists_outerFrame {d : ℕ} {S : Set (Fin d → ℝ)} (hS : IsSolid S) :
    ∃ F : NativeFrame d, OuterFrameSpec S F := by
  obtain ⟨E, hE, _⟩ := (lowner_fritz_john S hS).2.1
  obtain ⟨A, c, hA, rfl⟩ := hE.1
  exact ⟨(A, c), hA, hE⟩
private theorem chosenOuterFrame_spec {d : ℕ} {S : Set (Fin d → ℝ)} (hS : IsSolid S) :
    OuterFrameSpec S (chosenOuterFrame S) := by
  unfold chosenOuterFrame
  rw [dif_pos (exists_outerFrame hS)]
  exact Classical.choose_spec (exists_outerFrame hS)
private theorem nativeCodedBody_solid {d p : ℕ} {K : Set (Space d)}
    (hK : IsCompact K) (hcv : Convex ℝ K) (cuts : Fin p → CutCode d)
    (hi : (interior (codedBody K cuts)).Nonempty) : IsSolid (nativeCodedBody K cuts) := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  have hc := (isCompact_activeBody hK (fun i => decodeCut (cuts i))).image e.continuous
  have hv := (convex_activeBody hcv (fun i => decodeCut (cuts i))).linear_image e.toLinearMap
  have hint : (interior (nativeCodedBody K cuts)).Nonempty := by
    have h := hi.image e.toHomeomorph
    rw [e.toHomeomorph.image_interior] at h
    exact h
  exact ⟨hc.isClosed, hc.isBounded, hv, hint⟩
private theorem chosenOuterFrame_coded_spec {d p : ℕ} {K : Set (Space d)}
    (hK : IsCompact K) (hcv : Convex ℝ K) (cuts : Fin p → CutCode d)
    (hi : (interior (codedBody K cuts)).Nonempty) :
    let S := nativeCodedBody K cuts
    let F := chosenOuterFrame S
    F.1.det ≠ 0 ∧ IsMinVolCircumscribed S (ellipsoid F.1 F.2) ∧
      S ⊆ ellipsoid F.1 F.2 ∧
      ellipsoid ((1 / (d : ℝ)) • F.1) F.2 ⊆ S := by
  dsimp only
  have hsolid := nativeCodedBody_solid hK hcv cuts hi
  have hs := chosenOuterFrame_spec hsolid
  exact ⟨hs.1, hs.2, hs.2.2.1,
    ((lowner_fritz_john _ hsolid).2.2 _ _ hs.1 hs.2).1⟩
private theorem codedBody_snoc {d p : ℕ} (K : Set (Space d)) (cuts : Fin p → CutCode d)
    (cut : CutCode d) : codedBody K (Fin.snoc cuts cut) = codedBody K cuts ∩ cutSet (decodeCut cut) := by
  ext x
  simp only [codedBody, activeBody, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro h
    refine ⟨⟨h.1, fun i => ?_⟩, ?_⟩
    · simpa only [Fin.snoc_castSucc] using h.2 i.castSucc
    · simpa only [Fin.snoc_last] using h.2 (Fin.last p)
  · intro h
    refine ⟨h.1.1, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using h.2
    · simpa only [Fin.snoc_castSucc] using h.1.2 j
private theorem codedBody_snoc_zero {d p : ℕ} (K : Set (Space d)) (cuts : Fin p → CutCode d) :
    codedBody K (Fin.snoc cuts 0) = codedBody K cuts := by
  rw [codedBody_snoc]
  have hz : decodeCut (0 : CutCode d) = 0 := by
    simp [decodeCut]
    rfl
  rw [hz, zero_cutSet, Set.inter_univ]
private theorem ball_scaled_unit_parameterization {d : ℕ} {r : ℝ} (hr : 0 < r) (x : Space d) :
    x ∈ Metric.closedBall 0 r ↔ ∃ u : Fin d → ℝ,
      u ∈ unitBall d ∧ x = r • (EuclideanSpace.equiv (Fin d) ℝ).symm u := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  constructor
  · intro hx
    refine ⟨e (r⁻¹ • x), ?_, ?_⟩
    · apply (LG2021.euclidean_unitBall_iff (r⁻¹ • x)).mpr
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hr)]
      have hxn : ‖x‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
      calc
        r⁻¹ * ‖x‖ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left hxn (inv_nonneg.mpr hr.le)
        _ = 1 := inv_mul_cancel₀ hr.ne'
    · simp [e, smul_smul, hr.ne']
  · rintro ⟨u, hu, rfl⟩
    have hunit : ‖e.symm u‖ ≤ 1 := by
      have hu' : e (e.symm u) ∈ unitBall d := by
        rw [e.apply_symm_apply]
        exact hu
      have h := (LG2021.euclidean_unitBall_iff (e.symm u)).mp hu'
      simpa only [Metric.mem_closedBall, dist_zero_right] using h
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left hunit hr.le).trans_eq (mul_one r)
private theorem native_frame_image_ball {d : ℕ} (F : Frame d) {r : ℝ} (hr : 0 < r) :
    (EuclideanSpace.equiv (Fin d) ℝ) '' (frameApply F '' Metric.closedBall 0 r) =
      ellipsoid (r • F.1) ((EuclideanSpace.equiv (Fin d) ℝ) F.2) := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  have heval (u : Fin d → ℝ) : e (frameApply F (r • e.symm u)) =
      (r • F.1) *ᵥ u + e F.2 := by
    change e (e.symm (F.1 *ᵥ e (r • e.symm u)) + F.2) = _
    rw [map_add, e.apply_symm_apply, map_smul, e.apply_symm_apply,
      mulVec_smul, smul_mulVec]
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨u, hu, rfl⟩ := (ball_scaled_unit_parameterization hr z).mp hz
    exact ⟨u, hu, heval u⟩
  · rintro ⟨u, hu, hx⟩
    refine ⟨frameApply F (r • e.symm u), ⟨r • e.symm u, ?_, rfl⟩, ?_⟩
    · exact (ball_scaled_unit_parameterization hr _).mpr ⟨u, hu, rfl⟩
    · exact (heval u).trans hx.symm
private theorem canonicalOuterFrame_det_ne_zero {d p : ℕ} {K : Set (Space d)}
    (hK : IsCompact K) (hcv : Convex ℝ K) {r : ℝ} (hr : 0 < r)
    (cuts : Fin p → CutCode d) (hi : (interior (codedBody K cuts)).Nonempty) :
    (canonicalOuterFrame K r cuts).1.det ≠ 0 := by
  have hdet := (chosenOuterFrame_coded_spec hK hcv cuts hi).1
  simpa only [canonicalOuterFrame, Matrix.det_smul, Fintype.card_fin] using
    mul_ne_zero (pow_ne_zero d (inv_ne_zero hr.ne')) hdet
private theorem canonicalOuterFrame_inner_ball {d p : ℕ} (hd : 0 < d) {K : Set (Space d)}
    (hK : IsCompact K) (hcv : Convex ℝ K) {r : ℝ} (hr : 0 < r)
    (cuts : Fin p → CutCode d) (hi : (interior (codedBody K cuts)).Nonempty) :
    frameApply (canonicalOuterFrame K r cuts) '' Metric.closedBall 0 (r / (d : ℝ)) ⊆
      codedBody K cuts := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hrad : 0 < r / (d : ℝ) := div_pos hr hdreal
  have hfactor : (r / (d : ℝ)) * r⁻¹ = 1 / (d : ℝ) := by field_simp
  have himage := native_frame_image_ball (canonicalOuterFrame K r cuts) hrad
  simp only [canonicalOuterFrame, ContinuousLinearEquiv.apply_symm_apply, smul_smul,
    hfactor] at himage
  intro x hx
  let e := EuclideanSpace.equiv (Fin d) ℝ
  have he : e x ∈ ellipsoid ((1 / (d : ℝ)) •
      (chosenOuterFrame (nativeCodedBody K cuts)).1)
      (chosenOuterFrame (nativeCodedBody K cuts)).2 := by
    rw [← himage]
    exact ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := (chosenOuterFrame_coded_spec hK hcv cuts hi).2.2.2 he
  have hyx' : y = x := e.injective hyx
  simpa only [hyx'] using hy
end LG2021.Algorithm
end
end
/- LG2021AlgorithmState -/
section
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace LG2021.Algorithm
open MeasureTheory Concentration
open scoped Classical
private theorem step_continues {d u p : ℕ} (cfg : OracleConfig) (R : ℝ)
    (rounding : (Fin (p + 1) → CutCode d) → Frame d)
    (st : State d u p) (next : Fin u → Space d) (x : Space d) (y y' : ℝ)
    (h : winner cfg (st.2.2.2.1 + 1) (updatedScalars cfg st x y y') = none) :
    step cfg R rounding st next x y y' =
      continueState st (updatedScalars cfg st x y y') (updatedGradients cfg st x y) := by
  simp only [step, h]
private theorem step_restarts {d u p : ℕ} (cfg : OracleConfig) (R : ℝ)
    (rounding : (Fin (p + 1) → CutCode d) → Frame d)
    (st : State d u p) (next : Fin u → Space d) (x : Space d) (y y' : ℝ) (s : Fin u)
    (h : winner cfg (st.2.2.2.1 + 1) (updatedScalars cfg st x y y') = some s) :
    step cfg R rounding st next x y y' =
      restartState cfg R rounding st next (updatedScalars cfg st x y y')
        (updatedGradients cfg st x y) s := by
  simp only [step, h]
end LG2021.Algorithm
end
end
/- CorollaryTransport -/
section
noncomputable section
namespace BilateralProfitMHR.CorollaryTransport
open MeasureTheory
open scoped ENNReal
end BilateralProfitMHR.CorollaryTransport
end
end
/- LG2021GaussianGeometrySphere -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
end LG2021
end
end
/- Normalized Gaussian norm support -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
end LG2021
end
end
/- LG2021AlgorithmPolicy -/
section
noncomputable section
namespace LG2021.Algorithm
open MeasureTheory BilateralProfitMHR
open scoped Classical
end LG2021.Algorithm
end
end
/- CorollaryNormalization -/
section
noncomputable section
namespace BilateralProfitMHR.CorollaryTransport
open MeasureTheory
open scoped ENNReal
end BilateralProfitMHR.CorollaryTransport
end
end
/- LG2021Process -/
section
namespace LG2021
open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal
end LG2021
end
/- LG2021Concentration -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
end LG2021.Concentration
end
/- LG2021ConcentrationProducts -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationCentering -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationEstimators -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
end LG2021.Concentration
end
/- LG2021ConcentrationObservation -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationKernelMoments -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021GaussianMoments -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal NNReal
end LG2021
end
end
/- LG2021ConcentrationEstimatorMoments -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
end LG2021.Concentration
end
/- LG2021ConcentrationParameters -/
section
set_option autoImplicit false
namespace LG2021.Concentration
/-- Elementary bounds on the explicit confidence base. -/
private theorem parameterBase_bounds (d n : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    (10 ^ 6 : ℝ) ≤ parameterBase d D n ∧
      (d : ℝ) + 1 ≤ parameterBase d D n ∧
      D + 1 ≤ parameterBase d D n ∧
      (n : ℝ) + 1 ≤ parameterBase d D n ∧
      3 * (D + 1) * ((d : ℝ) + 1) ≤ parameterBase d D n := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hdn : (1 : ℝ) ≤ ((d : ℝ) + 1) * ((n : ℝ) + 1) := by nlinarith
  have hDn : (1 : ℝ) ≤ (D + 1) * ((n : ℝ) + 1) := by nlinarith
  have hdD : (1 : ℝ) ≤ ((d : ℝ) + 1) * (D + 1) := by nlinarith
  unfold parameterBase
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hdD (show 0 ≤ (n : ℝ) + 1 by positivity)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hDn (show 0 ≤ (d : ℝ) + 1 by positivity)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hdn (show 0 ≤ D + 1 by positivity)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hdD (show 0 ≤ (n : ℝ) + 1 by positivity)]
  · nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (n : ℝ) + 1 by linarith)
      (show 0 ≤ ((d : ℝ) + 1) * (D + 1) by positivity)]
/-- The explicit confidence logarithm is bounded below and above. -/
private theorem parameterLog_bounds (d n : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    1 ≤ parameterLog d D n ∧ parameterLog d D n ≤ 32 * parameterBase d D n := by
  have hb := (parameterBase_bounds d n hD).1
  have hA : 0 < parameterBase d D n := by nlinarith
  have hlower : 1 ≤ Real.log (parameterBase d D n) := by
    apply (Real.le_log_iff_exp_le hA).2
    have h := Real.exp_one_lt_three
    nlinarith
  have hupper := Real.log_le_sub_one_of_pos hA
  unfold parameterLog
  constructor <;> linarith
/-- Basic size bounds for the Gaussian scale in the logarithmic regime. -/
private theorem paperRadius_bounds {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 1 ≤ L) :
    (10 ^ 5 : ℝ) * (d : ℝ) ^ 2 ≤ paperRadius d L ∧
      0 < paperRadius d L ∧ paperRadius d L ≤ 2 * 10 ^ 5 * (d : ℝ) ^ 2 * L := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlo : 1 ≤ Real.sqrt (2 * L) := Real.one_le_sqrt.2 (by linarith)
  have hhi : Real.sqrt (2 * L) ≤ 2 * L := (Real.sqrt_le_left (by linarith)).2 (by nlinarith)
  unfold paperRadius
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlo (show 0 ≤ (10 ^ 5 : ℝ) * (d : ℝ) ^ 2 by positivity)]
  constructor
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_left hhi (show 0 ≤ (10 ^ 5 : ℝ) * (d : ℝ) ^ 2 by positivity)]
/-- The contraction parameter is positive and uniformly small. -/
private theorem paperLambda_bounds {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 1 ≤ L) :
    0 < paperLambda d L ∧ paperLambda d L ≤ 1 / 2 ∧
      (d : ℝ) * paperLambda d L ≤ 1 / 2 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hLpos : 0 < L := by linarith
  have hden : 0 < (4 * 10 ^ 5 : ℝ) * (d : ℝ) * L := by positivity
  unfold paperLambda
  refine ⟨by positivity, ?_, ?_⟩
  · apply (div_le_iff₀ hden).2
    have h := mul_le_mul hdR hL (by norm_num) (by positivity)
    nlinarith
  · rw [mul_one_div]
    apply (div_le_iff₀ hden).2
    have h := mul_le_mul_of_nonneg_left hL hdpos.le
    nlinarith
end LG2021.Concentration
end
/- LG2021ConcentrationFinite -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
open scoped NNReal
end LG2021.Concentration
end
/- LG2021ConcentrationTruncation -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationGaussianTails -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal
end LG2021.Concentration
end
/- LG2021ConcentrationParameterTails -/
section
set_option autoImplicit false
namespace LG2021.Concentration
end LG2021.Concentration
end
/- LG2021GaussianGeometrySurrogate -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
private theorem integrable_lipschitz_gaussian_affine {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (a : ℝ) (z : Space d) :
    Integrable (fun x => f (a • x + z)) (gaussian d) := by
  have hx : Integrable (fun x : Space d => x) (gaussian d) := by
    unfold gaussian
    exact IsGaussian.integrable_fun_id
  have hmajor : Integrable (fun x : Space d => ‖f 0‖ +
      (K : ℝ) * (|a| * ‖x‖ + ‖z‖)) (gaussian d) :=
    (integrable_const _).add (((hx.norm.const_mul |a|).add (integrable_const _)).const_mul _)
  apply hmajor.mono' (hf.continuous.comp (by fun_prop)).aestronglyMeasurable
  filter_upwards with x
  calc
    ‖f (a • x + z)‖ ≤ ‖f 0‖ + ‖f 0 - f (a • x + z)‖ := norm_le_insert _ _
    _ ≤ ‖f 0‖ + (K : ℝ) * ‖a • x + z‖ := by
      gcongr
      simpa only [zero_sub, norm_neg] using hf.norm_sub_le 0 (a • x + z)
    _ ≤ ‖f 0‖ + (K : ℝ) * (|a| * ‖x‖ + ‖z‖) := by
      gcongr
      simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le (a • x) z
private theorem integrable_lipschitz_gaussian {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) : Integrable f (gaussian d) := by
  simpa using integrable_lipschitz_gaussian_affine hf 1 0
private theorem gaussianMean_ge_value_zero {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f) : f 0 ≤ gaussianMean f := by
  have hx : Integrable (fun x : Space d => x) (gaussian d) := by
    unfold gaussian
    exact IsGaussian.integrable_fun_id
  have h := hc.map_integral_le hf.continuous.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hx (integrable_lipschitz_gaussian hf)
  simpa [gaussianMean, gaussian] using h
private theorem surrogate_le {d : ℕ} {f : Space d → ℝ} {K : NNReal} {lambda : ℝ}
    (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f)
    (hl : 0 < lambda) (hl1 : lambda ≤ 1) (z : Space d) : surrogate lambda f z ≤ f z := by
  have hi := integrable_lipschitz_gaussian hf
  have hia := integrable_lipschitz_gaussian_affine hf (1 - lambda) (lambda • z)
  have hp : ∀ x : Space d, f ((1 - lambda) • x + lambda • z) ≤
      (1 - lambda) * f x + lambda * f z := by
    intro x
    simpa only [smul_eq_mul] using hc.2 (Set.mem_univ x) (Set.mem_univ z)
      (sub_nonneg.mpr hl1) hl.le (by ring : 1 - lambda + lambda = 1)
  have hh := integral_mono hia ((hi.const_mul _).add (integrable_const _)) hp
  change (∫ x, f ((1 - lambda) • x + lambda • z) ∂gaussian d) ≤
    ∫ x, (1 - lambda) * f x + lambda * f z ∂gaussian d at hh
  simp only [integral_add (hi.const_mul _) (integrable_const _), integral_const_mul,
    integral_const, probReal_univ, smul_eq_mul] at hh
  change gaussianMean f + (_ - gaussianMean f) / lambda ≤ f z
  have hd : ((∫ x, f ((1 - lambda) • x + lambda • z) ∂gaussian d) -
      gaussianMean f) / lambda ≤ f z - gaussianMean f := by
    apply (div_le_iff₀ hl).2
    unfold gaussianMean
    nlinarith
  linarith
private theorem surrogate_convex {d : ℕ} {f : Space d → ℝ} {K : NNReal} {lambda : ℝ}
    (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f) (hl : 0 < lambda) :
    ConvexOn ℝ Set.univ (surrogate lambda f) := by
  let F : Space d → ℝ := fun z => ∫ x, f ((1 - lambda) • x + lambda • z) ∂gaussian d
  have hF : ConvexOn ℝ Set.univ F := by
    refine ⟨convex_univ, ?_⟩
    intro z hz w hw a b ha hb hab
    have hiz := integrable_lipschitz_gaussian_affine hf (1 - lambda) (lambda • z)
    have hiw := integrable_lipschitz_gaussian_affine hf (1 - lambda) (lambda • w)
    have him := integrable_lipschitz_gaussian_affine hf (1 - lambda)
      (lambda • (a • z + b • w))
    have hpoint : ∀ x : Space d,
        f ((1 - lambda) • x + lambda • (a • z + b • w)) ≤
          a * f ((1 - lambda) • x + lambda • z) +
          b * f ((1 - lambda) • x + lambda • w) := by
      intro x
      have heq : a • ((1 - lambda) • x + lambda • z) +
          b • ((1 - lambda) • x + lambda • w) =
          (1 - lambda) • x + lambda • (a • z + b • w) := by
        calc
          _ = (a + b) • ((1 - lambda) • x) + lambda • (a • z + b • w) := by module
          _ = _ := by rw [hab, one_smul]
      simpa only [heq, smul_eq_mul] using hc.2
        (Set.mem_univ ((1 - lambda) • x + lambda • z))
        (Set.mem_univ ((1 - lambda) • x + lambda • w)) ha hb hab
    have hh := integral_mono him ((hiz.const_mul a).add (hiw.const_mul b)) hpoint
    change (∫ x, f ((1 - lambda) • x + lambda • (a • z + b • w)) ∂gaussian d) ≤
      ∫ x, a * f ((1 - lambda) • x + lambda • z) +
        b * f ((1 - lambda) • x + lambda • w) ∂gaussian d at hh
    simpa only [F, integral_add (hiz.const_mul a) (hiw.const_mul b), integral_const_mul,
      smul_eq_mul] using hh
  have hscaled := (hF.smul (show 0 ≤ 1 / lambda by positivity)).add_const
    (gaussianMean f - gaussianMean f / lambda)
  have heq : surrogate lambda f = fun z => (1 / lambda) * F z +
      (gaussianMean f - gaussianMean f / lambda) := by
    funext z
    simp only [surrogate, F]
    ring
  rw [heq]
  exact hscaled
end LG2021
end
end
/- LG2021ConcentrationEnvelopes -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
end LG2021.Concentration
end
/- LG2021ConcentrationBias -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021GaussianGeometryTranslation -/
section
noncomputable section
namespace LG2021.GaussianTranslation
universe uX uY uι
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
end LG2021.GaussianTranslation
namespace LG2021
open MeasureTheory ProbabilityTheory
end LG2021
end
end
/- LG2021GaussianGeometryDensity -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
end LG2021
end
end
/- LG2021GaussianGeometryAffine -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
end LG2021
end
end
/- LG2021GaussianGeometryChangeOfMeasure -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
end LG2021
end
end
/- LG2021GaussianGeometryMollification -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace
end LG2021
end
end
/- LG2021GaussianGeometrySmoothingReuse -/
section
noncomputable section
namespace LG2021.ReusedSmoothing.RGF6
open MeasureTheory ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
private lemma lipschitz_cont (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y, |f x-f y| ≤ L*‖x-y‖) : Continuous f := by
  refine (LipschitzWith.of_dist_le_mul (K := L.toNNReal) (fun x y => ?_)).continuous
  simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,Real.coe_toNNReal _ hL] using hlip x y
private lemma nonsmooth_integrable (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y, |f x-f y| ≤ L*‖x-y‖) (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    Integrable (fun u => f (x+μ • u) • u) (stdGaussian E) := by
  have hc := lipschitz_cont f L hL hlip
  have h1 : Integrable (fun u : E => ‖u‖) (stdGaussian E) := IsGaussian.integrable_id.norm
  have h2 : Integrable (fun u : E => ‖u‖^2) (stdGaussian E) :=
    (IsGaussian.memLp_id (stdGaussian E) (2:ℕ) (by simp)).integrable_norm_pow (by norm_num)
  refine Integrable.mono' ((h1.const_mul |f x|).add (h2.const_mul (L*μ)))
    ((hc.comp (by fun_prop)).smul continuous_id).aestronglyMeasurable ?_
  filter_upwards [] with u
  have hh := hlip (x+μ • u) x
  rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hμ] at hh
  have hfn : |f (x+μ • u)| ≤ |f x|+L*μ*‖u‖ := by
    have htri := abs_add_le (f (x+μ • u)-f x) (f x)
    rw [sub_add_cancel] at htri
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hfn (norm_nonneg u)
  rw [norm_smul,Real.norm_eq_abs]
  dsimp only [Pi.add_apply]
  nlinarith
end LG2021.ReusedSmoothing.RGF6
namespace LG2021
open MeasureTheory ProbabilityTheory
private theorem gaussianMollify_hasGradient {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {epsilon : ℝ} (he : 0 < epsilon) (z : Space d) :
    HasGradientAt (gaussianMollify epsilon f)
      (∫ u, ((f (z + epsilon • u) - f z) / epsilon) • u ∂gaussian d) z := by
  have hLip (x y : Space d) : |f x - f y| ≤ (K : ℝ) * ‖x - y‖ := by
    simpa only [Real.norm_eq_abs] using hf.norm_sub_le x y
  have heq : gaussianMollify epsilon f =
      RandomGradFree.Shared.smoothing f epsilon := rfl
  rw [heq]
  simpa only [gaussian, RandomGradFree.Nonsmooth.oracle] using
    RandomGradFree.Nonsmooth.smoothing_hasGradient f (K : ℝ) K.coe_nonneg hLip epsilon he z
end LG2021
end
end
/- LG2021GaussianGeometryIntegrability -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
end LG2021
end
end
/- LG2021GaussianGeometryGradient -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
private theorem integrable_gaussian_affine_value_smul {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {epsilon : ℝ} (he : 0 ≤ epsilon) (z : Space d) :
    Integrable (fun u => f (z + epsilon • u) • u) (gaussian d) := by
  apply ReusedSmoothing.RGF6.nonsmooth_integrable f (K : ℝ) K.coe_nonneg
    (fun x y => ?_) epsilon he z
  simpa only [Real.norm_eq_abs] using hf.norm_sub_le x y
private theorem gaussianMollify_hasGradient_uncentered {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {epsilon : ℝ} (he : 0 < epsilon) (z : Space d) :
    HasGradientAt (gaussianMollify epsilon f)
      (epsilon⁻¹ • ∫ u, f (z + epsilon • u) • u ∂gaussian d) z := by
  have hi := integrable_gaussian_affine_value_smul hf he.le z
  have hx : Integrable (fun u : Space d => u) (gaussian d) := IsGaussian.integrable_fun_id
  have heq : (fun u : Space d => ((f (z + epsilon • u) - f z) / epsilon) • u) =
      fun u => epsilon⁻¹ • (f (z + epsilon • u) • u - f z • u) := by
    funext u
    simp only [div_eq_mul_inv, smul_sub, smul_smul, ← sub_smul]
    congr 1
    ring
  have h := gaussianMollify_hasGradient hf he z
  have hic : Integrable (fun u : Space d => f z • u) (gaussian d) := hx.smul (f z)
  rw [heq, integral_smul, integral_sub hi hic, integral_smul] at h
  simpa only [gaussian, integral_id_stdGaussian, smul_zero, sub_zero] using h
private theorem surrogate_hasFDerivAt {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {lambda : ℝ} (hl : lambda ≠ 0) (hl1 : lambda < 1)
    (z : Space d) :
    HasFDerivAt (surrogate lambda f)
      (InnerProductSpace.toDual ℝ (Space d)
        ((1-lambda)⁻¹ • ∫ u, f (lambda • z + (1-lambda) • u) • u ∂gaussian d)) z := by
  let A := InnerProductSpace.toDual ℝ (Space d)
    ((1-lambda)⁻¹ • ∫ u, f (lambda • z + (1-lambda) • u) • u ∂gaussian d)
  have h := (gaussianMollify_hasGradient_uncentered hf (sub_pos.mpr hl1)
    (lambda • z)).hasFDerivAt
  have hc := h.comp z ((hasFDerivAt_id z).const_smul lambda)
  have hh := (((hc.sub_const (gaussianMean f)).const_mul lambda⁻¹).const_add (gaussianMean f))
  have heq : (fun y => gaussianMean f +
      lambda⁻¹ * (gaussianMollify (1-lambda) f (lambda • y) - gaussianMean f)) =
      surrogate lambda f := by
    ext y
    simp only [surrogate, gaussianMollify, add_comm]
    ring
  change HasFDerivAt (fun y => gaussianMean f +
      lambda⁻¹ * (gaussianMollify (1-lambda) f (lambda • y) - gaussianMean f))
      (lambda⁻¹ • A.comp (lambda • ContinuousLinearMap.id ℝ (Space d))) z at hh
  rw [heq] at hh
  have heqD : lambda⁻¹ • A.comp (lambda • ContinuousLinearMap.id ℝ (Space d)) = A := by
    ext v
    simp [ContinuousLinearMap.comp_apply, hl]
  rw [heqD] at hh
  exact hh
end LG2021
end
end
/- LG2021ConcentrationSurrogateBias -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationLemma4 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationConditional -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationOracleMoments -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationOracleGradient -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationPathLaw -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal
end LG2021.Concentration
end
end
/- LG2021ConcentrationFreshSeed -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal
end LG2021.Concentration
end
end
/- LG2021ConcentrationNoAnticipation -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped Classical
end LG2021.Concentration
end
end
/- LG2021ConcentrationSeedCoordinates -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal
end LG2021.Concentration
end
end
/- LG2021ConcentrationPairPath -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal
end LG2021.Concentration
end
end
/- LG2021ConcentrationPairKernel -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR
end LG2021.Concentration
end
end
/- LG2021ConcentrationObservationPath -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal Classical
end LG2021.Concentration
end
end
/- LG2021ConcentrationPredictableMeans -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
end LG2021.Concentration
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
end LG2021.Concentration
end
end
/- LG2021ConcentrationPathAccumulation -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal
end LG2021.Concentration
end
end
/- LG2021ConcentrationPredictable -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
end LG2021.Concentration
end
end
/- LG2021ConcentrationKernelPrefix -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
end LG2021.Concentration
end
end
/- LG2021ConcentrationPathFinite -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal
end LG2021.Concentration
end
end
/- LG2021ConcentrationPredictableEstimators -/
section
noncomputable section
set_option maxHeartbeats 800000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal
end LG2021.Concentration
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal
end LG2021.Concentration
end
end
/- LG2021ConcentrationPredictableGradient -/
section
noncomputable section
set_option maxHeartbeats 800000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal
end LG2021.Concentration
end
end
/- LG2021ConcentrationBernstein -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021OracleConfidenceArithmetic -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
private theorem oracleMomentConstant_pos : 0 < oracleMomentConstant := by norm_num [oracleMomentConstant]
private theorem oracleConcentrationConstant_pos : 0 < oracleConcentrationConstant := by
  norm_num [oracleConcentrationConstant]
end LG2021.Concentration
end
end
/- LG2021ConcentrationHistoryPrefix -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal
end LG2021.Concentration
end
end
/- LG2021ConcentrationEstimatorConfidence -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal
end LG2021.Concentration
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal
end LG2021.Concentration
end
end
/- LG2021ConcentrationTerminalConfidence -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal
end LG2021.Concentration
end
end
/- LG2021AlgorithmInvariant -/
section
noncomputable section
namespace LG2021.Algorithm
open Set MeasureTheory BilateralProfitMHR
open scoped Classical
private theorem canonicalOuterFrame_snoc_zero {d p : ℕ} (K : Set (Space d)) (r : ℝ)
    (cuts : Fin p → CutCode d) :
    canonicalOuterFrame K r (Fin.snoc cuts 0) = canonicalOuterFrame K r cuts := by
  unfold canonicalOuterFrame nativeCodedBody
  rw [codedBody_snoc_zero]
private theorem step_frame {d u p : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (st : State d u p) (hframe : st.2.1 = canonicalOuterFrame K cfg.radius st.1)
    (next : Fin u → Space d) (x : Space d) (y y' : ℝ) :
    (step cfg R (canonicalOuterFrame K cfg.radius) st next x y y').2.1 =
      canonicalOuterFrame K cfg.radius (step cfg R (canonicalOuterFrame K cfg.radius) st next x y y').1 := by
  cases h : winner cfg (st.2.2.2.1 + 1) (updatedScalars cfg st x y y') with
  | none =>
      simp only [step, h, continueState]
      rw [canonicalOuterFrame_snoc_zero]
      exact hframe
  | some s => simp only [step, h, restartState]
private theorem runState_frame {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (p : ℕ) (ys : Fin p → ℝ × ℝ) :
    (runState cfg K R seed p ys).2.1 =
      canonicalOuterFrame K cfg.radius (runState cfg K R seed p ys).1 := by
  induction p with
  | zero => rfl
  | succ p ih =>
      exact step_frame cfg K R _ (ih _) _ _ _ _
private theorem step_preserves_set {d u p : ℕ} (cfg : OracleConfig) (K S : Set (Space d))
    {R : ℝ} (hR : 0 ≤ R) (hbounded : ∀ x ∈ K, ‖x‖ ≤ R)
    (rounding : (Fin (p + 1) → CutCode d) → Frame d) (st : State d u p)
    (hS : S ⊆ codedBody K st.1) (next : Fin u → Space d) (x : Space d) (y y' : ℝ)
    (hmargin : ∀ s : Fin u,
      winner cfg (st.2.2.2.1 + 1) (updatedScalars cfg st x y y') = some s →
      ∀ w ∈ S, cutValue (cutFromEstimate st.2.1 (st.2.2.1 s)
        (gradientEstimate (st.2.2.2.1 + 1) (updatedGradients cfg st x y) s)) w ≤
        -lowerBound cfg (st.2.2.2.1 + 1) (updatedScalars cfg st x y y') s / 4) :
    S ⊆ codedBody K (step cfg R rounding st next x y y').1 := by
  cases h : winner cfg (st.2.2.2.1 + 1) (updatedScalars cfg st x y y') with
  | none =>
      simpa only [step, h, continueState, codedBody_snoc_zero] using hS
  | some s =>
      intro w hw
      simp only [step, h, restartState]
      rw [codedBody_snoc]
      refine ⟨hS hw, ?_⟩
      apply roundedInwardCut_preserves_margin _
        (winner_positive cfg _ _ h) hR w (hbounded w (hS hw).1)
      exact hmargin s h w hw
private theorem restart_body_subset_raw_cut {d u p : ℕ} (cfg : OracleConfig) (K : Set (Space d))
    {R : ℝ} (hR : 0 ≤ R) (hbounded : ∀ x ∈ K, ‖x‖ ≤ R)
    (rounding : (Fin (p + 1) → CutCode d) → Frame d) (st : State d u p)
    (next : Fin u → Space d) (x : Space d) (y y' : ℝ) (s : Fin u)
    (h : winner cfg (st.2.2.2.1 + 1) (updatedScalars cfg st x y y') = some s) :
    codedBody K (step cfg R rounding st next x y y').1 ⊆
      codedBody K st.1 ∩ cutSet (cutFromEstimate st.2.1 (st.2.2.1 s)
        (gradientEstimate (st.2.2.2.1 + 1) (updatedGradients cfg st x y) s)) := by
  simp only [step, h, restartState]
  rw [codedBody_snoc]
  intro w hw
  exact ⟨hw.1, roundedInwardCut_subset_original _
    (winner_positive cfg _ _ h) hR w (hbounded w hw.1.1) hw.2⟩
private theorem cutFromEstimate_normal_ne_zero {d : ℕ} (F : Frame d) (z v w : Space d)
    {θ : ℝ} (hθ : 0 < θ) (hmargin : cutValue (cutFromEstimate F z v) w ≤ -θ / 4) :
    (cutFromEstimate F z v).1 ≠ 0 := by
  intro hzero
  have hoff : (cutFromEstimate F z v).2 = 0 := by
    change inner ℝ (cutFromEstimate F z v).1 (frameApply F z) = 0
    rw [hzero, inner_zero_left]
  rw [cutValue, hzero, hoff, inner_zero_left, sub_self] at hmargin
  linarith
private theorem matrixAction_smul {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (a : ℝ) (x : Space d) : matrixAction M (a • x) = a • matrixAction M x := by
  simp [matrixAction, Matrix.mulVec_smul]
private theorem frame_lipschitz_of_inner_ball {d : ℕ} (F : Frame d) {K : Set (Space d)}
    {t D : ℝ} (ht : 0 < t)
    (hinner : frameApply F '' Metric.closedBall 0 t ⊆ K)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) :
    LipschitzWith (D / t).toNNReal (frameApply F) := by
  have hzero : frameApply F 0 ∈ K := hinner ⟨0, by simpa using ht.le, rfl⟩
  have hnorm (x : Space d) : ‖matrixAction F.1 x‖ ≤ (D / t) * ‖x‖ := by
    by_cases hx : x = 0
    · subst x
      simp [matrixAction]
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let u := (t / ‖x‖) • x
    have hu : u ∈ Metric.closedBall (0 : Space d) t := by
      simp [u, Metric.mem_closedBall, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht, abs_of_pos (div_pos ht hxpos), hxpos.ne']
    have hd := hdiam (frameApply F u) (hinner ⟨u, hu, rfl⟩) (frameApply F 0) hzero
    have hdist : dist (frameApply F u) (frameApply F 0) = ‖matrixAction F.1 u‖ := by
      simp [frameApply, matrixAction, dist_eq_norm]
    rw [hdist, show u = (t / ‖x‖) • x from rfl, matrixAction_smul, norm_smul,
      Real.norm_eq_abs, abs_of_pos (div_pos ht hxpos)] at hd
    calc
      ‖matrixAction F.1 x‖ = (‖x‖ / t) * ((t / ‖x‖) * ‖matrixAction F.1 x‖) := by field_simp
      _ ≤ (‖x‖ / t) * D := mul_le_mul_of_nonneg_left hd (by positivity)
      _ = (D / t) * ‖x‖ := by ring
  apply LipschitzWith.of_dist_le'
  intro x y
  have he : frameApply F x - frameApply F y = matrixAction F.1 (x - y) := by
    rw [matrixAction_sub]
    simp [frameApply]
  simpa only [dist_eq_norm, he] using hnorm (x - y)
private theorem canonicalOuterFrame_lipschitz {d p : ℕ} (hd : 0 < d)
    {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    {r D : ℝ} (hr : 0 < r) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (cuts : Fin p → CutCode d) (hi : (interior (codedBody K cuts)).Nonempty) :
    LipschitzWith ((d : ℝ) * D / r).toNNReal (frameApply (canonicalOuterFrame K r cuts)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hinner := canonicalOuterFrame_inner_ball hd hK hcv hr cuts hi
  have h := frame_lipschitz_of_inner_ball (canonicalOuterFrame K r cuts)
    (div_pos hr hdR) (hinner.trans (show codedBody K cuts ⊆ K from fun _ hx => hx.1)) hdiam
  have he : D / (r / (d : ℝ)) = (d : ℝ) * D / r := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  simpa only [he] using h
private theorem canonical_loss_lipschitz {d p : ℕ} (hd : 0 < d)
    {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    {r D : ℝ} (hr : 0 < r) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (cuts : Fin p → CutCode d) (hi : (interior (codedBody K cuts)).Nonempty)
    (F : Space d → ℝ) (hF : LipschitzWith 1 F) :
    LipschitzWith ((d : ℝ) * D / r).toNNReal
      (fun x => F (frameApply (canonicalOuterFrame K r cuts) x)) := by
  simpa only [one_mul, Function.comp_def] using hF.comp (canonicalOuterFrame_lipschitz hd hK hcv hr hdiam cuts hi)
end LG2021.Algorithm
end
end
/- LG2021OracleSampleComplexity -/
section
noncomputable section
namespace LG2021.Algorithm
open MeasureTheory
private theorem scaled_sqrt_le_of_sample_bound {a θ H C m : ℝ}
    (ha : 0 < a) (hθ : 0 < θ) (hH : 0 ≤ H) (hC : 0 < C) (hm : 0 < m)
    (hbound : (8 * a / θ) ^ 2 * H / C ≤ m) :
    a * Real.sqrt (H / (C * m)) ≤ θ / 8 := by
  have hmul := (div_le_iff₀ hC).1 hbound
  rw [div_pow, div_mul_eq_mul_div] at hmul
  have hmul := (div_le_iff₀ (sq_pos_of_pos hθ)).1 hmul
  have hratio : a ^ 2 * H / (C * m) ≤ θ ^ 2 / 64 := by
    apply (div_le_iff₀ (mul_pos hC hm)).2
    nlinarith
  have hsq := Real.sq_sqrt (div_nonneg hH (mul_pos hC hm).le)
  have hnonneg := Real.sqrt_nonneg (H / (C * m))
  have halg : (a * Real.sqrt (H / (C * m))) ^ 2 =
      a ^ 2 * H / (C * m) := by rw [mul_pow, hsq]; ring
  nlinarith
private theorem lowerBound_le_true {u : ℕ} (cfg : OracleConfig) (m : ℕ)
    (sums : Fin u → ℝ) (s : Fin u) (θ : ℝ)
    (herror : |scalarEstimate m sums s - θ| ≤ confidenceRadius cfg u m) :
    lowerBound cfg m sums s ≤ max 0 θ := by
  unfold lowerBound
  apply max_le_max le_rfl
  have h := (abs_le.mp herror).2
  linarith
private theorem eligible_of_confidence {u : ℕ} (cfg : OracleConfig) (m : ℕ)
    (sums : Fin u → ℝ) (s : Fin u) {θ : ℝ}
    (hθ : 0 < θ) (hm : 0 < m) (hLambda : 0 < cfg.lambda)
    (hc : 0 < cfg.momentConstant) (hr : 0 < cfg.radius)
    (hC : 0 < cfg.concentrationConstant) (hH : 0 ≤ confidenceLog cfg u)
    (hbias : 1 / (8 * cfg.radius * (cfg.horizon : ℝ)) ≤ θ / 8)
    (herror : |scalarEstimate m sums s - θ| ≤ confidenceRadius cfg u m)
    (hscalar : (8 * (cfg.momentConstant / cfg.lambda + 1) / θ) ^ 2 *
      confidenceLog cfg u / cfg.concentrationConstant ≤ (m : ℝ))
    (hgradient : (8 * cfg.momentConstant * cfg.radius / θ) ^ 2 *
      confidenceLog cfg u / cfg.concentrationConstant ≤ (m : ℝ)) :
    eligible cfg m sums s := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have ha : 0 < cfg.momentConstant / cfg.lambda + 1 := by positivity
  have hsqrt := scaled_sqrt_le_of_sample_bound ha hθ hH hC hmreal hscalar
  have he : confidenceRadius cfg u m ≤ θ / 4 := by
    unfold confidenceRadius
    linarith
  have hlower : θ / 2 ≤ lowerBound cfg m sums s := by
    have hlo := (abs_le.mp herror).1
    have hmax : scalarEstimate m sums s - confidenceRadius cfg u m ≤
        lowerBound cfg m sums s := le_max_right _ _
    linarith
  have hlpos : 0 < lowerBound cfg m sums s := by linarith
  refine ⟨hlpos, ?_⟩
  apply le_trans _ hgradient
  apply div_le_div_of_nonneg_right _ hC.le
  apply mul_le_mul_of_nonneg_right _ hH
  apply (sq_le_sq₀ (by positivity : 0 ≤
    4 * cfg.momentConstant * cfg.radius / lowerBound cfg m sums s)
    (by positivity : 0 ≤ 8 * cfg.momentConstant * cfg.radius / θ)).2
  apply (div_le_div_iff₀ hlpos hθ).2
  have h := mul_le_mul_of_nonneg_left hlower
    (show 0 ≤ 8 * cfg.momentConstant * cfg.radius by positivity)
  nlinarith
private theorem firstEligible_eq_none_iff (cfg : OracleConfig) {u : ℕ}
    (indices : List (Fin u)) (m : ℕ) (sums : Fin u → ℝ) :
    firstEligible cfg indices m sums = none ↔ ∀ s ∈ indices, ¬eligible cfg m sums s := by
  induction indices with
  | nil => simp [firstEligible]
  | cons i indices ih =>
      by_cases hi : eligible cfg m sums i <;> simp [firstEligible, hi, ih]
private theorem winner_eq_none_iff (cfg : OracleConfig) {u : ℕ}
    (m : ℕ) (sums : Fin u → ℝ) :
    winner cfg m sums = none ↔ ∀ s, ¬eligible cfg m sums s := by
  simp [winner, firstEligible_eq_none_iff]
private theorem nonstopping_cost_lt {u : ℕ} (cfg : OracleConfig) (m : ℕ)
    (sums : Fin u → ℝ) (s : Fin u) {θ : ℝ}
    (hθ : 0 < θ) (hm : 0 < m) (hLambda : 0 < cfg.lambda)
    (hc : 0 < cfg.momentConstant) (hr : 0 < cfg.radius)
    (hC : 0 < cfg.concentrationConstant) (hH : 0 ≤ confidenceLog cfg u)
    (hbias : 1 / (8 * cfg.radius * (cfg.horizon : ℝ)) ≤ θ / 8)
    (herror : |scalarEstimate m sums s - θ| ≤ confidenceRadius cfg u m)
    (hnone : winner cfg m sums = none) :
    (m : ℝ) * θ ^ 2 <
      64 * max ((cfg.momentConstant / cfg.lambda + 1) ^ 2)
        ((cfg.momentConstant * cfg.radius) ^ 2) *
          confidenceLog cfg u / cfg.concentrationConstant := by
  by_contra hnot
  have hbound := le_of_not_gt hnot
  have hcommon :
      (64 * max ((cfg.momentConstant / cfg.lambda + 1) ^ 2)
        ((cfg.momentConstant * cfg.radius) ^ 2) *
          confidenceLog cfg u / cfg.concentrationConstant) / θ ^ 2 ≤ (m : ℝ) :=
    (div_le_iff₀ (sq_pos_of_pos hθ)).2 hbound
  have hpart (a : ℝ)
      (ha : a ^ 2 ≤ max ((cfg.momentConstant / cfg.lambda + 1) ^ 2)
        ((cfg.momentConstant * cfg.radius) ^ 2)) :
      (8 * a / θ) ^ 2 * confidenceLog cfg u / cfg.concentrationConstant ≤ (m : ℝ) := by
    apply le_trans _ hcommon
    have heq : (8 * a / θ) ^ 2 * confidenceLog cfg u / cfg.concentrationConstant =
        (64 * a ^ 2 * confidenceLog cfg u / cfg.concentrationConstant) / θ ^ 2 := by
      field_simp
      ring
    rw [heq]
    gcongr
  have helig := eligible_of_confidence cfg m sums s hθ hm hLambda hc hr hC hH hbias herror
    (hpart _ (le_max_left _ _)) (by
      simpa only [mul_assoc] using hpart (cfg.momentConstant * cfg.radius) (le_max_right _ _))
  exact (winner_eq_none_iff cfg m sums).1 hnone s helig
end LG2021.Algorithm
end
end
/- LG2021AlgorithmTrace -/
section
noncomputable section
namespace LG2021.Algorithm
open scoped Classical
private theorem traceState_succ {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (p : ℕ) :
    traceState cfg K R seed ys (p + 1) =
      step cfg R (canonicalOuterFrame K cfg.radius) (traceState cfg K R seed ys p)
        (seedCandidates seed (p + 1)) (seedGaussian seed p) (ys p).1 (ys p).2 := rfl
private theorem traceStage_monotone {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) :
    Monotone (traceStage cfg K R seed ys) := by
  apply monotone_nat_of_le_succ
  intro p
  simp only [traceStage]
  omega
private theorem traceState_nonstopping {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (p : ℕ) :
    (traceState cfg K R seed ys p).2.2.2.1 = 0 ∨
      winner cfg (traceState cfg K R seed ys p).2.2.2.1
        (traceState cfg K R seed ys p).2.2.2.2.1 = none := by
  cases p with
  | zero => exact Or.inl rfl
  | succ p =>
      rw [traceState_succ]
      cases h : traceWinner cfg K R seed ys p with
      | none =>
          right
          change winner cfg _ _ = none
          rw [step_continues cfg R _ _ _ _ _ _ h]
          exact h
      | some s =>
          left
          rw [step_restarts cfg R _ _ _ _ _ _ s h]
          rfl
private theorem traceState_age_eq_card {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (p : ℕ) :
    (traceState cfg K R seed ys p).2.2.2.1 =
      ((Finset.range p).filter (fun j => traceStage cfg K R seed ys j =
        traceStage cfg K R seed ys p)).card := by
  induction p with
  | zero => simp [traceState, runState, initialState]
  | succ p ih =>
      rw [traceState_succ]
      cases h : traceWinner cfg K R seed ys p with
      | none =>
          rw [step_continues cfg R _ _ _ _ _ _ h]
          have hstage : traceStage cfg K R seed ys (p + 1) =
              traceStage cfg K R seed ys p := by simp [traceStage, h]
          change (traceState cfg K R seed ys p).2.2.2.1 + 1 = _
          rw [hstage, Finset.range_add_one, Finset.filter_insert]
          simp only [if_true]
          rw [Finset.card_insert_of_notMem (by simp)]
          exact congrArg (fun q => q + 1) ih
      | some s =>
          rw [step_restarts cfg R _ _ _ _ _ _ s h]
          change 0 = _
          have hstage : traceStage cfg K R seed ys (p + 1) =
              traceStage cfg K R seed ys p + 1 := by simp [traceStage, h]
          have hempty : (Finset.range (p + 1)).filter (fun j => traceStage cfg K R seed ys j =
              traceStage cfg K R seed ys (p + 1)) = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.2
            intro j hj
            rcases Finset.mem_filter.1 hj with ⟨hjp, hjs⟩
            have hle := traceStage_monotone cfg K R seed ys (Nat.le_of_lt_succ (Finset.mem_range.1 hjp))
            rw [hstage] at hjs
            omega
          rw [hempty]
          rfl
private theorem traceCore_succ_of_same_stage {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) (p : ℕ)
    (hstage : traceStage cfg K R seed ys (p + 1) = traceStage cfg K R seed ys p) :
    traceCore cfg K R seed ys (p + 1) = traceCore cfg K R seed ys p := by
  have hn : traceWinner cfg K R seed ys p = none := by
    by_contra hh
    simp only [traceStage, if_neg hh] at hstage
    omega
  unfold traceCore
  rw [traceState_succ, step_continues cfg R _ _ _ _ _ _ hn]
  rfl
private theorem eq_of_same_monotone_stage {X : Type*} (stage : ℕ → ℕ)
    (hmono : Monotone stage) (value : ℕ → X)
    (hnext : ∀ p, stage (p + 1) = stage p → value (p + 1) = value p)
    {p q : ℕ} (hpq : p ≤ q) (hstage : stage q = stage p) : value q = value p := by
  revert hstage
  induction q, hpq using Nat.le_induction with
  | base => intro _; rfl
  | succ j hpj ih =>
      intro hjs
      have hj : stage j = stage p := le_antisymm
        ((hmono (Nat.le_succ j)).trans_eq hjs) (hmono hpj)
      exact (hnext j (hjs.trans hj.symm)).trans (ih hj)
private theorem traceCore_eq_of_same_stage {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) {p q : ℕ}
    (hstage : traceStage cfg K R seed ys p = traceStage cfg K R seed ys q) :
    traceCore cfg K R seed ys p = traceCore cfg K R seed ys q := by
  rcases le_total p q with hpq | hqp
  · exact (eq_of_same_monotone_stage _ (traceStage_monotone cfg K R seed ys) _
      (traceCore_succ_of_same_stage cfg K R seed ys) hpq hstage.symm).symm
  · exact eq_of_same_monotone_stage _ (traceStage_monotone cfg K R seed ys) _
      (traceCore_succ_of_same_stage cfg K R seed ys) hqp hstage
private theorem traceState_age_eq_stage_prefix {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) (p : ℕ) :
    (traceState cfg K R seed ys p).2.2.2.1 + 1 =
      ((Finset.range (p + 1)).filter (fun j => traceStage cfg K R seed ys j =
        traceStage cfg K R seed ys p)).card := by
  rw [traceState_age_eq_card, Finset.range_add_one, Finset.filter_insert]
  simp only [if_true]
  rw [Finset.card_insert_of_notMem (by simp)]
end LG2021.Algorithm
end
end
/- LG2021TraceSums -/
section
noncomputable section
namespace LG2021.Algorithm
open Concentration
end LG2021.Algorithm
end
end
/- LG2021TerminalTrace -/
section
noncomputable section
namespace LG2021.Algorithm
end LG2021.Algorithm
end
end
/- LG2021RegretAggregation -/
section
namespace LG2021
private theorem stage_regret_sq_le {ι : Type*} (s : Finset ι) (N Δ : ι → ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hN : ∀ i ∈ s, 0 ≤ N i)
    (hcost : ∀ i ∈ s, N i * Δ i ^ 2 ≤ A) :
    (∑ i ∈ s, N i * Δ i) ^ 2 ≤ (∑ i ∈ s, N i) * ((s.card : ℝ) * A) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hN (fun _ _ => hA)
    (r := fun i => N i * Δ i) (g := fun _ => A) (fun i hi => by
      calc
        (N i * Δ i) ^ 2 = N i * (N i * Δ i ^ 2) := by ring
        _ ≤ N i * A := mul_le_mul_of_nonneg_left (hcost i hi) (hN i hi))
  simpa only [Finset.sum_const, nsmul_eq_mul] using h
private theorem stage_regret_le_sqrt {ι : Type*} (s : Finset ι) (N Δ : ι → ℝ)
    {A n k : ℝ} (hA : 0 ≤ A) (hN : ∀ i ∈ s, 0 ≤ N i)
    (hcost : ∀ i ∈ s, N i * Δ i ^ 2 ≤ A)
    (htotal : ∑ i ∈ s, N i ≤ n) (hcount : (s.card : ℝ) ≤ k) :
    ∑ i ∈ s, N i * Δ i ≤ Real.sqrt (n * (k * A)) := by
  have hn : 0 ≤ n := (Finset.sum_nonneg hN).trans htotal
  have hcard : 0 ≤ (s.card : ℝ) * A := mul_nonneg (Nat.cast_nonneg _) hA
  apply Real.le_sqrt_of_sq_le
  exact (stage_regret_sq_le s N Δ hA hN hcost).trans
    (mul_le_mul htotal (mul_le_mul_of_nonneg_right hcount hA) hcard hn)
private theorem stage_regret_le_sqrt_mul {ι : Type*} (s : Finset ι) (N Δ : ι → ℝ)
    {A n k : ℝ} (hA : 0 ≤ A) (hN : ∀ i ∈ s, 0 ≤ N i)
    (hcost : ∀ i ∈ s, N i * Δ i ^ 2 ≤ A)
    (htotal : ∑ i ∈ s, N i ≤ n) (hcount : (s.card : ℝ) ≤ k) :
    ∑ i ∈ s, N i * Δ i ≤ Real.sqrt A * Real.sqrt (n * k) := by
  have hn : 0 ≤ n := (Finset.sum_nonneg hN).trans htotal
  have hk : 0 ≤ k := (Nat.cast_nonneg s.card).trans hcount
  calc
    ∑ i ∈ s, N i * Δ i ≤ Real.sqrt (n * (k * A)) :=
      stage_regret_le_sqrt s N Δ hA hN hcost htotal hcount
    _ = Real.sqrt A * Real.sqrt (n * k) := by
      rw [show n * (k * A) = A * (n * k) by ring, Real.sqrt_mul hA]
end LG2021
end
/- LG2021StageAggregation -/
section
noncomputable section
namespace LG2021.Algorithm
open scoped Classical
private theorem stageFiber_nonempty {tag : ℕ → ℕ} {N s : ℕ} (hs : s ∈ stages tag N) :
    (stageFiber tag N s).Nonempty := by
  rcases Finset.mem_image.1 hs with ⟨p, hp, hps⟩
  exact ⟨p, Finset.mem_filter.2 ⟨hp, hps⟩⟩
private theorem stageValue_eq {tag : ℕ → ℕ} {N : ℕ} {g : ℕ → ℝ}
    (hconst : ∀ p < N, ∀ q < N, tag p = tag q → g p = g q)
    {s p : ℕ} (hp : p ∈ stageFiber tag N s) : stageValue tag N g s = g p := by
  have hne : (stageFiber tag N s).Nonempty := ⟨p, hp⟩
  rw [stageValue, dif_pos hne]
  have hrep := (stageFiber tag N s).max'_mem hne
  rcases Finset.mem_filter.1 hp with ⟨hpn, hps⟩
  rcases Finset.mem_filter.1 hrep with ⟨hrn, hrs⟩
  exact hconst _ (Finset.mem_range.1 hrn) p (Finset.mem_range.1 hpn) (hrs.trans hps.symm)
private theorem stageFiber_eq_prefix_at_max {tag : ℕ → ℕ} {N s : ℕ}
    (hne : (stageFiber tag N s).Nonempty) :
    stageFiber tag N s = stageFiber tag ((stageFiber tag N s).max' hne + 1) s := by
  let p := (stageFiber tag N s).max' hne
  have hp := (stageFiber tag N s).max'_mem hne
  have hpn : p < N := Finset.mem_range.1 (Finset.mem_filter.1 hp).1
  ext j
  constructor
  · intro hj
    have hjp : j ≤ p := (stageFiber tag N s).le_max' j hj
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), (Finset.mem_filter.1 hj).2⟩
  · intro hj
    rcases Finset.mem_filter.1 hj with ⟨hjp, hjs⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by
      have hjp' := Finset.mem_range.1 hjp
      omega), hjs⟩
private theorem sum_eq_stage_sum {tag : ℕ → ℕ} {N : ℕ} {g : ℕ → ℝ}
    (hconst : ∀ p < N, ∀ q < N, tag p = tag q → g p = g q) :
    (∑ p ∈ Finset.range N, g p) =
      ∑ s ∈ stages tag N, ((stageFiber tag N s).card : ℝ) * stageValue tag N g s := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun p hp => Finset.mem_image_of_mem tag hp) g]
  apply Finset.sum_congr rfl
  intro s hs
  calc
    _ = ∑ _ ∈ stageFiber tag N s, stageValue tag N g s := by
      apply Finset.sum_congr rfl
      intro p hp
      exact (stageValue_eq hconst hp).symm
    _ = _ := by simp
private theorem sum_stage_counts (tag : ℕ → ℕ) (N : ℕ) :
    (∑ s ∈ stages tag N, ((stageFiber tag N s).card : ℝ)) = N := by
  have h := (Finset.card_eq_sum_card_image tag (Finset.range N)).symm
  simp only [Finset.card_range] at h
  exact_mod_cast h
private theorem sum_le_sqrt_stage_budget {tag : ℕ → ℕ} {N : ℕ} {g : ℕ → ℝ}
    (hconst : ∀ p < N, ∀ q < N, tag p = tag q → g p = g q)
    {B k : ℝ} (hB : 0 ≤ B)
    (hprefix : ∀ p < N,
      ((stageFiber tag (p + 1) (tag p)).card : ℝ) * (g p) ^ 2 ≤ B)
    (hcount : ((stages tag N).card : ℝ) ≤ k) :
    (∑ p ∈ Finset.range N, g p) ≤ Real.sqrt B * Real.sqrt ((N : ℝ) * k) := by
  rw [sum_eq_stage_sum hconst]
  apply LG2021.stage_regret_le_sqrt_mul _ _ _ hB (fun _ _ => Nat.cast_nonneg _) _
    (le_of_eq (sum_stage_counts tag N)) hcount
  intro s hs
  have hne := stageFiber_nonempty hs
  let p := (stageFiber tag N s).max' hne
  have hp := (stageFiber tag N s).max'_mem hne
  have hpn : p < N := Finset.mem_range.1 (Finset.mem_filter.1 hp).1
  have hps : tag p = s := (Finset.mem_filter.1 hp).2
  have h := hprefix p hpn
  rw [hps, ← stageFiber_eq_prefix_at_max hne] at h
  rw [stageValue_eq hconst hp]
  exact h
private theorem stages_card_le_of_bound {tag : ℕ → ℕ} {N j : ℕ}
    (htag : ∀ p < N, tag p ≤ j) : (stages tag N).card ≤ j + 1 := by
  have hsub : stages tag N ⊆ Finset.range (j + 1) := by
    intro s hs
    rcases Finset.mem_image.1 hs with ⟨p, hp, rfl⟩
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (htag p (Finset.mem_range.1 hp)))
  simpa using Finset.card_le_card hsub
private theorem clipped_stage_cost_le {m : ℕ} {g θ k B : ℝ}
    (hm : 1 ≤ m) (hg : 0 ≤ g) (hg1 : g ≤ 1) (hk : 0 < k) (hθ : 0 ≤ θ)
    (hgap : g ≤ 2 * k * θ) (hbudget : ((m - 1 : ℕ) : ℝ) * θ ^ 2 ≤ B) :
    (m : ℝ) * g ^ 2 ≤ 4 * k ^ 2 * B + 1 := by
  have hg2 : g ^ 2 ≤ 1 := by nlinarith
  have hsq := (sq_le_sq₀ hg (by positivity : 0 ≤ 2 * k * θ)).2 hgap
  have hmR : (m : ℝ) = ((m - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast (Nat.sub_add_cancel hm).symm
  calc
    _ = ((m - 1 : ℕ) : ℝ) * g ^ 2 + g ^ 2 := by rw [hmR]; ring
    _ ≤ ((m - 1 : ℕ) : ℝ) * (2 * k * θ) ^ 2 + 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)) hg2
    _ = 4 * k ^ 2 * (((m - 1 : ℕ) : ℝ) * θ ^ 2) + 1 := by ring
    _ ≤ _ := by gcongr
end LG2021.Algorithm
end
end
/- LG2021StageSampleCost -/
section
noncomputable section
namespace LG2021.Algorithm
open scoped Classical
private theorem effectiveGap_bounds {n : ℕ} {k Δ : ℝ} (hΔ : 0 ≤ Δ) :
    0 ≤ effectiveGap n k Δ ∧ effectiveGap n k Δ ≤ 1 := by
  unfold effectiveGap
  split_ifs <;> constructor <;> simp [hΔ]
private theorem min_gap_le_effective_add {n : ℕ} (hn : 0 < n) {k Δ : ℝ}
    (hk : 0 ≤ k) : min 1 Δ ≤ effectiveGap n k Δ + 2 * (k + 1) / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold effectiveGap
  split_ifs with h
  · exact (min_le_right _ _).trans (by simpa using h)
  · have hnonneg : 0 ≤ 2 * (k + 1) / (n : ℝ) := by positivity
    linarith
private theorem candidate_gap_comparison {n : ℕ} (hn : 0 < n) {k Δ θ : ℝ}
    (hk : 1 ≤ k) (hlarge : 2 * (k + 1) / (n : ℝ) < Δ)
    (hcandidate : (Δ - 1 / (n : ℝ)) / k ≤ θ) :
    0 < θ ∧ 1 / (n : ℝ) ≤ θ ∧ Δ ≤ 2 * k * θ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkpos : 0 < k := by linarith
  have ht : 0 < 1 / (n : ℝ) := by positivity
  have hlarge' : 2 * (k + 1) * (1 / (n : ℝ)) < Δ := by
    simpa only [div_eq_mul_inv, one_mul] using hlarge
  have htheta : Δ - 1 / (n : ℝ) ≤ θ * k := (div_le_iff₀ hkpos).1 hcandidate
  have hlow : 1 / (n : ℝ) ≤ θ := by
    apply (mul_le_mul_iff_right₀ hkpos).1
    nlinarith [mul_nonneg hkpos.le ht.le]
  refine ⟨lt_of_lt_of_le ht hlow, hlow, ?_⟩
  have hΔ : 2 * (1 / (n : ℝ)) ≤ Δ := by nlinarith [mul_nonneg hkpos.le ht.le]
  nlinarith
private theorem confidence_bias_le {n : ℕ} (hn : 0 < n) {r θ : ℝ}
    (hr : 1 ≤ r) (hθ : 1 / (n : ℝ) ≤ θ) :
    1 / (8 * r * (n : ℝ)) ≤ θ / 8 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 8 * (n : ℝ) ≤ 8 * r * (n : ℝ) := by nlinarith
  calc
    _ ≤ 1 / (8 * (n : ℝ)) := one_div_le_one_div_of_le (by positivity) hden
    _ = (1 / (n : ℝ)) / 8 := by ring
    _ ≤ _ := by linarith
private theorem actual_state_stage_cost_le {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) (p : ℕ) {k Δ : ℝ}
    (hn : 0 < cfg.horizon) (hk : 1 ≤ k) (hΔ : 0 ≤ Δ)
    (hLambda : 0 < cfg.lambda) (hc : 0 < cfg.momentConstant)
    (hr : 1 ≤ cfg.radius) (hC : 0 < cfg.concentrationConstant)
    (hH : 0 ≤ confidenceLog cfg u)
    (hcandidate : ∃ s : Fin u, ∃ θ : ℝ,
      (Δ - 1 / (cfg.horizon : ℝ)) / k ≤ θ ∧
      (0 < (traceState cfg K R seed ys p).2.2.2.1 →
      |scalarEstimate (traceState cfg K R seed ys p).2.2.2.1
        (traceState cfg K R seed ys p).2.2.2.2.1 s - θ| ≤
          confidenceRadius cfg u (traceState cfg K R seed ys p).2.2.2.1)) :
    ((traceState cfg K R seed ys p).2.2.2.1 + 1 : ℕ) * effectiveGap cfg.horizon k Δ ^ 2 ≤
      4 * k ^ 2 * sampleBudget cfg u + 1 := by
  have hB : 0 ≤ sampleBudget cfg u := by unfold sampleBudget; positivity
  by_cases hsmall : Δ ≤ 2 * (k + 1) / (cfg.horizon : ℝ)
  · simp only [effectiveGap, if_pos hsmall, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
    positivity
  have hlarge := lt_of_not_ge hsmall
  obtain ⟨s, θ, hhit, herror⟩ := hcandidate
  have htheta := candidate_gap_comparison hn hk hlarge hhit
  have hbias := confidence_bias_le hn hr htheta.2.1
  have hgb := effectiveGap_bounds (n := cfg.horizon) (k := k) hΔ
  have hgap : effectiveGap cfg.horizon k Δ ≤ 2 * k * θ := by
    rw [effectiveGap, if_neg hsmall]
    exact (min_le_right _ _).trans htheta.2.2
  rcases traceState_nonstopping cfg K R seed ys p with hzero | hnone
  · rw [hzero]
    norm_num
    have hsq : effectiveGap cfg.horizon k Δ ^ 2 ≤ 1 := by nlinarith [hgb.1, hgb.2]
    nlinarith
  by_cases hmzero : (traceState cfg K R seed ys p).2.2.2.1 = 0
  · rw [hmzero]
    norm_num
    have hsq : effectiveGap cfg.horizon k Δ ^ 2 ≤ 1 := by nlinarith [hgb.1, hgb.2]
    nlinarith
  have hm : 0 < (traceState cfg K R seed ys p).2.2.2.1 := Nat.pos_of_ne_zero hmzero
  have hbudget := nonstopping_cost_lt cfg _ _ s htheta.1 hm hLambda hc
    (by linarith : 0 < cfg.radius) hC hH hbias (herror hm) hnone
  have hlast := clipped_stage_cost_le
    (m := (traceState cfg K R seed ys p).2.2.2.1 + 1) (by omega)
    hgb.1 hgb.2 (by linarith : 0 < k) htheta.1.le hgap
    (by simpa only [Nat.add_sub_cancel] using hbudget.le)
  simpa only [Nat.cast_add, Nat.cast_one, sampleBudget] using hlast
end LG2021.Algorithm
end
end
/- LG2021StageRegret -/
section
noncomputable section
namespace LG2021.Algorithm
open MeasureTheory
private theorem traceComparatorGap_eq_of_same_stage {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) (L : Space d → ℝ) (xstar : Space d) {p q : ℕ}
    (hstage : traceStage cfg K R seed ys p = traceStage cfg K R seed ys q) :
    traceComparatorGap cfg K R seed ys L xstar p = traceComparatorGap cfg K R seed ys L xstar q := by
  have hcore := traceCore_eq_of_same_stage cfg K R seed ys hstage
  have hframe : (traceState cfg K R seed ys p).2.1 =
      (traceState cfg K R seed ys q).2.1 :=
    congrArg (fun z : Frame d × (Fin u → Space d) => z.1) hcore
  exact congrArg (frameGap L xstar) hframe
private theorem trace_effective_gap_sum_le {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) (L : Space d → ℝ) (xstar : Space d) (N : ℕ) {k j : ℝ}
    (hn : 0 < cfg.horizon) (hk : 1 ≤ k)
    (hLambda : 0 < cfg.lambda) (hc : 0 < cfg.momentConstant)
    (hr : 1 ≤ cfg.radius) (hC : 0 < cfg.concentrationConstant)
    (hH : 0 ≤ confidenceLog cfg u)
    (hΔ : ∀ p < N, 0 ≤ traceComparatorGap cfg K R seed ys L xstar p)
    (hcandidate : ∀ p < N, ∃ s : Fin u, ∃ θ : ℝ,
      (traceComparatorGap cfg K R seed ys L xstar p - 1 / (cfg.horizon : ℝ)) / k ≤ θ ∧
      (0 < (traceState cfg K R seed ys p).2.2.2.1 →
        |scalarEstimate (traceState cfg K R seed ys p).2.2.2.1
          (traceState cfg K R seed ys p).2.2.2.2.1 s - θ| ≤
          confidenceRadius cfg u (traceState cfg K R seed ys p).2.2.2.1))
    (hcount : ((stages (traceStage cfg K R seed ys) N).card : ℝ) ≤ j) :
    (∑ p ∈ Finset.range N, effectiveGap cfg.horizon k (traceComparatorGap cfg K R seed ys L xstar p)) ≤
      Real.sqrt (4 * k ^ 2 * sampleBudget cfg u + 1) * Real.sqrt ((N : ℝ) * j) := by
  apply sum_le_sqrt_stage_budget
    (tag := traceStage cfg K R seed ys)
    (fun p _ q _ h => congrArg (effectiveGap cfg.horizon k)
      (traceComparatorGap_eq_of_same_stage cfg K R seed ys L xstar h))
    (by unfold sampleBudget; positivity) _ hcount
  intro p hp
  have hcost := actual_state_stage_cost_le cfg K R seed ys p hn hk (hΔ p hp)
    hLambda hc hr hC hH (hcandidate p hp)
  rw [traceState_age_eq_stage_prefix] at hcost
  exact hcost
private theorem trace_capped_gap_sum_le {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) (L : Space d → ℝ) (xstar : Space d) (N : ℕ) {k B : ℝ}
    (hn : 0 < cfg.horizon) (hk : 0 ≤ k) (hN : N ≤ cfg.horizon)
    (heffective : (∑ p ∈ Finset.range N,
      effectiveGap cfg.horizon k (traceComparatorGap cfg K R seed ys L xstar p)) ≤ B) :
    (∑ p ∈ Finset.range N, min 1 (traceComparatorGap cfg K R seed ys L xstar p)) ≤ B + 2 * (k + 1) := by
  have hnR : (0 : ℝ) < cfg.horizon := by exact_mod_cast hn
  have hNR : (N : ℝ) ≤ cfg.horizon := by exact_mod_cast hN
  calc
    _ ≤ ∑ p ∈ Finset.range N,
        (effectiveGap cfg.horizon k (traceComparatorGap cfg K R seed ys L xstar p) +
          2 * (k + 1) / (cfg.horizon : ℝ)) :=
      Finset.sum_le_sum fun _ _ => min_gap_le_effective_add hn hk
    _ = (∑ p ∈ Finset.range N,
        effectiveGap cfg.horizon k (traceComparatorGap cfg K R seed ys L xstar p)) +
          (N : ℝ) * (2 * (k + 1) / (cfg.horizon : ℝ)) := by
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ B + (cfg.horizon : ℝ) * (2 * (k + 1) / (cfg.horizon : ℝ)) := by gcongr
    _ = _ := by field_simp
end LG2021.Algorithm
end
end
/- LG2021TraceMeasurable -/
section
noncomputable section
namespace LG2021.Algorithm
open MeasureTheory
open scoped Classical
end LG2021.Algorithm
end
end
/- LG2021ConcentrationStageEstimators -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
end LG2021.Concentration
end
end
/- LG2021ConcentrationSumExpansion -/
section
noncomputable section
namespace LG2021.Concentration
open Algorithm
end LG2021.Concentration
end
end
/- LG2021ConcentrationStageExpansion -/
section
noncomputable section
namespace LG2021.Concentration
open Algorithm
end LG2021.Concentration
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR
end LG2021.Concentration
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR
end LG2021.Concentration
end
end
/- LG2021AlgorithmEllipsoidHelpers -/
section
noncomputable section
namespace LG2021.Algorithm
open Matrix MeasureTheory ModernConvex.EllipsoidMethod
private theorem normalized_cut_direction {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) (a : Fin n → ℝ) (ha : a ≠ 0) :
    cutDirection B a ⬝ᵥ cutDirection B a = 1 ∧
      Bᵀ *ᵥ a = Real.sqrt (a ⬝ᵥ ((B * Bᵀ) *ᵥ a)) • cutDirection B a ∧
      0 < Real.sqrt (a ⬝ᵥ ((B * Bᵀ) *ᵥ a)) := by
  set w := Bᵀ *ᵥ a with hwdef
  have hBt : IsUnit Bᵀ.det := by rw [det_transpose]; exact isUnit_iff_ne_zero.mpr hB
  have hw0 : w ≠ 0 := by
    intro h
    apply ha
    have : (Bᵀ)⁻¹ *ᵥ w = a := by rw [hwdef, mulVec_mulVec, nonsing_inv_mul _ hBt, one_mulVec]
    rw [← this, h, mulVec_zero]
  have hq : a ⬝ᵥ ((B * Bᵀ) *ᵥ a) = w ⬝ᵥ w := by
    rw [← mulVec_mulVec, dotProduct_mulVec, hwdef, ← mulVec_transpose]
  have hqpos : 0 < w ⬝ᵥ w := by
    have h0 : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)
    exact lt_of_le_of_ne h0 (Ne.symm (fun h => hw0 (dotProduct_self_eq_zero.mp h)))
  have hsq : 0 < Real.sqrt (w ⬝ᵥ w) := Real.sqrt_pos.2 hqpos
  refine ⟨?_, ?_, by rw [hq]; exact hsq⟩
  · unfold cutDirection
    rw [hq, ← hwdef, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc]
    rw [one_div_mul_one_div, Real.mul_self_sqrt hqpos.le]
    field_simp
  · unfold cutDirection
    rw [hq, ← hwdef, smul_smul, mul_one_div_cancel hsq.ne', one_smul]
end LG2021.Algorithm
end
end
/- LG2021AlgorithmShallow -/
section
noncomputable section
namespace LG2021.Algorithm
open Matrix MeasureTheory ModernConvex.EllipsoidMethod
end LG2021.Algorithm
end
end
/- LG2021AlgorithmVolume -/
section
/-!
Minimum-ellipsoid and protected-volume adapters. The source simplex supplies
the protected positive volume. The geometric contraction is the explicit
shallow-cut theorem.
-/
noncomputable section
namespace LG2021.Algorithm
open Matrix MeasureTheory Set ModernConvex.Ellipsoids
open LG2021.JohnHelpers
open scoped ENNReal
private theorem chosenOuterFrame_shallow_det {d : ℕ} (hd : 0 < d)
    {S : Set (Fin d → ℝ)} (hS : IsSolid S)
    (c : Fin d → ℝ) (B : Matrix (Fin d) (Fin d) ℝ) (hB : B.det ≠ 0)
    (p : Fin d → ℝ) (hp : p ⬝ᵥ p = 1) (hsub : S ⊆ shallowSlice c B p) :
    |(chosenOuterFrame S).1.det| ≤
      Real.exp (-1 / (8 * ((d : ℝ) + 1))) * |B.det| := by
  obtain ⟨B', c', hB', hcover, hdet, _⟩ :=
    LG2021.shallow_ellipsoid_cover hd c B hB p hp
  have hmin := (chosenOuterFrame_spec hS).2.2.2
    (ellipsoid B' c') ⟨B', c', hB', rfl⟩ (hsub.trans hcover)
  rw [Vol_ellipsoid, Vol_ellipsoid] at hmin
  have hminR := (ENNReal.ofReal_le_ofReal_iff (abs_nonneg B'.det)).mp hmin
  exact hminR.trans hdet
private theorem chosenOuterFrame_det_upper {d : ℕ} {S : Set (Fin d → ℝ)} (hS : IsSolid S)
    {c : Fin d → ℝ} {R : ℝ} (hR : 0 < R)
    (hsub : S ⊆ ellipsoid (R • (1 : Matrix (Fin d) (Fin d) ℝ)) c) :
    |(chosenOuterFrame S).1.det| ≤ R^d := by
  have hdet : (R • (1 : Matrix (Fin d) (Fin d) ℝ)).det ≠ 0 := by
    simp [det_smul, hR.ne']
  have hmin := (chosenOuterFrame_spec hS).2.2.2
    (ellipsoid (R • (1 : Matrix (Fin d) (Fin d) ℝ)) c)
    ⟨_, _, hdet, rfl⟩ hsub
  rw [Vol_ellipsoid, Vol_ellipsoid, det_smul, det_one, mul_one, Fintype.card_fin,
    abs_of_nonneg (pow_nonneg hR.le _)] at hmin
  exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg hR.le _)).mp hmin
private theorem ellipsoid_cut_subset_shallow {d : ℕ} (hd : 0 < d) (c : Fin d → ℝ)
    (B : Matrix (Fin d) (Fin d) ℝ) (hB : B.det ≠ 0)
    (a : Fin d → ℝ) (ha : a ≠ 0) (z : Fin d → ℝ)
    (hz : z ⬝ᵥ z ≤ (1 / (2 * (d : ℝ)))^2) :
    ellipsoid B c ∩ {x | a ⬝ᵥ x ≤ a ⬝ᵥ (c + B *ᵥ z)} ⊆
      shallowSlice c B (ModernConvex.EllipsoidMethod.cutDirection B a) := by
  obtain ⟨hp, hBa, hsq⟩ := normalized_cut_direction B hB a ha
  let p := ModernConvex.EllipsoidMethod.cutDirection B a
  have hznorm : p ⬝ᵥ z ≤ 1 / (2 * (d : ℝ)) := by
    have hc := scalar_unit_cauchy z p hp
    rw [dotProduct_comm z p] at hc
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hpos : 0 < 1 / (2 * (d : ℝ)) := by positivity
    nlinarith
  rintro x ⟨⟨u, hu, rfl⟩, hcut⟩
  refine ⟨u, hu, ?_, by rw [add_comm]⟩
  have he : ∀ v : Fin d → ℝ, a ⬝ᵥ (B *ᵥ v) =
      Real.sqrt (a ⬝ᵥ ((B * Bᵀ) *ᵥ a)) * (p ⬝ᵥ v) := by
    intro v
    rw [dotProduct_mulVec, ← mulVec_transpose, hBa, smul_dotProduct, smul_eq_mul]
  change a ⬝ᵥ (B *ᵥ u + c) ≤ a ⬝ᵥ (c + B *ᵥ z) at hcut
  simp only [dotProduct_add, he] at hcut
  have hpu : p ⬝ᵥ u ≤ p ⬝ᵥ z := by nlinarith
  exact hpu.trans hznorm
private theorem chosenOuterFrame_cut_contraction {d : ℕ} (hd : 0 < d)
    {S T : Set (Fin d → ℝ)} (hT : IsSolid T)
    (F : NativeFrame d) (hF : OuterFrameSpec S F)
    (a : Fin d → ℝ) (ha : a ≠ 0) (z : Fin d → ℝ)
    (hz : z ⬝ᵥ z ≤ (1 / (2 * (d : ℝ)))^2)
    (hsub : T ⊆ S ∩ {x | a ⬝ᵥ x ≤ a ⬝ᵥ (F.2 + F.1 *ᵥ z)}) :
    |(chosenOuterFrame T).1.det| ≤
      Real.exp (-1 / (8 * ((d : ℝ) + 1))) * |F.1.det| := by
  apply chosenOuterFrame_shallow_det hd hT F.2 F.1 hF.1
    (ModernConvex.EllipsoidMethod.cutDirection F.1 a) (normalized_cut_direction F.1 hF.1 a ha).1
  apply (hsub.trans ?_).trans (ellipsoid_cut_subset_shallow hd F.2 F.1 hF.1 a ha z hz)
  exact inter_subset_inter_left _ hF.2.2.1
private theorem native_unitBall_volume_le (d : ℕ) :
    volume (unitBall d) ≤ ENNReal.ofReal ((2 : ℝ)^d) := by
  have hsub : unitBall d ⊆ Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) := by
    intro x hx
    constructor
    · intro i
      exact (abs_le.mp (unitBall_coord hx i)).1
    · intro i
      exact (abs_le.mp (unitBall_coord hx i)).2
  have h : volume (unitBall d) ≤ volume (Icc (fun _ : Fin d => (-1 : ℝ)) (fun _ => (1 : ℝ))) :=
    measure_mono hsub
  norm_num [Real.volume_Icc_pi, ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)] at h ⊢
  exact h
private theorem chosenOuterFrame_det_lower_of_volume {d : ℕ} {S P : Set (Fin d → ℝ)}
    (hS : IsSolid S) {v : ℝ} (hvol : ENNReal.ofReal v ≤ volume P) (hsub : P ⊆ S) :
    v / (2 : ℝ)^d ≤ |(chosenOuterFrame S).1.det| := by
  have h := hvol.trans (measure_mono (hsub.trans (chosenOuterFrame_spec hS).2.2.1))
  rw [volume_ellipsoid] at h
  have hbound : ENNReal.ofReal v ≤ ENNReal.ofReal |(chosenOuterFrame S).1.det| *
      ENNReal.ofReal ((2 : ℝ)^d) := h.trans (by gcongr; exact native_unitBall_volume_le d)
  rw [← ENNReal.ofReal_mul (abs_nonneg _)] at hbound
  have hreal := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (abs_nonneg _) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _))).mp hbound
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2^d)).mpr hreal
private theorem convex_interior_nonempty_of_positive_volume {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
    {S : Set E} (hcv : Convex ℝ S) (hvol : 0 < volume S) : (interior S).Nonempty := by
  apply hcv.interior_nonempty_iff_affineSpan_eq_top.mpr
  by_contra hspan
  have hzero : volume S = 0 := measure_mono_null (subset_affineSpan ℝ S)
    (MeasureTheory.Measure.addHaar_affineSubspace volume (affineSpan ℝ S) hspan)
  rw [hzero] at hvol
  exact (lt_irrefl 0) hvol
private theorem codedBody_interior_of_preserved_simplex {d p k : ℕ} {K : Set (Space d)}
    (hcv : Convex ℝ K) (cuts : Fin p → CutCode d) (v : Fin k → Space d)
    (hvol : 0 < volume (convexHull ℝ (range v)))
    (hpreserve : ∀ i, v i ∈ codedBody K cuts) :
    (interior (codedBody K cuts)).Nonempty := by
  have hbodycv : Convex ℝ (codedBody K cuts) := convex_activeBody hcv _
  have hsub : convexHull ℝ (range v) ⊆ codedBody K cuts :=
    convexHull_min (by rintro _ ⟨i, rfl⟩; exact hpreserve i) hbodycv
  exact convex_interior_nonempty_of_positive_volume hbodycv (hvol.trans_le (measure_mono hsub))
end LG2021.Algorithm
end
end
/- LG2021AlgorithmSimplex -/
section
noncomputable section
namespace LG2021.Algorithm
open Matrix MeasureTheory Set
open scoped BigOperators Classical
private theorem sliceRadius_pos : 0 < sliceRadius := Real.sqrt_pos.mpr (by norm_num)
end LG2021.Algorithm
end
end
/- LG2021GaussianGeometryConvex -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
/-- The differential of a differentiable convex function is a supporting functional. -/
private theorem convex_supporting_fderiv {d : ℕ} {f : Space d → ℝ}
    (hc : ConvexOn ℝ Set.univ f) {x : Space d} {D : Space d →L[ℝ] ℝ}
    (hD : HasFDerivAt f D x) (y : Space d) : f x + D (y - x) ≤ f y := by
  let line : ℝ → Space d := fun t => x + t • (y - x)
  have hline : HasDerivAt line (y - x) 0 := by
    simpa [line] using (hasDerivAt_id (0 : ℝ)).smul_const (y - x) |>.const_add x
  have hder : HasDerivAt (fun t => f (line t)) (D (y - x)) 0 := by
    have hDx : HasFDerivAt f D (line 0) := by simpa [line] using hD
    exact hDx.comp_hasDerivAt 0 hline
  have hconv : ConvexOn ℝ Set.univ (fun t : ℝ => f (line t)) := by
    refine ⟨convex_univ, ?_⟩
    intro a ha b hb s t hs ht hst
    have heq : s • line a + t • line b = line (s * a + t * b) := by
      dsimp [line]
      calc
        _ = (s + t) • x + (s * a + t * b) • (y - x) := by module
        _ = _ := by rw [hst, one_smul]
    simpa only [smul_eq_mul, heq] using hc.2 (Set.mem_univ (line a))
      (Set.mem_univ (line b)) hs ht hst
  have h := hconv.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
    (by norm_num : (0 : ℝ) < 1) hder
  simp [slope_def_field, line] at h
  simp only [map_sub]
  linarith
end LG2021
end
end
/- LG2021AlgorithmPreservation -/
section
/-! The stopping test and its actual confidence estimates preserve every
near-minimizing point. The strict margin also justifies inward rational rounding. -/
noncomputable section
namespace LG2021.Algorithm
private theorem winner_lowerBound_le_true {u : ℕ} (cfg : OracleConfig) (m : ℕ)
    (sums : Fin u → ℝ) {s : Fin u} {θ : ℝ}
    (hw : winner cfg m sums = some s)
    (he : |scalarEstimate m sums s - θ| ≤ confidenceRadius cfg u m) :
    lowerBound cfg m sums s ≤ θ := by
  have hp := winner_positive cfg m sums hw
  have h := lowerBound_le_true cfg m sums s θ he
  rcases le_total 0 θ with hθ | hθ
  · simpa only [max_eq_right hθ] using h
  · rw [max_eq_left hθ] at h
    exact (not_lt_of_ge h hp).elim
private theorem winner_gradient_error_bound {d u : ℕ} (cfg : OracleConfig) (m : ℕ)
    (sums : Fin u → ℝ) {s : Fin u} {θ : ℝ} {v g x z : Space d}
    (hm : 0 < m) (hc : 0 < cfg.momentConstant) (hr : 0 < cfg.radius)
    (hC : 0 < cfg.concentrationConstant) (hH : 0 ≤ confidenceLog cfg u)
    (hw : winner cfg m sums = some s)
    (hscalar : |scalarEstimate m sums s - θ| ≤ confidenceRadius cfg u m)
    (hgradient : inner ℝ (v - g) (x - z) ≤ 2 * cfg.radius *
      (cfg.momentConstant * Real.sqrt (confidenceLog cfg u /
        (cfg.concentrationConstant * (m : ℝ))) + 1 / (8 * cfg.radius * cfg.horizon))) :
    inner ℝ (v - g) (x - z) ≤ 1 / (4 * (cfg.horizon : ℝ)) + θ / 2 := by
  have hel := winner_some_eligible cfg m sums hw
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hb : (8 * (cfg.momentConstant * cfg.radius / 2) /
      lowerBound cfg m sums s)^2 * confidenceLog cfg u / cfg.concentrationConstant ≤ m := by
    convert hel.2 using 1 <;> ring
  have h := scaled_sqrt_le_of_sample_bound (by positivity :
    0 < cfg.momentConstant * cfg.radius / 2) hel.1 hH hC hmR hb
  have hθ := winner_lowerBound_le_true cfg m sums hw hscalar
  have hid : 2 * cfg.radius * (1 / (8 * cfg.radius * cfg.horizon)) =
      1 / (4 * (cfg.horizon : ℝ)) := by field_simp; ring
  rw [mul_add, hid] at hgradient
  nlinarith
private theorem surrogate_protected_inner {d : ℕ} {f : Space d → ℝ} {J : NNReal}
    (hf : LipschitzWith J f) (hc : ConvexOn ℝ Set.univ f)
    {lambda : ℝ} (hlambda : 0 < lambda) (hlambda1 : lambda < 1) (z x : Space d) {δ : ℝ}
    (hx : f x ≤ f 0 + δ) :
    inner ℝ (gradient (surrogate lambda f) z) (x - z) ≤
      δ - (surrogate lambda f z - f 0) := by
  have h := convex_supporting_fderiv (surrogate_convex hf hc hlambda)
    (surrogate_hasFDerivAt hf hlambda.ne' hlambda1 z).differentiableAt.hasFDerivAt x
  have hle := surrogate_le hf hc hlambda hlambda1.le x
  have heq : inner ℝ (gradient (surrogate lambda f) z) (x - z) =
      fderiv ℝ (surrogate lambda f) z (x - z) := by rw [← toDual_gradient]; rfl
  rw [heq]
  linarith
private theorem winner_protected_margin {d u : ℕ} (cfg : OracleConfig) (m : ℕ)
    (sums : Fin u → ℝ) {s : Fin u} {f : Space d → ℝ} {J : NNReal}
    (hf : LipschitzWith J f) (hcv : ConvexOn ℝ Set.univ f)
    (hlambda : 0 < cfg.lambda) (hlambda1 : cfg.lambda < 1)
    (hm : 1 ≤ m) (hmn : m ≤ cfg.horizon)
    (hc : 1 ≤ cfg.momentConstant) (hr : 1 ≤ cfg.radius)
    (hC : 0 < cfg.concentrationConstant) (hC1 : cfg.concentrationConstant ≤ 1)
    (hH : 1 ≤ confidenceLog cfg u)
    (hw : winner cfg m sums = some s) (z v x : Space d) {δ : ℝ}
    (hδ : δ ≤ 1 / (4 * (cfg.horizon : ℝ))) (hx : f x ≤ f 0 + δ)
    (hscalar : |scalarEstimate m sums s - (surrogate cfg.lambda f z - f 0)| ≤
      confidenceRadius cfg u m)
    (hgradient : inner ℝ (v - gradient (surrogate cfg.lambda f) z) (x - z) ≤
      2 * cfg.radius * (cfg.momentConstant * Real.sqrt (confidenceLog cfg u /
        (cfg.concentrationConstant * (m : ℝ))) + 1 / (8 * cfg.radius * cfg.horizon))) :
    inner ℝ v (x - z) ≤ -lowerBound cfg m sums s / 4 := by
  have hel := winner_some_eligible cfg m sums hw
  have hn : (0 : ℝ) < cfg.horizon := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < m) hmn)
  have hgap := stopping_gap_margin hm hmn hel.1 hc hr hH hC hC1 hel.2
  apply oracle_strict_margin hn hel.1 (winner_lowerBound_le_true cfg m sums hw hscalar)
    (le_trans (by apply div_le_div_of_nonneg_right (by norm_num) hn.le) hgap) hδ
    (surrogate_protected_inner hf hcv hlambda hlambda1 z x hx)
  exact winner_gradient_error_bound cfg m sums (by omega) (by linarith) (by linarith)
    hC (by linarith) hw hscalar hgradient
private theorem frameApply_frameUnapply {d : ℕ} (F : Frame d) (hF : F.1.det ≠ 0)
    (w : Space d) : frameApply F (frameUnapply F w) = w := by
  have he : matrixAction F.1 (matrixAction F.1⁻¹ (w - F.2)) = w - F.2 := by
    simp only [matrixAction, ContinuousLinearEquiv.apply_symm_apply,
      Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv F.1 (isUnit_iff_ne_zero.mpr hF),
      Matrix.one_mulVec, ContinuousLinearEquiv.symm_apply_apply]
  exact (congrArg (fun x => x + F.2) he).trans (sub_add_cancel w F.2)
private theorem frame_loss_convex {d : ℕ} (F : Frame d) {f : Space d → ℝ}
    (hf : ConvexOn ℝ Set.univ f) :
    ConvexOn ℝ Set.univ (fun x => f (frameApply F x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have he : frameApply F (a • x + b • y) = a • frameApply F x + b • frameApply F y := by
    simp only [frameApply, matrixAction_add, matrixAction_smul]
    calc
      _ = a • matrixAction F.1 x + b • matrixAction F.1 y + (a + b) • F.2 := by rw [hab, one_smul]
      _ = _ := by module
  change f (frameApply F (a • x + b • y)) ≤ _
  rw [he]
  exact hf.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
private theorem winner_original_margin {d u : ℕ} (cfg : OracleConfig) (m : ℕ)
    (sums : Fin u → ℝ) {s : Fin u} (F : Frame d) (hF : F.1.det ≠ 0)
    {f : Space d → ℝ} {J : NNReal}
    (hf : LipschitzWith J (fun x => f (frameApply F x)))
    (hcv : ConvexOn ℝ Set.univ f)
    (hlambda : 0 < cfg.lambda) (hlambda1 : cfg.lambda < 1)
    (hm : 1 ≤ m) (hmn : m ≤ cfg.horizon)
    (hc : 1 ≤ cfg.momentConstant) (hr : 1 ≤ cfg.radius)
    (hC : 0 < cfg.concentrationConstant) (hC1 : cfg.concentrationConstant ≤ 1)
    (hH : 1 ≤ confidenceLog cfg u) (hw : winner cfg m sums = some s)
    (z v w : Space d) {δ fmin : ℝ}
    (hδ : δ ≤ 1 / (4 * (cfg.horizon : ℝ)))
    (hcenter : fmin ≤ f (frameApply F 0)) (hwnear : f w ≤ fmin + δ)
    (hscalar : |scalarEstimate m sums s -
      (surrogate cfg.lambda (fun x => f (frameApply F x)) z - f (frameApply F 0))| ≤
        confidenceRadius cfg u m)
    (hgradient : inner ℝ
      (v - gradient (surrogate cfg.lambda (fun x => f (frameApply F x))) z)
      (frameUnapply F w - z) ≤
      2 * cfg.radius * (cfg.momentConstant * Real.sqrt (confidenceLog cfg u /
        (cfg.concentrationConstant * (m : ℝ))) + 1 / (8 * cfg.radius * cfg.horizon))) :
    cutValue (cutFromEstimate F z v) w ≤ -lowerBound cfg m sums s / 4 := by
  rw [cutValue, cutFromEstimate_value F hF]
  apply winner_protected_margin cfg m sums hf (frame_loss_convex F hcv)
    hlambda hlambda1 hm hmn hc hr hC hC1 hH hw z v (frameUnapply F w) hδ _ hscalar hgradient
  rw [frameApply_frameUnapply F hF]
  linarith
end LG2021.Algorithm
end
end
/- LG2021AlgorithmStageVolume -/
section
noncomputable section
namespace LG2021.Algorithm
open Set MeasureTheory Matrix ModernConvex.Ellipsoids
open scoped Classical
private theorem native_inner {d : ℕ} (x y : Space d) :
    (EuclideanSpace.equiv (Fin d) ℝ x) ⬝ᵥ (EuclideanSpace.equiv (Fin d) ℝ y) =
      inner ℝ x y := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.equiv,
    PiLp.coe_continuousLinearEquiv, star_trivial, dotProduct_comm]
private theorem native_image_volume {d : ℕ} (S : Set (Space d)) :
    volume ((EuclideanSpace.equiv (Fin d) ℝ) '' S) = volume S := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  have hp : MeasurePreserving e.symm (volume : Measure (Fin d → ℝ)) volume :=
    PiLp.volume_preserving_toLp (Fin d)
  have h := hp.measure_preimage_emb e.symm.toHomeomorph.measurableEmbedding S
  have he : e.symm ⁻¹' S = e '' S := by
    ext x
    constructor
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa only [Set.mem_preimage, e.symm_apply_apply] using hy
  rwa [he] at h
private theorem canonical_cut_contraction {d p q : ℕ} (hd : 0 < d)
    {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    {r : ℝ} (hr : 0 < r) (cuts : Fin p → CutCode d) (nextCuts : Fin q → CutCode d)
    (hi : (interior (codedBody K cuts)).Nonempty)
    (hi' : (interior (codedBody K nextCuts)).Nonempty)
    (z v : Space d) (hz : ‖z‖ ≤ r / (2 * (d : ℝ)))
    (ha : (cutFromEstimate (canonicalOuterFrame K r cuts) z v).1 ≠ 0)
    (hsub : codedBody K nextCuts ⊆ codedBody K cuts ∩
      cutSet (cutFromEstimate (canonicalOuterFrame K r cuts) z v)) :
    |(chosenOuterFrame (nativeCodedBody K nextCuts)).1.det| ≤
      Real.exp (-1 / (8 * ((d : ℝ) + 1))) *
        |(chosenOuterFrame (nativeCodedBody K cuts)).1.det| := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  let F := chosenOuterFrame (nativeCodedBody K cuts)
  let a := (cutFromEstimate (canonicalOuterFrame K r cuts) z v).1
  have hane : e a ≠ 0 := by
    intro he
    apply ha
    exact e.injective (by simpa using he)
  have hz' : (e (r⁻¹ • z)) ⬝ᵥ (e (r⁻¹ • z)) ≤ (1 / (2 * (d : ℝ)))^2 := by
    rw [native_inner, real_inner_self_eq_norm_sq]
    have hn : ‖r⁻¹ • z‖ ≤ 1 / (2 * (d : ℝ)) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      have h := mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hr.le)
      calc
        r⁻¹ * ‖z‖ ≤ r⁻¹ * (r / (2 * (d : ℝ))) := h
        _ = _ := by field_simp
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hn
  apply chosenOuterFrame_cut_contraction hd (nativeCodedBody_solid hK hcv nextCuts hi')
    F (chosenOuterFrame_spec (nativeCodedBody_solid hK hcv cuts hi)) (e a) hane (e (r⁻¹ • z)) hz'
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨⟨w, (hsub hw).1, rfl⟩, ?_⟩
  have he : e (frameApply (canonicalOuterFrame K r cuts) z) =
      F.2 + F.1 *ᵥ e (r⁻¹ • z) := by
    change e (e.symm ((r⁻¹ • F.1) *ᵥ e z) + e.symm F.2) = _
    rw [map_add, e.apply_symm_apply, e.apply_symm_apply]
    simp only [map_smul, smul_mulVec, mulVec_smul, add_comm]
  change e a ⬝ᵥ e w ≤ e a ⬝ᵥ (F.2 + F.1 *ᵥ e (r⁻¹ • z))
  rw [← he, native_inner, native_inner]
  exact (hsub hw).2
private theorem trace_preserves_simplex {d u N : ℕ} (cfg : OracleConfig)
    {K : Set (Space d)} (hcv : Convex ℝ K) {R : ℝ} (hR : 0 ≤ R)
    (hbounded : ∀ x ∈ K, ‖x‖ ≤ R) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) (v : Fin (d + 1) → Space d)
    (hv : ∀ i, v i ∈ K) (hvol : 0 < volume (convexHull ℝ (range v)))
    (hmargin : ∀ p < N,
      (interior (codedBody K (traceState cfg K R seed ys p).1)).Nonempty →
      (∀ i, v i ∈ codedBody K (traceState cfg K R seed ys p).1) →
      ∀ s, traceWinner cfg K R seed ys p = some s →
      ∀ i, cutValue (traceCut cfg K R seed ys p s) (v i) ≤
        -traceCertified cfg K R seed ys p s / 4) :
    ∀ p ≤ N, (∀ i, v i ∈ codedBody K (traceState cfg K R seed ys p).1) ∧
      (interior (codedBody K (traceState cfg K R seed ys p).1)).Nonempty := by
  intro p hp
  induction p with
  | zero =>
      have hvertices : ∀ i, v i ∈ codedBody K (traceState cfg K R seed ys 0).1 := by
        intro i
        exact ⟨hv i, by simp [traceState, runState, initialState]⟩
      exact ⟨hvertices, codedBody_interior_of_preserved_simplex hcv _ v hvol hvertices⟩
  | succ p ih =>
      have hprev := ih (by omega)
      have hs : range v ⊆ codedBody K (traceState cfg K R seed ys p).1 := by
        rintro _ ⟨i, rfl⟩
        exact hprev.1 i
      have hn := step_preserves_set cfg K (range v) hR hbounded
        (canonicalOuterFrame K cfg.radius) (traceState cfg K R seed ys p) hs
        (seedCandidates seed (p + 1)) (seedGaussian seed p) (ys p).1 (ys p).2
        (by
          intro s hw w hwv
          rcases hwv with ⟨i, rfl⟩
          exact hmargin p (by omega) hprev.2 hprev.1 s hw i)
      have hvertices : ∀ i, v i ∈ codedBody K (traceState cfg K R seed ys (p + 1)).1 :=
        fun i => hn (mem_range_self i)
      exact ⟨hvertices, codedBody_interior_of_preserved_simplex hcv _ v hvol hvertices⟩
private theorem trace_candidates_bound {d u N : ℕ} (cfg : OracleConfig) (K : Set (Space d))
    (R : ℝ) (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) {a : ℝ}
    (hseed : ∀ p ≤ N, ∀ s, ‖seedCandidates seed p s‖ ≤ a) :
    ∀ p ≤ N, ∀ s, ‖(traceState cfg K R seed ys p).2.2.1 s‖ ≤ a := by
  intro p hp
  induction p with
  | zero => exact hseed 0 (Nat.zero_le _)
  | succ p ih =>
      rw [traceState_succ]
      cases hw : traceWinner cfg K R seed ys p with
      | none =>
          rw [step_continues cfg R _ _ _ _ _ _ hw]
          exact ih (by omega)
      | some s =>
          rw [step_restarts cfg R _ _ _ _ _ _ s hw]
          exact hseed (p + 1) hp
private theorem traceDet_succ_of_none {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d))
    (R : ℝ) (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (p : ℕ)
    (hw : traceWinner cfg K R seed ys p = none) :
    traceDet cfg K R seed ys (p + 1) = traceDet cfg K R seed ys p := by
  unfold traceDet
  rw [traceState_succ, step_continues cfg R _ _ _ _ _ _ hw]
  change |(chosenOuterFrame (nativeCodedBody K (Fin.snoc _ 0))).1.det| = _
  unfold nativeCodedBody
  rw [codedBody_snoc_zero]
private theorem traceDet_succ_of_some {d u : ℕ} (hd : 0 < d) (cfg : OracleConfig)
    {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    {R : ℝ} (hR : 0 ≤ R) (hbounded : ∀ x ∈ K, ‖x‖ ≤ R)
    (hr : 0 < cfg.radius) (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ)
    (p : ℕ) {s : Fin u} (hw : traceWinner cfg K R seed ys p = some s)
    (hi : (interior (codedBody K (traceState cfg K R seed ys p).1)).Nonempty)
    (hi' : (interior (codedBody K (traceState cfg K R seed ys (p + 1)).1)).Nonempty)
    (hz : ‖(traceState cfg K R seed ys p).2.2.1 s‖ ≤ cfg.radius / (2 * (d : ℝ)))
    (w : Space d) (hmargin : cutValue (traceCut cfg K R seed ys p s) w ≤
      -traceCertified cfg K R seed ys p s / 4) :
    traceDet cfg K R seed ys (p + 1) ≤ Real.exp (-1 / (8 * ((d : ℝ) + 1))) *
      traceDet cfg K R seed ys p := by
  have hframe := runState_frame cfg K R seed p (fun i => ys i)
  change (traceState cfg K R seed ys p).2.1 = _ at hframe
  have hnormal := cutFromEstimate_normal_ne_zero _ _ _ w
    (winner_positive cfg _ _ hw) hmargin
  have hsub := restart_body_subset_raw_cut cfg K hR hbounded
    (canonicalOuterFrame K cfg.radius) (traceState cfg K R seed ys p)
    (seedCandidates seed (p + 1)) (seedGaussian seed p) (ys p).1 (ys p).2 s hw
  rw [hframe] at hnormal hsub
  exact canonical_cut_contraction hd hK hcv hr _ _ hi hi' _ _ hz hnormal hsub
private theorem traceDet_initial_upper {d u : ℕ} (cfg : OracleConfig)
    {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    {R : ℝ} (hR : 0 < R) (hbounded : ∀ x ∈ K, ‖x‖ ≤ R)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ)
    (hi : (interior (codedBody K (traceState cfg K R seed ys 0).1)).Nonempty) :
    traceDet cfg K R seed ys 0 ≤ R^d := by
  apply chosenOuterFrame_det_upper
    (nativeCodedBody_solid hK hcv (traceState cfg K R seed ys 0).1 hi) (c := 0) hR
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨w, hw, he⟩ := (ball_scaled_unit_parameterization hR x).mp
    (by simpa using hbounded x hx.1)
  refine ⟨w, hw, ?_⟩
  rw [he]
  simp only [smul_mulVec, one_mulVec, add_zero, map_smul,
    ContinuousLinearEquiv.apply_symm_apply]
private theorem traceStage_bound_of_simplex {d u N : ℕ} (hd : 0 < d) (cfg : OracleConfig)
    {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    {R : ℝ} (hR : 0 < R) (hbounded : ∀ x ∈ K, ‖x‖ ≤ R) (hr : 0 < cfg.radius)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ)
    (v : Fin (d + 1) → Space d) (hv : ∀ i, v i ∈ K)
    {V : ℝ} (hV : 0 < V) (hvol : ENNReal.ofReal V ≤ volume (convexHull ℝ (range v)))
    (hseed : ∀ p ≤ N, ∀ s, ‖seedCandidates seed p s‖ ≤ cfg.radius / (2 * (d : ℝ)))
    (hmargin : ∀ p < N,
      (interior (codedBody K (traceState cfg K R seed ys p).1)).Nonempty →
      (∀ i, v i ∈ codedBody K (traceState cfg K R seed ys p).1) →
      ∀ s, traceWinner cfg K R seed ys p = some s →
      ∀ i, cutValue (traceCut cfg K R seed ys p s) (v i) ≤
        -traceCertified cfg K R seed ys p s / 4) :
    (traceStage cfg K R seed ys N : ℝ) ≤
      8 * ((d : ℝ) + 1) * ((d : ℝ) * Real.log R - Real.log (V / (2 : ℝ)^d)) := by
  have hvpos : 0 < volume (convexHull ℝ (range v)) :=
    (ENNReal.ofReal_pos.mpr hV).trans_le hvol
  have hp := trace_preserves_simplex cfg hcv hR.le hbounded seed ys v hv hvpos hmargin
  have hz := trace_candidates_bound cfg K R seed ys hseed
  let q := Real.exp (-1 / (8 * ((d : ℝ) + 1)))
  have hq : 0 < q := Real.exp_pos _
  have hseq : ∀ p ≤ N, traceDet cfg K R seed ys p ≤ q^(traceStage cfg K R seed ys p) * R^d := by
    intro p hpn
    induction p with
    | zero =>
        simpa [traceStage] using traceDet_initial_upper cfg hK hcv hR hbounded seed ys (hp 0 (Nat.zero_le _)).2
    | succ p ih =>
        have ih' := ih (by omega)
        cases hw : traceWinner cfg K R seed ys p with
        | none =>
            rw [traceDet_succ_of_none cfg K R seed ys p hw]
            simpa only [traceStage, hw, ↓reduceIte, Nat.add_zero] using ih'
        | some s =>
            have hstep := traceDet_succ_of_some hd cfg hK hcv hR.le hbounded hr seed ys p hw
              (hp p (by omega)).2 (hp (p + 1) hpn).2 (hz p (by omega) s) (v 0)
              (hmargin p (by omega) (hp p (by omega)).2 (hp p (by omega)).1 s hw 0)
            calc
              _ ≤ q * traceDet cfg K R seed ys p := hstep
              _ ≤ q * (q^(traceStage cfg K R seed ys p) * R^d) :=
                mul_le_mul_of_nonneg_left ih' hq.le
              _ = _ := by simp only [traceStage, hw, Option.some_ne_none, ↓reduceIte, pow_succ]; ring
  have hsub : convexHull ℝ (range v) ⊆ codedBody K (traceState cfg K R seed ys N).1 :=
    convexHull_min (by rintro _ ⟨i, rfl⟩; exact (hp N le_rfl).1 i) (convex_activeBody hcv _)
  have hnatvol : ENNReal.ofReal V ≤ volume ((EuclideanSpace.equiv (Fin d) ℝ) ''
      convexHull ℝ (range v)) := by rwa [native_image_volume]
  have hlower := chosenOuterFrame_det_lower_of_volume
    (nativeCodedBody_solid hK hcv _ (hp N le_rfl).2) hnatvol (Set.image_mono hsub)
  have hpositive : 0 < V / (2 : ℝ)^d := by positivity
  have hlog := Real.log_le_log hpositive (hlower.trans (hseq N le_rfl))
  rw [Real.log_mul (pow_pos hq _).ne' (pow_pos hR _).ne', Real.log_pow, Real.log_pow] at hlog
  dsimp [q] at hlog
  rw [Real.log_exp] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 8 * ((d : ℝ) + 1))
  field_simp at hmul
  nlinarith
end LG2021.Algorithm
end
end
/- LG2021CandidateSampling -/
section
noncomputable section
namespace LG2021.Algorithm
open MeasureTheory
private theorem candidateCount_pos {n : ℕ} (hn : 1 ≤ n) : 0 < candidateCount n := by
  apply Nat.one_le_ceil_iff.2
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 1 < 3 * (n : ℝ) ^ 2 := by nlinarith
  exact mul_pos (by norm_num) (Real.log_pos hp)
end LG2021.Algorithm
end
end
/- LG2021RateAlgebra -/
section
noncomputable section
namespace LG2021.Algorithm
open Concentration
end LG2021.Algorithm
end
end
/- LG2021AlgorithmStageRate -/
section
noncomputable section
namespace LG2021.Algorithm
open Set MeasureTheory Concentration
private theorem sourceSimplexVolume_pos (d : ℕ) {D : ℝ} (hD : 0 < D) (L : ℝ) :
    0 < sourceSimplexVolume d D L := by
  unfold sourceSimplexVolume
  exact div_pos (mul_pos (pow_pos (div_pos (Real.exp_pos _) hD) _)
    (pow_pos sliceRadius_pos _)) (mul_pos (by norm_num) (by exact_mod_cast d.factorial_pos))
private theorem parameter_delta_le_horizon (d : ℕ) {n : ℕ} (hn : 1 ≤ n) {D : ℝ} (hD : 0 ≤ D) :
    Real.exp (-parameterLog d D n) ≤ 1 / (4 * (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hprod : 1 ≤ ((d : ℝ) + 1) * (D + 1) := by nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hbase : 4 * (n : ℝ) ≤ parameterBase d D n := by
    have h := mul_le_mul_of_nonneg_right hprod (show 0 ≤ 10^6 * ((n : ℝ) + 1) by positivity)
    unfold parameterBase
    nlinarith
  have hA := (parameterBase_bounds d n hD).1
  have hlogA : 0 ≤ Real.log (parameterBase d D n) := Real.log_nonneg (by linarith)
  have hlog := Real.log_le_log (show 0 < 4 * (n : ℝ) by positivity) hbase
  have hL : Real.log (4 * (n : ℝ)) ≤ parameterLog d D n := by
    unfold parameterLog
    linarith
  calc
    _ ≤ Real.exp (-Real.log (4 * (n : ℝ))) := Real.exp_le_exp.mpr (neg_le_neg hL)
    _ = _ := by rw [Real.exp_neg, Real.exp_log (by positivity), one_div]
end LG2021.Algorithm
end
end
/- LG2021AlgorithmGoodHistory -/
section
noncomputable section
namespace LG2021.Algorithm
open Set MeasureTheory
private theorem traceSampleCount_le {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (p : ℕ) :
    traceSampleCount cfg K R seed ys p ≤ p + 1 := by
  unfold traceSampleCount
  rw [traceState_age_eq_card]
  exact Nat.add_le_add_right ((Finset.card_filter_le _ _).trans_eq (Finset.card_range p)) 1
private theorem trace_margin_of_confidence {d u N : ℕ} (hd : 0 < d) (cfg : OracleConfig)
    {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K) (R : ℝ)
    {D δ fmin : ℝ} (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ)
    (v : Fin (d + 1) → Space d) (f : Space d → ℝ)
    (hf : LipschitzWith 1 f) (hfc : ConvexOn ℝ Set.univ f)
    (hmin : ∀ x ∈ K, fmin ≤ f x) (hnear : ∀ i, f (v i) ≤ fmin + δ)
    (hN : N ≤ cfg.horizon) (hdelta : δ ≤ 1 / (4 * (cfg.horizon : ℝ)))
    (hlambda : 0 < cfg.lambda) (hlambda1 : cfg.lambda < 1)
    (hc : 1 ≤ cfg.momentConstant) (hr : 1 ≤ cfg.radius)
    (hC : 0 < cfg.concentrationConstant) (hC1 : cfg.concentrationConstant ≤ 1)
    (hH : 1 ≤ confidenceLog cfg u)
    (hscalar : ∀ p < N,
      (interior (codedBody K (traceState cfg K R seed ys p).1)).Nonempty →
      ∀ s, |traceScalar cfg K R seed ys p s - traceGap cfg K R seed ys f p s| ≤
        confidenceRadius cfg u (traceSampleCount cfg K R seed ys p))
    (hgradient : ∀ p < N,
      (interior (codedBody K (traceState cfg K R seed ys p).1)).Nonempty →
      (∀ i, v i ∈ codedBody K (traceState cfg K R seed ys p).1) →
      ∀ s, traceWinner cfg K R seed ys p = some s →
      ∀ i, traceGradientDeviation cfg K R seed ys f p s (v i) ≤
        2 * cfg.radius * (cfg.momentConstant * Real.sqrt (confidenceLog cfg u /
          (cfg.concentrationConstant * (traceSampleCount cfg K R seed ys p : ℝ))) +
            1 / (8 * cfg.radius * cfg.horizon))) :
    ∀ p < N, (interior (codedBody K (traceState cfg K R seed ys p).1)).Nonempty →
      (∀ i, v i ∈ codedBody K (traceState cfg K R seed ys p).1) →
      ∀ s, traceWinner cfg K R seed ys p = some s →
      ∀ i, cutValue (traceCut cfg K R seed ys p s) (v i) ≤
        -traceCertified cfg K R seed ys p s / 4 := by
  intro p hp hi hret s hw i
  have hrpos : 0 < cfg.radius := by linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hframe := runState_frame cfg K R seed p (fun i => ys i)
  change (traceState cfg K R seed ys p).2.1 =
    canonicalOuterFrame K cfg.radius (traceState cfg K R seed ys p).1 at hframe
  have hdet := canonicalOuterFrame_det_ne_zero hK hcv hrpos _ hi
  have hLip := canonical_loss_lipschitz hd hK hcv hrpos hdiam _ hi f hf
  have hinner := canonicalOuterFrame_inner_ball hd hK hcv hrpos _ hi
  have hcenter : fmin ≤ f (frameApply (traceState cfg K R seed ys p).2.1 0) := by
    apply hmin
    rw [hframe]
    exact (hinner ⟨0, by simpa using (div_pos hrpos hdR).le, rfl⟩).1
  rw [← hframe] at hdet hLip
  have hm : traceSampleCount cfg K R seed ys p ≤ cfg.horizon :=
    (traceSampleCount_le cfg K R seed ys p).trans (by omega)
  exact winner_original_margin cfg (traceSampleCount cfg K R seed ys p) _
    (traceState cfg K R seed ys p).2.1 hdet hLip hfc hlambda hlambda1
    (by unfold traceSampleCount; omega) hm hc hr hC hC1 hH hw _ _ (v i)
    hdelta hcenter (hnear i) (hscalar p hp hi s) (hgradient p hp hi hret s hw i)
end LG2021.Algorithm
end
end
/- LG2021ConcentrationStageBuffers -/
section
noncomputable section
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR
end LG2021.Concentration
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR
end LG2021.Concentration
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR
end LG2021.Concentration
end
end
/- LG2021GuardedRegret -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory Set
open scoped Classical
namespace Algorithm
private theorem convexOn_loss_frame {d : ℕ} {L : Space d → ℝ}
    (hL : ConvexOn ℝ univ L) (F : Frame d) :
    ConvexOn ℝ univ (fun x => L (frameApply F x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have he : frameApply F (a • x + b • y) = a • frameApply F x + b • frameApply F y := by
    simp only [frameApply, matrixAction_add, matrixAction_smul]
    have hz : a • F.2 + b • F.2 = F.2 := by rw [← add_smul, hab, one_smul]
    simp only [smul_add]
    calc
      _ = a • matrixAction F.1 x + b • matrixAction F.1 y + (a • F.2 + b • F.2) :=
        congrArg (fun v => a • matrixAction F.1 x + b • matrixAction F.1 y + v) hz.symm
      _ = _ := by abel
  change L (frameApply F (a • x + b • y)) ≤
    a • L (frameApply F x) + b • L (frameApply F y)
  rw [he]
  exact hL.2 (mem_univ _) (mem_univ _) ha hb hab
end Algorithm
end LG2021
end
end
/- LG2021PairRegret -/
section
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped Classical
end LG2021.Concentration
end
end
/- LG2021AlgorithmParameters -/
section
noncomputable section
namespace LG2021.Algorithm
open Concentration
private theorem oracleConfig_bounds {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    {D : ℝ} (hD : 0 ≤ D) :
    1 ≤ (oracleConfig d D n).radius ∧
    0 < (oracleConfig d D n).lambda ∧ (oracleConfig d D n).lambda ≤ 1 / 2 ∧
    1 ≤ (oracleConfig d D n).momentConstant ∧
    0 < (oracleConfig d D n).concentrationConstant ∧
    (oracleConfig d D n).concentrationConstant ≤ 1 ∧
    1 ≤ confidenceLog (oracleConfig d D n) (candidateCount n) := by
  have hL := (parameterLog_bounds d n hD).1
  have hr := (paperRadius_bounds hd hL).1
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hl := paperLambda_bounds hd hL
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hu : (1 : ℝ) ≤ candidateCount n := by exact_mod_cast candidateCount_pos (by omega : 1 ≤ n)
  refine ⟨?_, hl.1, hl.2.1, ?_, oracleConcentrationConstant_pos, ?_, ?_⟩
  · change 1 ≤ paperRadius d (parameterLog d D n)
    nlinarith
  · norm_num [oracleConfig, oracleMomentConstant]
  · norm_num [oracleConfig, oracleConcentrationConstant]
  · unfold confidenceLog oracleConfig
    apply (Real.le_log_iff_exp_le (by positivity)).2
    have he := Real.exp_one_lt_three
    have hpow : (8 : ℝ) ≤ (n : ℝ) ^ 3 := by
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hnR 3
      norm_num at hp
      exact hp
    nlinarith [mul_le_mul_of_nonneg_left hu (show 0 ≤ (n : ℝ) ^ 3 by positivity)]
end LG2021.Algorithm
end
end
/- LG2021ConcentrationActualBias -/
section
noncomputable section
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped Classical
end LG2021.Concentration
end
end
/- LG2021ConcentrationStageBias -/
section
noncomputable section
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped Classical
end LG2021.Concentration
end
end
/- LG2021ConcentrationStageEvents -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
end LG2021.Concentration
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
end LG2021.Concentration
end
end
/- LG2021StageStarts -/
section
noncomputable section
namespace LG2021.Algorithm
open scoped Classical
end LG2021.Algorithm
end
end
/- LG2021ConcentrationActualConfidence -/
section
noncomputable section
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory
end LG2021.Concentration
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
end
/- LG2021ConfidencePrefix -/
section
noncomputable section
namespace LG2021.Algorithm
end LG2021.Algorithm
end
end
/- LG2021WinnerSamples -/
section
noncomputable section
namespace LG2021.Algorithm
end LG2021.Algorithm
end
end
/- LG2021ConcentrationGoodHistory -/
section
noncomputable section
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory
end LG2021.Concentration
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory
end LG2021.Concentration
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
end
/- LG2021ConcentrationConfidenceEvent -/
section
noncomputable section
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
end
/- LG2021ConcentrationCandidateCoordinates -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal
end LG2021.Concentration
end
end
/- LG2021CurrentConfidence -/
section
noncomputable section
namespace LG2021.Algorithm
set_option maxHeartbeats 1000000
private theorem trace_candidate_gap_eq_of_same_stage {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) (f : Space d → ℝ) (s : Fin u) {p q : ℕ}
    (hstage : traceStage cfg K R seed ys p = traceStage cfg K R seed ys q) :
    traceGap cfg K R seed ys f p s = traceGap cfg K R seed ys f q s := by
  have hcore := traceCore_eq_of_same_stage cfg K R seed ys hstage
  have hframe : (traceState cfg K R seed ys p).2.1 = (traceState cfg K R seed ys q).2.1 :=
    congrArg (fun z : Frame d × (Fin u → Space d) => z.1) hcore
  have hcand : (traceState cfg K R seed ys p).2.2.1 = (traceState cfg K R seed ys q).2.2.1 :=
    congrArg (fun z : Frame d × (Fin u → Space d) => z.2) hcore
  unfold traceGap traceLocalLoss
  rw [hframe, hcand]
private theorem stored_scalar_confidence_of_updated {d u N : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) (f : Space d → ℝ)
    (hscalar : ∀ q < N, ∀ s,
      |traceScalar cfg K R seed ys q s - traceGap cfg K R seed ys f q s| ≤
        confidenceRadius cfg u (traceSampleCount cfg K R seed ys q))
    {p : ℕ} (hp : p ≤ N) (hage : 0 < (traceState cfg K R seed ys p).2.2.2.1)
    (s : Fin u) :
    |scalarEstimate (traceState cfg K R seed ys p).2.2.2.1
      (traceState cfg K R seed ys p).2.2.2.2.1 s - traceGap cfg K R seed ys f p s| ≤
        confidenceRadius cfg u (traceState cfg K R seed ys p).2.2.2.1 := by
  cases p with
  | zero => change 0 < 0 at hage; omega
  | succ q =>
      have hprev := hscalar q (by omega) s
      cases h : traceWinner cfg K R seed ys q with
      | none =>
          have hstage : traceStage cfg K R seed ys (q + 1) = traceStage cfg K R seed ys q := by
            simp only [traceStage, h, if_true, Nat.add_zero]
          rw [trace_candidate_gap_eq_of_same_stage cfg K R seed ys f s hstage]
          have hs : traceState cfg K R seed ys (q + 1) =
              continueState (traceState cfg K R seed ys q)
                (updatedScalars cfg (traceState cfg K R seed ys q) (seedGaussian seed q) (ys q).1 (ys q).2)
                (updatedGradients cfg (traceState cfg K R seed ys q) (seedGaussian seed q) (ys q).1) := by
            rw [traceState_succ, step_continues cfg R _ _ _ _ _ _ h]
          simpa only [traceScalar, traceSampleCount, hs, continueState] using hprev
      | some s' =>
          rw [traceState_succ, step_restarts cfg R _ _ _ _ _ _ s' h] at hage
          change 0 < 0 at hage
          omega
end LG2021.Algorithm
end
end
/- LG2021FinalRateAlgebra -/
section
noncomputable section
namespace LG2021.Algorithm
private theorem separationFactor_ge_one {d : ℕ} (hd : 0 < d) : 1 ≤ separationFactor d := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 1 ≤ Real.sqrt (d : ℝ) := Real.one_le_sqrt.2 hdR
  unfold separationFactor
  nlinarith [mul_le_mul hdR hs (by norm_num) (Nat.cast_nonneg d)]
end LG2021.Algorithm
end
end
/- LG2021CandidateHitGeometry -/
section
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace LG2021.Algorithm
open Set MeasureTheory Concentration
open scoped Classical
end LG2021.Algorithm
end
end
/- LG2021CandidateHitEvent -/
section
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace LG2021.Algorithm
open Set MeasureTheory Concentration BilateralProfitMHR
open scoped ENNReal Classical
end LG2021.Algorithm
end
end
/- LG2021CandidateNormSupport -/
section
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
namespace LG2021.Algorithm
open Set MeasureTheory Concentration BilateralProfitMHR
open scoped ENNReal
end LG2021.Algorithm
end
end
/- LG2021CandidateHitTerminal -/
section
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace LG2021.Algorithm
open Set MeasureTheory Concentration BilateralProfitMHR
open scoped ENNReal Classical
end LG2021.Algorithm
end
end
/- LG2021CandidateHitLift -/
section
noncomputable section
namespace LG2021.Algorithm
open Set MeasureTheory Concentration
end LG2021.Algorithm
end
end
/- LG2021PairLossMartingale -/
section
noncomputable section
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped ENNReal Classical
end LG2021.Concentration
end
end
/- LG2021PairLossTerminal -/
section
noncomputable section
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped ENNReal Classical
end LG2021.Concentration
end
end
/- LG2021PairLossTrace -/
section
noncomputable section
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped ENNReal Classical
end LG2021.Concentration
end
end
/- LG2021ConcentrationTerminalGood -/
section
noncomputable section
set_option maxHeartbeats 1500000
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory
end LG2021.Concentration
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
end
/- LG2021ComparatorNonneg -/
section
noncomputable section
namespace LG2021.Algorithm
private theorem canonical_frameGap_nonneg {d p : ℕ} (hd : 0 < d)
    {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K) {r D : ℝ}
    (hr : 0 < r) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (cuts : Fin p → CutCode d) (hi : (interior (codedBody K cuts)).Nonempty)
    (f : Space d → ℝ) (hf : LipschitzWith 1 f) (hc : ConvexOn ℝ Set.univ f)
    (xstar : Space d) (hmin : ∀ x ∈ K, f xstar ≤ f x) :
    0 ≤ frameGap f xstar (canonicalOuterFrame K r cuts) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hLip := canonical_loss_lipschitz hd hK hcv hr hdiam cuts hi f hf
  have hconv := convexOn_loss_frame hc (canonicalOuterFrame K r cuts)
  have hmean := gaussianMean_ge_value_zero hLip hconv
  have hinner := canonicalOuterFrame_inner_ball hd hK hcv hr cuts hi
  have hcenter : frameApply (canonicalOuterFrame K r cuts) 0 ∈ K :=
    (hinner ⟨0, by simpa using (div_pos hr hdpos).le, rfl⟩).1
  have hlow := hmin _ hcenter
  unfold frameGap
  linarith
private theorem traceComparatorGap_nonneg {d u : ℕ} (hd : 0 < d) (cfg : OracleConfig)
    {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K) {D : ℝ}
    (hr : 0 < cfg.radius) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (R : ℝ) (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (p : ℕ)
    (hi : (interior (codedBody K (traceState cfg K R seed ys p).1)).Nonempty)
    (f : Space d → ℝ) (hf : LipschitzWith 1 f) (hc : ConvexOn ℝ Set.univ f)
    (xstar : Space d) (hmin : ∀ x ∈ K, f xstar ≤ f x) :
    0 ≤ traceComparatorGap cfg K R seed ys f xstar p := by
  have hframe := runState_frame cfg K R seed p (fun i => ys i)
  change (traceState cfg K R seed ys p).2.1 =
    canonicalOuterFrame K cfg.radius (traceState cfg K R seed ys p).1 at hframe
  unfold traceComparatorGap
  rw [hframe]
  exact canonical_frameGap_nonneg hd hK hcv hr hdiam _ hi f hf hc xstar hmin
end LG2021.Algorithm
end
end
/- LG2021PathwiseRegret -/
section
noncomputable section
namespace LG2021.Algorithm
open Concentration
end LG2021.Algorithm
end
end
/- LG2021DeterministicClosure -/
section
noncomputable section
set_option maxHeartbeats 1000000
namespace LG2021.Algorithm
open MeasureTheory Concentration Set
end LG2021.Algorithm
end
end
/- LG2021ExpectedRegret -/
section
noncomputable section
namespace LG2021
open MeasureTheory BilateralProfitMHR
open scoped ENNReal
end LG2021
end
end
/- LG2021CanonicalExpectedRegret -/
section
noncomputable section
namespace LG2021.Algorithm
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Concentration
open scoped ENNReal
end LG2021.Algorithm
end
end
/- Canonical fixed-dimensional bandit theorem -/
section
noncomputable section
set_option maxHeartbeats 2000000
namespace LG2021
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport
open Algorithm Concentration Set Metric
end LG2021
end
end
/- LG2021LipschitzExtension -/
section
/-!
The global extension needed only in the analysis of the bandit policy.
The infimal-convolution construction follows the existing real Lipschitz
extension proof in Mathlib; compact convexity additionally preserves convexity.
The infimal-convolution formulation supplies the global extension used in the formal proof.
-/
noncomputable section
namespace LG2021
open Set
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end LG2021
end
end
/- LG2021Erosion -/
section
/-!
The known-body erosion used in Appendix F of Lattimore and György (2021).
The interior Lipschitz proof adapts Mathlib's convex secant argument, using
the loss range [0,1] to obtain the exact constant. The loss and its extension
are analysis objects; the eroded body uses only the known body and scale.
-/
noncomputable section
namespace LG2021
open Set Metric
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end LG2021
end
end
/- CorollaryTransport -/
section
namespace BilateralProfitMHR.CorollaryTransport
open MeasureTheory
open scoped ENNReal
section Geometry
variable {X Y Ω : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]
end Geometry
section Observations
variable {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
end Observations
end BilateralProfitMHR.CorollaryTransport
end
/- CorollaryNormalization -/
section
namespace BilateralProfitMHR.CorollaryTransport
open MeasureTheory
open scoped ENNReal
end BilateralProfitMHR.CorollaryTransport
end
/- LG2021ErosionTransport -/
section
noncomputable section
namespace LG2021
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
open scoped ENNReal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
end LG2021
end
end
/- LG2021Reduction -/
section
namespace LG2021
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport
open scoped ENNReal
end LG2021
end
/- LG2021CanonicalTransport -/
section
/-! Quantifier-preserving reduction from the canonical Lipschitz problem to
continuous convex losses, arbitrary affine dimension, and the stated noise norm.
The reduction preserves the choice of policy before the unknown loss and noise. -/
noncomputable section
namespace LG2021
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
open scoped ENNReal
end LG2021
end
end
/- LG2021NormalizedTransport -/
section
noncomputable section
namespace LG2021
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
end LG2021
end
end
/- LG2021SharpClosure -/
section
noncomputable section
set_option maxHeartbeats 2000000
namespace LG2021.Algorithm
open MeasureTheory Concentration Set
theorem terminal_regret_of_current_bounds_sharp {d n N : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    {R D : ℝ} (hR : 0 < R) (hRD : R ≤ D)
    (hbounded : ∀ x ∈ K, ‖x‖ ≤ R) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (seed : Seed d (candidateCount n) n) (ys : ℕ → ℝ × ℝ)
    (f : Space d → ℝ) (hf : LipschitzWith 1 f) (hc : ConvexOn ℝ univ f)
    (xstar : Space d) (hmin : ∀ x ∈ K, f xstar ≤ f x)
    (v : Fin (d + 1) → Space d) (hv0 : v 0 = xstar) (hv : ∀ i, v i ∈ K)
    (hnear : ∀ i, f (v i) ≤ f xstar + Real.exp (-parameterLog d D n))
    (hvol : ENNReal.ofReal (sourceSimplexVolume d D (parameterLog d D n)) ≤
      volume (convexHull ℝ (range v))) (hN : N ≤ n) {r : ℝ}
    (hseed : ∀ p ≤ N, ∀ s, ‖seedCandidates seed p s‖ ≤
      (oracleConfig d D n).radius / (2 * (d : ℝ)))
    (hscalar : ∀ p < N,
      (interior (codedBody K (traceState (oracleConfig d D n) K R seed ys p).1)).Nonempty →
      ∀ s, |traceScalar (oracleConfig d D n) K R seed ys p s -
        traceGap (oracleConfig d D n) K R seed ys f p s| ≤
          confidenceRadius (oracleConfig d D n) (candidateCount n)
            (traceSampleCount (oracleConfig d D n) K R seed ys p))
    (hgradient : ∀ p < N,
      (interior (codedBody K (traceState (oracleConfig d D n) K R seed ys p).1)).Nonempty →
      (∀ i, v i ∈ codedBody K (traceState (oracleConfig d D n) K R seed ys p).1) →
      ∀ s, traceWinner (oracleConfig d D n) K R seed ys p = some s →
      ∀ i, traceGradientDeviation (oracleConfig d D n) K R seed ys f p s (v i) ≤
        2 * (oracleConfig d D n).radius *
          ((oracleConfig d D n).momentConstant * Real.sqrt
            (confidenceLog (oracleConfig d D n) (candidateCount n) /
              ((oracleConfig d D n).concentrationConstant *
                (traceSampleCount (oracleConfig d D n) K R seed ys p : ℝ))) +
            1 / (8 * (oracleConfig d D n).radius * n)))
    (hhit : (∀ p ≤ N,
      (interior (codedBody K (traceState (oracleConfig d D n) K R seed ys p).1)).Nonempty) →
      (∀ p ≤ N, xstar ∈ codedBody K (traceState (oracleConfig d D n) K R seed ys p).1) →
      ∀ p ≤ N, ∃ s : Fin (candidateCount n),
        (traceComparatorGap (oracleConfig d D n) K R seed ys f xstar p - 1 / (n : ℝ)) /
          separationFactor d ≤ traceGap (oracleConfig d D n) K R seed ys f p s)
    (hpath : (∀ p < N,
      (interior (codedBody K (traceState (oracleConfig d D n) K R seed ys p).1)).Nonempty) →
      r ≤ 2 * (∑ p ∈ Finset.range N,
        min 1 (traceComparatorGap (oracleConfig d D n) K R seed ys f xstar p)) +
          Real.sqrt ((n : ℝ) * Real.log n) + 1) :
    (8 * ((d : ℝ) + 1) * ((d : ℝ) * Real.log R -
      Real.log (sourceSimplexVolume d D (parameterLog d D n) / (2 : ℝ)^d)) ≤
        128 * (d : ℝ)^2 * parameterLog d D n) →
    r ≤ sharpPathBound d D n := by
  intro hvolumeSharp
  let cfg := oracleConfig d D n
  let j : ℝ := 129 * (d : ℝ)^2 * parameterLog d D n
  have hDp : 0 < D := hR.trans_le hRD
  have hp := oracleConfig_bounds hd hn hDp.le
  have hr : 0 < cfg.radius := by linarith [hp.1]
  have hdelta := parameter_delta_le_horizon d (by omega : 1 ≤ n) hDp.le
  have hmargin := trace_margin_of_confidence hd cfg hK hcv R hdiam seed ys v f hf hc
    hmin hnear hN hdelta hp.2.1 (by linarith [hp.2.2.1]) hp.2.2.2.1 hp.1
    hp.2.2.2.2.1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2 hscalar hgradient
  have hVp := sourceSimplexVolume_pos d hDp (parameterLog d D n)
  have hgeo := trace_preserves_simplex cfg hcv hR.le hbounded seed ys v hv
    ((ENNReal.ofReal_pos.mpr hVp).trans_le hvol) hmargin
  have hstage := traceStage_bound_of_simplex hd cfg hK hcv hR hbounded hr seed ys v hv
    hVp hvol hseed hmargin
  have hhealthy : ∀ p ≤ N, (interior (codedBody K (traceState cfg K R seed ys p).1)).Nonempty :=
    fun p hpn => (hgeo p hpn).2
  have hxret : ∀ p ≤ N, xstar ∈ codedBody K (traceState cfg K R seed ys p).1 := by
    intro p hpn
    rw [← hv0]
    exact (hgeo p hpn).1 0
  have hhits := hhit hhealthy hxret
  have hscalarAll : ∀ p < N, ∀ s,
      |traceScalar cfg K R seed ys p s - traceGap cfg K R seed ys f p s| ≤
        confidenceRadius cfg (candidateCount n) (traceSampleCount cfg K R seed ys p) :=
    fun p hpn s => hscalar p hpn (hhealthy p hpn.le) s
  have hΔ : ∀ p < N, 0 ≤ traceComparatorGap cfg K R seed ys f xstar p := by
    intro p hpn
    exact traceComparatorGap_nonneg hd cfg hK hcv hr hdiam R seed ys p
      (hhealthy p hpn.le) f hf hc xstar hmin
  have hcand : ∀ p < N, ∃ s : Fin (candidateCount n), ∃ θ : ℝ,
      (traceComparatorGap cfg K R seed ys f xstar p - 1 / (n : ℝ)) /
        separationFactor d ≤ θ ∧
      (0 < (traceState cfg K R seed ys p).2.2.2.1 →
        |scalarEstimate (traceState cfg K R seed ys p).2.2.2.1
          (traceState cfg K R seed ys p).2.2.2.2.1 s - θ| ≤
          confidenceRadius cfg (candidateCount n) (traceState cfg K R seed ys p).2.2.2.1) := by
    intro p hpn
    obtain ⟨s, hs⟩ := hhits p hpn.le
    refine ⟨s, traceGap cfg K R seed ys f p s, hs, ?_⟩
    intro hage
    exact stored_scalar_confidence_of_updated cfg K R seed ys f hscalarAll hpn.le hage s
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : 1 ≤ parameterLog d D n := (parameterLog_bounds d n hDp.le).1
  have hd2 : (1 : ℝ) ≤ (d : ℝ)^2 := by nlinarith
  have hmul : (1 : ℝ) ≤ (d : ℝ)^2 * parameterLog d D n := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ (d : ℝ)^2 - 1)
      (show 0 ≤ parameterLog d D n by linarith)]
  have hcard := stages_card_le_of_bound (tag := traceStage cfg K R seed ys) (N := N)
    (fun p hp => traceStage_monotone cfg K R seed ys (Nat.le_of_lt hp))
  have hcardR : ((stages (traceStage cfg K R seed ys) N).card : ℝ) ≤
      (traceStage cfg K R seed ys N : ℝ) + 1 := by exact_mod_cast hcard
  have hcount : ((stages (traceStage cfg K R seed ys) N).card : ℝ) ≤ j := by
    dsimp [j]
    have hh := hstage.trans hvolumeSharp
    nlinarith
  have heff := trace_effective_gap_sum_le cfg K R seed ys f xstar N
    (by omega : 0 < n) (separationFactor_ge_one hd) hp.2.1 oracleMomentConstant_pos hp.1
    oracleConcentrationConstant_pos (by linarith [hp.2.2.2.2.2.2]) hΔ hcand hcount
  have heff' : (∑ p ∈ Finset.range N,
      effectiveGap n (separationFactor d) (traceComparatorGap cfg K R seed ys f xstar p)) ≤
        Real.sqrt (4 * separationFactor d ^ 2 * sampleBudget cfg (candidateCount n) + 1) *
          Real.sqrt ((n : ℝ) * j) := by
    apply heff.trans
    have hj : 0 ≤ j := by dsimp [j]; positivity
    gcongr
  have hcap := trace_capped_gap_sum_le cfg K R seed ys f xstar N (by omega : 0 < n)
    (by linarith [separationFactor_ge_one hd] : 0 ≤ separationFactor d) hN heff'
  have hpath' := hpath (fun p hpn => hhealthy p hpn.le)
  unfold sharpPathBound
  change r ≤ 2 * Real.sqrt (4 * separationFactor d ^ 2 * sampleBudget cfg (candidateCount n) + 1) *
    Real.sqrt ((n : ℝ) * j) + Real.sqrt ((n : ℝ) * Real.log n) +
      4 * (separationFactor d + 1) + 1
  linarith
end LG2021.Algorithm
end
end
/- LG2021SharpRateBase -/
section
noncomputable section
namespace LG2021
open Concentration
end LG2021
end
end
/- LG2021SharpRateAlgebra -/
section
noncomputable section
namespace LG2021.Algorithm
open Concentration
end LG2021.Algorithm
end
end
section
namespace LG2021.Algorithm
end LG2021.Algorithm
end
/- LG2021SharpStageRate -/
section
noncomputable section
namespace LG2021.Algorithm
open Set MeasureTheory Concentration
end LG2021.Algorithm
end
end
/- LG2021SharpTransport -/
section
/-!
Transport of the explicit universal dimension bound through Lipschitz extension
and the known-body erosion. The comparator is an infimum, so the convex loss
need not be continuous at the boundary of its domain.
-/
noncomputable section
namespace LG2021
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
open scoped ENNReal
section Erosion
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
end Erosion
end LG2021
end
end
/- LG2021SharpRateFixed -/
section
noncomputable section
namespace LG2021
end LG2021
end
end
/- LG2021SharpSourceTransport -/
section
/-!
The explicit source rate for arbitrary locations of the contained unit ball.
The loss comparator is its infimum on the compact action set; whenever the
minimum is attained this equals the source's minimum comparator.
-/
noncomputable section
namespace LG2021
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
open scoped ENNReal
end LG2021
end
end
/- LG2021SharpMain -/
section
noncomputable section
set_option maxHeartbeats 2000000
namespace LG2021
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport
open Algorithm Concentration Set Metric
end LG2021
end
end
open LG2021 MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric

open LG2021 LG2021.Algorithm LG2021.Concentration MeasureTheory Set
theorem solution {d n N : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    {R D : ℝ} (hR : 0 < R) (hRD : R ≤ D)
    (hbounded : ∀ x ∈ K, ‖x‖ ≤ R) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (seed : Seed d (candidateCount n) n) (ys : ℕ → ℝ × ℝ)
    (f : Space d → ℝ) (hf : LipschitzWith 1 f) (hc : ConvexOn ℝ univ f)
    (xstar : Space d) (hmin : ∀ x ∈ K, f xstar ≤ f x)
    (v : Fin (d + 1) → Space d) (hv0 : v 0 = xstar) (hv : ∀ i, v i ∈ K)
    (hnear : ∀ i, f (v i) ≤ f xstar + Real.exp (-parameterLog d D n))
    (hvol : ENNReal.ofReal (sourceSimplexVolume d D (parameterLog d D n)) ≤
      volume (convexHull ℝ (range v))) (hN : N ≤ n) {r : ℝ}
    (hseed : ∀ p ≤ N, ∀ s, ‖seedCandidates seed p s‖ ≤
      (oracleConfig d D n).radius / (2 * (d : ℝ)))
    (hscalar : ∀ p < N,
      (interior (codedBody K (traceState (oracleConfig d D n) K R seed ys p).1)).Nonempty →
      ∀ s, |traceScalar (oracleConfig d D n) K R seed ys p s -
        traceGap (oracleConfig d D n) K R seed ys f p s| ≤
          confidenceRadius (oracleConfig d D n) (candidateCount n)
            (traceSampleCount (oracleConfig d D n) K R seed ys p))
    (hgradient : ∀ p < N,
      (interior (codedBody K (traceState (oracleConfig d D n) K R seed ys p).1)).Nonempty →
      (∀ i, v i ∈ codedBody K (traceState (oracleConfig d D n) K R seed ys p).1) →
      ∀ s, traceWinner (oracleConfig d D n) K R seed ys p = some s →
      ∀ i, traceGradientDeviation (oracleConfig d D n) K R seed ys f p s (v i) ≤
        2 * (oracleConfig d D n).radius *
          ((oracleConfig d D n).momentConstant * Real.sqrt
            (confidenceLog (oracleConfig d D n) (candidateCount n) /
              ((oracleConfig d D n).concentrationConstant *
                (traceSampleCount (oracleConfig d D n) K R seed ys p : ℝ))) +
            1 / (8 * (oracleConfig d D n).radius * n)))
    (hhit : (∀ p ≤ N,
      (interior (codedBody K (traceState (oracleConfig d D n) K R seed ys p).1)).Nonempty) →
      (∀ p ≤ N, xstar ∈ codedBody K (traceState (oracleConfig d D n) K R seed ys p).1) →
      ∀ p ≤ N, ∃ s : Fin (candidateCount n),
        (traceComparatorGap (oracleConfig d D n) K R seed ys f xstar p - 1 / (n : ℝ)) /
          separationFactor d ≤ traceGap (oracleConfig d D n) K R seed ys f p s)
    (hpath : (∀ p < N,
      (interior (codedBody K (traceState (oracleConfig d D n) K R seed ys p).1)).Nonempty) →
      r ≤ 2 * (∑ p ∈ Finset.range N,
        min 1 (traceComparatorGap (oracleConfig d D n) K R seed ys f xstar p)) +
          Real.sqrt ((n : ℝ) * Real.log n) + 1) :
    (8 * ((d : ℝ) + 1) * ((d : ℝ) * Real.log R -
      Real.log (sourceSimplexVolume d D (parameterLog d D n) / (2 : ℝ)^d)) ≤
        128 * (d : ℝ)^2 * parameterLog d D n) →
    r ≤ sharpPathBound d D n := by
  exact LG2021.Algorithm.terminal_regret_of_current_bounds_sharp hd hn hK hcv hR hRD
    hbounded hdiam seed ys f hf hc xstar hmin v hv0 hv hnear hvol hN
    hseed hscalar hgradient hhit hpath
