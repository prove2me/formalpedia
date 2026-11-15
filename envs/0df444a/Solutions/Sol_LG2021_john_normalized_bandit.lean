-- Prove2me | solution 1 for LG2021.john_normalized_bandit
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-14T17:13:39.568515+00:00
-- url     : https://prove2.me/submissions/3ddb79b3-efc3-467a-82c5-3f357f630c2d

import Mathlib
import Definitions.Def_LG2021_CanonicalBandit
import Definitions.Def_LG2021_RegretRate
import Definitions.Def_LG2021_Policy
import Theorems.Thm_ModernConvex_Ellipsoids_lowner_fritz_john
import Theorems.Thm_LG2021_theorem_1

set_option autoImplicit false

/- John-coordinate helpers -/
section
noncomputable section
namespace LG2021.JohnHelpers
open Matrix Finset MeasureTheory ModernConvex.Ellipsoids
private lemma solid_compact {n : ℕ} {S : Set (Fin n → ℝ)} (hS : IsSolid S) : IsCompact S :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨hS.1,hS.2.1⟩
private noncomputable def affineHomeomorph {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) (c : Fin n → ℝ) : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) where
  toFun x := A *ᵥ x+c
  invFun x := A⁻¹ *ᵥ (x-c)
  left_inv x := by
    dsimp only
    rw [add_sub_cancel_right, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), Matrix.one_mulVec]
  right_inv x := by
    dsimp only
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA),
      Matrix.one_mulVec, sub_add_cancel]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end LG2021.JohnHelpers

end
end

/- Affine-hull and John coordinates -/
section

namespace LG2021

open Set ModernConvex.Ellipsoids

/-- A compact convex set admits full-dimensional coordinates in its affine hull.
The coordinate dimension does not exceed the ambient dimension. -/
private theorem affine_hull_coordinates {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d)))
    (hne : K.Nonempty) (hK : IsCompact K) (hcv : Convex ℝ K) :
    ∃ m : ℕ, m ≤ d ∧ ∃ S : Set (Fin m → ℝ),
      ∃ f : (Fin m → ℝ) →ᵃ[ℝ] EuclideanSpace ℝ (Fin d),
        IsSolid S ∧ Continuous f ∧ f '' S = K := by
  classical
  obtain ⟨p, hp⟩ := hne
  let H := affineSpan ℝ K
  let p' : H := ⟨p, subset_affineSpan ℝ K hp⟩
  letI : Nonempty H := ⟨p'⟩
  let m := Module.finrank ℝ H.direction
  let e : (Fin m → ℝ) ≃ᵃ[ℝ] H :=
    (Module.finBasis ℝ H.direction).equivFun.symm.toAffineEquiv.trans
      (AffineIsometryEquiv.vaddConst ℝ p').toAffineEquiv
  let eh := e.toContinuousAffineEquiv.toHomeomorph
  let S : Set (Fin m → ℝ) := e ⁻¹' (Subtype.val ⁻¹' K)
  let f := H.subtype.comp e.toAffineMap
  have hm : m ≤ d := by
    have hh := Submodule.finrank_le H.direction
    simpa [m] using hh
  have hcompact0 : IsCompact ((Subtype.val : H → EuclideanSpace ℝ (Fin d)) ⁻¹' K) := by
    apply Topology.IsInducing.subtypeVal.isCompact_preimage' hK
    intro x hx
    exact ⟨⟨x, subset_affineSpan ℝ K hx⟩, rfl⟩
  have hcompact : IsCompact S := by
    exact eh.isClosedEmbedding.isCompact_preimage hcompact0
  have hconvex : Convex ℝ S := hcv.affine_preimage f
  have hinterior0 : (interior ((Subtype.val : H → EuclideanSpace ℝ (Fin d)) ⁻¹' K)).Nonempty := by
    simpa only [intrinsicInterior, Set.image_nonempty] using
      (Set.Nonempty.intrinsicInterior hcv ⟨p, hp⟩)
  have hinterior : (interior S).Nonempty := by
    obtain ⟨x, hx⟩ := hinterior0
    refine ⟨eh.symm x, ?_⟩
    change eh.symm x ∈ interior (eh ⁻¹' _)
    rw [← eh.preimage_interior]
    simpa using hx
  refine ⟨m, hm, S, f, ⟨hcompact.isClosed, hcompact.isBounded, hconvex, hinterior⟩,
    f.continuous_of_finiteDimensional, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    let x' : H := ⟨x, subset_affineSpan ℝ K hx⟩
    refine ⟨e.symm x', ?_, ?_⟩
    · change (e (e.symm x') : EuclideanSpace ℝ (Fin d)) ∈ K
      simpa using hx
    · change (e (e.symm x') : EuclideanSpace ℝ (Fin d)) = x
      simp [x']

open Matrix

private def matrixAffineMap {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (c : Fin m → ℝ) :
    (Fin m → ℝ) →ᵃ[ℝ] (Fin m → ℝ) :=
  A.mulVecLin.toAffineMap + AffineMap.const ℝ (Fin m → ℝ) c

/-- John normalization in ordinary real coordinates, including dimension zero. -/
private theorem john_coordinates {m : ℕ} (S : Set (Fin m → ℝ)) (hS : IsSolid S) :
    ∃ R : Set (Fin m → ℝ), ∃ f : (Fin m → ℝ) →ᵃ[ℝ] (Fin m → ℝ),
      IsSolid R ∧ Continuous f ∧ f '' R = S ∧ unitBall m ⊆ R ∧
        R ⊆ ellipsoid ((m : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ)) 0 := by
  classical
  obtain ⟨⟨E, hE, _⟩, hround⟩ := (lowner_fritz_john S hS).1
  obtain ⟨A, c, hA, rfl⟩ := hE.1
  let e := JohnHelpers.affineHomeomorph A hA c
  let f := matrixAffineMap A c
  let R := e ⁻¹' S
  have hef : (e : (Fin m → ℝ) → (Fin m → ℝ)) = f := rfl
  have hcompact : IsCompact R := e.isClosedEmbedding.isCompact_preimage (JohnHelpers.solid_compact hS)
  have hconvex : Convex ℝ R := hS.2.2.1.affine_preimage f
  have hinterior : (interior R).Nonempty := by
    obtain ⟨x, hx⟩ := hS.2.2.2
    refine ⟨e.symm x, ?_⟩
    change e.symm x ∈ interior (e ⁻¹' S)
    rw [← e.preimage_interior]
    simpa using hx
  refine ⟨R, f, ⟨hcompact.isClosed, hcompact.isBounded, hconvex, hinterior⟩,
    f.continuous_of_finiteDimensional, ?_, ?_, ?_⟩
  · change e '' (e ⁻¹' S) = S
    exact e.surjective.image_preimage S
  · intro x hx
    apply hE.2.1
    exact ⟨x, hx, rfl⟩
  · intro x hx
    obtain ⟨u, hu, he⟩ := (hround A c hA hE).1 hx
    have he' : e x = e ((m : ℝ) • u) := by
      change A *ᵥ x + c = A *ᵥ ((m : ℝ) • u) + c
      change A *ᵥ x + c = ((m : ℝ) • A) *ᵥ u + c at he
      simpa only [smul_mulVec, mulVec_smul] using he
    have hx' : x = (m : ℝ) • u := e.injective he'
    refine ⟨u, hu, ?_⟩
    simpa only [smul_mulVec, one_mulVec, add_zero] using hx'

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

private theorem euclidean_dilate_subset {m : ℕ} (x : EuclideanSpace ℝ (Fin m))
    (hx : EuclideanSpace.equiv (Fin m) ℝ x ∈
      ellipsoid ((m : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ)) 0) :
    x ∈ Metric.closedBall 0 (m : ℝ) := by
  let q := EuclideanSpace.equiv (Fin m) ℝ
  obtain ⟨u, hu, hxu⟩ := hx
  let v := q.symm u
  have hv : ‖v‖ ≤ 1 := by
    have huv : q v ∈ unitBall m := by simpa [v, unitBall] using hu
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (euclidean_unitBall_iff v).mp huv
  have he : x = (m : ℝ) • v := by
    apply q.injective
    simpa only [map_smul, v, ContinuousLinearEquiv.apply_symm_apply,
      smul_mulVec, one_mulVec, add_zero] using hxu
  rw [Metric.mem_closedBall, dist_zero_right, he, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg m)]
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-- Every nonempty compact convex body is the affine image of a John-normalized
body in its affine dimension. This also covers singleton bodies (dimension zero). -/
private theorem affine_hull_john_representation {d : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin d))) (hne : K.Nonempty)
    (hK : IsCompact K) (hcv : Convex ℝ K) :
    ∃ m : ℕ, m ≤ d ∧ ∃ R : Set (EuclideanSpace ℝ (Fin m)),
      ∃ f : EuclideanSpace ℝ (Fin m) →ᵃ[ℝ] EuclideanSpace ℝ (Fin d),
        R.Nonempty ∧ IsCompact R ∧ Convex ℝ R ∧
        Metric.closedBall 0 1 ⊆ R ∧ R ⊆ Metric.closedBall 0 (m : ℝ) ∧
        Continuous f ∧ f '' R = K := by
  obtain ⟨m, hmd, S, g, hS, _, hg⟩ := affine_hull_coordinates K hne hK hcv
  obtain ⟨R, f, hR, _, hf, hinner, houter⟩ := john_coordinates S hS
  let q := EuclideanSpace.equiv (Fin m) ℝ
  let R0 := q ⁻¹' R
  let f0 := g.comp (f.comp q.toLinearEquiv.toAffineEquiv.toAffineMap)
  have hcompact : IsCompact R0 := q.toHomeomorph.isClosedEmbedding.isCompact_preimage
    (JohnHelpers.solid_compact hR)
  have hconvex : Convex ℝ R0 :=
    hR.2.2.1.affine_preimage q.toLinearEquiv.toAffineEquiv.toAffineMap
  have hinner0 : Metric.closedBall 0 1 ⊆ R0 := by
    intro x hx
    exact hinner ((euclidean_unitBall_iff x).mpr hx)
  have houter0 : R0 ⊆ Metric.closedBall 0 (m : ℝ) := by
    intro x hx
    exact euclidean_dilate_subset x (houter hx)
  refine ⟨m, hmd, R0, f0, ⟨0, hinner0 (by simp)⟩, hcompact, hconvex,
    hinner0, houter0, f0.continuous_of_finiteDimensional, ?_⟩
  change (fun x => g (f (q x))) '' (q ⁻¹' R) = K
  rw [← Set.image_image (fun x => g (f x)) q (q ⁻¹' R),
    q.surjective.image_preimage, ← Set.image_image g f R, hf, hg]

end LG2021

end

/- Affine policy and kernel transport -/
section
namespace BilateralProfitMHR.CorollaryTransport
open MeasureTheory
open scoped ENNReal
section Geometry

variable {X Y Ω : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]


private theorem mapQuery_isOn (f : Y → X) (hf : Measurable f) (A : QueryAlg Y Ω)
    {K : Set X} {R : Set Y} (hA : A.IsOn R) (hfK : Set.MapsTo f R K) :
    (mapQuery f hf A).IsOn K := by
  intro τ ω y
  exact hfK (hA τ ω y)

private theorem pullKernel_measurable (f : Y → X) (hf : Measurable f)
    (ν : ObsKernel X) (hν : ν.IsMeasurable) : (pullKernel f ν).IsMeasurable := by
  intro τ
  change Measurable (fun w : (Fin τ → Y) × (Fin τ → ℝ) × Y =>
    ν τ (fun i => f (w.1 i)) w.2.1 (f w.2.2))
  exact (hν τ).comp (show Measurable (fun w : (Fin τ → Y) × (Fin τ → ℝ) × Y =>
    ((fun i => f (w.1 i)), w.2.1, f w.2.2)) from by fun_prop)

private theorem pullKernel_noiseCond (f : Y → X) (ν : ObsKernel X)
    {K : Set X} {R : Set Y} (hfK : Set.MapsTo f R K) (L : X → ℝ) (γ : ℝ)
    (hν : NoiseCond K L γ ν) : NoiseCond R (L ∘ f) γ (pullKernel f ν) := by
  intro τ xs ys x hxs hx
  exact hν τ (fun i => f (xs i)) ys (f x) (fun i => hfK (hxs i)) (hfK hx)

private theorem cumLoss_mapQuery (f : Y → X) (hf : Measurable f) (A : QueryAlg Y Ω)
    (ν : ObsKernel X) (g : X → ℝ≥0∞) (ω : Ω) (m τ : ℕ) (y : Fin τ → ℝ) :
    cumLoss (mapQuery f hf A) ν g ω m τ y =
      cumLoss A (pullKernel f ν) (g ∘ f) ω m τ y := by
  induction m generalizing τ with
  | zero => rfl
  | succ m ih =>
      simp only [cumLoss, mapQuery, Function.comp_apply]
      congr 1
      apply lintegral_congr
      intro z
      exact ih (τ + 1) (Fin.snoc y z)

private theorem expectedCumLoss_mapQuery (f : Y → X) (hf : Measurable f) (A : QueryAlg Y Ω)
    (P : Measure Ω) (ν : ObsKernel X) (g : X → ℝ≥0∞) (n : ℕ) :
    expectedCumLoss (mapQuery f hf A) P ν g n =
      expectedCumLoss A P (pullKernel f ν) (g ∘ f) n := by
  apply lintegral_congr
  intro ω
  exact cumLoss_mapQuery f hf A ν g ω n 0 Fin.elim0

end Geometry
end BilateralProfitMHR.CorollaryTransport

end

/- Affine regret identity -/
section
namespace BilateralProfitMHR.CorollaryTransport
open MeasureTheory
open scoped ENNReal
private theorem sInf_loss_image {X Y : Type} (f : Y → X) {R : Set Y} {K : Set X}
    (himage : f '' R = K) (L : X → ℝ) :
    sInf ((L ∘ f) '' R) = sInf (L '' K) := by
  change sInf ((fun x => L (f x)) '' R) = _
  rw [← Set.image_image L f R, himage]

private theorem expectedRegret_mapQuery {X Y Ω : Type} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Ω] (f : Y → X) (hf : Measurable f)
    {R : Set Y} {K : Set X} (himage : f '' R = K) (L : X → ℝ)
    (A : QueryAlg Y Ω) (P : Measure Ω) (ν : ObsKernel X) (n : ℕ) :
    expectedCumLoss (mapQuery f hf A) P ν
      (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n =
    expectedCumLoss A P (pullKernel f ν)
      (fun x => ENNReal.ofReal ((L ∘ f) x - sInf ((L ∘ f) '' R))) n := by
  rw [expectedCumLoss_mapQuery, sInf_loss_image f himage L]
  rfl

private theorem pullKernel_unitNoiseCond {X Y : Type} (f : Y → X) (ν : ObsKernel X)
    {K : Set X} {R : Set Y} (hfK : Set.MapsTo f R K) (L : X → ℝ)
    (hν : UnitNoiseCond K L ν) : UnitNoiseCond R (L ∘ f) (pullKernel f ν) := by
  intro τ xs ys x hxs hx
  exact hν τ (fun i => f (xs i)) ys (f x) (fun i => hfK (hxs i)) (hfK hx)

end BilateralProfitMHR.CorollaryTransport

end

/- Dimension constants and singleton bodies -/
section
namespace LG2021
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport
open scoped ENNReal
private noncomputable def dimensionConstant (d : ℕ) (D : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (d + 1), max 0 (D m)

private theorem dimensionConstant_nonneg (d : ℕ) (D : ℕ → ℝ) :
    0 ≤ dimensionConstant d D := by
  exact Finset.sum_nonneg (fun m _ => le_max_left _ _)

private theorem le_dimensionConstant (d : ℕ) (D : ℕ → ℝ) {m : ℕ} (hm : m ≤ d) :
    D m ≤ dimensionConstant d D := by
  exact (le_max_right 0 (D m)).trans
    (Finset.single_le_sum (fun i _ => le_max_left 0 (D i))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hm)))

/-- A constant query policy, used for bodies of affine dimension zero. -/
private def constantQuery {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (x : X) : QueryAlg X Ω where
  query _ _ _ := x
  query_measurable _ := measurable_const

private theorem cumLoss_constantQuery_zero {X Ω : Type} [MeasurableSpace X]
    [MeasurableSpace Ω] (x : X) (ν : ObsKernel X) (g : X → ℝ≥0∞) (hg : g x = 0)
    (ω : Ω) (m τ : ℕ) (y : Fin τ → ℝ) :
    cumLoss (constantQuery x) ν g ω m τ y = 0 := by
  induction m generalizing τ with
  | zero => rfl
  | succ m ih =>
      simp only [cumLoss, ih, lintegral_zero, add_zero]
      exact hg

private theorem expectedCumLoss_constantQuery_zero {X Ω : Type} [MeasurableSpace X]
    [MeasurableSpace Ω] (x : X) (P : Measure Ω) (ν : ObsKernel X)
    (g : X → ℝ≥0∞) (hg : g x = 0) (n : ℕ) :
    expectedCumLoss (constantQuery x) P ν g n = 0 := by
  simp [expectedCumLoss, cumLoss_constantQuery_zero x ν g hg]

private theorem zero_dim_expectedRegret {Ω : Type} [MeasurableSpace Ω]
    {K : Set (EuclideanSpace ℝ (Fin 0))} (hne : K.Nonempty)
    (P : Measure Ω) (ν : ObsKernel (EuclideanSpace ℝ (Fin 0)))
    (L : EuclideanSpace ℝ (Fin 0) → ℝ) (n : ℕ) :
    (constantQuery (Ω := Ω) (0 : EuclideanSpace ℝ (Fin 0))).IsOn K ∧
      expectedCumLoss (constantQuery (0 : EuclideanSpace ℝ (Fin 0))) P ν
        (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n = 0 := by
  have hK : K = {0} := by
    ext x
    constructor
    · intro _
      exact Subsingleton.elim x 0
    · intro _
      obtain ⟨y, hy⟩ := hne
      simpa only [Subsingleton.elim x y] using hy
  subst K
  constructor
  · intro τ ω y
    simp [constantQuery]
  · apply expectedCumLoss_constantQuery_zero
    simp

end LG2021

end

/- Specialization of the explicit dimension rate -/
section
namespace LG2021
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
private def SharpConvexBandit (C : ℝ) : Prop :=
  ∀ d : ℕ, 0 < d → ∀ n : ℕ, 2 ≤ n →
    ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → Convex ℝ K →
      (∃ a, closedBall a 1 ⊆ K) →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
        ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
          ∀ L : EuclideanSpace ℝ (Fin d) → ℝ,
            ConvexOn ℝ K L → (∀ x ∈ K, L x ∈ Icc 0 1) →
            ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable →
              UnitNoiseCond K L ν →
                expectedCumLoss A P ν
                  (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
                    ENNReal.ofReal (C * sharpRate d (Metric.diam K) n)
private theorem sourceLog_lower {n : ℕ} (hn : 2 ≤ n) {D : ℝ} (hD : 2 ≤ D) :
    1 ≤ Real.log ((n : ℝ) * D) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hND : (4 : ℝ) ≤ (n : ℝ) * D := by nlinarith
  apply (Real.le_log_iff_exp_le (by positivity : 0 < (n : ℝ) * D)).2
  linarith [Real.exp_one_lt_three]
private theorem sharpRate_eq_max {d n : ℕ} (hd : 0 < d) {D : ℝ}
    (ht : 0 ≤ Real.log ((n : ℝ) * D)) :
    sharpRate d D n =
      max ((d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n *
          (Real.log ((n : ℝ) * D) * Real.sqrt (Real.log ((n : ℝ) * D))))
        ((d : ℝ) ^ 3 * Real.sqrt d * Real.sqrt n *
          Real.log ((n : ℝ) * D) ^ 2) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hsq := Real.sq_sqrt ht
  unfold sharpRate
  rw [mul_max_of_nonneg _ _ (by positivity)]
  simp only [mul_one]
  congr 1
  field_simp
  linear_combination Real.sqrt n * Real.log ((n : ℝ) * D) * hsq
private theorem log_horizon_half_lower {n : ℕ} (hn : 2 ≤ n) :
    (1 / 2 : ℝ) ≤ Real.log n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at htwo
  exact htwo.trans (Real.log_le_log (by norm_num) hnR)
private theorem sharpRate_le_dimension_horizon_rate {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    {D : ℝ} (hD : 2 ≤ D) (hDupper : D ≤ 2 * (d : ℝ) * n) :
    sharpRate d D n ≤
      ((d : ℝ) ^ 4 * Real.sqrt d * (4 * (d : ℝ) + 4) ^ 2) *
        Real.sqrt n * Real.log n ^ 2 := by
  let t := Real.log ((n : ℝ) * D)
  let M := 4 * (d : ℝ) + 4
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hDpos : 0 < D := by linarith
  have ht : 1 ≤ t := sourceLog_lower hn hD
  have hlogn := log_horizon_half_lower hn
  have hlogconst : Real.log (2 * (d : ℝ)) ≤ 2 * (d : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * (d : ℝ))
    linarith
  have hlogD := Real.log_le_log hDpos hDupper
  rw [Real.log_mul (by positivity : (2 * (d : ℝ)) ≠ 0) hnpos.ne'] at hlogD
  have htupper : t ≤ M * Real.log n := by
    have hteq : t = Real.log n + Real.log D := Real.log_mul hnpos.ne' hDpos.ne'
    dsimp [M]
    rw [hteq]
    nlinarith [mul_le_mul_of_nonneg_left hlogn (show 0 ≤ 4 * (d : ℝ) by positivity)]
  have hsqrt : Real.sqrt t ≤ t := by
    apply (Real.sqrt_le_left (by linarith : 0 ≤ t)).2
    nlinarith
  have hproduct : t * Real.sqrt t ≤ t ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsqrt (by linarith : 0 ≤ t)]
  have hsquare : t ^ 2 ≤ (M * Real.log n) ^ 2 := by gcongr
  have hdpow : (d : ℝ) ^ 3 ≤ (d : ℝ) ^ 4 :=
    pow_le_pow_right₀ hdR (by decide : 3 ≤ 4)
  rw [sharpRate_eq_max hd (by dsimp [t] at ht; linarith)]
  change max ((d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n * (t * Real.sqrt t))
      ((d : ℝ) ^ 3 * Real.sqrt d * Real.sqrt n * t ^ 2) ≤ _
  have hnorm :
      (d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n * (M * Real.log n) ^ 2 =
        ((d : ℝ) ^ 4 * Real.sqrt d * (4 * (d : ℝ) + 4) ^ 2) *
          Real.sqrt n * Real.log n ^ 2 := by dsimp [M]; ring
  apply max_le
  · calc
      _ ≤ (d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n * t ^ 2 := by gcongr
      _ ≤ (d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n * (M * Real.log n) ^ 2 := by gcongr
      _ = _ := hnorm
  · calc
      _ ≤ (d : ℝ) ^ 4 * Real.sqrt d * Real.sqrt n * (M * Real.log n) ^ 2 := by gcongr
      _ = _ := hnorm
private theorem two_le_diameter_of_unitBall {d : ℕ} (hd : 0 < d)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    {a : EuclideanSpace ℝ (Fin d)} (hinner : closedBall a 1 ⊆ K) :
    2 ≤ Metric.diam K := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hball := Metric.diam_closedBall_eq a (by norm_num : (0 : ℝ) ≤ 1)
  have hm := Metric.diam_mono hinner hK.isBounded
  simpa only [hball, mul_one] using hm

end LG2021

end

/- John normalization of the source theorem -/
section

/-!
John normalization of the explicit source theorem. The source theorem is the
sole bandit premise. The affine-hull representation includes lower-dimensional
compact convex sets, and the zero-dimensional case has zero regret.
-/

noncomputable section
namespace LG2021

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
open scoped ENNReal

private def johnDimensionFactor (m : ℕ) : ℝ :=
  (m : ℝ)^4 * Real.sqrt m * (4 * (m : ℝ) + 4)^2

private theorem john_body_bandit_of_theorem_1 {C : ℝ} (hC : 0 ≤ C)
    (hsource : SharpConvexBandit C) {m : ℕ} {n : ℕ} (hn : 2 ≤ n)
    (R : Set (EuclideanSpace ℝ (Fin m))) (hR : IsCompact R) (hRc : Convex ℝ R)
    (hinner : closedBall 0 1 ⊆ R) (houter : R ⊆ closedBall 0 (m : ℝ)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
      ∃ A : QueryAlg (EuclideanSpace ℝ (Fin m)) Ω, A.IsOn R ∧
        ∀ L : EuclideanSpace ℝ (Fin m) → ℝ,
          ConvexOn ℝ R L → (∀ x ∈ R, L x ∈ Icc 0 1) →
          ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin m)), ν.IsMeasurable →
            UnitNoiseCond R L ν →
              expectedCumLoss A P ν
                (fun x => ENNReal.ofReal (L x - sInf (L '' R))) n ≤
                  ENNReal.ofReal ((C * johnDimensionFactor m) *
                    Real.sqrt n * Real.log n ^ 2) := by
  by_cases hm : m = 0
  · subst m
    have hzero : (0 : EuclideanSpace ℝ (Fin 0)) ∈ R := hinner (by simp)
    refine ⟨Unit, inferInstance, Measure.dirac (), by infer_instance,
      constantQuery 0, (by intro τ ω y; exact hzero), ?_⟩
    intro L _hLv _hLr ν _hνm _hν
    rw [(zero_dim_expectedRegret ⟨0, hzero⟩ (Measure.dirac ()) ν L n).2]
    exact bot_le
  · have hmp : 0 < m := Nat.pos_of_ne_zero hm
    obtain ⟨Ω, mΩ, P, hP, A, hA, hregret⟩ :=
      hsource m hmp n hn R hR hRc ⟨0, hinner⟩
    letI := mΩ
    refine ⟨Ω, mΩ, P, hP, A, hA, ?_⟩
    intro L hLv hLr ν hνm hν
    have hD : 2 ≤ Metric.diam R := two_le_diameter_of_unitBall hmp hR hinner
    have hupper : Metric.diam R ≤ 2 * (m : ℝ) * n := by
      have hrad : Metric.diam R ≤ 2 * (m : ℝ) :=
        Metric.diam_le_of_subset_closedBall (Nat.cast_nonneg m) houter
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hrate := sharpRate_le_dimension_horizon_rate hmp hn hD hupper
    apply (hregret L hLv hLr ν hνm hν).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      C * sharpRate m (Metric.diam R) n ≤
          C * (johnDimensionFactor m * Real.sqrt n * Real.log n ^ 2) :=
        mul_le_mul_of_nonneg_left hrate hC
      _ = _ := by ring

/-- The fixed-dimensional compact-body guarantee follows directly from the
source theorem through the affine-hull version of John's normalization. -/
private theorem john_normalized_bandit_of_theorem_1
    (hsource : ∃ C : ℝ, 0 ≤ C ∧ SharpConvexBandit C) :
    ∀ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      ∀ K : Set (EuclideanSpace ℝ (Fin d)), K.Nonempty → IsCompact K → Convex ℝ K →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
          ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
            ∀ L : EuclideanSpace ℝ (Fin d) → ℝ,
              ContinuousOn L K → ConvexOn ℝ K L → (∀ x ∈ K, L x ∈ Icc 0 1) →
              ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable →
                UnitNoiseCond K L ν →
                  expectedCumLoss A P ν
                    (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
                      ENNReal.ofReal (C * Real.sqrt n * Real.log n ^ 2) := by
  obtain ⟨C, hC, hbandit⟩ := hsource
  intro d
  let B := dimensionConstant d (fun m => C * johnDimensionFactor m)
  refine ⟨B, dimensionConstant_nonneg d _, ?_⟩
  intro n hn K hne hK hcv
  obtain ⟨m, hmd, R, f, _hRne, hR, hRc, hinner, houter, hf, himage⟩ :=
    affine_hull_john_representation K hne hK hcv
  obtain ⟨Ω, mΩ, P, hP, A, hA, hregret⟩ :=
    john_body_bandit_of_theorem_1 hC hbandit hn R hR hRc hinner houter
  letI := mΩ
  have hmap : MapsTo f R K := by
    intro x hx
    rw [← himage]
    exact ⟨x, hx, rfl⟩
  have hCB : C * johnDimensionFactor m ≤ B :=
    le_dimensionConstant d (fun j => C * johnDimensionFactor j) hmd
  refine ⟨Ω, mΩ, P, hP, mapQuery f hf.measurable A,
    mapQuery_isOn f hf.measurable A hA hmap, ?_⟩
  intro L _hLc hLv hLr ν hνm hν
  have hcompv : ConvexOn ℝ R (L ∘ f) := (hLv.comp_affineMap f).subset hmap hRc
  have hcompr : ∀ x ∈ R, (L ∘ f) x ∈ Icc (0 : ℝ) 1 := fun x hx => hLr _ (hmap hx)
  have hb := hregret (L ∘ f) hcompv hcompr (pullKernel f ν)
    (pullKernel_measurable f hf.measurable ν hνm) (pullKernel_unitNoiseCond f ν hmap L hν)
  rw [expectedRegret_mapQuery f hf.measurable himage L]
  exact hb.trans (ENNReal.ofReal_le_ofReal (by gcongr))


end LG2021

end
end

open LG2021 MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric

/-- John and affine-hull normalization of the explicit convex-bandit theorem.
The constant depends only on ambient dimension. -/
theorem LG2021.john_normalized_bandit :
    ∀ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      ∀ K : Set (EuclideanSpace ℝ (Fin d)), K.Nonempty → IsCompact K → Convex ℝ K →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
          ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
            ∀ L : EuclideanSpace ℝ (Fin d) → ℝ,
              ContinuousOn L K → ConvexOn ℝ K L → (∀ x ∈ K, L x ∈ Icc 0 1) →
              ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable →
                UnitNoiseCond K L ν →
                  expectedCumLoss A P ν
                    (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
                      ENNReal.ofReal (C * Real.sqrt n * Real.log n ^ 2) := by
  exact LG2021.john_normalized_bandit_of_theorem_1 LG2021.theorem_1

theorem solution :
    ∀ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      ∀ K : Set (EuclideanSpace ℝ (Fin d)), K.Nonempty → IsCompact K → Convex ℝ K →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
          ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
            ∀ L : EuclideanSpace ℝ (Fin d) → ℝ,
              ContinuousOn L K → ConvexOn ℝ K L → (∀ x ∈ K, L x ∈ Icc 0 1) →
              ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable →
                UnitNoiseCond K L ν →
                  expectedCumLoss A P ν
                    (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
                      ENNReal.ofReal (C * Real.sqrt n * Real.log n ^ 2) := by
  exact LG2021.john_normalized_bandit
