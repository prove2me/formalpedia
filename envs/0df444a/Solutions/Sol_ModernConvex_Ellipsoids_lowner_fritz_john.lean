-- Prove2me | solution 1 for ModernConvex.Ellipsoids.lowner_fritz_john
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-31T09:04:32.727843+00:00
-- url     : https://prove2.me/submissions/b28e5c77-d478-4f07-9b7e-77c2f7d10752

import Mathlib
import Definitions.Def_ModernConvex_Ellipsoids_Ellipsoid

open Matrix

section
open Matrix Finset MeasureTheory
namespace ModernConvex.Ellipsoids.Fresh

lemma continuous_dot_self (n : ℕ) : Continuous (fun x : Fin n → ℝ => x ⬝ᵥ x) := by
  unfold dotProduct
  fun_prop

lemma unitBall_closed (n : ℕ) : IsClosed (unitBall n) :=
  isClosed_le (continuous_dot_self n) continuous_const

lemma unitBall_coord {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ unitBall n) (i : Fin n) :
    |x i| ≤ 1 := by
  have hs : x i * x i ≤ x ⬝ᵥ x :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
  have hq : x ⬝ᵥ x ≤ 1 := hx
  rw [abs_le]
  constructor <;> nlinarith

lemma unitBall_bounded (n : ℕ) : Bornology.IsBounded (unitBall n) := by
  apply (show Bornology.IsBounded (Metric.closedBall (0 : Fin n → ℝ) 1) from Metric.isBounded_closedBall).subset
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
    (fun i => by simpa only [Real.norm_eq_abs] using unitBall_coord hx i)

lemma unitBall_compact (n : ℕ) : IsCompact (unitBall n) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨unitBall_closed n, unitBall_bounded n⟩

lemma zero_mem_unitBall (n : ℕ) : (0 : Fin n → ℝ) ∈ unitBall n := by
  simp [unitBall]

lemma unitBall_interior_nonempty (n : ℕ) : (interior (unitBall n)).Nonempty := by
  refine ⟨0, mem_interior.mpr ?_⟩
  refine ⟨{x : Fin n → ℝ | x ⬝ᵥ x < 1}, ?_,
    isOpen_lt (continuous_dot_self n) continuous_const, ?_⟩
  · intro x hx
    change x ⬝ᵥ x < 1 at hx
    exact hx.le
  · simp

lemma volume_unitBall_pos (n : ℕ) : 0 < volume (unitBall n) :=
  (isOpen_interior.measure_pos volume (unitBall_interior_nonempty n)).trans_le
    (measure_mono interior_subset)

lemma volume_unitBall_ne_top (n : ℕ) : volume (unitBall n) ≠ ⊤ :=
  (unitBall_compact n).measure_ne_top

lemma solid_compact {n : ℕ} {S : Set (Fin n → ℝ)} (hS : IsSolid S) : IsCompact S :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨hS.1,hS.2.1⟩

lemma solid_nonempty {n : ℕ} {S : Set (Fin n → ℝ)} (hS : IsSolid S) : S.Nonempty :=
  hS.2.2.2.mono interior_subset

end ModernConvex.Ellipsoids.Fresh
end

section
open Matrix Finset
namespace ModernConvex.Ellipsoids.Fresh

def polarSet {n : ℕ} (S : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {u | ∀ x ∈ S, u ⬝ᵥ x ≤ 1}

lemma polarSet_closed {n : ℕ} (S : Set (Fin n → ℝ)) : IsClosed (polarSet S) := by
  have he : polarSet S = ⋂ x ∈ S, {u | u ⬝ᵥ x ≤ 1} := by ext u; simp [polarSet]
  rw [he]
  refine isClosed_iInter (fun x => isClosed_iInter (fun _ => isClosed_le ?_ continuous_const))
  unfold dotProduct
  fun_prop

lemma dual_coeff_dot {n : ℕ} (f : (Fin n → ℝ) →ₗ[ℝ] ℝ) (x : Fin n → ℝ) :
    (fun i => f (Pi.single i 1)) ⬝ᵥ x = f x := by
  have hs : (∑ i, x i • (Pi.single i 1 : Fin n → ℝ)) = x := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  calc
    _ = ∑ i, f (x i • (Pi.single i 1 : Fin n → ℝ)) := by simp [dotProduct, mul_comm]
    _ = f (∑ i, x i • (Pi.single i 1 : Fin n → ℝ)) := (map_sum f _ _).symm
    _ = f x := congrArg f hs

lemma mem_of_polar_constraints {n : ℕ} {S : Set (Fin n → ℝ)}
    (hcl : IsClosed S) (hcv : Convex ℝ S) (h0 : (0 : Fin n → ℝ) ∈ S)
    {x : Fin n → ℝ} (hx : ∀ u ∈ polarSet S, u ⬝ᵥ x ≤ 1) : x ∈ S := by
  by_contra hn
  obtain ⟨f,a,hfa,hax⟩ := geometric_hahn_banach_closed_point hcv hcl hn
  have ha : 0 < a := by simpa using hfa 0 h0
  let u : Fin n → ℝ := fun i => f (Pi.single i 1) / a
  have hdot : ∀ y, u ⬝ᵥ y = f y / a := by
    intro y
    dsimp [u]
    unfold dotProduct
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    exact congrArg (fun t : ℝ => t/a) (dual_coeff_dot f.toLinearMap y)
  have hu : u ∈ polarSet S := by
    intro y hy
    rw [hdot]
    exact (div_le_one ha).mpr (hfa y hy).le
  have hh := hx u hu
  rw [hdot] at hh
  have hh' := (div_le_one ha).mp hh
  linarith

end ModernConvex.Ellipsoids.Fresh
end

section
open Matrix Finset
namespace ModernConvex.Ellipsoids.Fresh

lemma dot_self_nonneg {n : ℕ} (u : Fin n → ℝ) : 0 ≤ u ⬝ᵥ u :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (u i))

lemma normalized_mem_unitBall {n : ℕ} (u : Fin n → ℝ) (hu : 0 < u ⬝ᵥ u) :
    (1 / Real.sqrt (u ⬝ᵥ u)) • u ∈ unitBall n := by
  have hr := Real.sqrt_pos.mpr hu
  have hs := Real.sq_sqrt hu.le
  change ((1 / Real.sqrt (u ⬝ᵥ u)) • u) ⬝ᵥ ((1 / Real.sqrt (u ⬝ᵥ u)) • u) ≤ 1
  rw [smul_dotProduct, dotProduct_smul]
  change (1 / Real.sqrt (u ⬝ᵥ u)) * ((1 / Real.sqrt (u ⬝ᵥ u)) * (u ⬝ᵥ u)) ≤ 1
  have he : (1 / Real.sqrt (u ⬝ᵥ u)) * ((1 / Real.sqrt (u ⬝ᵥ u)) * (u ⬝ᵥ u)) = 1 := by
    field_simp
    nlinarith
  rw [he]

lemma ball_dot_iff {n : ℕ} (u : Fin n → ℝ) (r : ℝ) :
    (∀ v ∈ unitBall n, u ⬝ᵥ v ≤ r) ↔ 0 ≤ r ∧ u ⬝ᵥ u ≤ r^2 := by
  constructor
  · intro h
    have hr : 0 ≤ r := by simpa using h 0 (zero_mem_unitBall n)
    refine ⟨hr,?_⟩
    by_contra hn
    have hq : 0 < u ⬝ᵥ u := lt_of_le_of_lt (sq_nonneg r) (lt_of_not_ge hn)
    have hs := Real.sq_sqrt hq.le
    have hp := Real.sqrt_pos.mpr hq
    have hh := h _ (normalized_mem_unitBall u hq)
    rw [dotProduct_smul] at hh
    change (1/Real.sqrt (u ⬝ᵥ u))*(u ⬝ᵥ u) ≤ r at hh
    have he : (1/Real.sqrt (u ⬝ᵥ u))*(u ⬝ᵥ u) = Real.sqrt (u ⬝ᵥ u) := by
      field_simp
      nlinarith
    rw [he] at hh
    nlinarith
  · rintro ⟨hr,hq⟩ v hv
    have hvq : v ⬝ᵥ v ≤ 1 := hv
    have hcs : (u ⬝ᵥ v)^2 ≤ (u ⬝ᵥ u)*(v ⬝ᵥ v) := by
      simpa only [dotProduct, pow_two] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
    have hm := mul_le_mul_of_nonneg_left hvq (dot_self_nonneg u)
    nlinarith

lemma polarSet_subset_unitBall {n : ℕ} {S : Set (Fin n → ℝ)}
    (hB : unitBall n ⊆ S) : polarSet S ⊆ unitBall n := by
  intro u hu
  have hh := (ball_dot_iff u 1).mp (fun v hv => hu v (hB hv))
  change u ⬝ᵥ u ≤ 1
  simpa only [one_pow] using hh.2

lemma polarSet_compact {n : ℕ} {S : Set (Fin n → ℝ)} (hB : unitBall n ⊆ S) :
    IsCompact (polarSet S) :=
  (unitBall_compact n).of_isClosed_subset (polarSet_closed S) (polarSet_subset_unitBall hB)

end ModernConvex.Ellipsoids.Fresh
end

section

open Matrix
namespace ModernConvex.Ellipsoids.Fresh

/-- Dual moment property of the active unit contacts. -/
def ContactMoments {n : ℕ} (T : Set (Fin n → ℝ)) : Prop :=
  ∀ (H : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ),
    (∀ u ∈ T, u ⬝ᵥ u = 1 → 0 ≤ u ⬝ᵥ (H *ᵥ u) + b ⬝ᵥ u) → 0 ≤ H.trace

end ModernConvex.Ellipsoids.Fresh
end

section

open Matrix
namespace ModernConvex.Ellipsoids.Fresh

def OuterFeasible {n : ℕ} (T : Set (Fin n → ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : Prop :=
  ∀ u ∈ T, (A *ᵥ u + b) ⬝ᵥ (A *ᵥ u + b) ≤ 1

def InnerFeasible {n : ℕ} (T : Set (Fin n → ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : Prop :=
  ∀ u ∈ T, 0 ≤ 1 - b ⬝ᵥ u ∧
    (A *ᵥ u) ⬝ᵥ (A *ᵥ u) ≤ (1 - b ⬝ᵥ u) ^ 2

def OuterOptimal {n : ℕ} (T : Set (Fin n → ℝ)) : Prop :=
  ∀ A b, OuterFeasible T A b → |A.det| ≤ 1

def InnerOptimal {n : ℕ} (T : Set (Fin n → ℝ)) : Prop :=
  ∀ A b, InnerFeasible T A b → |A.det| ≤ 1

end ModernConvex.Ellipsoids.Fresh
end

section
open Matrix
namespace ModernConvex.Ellipsoids.Fresh

lemma dot_affine_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b u v : Fin n → ℝ) :
    u ⬝ᵥ (Aᵀ *ᵥ v+b) = (A *ᵥ u) ⬝ᵥ v + b ⬝ᵥ u := by
  rw [dotProduct_add, dotProduct_mulVec, vecMul_transpose, dotProduct_comm u b]

lemma innerFeasible_of_containment {n : ℕ} {S : Set (Fin n → ℝ)}
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (hsub : ellipsoid Aᵀ b ⊆ S) : InnerFeasible (polarSet S) A b := by
  intro u hu
  apply (ball_dot_iff (A *ᵥ u) (1-b ⬝ᵥ u)).mp
  intro v hv
  have hh := hu _ (hsub ⟨v,hv,rfl⟩)
  rw [dot_affine_transpose] at hh
  linarith

lemma containment_of_innerFeasible {n : ℕ} {S : Set (Fin n → ℝ)}
    (hcl : IsClosed S) (hcv : Convex ℝ S) (h0 : (0 : Fin n → ℝ) ∈ S)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (hf : InnerFeasible (polarSet S) A b) : ellipsoid Aᵀ b ⊆ S := by
  rintro x ⟨v,hv,rfl⟩
  apply mem_of_polar_constraints hcl hcv h0
  intro u hu
  have hh := (ball_dot_iff (A *ᵥ u) (1-b ⬝ᵥ u)).mpr (hf u hu) v hv
  rw [dot_affine_transpose]
  linarith

end ModernConvex.Ellipsoids.Fresh
end

section
open Matrix Finset
open scoped Matrix.Norms.Elementwise
namespace ModernConvex.Ellipsoids.Fresh

abbrev AffineParam (n : ℕ) := Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)

def innerFeasible {n : ℕ} (S : Set (Fin n → ℝ)) : Set (AffineParam n) :=
  {p | ∀ u ∈ unitBall n, p.1 *ᵥ u + p.2 ∈ S}

def outerFeasible {n : ℕ} (S : Set (Fin n → ℝ)) : Set (AffineParam n) :=
  {p | ∀ x ∈ S, p.1 *ᵥ x + p.2 ∈ unitBall n}

lemma continuous_affine_eval {n : ℕ} (u : Fin n → ℝ) :
    Continuous (fun p : AffineParam n => p.1 *ᵥ u + p.2) := by
  unfold Matrix.mulVec dotProduct
  fun_prop

lemma innerFeasible_closed {n : ℕ} {S : Set (Fin n → ℝ)} (hS : IsClosed S) :
    IsClosed (innerFeasible S) := by
  have he : innerFeasible S = ⋂ u ∈ unitBall n,
      (fun p : AffineParam n => p.1 *ᵥ u + p.2) ⁻¹' S := by
    ext p
    simp [innerFeasible]
  rw [he]
  exact isClosed_iInter (fun u => isClosed_iInter (fun _ => hS.preimage (continuous_affine_eval u)))

lemma outerFeasible_closed {n : ℕ} (S : Set (Fin n → ℝ)) :
    IsClosed (outerFeasible S) := by
  have he : outerFeasible S = ⋂ x ∈ S,
      (fun p : AffineParam n => p.1 *ᵥ x + p.2) ⁻¹' unitBall n := by
    ext p
    simp [outerFeasible]
  rw [he]
  exact isClosed_iInter (fun x => isClosed_iInter (fun _ =>
    (unitBall_closed n).preimage (continuous_affine_eval x)))

lemma single_mem_unitBall {n : ℕ} (j : Fin n) :
    (Pi.single j 1 : Fin n → ℝ) ∈ unitBall n := by
  simp [unitBall, dotProduct_single]

lemma innerFeasible_bounded {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS : Bornology.IsBounded S) : Bornology.IsBounded (innerFeasible S) := by
  obtain ⟨R,hR⟩ := hS.exists_norm_le
  let M := max R 0
  have hM : 0 ≤ M := le_max_right _ _
  have hRM : R ≤ M := le_max_left _ _
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨2*M,?_⟩
  intro p hp
  have hc : ‖p.2‖ ≤ M := by
    have h0 := hp 0 (zero_mem_unitBall n)
    simp only [Matrix.mulVec_zero, zero_add] at h0
    exact (hR _ h0).trans hRM
  have hA : ‖p.1‖ ≤ 2*M := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : (0:ℝ) ≤ 2*M)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity : (0:ℝ) ≤ 2*M)).mpr
    intro j
    have hj := hR _ (hp (Pi.single j 1) (single_mem_unitBall j))
    have hij := (norm_le_pi_norm (p.1 *ᵥ Pi.single j 1 + p.2) i).trans (hj.trans hRM)
    have hci := (norm_le_pi_norm p.2 i).trans hc
    have he : p.1 i j = (p.1 *ᵥ Pi.single j 1 + p.2) i - p.2 i := by
      simp
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith)
  rw [Prod.norm_def]
  exact max_le hA (by linarith)

lemma innerFeasible_compact {n : ℕ} {S : Set (Fin n → ℝ)} (hS : IsSolid S) :
    IsCompact (innerFeasible S) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨innerFeasible_closed hS.1,innerFeasible_bounded hS.2.1⟩

end ModernConvex.Ellipsoids.Fresh
end

section
open Matrix Finset
namespace ModernConvex.Ellipsoids.Fresh

lemma solid_contains_closedBall {n : ℕ} {S : Set (Fin n → ℝ)} (hS : IsSolid S) :
    ∃ x : Fin n → ℝ, ∃ r : ℝ, 0 < r ∧ Metric.closedBall x r ⊆ S := by
  obtain ⟨x,hx⟩ := hS.2.2.2
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  exact ⟨x,ε/2,by positivity,(Metric.closedBall_subset_ball (by linarith)).trans hsub⟩

lemma solid_basis_points {n : ℕ} {S : Set (Fin n → ℝ)} (hS : IsSolid S) :
    ∃ x : Fin n → ℝ, ∃ r : ℝ, 0 < r ∧ x ∈ S ∧
      ∀ j : Fin n, x + r • Pi.single j 1 ∈ S := by
  obtain ⟨x,r,hr,hsub⟩ := solid_contains_closedBall hS
  refine ⟨x,r,hr,hsub (Metric.mem_closedBall_self hr.le),?_⟩
  intro j
  apply hsub
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
  simp [Real.norm_eq_abs, abs_of_pos hr, Pi.norm_single]

lemma innerFeasible_nonsingular {n : ℕ} {S : Set (Fin n → ℝ)} (hS : IsSolid S) :
    ∃ p ∈ innerFeasible S, p.1.det ≠ 0 := by
  obtain ⟨x,r,hr,hsub⟩ := solid_contains_closedBall hS
  refine ⟨(r • (1 : Matrix (Fin n) (Fin n) ℝ),x),?_,?_⟩
  · intro u hu
    apply hsub
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, add_sub_cancel_right]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hn : ‖u‖ ≤ 1 := (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
      (fun i => by simpa only [Real.norm_eq_abs] using unitBall_coord hu i)
    nlinarith
  · simp [ne_of_gt hr]

end ModernConvex.Ellipsoids.Fresh
end

section
open Matrix Finset
open scoped Matrix.Norms.Elementwise
namespace ModernConvex.Ellipsoids.Fresh

lemma outerFeasible_bounded {n : ℕ} {S : Set (Fin n → ℝ)} (hS : IsSolid S) :
    Bornology.IsBounded (outerFeasible S) := by
  obtain ⟨x,r,hr,hx,hbasis⟩ := solid_basis_points hS
  let C : ℝ := 2/r
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let D : ℝ := 1 + C * ∑ j, |x j|
  have hD : 0 ≤ D := by dsimp [D]; positivity
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max C D,?_⟩
  intro p hp
  have hbase : ∀ i, |(p.1 *ᵥ x+p.2) i| ≤ 1 :=
    fun i => unitBall_coord (hp x hx) i
  have hentry : ∀ i j, |p.1 i j| ≤ C := by
    intro i j
    have hshift := unitBall_coord (hp _ (hbasis j)) i
    have hid : (p.1 *ᵥ (x+r • Pi.single j 1)+p.2) i =
        (p.1 *ᵥ x+p.2) i + r * p.1 i j := by
      simp [Matrix.mulVec_add, Matrix.mulVec_smul]
      ring
    rw [hid] at hshift
    have he : |r * p.1 i j| ≤ 2 := by
      have ht := abs_sub ((p.1 *ᵥ x+p.2) i+r*p.1 i j) ((p.1 *ᵥ x+p.2) i)
      have hh := hbase i
      simp only [add_sub_cancel_left] at ht
      linarith
    rw [abs_mul, abs_of_pos hr] at he
    exact (le_div_iff₀ hr).mpr (by nlinarith)
  have hA : ‖p.1‖ ≤ C :=
    (pi_norm_le_iff_of_nonneg hC).mpr (fun i =>
      (pi_norm_le_iff_of_nonneg hC).mpr (fun j => by simpa using hentry i j))
  have hc : ‖p.2‖ ≤ D := by
    apply (pi_norm_le_iff_of_nonneg hD).mpr
    intro i
    have hm : |(p.1 *ᵥ x) i| ≤ C * ∑ j, |x j| := by
      calc
        _ = |∑ j, p.1 i j * x j| := rfl
        _ ≤ ∑ j, |p.1 i j * x j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, C * |x j| := Finset.sum_le_sum (fun j _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hentry i j) (abs_nonneg _))
        _ = _ := (Finset.mul_sum _ _ _).symm
    have ht := abs_sub ((p.1 *ᵥ x+p.2) i) ((p.1 *ᵥ x) i)
    have hh := hbase i
    simp only [Pi.add_apply] at hh
    simp only [Pi.add_apply, add_sub_cancel_left] at ht
    rw [Real.norm_eq_abs]
    dsimp [D]
    linarith
  rw [Prod.norm_def]
  exact max_le_max hA hc

lemma outerFeasible_compact {n : ℕ} {S : Set (Fin n → ℝ)} (hS : IsSolid S) :
    IsCompact (outerFeasible S) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨outerFeasible_closed S,outerFeasible_bounded hS⟩

end ModernConvex.Ellipsoids.Fresh
end

section
open Matrix Finset
namespace ModernConvex.Ellipsoids.Fresh

lemma unitBall_of_coord_bound {n : ℕ} {u : Fin n → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hnr : (n:ℝ)*r^2 ≤ 1) (hu : ∀ i, |u i| ≤ r) : u ∈ unitBall n := by
  have hs : (∑ i, u i*u i) ≤ ∑ _i : Fin n, r^2 := by
    apply Finset.sum_le_sum
    intro i hi
    have hh := (sq_le_sq₀ (abs_nonneg (u i)) hr).mpr (hu i)
    rw [sq_abs] at hh
    simpa only [pow_two] using hh
  have he : (∑ _i : Fin n, r^2) = (n:ℝ)*r^2 := by simp
  change (∑ i, u i*u i) ≤ 1
  rw [he] at hs
  exact hs.trans hnr

lemma outerFeasible_nonsingular {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS : Bornology.IsBounded S) : ∃ p ∈ outerFeasible S, p.1.det ≠ 0 := by
  obtain ⟨R,hR⟩ := hS.exists_norm_le
  let M := max R 1
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hn : 0 < (n:ℝ)+1 := by positivity
  let r : ℝ := 1 / (((n:ℝ)+1)*M)
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨(r • (1 : Matrix (Fin n) (Fin n) ℝ),0),?_,?_⟩
  · intro x hx
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, add_zero]
    apply unitBall_of_coord_bound (r := 1/((n:ℝ)+1)) (by positivity)
    · have hh : (n:ℝ) / ((n:ℝ)+1)^2 ≤ 1 :=
        (div_le_one (sq_pos_of_pos hn)).mpr (by nlinarith [sq_nonneg (n:ℝ)])
      simpa only [one_div, inv_pow, div_eq_mul_inv, one_mul] using hh
    · intro i
      change |r*x i| ≤ _
      rw [abs_mul, abs_of_pos hr]
      have hxM : |x i| ≤ M := by
        exact (norm_le_pi_norm x i).trans ((hR x hx).trans (le_max_left _ _))
      calc
        r*|x i| ≤ r*M := mul_le_mul_of_nonneg_left hxM hr.le
        _ = 1/((n:ℝ)+1) := by dsimp [r]; field_simp
  · simp [ne_of_gt hr]

end ModernConvex.Ellipsoids.Fresh
end

section
open Matrix MeasureTheory
open scoped ENNReal
namespace ModernConvex.Ellipsoids.Fresh

lemma volume_translate {n : ℕ} (S : Set (Fin n → ℝ)) (c : Fin n → ℝ) :
    volume ((fun x => x+c) '' S) = volume S := by
  have he : (fun x => x+c) '' S = (fun x => x+(-c)) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa using hy
    · intro hx
      exact ⟨x+(-c), hx, by simp⟩
  rw [he, measure_preimage_add_right]

lemma ellipsoid_image {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    ellipsoid A c = (fun x => x+c) '' (Matrix.toLin' A '' unitBall n) := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨A *ᵥ u, ⟨u,hu,rfl⟩, rfl⟩
  · rintro ⟨v,⟨u,hu,rfl⟩,rfl⟩
    exact ⟨u,hu,rfl⟩

lemma volume_ellipsoid {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    volume (ellipsoid A c) = ENNReal.ofReal |A.det| * volume (unitBall n) := by
  rw [ellipsoid_image, volume_translate, Measure.addHaar_image_linearMap]
  simp only [LinearMap.det_toLin']

lemma Vol_ellipsoid {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    Vol (ellipsoid A c) = ENNReal.ofReal |A.det| := by
  unfold Vol
  rw [volume_ellipsoid]
  exact ENNReal.mul_div_cancel_right (volume_unitBall_pos n).ne' (volume_unitBall_ne_top n)

lemma ellipsoid_compact {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    IsCompact (ellipsoid A c) := by
  rw [ellipsoid_image]
  apply IsCompact.image
  · exact (unitBall_compact n).image (Matrix.toLin' A).continuous_of_finiteDimensional
  · fun_prop

end ModernConvex.Ellipsoids.Fresh
end

section
open Matrix
namespace ModernConvex.Ellipsoids.Fresh

lemma exists_inner_det_max {n : ℕ} {S : Set (Fin n → ℝ)} (hS : IsSolid S) :
    ∃ p ∈ innerFeasible S, p.1.det ≠ 0 ∧
      ∀ q ∈ innerFeasible S, |q.1.det| ≤ |p.1.det| := by
  obtain ⟨p0,hp0,hd0⟩ := innerFeasible_nonsingular hS
  have hc : Continuous (fun p : AffineParam n => |p.1.det|) := by fun_prop
  obtain ⟨p,hp,hmax⟩ := (innerFeasible_compact hS).exists_isMaxOn ⟨p0,hp0⟩ hc.continuousOn
  refine ⟨p,hp,?_,fun _ hq => hmax hq⟩
  have hh := (abs_pos.mpr hd0).trans_le (hmax hp0)
  exact abs_pos.mp hh

lemma exists_outer_det_max {n : ℕ} {S : Set (Fin n → ℝ)} (hS : IsSolid S) :
    ∃ p ∈ outerFeasible S, p.1.det ≠ 0 ∧
      ∀ q ∈ outerFeasible S, |q.1.det| ≤ |p.1.det| := by
  obtain ⟨p0,hp0,hd0⟩ := outerFeasible_nonsingular hS.2.1
  have hc : Continuous (fun p : AffineParam n => |p.1.det|) := by fun_prop
  obtain ⟨p,hp,hmax⟩ := (outerFeasible_compact hS).exists_isMaxOn ⟨p0,hp0⟩ hc.continuousOn
  refine ⟨p,hp,?_,fun _ hq => hmax hq⟩
  have hh := (abs_pos.mpr hd0).trans_le (hmax hp0)
  exact abs_pos.mp hh

lemma exists_maxVolInscribed {n : ℕ} {S : Set (Fin n → ℝ)} (hS : IsSolid S) :
    ∃ E, IsMaxVolInscribed S E := by
  obtain ⟨p,hp,hd,hmax⟩ := exists_inner_det_max hS
  refine ⟨ellipsoid p.1 p.2, ⟨p.1,p.2,hd,rfl⟩, ?_, ?_⟩
  · rintro x ⟨u,hu,rfl⟩
    exact hp u hu
  · intro E hE hES
    obtain ⟨A,c,hA,rfl⟩ := hE
    rw [Vol_ellipsoid, Vol_ellipsoid]
    apply ENNReal.ofReal_le_ofReal
    apply hmax (A,c)
    intro u hu
    exact hES ⟨u,hu,rfl⟩

end ModernConvex.Ellipsoids.Fresh
end

section
open Matrix
namespace ModernConvex.Ellipsoids.Fresh

lemma mem_ellipsoid_iff_inverse {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.det ≠ 0) (c x : Fin n → ℝ) :
    x ∈ ellipsoid A c ↔ A⁻¹ *ᵥ (x-c) ∈ unitBall n := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  constructor
  · rintro ⟨u,huB,rfl⟩
    rw [add_sub_cancel_right, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hu, Matrix.one_mulVec]
    exact huB

  · intro hx
    refine ⟨A⁻¹ *ᵥ (x-c),hx,?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hu, Matrix.one_mulVec,
      sub_add_cancel]

lemma outerFeasible_inverse_contains {n : ℕ} {S : Set (Fin n → ℝ)}
    {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ}
    (hA : A.det ≠ 0) (hf : (A,b) ∈ outerFeasible S) :
    S ⊆ ellipsoid A⁻¹ (-(A⁻¹ *ᵥ b)) := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  intro x hx
  refine ⟨A *ᵥ x+b,hf x hx,?_⟩
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hu,
    Matrix.one_mulVec, add_neg_cancel_right]

lemma inverse_outerFeasible {n : ℕ} {S : Set (Fin n → ℝ)}
    {A : Matrix (Fin n) (Fin n) ℝ} {c : Fin n → ℝ}
    (hA : A.det ≠ 0) (hsub : S ⊆ ellipsoid A c) :
    (A⁻¹,-(A⁻¹ *ᵥ c)) ∈ outerFeasible S := by
  intro x hx
  have hh := (mem_ellipsoid_iff_inverse hA c x).mp (hsub hx)
  rw [Matrix.mulVec_sub] at hh
  simpa only [sub_eq_add_neg] using hh

lemma exists_minVolCircumscribed {n : ℕ} {S : Set (Fin n → ℝ)} (hS : IsSolid S) :
    ∃ E, IsMinVolCircumscribed S E := by
  obtain ⟨p,hp,hd,hmax⟩ := exists_outer_det_max hS
  have hdi : p.1⁻¹.det ≠ 0 := by simp [Matrix.det_nonsing_inv,hd]
  refine ⟨ellipsoid p.1⁻¹ (-(p.1⁻¹ *ᵥ p.2)),
    ⟨p.1⁻¹,-(p.1⁻¹ *ᵥ p.2),hdi,rfl⟩,
    outerFeasible_inverse_contains hd hp,?_⟩
  intro E hE hSE
  obtain ⟨A,c,hA,rfl⟩ := hE
  have hh := hmax (A⁻¹,-(A⁻¹ *ᵥ c)) (inverse_outerFeasible hA hSE)
  simp only [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, abs_inv] at hh
  rw [Vol_ellipsoid, Vol_ellipsoid]
  apply ENNReal.ofReal_le_ofReal
  simp only [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, abs_inv]
  exact (inv_le_comm₀ (abs_pos.mpr hd) (abs_pos.mpr hA)).mpr hh

end ModernConvex.Ellipsoids.Fresh
end

section
open Matrix
namespace ModernConvex.Ellipsoids.Fresh

lemma ellipsoid_one_zero (n : ℕ) :
    ellipsoid (1 : Matrix (Fin n) (Fin n) ℝ) 0 = unitBall n := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    simpa only [Matrix.one_mulVec, add_zero] using (show u ∈ unitBall n from hu)
  · intro hx
    exact ⟨x,hx,by simp⟩

lemma Vol_unitBall (n : ℕ) : Vol (unitBall n) = 1 := by
  rw [← ellipsoid_one_zero n, Vol_ellipsoid]
  simp

lemma native_innerOptimal {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS : IsSolid S) (hmax : IsMaxVolInscribed S (unitBall n)) :
    InnerOptimal (polarSet S) := by
  intro A b hf
  by_cases hd : A.det = 0
  · simp [hd]
  have hdt : Aᵀ.det ≠ 0 := by simpa using hd
  have hsub := containment_of_innerFeasible hS.1 hS.2.2.1
    (hmax.2.1 (zero_mem_unitBall n)) A b hf
  have hh := hmax.2.2 (ellipsoid Aᵀ b) ⟨Aᵀ,b,hdt,rfl⟩ hsub
  rw [Vol_ellipsoid, Vol_unitBall, Matrix.det_transpose] at hh
  exact ENNReal.ofReal_le_one.mp hh

lemma native_outerOptimal {n : ℕ} {S : Set (Fin n → ℝ)}
    (hmin : IsMinVolCircumscribed S (unitBall n)) : OuterOptimal S := by
  intro A b hf
  by_cases hd : A.det = 0
  · simp [hd]
  have hdi : A⁻¹.det ≠ 0 := by simp [Matrix.det_nonsing_inv,hd]
  have hsub : S ⊆ ellipsoid A⁻¹ (-(A⁻¹ *ᵥ b)) :=
    outerFeasible_inverse_contains hd hf
  have hh := hmin.2.2 (ellipsoid A⁻¹ (-(A⁻¹ *ᵥ b)))
    ⟨A⁻¹,-(A⁻¹ *ᵥ b),hdi,rfl⟩ hsub
  rw [Vol_unitBall, Vol_ellipsoid] at hh
  have hi := ENNReal.one_le_ofReal.mp hh
  simp only [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, abs_inv] at hi
  exact (one_le_inv₀ (abs_pos.mpr hd)).mp hi

end ModernConvex.Ellipsoids.Fresh
end

section

open Set
namespace ModernConvex.Ellipsoids.Fresh

lemma compact_quadratic_perturbation {E : Type*} [TopologicalSpace E]
    {T : Set E} (hT : IsCompact T) (f g r : E → ℝ)
    (hf : ContinuousOn f T) (hg : ContinuousOn g T) (hr : ContinuousOn r T)
    (hf0 : ∀ x ∈ T, f x ≤ 0) (hactive : ∀ x ∈ T, f x = 0 → g x < 0) :
    ∃ e : ℝ, 0 < e ∧ ∀ t, 0 ≤ t → t ≤ e →
      ∀ x ∈ T, f x + t * g x + t ^ 2 * r x ≤ 0 := by
  by_cases hne : T.Nonempty
  · obtain ⟨x₀,hx₀,hmin⟩ := hT.exists_isMinOn hne (fun x hx => (hf x hx).neg.max (hg x hx).neg)
    let d := max (-f x₀) (-g x₀)
    have hd : 0 < d := by
      by_cases hzero : f x₀ = 0
      · exact lt_of_lt_of_le (neg_pos.mpr (hactive x₀ hx₀ hzero)) (le_max_right _ _)
      · exact lt_of_lt_of_le (neg_pos.mpr (lt_of_le_of_ne (hf0 x₀ hx₀) hzero))
          (le_max_left _ _)
    obtain ⟨M,hM⟩ := hT.bddAbove_image (hg.abs.add hr.abs)
    let B := max M 0 + 1
    have hB : 0 < B := by dsimp [B]; positivity
    have hb (x) (hx : x ∈ T) : |g x| + |r x| ≤ B := by
      have := hM (mem_image_of_mem (fun x => |g x| + |r x|) hx)
      dsimp [B]
      linarith [le_max_left M 0]
    refine ⟨min 1 (d / B), lt_min zero_lt_one (div_pos hd hB), ?_⟩
    intro t ht hte x hx
    have ht1 : t ≤ 1 := hte.trans (min_le_left _ _)
    have htd : t * B ≤ d := (le_div_iff₀ hB).mp (hte.trans (min_le_right _ _))
    have hxsplit : f x ≤ -d ∨ g x ≤ -d := by
      have hm : d ≤ max (-f x) (-g x) := hmin hx
      rcases le_max_iff.mp hm with h | h
      · left; linarith
      · right; linarith
    have hfg := hf0 x hx
    have hgb : g x ≤ B := (le_abs_self _).trans (by linarith [hb x hx, abs_nonneg (r x)])
    have hrb : r x ≤ B := (le_abs_self _).trans (by linarith [hb x hx, abs_nonneg (g x)])
    have htr : t * r x ≤ d := (mul_le_mul_of_nonneg_left hrb ht).trans htd
    rcases hxsplit with hlow | hlow
    · have htrabs : t ^ 2 * r x ≤ t * |r x| := by
        calc
          t ^ 2 * r x ≤ t ^ 2 * |r x| := mul_le_mul_of_nonneg_left (le_abs_self _) (sq_nonneg _)
          _ ≤ t * |r x| := mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg _)
      have htg : t * g x ≤ t * |g x| := mul_le_mul_of_nonneg_left (le_abs_self _) ht
      have htotal := mul_le_mul_of_nonneg_left (hb x hx) ht
      nlinarith
    · have := mul_le_mul_of_nonneg_left hlow ht
      have := mul_le_mul_of_nonneg_left htr ht
      nlinarith
  · refine ⟨1,zero_lt_one,?_⟩
    intro t ht hte x hx
    exact (hne ⟨x,hx⟩).elim

end ModernConvex.Ellipsoids.Fresh
end

section

open Matrix Polynomial Filter Topology
namespace ModernConvex.Ellipsoids.Fresh

lemma det_variation_derivative {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • H).det) H.trace 0 := by
  let p : ℝ[X] := (1 + (X : ℝ[X]) • H.map C).det
  have hp := p.hasDerivAt (0 : ℝ)
  have hd : p.derivative.eval 0 = H.trace := Matrix.derivative_det_one_add_X_smul H
  rw [hd] at hp
  have heq : (fun t : ℝ => (1 + t • H).det) = (fun t => p.eval t) := by
    funext t
    dsimp [p]
    change (1 + t • H).det = (Polynomial.evalRingHom t) ((1 + (X : ℝ[X]) • H.map C).det)
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
    simp only [Polynomial.coe_evalRingHom]
    split_ifs <;> simp only [smul_eq_mul, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_one, Polynomial.eval_zero, Polynomial.eval_X, Polynomial.eval_C]
  rw [heq]
  exact hp

lemma exists_det_improvement {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : 0 < H.trace) {e : ℝ} (he : 0 < e) :
    ∃ t : ℝ, 0 < t ∧ t ≤ e ∧ 1 < (1 + t • H).det := by
  have hd := (det_variation_derivative H).tendsto_slope_zero_right
  have hpos := hd.eventually (eventually_gt_nhds hH)
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < e :=
    (eventually_lt_nhds he).filter_mono nhdsWithin_le_nhds
  have htpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t,ht,hte,hv⟩ := (htpos.and (hsmall.and hpos)).exists
  refine ⟨t,ht,hte.le,?_⟩
  simp only [zero_add, zero_smul, add_zero, det_one, smul_eq_mul] at hv
  have ht' : 0 < t⁻¹ := inv_pos.mpr ht
  exact sub_pos.mp ((mul_pos_iff_of_pos_left ht').mp hv)

end ModernConvex.Ellipsoids.Fresh
end

section

open Matrix
namespace ModernConvex.Ellipsoids.Fresh

lemma outer_perturbation_expansion {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (b u : Fin n → ℝ) (t : ℝ) :
    ((1 + t • H) *ᵥ u + t • b) ⬝ᵥ ((1 + t • H) *ᵥ u + t • b) - 1 =
      (u ⬝ᵥ u - 1) + t * (2 * (u ⬝ᵥ (H *ᵥ u) + b ⬝ᵥ u)) +
        t ^ 2 * ((H *ᵥ u + b) ⬝ᵥ (H *ᵥ u + b)) := by
  simp only [add_mulVec, one_mulVec, smul_mulVec, dotProduct_add, add_dotProduct,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm (H *ᵥ u) u, dotProduct_comm u b,
    dotProduct_comm (H *ᵥ u) b]
  ring

lemma inner_perturbation_expansion {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (b u : Fin n → ℝ) (t : ℝ) :
    ((1 + t • H) *ᵥ u) ⬝ᵥ ((1 + t • H) *ᵥ u) - (1 - (t • b) ⬝ᵥ u) ^ 2 =
      (u ⬝ᵥ u - 1) + t * (2 * (u ⬝ᵥ (H *ᵥ u) + b ⬝ᵥ u)) +
        t ^ 2 * ((H *ᵥ u) ⬝ᵥ (H *ᵥ u) - (b ⬝ᵥ u) ^ 2) := by
  simp only [add_mulVec, one_mulVec, smul_mulVec, dotProduct_add, add_dotProduct,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm (H *ᵥ u) u]
  ring

lemma strict_contact_outer_improvement {n : ℕ} {T : Set (Fin n → ℝ)}
    (hT : IsCompact T) (hTB : T ⊆ unitBall n)
    (H : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (htr : 0 < H.trace)
    (hcontact : ∀ u ∈ T, u ⬝ᵥ u = 1 → u ⬝ᵥ (H *ᵥ u) + b ⬝ᵥ u < 0) :
    ∃ A c, OuterFeasible T A c ∧ 1 < A.det := by
  obtain ⟨e,he,hstep⟩ := compact_quadratic_perturbation hT
    (fun u => u ⬝ᵥ u - 1) (fun u => 2 * (u ⬝ᵥ (H *ᵥ u) + b ⬝ᵥ u))
    (fun u => (H *ᵥ u + b) ⬝ᵥ (H *ᵥ u + b))
    (by unfold dotProduct; fun_prop) (by unfold dotProduct mulVec; fun_prop)
    (by unfold dotProduct mulVec; fun_prop)
    (fun u hu => sub_nonpos.mpr (hTB hu))
    (fun u hu hzero => by have := hcontact u hu (sub_eq_zero.mp hzero); linarith)
  obtain ⟨t,ht,hte,hdet⟩ := exists_det_improvement H htr he
  refine ⟨1 + t • H,t • b,?_,hdet⟩
  intro u hu
  have hq := hstep t ht.le hte u hu
  rw [← outer_perturbation_expansion] at hq
  linarith

lemma strict_contact_inner_improvement {n : ℕ} {T : Set (Fin n → ℝ)}
    (hT : IsCompact T) (hTB : T ⊆ unitBall n)
    (H : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (htr : 0 < H.trace)
    (hcontact : ∀ u ∈ T, u ⬝ᵥ u = 1 → u ⬝ᵥ (H *ᵥ u) + b ⬝ᵥ u < 0) :
    ∃ A c, InnerFeasible T A c ∧ 1 < A.det := by
  obtain ⟨e,he,hstep⟩ := compact_quadratic_perturbation hT
    (fun u => u ⬝ᵥ u - 1) (fun u => 2 * (u ⬝ᵥ (H *ᵥ u) + b ⬝ᵥ u))
    (fun u => (H *ᵥ u) ⬝ᵥ (H *ᵥ u) - (b ⬝ᵥ u) ^ 2)
    (by unfold dotProduct; fun_prop) (by unfold dotProduct mulVec; fun_prop)
    (by unfold dotProduct mulVec; fun_prop)
    (fun u hu => sub_nonpos.mpr (hTB hu))
    (fun u hu hzero => by have := hcontact u hu (sub_eq_zero.mp hzero); linarith)
  obtain ⟨e',he',hbase⟩ := compact_quadratic_perturbation hT
    (fun _ => (-1 : ℝ)) (fun u => b ⬝ᵥ u) (fun _ => (0 : ℝ))
    continuousOn_const (by unfold dotProduct; fun_prop) continuousOn_const
    (by intros; norm_num) (by intros; norm_num at *)
  obtain ⟨t,ht,hte,hdet⟩ := exists_det_improvement H htr (lt_min he he')
  refine ⟨1 + t • H,t • b,?_,hdet⟩
  intro u hu
  constructor
  · have hb := hbase t ht.le (hte.trans (min_le_right _ _)) u hu
    simp only [smul_dotProduct, smul_eq_mul]
    nlinarith
  · have hq := hstep t ht.le (hte.trans (min_le_left _ _)) u hu
    rw [← inner_perturbation_expansion] at hq
    linarith

end ModernConvex.Ellipsoids.Fresh
end

section

open Matrix
namespace ModernConvex.Ellipsoids.Fresh

lemma contact_moments_of_no_direction {n : ℕ} (hn : 0 < n) {T : Set (Fin n → ℝ)}
    (hno : ∀ H b, 0 < H.trace →
      ¬ (∀ u ∈ T, u ⬝ᵥ u = 1 → u ⬝ᵥ (H *ᵥ u) + b ⬝ᵥ u < 0)) :
    ContactMoments T := by
  intro H b hcontact
  by_contra! htr
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let e : ℝ := -H.trace / (2 * n)
  have he : 0 < e := div_pos (neg_pos.mpr htr) (by positivity)
  have hen : e * n = -H.trace / 2 := by
    dsimp [e]
    field_simp
  let K : Matrix (Fin n) (Fin n) ℝ := -H - e • 1
  have hKt : 0 < K.trace := by
    simp only [K, trace_sub, trace_neg, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
    nlinarith
  apply hno K (-b) hKt
  intro u hu hunit
  have hc := hcontact u hu hunit
  dsimp [K]
  simp only [sub_mulVec, neg_mulVec, smul_mulVec, one_mulVec,
    dotProduct_sub, dotProduct_neg, dotProduct_smul, neg_dotProduct, smul_eq_mul, hunit]
  linarith

lemma outerOptimal_contactMoments {n : ℕ} (hn : 0 < n) {T : Set (Fin n → ℝ)}
    (hT : IsCompact T) (hTB : T ⊆ unitBall n) (hopt : OuterOptimal T) :
    ContactMoments T := by
  apply contact_moments_of_no_direction hn
  intro H b htr hc
  obtain ⟨A,c,hf,hd⟩ := strict_contact_outer_improvement hT hTB H b htr hc
  have := hopt A c hf
  linarith [le_abs_self A.det]

lemma innerOptimal_contactMoments {n : ℕ} (hn : 0 < n) {T : Set (Fin n → ℝ)}
    (hT : IsCompact T) (hTB : T ⊆ unitBall n) (hopt : InnerOptimal T) :
    ContactMoments T := by
  apply contact_moments_of_no_direction hn
  intro H b htr hc
  obtain ⟨A,c,hf,hd⟩ := strict_contact_inner_improvement hT hTB H b htr hc
  have := hopt A c hf
  linarith [le_abs_self A.det]

end ModernConvex.Ellipsoids.Fresh
end

section

open Matrix
namespace ModernConvex.Ellipsoids.Fresh

lemma contact_scalar_quadratic {n : ℕ} {T : Set (Fin n → ℝ)}
    (hT : ContactMoments T) (x : Fin n → ℝ) (a b c : ℝ)
    (hp : ∀ u ∈ T, u ⬝ᵥ u = 1 →
      0 ≤ a + b * (x ⬝ᵥ u) + c * (x ⬝ᵥ u) ^ 2) :
    0 ≤ a * (n : ℝ) + c * (x ⬝ᵥ x) := by
  have h := hT (a • (1 : Matrix (Fin n) (Fin n) ℝ) + c • vecMulVec x x) (b • x) (by
    intro u hu huu
    have hp' := hp u hu huu
    simpa [add_mulVec, smul_mulVec, one_mulVec, vecMulVec_mulVec,
      op_smul_eq_smul, dotProduct_add, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      dotProduct_comm u x, huu, pow_two, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc] using hp')
  simpa [trace_add, trace_smul, trace_one, trace_vecMulVec, smul_eq_mul] using h

lemma contact_symmetric_inner_bound {n : ℕ} {T : Set (Fin n → ℝ)}
    (hT : ContactMoments T) (x : Fin n → ℝ)
    (hx : ∀ u ∈ T, u ⬝ᵥ u = 1 → |x ⬝ᵥ u| ≤ 1) :
    x ⬝ᵥ x ≤ (n : ℝ) := by
  have h := contact_scalar_quadratic hT x 1 0 (-1) (by
    intro u hu huu
    have ht := abs_le.mp (hx u hu huu)
    nlinarith [sq_nonneg (x ⬝ᵥ u), mul_nonneg (by linarith : 0 ≤ 1 - x ⬝ᵥ u)
      (by linarith : 0 ≤ 1 + x ⬝ᵥ u)])
  linarith

lemma contact_symmetric_outer_bound {n : ℕ} {T : Set (Fin n → ℝ)}
    (hT : ContactMoments T) (v : Fin n → ℝ) (hv : v ⬝ᵥ v = 1)
    (h : ℝ)
    (hvT : ∀ u ∈ T, u ⬝ᵥ u = 1 → |v ⬝ᵥ u| ≤ h) :
    1 ≤ (n : ℝ) * h ^ 2 := by
  have hm := contact_scalar_quadratic hT v (h ^ 2) 0 (-1) (by
    intro u hu huu
    have ht := abs_le.mp (hvT u hu huu)
    nlinarith [mul_nonneg (by linarith : 0 ≤ h - v ⬝ᵥ u)
      (by linarith : 0 ≤ h + v ⬝ᵥ u)])
  rw [hv] at hm
  nlinarith

end ModernConvex.Ellipsoids.Fresh
end

section

open Matrix
namespace ModernConvex.Ellipsoids.Fresh

lemma scalar_dot_self_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ x := by
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

lemma scalar_unit_cauchy {n : ℕ} (x u : Fin n → ℝ) (hu : u ⬝ᵥ u = 1) :
    (x ⬝ᵥ u) ^ 2 ≤ x ⬝ᵥ x := by
  have h := scalar_dot_self_nonneg (x - (x ⬝ᵥ u) • u)
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, hu, dotProduct_comm u x] at h
  nlinarith

lemma contact_inner_bound {n : ℕ} {T : Set (Fin n → ℝ)}
    (hT : ContactMoments T) (x : Fin n → ℝ)
    (hx : ∀ u ∈ T, u ⬝ᵥ u = 1 → x ⬝ᵥ u ≤ 1) :
    x ⬝ᵥ x ≤ (n : ℝ) ^ 2 := by
  let r := Real.sqrt (x ⬝ᵥ x)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = x ⬝ᵥ x := Real.sq_sqrt (scalar_dot_self_nonneg x)
  have hm := contact_scalar_quadratic hT x r (1 - r) (-1) (by
    intro u hu huu
    have ht := hx u hu huu
    have hcs := scalar_unit_cauchy x u huu
    have hlo : 0 ≤ r + x ⬝ᵥ u := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) hlo])
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hrn : r ≤ (n : ℝ) := by nlinarith
  nlinarith

lemma contact_outer_bound {n : ℕ} {T : Set (Fin n → ℝ)}
    (hT : ContactMoments T) (v : Fin n → ℝ) (hv : v ⬝ᵥ v = 1)
    (h : ℝ) (hvT : ∀ u ∈ T, u ⬝ᵥ u = 1 → v ⬝ᵥ u ≤ h) :
    1 ≤ (n : ℝ) * h := by
  have hm := contact_scalar_quadratic hT v h (h - 1) (-1) (by
    intro u hu huu
    have ht := hvT u hu huu
    have hcs := scalar_unit_cauchy v u huu
    rw [hv] at hcs
    have hlo : 0 ≤ 1 + v ⬝ᵥ u := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) hlo])
  rw [hv] at hm
  nlinarith

end ModernConvex.Ellipsoids.Fresh
end

section

open Matrix
namespace ModernConvex.Ellipsoids.Fresh

lemma positive_product_le_one_of_sum_le {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (hs : ∑ i, x i ≤ (n : ℝ)) : ∏ i, x i ≤ 1 := by
  have hp : 0 < ∏ i, x i := Finset.prod_pos (fun i _ => hx i)
  apply (Real.log_nonpos_iff hp.le).mp
  rw [Real.log_prod (fun i _ => (hx i).ne')]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => Real.log_le_sub_one_of_pos (hx i))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  linarith

lemma positive_eq_one_of_product_one_sum_le {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (hs : ∑ i, x i ≤ (n : ℝ))
    (hp : ∏ i, x i = 1) : ∀ i, x i = 1 := by
  have hlog : ∑ i, Real.log (x i) = 0 := by
    rw [← Real.log_prod (fun i _ => (hx i).ne'), hp, Real.log_one]
  have hd : ∀ i, 0 ≤ x i - 1 - Real.log (x i) := by
    intro i
    linarith [Real.log_le_sub_one_of_pos (hx i)]
  have hz : ∑ i, (x i - 1 - Real.log (x i)) = 0 := by
    have hnon := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hd i)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, hlog] at hnon ⊢
    linarith
  have heach := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hd i)).mp hz
  intro i
  by_contra hi
  have hstrict := Real.log_lt_sub_one_of_pos (hx i) hi
  have heq := heach i (Finset.mem_univ i)
  linarith

lemma posdef_det_le_one_of_trace_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (htrace : A.trace ≤ (n : ℝ)) : A.det ≤ 1 := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  apply positive_product_le_one_of_sum_le _ hA.eigenvalues_pos
  simpa only [hA.isHermitian.trace_eq_sum_eigenvalues, RCLike.ofReal_real_eq_id, id_eq] using htrace

lemma posdef_eq_one_of_det_one_trace_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (htrace : A.trace ≤ (n : ℝ)) (hdet : A.det = 1) : A = 1 := by
  have he := positive_eq_one_of_product_one_sum_le hA.isHermitian.eigenvalues
    hA.eigenvalues_pos (by simpa only [hA.isHermitian.trace_eq_sum_eigenvalues,
      RCLike.ofReal_real_eq_id, id_eq] using htrace)
    (by simpa only [hA.isHermitian.det_eq_prod_eigenvalues, RCLike.ofReal_real_eq_id, id_eq] using hdet)
  rw [hA.isHermitian.spectral_theorem]
  simp only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq]
  have hd : diagonal (fun i => (hA.isHermitian.eigenvalues i : ℝ)) =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by simp [he]
  rw [hd]
  simp

lemma possemidef_eq_one_of_det_one_trace_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (htrace : A.trace ≤ (n : ℝ)) (hdet : A.det = 1) : A = 1 := by
  apply posdef_eq_one_of_det_one_trace_le _ htrace hdet
  apply hA.posDef_iff_det_ne_zero.mpr
  rw [hdet]
  norm_num

end ModernConvex.Ellipsoids.Fresh
end

section

open Matrix
namespace ModernConvex.Ellipsoids.Fresh

lemma contact_center_zero {n : ℕ} {T : Set (Fin n → ℝ)}
    (hm : ContactMoments T) (b : Fin n → ℝ)
    (hb : ∀ u ∈ T, u ⬝ᵥ u = 1 → b ⬝ᵥ u ≤ 0) : b = 0 := by
  let r := Real.sqrt (b ⬝ᵥ b)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = b ⬝ᵥ b := Real.sq_sqrt (scalar_dot_self_nonneg b)
  have h := contact_scalar_quadratic hm b 0 (-r) (-1) (by
    intro u hu huu
    have hcs := scalar_unit_cauchy b u huu
    have hb' := hb u hu huu
    have hlow : 0 ≤ r + b ⬝ᵥ u := by nlinarith
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hb' hlow])
  apply dotProduct_self_eq_zero.mp
  nlinarith [scalar_dot_self_nonneg b]

lemma inner_feasible_trace_le {n : ℕ} {T : Set (Fin n → ℝ)}
    (hm : ContactMoments T) {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ}
    (hf : InnerFeasible T A b) : A.trace ≤ (n : ℝ) := by
  have hh := hm (1 - A) (-b) (by
    intro u hu huu
    obtain ⟨hbase,hsq⟩ := hf u hu
    have hcs := scalar_unit_cauchy (A *ᵥ u) u huu
    rw [dotProduct_comm (A *ᵥ u) u] at hcs
    have hq : u ⬝ᵥ (A *ᵥ u) ≤ 1 - b ⬝ᵥ u := by nlinarith
    simp only [sub_mulVec, one_mulVec, dotProduct_sub, neg_dotProduct, huu]
    linarith)
  simpa only [trace_sub, trace_one, Fintype.card_fin, sub_nonneg] using hh

lemma inner_spd_feasible_unique {n : ℕ} {T : Set (Fin n → ℝ)}
    (hm : ContactMoments T) {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ}
    (hf : InnerFeasible T A b) (hA : A.PosDef) (hdet : A.det = 1) :
    A = 1 ∧ b = 0 := by
  have heq := posdef_eq_one_of_det_one_trace_le hA (inner_feasible_trace_le hm hf) hdet
  refine ⟨heq,contact_center_zero hm b ?_⟩
  intro u hu huu
  obtain ⟨hb,hq⟩ := hf u hu
  rw [heq, one_mulVec, huu] at hq
  nlinarith

lemma outer_feasible_trace_le {n : ℕ} {T : Set (Fin n → ℝ)}
    (hm : ContactMoments T) {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ}
    (hf : OuterFeasible T A b) : (Aᵀ * A).trace + (n : ℝ) * (b ⬝ᵥ b) ≤ n := by
  have hh := hm (1 - Aᵀ * A - (b ⬝ᵥ b) • 1) ((-2 : ℝ) • (Aᵀ *ᵥ b)) (by
    intro u hu huu
    have hq := hf u hu
    have hg : u ⬝ᵥ ((Aᵀ * A) *ᵥ u) = (A *ᵥ u) ⬝ᵥ (A *ᵥ u) := by
      rw [← mulVec_mulVec, dotProduct_transpose_mulVec]
    have hl : (Aᵀ *ᵥ b) ⬝ᵥ u = b ⬝ᵥ (A *ᵥ u) := by
      rw [dotProduct_comm, dotProduct_transpose_mulVec]
    simp only [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, huu, hg, hl]
    simp only [add_dotProduct, dotProduct_add, dotProduct_comm (A *ᵥ u) b] at hq
    linarith)
  simp only [trace_sub, trace_one, Fintype.card_fin, trace_smul, smul_eq_mul] at hh
  nlinarith

lemma outer_feasible_unique {n : ℕ} (hn : 0 < n) {T : Set (Fin n → ℝ)}
    (hm : ContactMoments T) {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ}
    (hf : OuterFeasible T A b) (hdet : |A.det| = 1) : Aᵀ * A = 1 ∧ b = 0 := by
  have hq := outer_feasible_trace_le hm hf
  have hb := scalar_dot_self_nonneg b
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hG : (Aᵀ * A).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self A
  have hgd : (Aᵀ * A).det = 1 := by
    rw [det_mul, det_transpose]
    nlinarith [sq_abs A.det]
  have heq := possemidef_eq_one_of_det_one_trace_le hG (by nlinarith) hgd
  refine ⟨heq,?_⟩
  rw [heq, trace_one, Fintype.card_fin] at hq
  apply dotProduct_self_eq_zero.mp
  nlinarith

end ModernConvex.Ellipsoids.Fresh
end

section

open Matrix
open scoped MatrixOrder
namespace ModernConvex.Ellipsoids.Fresh

lemma orthogonal_dot_self {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (hO : Oᵀ * O = 1) (u : Fin n → ℝ) :
    (O *ᵥ u) ⬝ᵥ (O *ᵥ u) = u ⬝ᵥ u := by
  calc
    _ = u ⬝ᵥ (Oᵀ *ᵥ (O *ᵥ u)) := (dotProduct_transpose_mulVec O u (O *ᵥ u)).symm
    _ = _ := by rw [mulVec_mulVec, hO, one_mulVec]

lemma ellipsoid_mul_orthogonal {n : ℕ} (A O : Matrix (Fin n) (Fin n) ℝ)
    (hO : O * Oᵀ = 1) (c : Fin n → ℝ) : ellipsoid (A * O) c = ellipsoid A c := by
  have hO' : Oᵀ * O = 1 := mul_eq_one_comm.mp hO
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    refine ⟨O *ᵥ u,?_,?_⟩
    · simpa only [orthogonal_dot_self O hO' u] using hu
    · rw [mulVec_mulVec]
  · rintro ⟨u,hu,rfl⟩
    refine ⟨Oᵀ *ᵥ u,?_,?_⟩
    · simpa only [transpose_transpose, orthogonal_dot_self Oᵀ (by simpa using hO) u] using hu
    · simp only [mulVec_mulVec, Matrix.mul_assoc, hO, mul_one]

lemma exists_spd_shape {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) :
    ∃ T : Matrix (Fin n) (Fin n) ℝ, T.PosDef ∧
      T.det = |A.det| ∧ ∀ c, ellipsoid T c = ellipsoid A c := by
  have hAu : IsUnit A := (isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA)
  let G := A * Aᵀ
  have hG : G.PosDef := by
    simpa only [G, conjTranspose_eq_transpose_of_trivial] using
      PosDef.mul_conjTranspose_self A (vecMul_injective_of_isUnit hAu)
  let T := CFC.sqrt G
  have hT0 : T.PosSemidef := (CFC.sqrt_nonneg G).posSemidef
  have hTsq : T * T = G := by simpa only [T, pow_two] using CFC.sq_sqrt G
  have hdetG : G.det = A.det ^ 2 := by simp [G, det_mul, det_transpose, pow_two]
  have hdetT : T.det = |A.det| := by
    have hd := hG.posSemidef.det_sqrt
    simpa only [T, RCLike.sqrt_real, hdetG, Real.sqrt_sq_eq_abs] using hd
  have hT : T.PosDef := hT0.posDef_iff_det_ne_zero.mpr (by rw [hdetT]; exact abs_ne_zero.mpr hA)
  have hTt : Tᵀ = T := (isHermitian_iff_isSymm.mp hT.isHermitian)
  let O := T⁻¹ * A
  have hO : O * Oᵀ = 1 := by
    dsimp [O]
    rw [transpose_mul, ← mul_assoc, mul_assoc T⁻¹ A Aᵀ]
    change T⁻¹ * G * T⁻¹ᵀ = 1
    rw [← hTsq, transpose_nonsing_inv, hTt, ← mul_assoc,
      nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hT.det_pos.ne'), one_mul,
      mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hT.det_pos.ne')]
  have hTO : T * O = A := by
    dsimp [O]
    rw [← mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hT.det_pos.ne'), one_mul]
  refine ⟨T,hT,hdetT,?_⟩
  intro c
  rw [← hTO]
  exact (ellipsoid_mul_orthogonal T O hO c).symm

end ModernConvex.Ellipsoids.Fresh
end

section
open Matrix
namespace ModernConvex.Ellipsoids.Fresh

lemma normalized_inner_moments {n : ℕ} (hn : 0 < n) {S : Set (Fin n → ℝ)}
    (hS : IsSolid S) (hmax : IsMaxVolInscribed S (unitBall n)) :
    ContactMoments (polarSet S) :=
  innerOptimal_contactMoments hn (polarSet_compact hmax.2.1)
    (polarSet_subset_unitBall hmax.2.1) (native_innerOptimal hS hmax)

lemma normalized_outer_moments {n : ℕ} (hn : 0 < n) {S : Set (Fin n → ℝ)}
    (hS : IsSolid S) (hmin : IsMinVolCircumscribed S (unitBall n)) :
    ContactMoments S :=
  outerOptimal_contactMoments hn (solid_compact hS) hmin.2.1 (native_outerOptimal hmin)

lemma normalized_maximal_unique {n : ℕ} (hn : 0 < n) {S E : Set (Fin n → ℝ)}
    (hS : IsSolid S) (hmax : IsMaxVolInscribed S (unitBall n))
    (hE : IsMaxVolInscribed S E) : E = unitBall n := by
  have hv : Vol E = 1 := by
    apply le_antisymm
    · simpa only [Vol_unitBall] using hmax.2.2 E hE.1 hE.2.1
    · simpa only [Vol_unitBall] using hE.2.2 (unitBall n) hmax.1 hmax.2.1
  obtain ⟨A,c,hA,rfl⟩ := hE.1
  rw [Vol_ellipsoid] at hv
  have hdet : |A.det| = 1 := ENNReal.ofReal_eq_one.mp hv
  obtain ⟨T,hT,hTd,hshape⟩ := exists_spd_shape A hA
  have ht : Tᵀ = T := isHermitian_iff_isSymm.mp hT.isHermitian
  have hf : InnerFeasible (polarSet S) T c := by
    apply innerFeasible_of_containment
    rw [ht,hshape c]
    exact hE.2.1
  obtain ⟨hT1,hc⟩ := inner_spd_feasible_unique (normalized_inner_moments hn hS hmax)
    hf hT (hTd.trans hdet)
  rw [← hshape c,hT1,hc,ellipsoid_one_zero]

lemma normalized_minimal_unique {n : ℕ} (hn : 0 < n) {S E : Set (Fin n → ℝ)}
    (hS : IsSolid S) (hmin : IsMinVolCircumscribed S (unitBall n))
    (hE : IsMinVolCircumscribed S E) : E = unitBall n := by
  have hv : Vol E = 1 := by
    apply le_antisymm
    · simpa only [Vol_unitBall] using hE.2.2 (unitBall n) hmin.1 hmin.2.1
    · simpa only [Vol_unitBall] using hmin.2.2 E hE.1 hE.2.1
  obtain ⟨A,c,hA,rfl⟩ := hE.1
  rw [Vol_ellipsoid] at hv
  have hdet : |A.det| = 1 := ENNReal.ofReal_eq_one.mp hv
  have hdi : |A⁻¹.det| = 1 := by simp [det_nonsing_inv,abs_inv,hdet]
  have hf := inverse_outerFeasible hA hE.2.1
  obtain ⟨hG,hb⟩ := outer_feasible_unique hn (normalized_outer_moments hn hS hmin) hf hdi
  have hc : A⁻¹ *ᵥ c = 0 := neg_eq_zero.mp hb
  ext x
  rw [mem_ellipsoid_iff_inverse hA]
  change (A⁻¹ *ᵥ (x-c)) ⬝ᵥ (A⁻¹ *ᵥ (x-c)) ≤ 1 ↔ x ⬝ᵥ x ≤ 1
  rw [mulVec_sub,hc,sub_zero,orthogonal_dot_self A⁻¹ hG]

end ModernConvex.Ellipsoids.Fresh
end

section
open Matrix MeasureTheory
namespace ModernConvex.Ellipsoids.Fresh

noncomputable def affineHomeomorph {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
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

lemma affine_image_ellipsoid {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (c d : Fin n → ℝ) :
    (fun x => A *ᵥ x+c) '' ellipsoid B d = ellipsoid (A*B) (A *ᵥ d+c) := by
  ext x
  constructor
  · rintro ⟨_,⟨u,hu,rfl⟩,rfl⟩
    exact ⟨u,hu,by dsimp only; rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, add_assoc]⟩
  · rintro ⟨u,hu,rfl⟩
    refine ⟨B *ᵥ u+d,⟨u,hu,rfl⟩,?_⟩
    dsimp only
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, add_assoc]

lemma affine_image_solid {n : ℕ} {S : Set (Fin n → ℝ)} (hS : IsSolid S)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (c : Fin n → ℝ) :
    IsSolid ((fun x => A *ᵥ x+c) '' S) := by
  have hc : IsCompact ((fun x => A *ᵥ x+c) '' S) :=
    (solid_compact hS).image (by fun_prop)
  refine ⟨hc.isClosed,hc.isBounded,?_,?_⟩
  · rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩ a b ha hb hab
    refine ⟨a • u+b • v,hS.2.2.1 hu hv ha hb hab,?_⟩
    dsimp only
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    calc
      a • (A *ᵥ u)+b • (A *ᵥ v)+c =
          a • (A *ᵥ u)+b • (A *ᵥ v)+(a+b) • c := by rw [hab,one_smul]
      _ = a • (A *ᵥ u+c)+b • (A *ᵥ v+c) := by module
  · have h := Set.Nonempty.image (affineHomeomorph A hA c) hS.2.2.2
    rw [(affineHomeomorph A hA c).image_interior] at h
    exact h

lemma affine_image_fullDim {n : ℕ} {E : Set (Fin n → ℝ)}
    (hE : IsFullDimEllipsoid E) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) (c : Fin n → ℝ) :
    IsFullDimEllipsoid ((fun x => A *ᵥ x+c) '' E) := by
  obtain ⟨B,d,hB,rfl⟩ := hE
  exact ⟨A*B,A *ᵥ d+c,by rw [Matrix.det_mul]; exact mul_ne_zero hA hB,
    affine_image_ellipsoid A B c d⟩

lemma Vol_affine_image {n : ℕ} (S : Set (Fin n → ℝ))
    (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    Vol ((fun x => A *ᵥ x+c) '' S) = ENNReal.ofReal |A.det| * Vol S := by
  have he : (fun x => A *ᵥ x+c) '' S =
      (fun x => x+c) '' (Matrix.toLin' A '' S) := by
    rw [Set.image_image]
    rfl
  unfold Vol
  rw [he, volume_translate, Measure.addHaar_image_linearMap]
  simp only [LinearMap.det_toLin', mul_div_assoc]

end ModernConvex.Ellipsoids.Fresh
end

section
open Matrix
namespace ModernConvex.Ellipsoids.Fresh

lemma affineHomeomorph_symm_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) (c x : Fin n → ℝ) :
    (affineHomeomorph A hA c).symm x = A⁻¹ *ᵥ x + -(A⁻¹ *ᵥ c) := by
  change A⁻¹ *ᵥ (x-c) = _
  rw [Matrix.mulVec_sub, sub_eq_add_neg]

lemma affine_symm_image_fullDim {n : ℕ} {E : Set (Fin n → ℝ)}
    (hE : IsFullDimEllipsoid E) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) (c : Fin n → ℝ) :
    IsFullDimEllipsoid ((affineHomeomorph A hA c).symm '' E) := by
  have hi : A⁻¹.det ≠ 0 := by simp [Matrix.det_nonsing_inv,hA]
  simpa only [affineHomeomorph_symm_apply] using
    affine_image_fullDim hE A⁻¹ hi (-(A⁻¹ *ᵥ c))

lemma affine_image_maximal {n : ℕ} {S E : Set (Fin n → ℝ)}
    (hE : IsMaxVolInscribed S E) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) (c : Fin n → ℝ) :
    IsMaxVolInscribed ((fun x => A *ᵥ x+c) '' S) ((fun x => A *ᵥ x+c) '' E) := by
  let e := affineHomeomorph A hA c
  refine ⟨affine_image_fullDim hE.1 A hA c,Set.image_mono hE.2.1,?_⟩
  intro F hF hFS
  have hsub : e.symm '' F ⊆ S := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy,he⟩ := hFS hx
    have hxy : e y = x := he
    rw [← hxy,e.symm_apply_apply]
    exact hy
  have hh := hE.2.2 (e.symm '' F) (affine_symm_image_fullDim hF A hA c) hsub
  have hh' := mul_le_mul' (le_refl (ENNReal.ofReal |A.det|)) hh
  rw [← Vol_affine_image, ← Vol_affine_image] at hh'
  have he : (fun x => A *ᵥ x+c) '' (e.symm '' F) = F := by
    change e '' (e.symm '' F) = F
    exact e.toEquiv.image_symm_image F
  rw [he] at hh'
  exact hh'

lemma affine_image_minimal {n : ℕ} {S E : Set (Fin n → ℝ)}
    (hE : IsMinVolCircumscribed S E) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) (c : Fin n → ℝ) :
    IsMinVolCircumscribed ((fun x => A *ᵥ x+c) '' S) ((fun x => A *ᵥ x+c) '' E) := by
  let e := affineHomeomorph A hA c
  refine ⟨affine_image_fullDim hE.1 A hA c,Set.image_mono hE.2.1,?_⟩
  intro F hF hSF
  have hsub : S ⊆ e.symm '' F := by
    intro x hx
    exact ⟨e x,hSF ⟨x,hx,rfl⟩,e.symm_apply_apply x⟩
  have hh := hE.2.2 (e.symm '' F) (affine_symm_image_fullDim hF A hA c) hsub
  have hh' := mul_le_mul' (le_refl (ENNReal.ofReal |A.det|)) hh
  rw [← Vol_affine_image, ← Vol_affine_image] at hh'
  have he : (fun x => A *ᵥ x+c) '' (e.symm '' F) = F := by
    change e '' (e.symm '' F) = F
    exact e.toEquiv.image_symm_image F
  rw [he] at hh'
  exact hh'

end ModernConvex.Ellipsoids.Fresh
end

section
open Matrix
namespace ModernConvex.Ellipsoids.Fresh

lemma inverse_affine_ellipsoid {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) (c : Fin n → ℝ) :
    (fun x => A⁻¹ *ᵥ x + -(A⁻¹ *ᵥ c)) '' ellipsoid A c = unitBall n := by
  rw [affine_image_ellipsoid, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA),
    add_neg_cancel, ellipsoid_one_zero]

lemma normalize_maximal {n : ℕ} {S : Set (Fin n → ℝ)}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (c : Fin n → ℝ)
    (hE : IsMaxVolInscribed S (ellipsoid A c)) :
    IsMaxVolInscribed ((fun x => A⁻¹ *ᵥ x + -(A⁻¹ *ᵥ c)) '' S) (unitBall n) := by
  have hi : A⁻¹.det ≠ 0 := by simp [Matrix.det_nonsing_inv,hA]
  have hh := affine_image_maximal hE A⁻¹ hi (-(A⁻¹ *ᵥ c))
  rw [inverse_affine_ellipsoid A hA c] at hh
  exact hh

lemma normalize_minimal {n : ℕ} {S : Set (Fin n → ℝ)}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (c : Fin n → ℝ)
    (hE : IsMinVolCircumscribed S (ellipsoid A c)) :
    IsMinVolCircumscribed ((fun x => A⁻¹ *ᵥ x + -(A⁻¹ *ᵥ c)) '' S) (unitBall n) := by
  have hi : A⁻¹.det ≠ 0 := by simp [Matrix.det_nonsing_inv,hA]
  have hh := affine_image_minimal hE A⁻¹ hi (-(A⁻¹ *ᵥ c))
  rw [inverse_affine_ellipsoid A hA c] at hh
  exact hh

lemma affine_image_centrallySymmetric {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS : IsCentralSymmetric S) (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :
    IsCentralSymmetric ((fun x => A *ᵥ x+c) '' S) := by
  obtain ⟨z,hz⟩ := hS
  refine ⟨A *ᵥ z+c,?_⟩
  rintro x ⟨y,hy,rfl⟩
  refine ⟨2 • z-y,hz y hy,?_⟩
  dsimp only
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  module

end ModernConvex.Ellipsoids.Fresh
end

section
open Matrix
namespace ModernConvex.Ellipsoids.Fresh

lemma maximal_unique {n : ℕ} (hn : 0 < n) {S E F : Set (Fin n → ℝ)}
    (hS : IsSolid S) (hE : IsMaxVolInscribed S E) (hF : IsMaxVolInscribed S F) : E = F := by
  obtain ⟨A,c,hA,rfl⟩ := hE.1
  have hi : A⁻¹.det ≠ 0 := by simp [det_nonsing_inv,Ring.inverse_eq_inv,hA]
  let e := affineHomeomorph A⁻¹ hi (-(A⁻¹ *ᵥ c))
  have hsolid := affine_image_solid hS A⁻¹ hi (-(A⁻¹ *ᵥ c))
  have hnorm := normalize_maximal A hA c hE
  have hother := affine_image_maximal hF A⁻¹ hi (-(A⁻¹ *ᵥ c))
  have heq := normalized_maximal_unique hn hsolid hnorm hother
  have hball := inverse_affine_ellipsoid A hA c
  apply Set.image_injective.mpr e.injective
  exact hball.trans heq.symm

lemma minimal_unique {n : ℕ} (hn : 0 < n) {S E F : Set (Fin n → ℝ)}
    (hS : IsSolid S) (hE : IsMinVolCircumscribed S E) (hF : IsMinVolCircumscribed S F) : E = F := by
  obtain ⟨A,c,hA,rfl⟩ := hE.1
  have hi : A⁻¹.det ≠ 0 := by simp [det_nonsing_inv,Ring.inverse_eq_inv,hA]
  let e := affineHomeomorph A⁻¹ hi (-(A⁻¹ *ᵥ c))
  have hsolid := affine_image_solid hS A⁻¹ hi (-(A⁻¹ *ᵥ c))
  have hnorm := normalize_minimal A hA c hE
  have hother := affine_image_minimal hF A⁻¹ hi (-(A⁻¹ *ᵥ c))
  have heq := normalized_minimal_unique hn hsolid hnorm hother
  have hball := inverse_affine_ellipsoid A hA c
  apply Set.image_injective.mpr e.injective
  exact hball.trans heq.symm

end ModernConvex.Ellipsoids.Fresh
end

section

namespace ModernConvex.Ellipsoids.Fresh

lemma bounded_translation_orbit_zero {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS : Bornology.IsBounded S) (x v : Fin n → ℝ)
    (horbit : ∀ k : ℕ, x + (k : ℝ) • v ∈ S) : v = 0 := by
  obtain ⟨M, hM⟩ := hS.exists_norm_le
  by_contra hv
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  obtain ⟨k, hk⟩ := exists_nat_gt ((M + ‖x‖) / ‖v‖)
  have hlarge := (div_lt_iff₀ hvpos).mp hk
  have hnorm := norm_sub_le (x + (k : ℝ) • v) x
  have hcancel : x + (k : ℝ) • v - x = (k : ℝ) • v := by abel
  rw [hcancel, norm_smul, Real.norm_natCast] at hnorm
  have hbound := hM _ (horbit k)
  nlinarith

lemma bounded_symmetry_center_unique {n : ℕ} {S : Set (Fin n → ℝ)}
    (hS : Bornology.IsBounded S) (hne : S.Nonempty) (c d : Fin n → ℝ)
    (hc : ∀ x ∈ S, (2 : ℝ) • c - x ∈ S)
    (hd : ∀ x ∈ S, (2 : ℝ) • d - x ∈ S) : c = d := by
  obtain ⟨x, hx⟩ := hne
  have horbit : ∀ k : ℕ, x + (k : ℝ) • ((2 : ℝ) • (c - d)) ∈ S := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      have h := hc _ (hd _ ih)
      convert h using 1
      push_cast
      module
  have hz := bounded_translation_orbit_zero hS x ((2 : ℝ) • (c - d)) horbit
  have hsub : c - d = 0 := (smul_eq_zero.mp hz).resolve_left (by norm_num)
  exact sub_eq_zero.mp hsub

end ModernConvex.Ellipsoids.Fresh
end

section

open Matrix
namespace ModernConvex.Ellipsoids.Fresh

lemma mem_scaled_ball_iff {n : ℕ} (r : ℝ) (hr : 0 < r) (x : Fin n → ℝ) :
    x ∈ ellipsoid (r • (1 : Matrix (Fin n) (Fin n) ℝ)) 0 ↔ x ⬝ᵥ x ≤ r ^ 2 := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simp only [smul_mulVec, one_mulVec, add_zero, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hu)]
  · intro hx
    refine ⟨r⁻¹ • x, ?_, ?_⟩
    · simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
      have h := (div_le_one (sq_pos_of_pos hr)).mpr hx
      simpa only [div_eq_mul_inv, inv_pow, pow_two, _root_.mul_inv_rev, mul_assoc, mul_comm,
        mul_left_comm] using h
    · simp [smul_mulVec, smul_smul, hr.ne']

lemma unit_ball_neg_iff {n : ℕ} (x : Fin n → ℝ) :
    -x ∈ unitBall n ↔ x ∈ unitBall n := by
  simp [unitBall, neg_dotProduct, dotProduct_neg]

lemma ellipsoid_reflection_mem {n q : ℕ} (A : Matrix (Fin n) (Fin q) ℝ)
    (c x : Fin n → ℝ) (hx : x ∈ ellipsoid A c) :
    (2 : ℝ) • c - x ∈ ellipsoid A c := by
  obtain ⟨u, hu, rfl⟩ := hx
  refine ⟨-u, ?_, ?_⟩
  · simpa only [neg_dotProduct, dotProduct_neg, neg_neg] using hu
  · rw [mulVec_neg]
    module

end ModernConvex.Ellipsoids.Fresh
end

section

open Matrix
namespace ModernConvex.Ellipsoids.Fresh

lemma reflection_image_eq {n : ℕ} {S : Set (Fin n → ℝ)} (d : Fin n → ℝ)
    (hd : ∀ x ∈ S, (2 : ℝ) • d - x ∈ S) :
    (fun x => -(1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x + (2 : ℝ) • d) '' S = S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [neg_mulVec, one_mulVec, sub_eq_add_neg, add_comm] using hd y hy
  · intro hx
    refine ⟨(2 : ℝ) • d - x, hd x hx, ?_⟩
    simp only [neg_mulVec, one_mulVec]
    module

lemma reflection_ball_center_zero {n : ℕ} (d : Fin n → ℝ)
    (he : (fun x => -(1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x + (2 : ℝ) • d) ''
      unitBall n = unitBall n) : d = 0 := by
  apply bounded_symmetry_center_unique (unitBall_compact n).isBounded
    ⟨0, zero_mem_unitBall n⟩ d 0
  · intro x hx
    have hmem : -(1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x + (2 : ℝ) • d ∈ unitBall n := by
      rw [← he]
      exact ⟨x, hx, rfl⟩
    simpa only [neg_mulVec, one_mulVec, sub_eq_add_neg, add_comm] using hmem
  · intro x hx
    simpa using (unit_ball_neg_iff x).mpr hx

lemma normalized_maximal_symmetric_zero {n : ℕ} (hn : 0 < n)
    {S : Set (Fin n → ℝ)} (hS : IsSolid S)
    (hmax : IsMaxVolInscribed S (unitBall n)) (hs : IsCentralSymmetric S) :
    ∀ x ∈ S, -x ∈ S := by
  obtain ⟨d, hd⟩ := hs
  have htransport := affine_image_maximal hmax (-(1 : Matrix (Fin n) (Fin n) ℝ))
    (by rw [Matrix.det_neg, Matrix.det_one]; simp) ((2 : ℝ) • d)
  rw [reflection_image_eq d hd] at htransport
  have he := normalized_maximal_unique hn hS hmax htransport
  have hd0 := reflection_ball_center_zero d he
  subst d
  simpa using hd

lemma normalized_minimal_symmetric_zero {n : ℕ} (hn : 0 < n)
    {S : Set (Fin n → ℝ)} (hS : IsSolid S)
    (hmin : IsMinVolCircumscribed S (unitBall n)) (hs : IsCentralSymmetric S) :
    ∀ x ∈ S, -x ∈ S := by
  obtain ⟨d, hd⟩ := hs
  have htransport := affine_image_minimal hmin (-(1 : Matrix (Fin n) (Fin n) ℝ))
    (by rw [Matrix.det_neg, Matrix.det_one]; simp) ((2 : ℝ) • d)
  rw [reflection_image_eq d hd] at htransport
  have he := normalized_minimal_unique hn hS hmin htransport
  have hd0 := reflection_ball_center_zero d he
  subst d
  simpa using hd

end ModernConvex.Ellipsoids.Fresh
end

section
open Matrix
namespace ModernConvex.Ellipsoids.Fresh

lemma contact_polar_bound {n : ℕ} {S : Set (Fin n → ℝ)}
    (hm : ContactMoments S) {u : Fin n → ℝ} (hu : u ∈ polarSet S) :
    u ⬝ᵥ u ≤ (n : ℝ)^2 :=
  contact_inner_bound hm u (fun v hv _ => hu v hv)

lemma contact_polar_symmetric_bound {n : ℕ} {S : Set (Fin n → ℝ)}
    (hm : ContactMoments S) (hs : ∀ x ∈ S, -x ∈ S)
    {u : Fin n → ℝ} (hu : u ∈ polarSet S) : u ⬝ᵥ u ≤ (n : ℝ) := by
  apply contact_symmetric_inner_bound hm u
  intro v hv _
  apply abs_le.mpr
  have hh := hu (-v) (hs v hv)
  simp only [dotProduct_neg] at hh
  exact ⟨by linarith,hu v hv⟩

lemma scaled_ball_subset_of_polar_bound {n : ℕ} {S : Set (Fin n → ℝ)}
    (hcl : IsClosed S) (hcv : Convex ℝ S) (h0 : (0 : Fin n → ℝ) ∈ S)
    (r : ℝ) (hr : 0 < r)
    (hbound : ∀ u ∈ polarSet S, u ⬝ᵥ u ≤ r^2) :
    ellipsoid ((1/r) • (1 : Matrix (Fin n) (Fin n) ℝ)) 0 ⊆ S := by
  intro x hx
  have hxq := (mem_scaled_ball_iff (1/r) (one_div_pos.mpr hr) x).mp hx
  apply mem_of_polar_constraints hcl hcv h0
  intro u hu
  have huq := hbound u hu
  have hcs : (u ⬝ᵥ x)^2 ≤ (u ⬝ᵥ u)*(x ⬝ᵥ x) := by
    simpa only [dotProduct,pow_two] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u x
  have hmul := mul_le_mul huq hxq (scalar_dot_self_nonneg x) (sq_nonneg r)
  have he : r^2 * (1/r)^2 = 1 := by field_simp
  rw [he] at hmul
  nlinarith

lemma inner_contact_containment {n : ℕ} (hn : 0 < n) {S : Set (Fin n → ℝ)}
    (hm : ContactMoments (polarSet S)) :
    S ⊆ ellipsoid ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) 0 := by
  intro x hx
  apply (mem_scaled_ball_iff (n : ℝ) (by exact_mod_cast hn) x).mpr
  apply contact_inner_bound hm x
  intro u hu _
  simpa only [dotProduct_comm] using hu x hx

lemma inner_contact_symmetric_containment {n : ℕ} (hn : 0 < n) {S : Set (Fin n → ℝ)}
    (hm : ContactMoments (polarSet S)) (hs : ∀ x ∈ S, -x ∈ S) :
    S ⊆ ellipsoid ((Real.sqrt n) • (1 : Matrix (Fin n) (Fin n) ℝ)) 0 := by
  intro x hx
  apply (mem_scaled_ball_iff (Real.sqrt n) (Real.sqrt_pos.mpr (by exact_mod_cast hn)) x).mpr
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  apply contact_symmetric_inner_bound hm x
  intro u hu _
  have hp := hu x hx
  have hn' := hu (-x) (hs x hx)
  simp only [dotProduct_neg] at hn'
  rw [dotProduct_comm x u]
  exact abs_le.mpr ⟨by linarith,hp⟩

end ModernConvex.Ellipsoids.Fresh
end

section
open Matrix
namespace ModernConvex.Ellipsoids.Fresh

lemma contact_zero_mem {n : ℕ} (hn : 0 < n) {S : Set (Fin n → ℝ)}
    (hcl : IsClosed S) (hcv : Convex ℝ S) (hm : ContactMoments S) :
    (0 : Fin n → ℝ) ∈ S := by
  by_contra hz
  obtain ⟨f,a,hfa,ha⟩ := geometric_hahn_banach_closed_point hcv hcl hz
  have ha0 : a < 0 := by simpa using ha
  let b : Fin n → ℝ := fun i => f (Pi.single i 1) / a
  have hb : ∀ u, b ⬝ᵥ u = f u / a := by
    intro u
    dsimp [b]
    unfold dotProduct
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    exact congrArg (fun t : ℝ => t/a) (dual_coeff_dot f.toLinearMap u)
  have hh := hm (-1) b (by
    intro u hu hunit
    rw [Matrix.neg_mulVec, Matrix.one_mulVec, dotProduct_neg, hunit, hb]
    have hratio : 1 ≤ f u / a := (le_div_iff_of_neg ha0).mpr (by simpa using (hfa u hu).le)
    linarith)
  have ht : (-1 : Matrix (Fin n) (Fin n) ℝ).trace = -(n:ℝ) := by simp
  rw [ht] at hh
  have hnreal : (0:ℝ) < n := by exact_mod_cast hn
  linarith

end ModernConvex.Ellipsoids.Fresh
end

section
open Matrix
namespace ModernConvex.Ellipsoids.Fresh

lemma normalized_inner_rounding {n : ℕ} (hn : 0 < n) {S : Set (Fin n → ℝ)}
    (hS : IsSolid S) (hmax : IsMaxVolInscribed S (unitBall n)) :
    S ⊆ ellipsoid ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) 0 ∧
    (IsCentralSymmetric S → S ⊆ ellipsoid (Real.sqrt n • (1 : Matrix (Fin n) (Fin n) ℝ)) 0) := by
  have hm := normalized_inner_moments hn hS hmax
  refine ⟨inner_contact_containment hn hm,?_⟩
  intro hs
  exact inner_contact_symmetric_containment hn hm (normalized_maximal_symmetric_zero hn hS hmax hs)

lemma normalized_outer_rounding {n : ℕ} (hn : 0 < n) {S : Set (Fin n → ℝ)}
    (hS : IsSolid S) (hmin : IsMinVolCircumscribed S (unitBall n)) :
    ellipsoid ((1/(n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ)) 0 ⊆ S ∧
    (IsCentralSymmetric S → ellipsoid ((1/Real.sqrt n) • (1 : Matrix (Fin n) (Fin n) ℝ)) 0 ⊆ S) := by
  have hm := normalized_outer_moments hn hS hmin
  have h0 := contact_zero_mem hn hS.1 hS.2.2.1 hm
  refine ⟨scaled_ball_subset_of_polar_bound hS.1 hS.2.2.1 h0 (n : ℝ)
    (by exact_mod_cast hn) (fun u hu => contact_polar_bound hm hu),?_⟩
  intro hs
  apply scaled_ball_subset_of_polar_bound hS.1 hS.2.2.1 h0 (Real.sqrt n)
    (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  intro u hu
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  exact contact_polar_symmetric_bound hm (normalized_minimal_symmetric_zero hn hS hmin hs) hu

end ModernConvex.Ellipsoids.Fresh
end

section
open Matrix
namespace ModernConvex.Ellipsoids.Fresh

lemma affine_image_ball_dilate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (c : Fin n → ℝ) (r : ℝ) :
    (fun x => A *ᵥ x+c) '' ellipsoid (r • (1 : Matrix (Fin n) (Fin n) ℝ)) 0 =
      ellipsoid (r • A) c := by
  rw [affine_image_ellipsoid]
  simp

lemma subset_dilate_of_normalized_subset {n : ℕ} {S : Set (Fin n → ℝ)}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (c : Fin n → ℝ) (r : ℝ)
    (hsub : (affineHomeomorph A hA c).symm '' S ⊆
      ellipsoid (r • (1 : Matrix (Fin n) (Fin n) ℝ)) 0) :
    S ⊆ ellipsoid (r • A) c := by
  have hh := Set.image_mono (f := affineHomeomorph A hA c) hsub
  have he : (affineHomeomorph A hA c) '' ((affineHomeomorph A hA c).symm '' S) = S :=
    (affineHomeomorph A hA c).toEquiv.image_symm_image S
  rw [he] at hh
  rw [show (affineHomeomorph A hA c) '' ellipsoid (r • (1 : Matrix (Fin n) (Fin n) ℝ)) 0 =
    ellipsoid (r • A) c from affine_image_ball_dilate A c r] at hh
  exact hh

lemma dilate_subset_of_normalized_subset {n : ℕ} {S : Set (Fin n → ℝ)}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (c : Fin n → ℝ) (r : ℝ)
    (hsub : ellipsoid (r • (1 : Matrix (Fin n) (Fin n) ℝ)) 0 ⊆
      (affineHomeomorph A hA c).symm '' S) :
    ellipsoid (r • A) c ⊆ S := by
  have hh := Set.image_mono (f := affineHomeomorph A hA c) hsub
  have he : (affineHomeomorph A hA c) '' ((affineHomeomorph A hA c).symm '' S) = S :=
    (affineHomeomorph A hA c).toEquiv.image_symm_image S
  rw [he] at hh
  rw [show (affineHomeomorph A hA c) '' ellipsoid (r • (1 : Matrix (Fin n) (Fin n) ℝ)) 0 =
    ellipsoid (r • A) c from affine_image_ball_dilate A c r] at hh
  exact hh

end ModernConvex.Ellipsoids.Fresh
end

section
open Matrix
namespace ModernConvex.Ellipsoids.Fresh

lemma maximal_rounding {n : ℕ} (hn : 0 < n) {S : Set (Fin n → ℝ)}
    (hS : IsSolid S) (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    (hA : A.det ≠ 0) (hE : IsMaxVolInscribed S (ellipsoid A c)) :
    S ⊆ ellipsoid ((n : ℝ) • A) c ∧
    (IsCentralSymmetric S → S ⊆ ellipsoid (Real.sqrt n • A) c) := by
  have hi : A⁻¹.det ≠ 0 := by simp [det_nonsing_inv,Ring.inverse_eq_inv,hA]
  have hsolid := affine_image_solid hS A⁻¹ hi (-(A⁻¹ *ᵥ c))
  have hh := normalized_inner_rounding hn hsolid (normalize_maximal A hA c hE)
  have hident : ⇑(affineHomeomorph A hA c).symm =
      (fun x => A⁻¹ *ᵥ x + -(A⁻¹ *ᵥ c)) := by
    funext x
    change A⁻¹ *ᵥ (x-c) = _
    rw [mulVec_sub,sub_eq_add_neg]
  constructor
  · apply subset_dilate_of_normalized_subset A hA c (n : ℝ)
    rw [hident]
    exact hh.1
  · intro hs
    apply subset_dilate_of_normalized_subset A hA c (Real.sqrt n)
    rw [hident]
    exact hh.2 (affine_image_centrallySymmetric hs A⁻¹ (-(A⁻¹ *ᵥ c)))

lemma minimal_rounding {n : ℕ} (hn : 0 < n) {S : Set (Fin n → ℝ)}
    (hS : IsSolid S) (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ)
    (hA : A.det ≠ 0) (hE : IsMinVolCircumscribed S (ellipsoid A c)) :
    ellipsoid ((1/(n : ℝ)) • A) c ⊆ S ∧
    (IsCentralSymmetric S → ellipsoid ((1/Real.sqrt n) • A) c ⊆ S) := by
  have hi : A⁻¹.det ≠ 0 := by simp [det_nonsing_inv,Ring.inverse_eq_inv,hA]
  have hsolid := affine_image_solid hS A⁻¹ hi (-(A⁻¹ *ᵥ c))
  have hh := normalized_outer_rounding hn hsolid (normalize_minimal A hA c hE)
  have hident : ⇑(affineHomeomorph A hA c).symm =
      (fun x => A⁻¹ *ᵥ x + -(A⁻¹ *ᵥ c)) := by
    funext x
    change A⁻¹ *ᵥ (x-c) = _
    rw [mulVec_sub,sub_eq_add_neg]
  constructor
  · apply dilate_subset_of_normalized_subset A hA c (1/(n : ℝ))
    rw [hident]
    exact hh.1
  · intro hs
    apply dilate_subset_of_normalized_subset A hA c (1/Real.sqrt n)
    rw [hident]
    exact hh.2 (affine_image_centrallySymmetric hs A⁻¹ (-(A⁻¹ *ᵥ c)))

end ModernConvex.Ellipsoids.Fresh
end

section

open Matrix
namespace ModernConvex.Ellipsoids.Fresh

lemma zero_dim_ellipsoid (A : Matrix (Fin 0) (Fin 0) ℝ) (c : Fin 0 → ℝ) :
    ellipsoid A c = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  refine ⟨0, ?_, Subsingleton.elim _ _⟩
  simp

lemma zero_dim_solid_eq_univ {S : Set (Fin 0 → ℝ)} (hS : IsSolid S) :
    S = Set.univ := by
  obtain ⟨x, hx⟩ := hS.2.2.2
  have hxS : x ∈ S := interior_subset hx
  apply Set.eq_univ_of_forall
  intro y
  simpa only [Subsingleton.elim y x] using hxS

lemma zero_dim_full_iff (E : Set (Fin 0 → ℝ)) :
    IsFullDimEllipsoid E ↔ E = Set.univ := by
  constructor
  · rintro ⟨A, c, _, rfl⟩
    exact zero_dim_ellipsoid A c
  · rintro rfl
    refine ⟨1, 0, ?_, (zero_dim_ellipsoid 1 0).symm⟩
    simp

lemma zero_dim_max_iff {S : Set (Fin 0 → ℝ)} (hS : IsSolid S)
    (E : Set (Fin 0 → ℝ)) : IsMaxVolInscribed S E ↔ E = Set.univ := by
  rw [zero_dim_solid_eq_univ hS]
  constructor
  · exact fun h => (zero_dim_full_iff E).mp h.1
  · rintro rfl
    refine ⟨(zero_dim_full_iff _).mpr rfl, Set.Subset.rfl, ?_⟩
    intro E' hE' _
    rw [(zero_dim_full_iff E').mp hE']

lemma zero_dim_min_iff {S : Set (Fin 0 → ℝ)} (hS : IsSolid S)
    (E : Set (Fin 0 → ℝ)) : IsMinVolCircumscribed S E ↔ E = Set.univ := by
  rw [zero_dim_solid_eq_univ hS]
  constructor
  · exact fun h => (zero_dim_full_iff E).mp h.1
  · rintro rfl
    refine ⟨(zero_dim_full_iff _).mpr rfl, Set.Subset.rfl, ?_⟩
    intro E' hE' _
    rw [(zero_dim_full_iff E').mp hE']

end ModernConvex.Ellipsoids.Fresh
end

section
open Matrix
namespace ModernConvex.Ellipsoids.Fresh

/-- Ben-Tal–Nemirovski, Theorem 4.9.1 (Löwner–Fritz John), p. 259. Let `S ⊂ ℝⁿ` be a solid. Then
(i) there exists and is uniquely defined the largest volume full-dimensional ellipsoid `E_in`
contained in `S`; the concentric to `E_in` `n` times larger ellipsoid contains `S`, and if `S` is
central-symmetric already the `√n` times larger one does;
(ii) there exists and is uniquely defined the smallest volume full-dimensional ellipsoid `E_out`
containing `S`; the concentric to `E_out` `n` times smaller ellipsoid is contained in `S`, and if
`S` is central-symmetric already the `√n` times smaller one is.
"Concentric, `r` times larger" ellipsoid of `E = {Au + c | uᵀu ≤ 1}` is `{(rA)u + c | uᵀu ≤ 1}`. -/
theorem native_lowner_fritz_john {n : ℕ} (S : Set (Fin n → ℝ)) (hS : IsSolid S) :
    ((∃! E : Set (Fin n → ℝ), IsMaxVolInscribed S E) ∧
      ∀ (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ), A.det ≠ 0 →
        IsMaxVolInscribed S (ellipsoid A c) →
          S ⊆ ellipsoid ((n : ℝ) • A) c ∧
            (IsCentralSymmetric S → S ⊆ ellipsoid (Real.sqrt n • A) c)) ∧
    ((∃! E : Set (Fin n → ℝ), IsMinVolCircumscribed S E) ∧
      ∀ (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ), A.det ≠ 0 →
        IsMinVolCircumscribed S (ellipsoid A c) →
          ellipsoid ((1 / (n : ℝ)) • A) c ⊆ S ∧
            (IsCentralSymmetric S → ellipsoid ((1 / Real.sqrt n) • A) c ⊆ S)) := by
  by_cases hn : n = 0
  · subst n
    have hsu := zero_dim_solid_eq_univ hS
    constructor
    · constructor
      · exact ⟨Set.univ,(zero_dim_max_iff hS _).mpr rfl,fun E hE => (zero_dim_max_iff hS E).mp hE⟩
      · intro A c _ _
        simp only [zero_dim_ellipsoid,hsu,Set.Subset.refl,implies_true,and_self]
    · constructor
      · exact ⟨Set.univ,(zero_dim_min_iff hS _).mpr rfl,fun E hE => (zero_dim_min_iff hS E).mp hE⟩
      · intro A c _ _
        simp only [zero_dim_ellipsoid,hsu,Set.Subset.refl,implies_true,and_self]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨E,hE⟩ := exists_maxVolInscribed hS
    obtain ⟨F,hF⟩ := exists_minVolCircumscribed hS
    exact ⟨⟨⟨E,hE,fun E' hE' => maximal_unique hnpos hS hE' hE⟩,
      fun A c hA hmax => maximal_rounding hnpos hS A c hA hmax⟩,
      ⟨⟨F,hF,fun F' hF' => minimal_unique hnpos hS hF' hF⟩,
      fun A c hA hmin => minimal_rounding hnpos hS A c hA hmin⟩⟩

end ModernConvex.Ellipsoids.Fresh
end

open Matrix ModernConvex.Ellipsoids

theorem solution {n : ℕ} (S : Set (Fin n → ℝ)) (hS : IsSolid S) :
    ((∃! E : Set (Fin n → ℝ), IsMaxVolInscribed S E) ∧
      ∀ (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ), A.det ≠ 0 →
        IsMaxVolInscribed S (ellipsoid A c) →
          S ⊆ ellipsoid ((n : ℝ) • A) c ∧
            (IsCentralSymmetric S → S ⊆ ellipsoid (Real.sqrt n • A) c)) ∧
    ((∃! E : Set (Fin n → ℝ), IsMinVolCircumscribed S E) ∧
      ∀ (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ), A.det ≠ 0 →
        IsMinVolCircumscribed S (ellipsoid A c) →
          ellipsoid ((1 / (n : ℝ)) • A) c ⊆ S ∧
            (IsCentralSymmetric S → ellipsoid ((1 / Real.sqrt n) • A) c ⊆ S))  := by
  exact Fresh.native_lowner_fritz_john S hS
