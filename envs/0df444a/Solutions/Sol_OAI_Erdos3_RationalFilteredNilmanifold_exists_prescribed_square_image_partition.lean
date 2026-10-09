-- Prove2me | solution 1 for OAI.Erdos3.RationalFilteredNilmanifold.exists_prescribed_square_image_partition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T07:01:31.384807+00:00
-- url     : https://prove2.me/submissions/b23236f8-f779-4e54-b024-1d74c9de6dff

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B042

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InteriorIntervalCutoff
namespace OAI

section

namespace Erdos3

theorem same_side_of_cut_of_small_displacement {x y c ρ : ℝ}
    (hxy : |x - y| ≤ ρ) (hgap : ρ < |x - c|) : (c ≤ x ↔ c ≤ y) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hxy
  by_cases hcx : c ≤ x
  · rw [abs_of_nonneg (sub_nonneg.mpr hcx)] at hgap
    have hcy : c ≤ y := by linarith
    simp only [hcx, hcy]
  · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge hcx))] at hgap
    have hcy : ¬c ≤ y := by linarith
    simp only [hcx, hcy]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem cyclic_wrap_branch_eq_of_good_circle {N : ℕ} [NeZero N]
    (h x y : ZMod N) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hdist : dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) :
    (N - h.val ≤ x.val ↔ N - h.val ≤ y.val) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hd := good_circle_observations_control_representatives h x y hρ hx hy hdist
  rw [← sub_div, abs_div, abs_of_pos hN] at hd
  have hdiff : |(x.val : ℝ) - y.val| ≤ (N : ℝ) * ρ := by
    have h := (div_le_iff₀ hN).mp hd
    nlinarith
  have hgap := (outside_cyclicWrapExceptional h x hx).2.2
  have hb := same_side_of_cut_of_small_displacement hdiff hgap
  exact_mod_cast hb

theorem cyclic_representative_difference_of_good_circle {N : ℕ} [NeZero N]
    (h x y : ZMod N) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hdist : dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) :
    ((h + x).val : ℤ) - ((h + y).val : ℤ) = (x.val : ℤ) - (y.val : ℤ) := by
  have hb := cyclic_wrap_branch_eq_of_good_circle h x y hρ hx hy hdist
  rw [cyclic_representative_add h x, cyclic_representative_add h y]
  simp only [← hb]
  ring

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicOrdinaryShiftBranches
namespace OAI

section

namespace Erdos3

theorem ordinaryShiftBranch_bound {N : ℕ} (h : ZMod N) (b : Fin 2) (x : ZMod N) :
    |ordinaryShiftBranch h b x| ≤ 1 := by
  have hb := b.isLt
  unfold ordinaryShiftBranch
  rw [abs_le]
  split_ifs <;> omega

theorem ordinary_shift_from_cyclic_representative {N : ℕ} [NeZero N]
    (h : ZMod N) (b : Fin 2) (x : ZMod N) :
    (x.val : ℤ) + h.val - (b.val : ℤ) * N =
      ((h + x).val : ℤ) + ordinaryShiftBranch h b x * N := by
  rw [cyclic_representative_add h x]
  unfold ordinaryShiftBranch
  split_ifs <;> ring

theorem ordinaryShiftBranch_eq_of_good_circle {N : ℕ} [NeZero N]
    (h : ZMod N) (b : Fin 2) (x y : ZMod N) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hdist : dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) :
    ordinaryShiftBranch h b x = ordinaryShiftBranch h b y := by
  have hb := cyclic_wrap_branch_eq_of_good_circle h x y hρ hx hy hdist
  simp only [ordinaryShiftBranch, ← hb]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CyclicAlternativePathRecovery
namespace OAI

section

namespace Erdos3

theorem ordinary_shift_path_dist_le {X : Type*} [PseudoMetricSpace X]
    (P : ℤ → X) {N : ℕ} [NeZero N] (h : ZMod N) (b : Fin 2) (x y : ZMod N)
    {ρ δ : ℝ} (hρ : 0 < ρ)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hcircle : dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ)
    (hobs : ∀ t : ℤ, |t| ≤ 1 →
      dist (P (((h + x).val : ℤ) + t * N)) (P (((h + y).val : ℤ) + t * N)) ≤ δ) :
    dist (P ((x.val : ℤ) + h.val - (b.val : ℤ) * N))
      (P ((y.val : ℤ) + h.val - (b.val : ℤ) * N)) ≤ δ := by
  have hb := ordinaryShiftBranch_eq_of_good_circle h b x y hρ hx hy hcircle
  rw [ordinary_shift_from_cyclic_representative h b x,
    ordinary_shift_from_cyclic_representative h b y, ← hb]
  exact hobs _ (ordinaryShiftBranch_bound h b x)

theorem positive_cell_ordinary_shift_recovery {I J X : Type*} [PseudoMetricSpace X]
    {N : ℕ} [NeZero N] (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ)
    (P : ℤ → X) {ρ δ : ℝ} (hρ : 0 < ρ)
    (hA : ∀ i x, 0 ≤ A i x)
    (hcircle : ∀ i x y, 0 < A i x → 0 < A i y →
      dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ)
    (hobs : ∀ j x y, 0 < B j x → 0 < B j y → ∀ t : ℤ, |t| ≤ 1 →
      dist (P ((x.val : ℤ) + t * N)) (P ((y.val : ℤ) + t * N)) ≤ δ)
    (h : ZMod N) (b : Fin 2) (i : I) (j : J) (x y : ZMod N)
    (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
    (hxy : 0 < A i x * B j (x + h)) (hyy : 0 < A i y * B j (y + h)) :
    dist (P ((x.val : ℤ) + h.val - (b.val : ℤ) * N))
      (P ((y.val : ℤ) + h.val - (b.val : ℤ) * N)) ≤ δ := by
  have hpos (z : ZMod N) (hz : 0 < A i z * B j (z + h)) : 0 < A i z ∧ 0 < B j (z + h) := by
    rcases mul_pos_iff.mp hz with h | h
    · exact h
    · linarith [hA i z]
  obtain ⟨hAx, hBx⟩ := hpos x hxy
  obtain ⟨hAy, hBy⟩ := hpos y hyy
  apply ordinary_shift_path_dist_le P h b x y hρ hx hy (hcircle i x y hAx hAy)
  intro t ht
  simpa only [add_comm h x, add_comm h y] using hobs j (x + h) (y + h) hBx hBy t ht

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CappedDistanceReconstruction
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem cappedDistanceTest_unit_interval {X : Type*} [PseudoMetricSpace X] (a x : X) :
    (cappedDistanceTest a x).im = 0 ∧ 0 ≤ (cappedDistanceTest a x).re ∧
      (cappedDistanceTest a x).re ≤ 1 :=
  ⟨rfl, le_min zero_le_one dist_nonneg, min_le_left _ _⟩

theorem cappedDistanceTest_lipschitz {X : Type*} [PseudoMetricSpace X] (a : X) :
    LipschitzWith 1 (cappedDistanceTest a) := by
  unfold cappedDistanceTest
  simpa only [one_mul, Function.comp_def] using
    Complex.isometry_ofReal.lipschitz.comp ((LipschitzWith.dist_right a).const_min 1)

theorem local_dist_le_of_positive_reconstruction {A X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] (f : A → X) (g : A → Y) (L : ℝ≥0)
    (hrec : ∀ a : X, ∃ (v : Y → ℂ) (K : ℝ≥0), K ≤ L ∧ LipschitzWith K v ∧
      ∀ x, v (g x) = cappedDistanceTest a (f x))
    (x y : A) (hnear : (L : ℝ) * dist (g x) (g y) < 1) :
    dist (f x) (f y) ≤ L * dist (g x) (g y) := by
  obtain ⟨v, K, hK, hv, heval⟩ := hrec (f x)
  have hmin : min 1 (dist (f x) (f y)) ≤ (L : ℝ) * dist (g x) (g y) := by
    have h := hv.dist_le_mul (g y) (g x)
    rw [heval, heval] at h
    simpa only [cappedDistanceTest, dist_self, min_eq_right zero_le_one,
      Complex.ofReal_zero, dist_zero_right, dist_zero_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_min zero_le_one dist_nonneg), dist_comm] using
      h.trans (mul_le_mul_of_nonneg_right (show (K : ℝ) ≤ L from hK) dist_nonneg)
  have hdist : dist (f x) (f y) < 1 := by
    by_contra h
    rw [min_eq_left (le_of_not_gt h)] at hmin
    linarith
  simpa only [min_eq_right hdist.le] using hmin

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FrozenCosetVariation
namespace OAI

section

namespace Erdos3

open scoped NNReal ENNReal

variable {G : Type*} [Group G] [PseudoEMetricSpace G]

variable [IsIsometricSMul Gᵐᵒᵖ G]

end Erdos3

namespace Erdos3

open scoped NNReal

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal ENNReal

variable {G X : Type*} [Group G] [MetricSpace G]
  [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G] [PseudoEMetricSpace X]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {G : Type*} [Group G]

variable [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G]

end Erdos3

end

section

namespace Erdos3

variable {G H : Type*} [Group G] [Group H]

open scoped NNReal

variable [MetricSpace G] [MetricSpace H]
  [IsIsometricSMul Gᵐᵒᵖ G] [IsIsometricSMul Hᵐᵒᵖ H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {G H : Type*} [Group G] [Group H] [MetricSpace G] [MetricSpace H]
  [IsIsometricSMul Gᵐᵒᵖ G] [IsIsometricSMul Hᵐᵒᵖ H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (Γ : Subgroup G) (Λ : Subgroup H)
  (hΓ : IsClosed (Γ : Set G)) (hΛ : IsClosed (Λ : Set H))
  (φ : G →* H) (r : H) (h : ∀ γ ∈ Γ, r⁻¹ * φ γ * r ∈ Λ)

omit [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G] in
theorem frozenCosetMap_dist_left (a b : H) (x : G ⧸ Γ) :
    letI := rightCosetMetricSpace Λ hΛ
    dist (frozenCosetMap Γ Λ φ a r h x) (frozenCosetMap Γ Λ φ b r h x) ≤ dist a b := by
  let := rightCosetMetricSpace Λ hΛ
  induction x using Quotient.inductionOn with
  | h x =>
    have hLip := lipschitz_quotient_orbit Λ hΛ (QuotientGroup.mk (φ x * r))
    simpa only [NNReal.coe_one, one_mul, MulAction.Quotient.smul_mk, smul_eq_mul,
      mul_assoc, frozenCosetMap_mk] using hLip.dist_le_mul a b

theorem frozenCosetMap_dist_le (a b : H) {A C : ℝ≥0}
    (hφ : LipschitzWith C φ) (ha : LipschitzWith A (fun x => a * x)) (x y : G ⧸ Γ) :
    letI := rightCosetMetricSpace Γ hΓ
    letI := rightCosetMetricSpace Λ hΛ
    dist (frozenCosetMap Γ Λ φ a r h x) (frozenCosetMap Γ Λ φ b r h y) ≤
      (A * C : ℝ≥0) * dist x y + dist a b := by
  let := rightCosetMetricSpace Γ hΓ
  let := rightCosetMetricSpace Λ hΛ
  exact (dist_triangle _ (frozenCosetMap Γ Λ φ a r h y) _).trans
    (add_le_add ((lipschitz_frozenCosetMap Γ Λ hΓ hΛ φ a r h hφ ha).dist_le_mul x y)
      (frozenCosetMap_dist_left Γ Λ hΛ φ r h a b y))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeProductOrbitMetric
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open scoped NNReal BigOperators

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

theorem realBCHPiEquiv_symm_lipschitz :
    letI : ∀ i, MetricSpace (D i).RealGroup := fun i =>
      rightMetricSpace (hnil := (D i).filtration.realification.lowerCentralSeries_eq_bot)
        ((D i).basis.baseChange ℝ)
    letI := rightMetricSpace (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
      ((pi D).basis.baseChange ℝ)
    LipschitzWith (productMetricBound d) (realBCHPiEquiv (fun i => (D i).filtration)).symm := by
  let : ∀ i, MetricSpace (D i).RealGroup := fun i =>
    rightMetricSpace (hnil := (D i).filtration.realification.lowerCentralSeries_eq_bot)
      ((D i).basis.baseChange ℝ)
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] (∀ i, L i)) := ((pi D).basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
    ((pi D).basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
    ((pi D).basis.baseChange ℝ)
  apply lipschitzWith_of_coordinatewise
  intro i y
  let e := realBCHPiEquiv (fun j => (D j).filtration)
  let u : (pi D).RealGroup := e.symm (Function.update y i 1)
  have heval (a : (D i).RealGroup) :
      e.symm (Function.update y i a) = productInclusionHom D i a * u := by
    have hup : Function.update y i a = Pi.mulSingle i a * Function.update y i 1 := by
      funext j
      by_cases hji : j = i
      · subst j
        simp only [Function.update_self, Pi.mul_apply, Pi.mulSingle_eq_same, mul_one]
      · simp only [Function.update_of_ne hji, Pi.mul_apply, Pi.mulSingle_eq_of_ne hji, one_mul]
    rw [hup, map_mul, realBCHPiEquiv_symm_single]
  have h := (isometry_mul_right u).lipschitz.comp (productInclusionHom_lipschitz D i)
  change LipschitzWith (coordinateLipschitzBound (Fintype.card (Σ j, Fin (d j))) (d i) 1)
    (fun a => e.symm (Function.update y i a))
  simpa only [Function.comp_def, heval, one_mul] using h

theorem native_product_group_dist_le (a b : (pi D).RealGroup) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ i,
      letI := rightMetricSpace (hnil := (D i).filtration.realification.lowerCentralSeries_eq_bot)
        ((D i).basis.baseChange ℝ)
      dist (productProjectionHom D i a) (productProjectionHom D i b) ≤ ρ) :
    letI := rightMetricSpace (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
      ((pi D).basis.baseChange ℝ)
    dist a b ≤ (productMetricBound d : ℝ) * ρ := by
  let : ∀ i, MetricSpace (D i).RealGroup := fun i =>
    rightMetricSpace (hnil := (D i).filtration.realification.lowerCentralSeries_eq_bot)
      ((D i).basis.baseChange ℝ)
  let := rightMetricSpace (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
    ((pi D).basis.baseChange ℝ)
  let e := realBCHPiEquiv (fun i => (D i).filtration)
  have hpi : dist (e a) (e b) ≤ ρ := (dist_pi_le_iff hρ).mpr h
  have hdist := (realBCHPiEquiv_symm_lipschitz D).dist_le_mul (e a) (e b)
  change dist (e.symm (e a)) (e.symm (e b)) ≤
    (productMetricBound d : ℝ) * dist (e a) (e b) at hdist
  simp only [MulEquiv.symm_apply_apply] at hdist
  exact hdist.trans (mul_le_mul_of_nonneg_left hpi (productMetricBound d).coe_nonneg)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {ι σ : Type*} [Fintype ι]
  {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  {w : σ → ℕ} (g : ∀ i, (D i).filtration.realification.PolynomialOrbit w)
  (N : ℕ) [NeZero N]

variable [DecidableEq ι]

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeProductPartition
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_native_product_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι σ : Type*} [Fintype ι] [DecidableEq ι]
      {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (w : σ → ℕ) {p ρ : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∀ g : (pi D).filtration.realification.PolynomialOrbit w,
        ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ A : Fin n → (pi D).Niltest w,
            (∀ j, (A j).orbit = g) ∧
            (∀ j, (A j).UnitIntervalValued) ∧
            (∀ j, (A j).ComplexityLE ((p + C) ^ C)) ∧
            (∀ z, ∑ j, ((A j).observable z).re = 1) ∧
            (letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
             ∀ j x y, 0 < ((A j).observable x).re → 0 < ((A j).observable y).re →
               ∀ i, dist (productProjection D i x) (productProjection D i y) ≤ ρ) := by
  obtain ⟨B, _, hpartition⟩ := exists_native_niltest_partition s 1
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + 2) ^ 2 + (X + 4) ^ 4 + (X + 2) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro ι σ _ _ L _ _ _ _ _ _ _ _ _ _ d D w p ρ hp hι hD hρ hρinv g
  let t := p + (p + 2) ^ 2 + (p + 4) ^ 4 + (p + 2) ^ a
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hgeom : (p + 2) ^ 2 ≤ t := by
    dsimp [t]
    linarith [show 0 ≤ (p + 4) ^ 4 from by positivity,
      show 0 ≤ (p + 2) ^ a from by positivity]
  let ε := ρ / Real.exp ((p + 4) ^ 4)
  have hε : 0 < ε := div_pos hρ (Real.exp_pos _)
  have hεinv : 1 / ε ≤ Real.exp ((t + 2) ^ 1) := by
    calc
      _ = Real.exp ((p + 4) ^ 4) * (1 / ρ) := by dsimp [ε]; field_simp
      _ ≤ Real.exp ((p + 4) ^ 4) * Real.exp ((p + 2) ^ a) :=
        mul_le_mul_of_nonneg_left hρinv (Real.exp_pos _).le
      _ = Real.exp ((p + 4) ^ 4 + (p + 2) ^ a) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [t]; simp only [pow_one]; nlinarith [sq_nonneg (p + 2)])
  obtain ⟨n, hn, hnb, A, horbit, hunit, hcomplexity, hsum, hdiam⟩ :=
    hpartition (pi D) w ht ((pi_geometry D hp hι hD).mono (pi D) hgeom) hε hεinv g
  have hcost : (t + B) ^ B ≤ (p + C) ^ C := by
    simpa [T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨n, hn, hnb.trans (Real.exp_le_exp.mpr hcost), A, horbit, hunit,
    fun j => (hcomplexity j).mono hcost, hsum, ?_⟩
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  intro j x y hx hy i
  have hxy := hdiam j x y hx hy
  have hprod := (productSpaceEquiv_lipschitz D).dist_le_mul x y
  have hcoord := dist_le_pi_dist (productSpaceEquiv D x) (productSpaceEquiv D y) i
  change dist (productProjection D i x) (productProjection D i y) ≤
    dist (productSpaceEquiv D x) (productSpaceEquiv D y) at hcoord
  calc
    _ ≤ (productMetricBound d : ℝ) * dist x y := hcoord.trans hprod
    _ ≤ (productMetricBound d : ℝ) * ε :=
      mul_le_mul_of_nonneg_left hxy (productMetricBound d).coe_nonneg
    _ ≤ Real.exp ((p + 4) ^ 4) * ε :=
      mul_le_mul_of_nonneg_right (productMetricBound_le_exp d hp hι (fun i => (hD i).1)) hε.le
    _ = ρ := by dsimp [ε]; field_simp

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProjectedNativeCoefficient
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {F : NilpotentLieFiltration L s} {w : σ → ℕ}

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem realSquarePairHom_component (z : F.squareFiltration.realification.Group) (b : Bool) :
    realBCHPiEquiv (fun _ : Bool => F) (F.realSquarePairHom z) b =
      cond b (F.realSquareFstHom z) (F.realSquareSndHom z) := by
  cases b
  · apply NilpotentLieBCHGroup.ext
    change realificationLieHom (liePiEval false) (realificationLieHom F.squarePairMap z.coord) =
      realificationLieHom F.squareSnd z.coord
    induction z.coord using TensorProduct.induction_on with
    | zero => simp
    | tmul r x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  · apply NilpotentLieBCHGroup.ext
    change realificationLieHom (liePiEval true) (realificationLieHom F.squarePairMap z.coord) =
      realificationLieHom F.squareFst z.coord
    induction z.coord using TensorProduct.induction_on with
    | zero => simp
    | tmul r x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]

theorem realSquarePairHom_normalization (ε γ a b : F.realification.Group)
    (z : F.squareFiltration.realification.Group)
    (hf : F.realSquareFstHom z = ε⁻¹ * a * γ⁻¹)
    (hs : F.realSquareSndHom z = b) :
    (realBCHPiEquiv (fun _ : Bool => F)).symm (fun flag => cond flag ε⁻¹ 1) *
      (realBCHPiEquiv (fun _ : Bool => F)).symm (fun flag => cond flag a b) *
      ((realBCHPiEquiv (fun _ : Bool => F)).symm (fun flag => cond flag γ 1))⁻¹ =
        F.realSquarePairHom z := by
  apply (realBCHPiEquiv (fun _ : Bool => F)).injective
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  funext flag
  rw [F.realSquarePairHom_component]
  cases flag <;> simp only [Pi.mul_apply, Pi.inv_apply, Bool.cond_false, Bool.cond_true,
    inv_one, one_mul, mul_one, hf, hs]

end Erdos3.NilpotentLieFiltration

namespace Erdos3

open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r) (F : NilpotentLieFiltration M t)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

end Erdos3.DegreeRankLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslatedShiftTesting
namespace OAI

universe u

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.PositiveCyclicNiltest

open scoped TensorProduct BigOperators

end Erdos3.PositiveCyclicNiltest

end

section

namespace Erdos3

open scoped TensorProduct

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_interval_refined_partition (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} [Fintype I] {s N : ℕ} [NeZero N]
      (A : I → ZMod N → ℝ) {p ρ : ℝ},
      1 ≤ s → 0 ≤ p → (Fintype.card I : ℝ) ≤ Real.exp p →
      (∀ i, PositiveCyclicNiltest.{0} s N p (A i)) → (∀ x, ∑ i, A i x = 1) →
      0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧ (Fintype.card (I × Fin n) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ U : (I × Fin n) → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} s N ((p + C) ^ C) (U j)) ∧
          (∀ x, ∑ j, U j x = 1) ∧
          (∀ j x, 0 < U j x → 0 < A j.1 x) ∧
          (∀ j x y, 0 < U j x → 0 < U j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) ∧
          (∀ h : ZMod N, ((cyclicWrapExceptional h ρ).card : ℝ) / N ≤ 6 * ρ + 3 / N) ∧
          ∀ h j x y, x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
            0 < U j x → 0 < U j y →
            |(x.val : ℝ) / N - (y.val : ℝ) / N| ≤ ρ ∧
              (N - h.val ≤ x.val ↔ N - h.val ≤ y.val) ∧
              ((h + x).val : ℤ) - ((h + y).val : ℤ) = (x.val : ℤ) - (y.val : ℤ) := by
  obtain ⟨B, _, hinterval⟩ := exists_interval_circle_partition a
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C B) ^ B
  let R := T + (T + 2) ^ 2 + 3
  let Q := (R + 2) ^ 2 + R + (R + (R ^ 2 + R + 3) ^ 2) + R ^ 2 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * T + Q)
  refine ⟨C, hC, ?_⟩
  intro I _ s N _ A p ρ hs hp hcard hA hsum hρ hρinv
  obtain ⟨n, hn, hnb, V, hV, hVsum, hdiam⟩ := hinterval N hp hρ hρinv
  let t := p + (p + B) ^ B
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hBt : (p + B) ^ B ≤ t := le_add_of_nonneg_left hp
  have hcost : 2 * t + productNiltestBudget (raisedNiltestBudget t) ≤ (p + C) ^ C := by
    simpa [T, X, R, Q, t, Polynomial.eval₂_pow, productNiltestBudget,
      productObservableLipBudget, raisedNiltestBudget] using hbudget p hp
  have hQ0 : 0 ≤ productNiltestBudget (raisedNiltestBudget t) := by
    unfold productNiltestBudget productObservableLipBudget raisedNiltestBudget
    positivity
  have hproduct : productNiltestBudget (raisedNiltestBudget t) ≤ (p + C) ^ C := by linarith
  have htC : t ≤ (p + C) ^ C := by linarith
  let U : (I × Fin n) → ZMod N → ℝ := fun j x => A j.1 x * V j.2 x
  have hpositive (j : I × Fin n) (x : ZMod N) (hx : 0 < U j x) :
      0 < A j.1 x ∧ 0 < V j.2 x := by
    change 0 < A j.1 x * V j.2 x at hx
    rcases mul_pos_iff.mp hx with h | h
    · exact h
    · linarith [((hA j.1).unit_interval x).1]
  refine ⟨n, hn, ?_, U, ?_, ?_, fun j x hx => (hpositive j x hx).1,
    fun j x y hx hy => hdiam j.2 x y (hpositive j x hx).2 (hpositive j y hy).2,
    fun h => cyclicWrapExceptional_density_le h hρ.le, ?_⟩
  · calc
      _ = (Fintype.card I : ℝ) * n := by rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      _ ≤ Real.exp p * Real.exp ((p + B) ^ B) :=
        mul_le_mul hcard hnb (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp t := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr htC
  · intro j
    exact (((hA j.1).mono le_rfl hpt).mul ((hV j.2).mono hs hBt) ht).mono le_rfl hproduct
  · intro x
    simp only [U, Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hVsum, mul_one]
    exact hsum x
  · intro h j x y hx hy hUx hUy
    have hxy := hdiam j.2 x y (hpositive j x hUx).2 (hpositive j y hUy).2
    exact ⟨good_circle_observations_control_representatives h x y hρ hx hy hxy,
      cyclic_wrap_branch_eq_of_good_circle h x y hρ hx hy hxy,
      cyclic_representative_difference_of_good_circle h x y hρ hx hy hxy⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedObservationRefinement
namespace OAI

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_fixed_observation_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
      {L : ι → Type v} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (N : ℕ) [NeZero N] {p ρ : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : Fin n → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{max u v} s N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
           ∀ j x y, 0 < A j x → 0 < A j y → ∀ i,
             dist ((D i).cyclicOrbitPoint (g i) N (fun _ : Unit => x))
               ((D i).cyclicOrbitPoint (g i) N (fun _ : Unit => y)) ≤ ρ) := by
  obtain ⟨C, hC, hpartition⟩ := exists_native_product_partition s a
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ _ _ _ _ d D g N _ p ρ hp hι hD hρ hρinv
  let G := NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) g
  obtain ⟨n, hn, hnb, tests, horbit, hunit, hcomplexity, hsum, hdiam⟩ :=
    hpartition D (fun _ : Unit => 1) hp hι hD hρ hρinv G
  let A : Fin n → ZMod N → ℝ := fun j x => ((tests j).evalCyclic N (fun _ : Unit => x)).re
  have heval (j : Fin n) (x : ZMod N) :
      A j x = ((tests j).observable ((pi D).cyclicOrbitPoint G N (fun _ : Unit => x))).re := by
    change ((tests j).observable (QuotientGroup.mk
      ((pi D).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (tests j).orbit))).re = _
    rw [horbit j]
    rfl
  have hpoint (i : ι) (x : ZMod N) :
      productProjection D i ((pi D).cyclicOrbitPoint G N (fun _ : Unit => x)) =
        (D i).cyclicOrbitPoint (g i) N (fun _ : Unit => x) := by
    exact congrArg (fun z : (D i).RealGroup => (QuotientGroup.mk z : (D i).Space))
      (NilpotentLieFiltration.piRealOrbit_eval (fun i => (D i).filtration) g
        (fun _ : Unit => (x.val : ℤ)) i)
  refine ⟨n, hn, hnb, A, ?_, ?_, ?_⟩
  · intro j
    exact .of_test (pi D) le_rfl (tests j) (hunit j) (hcomplexity j) (fun _ => rfl)
  · intro x
    simpa only [heval] using hsum ((pi D).cyclicOrbitPoint G N (fun _ : Unit => x))
  · let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
    intro j x y hx hy i
    have hd := hdiam j _ _ ((heval j x) ▸ hx) ((heval j y) ▸ hy) i
    simpa only [hpoint] using hd

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_fixed_shifted_observation_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (N : ℕ) [NeZero N] {p ρ : ℝ},
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : Fin n → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} s N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
           ∀ j x y, 0 < A j x → 0 < A j y → ∀ i (t : ℤ), |t| ≤ 1 →
             dist ((D i).integerOrbitPoint (g i) ((x.val : ℤ) + t * N))
               ((D i).integerOrbitPoint (g i) ((y.val : ℤ) + t * N)) ≤ ρ) := by
  obtain ⟨B, _, hpartition⟩ := exists_fixed_observation_partition.{0, 0} s a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((3 * X + 3 + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ d D g N _ p ρ hp hι hD hρ hρinv
  let E := fun k : ι × Fin 3 => D k.1
  let G := fun k : ι × Fin 3 =>
    (g k.1).translate (fun _ => Nat.zero_lt_one) (fun _ => ((k.2.val : ℤ) - 1) * N)
  let : FiniteDimensional ℚ (∀ k : ι × Fin 3, L k.1) :=
    (productFinBasis E).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ k : ι × Fin 3, L k.1))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ k : ι × Fin 3, L k.1)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ k : ι × Fin 3, L k.1)) :=
    realification_moduleTopology_t2 (productFinBasis E)
  let r := 3 * p + 3
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hr : 0 ≤ r := hp.trans hpr
  have hcount : (Fintype.card (ι × Fin 3) : ℝ) ≤ r := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
    dsimp [r]
    linarith
  have hinv : 1 / ρ ≤ Real.exp ((r + 2) ^ a) :=
    hρinv.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) a))
  obtain ⟨n, hn, hnb, A, hA, hsum, hdiam⟩ :=
    hpartition E G N hr hcount (fun k => (hD k.1).mono (D k.1) hpr) hρ hinv
  have hcost : (r + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, r, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨n, hn, hnb.trans (Real.exp_le_exp.mpr hcost), A,
    fun j => (hA j).mono le_rfl hcost, hsum, ?_⟩
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  intro j x y hx hy i t ht
  have ht' := abs_le.mp ht
  let k : Fin 3 := ⟨(t + 1).toNat, by omega⟩
  have hk : (k.val : ℤ) - 1 = t := by dsimp [k]; omega
  simpa only [E, G, cyclicOrbitPoint_translate, hk] using hdiam j x y hx hy (i, k)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntervalResiduePartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_fixed_shifted_residue_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (q N : ℕ) [NeZero q] [NeZero N] {p ρ : ℝ},
      1 ≤ s → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (q : ℝ) ≤ Real.exp p → 0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧ ((n * q : ℕ) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : (Fin n × ZMod q) → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} s N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (∀ j x, 0 < A j x → (x.val : ZMod q) = j.2) ∧
          (letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
           ∀ j x y, 0 < A j x → 0 < A j y → ∀ i (t : ℤ), |t| ≤ 1 →
             dist ((D i).integerOrbitPoint (g i) ((x.val : ℤ) + t * N))
               ((D i).integerOrbitPoint (g i) ((y.val : ℤ) + t * N)) ≤ ρ) := by
  obtain ⟨B, _, hpartition⟩ := exists_fixed_shifted_observation_partition s a
  obtain ⟨R, _, hrefine⟩ := exists_controlled_residue_refinement
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C R) ^ R)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ d D g q N _ _ p ρ hs hp hι hD hq hρ hρinv
  obtain ⟨n, hn, hnb, A, hA, hsum, hdiam⟩ := hpartition D g N hp hι hD hρ hρinv
  let t := p + (p + B) ^ B
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hBt : (p + B) ^ B ≤ t := le_add_of_nonneg_left hp
  obtain ⟨U, hcount, hU, hUsum, hsupport⟩ := hrefine (q := q) A ht hs
    (by simpa only [Fintype.card_fin] using hnb.trans (Real.exp_le_exp.mpr hBt))
    (hq.trans (Real.exp_le_exp.mpr hpt)) (fun j => (hA j).mono le_rfl hBt) hsum
  have hsumcost : t + (t + R) ^ R ≤ (p + C) ^ C := by
    simpa [T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (t + R) ^ R ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsumcost
  refine ⟨n, hn, ?_, U, fun j => (hU j).mono le_rfl hcost, hUsum,
    fun j x hx => (hsupport j x hx).2, ?_⟩
  · simpa only [Fintype.card_prod, Fintype.card_fin, ZMod.card] using
      hcount.trans (Real.exp_le_exp.mpr hcost)
  · let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
    intro j x y hx hy i t ht
    exact hdiam j.1 x y (hsupport j x hx).1 (hsupport j y hy).1 i t ht

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSharedFrozenCorrelations
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
  (φ : L →ₗ⁅ℚ⁆ M) (a r : E.RealGroup)
  (h : ∀ γ ∈ D.realLattice,
    r⁻¹ * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ γ * r ∈ E.realLattice)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem native_frozenCosetMap_dist_le {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {s d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (φ : L →ₗ⁅ℚ⁆ M) (r a b : E.RealGroup)
    (h : ∀ γ ∈ D.realLattice, r⁻¹ * realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ γ * r ∈ E.realLattice)
    {A C : ℝ≥0}
    (hφ :
      letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
      LipschitzWith C (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
    (ha :
      letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
      LipschitzWith A (fun x => a * x)) (x y : D.RealGroup) :
    letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot)
      (E.basis.baseChange ℝ)
    letI := D.metricSpace
    letI := E.metricSpace
    let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ
    dist (QuotientGroup.mk (a * ψ x * r) : E.Space) (QuotientGroup.mk (b * ψ y * r)) ≤
      (A * C : ℝ≥0) * dist (QuotientGroup.mk x : D.Space) (QuotientGroup.mk y) + dist a b := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (D.basis.baseChange ℝ).finiteDimensional_of_finite
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] M) := (E.basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := E.filtration.realification.lowerCentralSeries_eq_bot)
    (E.basis.baseChange ℝ)
  exact frozenCosetMap_dist_le D.realLattice E.realLattice D.realLattice_closed_discrete.1
    E.realLattice_closed_discrete.1 _ r h a b hφ ha (QuotientGroup.mk x) (QuotientGroup.mk y)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

theorem mapped_normal_conjugation_mem {G H : Type*} [Group G] [Group H]
    (Γ Λ : Subgroup G) (hle : Λ ≤ Γ) (hnormal : (Λ.subgroupOf Γ).Normal)
    (f : G →* H) {κ x : H} (hκ : κ ∈ Γ.map f) (hx : x ∈ Λ.map f) :
    κ * x * κ⁻¹ ∈ Λ.map f := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hκ
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_map.mpr ⟨k * y * k⁻¹,
    (Subgroup.normal_subgroupOf_iff hle).mp hnormal y k hy hk, ?_⟩
  simp only [map_mul, map_inv]

namespace RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

theorem normalized_right_compatibility {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (φ : L →ₗ⁅ℚ⁆ M) (q : ℕ) (hq : 0 < q) (Λ : Subgroup D.filtration.Group)
    (hconj : Λ ≤ D.conjugationPullback E φ q) (hle : Λ ≤ D.lattice)
    (hnormal : (Λ.subgroupOf D.lattice).Normal)
    (κ : D.RealGroup) (hκ : κ ∈ D.realLattice) (r : E.RealGroup)
    (hr : (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q) :
    let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ
    ∀ x ∈ Λ.map realificationHom, (ψ κ⁻¹ * r)⁻¹ * ψ x * (ψ κ⁻¹ * r) ∈ E.realLattice := by
  let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ
  have hright := D.real_conjugationPullback_property E φ q hq Λ hconj r hr
  dsimp only
  intro x hx
  have hmem := mapped_normal_conjugation_mem D.lattice Λ hle hnormal realificationHom hκ hx
  have heq : (ψ κ⁻¹ * r)⁻¹ * ψ x * (ψ κ⁻¹ * r) = r⁻¹ * ψ (κ * x * κ⁻¹) * r := by
    simp only [map_mul, map_inv]
    group
  rw [heq]
  exact hright _ hmem

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerRefilteredCyclicExpansion
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped NNReal TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped NNReal TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_native_immersion_local_inverse (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M), Function.Injective φ → ∀ {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∃ Λ : Subgroup E.filtration.Group,
        Λ ≤ E.lattice ∧ (Λ.subgroupOf E.lattice).Characteristic ∧
        (Λ.subgroupOf E.lattice).Normal ∧ (Λ.subgroupOf E.lattice).FiniteIndex ∧
        (Λ.relIndex E.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates E.basis Λ)
          (hout : bchSubgroupCoordinates E.basis Λ ⊆ denominatorGrid N),
          let Q := E.withLattice Λ N hN hin hout
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          letI := D.metricSpace
          letI := Q.metricSpace
          let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ
          ∀ x y : D.RealGroup,
            dist (QuotientGroup.mk (ψ x) : Q.Space) (QuotientGroup.mk (ψ y)) <
              Real.exp (-((p + C) ^ C)) →
            dist (QuotientGroup.mk x : D.Space) (QuotientGroup.mk y) ≤
              Real.exp ((p + C) ^ C) *
                dist (QuotientGroup.mk (ψ x) : Q.Space) (QuotientGroup.mk (ψ y)) := by
  obtain ⟨C, hC, hreconstruct⟩ := exists_uniform_native_positive_reconstruction s
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ hφ p hp hD hE hheight
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ, hrec⟩ :=
    hreconstruct D E φ hp hD hE hheight
  let Q := E.withLattice Λ N hN hin hout
  let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ
  have hψ : Function.Injective ψ := by
    let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
    have hf := Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ) φ.toLinearMap hφ
    intro x y hxy
    apply NilpotentLieBCHGroup.ext
    exact hf (congrArg NilpotentLieBCHGroup.coord hxy)
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ, ?_⟩
  let := D.metricSpace
  let := Q.metricSpace
  let K : ℝ≥0 := ⟨Real.exp ((p + C) ^ C), (Real.exp_pos _).le⟩
  have hcapped : ∀ a : D.Space, ∃ (v : Q.Space → ℂ) (B : ℝ≥0), B ≤ K ∧
      LipschitzWith B v ∧ ∀ x : D.RealGroup,
        v (QuotientGroup.mk (ψ x)) = cappedDistanceTest a (QuotientGroup.mk x) := by
    intro a
    obtain ⟨v, B, hB, hv, _, _, heval⟩ := hrec (cappedDistanceTest a) 1
      (by simpa only [NNReal.coe_one] using Real.one_le_exp hp)
      (cappedDistanceTest_lipschitz a) (cappedDistanceTest_unit_interval a) (by
        intro k hk x
        have hk1 : k = 1 := hψ ((MonoidHom.mem_ker.mp hk).trans (map_one ψ).symm)
        simp only [hk1, one_mul])
    exact ⟨v, B, hB, hv, heval⟩
  dsimp only
  intro x y hnear
  apply local_dist_le_of_positive_reconstruction
    (fun x : D.RealGroup => (QuotientGroup.mk x : D.Space))
    (fun x : D.RealGroup => (QuotientGroup.mk (ψ x) : Q.Space)) K hcapped x y
  change Real.exp ((p + C) ^ C) *
    dist (QuotientGroup.mk (ψ x) : Q.Space) (QuotientGroup.mk (ψ y)) < 1
  calc
    _ < Real.exp ((p + C) ^ C) * Real.exp (-((p + C) ^ C)) :=
      mul_lt_mul_of_pos_left hnear (Real.exp_pos ((p + C) ^ C))
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SquareRecoveryCoordinates
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

omit [DecidableEq ι] in
theorem realProductFinBasis_repr (x : ℝ ⊗[ℚ] (∀ i, L i))
    (k : Fin (Fintype.card (Σ i, Fin (d i)))) :
    let z := (Fintype.equivFin (Σ i, Fin (d i))).symm k
    ((pi D).basis.baseChange ℝ).repr x k =
      ((D z.1).basis.baseChange ℝ).repr (realificationLieHom (liePiEval z.1) x) z.2 := by
  dsimp only
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [Basis.baseChange_repr_tmul, realificationLieHom_tmul,
      productFinBasis_repr D, liePiEval_apply]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem realProductFinBasis_pi_symm_bound (g : ∀ i, (D i).RealGroup) {R : ℝ}
    (hg : ∀ i j, |((D i).basis.baseChange ℝ).repr (g i).coord j| ≤ R)
    (k : Fin (Fintype.card (Σ i, Fin (d i)))) :
    |((pi D).basis.baseChange ℝ).repr
      ((realBCHPiEquiv (fun i => (D i).filtration)).symm g).coord k| ≤ R := by
  rw [realProductFinBasis_repr D]
  let z := (Fintype.equivFin (Σ i, Fin (d i))).symm k
  change |((D z.1).basis.baseChange ℝ).repr
    (productProjectionHom D z.1 ((realBCHPiEquiv (fun i => (D i).filtration)).symm g)).coord z.2| ≤ R
  rw [productProjectionHom_pi_symm]
  exact hg z.1 z.2

theorem pi_symm_mem_realLattice (g : ∀ i, (D i).RealGroup)
    (hg : ∀ i, g i ∈ (D i).realLattice) :
    (realBCHPiEquiv (fun i => (D i).filtration)).symm g ∈ (pi D).realLattice := by
  apply (realBCHPiEquiv_mem_lattice (fun i => (D i).filtration)
    (fun i => (D i).lattice) _).mpr
  intro i
  rw [MulEquiv.apply_symm_apply]
  change g i ∈ (D i).realLattice
  exact hg i

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L κ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

omit [Fintype κ] in
theorem squareNormalizer_coordinate_bound (ε : D.RealGroup) {R : ℝ} (hR : 0 ≤ R)
    (hε : ∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ R)
    (j : Fin (Fintype.card (Σ _ : Bool, Fin d))) :
    |((pi (fun _ : Bool => D)).basis.baseChange ℝ).repr
      ((realBCHPiEquiv (fun _ : Bool => D.filtration)).symm
        (fun flag => cond flag ε⁻¹ 1)).coord j| ≤ R := by
  apply realProductFinBasis_pi_symm_bound
  intro flag i
  cases flag
  · simpa only [Bool.cond_false, coord_one, map_zero, Finsupp.zero_apply, abs_zero] using hR
  · simpa only [Bool.cond_true, coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hε i

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSquareRecovery
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open Module

namespace RationalFilteredNilmanifold

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_normalized_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d e : ℕ} (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N),
          let Q := D.withLattice Λ N hN hin hout
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot)
            (E.basis.baseChange ℝ)
          letI := Q.metricSpace
          letI := E.metricSpace
          let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ
          ∀ κ : D.RealGroup, κ ∈ D.realLattice → ∀ r : E.RealGroup,
            (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∀ a b : E.RealGroup,
              (∀ i, |(E.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
              ∀ x y : D.RealGroup,
                dist (QuotientGroup.mk (a * ψ x * (ψ κ⁻¹ * r)) : E.Space)
                    (QuotientGroup.mk (b * ψ y * (ψ κ⁻¹ * r))) ≤
                  Real.exp ((p + C) ^ C) * dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) +
                    dist a b := by
  obtain ⟨c₀, _, hcover⟩ := exists_uniform_conjugated_source_cover s
  obtain ⟨c₁, _, hleft⟩ := exists_uniform_left_lipschitz_exp_bound s k
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C c₀) ^ c₀ + (X + 1 + Polynomial.C c₁) ^ c₁ + (X + 1 + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ p hp hD hE hφ q hq hqp
  obtain ⟨Λ, htarget, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ⟩ :=
    hcover D E φ p hp hD hE hφ q hq hqp
  let Q := D.withLattice Λ N hN hin hout
  let t := p + 1
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hsum : (p + c₀) ^ c₀ + (t + c₁) ^ c₁ + (t + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [P, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hcoverC : (p + c₀) ^ c₀ ≤ (p + C) ^ C := by
    nlinarith [pow_nonneg (show 0 ≤ t + c₁ by positivity) c₁, sq_nonneg (t + 2)]
  have hmetricC : (t + c₁) ^ c₁ + (t + 2) ^ 2 ≤ (p + C) ^ C := by
    nlinarith [pow_nonneg (show 0 ≤ p + c₀ by positivity) c₀]
  let H := ⌈Real.exp p⌉₊
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  obtain ⟨A, _, hA, hALip⟩ := hleft (E.basis.baseChange ℝ) (lieStructureConstants E.basis) H t
    E.filtration.realification.lowerCentralSeries_eq_bot
    (fun i j k => (realLieBasis_structure E.basis i j k).symm) ht
    (by simpa only [Fintype.card_fin] using hE.1.trans hpt) (ceil_exp_le_exp_add_one hp)
    (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
  obtain ⟨B, _, hB, hBLip⟩ := exists_realificationMap_lipschitz_exp_bound
    (hnil := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot)
    D.basis E.basis φ H ht
    (by simpa only [Fintype.card_fin] using hD.1.trans hpt)
    (by simpa only [Fintype.card_fin] using hE.1.trans hpt) (ceil_exp_le_exp_add_one hp)
    (fun i j => rationalHeightLE_ceil_exp (hφ i j))
  have hAB : ((A * B : ℝ≥0) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ ≤ Real.exp ((t + c₁) ^ c₁) * Real.exp ((t + 2) ^ 2) := by push_cast; gcongr
      _ = Real.exp ((t + c₁) ^ c₁ + (t + 2) ^ 2) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hmetricC
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hcoverC),
    N, hN, hin, hout, hQ.mono Q hcoverC, ?_⟩
  let := Q.metricSpace
  let := E.metricSpace
  dsimp only
  intro κ hκ r hr a b ha x y
  have ha' : LipschitzWith A (fun z => a * z) := hALip a (fun i =>
    (ha i).trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by dsimp [t]; linarith) k)))
  have hcompat := D.normalized_right_compatibility E φ q hq Λ htarget hΛ hnormal κ hκ r hr
  have hdist := native_frozenCosetMap_dist_le Q E φ _ a b hcompat hBLip ha' x y
  exact hdist.trans (add_le_add (mul_le_mul_of_nonneg_right hAB dist_nonneg) le_rfl)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_subgroup_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M), Function.Injective φ → ∀ {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup E.filtration.Group, Λ ≤ E.lattice ∧
        (Λ.subgroupOf E.lattice).Characteristic ∧ (Λ.subgroupOf E.lattice).Normal ∧
        (Λ.subgroupOf E.lattice).FiniteIndex ∧ (Λ.relIndex E.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates E.basis Λ)
          (hout : bchSubgroupCoordinates E.basis Λ ⊆ denominatorGrid N),
          let Q := E.withLattice Λ N hN hin hout
          Q.GeometryComplexityLE ((p + C) ^ C) ∧
          letI := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot)
            (E.basis.baseChange ℝ)
          letI := D.metricSpace
          letI := Q.metricSpace
          let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) φ
          ∀ κ : E.RealGroup, κ ∈ E.realLattice → ∀ r : E.RealGroup,
            (E.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∀ a b x y : E.RealGroup, ∀ u v : D.RealGroup,
              (∀ i, |(E.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
              a * x * (κ⁻¹ * r) = ψ u → b * y * (κ⁻¹ * r) = ψ v →
              dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) + dist a b <
                Real.exp (-((p + C) ^ C)) →
              dist (QuotientGroup.mk u : D.Space) (QuotientGroup.mk v) ≤
                Real.exp ((p + C) ^ C) *
                  (dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) + dist a b) := by
  obtain ⟨A, _, hinverse⟩ := exists_native_immersion_local_inverse s
  obtain ⟨B, _, hnormalize⟩ := exists_uniform_normalized_recovery s k
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  let P := T + (T + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d e D E φ hφ p hp hD hE hheight q hq hqp
  obtain ⟨Λ₀, _, _, _, _, _, N₀, hN₀, hin₀, hout₀, hE₀, hlocal⟩ :=
    hinverse D E φ hφ hp hD hE hheight
  let E₀ := E.withLattice Λ₀ N₀ hN₀ hin₀ hout₀
  let t := p + (p + A) ^ A
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
  have hidHeight : ∀ i j, rationalLogHeight (E₀.basis.repr ((LieHom.id : M →ₗ⁅ℚ⁆ M) (E.basis j)) i) ≤ t := by
    intro i j
    apply rationalLogHeight_le_of_height (H := 1) _ (by simpa using Real.one_le_exp ht)
    change RationalHeightLE (E.basis.repr (E.basis j) i) 1
    rw [Basis.repr_self]
    by_cases h : j = i <;> simp [h, RationalHeightLE]
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, N, hN, hin, hout, hQ, hnorm⟩ :=
    hnormalize E E₀ (LieHom.id : M →ₗ⁅ℚ⁆ M) ht (hE.mono E hpt) (hE₀.mono E₀ hAt)
      hidHeight q hq (hqp.trans (Real.exp_le_exp.mpr hpt))
  let Q := E.withLattice Λ N hN hin hout
  let ψ := realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
    (hM := E.filtration.lowerCentralSeries_eq_bot) φ
  have hsum : t + (t + B) ^ B ≤ (p + C) ^ C := by
    simpa [P, T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hBC : (t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have hABC : (p + A) ^ A + (t + B) ^ B ≤ (p + C) ^ C := by
    dsimp [t] at hsum
    linarith
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hBC),
    N, hN, hin, hout, hQ.mono Q hBC, ?_⟩
  let := rightMetricSpace (hnil := E.filtration.realification.lowerCentralSeries_eq_bot) (E.basis.baseChange ℝ)
  let := D.metricSpace
  let := Q.metricSpace
  let := E₀.metricSpace
  have hid (z : E.RealGroup) : realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := E₀.filtration.lowerCentralSeries_eq_bot) (LieHom.id : M →ₗ⁅ℚ⁆ M) z = z := by
    apply NilpotentLieBCHGroup.ext
    exact realificationLieHom_id_apply z.coord
  dsimp only
  intro κ hκ r hr a b x y u v ha hu hv hnear
  have ha' : ∀ i, |(E.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((t + 2) ^ k) :=
    fun i => (ha i).trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) k))
  have hd := hnorm κ hκ r hr a b ha' x y
  simp only [hid] at hd
  rw [hu, hv] at hd
  change dist (QuotientGroup.mk (ψ u) : E₀.Space) (QuotientGroup.mk (ψ v)) ≤
    Real.exp ((t + B) ^ B) * dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) +
      dist a b at hd
  let delta := dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) + dist a b
  have hdelta : 0 ≤ delta := add_nonneg dist_nonneg dist_nonneg
  have hNpos : 1 ≤ Real.exp ((t + B) ^ B) := Real.one_le_exp (pow_nonneg (by positivity) _)
  have hbound : dist (QuotientGroup.mk (ψ u) : E₀.Space) (QuotientGroup.mk (ψ v)) ≤
      Real.exp ((t + B) ^ B) * delta := by
    apply hd.trans
    dsimp [delta]
    calc
      _ ≤ Real.exp ((t + B) ^ B) *
          dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) +
          Real.exp ((t + B) ^ B) * dist a b :=
        add_le_add le_rfl (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hNpos (show 0 ≤ dist a b from dist_nonneg))
      _ = _ := (mul_add _ _ _).symm
  have hsmall : dist (QuotientGroup.mk (ψ u) : E₀.Space) (QuotientGroup.mk (ψ v)) <
      Real.exp (-((p + A) ^ A)) := by
    apply hbound.trans_lt
    calc
      _ < Real.exp ((t + B) ^ B) * Real.exp (-((p + C) ^ C)) :=
        mul_lt_mul_of_pos_left hnear (Real.exp_pos _)
      _ = Real.exp ((t + B) ^ B - (p + C) ^ C) := by rw [← Real.exp_add, sub_eq_add_neg]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  apply (hlocal u v hsmall).trans
  calc
    _ ≤ Real.exp ((p + A) ^ A) * (Real.exp ((t + B) ^ B) * delta) :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
    _ = Real.exp ((p + A) ^ A + (t + B) ^ B) * delta := by rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hABC) hdelta

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_factorwise_subgroup_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
      {M : Type*} [LieRing M] [LieAlgebra ℚ M]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      {d : ι → ℕ} {e : ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (V : RationalFilteredNilmanifold M s e) (φ : M →ₗ⁅ℚ⁆ (∀ i, L i)),
      Function.Injective φ → ∀ {p : ℝ}, 0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (pi D).GeometryComplexityLE p →
      V.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight ((pi D).basis.repr (φ (V.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ (Δ : ∀ i, Subgroup (D i).filtration.Group) (N : ι → ℕ)
        (hN : ∀ i, 0 < N i)
        (hin : ∀ i, scaledIntegerGrid (N i) ⊆ bchSubgroupCoordinates (D i).basis (Δ i))
        (hout : ∀ i, bchSubgroupCoordinates (D i).basis (Δ i) ⊆ denominatorGrid (N i)),
        let E := fun i => (D i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
        (∀ i, Δ i ≤ (D i).lattice ∧ ((Δ i).subgroupOf (D i).lattice).Characteristic ∧
          ((Δ i).subgroupOf (D i).lattice).Normal ∧ ((Δ i).subgroupOf (D i).lattice).FiniteIndex ∧
          ((Δ i).relIndex (D i).lattice : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        (∀ i, (E i).GeometryComplexityLE ((p + C) ^ C)) ∧
        (pi E).GeometryComplexityLE ((p + C) ^ C) ∧
        letI : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
        letI := V.metricSpace
        let ψ := realificationMap (hnil := V.filtration.lowerCentralSeries_eq_bot)
          (hM := (pi D).filtration.lowerCentralSeries_eq_bot) φ
        ∀ κ : (pi D).RealGroup, κ ∈ (pi D).realLattice → ∀ r : (pi D).RealGroup,
          ((pi D).basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
          ∀ a b x y : (pi D).RealGroup, ∀ u v : V.RealGroup,
            (∀ i, |((pi D).basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            a * x * (κ⁻¹ * r) = ψ u → b * y * (κ⁻¹ * r) = ψ v →
            ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ Real.exp (-((p + C) ^ C)) →
              (∀ i, dist (QuotientGroup.mk (productProjectionHom D i x) : (E i).Space)
                (QuotientGroup.mk (productProjectionHom D i y)) ≤ ρ) →
              (∀ i,
                letI := rightMetricSpace (hnil := (D i).filtration.realification.lowerCentralSeries_eq_bot)
                  ((D i).basis.baseChange ℝ)
                dist (productProjectionHom D i a) (productProjectionHom D i b) ≤ ρ) →
              dist (QuotientGroup.mk u : V.Space) (QuotientGroup.mk v) ≤ Real.exp ((p + C) ^ C) * ρ := by
  obtain ⟨A, _, hrecovery⟩ := exists_uniform_subgroup_recovery s k
  obtain ⟨B, _, hfactor⟩ := exists_native_factorwise_covers
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  let F := (X + 4) ^ 4 + 1
  let P := T + (T + Polynomial.C B) ^ B + F + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ _ _ _ _ M _ _ _ _ _ _ d e D V φ hφ p hp hι hD hprod hV hheight q hq hqp
  obtain ⟨Λ, _, _, _, _, _, m, hm, hin₀, hout₀, hQ, hrecover⟩ :=
    hrecovery V (pi D) φ hφ hp hV hprod hheight q hq hqp
  let Q := (pi D).withLattice Λ m hm hin₀ hout₀
  let t := p + (p + A) ^ A
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
  obtain ⟨Δ, N, hN, hin, hout, hindex, hE, hpi, hsub⟩ :=
    hfactor D Λ m hm hin₀ ht (hι.trans hpt) (fun i => (hD i).mono (D i) hpt)
      (hQ.2.1.trans (Real.exp_le_exp.mpr hAt))
  let E := fun i => (D i).withLattice (Δ i) (N i) (hN i) (hin i) (hout i)
  have hsum : t + (t + B) ^ B + ((p + 4) ^ 4 + 1) + 1 ≤ (p + C) ^ C := by
    simpa [P, F, T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have hBC : (t + B) ^ B ≤ (p + C) ^ C := by
    linarith [show 0 ≤ (p + 4) ^ 4 from by positivity]
  have hAC : (p + A) ^ A + ((p + 4) ^ 4 + 1) + 1 ≤ (p + C) ^ C := by
    linarith [show 0 ≤ (t + B) ^ B from by positivity]
  refine ⟨Δ, N, hN, hin, hout, ?_, fun i => (hE i).mono (E i) hBC, hpi.mono (pi E) hBC, ?_⟩
  · intro i
    rcases hindex i with ⟨hle, hchar, hnormal, hfinite, hi⟩
    exact ⟨hle, hchar, hnormal, hfinite, hi.trans (Real.exp_le_exp.mpr hBC)⟩
  let : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
  let := V.metricSpace
  let := Q.metricSpace
  let := (pi E).metricSpace
  let := rightMetricSpace (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
    ((pi D).basis.baseChange ℝ)
  dsimp only
  intro κ hκ r hr a b x y u v ha hu hv ρ hρ hsmall hinput hleft
  have hcoord : dist (productSpaceEquiv E (QuotientGroup.mk x))
      (productSpaceEquiv E (QuotientGroup.mk y)) ≤ ρ := (dist_pi_le_iff hρ).mpr hinput
  have hfull := (productSpaceEquiv_symm_lipschitz E).dist_le_mul
    (productSpaceEquiv E (QuotientGroup.mk x)) (productSpaceEquiv E (QuotientGroup.mk y))
  simp only [Equiv.symm_apply_apply] at hfull
  have hprojection : dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) ≤
      dist (QuotientGroup.mk x : (pi E).Space) (QuotientGroup.mk y) := by
    have h := (sublatticeProjection_lipschitz Q (pi E) hsub rfl).dist_le_mul
      (QuotientGroup.mk x) (QuotientGroup.mk y)
    change dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) ≤
      (1 : ℝ) * dist (QuotientGroup.mk x : (pi E).Space) (QuotientGroup.mk y) at h
    simpa only [one_mul] using h
  have hcovered : dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) ≤
      (productMetricBound d : ℝ) * ρ :=
    hprojection.trans (hfull.trans (mul_le_mul_of_nonneg_left hcoord (productMetricBound d).coe_nonneg))
  have hleftbound := native_product_group_dist_le D a b hρ hleft
  have hK : 2 * (productMetricBound d : ℝ) ≤ Real.exp ((p + 4) ^ 4 + 1) := by
    calc
      _ ≤ Real.exp 1 * Real.exp ((p + 4) ^ 4) :=
        mul_le_mul (by linarith [Real.add_one_le_exp (1 : ℝ)])
          (productMetricBound_le_exp d hp hι (fun i => (hD i).1))
          (productMetricBound d).coe_nonneg (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, add_comm]
  have htotal : dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) + dist a b ≤
      Real.exp ((p + 4) ^ 4 + 1) * ρ := by
    calc
      _ ≤ (productMetricBound d : ℝ) * ρ + (productMetricBound d : ℝ) * ρ :=
        add_le_add hcovered hleftbound
      _ = (2 * (productMetricBound d : ℝ)) * ρ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hK hρ
  have hnear : dist (QuotientGroup.mk x : Q.Space) (QuotientGroup.mk y) + dist a b <
      Real.exp (-((p + A) ^ A)) := by
    calc
      _ ≤ Real.exp ((p + 4) ^ 4 + 1) * ρ := htotal
      _ ≤ Real.exp ((p + 4) ^ 4 + 1) * Real.exp (-((p + C) ^ C)) :=
        mul_le_mul_of_nonneg_left hsmall (Real.exp_pos _).le
      _ = Real.exp (((p + 4) ^ 4 + 1) - (p + C) ^ C) := by
        rw [← Real.exp_add, sub_eq_add_neg]
      _ < _ := Real.exp_lt_exp.mpr (by linarith)
  apply (hrecover κ hκ r hr a b x y u v ha hu hv hnear).trans
  calc
    _ ≤ Real.exp ((p + A) ^ A) * (Real.exp ((p + 4) ^ 4 + 1) * ρ) :=
      mul_le_mul_of_nonneg_left htotal (Real.exp_pos _).le
    _ = Real.exp ((p + A) ^ A + ((p + 4) ^ 4 + 1)) * ρ := by rw [← mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hρ

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeTwoSitePartition
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_native_two_site_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (q N : ℕ) [NeZero q] [NeZero N] {p ρ : ℝ},
      1 ≤ s → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (D i).GeometryComplexityLE p) →
      (q : ℝ) ≤ Real.exp p → 0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n m : ℕ, 0 < n ∧ 0 < m ∧
        (Fintype.card ((Fin n × ZMod q) × Fin m) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : ((Fin n × ZMod q) × Fin m) → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} s N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (∀ j x, 0 < A j x → (x.val : ZMod q) = j.1.2) ∧
          (∀ j x y, 0 < A j x → 0 < A j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) ∧
          (∀ h : ZMod N, ((cyclicWrapExceptional h ρ).card : ℝ) / N ≤ 6 * ρ + 3 / N) ∧
          (letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
           (∀ j x y, 0 < A j x → 0 < A j y → ∀ i (t : ℤ), |t| ≤ 1 →
             dist ((D i).integerOrbitPoint (g i) ((x.val : ℤ) + t * N))
               ((D i).integerOrbitPoint (g i) ((y.val : ℤ) + t * N)) ≤ ρ) ∧
           ∀ (h : ZMod N) (b : Fin 2) j k x y,
             x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
             0 < A j x * A k (x + h) → 0 < A j y * A k (y + h) → ∀ i,
               dist ((D i).integerOrbitPoint (g i) ((x.val : ℤ) + h.val - (b.val : ℤ) * N))
                 ((D i).integerOrbitPoint (g i) ((y.val : ℤ) + h.val - (b.val : ℤ) * N)) ≤ ρ) := by
  obtain ⟨B, _, hpartition⟩ := exists_fixed_shifted_residue_partition s a
  obtain ⟨R, _, hrefine⟩ := exists_interval_refined_partition a
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C R) ^ R)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ d D g q N _ _ p ρ hs hp hι hD hq hρ hρinv
  obtain ⟨n, hn, hnb, U, hU, hUsum, hres, hobs⟩ :=
    hpartition D g q N hs hp hι hD hq hρ hρinv
  let t := p + (p + B) ^ B
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hBt : (p + B) ^ B ≤ t := le_add_of_nonneg_left hp
  have hinv : 1 / ρ ≤ Real.exp ((t + 2) ^ a) :=
    hρinv.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) a))
  obtain ⟨m, hm, hcount, A, hA, hsum, hsupport, hcircle, hexception, _⟩ :=
    hrefine U hs ht
      (by simpa only [Fintype.card_prod, Fintype.card_fin, ZMod.card, Nat.cast_mul] using
        hnb.trans (Real.exp_le_exp.mpr hBt))
      (fun j => (hU j).mono le_rfl hBt) hUsum hρ hinv
  have hcost : (t + R) ^ R ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨n, m, hn, hm, hcount.trans (Real.exp_le_exp.mpr hcost), A,
    fun j => (hA j).mono le_rfl hcost, hsum,
    fun j x hx => hres j.1 x (hsupport j x hx), hcircle, hexception, ?_⟩
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  have hdiam j x y (hx : 0 < A j x) (hy : 0 < A j y) (i : ι) (k : ℤ) (hk : |k| ≤ 1) :
      dist ((D i).integerOrbitPoint (g i) ((x.val : ℤ) + k * N))
        ((D i).integerOrbitPoint (g i) ((y.val : ℤ) + k * N)) ≤ ρ :=
    hobs j.1 x y (hsupport j x hx) (hsupport j y hy) i k hk
  refine ⟨hdiam, ?_⟩
  intro h b j k x y hx hy hxy hyy i
  exact positive_cell_ordinary_shift_recovery A A ((D i).integerOrbitPoint (g i)) hρ
    (fun j x => ((hA j).unit_interval x).1) hcircle
    (fun j x y hx hy t ht => hdiam j x y hx hy i t ht) h b j k x y hx hy hxy hyy

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RecoveryPrecision
namespace OAI

section

namespace Erdos3

theorem recovery_precision_bounds {r K ε : ℝ} (hr : 0 ≤ r)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hinv : 1 / ε ≤ Real.exp K) :
    let δ := ε * Real.exp (-r)
    0 < δ ∧ δ ≤ ε ∧ δ ≤ Real.exp (-r) ∧
      Real.exp r * δ = ε ∧ 1 / δ ≤ Real.exp (K + r) := by
  dsimp only
  have hexp : Real.exp (-r) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr hr)
  refine ⟨mul_pos hε (Real.exp_pos _), ?_, ?_, ?_, ?_⟩
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hε.le
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hε1 (Real.exp_pos _).le
  · calc
      _ = ε * (Real.exp r * Real.exp (-r)) := by ring
      _ = ε := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  · calc
      1 / (ε * Real.exp (-r)) = (1 / ε) * Real.exp r := by
        simp only [one_div, Real.exp_neg, mul_inv_rev, inv_inv]
        exact mul_comm _ _
      _ ≤ Real.exp K * Real.exp r := mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le
      _ = _ := (Real.exp_add K r).symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AnchoredObservationPartition
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_anchored_observation_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {d : ι → ℕ} (E : ∀ i, Bool → RationalFilteredNilmanifold (L i) s (d i))
      (g : ∀ i b, (E i b).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (c : ι → ℤ) (q N : ℕ) [NeZero q] [NeZero N] {p ρ : ℝ},
      1 ≤ s → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i b, (E i b).GeometryComplexityLE p) →
      (q : ℝ) ≤ Real.exp p → 0 < ρ → 1 / ρ ≤ Real.exp ((p + 2) ^ a) →
      ∃ n m : ℕ, 0 < n ∧ 0 < m ∧
        (Fintype.card ((Fin n × ZMod q) × Fin m) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A : ((Fin n × ZMod q) × Fin m) → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} s N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (∀ j x, 0 < A j x → (x.val : ZMod q) = j.1.2) ∧
          (∀ j x y, 0 < A j x → 0 < A j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) ∧
          (∀ h : ZMod N, ((cyclicWrapExceptional h ρ).card : ℝ) / N ≤ 6 * ρ + 3 / N) ∧
          (letI : ∀ i b, MetricSpace (E i b).Space := fun i b => (E i b).metricSpace
           (∀ j x y, 0 < A j x → 0 < A j y → ∀ i,
             dist ((E i false).integerOrbitPoint (g i false) ((x.val : ℤ) + c i))
               ((E i false).integerOrbitPoint (g i false) ((y.val : ℤ) + c i)) ≤ ρ) ∧
           ∀ (h : ZMod N) (b : Fin 2) j k x y,
             x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
             0 < A j x * A k (x + h) → 0 < A j y * A k (y + h) → ∀ i,
               dist ((E i true).integerOrbitPoint (g i true) ((x.val : ℤ) + h.val - (b.val : ℤ) * N))
                 ((E i true).integerOrbitPoint (g i true) ((y.val : ℤ) + h.val - (b.val : ℤ) * N)) ≤ ρ) := by
  obtain ⟨B, _, hpartition⟩ := exists_native_two_site_partition s a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((2 * X + 2 + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro ι _ _ L _ _ _ _ _ _ d E g c q N _ _ p ρ hs hp hι hE hq hρ hρinv
  let D := fun k : ι × Bool => E k.1 k.2
  let G : ∀ k : ι × Bool, (D k).filtration.realification.PolynomialOrbit (fun _ : Unit => 1) :=
    fun | (i, false) => (g i false).translate (fun _ => Nat.zero_lt_one) (fun _ => c i)
        | (i, true) => g i true
  let r := 2 * p + 2
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hr : 0 ≤ r := hp.trans hpr
  have hcard : (Fintype.card (ι × Bool) : ℝ) ≤ r := by
    simp only [Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
    dsimp [r]
    linarith
  have hinv : 1 / ρ ≤ Real.exp ((r + 2) ^ a) :=
    hρinv.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) a))
  obtain ⟨n, m, hn, hm, hcount, A, hA, hsum, hres, hcircle, hexception, hobs, hmove⟩ :=
    hpartition D G q N hs hr hcard (fun k => (hE k.1 k.2).mono (E k.1 k.2) hpr)
      (hq.trans (Real.exp_le_exp.mpr hpr)) hρ hinv
  have hcost : (r + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, r, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨n, m, hn, hm, hcount.trans (Real.exp_le_exp.mpr hcost), A,
    fun j => (hA j).mono le_rfl hcost, hsum, hres, hcircle, hexception, ?_⟩
  let : ∀ i b, MetricSpace (E i b).Space := fun i b => (E i b).metricSpace
  constructor
  · intro j x y hx hy i
    have h := hobs j x y hx hy (i, false) 0 (by norm_num)
    simpa only [D, G, zero_mul, add_zero, integerOrbitPoint_translate] using h
  · intro h b j k x y hx hy hxy hyy i
    exact hmove h b j k x y hx hy hxy hyy (i, true)

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedSquareImagePartition
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_specified_square_recovery (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d dV : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      (V : RationalFilteredNilmanifold D.filtration.squareLieSubalgebra s dV) {p : ℝ},
      2 ≤ p → D.GeometryComplexityLE p → V.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight ((pi (fun _ : Bool => D)).basis.repr
        (D.filtration.squarePairMap (V.basis j)) i) ≤ p) →
      ∃ (Δ : Bool → Subgroup D.filtration.Group) (l : Bool → ℕ)
        (hl : ∀ i, 0 < l i)
        (hlin : ∀ i, scaledIntegerGrid (l i) ⊆ bchSubgroupCoordinates D.basis (Δ i))
        (hlout : ∀ i, bchSubgroupCoordinates D.basis (Δ i) ⊆ denominatorGrid (l i)),
        let E := fun i => D.withLattice (Δ i) (l i) (hl i) (hlin i) (hlout i)
        (∀ i, Δ i ≤ D.lattice ∧ ((Δ i).subgroupOf D.lattice).Characteristic ∧
          ((Δ i).subgroupOf D.lattice).Normal ∧ ((Δ i).subgroupOf D.lattice).FiniteIndex ∧
          ((Δ i).relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        (∀ i, (E i).GeometryComplexityLE ((p + C) ^ C)) ∧
        letI : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
        letI := V.metricSpace
        ∀ ε γ : D.RealGroup, γ ∈ D.realLattice →
          (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 2) ^ k)) →
          ∀ a b c d : D.RealGroup, ∀ u v : D.filtration.squareFiltration.realification.Group,
            D.filtration.realSquareFstHom u = ε⁻¹ * a * γ⁻¹ →
            D.filtration.realSquareSndHom u = b →
            D.filtration.realSquareFstHom v = ε⁻¹ * c * γ⁻¹ →
            D.filtration.realSquareSndHom v = d →
            ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ Real.exp (-((p + C) ^ C)) →
              dist (QuotientGroup.mk a : (E true).Space) (QuotientGroup.mk c) ≤ ρ →
              dist (QuotientGroup.mk b : (E false).Space) (QuotientGroup.mk d) ≤ ρ →
              dist (QuotientGroup.mk u : V.Space) (QuotientGroup.mk v) ≤
                Real.exp ((p + C) ^ C) * ρ := by
  obtain ⟨A, _, hrecovery⟩ := exists_factorwise_subgroup_recovery s k
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + 2) ^ 2 + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro L _ _ d dV _ _ _ _ D _ _ _ _ V p hp hD hV hmatrix
  have hp0 : 0 ≤ p := by linarith
  let D₂ := fun _ : Bool => D
  let : FiniteDimensional ℚ (Bool → L) := (productFinBasis D₂).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (Bool → L))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Bool → L)) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (Bool → L)) := realification_moduleTopology_t2 (productFinBasis D₂)
  let r := p + (p + 2) ^ 2 + 2
  have hpr : p ≤ r := by dsimp [r]; nlinarith [sq_nonneg (p + 2)]
  have hrr : (p + 2) ^ 2 ≤ r := by dsimp [r]; linarith
  have hr : 0 ≤ r := hp0.trans hpr
  have hbool : (Fintype.card Bool : ℝ) ≤ p := by
    simpa only [Fintype.card_bool, Nat.cast_ofNat] using hp
  have hprod := (pi_geometry D₂ hp0 hbool (fun _ => hD)).mono (pi D₂) hrr
  obtain ⟨Δ, l, hl, hlin, hlout, hindex, hE, _, hrecover⟩ :=
    hrecovery D₂ V D.filtration.squarePairMap D.filtration.squarePairMap_injective
      hr (hbool.trans hpr) (fun _ => hD.mono D hpr) hprod (hV.mono V hpr)
      (fun i j => (hmatrix i j).trans hpr)
      1 (by decide) (by simpa only [Nat.cast_one] using Real.one_le_exp hr)
  let E := fun i => D.withLattice (Δ i) (l i) (hl i) (hlin i) (hlout i)
  have hsum : r + (r + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, R, r, Polynomial.eval₂_pow] using hbudget p hp0
  have hAC : (r + A) ^ A ≤ (p + C) ^ C := (le_add_of_nonneg_left hr).trans hsum
  refine ⟨Δ, l, hl, hlin, hlout, ?_, fun i => (hE i).mono (E i) hAC, ?_⟩
  · intro i
    rcases hindex i with ⟨hle, hchar, hnormal, hfinite, hbound⟩
    exact ⟨hle, hchar, hnormal, hfinite, hbound.trans (Real.exp_le_exp.mpr hAC)⟩
  let : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
  let := V.metricSpace
  dsimp only
  intro ε γ hγ hε a b c d u v huf hus hvf hvs ρ hρ hsmall hfirst hsecond
  let e := realBCHPiEquiv (fun _ : Bool => D.filtration)
  let K := e.symm (fun flag => cond flag γ 1)
  let B := e.symm (fun flag => cond flag ε⁻¹ 1)
  let P := e.symm (fun flag => cond flag a b)
  let Q := e.symm (fun flag => cond flag c d)
  have hK : K ∈ (pi D₂).realLattice := by
    apply pi_symm_mem_realLattice D₂
    intro flag
    cases flag
    · exact D.realLattice.one_mem
    · exact hγ
  have hgrid : ((pi D₂).basis.baseChange ℝ).equivFun (1 : (pi D₂).RealGroup).coord ∈
      realDenominatorGrid 1 := by
    refine ⟨fun _ => 0, ?_⟩
    simp only [coord_one, map_zero, Nat.cast_one, one_smul, Int.cast_zero, Pi.zero_def]
  have hB : ∀ i, |((pi D₂).basis.baseChange ℝ).repr B.coord i| ≤ Real.exp ((r + 2) ^ k) := by
    intro i
    exact (D.squareNormalizer_coordinate_bound ε (Real.exp_pos _).le hε i).trans
      (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) k))
  have hu : B * P * (K⁻¹ * 1) = D.filtration.realSquarePairHom u := by
    simpa only [mul_one] using D.filtration.realSquarePairHom_normalization ε γ a b u huf hus
  have hv : B * Q * (K⁻¹ * 1) = D.filtration.realSquarePairHom v := by
    simpa only [mul_one] using D.filtration.realSquarePairHom_normalization ε γ c d v hvf hvs
  have hnear : ρ ≤ Real.exp (-((r + A) ^ A)) :=
    hsmall.trans (Real.exp_le_exp.mpr (neg_le_neg hAC))
  have hP (flag : Bool) : productProjectionHom D₂ flag P = cond flag a b :=
    productProjectionHom_pi_symm D₂ (fun flag => cond flag a b) flag
  have hQ (flag : Bool) : productProjectionHom D₂ flag Q = cond flag c d :=
    productProjectionHom_pi_symm D₂ (fun flag => cond flag c d) flag
  have hinput : ∀ i, dist (QuotientGroup.mk (productProjectionHom D₂ i P) : (E i).Space)
      (QuotientGroup.mk (productProjectionHom D₂ i Q)) ≤ ρ := by
    intro flag
    rw [hP, hQ]
    cases flag
    · exact hsecond
    · exact hfirst
  have hd := hrecover K hK 1 hgrid B B P Q u v hB hu hv ρ hρ hnear hinput
    (fun _ => by simpa only [dist_self] using hρ)
  exact hd.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hAC) hρ)

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_square_image_recovery (s t k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ SquareImageRecoverySpec.{u, v} s t k C := by
  obtain ⟨A, _, hsource⟩ := exists_native_source_cover
  obtain ⟨B, _, hrecovery⟩ := exists_specified_square_recovery s k
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (R + (R + Polynomial.C B) ^ B + (R + 3) ^ 2)
  refine ⟨C, hC, ?_⟩
  dsimp only [SquareImageRecoverySpec]
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d dV dQ D _ _ _ _ V Q φ p hp hD hV hQ hpair hφ
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨Λ, _, _, _, _, _, m, hm, hin, hout, hVc, hmap⟩ := hsource V Q φ hp0 hV hQ hφ
  let V' := V.withLattice Λ m hm hin hout
  let r := p + (p + A) ^ A
  have hpr : p ≤ r := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hr : 0 ≤ r := hp0.trans hpr
  have hAr : (p + A) ^ A ≤ r := le_add_of_nonneg_left hp0
  have hVr : V'.GeometryComplexityLE r := hVc.mono V' hAr
  obtain ⟨Δ, l, hl, hlin, hlout, hindex, hE, hrecover⟩ :=
    hrecovery D V' (hp.trans hpr) (hD.mono D hpr) hVr (fun i j => (hpair i j).trans hpr)
  let E := fun i => D.withLattice (Δ i) (l i) (hl i) (hlin i) (hlout i)
  have htotal : r + (r + B) ^ B + (r + 3) ^ 2 ≤ (p + C) ^ C := by
    simpa [X, R, r, Polynomial.eval₂_pow] using hbudget p hp0
  have hBC : (r + B) ^ B ≤ (p + C) ^ C := by nlinarith [sq_nonneg (r + 3)]
  have hsum : (r + 3) ^ 2 + (r + B) ^ B ≤ (p + C) ^ C := by linarith
  refine ⟨Δ, l, hl, hlin, hlout, ?_, fun i => (hE i).mono (E i) hBC, ?_⟩
  · intro i
    obtain ⟨hle, hchar, hnormal, hfinite, hbound⟩ := hindex i
    exact ⟨hle, hchar, hnormal, hfinite, hbound.trans (Real.exp_le_exp.mpr hBC)⟩
  let : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
  let := Q.metricSpace
  let := V'.metricSpace
  intro ε γ hγ hε a b c d u v huf hus hvf hvs ρ hρ hsmall hfirst hsecond
  have hεr : ∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((r + 2) ^ k) := by
    intro i
    exact (hε i).trans (Real.exp_le_exp.mpr
      (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith : p + 2 ≤ r + 2) k))
  have hsquare := hrecover ε γ hγ hεr a b c d u v huf hus hvf hvs ρ hρ
    (hsmall.trans (Real.exp_le_exp.mpr (neg_le_neg hBC))) hfirst hsecond
  have hprojection := nativeMap_dist_le V' Q φ hmap hr hVr (hQ.mono Q hpr)
    (fun i j => (hφ i j).trans hpr) u v
  apply hprojection.trans
  calc
    _ ≤ Real.exp ((r + 3) ^ 2) * (Real.exp ((r + B) ^ B) * ρ) :=
      mul_le_mul_of_nonneg_left hsquare (Real.exp_pos _).le
    _ = Real.exp ((r + 3) ^ 2 + (r + B) ^ B) * ρ := by rw [← mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hsum) hρ

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_prescribed_square_image_partition (s t k₀ a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ PrescribedSquareImagePartitionSpec s t k₀ a C := by
  obtain ⟨R, _, hrec⟩ := exists_square_image_recovery.{0, 0} s t k₀
  let B : ℕ := Classical.choose (exists_anchored_observation_partition s 1)
  have hpartition := @(Classical.choose_spec (exists_anchored_observation_partition s 1)).2
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C R) ^ R
  let T := X + U + (X + 2) ^ a + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  dsimp only [PrescribedSquareImagePartitionSpec]
  intro L M _ _ _ _ _ _ _ _ _ _ _ _ d dV dQ D _ _ _ _ V Q φ g c q N _ _ p ε
    hs hp hD hV hQ hpair hφ hq hε hε1 hεinv
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨Δ, l, hl, hlin, hlout, _, hE, hrecover⟩ := hrec D V Q φ hp hD hV hQ hpair hφ
  let E := fun i => D.withLattice (Δ i) (l i) (hl i) (hlin i) (hlout i)
  let r := (p + R) ^ R
  let K := (p + 2) ^ a
  let u := p + r + K + 2
  let δ := ε * Real.exp (-r)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpu : p ≤ u := by dsimp [u]; linarith
  have hru : r ≤ u := by dsimp [u]; linarith
  have hku : K + r ≤ u := by dsimp [u]; linarith
  have hu : 0 ≤ u := hp0.trans hpu
  obtain ⟨hδ, hδε, hδsmall, hδerror, hδinv⟩ := recovery_precision_bounds hr hε hε1 hεinv
  have htotal : u + (u + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, U, T, r, K, u, Polynomial.eval₂_pow] using hbudget p hp0
  have hcost : (u + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hu).trans htotal
  have huC : u ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) _)).trans htotal
  have hrC : r ≤ (p + C) ^ C := hru.trans huC
  let E' : Unit → Bool → RationalFilteredNilmanifold L s d := fun _ => E
  let g' : ∀ i b, (E' i b).filtration.realification.PolynomialOrbit (fun _ : Unit => 1) :=
    fun _ _ => g
  have hδinverse : 1 / δ ≤ Real.exp ((u + 2) ^ 1) := by
    apply hδinv.trans (Real.exp_le_exp.mpr _)
    rw [pow_one]
    linarith
  obtain ⟨n, k, hn, hk, hcount, A, hA, hsum, hres, hcircle, hexception, hanchor, hmove⟩ :=
    hpartition E' g' (fun _ => c) q N hs hu
      (by simpa only [Fintype.card_unit, Nat.cast_one] using
        ((by linarith : 1 ≤ p).trans hpu))
      (fun _ b => (hE b).mono (E b) hru)
      (hq.trans (Real.exp_le_exp.mpr hpu)) hδ hδinverse
  refine ⟨δ, hδ, hδε, hδinv.trans (Real.exp_le_exp.mpr (hku.trans huC)),
    n, k, hn, hk, hcount.trans (Real.exp_le_exp.mpr hcost), A,
    fun j => (hA j).mono le_rfl hcost, hsum, hres, hcircle, hexception, ?_⟩
  let : ∀ b, MetricSpace (E b).Space := fun b => (E b).metricSpace
  let := Q.metricSpace
  intro h branch η γ rSq hγ hη hnorm i j x y hx hy hxy hyy
  have hpositive (z : ZMod N) (hz : 0 < A i z * A j (z + h)) : 0 < A i z := by
    rcases mul_pos_iff.mp hz with hz | hz
    · exact hz.1
    · linarith [((hA i).unit_interval z).1]
  have hfirst := hmove h branch i j x y hx hy hxy hyy ()
  change dist ((E true).integerOrbitPoint g ((x.val : ℤ) + h.val - (branch.val : ℤ) * N))
    ((E true).integerOrbitPoint g ((y.val : ℤ) + h.val - (branch.val : ℤ) * N)) ≤ δ at hfirst
  have hsecond := hanchor i x y (hpositive x hxy) (hpositive y hyy) ()
  change dist ((E false).integerOrbitPoint g ((x.val : ℤ) + c))
    ((E false).integerOrbitPoint g ((y.val : ℤ) + c)) ≤ δ at hsecond
  have hbound := hrecover η γ hγ hη
    (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
      ((fun _ => (x.val : ℤ)) + fun _ => (h.val : ℤ) - (branch.val : ℤ) * N) g)
    (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
      ((fun _ => (x.val : ℤ)) + fun _ => c) g)
    (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
      ((fun _ => (y.val : ℤ)) + fun _ => (h.val : ℤ) - (branch.val : ℤ) * N) g)
    (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
      ((fun _ => (y.val : ℤ)) + fun _ => c) g)
    (D.filtration.squareFiltration.realification.polynomialOrbitEval
      (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) rSq)
    (D.filtration.squareFiltration.realification.polynomialOrbitEval
      (fun _ : Unit => 1) (fun _ => (y.val : ℤ)) rSq)
    (hnorm (fun _ => (x.val : ℤ))).1 (hnorm (fun _ => (x.val : ℤ))).2
    (hnorm (fun _ => (y.val : ℤ))).1 (hnorm (fun _ => (y.val : ℤ))).2 δ hδ.le hδsmall
    (by
      change dist ((E true).integerOrbitPoint g ((x.val : ℤ) + ((h.val : ℤ) - (branch.val : ℤ) * N)))
        ((E true).integerOrbitPoint g ((y.val : ℤ) + ((h.val : ℤ) - (branch.val : ℤ) * N))) ≤ δ
      simpa only [add_sub_assoc] using hfirst)
    hsecond
  exact hδerror ▸ hbound

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.RationalFilteredNilmanifold.exists_prescribed_square_image_partition := @OAI.Erdos3.RationalFilteredNilmanifold.exists_prescribed_square_image_partition
