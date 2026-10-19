-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedNarrowTrimmed_recentered_profile_error_law_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:31:46.211188+00:00
-- url     : https://prove2.me/submissions/c5bb8b4f-d2bd-4e2a-b911-a47c5102a200

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B194
import Definitions.Def_OAIE3v2B195
import Definitions.Def_OAIE3v2B196
import Theorems.Thm_OAI_Erdos3_BooleanCubeKernel_physicalSelectedResidue_width_recenter_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedNarrowTrimmed_shifted_vector_site_error_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem integerResidueMatrix_eq_iff_dvd_sub {I J : Type*}
    (C D : Matrix I J ℤ) (m : ℕ) :
    integerResidueMatrix C m = integerResidueMatrix D m ↔
      ∀ i j, (m : ℤ) ∣ C i j - D i j := by
  constructor
  · intro h i j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (C i j - D i j) m).mp
    rw [Int.cast_sub]
    exact sub_eq_zero.mpr (congrFun (congrFun h i) j)
  · intro h
    ext i j
    change (C i j : ZMod m) = (D i j : ZMod m)
    apply sub_eq_zero.mp
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (C i j - D i j) m).mpr (h i j)
    simpa only [Int.cast_sub] using hz

theorem integerResidueMatrix_reduce {I J : Type*} (C D : Matrix I J ℤ)
    {m n : ℕ} (hmn : m ∣ n) (h : integerResidueMatrix C n = integerResidueMatrix D n) :
    integerResidueMatrix C m = integerResidueMatrix D m := by
  apply (integerResidueMatrix_eq_iff_dvd_sub C D m).mpr
  have hd : (m : ℤ) ∣ (n : ℤ) := by exact_mod_cast hmn
  exact fun i j => hd.trans ((integerResidueMatrix_eq_iff_dvd_sub C D n).mp h i j)

theorem residueMatrixShift_spec {I J : Type*} [Fintype I] [Fintype J]
    (C D : Matrix I J ℤ) (q m : ℕ) (hq : 0 < q)
    (h : integerResidueMatrix C (q * m) = integerResidueMatrix D (q * m)) (r : J → ℤ) :
    (∀ i, (q : ℤ) * residueMatrixShift C D q r i = ((C - D) *ᵥ r) i) ∧
      residueMatrixShift C D q r ∈ integerScalarLattice I (m : ℤ) := by
  classical
  have hd (i) (j) : (q : ℤ) * (m : ℤ) ∣ C i j - D i j := by
    simpa only [Nat.cast_mul] using (integerResidueMatrix_eq_iff_dvd_sub C D (q * m)).mp h i j
  choose Z hZ using hd
  let t : I → ℤ := fun i => ∑ j, Z i j * r j
  have he (i) : ((C - D) *ᵥ r) i = (q : ℤ) * ((m : ℤ) * t i) := by
    change (∑ j, (C i j - D i j) * r j) = _
    simp_rw [hZ]
    dsimp only [t]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hs (i) : residueMatrixShift C D q r i = (m : ℤ) * t i := by
    unfold residueMatrixShift
    rw [he, Int.mul_ediv_cancel_left _ hq0]
  refine ⟨fun i => by rw [hs, he], ?_⟩
  refine ⟨t, ?_⟩
  funext i
  exact (hs i).symm

theorem residueMatrixShift_bound {I J : Type*} [Fintype I] [Fintype J]
    (C D : Matrix I J ℤ) (q m : ℕ) (hq : 0 < q)
    (h : integerResidueMatrix C (q * m) = integerResidueMatrix D (q * m))
    (r : J → ℤ) (hr : ∀ j, |(r j : ℝ)| ≤ q) (i : I) :
    |(residueMatrixShift C D q r i : ℝ)| ≤ ∑ j, |((C i j - D i j : ℤ) : ℝ)| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have he := (residueMatrixShift_spec C D q m hq h r).1 i
  have heR : (q : ℝ) * (residueMatrixShift C D q r i : ℝ) = (((C - D) *ᵥ r) i : ℝ) := by
    exact_mod_cast he
  have hm : (q : ℝ) * |(residueMatrixShift C D q r i : ℝ)| =
      |∑ j, ((C i j - D i j : ℤ) : ℝ) * (r j : ℝ)| := by
    rw [← abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q), ← abs_mul, heR]
    simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Int.cast_sum, Int.cast_mul]
  apply (mul_le_mul_iff_right₀ hqR).mp
  rw [hm]
  calc
    _ ≤ ∑ j, |((C i j - D i j : ℤ) : ℝ) * (r j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |((C i j - D i j : ℤ) : ℝ)| * (q : ℝ) :=
      Finset.sum_le_sum (fun j _ => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hr j) (abs_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm.trans (mul_comm _ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedSmoothSelectedMarginal
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pmf_map_finite_sum {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (y : Y) :
    (p.map F y).toReal = ∑ x ∈ S, (p x).toReal * (if F x = y then 1 else 0) := by
  rw [pmf_map_toReal_indicator]
  exact (hasSum_sum_of_ne_finset_zero (fun x hx => by rw [hp x hx, zero_mul])).tsum_eq

theorem pmf_image_finite_expectation {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (T : Finset Y) (hT : ∀ x ∈ S, F x ∈ T) (φ : Y → ℂ) :
    (∑' x, ((p x).toReal : ℂ) * φ (F x)) =
      ∑ y ∈ T, ((p.map F y).toReal : ℂ) * φ y := by
  have hs : (∑' x, ((p x).toReal : ℂ) * φ (F x)) =
      ∑ x ∈ S, ((p x).toReal : ℂ) * φ (F x) :=
    (hasSum_sum_of_ne_finset_zero (fun x hx => by
      rw [hp x hx, Complex.ofReal_zero, zero_mul])).tsum_eq
  rw [hs]
  simp_rw [pmf_map_finite_sum p S hp F, Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_eq_single (F x)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · intro hn
    exact (hn (hT x hx)).elim

theorem pmf_image_finite_test_error {X Y : Type*} [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (T : Finset Y) (hT : ∀ x ∈ S, F x ∈ T)
    (ψ φ : Y → ℂ) {A E : ℝ} (hA : 0 < A)
    (he : ∀ y ∈ T, ‖((A * (p.map F y).toReal : ℝ) : ℂ) - ψ y‖ ≤ E) :
    ‖(∑' x, ((p x).toReal : ℂ) * φ (F x)) -
      ∑ y ∈ T, (ψ y / (A : ℂ)) * φ y‖ ≤
        (E / A) * ∑ y ∈ T, ‖φ y‖ := by
  rw [pmf_image_finite_expectation p S hp F T hT φ, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ y ∈ T, (E / A) * ‖φ y‖ := by
      apply Finset.sum_le_sum
      intro y hy
      have hid : ((p.map F y).toReal : ℂ) - ψ y / (A : ℂ) =
          (((A * (p.map F y).toReal : ℝ) : ℂ) - ψ y) / (A : ℂ) := by
        rw [Complex.ofReal_mul, sub_div, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hA.ne')]
      rw [← sub_mul, norm_mul, hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (he y hy) hA.le) (norm_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem pmf_map_add_right {Y : Type*} [AddGroup Y] (p : PMF Y) (s y : Y) :
    p.map (fun v => v + s) y = p (y - s) := by
  have h := pmf_map_injective_at p (fun v => v + s) (fun _ _ h => add_right_cancel h) (y-s)
  simpa only [sub_add_cancel] using h

theorem pmf_map_image_add_right {X Y : Type*} [AddGroup Y]
    (p : PMF X) (F : X → Y) (s y : Y) :
    p.map (fun x => F x + s) y = p.map F (y-s) := by
  rw [show (fun x => F x + s) = (fun v => v+s) ∘ F from rfl, ← PMF.map_comp]
  exact pmf_map_add_right (p.map F) s y

theorem pmf_image_shifted_finite_test_error {X Y : Type*} [AddGroup Y] [DecidableEq Y]
    (p : PMF X) (S : Finset X) (hp : ∀ x ∉ S, (p x).toReal = 0)
    (F : X → Y) (s : Y) (T : Finset Y) (hT : ∀ x ∈ S, F x + s ∈ T)
    (ψ φ : Y → ℂ) {A E : ℝ} (hA : 0 < A)
    (he : ∀ y ∈ T, ‖((A * (p.map F (y-s)).toReal : ℝ) : ℂ) - ψ y‖ ≤ E) :
    ‖(∑' x, ((p x).toReal : ℂ) * φ (F x+s)) -
      ∑ y ∈ T, (ψ y / (A : ℂ)) * φ y‖ ≤ (E/A) * ∑ y ∈ T, ‖φ y‖ := by
  apply pmf_image_finite_test_error p S hp (fun x => F x+s) T hT ψ φ hA
  simpa only [pmf_map_image_add_right] using he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialStarCoordinates
namespace OAI

section

namespace Erdos3

theorem spatialStar_vertex {I R : Type*} [AddCommMonoid R] (v : (Unit ⊕ I) → R) (i : Unit ⊕ I) :
    spatialStar v i = v (.inl ()) + ∑ j ∈ spatialStarVertex i, v (.inr j) := by
  cases i with
  | inl i => cases i; simp [spatialStar, spatialStarVertex]
  | inr i => simp [spatialStar, spatialStarVertex]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SubspaceLayeredModeSmoothRemoval
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem smoothProductPMF_toReal_zero_off {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) (x : I → ℤ)
    (hx : x ∉ rectangularWeightIndices 0 S 1) : (smoothProductPMF S hS x).toReal = 0 := by
  have hz := rectangularWeight_zero_off_indices (smoothProductProfile I) 0 S hS
    (smoothProductProfile_zero_outside I) x hx
  simp only [rectangularWeight, rectangularLatticePoint_zero_origin] at hz
  simp only [smoothProductPMF, realWeightPMF_apply, hz, zero_div]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget
namespace OAI

section

namespace Erdos3

theorem rectangularWeightIndices_zero_mono {I : Type*} [Fintype I]
    {V W : I → ℝ} (hVW : ∀ i, V i ≤ W i) :
    rectangularWeightIndices 0 V 1 ⊆ rectangularWeightIndices 0 W 1 := by
  intro z hz
  apply (mem_rectangularWeightIndices_zero_iff W z).mpr
  exact fun i => (rectangularWeightIndices_zero_bound V hz i).trans (hVW i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PrincipalSpatialSiteComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem principalSpatialColumns_residue {D α N : Type*} {B : D → Type*} {h : D → ℕ}
    {L : PrincipalTupleIndex B h → ℕ} (m : ℕ) (c : N → ℤ) (index : N → PrincipalTupleIndex B h)
    (y : PrincipalIntegerTuples B h α L) :
    integerResidueMatrix (principalSpatialColumns c index y) m =
      principalSpatialResidueColumns m c index (principalResidueLabel m y) := by
  ext i n
  cases i <;> simp [integerResidueMatrix, principalSpatialColumns, scalarTupleSpatialColumns,
    tupleColumnMatrix, scalarTupleColumn, principalSpatialResidueColumns, principalResidueLabel]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PhysicalCubeMatrix
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Matrix

theorem physicalCubeRootDifferences_star {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (z : Option K × X → ℤ) (x : X) (i : Unit ⊕ α) :
    spatialStar (physicalCubeRootDifferences root D base z x) i =
      jointIntegerPhysicalSite (integerAffineCube root D (spatialStarVertex i)) (base, z) x := by
  rw [spatialStar_vertex, physicalCubeRootDifferences_vertex]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalSpatialScales
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem trimmedSpatial_residue_scale {K X : Type*} (B τ : ℝ) (N modulus : X → ℕ) (x : X) :
    (fun k => residueProfileWidth modulus (trimmedSpatialWidths (K := K) B τ N) (k, x)) =
      physicalSpatialInputScale K (trimmedSpatialRootScale τ N modulus x)
        (trimmedSpatialSlopeScale B τ N modulus x) := by
  funext k
  cases k <;> simp only [residueProfileWidth, trimmedSpatialWidths, centeredSpatialWidths,
    physicalSpatialInputScale, Option.elim', trimmedSpatialRootScale, trimmedSpatialSlopeScale, one_mul] <;> ring

theorem trimmedSpatial_scale_ratio {X : Type*} {B τ : ℝ} (hB : 0 ≤ B)
    (N modulus : X → ℕ) (x : X) :
    trimmedSpatialRootScale τ N modulus x =
      (1 + B) * trimmedSpatialSlopeScale B τ N modulus x := by
  have hb : 1 + B ≠ 0 := ne_of_gt (by linarith)
  unfold trimmedSpatialRootScale trimmedSpatialSlopeScale
  field_simp

theorem trimmedSpatial_scale_lower {X : Type*} {B τ ρ : ℝ}
    (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (N modulus : X → ℕ) (x : X) (hq : 0 < modulus x)
    (hlarge : 8 * (1 + B) * (modulus x : ℝ) * ρ ≤ τ * (N x : ℝ)) :
    ρ ≤ trimmedSpatialRootScale τ N modulus x ∧ ρ ≤ trimmedSpatialSlopeScale B τ N modulus x := by
  have hq' : (0 : ℝ) < modulus x := by exact_mod_cast hq
  have hb : (0 : ℝ) < 8 * (1 + B) := by positivity
  have hs : ρ ≤ trimmedSpatialSlopeScale B τ N modulus x := by
    unfold trimmedSpatialSlopeScale
    apply (le_div_iff₀ hq').mpr
    apply (le_div_iff₀ hb).mpr
    nlinarith [hlarge]
  refine ⟨?_, hs⟩
  unfold trimmedSpatialRootScale
  apply (le_div_iff₀ hq').mpr
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
  nlinarith [mul_nonneg hB (mul_nonneg hq'.le hρ)]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalAmbientVolumeRatio
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Matrix

theorem centeredPhysicalCubeMap_eq {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) :
    centeredPhysicalCubeMap (X := X) root D = physicalCubeRootDifferences root D 0 := by
  funext z d i
  cases i <;> simp only [centeredPhysicalCubeMap, physicalCubeRootDifferences,
    physicalCubeOffset, Pi.zero_apply, zero_add, Matrix.mulVec, dotProduct]

theorem centeredPhysicalCubeMap_mem_window {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (Q : Option K × X → ℝ)
    (z : Option K × X → ℤ) (hz : z ∈ rectangularWeightIndices 0 Q 1) :
    centeredPhysicalCubeMap root D z ∈ centeredPhysicalCubeWindow root D Q := by
  classical
  exact Finset.mem_image.mpr ⟨z, hz, rfl⟩

theorem spatialStarVertex_root_sum {K α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) {W : ℝ} (hW : 0 ≤ W)
    (hroot : (∑ k, |(root k : ℝ)|) ≤ W)
    (hD : ∀ i, (∑ k, |(D i k : ℝ)|) ≤ W) (i : Unit ⊕ α) :
    (∑ k, |(integerAffineCube root D (spatialStarVertex i) k : ℝ)|) ≤ 2 * W := by
  cases i with
  | inl i =>
    simpa only [spatialStarVertex, Sum.elim_inl, integerAffineCube, Finset.sum_empty,
      add_zero] using hroot.trans (by linarith : W ≤ 2 * W)
  | inr i =>
    simp only [spatialStarVertex, Sum.elim_inr, integerAffineCube, Finset.sum_singleton, Int.cast_add]
    calc
      _ ≤ ∑ k, (|(root k : ℝ)| + |(D i k : ℝ)|) :=
        Finset.sum_le_sum (fun _ _ => abs_add_le _ _)
      _ = (∑ k, |(root k : ℝ)|) + ∑ k, |(D i k : ℝ)| := Finset.sum_add_distrib
      _ ≤ 2 * W := by linarith [hD i]

theorem centeredPhysicalCubeWindow_star_bound {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (Q : Option K × X → ℝ) (H T : X → ℝ)
    {W : ℝ} (hW : 0 ≤ W) (hH : ∀ d, 0 < H d) (hT : ∀ d, 0 ≤ T d)
    (hscale : ∀ d, H d = (1 + W) * T d)
    (hQ : ∀ d, (fun k => Q (k, d)) = physicalSpatialInputScale K (H d) (T d))
    (hroot : (∑ k, |(root k : ℝ)|) ≤ W)
    (hD : ∀ i, (∑ k, |(D i k : ℝ)|) ≤ W)
    (v : X → (Unit ⊕ α) → ℤ) (hv : v ∈ centeredPhysicalCubeWindow root D Q) :
    ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / H d| ≤ 3 := by
  classical
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
  intro d i
  have hb := integerPhysicalSite_abs_bound (integerAffineCube root D (spatialStarVertex i)) Q z
    (rectangularWeightIndices_zero_bound Q hz) d
  have hq0 : Q (none, d) = H d := congrFun (hQ d) none
  have hqs (k : K) : Q (some k, d) = T d := congrFun (hQ d) (some k)
  simp only [physicalSiteWidth, hq0, hqs, ← Finset.sum_mul] at hb
  have hs := mul_le_mul_of_nonneg_right (spatialStarVertex_root_sum root D hW hroot hD i) (hT d)
  have hbound : |(integerPhysicalSite (integerAffineCube root D (spatialStarVertex i)) z d : ℝ)| ≤
      3 * H d := by nlinarith [hscale d, hT d]
  rw [centeredPhysicalCubeMap_eq, physicalCubeRootDifferences_star]
  simpa only [jointIntegerPhysicalSite, zero_add, abs_div, abs_of_pos (hH d)] using
    (div_le_iff₀ (hH d)).mpr hbound

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialShiftedWindowError
namespace OAI

section

namespace Erdos3

theorem spatialStar_add {I R : Type*} [AddCommMonoid R]
    (v w : (Unit ⊕ I) → R) : spatialStar (v + w) = spatialStar v + spatialStar w := by
  funext i
  cases i with
  | inl i => rfl
  | inr i => simp only [spatialStar, Sum.elim_inr, Pi.add_apply]; abel

namespace BooleanCubeKernel

open scoped BigOperators

theorem mem_spatialWindow_scaled_iff {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) (hH : ∀ d, 0 < H d) (b : ℝ) (v : X → (Unit ⊕ α) → ℤ) :
    v ∈ spatialWindow H b ↔ ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / H d| ≤ b := by
  rw [mem_spatialWindow_iff]
  simp only [abs_div, abs_of_pos (hH _), div_le_iff₀ (hH _), mul_comm]

theorem spatialWindow_add {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) {a b : ℝ} {v s : X → (Unit ⊕ α) → ℤ}
    (hv : v ∈ spatialWindow H a) (hs : s ∈ spatialWindow H b) :
    v + s ∈ spatialWindow H (a + b) := by
  apply (mem_spatialWindow_iff H (a+b) _).mpr
  intro d i
  change |((spatialStar (v d + s d) i : ℤ) : ℝ)| ≤ _
  rw [spatialStar_add, Pi.add_apply, Int.cast_add]
  calc
    _ ≤ |((spatialStar (v d) i : ℤ) : ℝ)| + |((spatialStar (s d) i : ℤ) : ℝ)| := abs_add_le _ _
    _ ≤ H d * a + H d * b := add_le_add
      ((mem_spatialWindow_iff H a v).mp hv d i) ((mem_spatialWindow_iff H b s).mp hs d i)
    _ = _ := (mul_add _ _ _).symm

theorem spatialWindow_of_coordinate_bound {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) (hH : ∀ d, 0 ≤ H d) {t : ℝ} (ht : 0 ≤ t)
    (s : X → (Unit ⊕ α) → ℤ) (hs : ∀ d i, |(s d i : ℝ)| ≤ H d * t) :
    s ∈ spatialWindow H (2*t) := by
  apply (mem_spatialWindow_iff H (2*t) s).mpr
  intro d i
  cases i with
  | inl i =>
    change |(s d (.inl ()) : ℝ)| ≤ _
    nlinarith [hs d (.inl ()), mul_nonneg (hH d) ht]
  | inr i =>
    change |((s d (.inl ()) + s d (.inr i) : ℤ) : ℝ)| ≤ _
    rw [Int.cast_add]
    exact (abs_add_le _ _).trans (by nlinarith [hs d (.inl ()), hs d (.inr i)])

end BooleanCubeKernel
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalResidueOffsetShift
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem trimmedSpatial_residue_width_lower {K X : Type*} {W τ ρ : ℝ}
    (hW : 0 ≤ W) (hρ : 0 ≤ ρ) (N q : X → ℕ) (hq : ∀ x, 0 < q x)
    (hsize : ∀ x, 8 * (1 + W) * (q x : ℝ) * ρ ≤ τ * (N x : ℝ))
    (z : Option K × X) :
    ρ ≤ residueProfileWidth q (trimmedSpatialWidths W τ N) z := by
  have h := trimmedSpatial_scale_lower hW hρ N q z.2 (hq z.2) (hsize z.2)
  have he := congrFun (trimmedSpatial_residue_scale (K := K) W τ N q z.2) z.1
  rw [he]
  cases z.1
  · exact h.1
  · exact h.2

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalResidueReconstruction_centered {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (z : Option K × X → ℤ) :
    physicalResidueReconstruction root D base residue q (centeredPhysicalCubeMap root D z) =
      physicalCubeResidueCoordinates root D base residue q z := by
  rw [centeredPhysicalCubeMap_eq]
  rfl

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Matrix

theorem physicalResidueOffsetShift_mem {K X α : Type*} [Fintype K] [Fintype α]
    (root root₀ : K → ℤ) (D D₀ : Matrix α K ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ d, 0 < q d) (m : ℕ)
    (hres : ∀ d, integerResidueMatrix (physicalCubeCoefficient root D) (q d * m) =
      integerResidueMatrix (physicalCubeCoefficient root₀ D₀) (q d * m)) (d : X) :
    physicalResidueOffsetShift root root₀ D D₀ r q d ∈ integerScalarLattice (Unit ⊕ α) (m : ℤ) :=
  (residueMatrixShift_spec _ _ (q d) m (hq d) (hres d) (fun k => r (k, d))).2

theorem physicalResidueReconstruction_offset_shift {K X α : Type*} [Fintype K] [Fintype α]
    (root root₀ : K → ℤ) (D D₀ : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ d, 0 < q d) (m : ℕ)
    (hres : ∀ d, integerResidueMatrix (physicalCubeCoefficient root D) (q d * m) =
      integerResidueMatrix (physicalCubeCoefficient root₀ D₀) (q d * m))
    (v : X → (Unit ⊕ α) → ℤ) :
    physicalResidueReconstruction root D base r q v =
      physicalResidueReconstruction root₀ D₀ base r q
        (v + physicalResidueOffsetShift root root₀ D D₀ r q) := by
  funext d i
  have hs := (residueMatrixShift_spec _ _ (q d) m (hq d) (hres d) (fun k => r (k, d))).1 i
  change (q d : ℤ) * physicalResidueOffsetShift root root₀ D D₀ r q d i = _ at hs
  change physicalCubeOffset base d i +
      (physicalCubeCoefficient root D *ᵥ (fun k => r (k, d))) i + (q d : ℤ) * v d i =
    physicalCubeOffset base d i +
      (physicalCubeCoefficient root₀ D₀ *ᵥ (fun k => r (k, d))) i +
        (q d : ℤ) * (v d i + physicalResidueOffsetShift root root₀ D D₀ r q d i)
  rw [mul_add, hs, Matrix.sub_mulVec, Pi.sub_apply]
  ring

theorem physicalResidueOffsetShift_bound {K X α : Type*} [Fintype K] [Fintype α]
    (root root₀ : K → ℤ) (D D₀ : Matrix α K ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ d, 0 < q d) (m : ℕ)
    (hres : ∀ d, integerResidueMatrix (physicalCubeCoefficient root D) (q d * m) =
      integerResidueMatrix (physicalCubeCoefficient root₀ D₀) (q d * m))
    (hr : ∀ k d, |(r (k, d) : ℝ)| ≤ q d) (d : X) (i : Unit ⊕ α) :
    |(physicalResidueOffsetShift root root₀ D D₀ r q d i : ℝ)| ≤
      ∑ k, |((physicalCubeCoefficient root D i k - physicalCubeCoefficient root₀ D₀ i k : ℤ) : ℝ)| :=
  residueMatrixShift_bound _ _ (q d) m (hq d) (hres d) (fun k => r (k, d)) (fun k => hr k d) i

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedKernelCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

omit [Fintype α] in
theorem allocatedPhysicalCube_principal_columns (i : Unit ⊕ α)
    (j : PrincipalTupleIndex B (layerSamplerDegree I n)) :
    physicalCubeCoefficient (allocatedPhysicalCubeRoot B U basis S c x y)
        (allocatedPhysicalCubeDirections B U basis S x y) i (some (.inr j)) =
      principalSpatialColumns (fun j => c (.inr j)) id y i j := by
  cases i <;> rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedTrimmedVectorSite
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

theorem allocatedPhysicalEntryBudget_one_le : 1 ≤ allocatedPhysicalEntryBudget B U basis S c := by
  have h := allocatedPhysicalRootBudget_nonneg B U basis S c
  unfold allocatedPhysicalEntryBudget
  linarith [Nat.cast_nonneg (α := ℝ) S.value]

omit [Fintype α] in
theorem allocatedPhysicalCube_root_entry_bound (k : LayerSamplerVariables G I n B) :
    |(allocatedPhysicalCubeRoot B U basis S c x y k : ℝ)| ≤ allocatedPhysicalEntryBudget B U basis S c := by
  apply (allocatedPhysicalCube_root_budget B U basis S c x y k).trans
  unfold allocatedPhysicalEntryBudget
  linarith [Nat.cast_nonneg (α := ℝ) S.value]

omit [Fintype α] in
theorem allocatedPhysicalCube_direction_entry_bound (i : α) (k : LayerSamplerVariables G I n B) :
    |(allocatedPhysicalCubeDirections B U basis S x y i k : ℝ)| ≤ allocatedPhysicalEntryBudget B U basis S c := by
  apply (allocatedPhysicalCube_directions_bound B U basis S x y i k).trans
  have h := allocatedPhysicalRootBudget_nonneg B U basis S c
  unfold allocatedPhysicalEntryBudget
  linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators NNReal

theorem anisotropicSpatialError_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (N : Type*) [Fintype N] (B : ℕ) {κ C ρ ξ : ℝ}
    (hκ : 0 ≤ κ) (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hξ : 0 ≤ ξ) :
    0 ≤ anisotropicSpatialError s N B κ C ρ ξ := by
  unfold anisotropicSpatialError normalizedFiberErrorConstant integerFiberErrorConstant
    anisotropicSpatialDetAllowance physicalSpatialInverseBound spatialKernelErrorConstant
  positivity

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

omit [Fintype α] in
theorem allocatedPhysicalCube_direction_sum (i : α) :
    (∑ k, |(allocatedPhysicalCubeDirections B U basis S x y i k : ℝ)|) ≤
      allocatedPhysicalRootBudget B U basis S c := by
  calc
    _ ≤ ∑ _k : LayerSamplerVariables G I n B, (S.value : ℝ) :=
      Finset.sum_le_sum (fun k _ => allocatedPhysicalCube_directions_bound B U basis S x y i k)
    _ = Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ) := by simp
    _ ≤ _ := le_add_of_nonneg_left (Finset.sum_nonneg (fun k _ => abs_nonneg (c k : ℝ)))

theorem allocatedTrimmedSpatial_window_bound {X : Type*} [Fintype X]
    (N q : X → ℕ) (hN : ∀ d, 0 < N d) (hq : ∀ d, 0 < q d)
    {W τ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (v : X → (Unit ⊕ α) → ℤ)
    (hv : v ∈ centeredPhysicalCubeWindow (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y)
      (residueProfileWidth q (trimmedSpatialWidths (K := LayerSamplerVariables G I n B) W τ N))) :
    ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / trimmedSpatialRootScale τ N q d| ≤ 3 := by
  apply centeredPhysicalCubeWindow_star_bound _ _ _ _ (fun d => trimmedSpatialSlopeScale W τ N q d)
    hW (fun d => (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).1)
    (fun d => (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).2.le)
    (fun d => trimmedSpatial_scale_ratio hW N q d)
    (fun d => trimmedSpatial_residue_scale W τ N q d)
    ((allocatedPhysicalCube_root_sum B U basis S c x y).trans hbudget)
    (fun i => (allocatedPhysicalCube_direction_sum B U basis S c x y i).trans hbudget) v hv

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedWholeResidueShift
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)

local notation "vars" => LayerSamplerVariables G I n B
local notation "sides" => allocatedPrincipalSides B U basis S

omit [Fintype α] [DecidableEq α] in
theorem allocatedPhysicalCube_coefficient_entry_bound
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides)
    (i : Unit ⊕ α) (k : Option vars) :
    |(physicalCubeCoefficient (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y) i k : ℝ)| ≤
        allocatedPhysicalEntryBudget B U basis S c := by
  cases k with
  | none =>
    cases i with
    | inl i =>
      simpa only [physicalCubeCoefficient, Int.cast_one, abs_one] using
        allocatedPhysicalEntryBudget_one_le B U basis S c
    | inr i =>
      simpa only [physicalCubeCoefficient, Int.cast_zero, abs_zero] using
        zero_le_one.trans (allocatedPhysicalEntryBudget_one_le B U basis S c)
  | some k =>
    cases i with
    | inl i => exact allocatedPhysicalCube_root_entry_bound B U basis S c x y k
    | inr i => exact allocatedPhysicalCube_direction_entry_bound B U basis S c x y i k

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)

local notation "vars" => LayerSamplerVariables G I n B
local notation "sides" => allocatedPrincipalSides B U basis S

omit [Fintype α] [DecidableEq α] in
theorem allocatedPhysicalCube_residue_of_whole_label
    (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides)
    (modulus : ℕ) (hlabel : principalResidueLabel modulus y = principalResidueLabel modulus y₀) :
    integerResidueMatrix (physicalCubeCoefficient
      (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y)) modulus =
    integerResidueMatrix (physicalCubeCoefficient
      (allocatedPhysicalCubeRoot B U basis S c x y₀)
      (allocatedPhysicalCubeDirections B U basis S x y₀)) modulus := by
  have hc : integerResidueMatrix (principalSpatialColumns (fun j => c (Sum.inr j)) id
      y) modulus =
    integerResidueMatrix (principalSpatialColumns (fun j => c (Sum.inr j)) id
      y₀) modulus := by
    rw [principalSpatialColumns_residue, principalSpatialColumns_residue, hlabel]
  ext i k
  cases k with
  | none => cases i <;> rfl
  | some k =>
    cases k with
    | inl g => cases i <;> rfl
    | inr j =>
      cases i with
      | inl i => exact congrFun (congrFun hc (.inl i)) j
      | inr i => exact congrFun (congrFun hc (.inr i)) j

omit [DecidableEq α] in
theorem allocatedPhysicalResidue_whole_offset_shift
    (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides)
    {X : Type*} (base : X → ℤ) (r : Option vars × X → ℤ)
    (q : X → ℕ) (hq : ∀ d, 0 < q d) (period modulus : ℕ)
    (hdiv : ∀ d, q d * period ∣ modulus)
    (hlabel : principalResidueLabel modulus y = principalResidueLabel modulus y₀)
    (hr : ∀ k d, |(r (k, d) : ℝ)| ≤ q d) :
    let root := allocatedPhysicalCubeRoot B U basis S c x y
    let root₀ := allocatedPhysicalCubeRoot B U basis S c x y₀
    let dirs := allocatedPhysicalCubeDirections B U basis S x y
    let dirs₀ := allocatedPhysicalCubeDirections B U basis S x y₀
    let shift := physicalResidueOffsetShift root root₀ dirs dirs₀ r q
    (∀ d, shift d ∈ integerScalarLattice (Unit ⊕ α) (period : ℤ)) ∧
    (∀ v, physicalResidueReconstruction root dirs base r q v =
      physicalResidueReconstruction root₀ dirs₀ base r q (v + shift)) ∧
    (∀ d i, |(shift d i : ℝ)| ≤
      Fintype.card (Option vars) * (2 * allocatedPhysicalEntryBudget B U basis S c)) := by
  intro root root₀ dirs dirs₀ shift
  have hres (d) : integerResidueMatrix (physicalCubeCoefficient root dirs) (q d * period) =
      integerResidueMatrix (physicalCubeCoefficient root₀ dirs₀) (q d * period) :=
    integerResidueMatrix_reduce _ _ (hdiv d)
      (allocatedPhysicalCube_residue_of_whole_label B U basis S c x y y₀ modulus hlabel)
  refine ⟨fun d => physicalResidueOffsetShift_mem root root₀ dirs dirs₀ r q hq period hres d,
    fun v => physicalResidueReconstruction_offset_shift root root₀ dirs dirs₀ base r q hq period hres v, ?_⟩
  intro d i
  apply (physicalResidueOffsetShift_bound root root₀ dirs dirs₀ r q hq period hres hr d i).trans
  calc
    _ ≤ ∑ _k : Option vars, 2 * allocatedPhysicalEntryBudget B U basis S c := by
      apply Finset.sum_le_sum
      intro k _
      rw [Int.cast_sub]
      apply (abs_sub _ _).trans
      have h₁ := allocatedPhysicalCube_coefficient_entry_bound B U basis S c x y i k
      have h₂ := allocatedPhysicalCube_coefficient_entry_bound B U basis S c x y₀ i k
      linarith
    _ = _ := by simp

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedReferenceWindowTest
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem smoothPhysicalResidue_reference_window_error {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root root₀ : K → ℤ) (D D₀ : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ d, 0 < q d) (modulus : ℕ)
    (hres : ∀ d, integerResidueMatrix (physicalCubeCoefficient root D) (q d * modulus) =
      integerResidueMatrix (physicalCubeCoefficient root₀ D₀) (q d * modulus))
    (Q : Option K × X → ℝ) (hQ : ∀ z, 0 < Q z)
    (window : Finset (X → (Unit ⊕ α) → ℤ))
    (hwindow : ∀ v ∈ centeredPhysicalCubeWindow root D Q,
      v + physicalResidueOffsetShift root root₀ D D₀ r q ∈ window)
    (ψ φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {A E : ℝ} (hA : 0 < A)
    (he : ∀ v ∈ window,
      ‖((A * (((smoothProductPMF Q hQ).map (centeredPhysicalCubeMap root D))
        (v - physicalResidueOffsetShift root root₀ D D₀ r q)).toReal : ℝ) : ℂ) - ψ v‖ ≤ E) :
    ‖(∑' z, ((smoothProductPMF Q hQ z).toReal : ℂ) *
        φ (physicalCubeResidueCoordinates root D base r q z)) -
      ∑ v ∈ window, (ψ v / (A : ℂ)) *
        φ (physicalResidueReconstruction root₀ D₀ base r q v)‖ ≤
      (E/A) * ∑ v ∈ window, ‖φ (physicalResidueReconstruction root₀ D₀ base r q v)‖ := by
  classical
  have h := pmf_image_shifted_finite_test_error (smoothProductPMF Q hQ)
    (rectangularWeightIndices 0 Q 1) (smoothProductPMF_toReal_zero_off Q hQ)
    (centeredPhysicalCubeMap root D) (physicalResidueOffsetShift root root₀ D D₀ r q)
    window (fun z hz => hwindow _ (centeredPhysicalCubeMap_mem_window root D Q z hz)) ψ
    (fun v => φ (physicalResidueReconstruction root₀ D₀ base r q v)) hA he
  simpa only [← physicalResidueReconstruction_offset_shift root root₀ D D₀ base r q hq modulus hres,
    physicalResidueReconstruction_centered] using h

theorem physicalCenteredResidueMixture_reference_error {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root root₀ : K → ℤ) (D D₀ : Matrix α K ℤ) (base : X → ℤ)
    (q : X → ℕ) (hq : ∀ d, 0 < q d) (modulus : ℕ)
    (hres : ∀ d, integerResidueMatrix (physicalCubeCoefficient root D) (q d * modulus) =
      integerResidueMatrix (physicalCubeCoefficient root₀ D₀) (q d * modulus))
    (cells : Finset (ColumnResiduePattern (Option K) X q))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (window : Finset (X → (Unit ⊕ α) → ℤ))
    (hwindow : ∀ a : cells, ∀ v ∈ centeredPhysicalCubeWindow root D (residueProfileWidth q V),
      v + physicalResidueOffsetShift root root₀ D D₀ (boundedColumnResidueRepresentative q a.val) q ∈ window)
    (ψ φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {A E Z : ℝ} (hA : 0 < A) (hZ : 0 < Z)
    (he : ∀ a : cells, ∀ v ∈ window,
      ‖((A * (((smoothProductPMF (residueProfileWidth q V)
        (residueProfileWidth_pos q V hq hV)).map (centeredPhysicalCubeMap root D))
          (v - physicalResidueOffsetShift root root₀ D D₀
            (boundedColumnResidueRepresentative q a.val) q)).toReal : ℝ) : ℂ) - ψ v‖ ≤ E) :
    let Q := residueProfileWidth q V
    let hQ := residueProfileWidth_pos q V hq hV
    let F := fun a : cells => physicalResidueReconstruction root₀ D₀ base
      (boundedColumnResidueRepresentative q a.val) q
    ‖(∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑' z, ((smoothProductPMF Q hQ z).toReal : ℂ) *
          φ (physicalCubeResidueCoordinates root D base (boundedColumnResidueRepresentative q a.val) q z)) /
          (Z : ℂ) -
      (∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑ v ∈ window, (ψ v / (A : ℂ)) * φ (F a v)) / (Z : ℂ)‖ ≤
      (∑ a : cells, selectedResidueCellWeight q cells V a *
        ((E/A) * ∑ v ∈ window, ‖φ (F a v)‖)) / Z := by
  classical
  intro Q hQ F
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ]
  apply div_le_div_of_nonneg_right _ hZ.le
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (selectedResidueCellWeight_nonneg q cells V a)]
  exact mul_le_mul_of_nonneg_left
    (smoothPhysicalResidue_reference_window_error root root₀ D D₀ base
      (boundedColumnResidueRepresentative q a.val) q hq modulus hres Q hQ window
      (hwindow a) ψ φ hA (he a)) (selectedResidueCellWeight_nonneg q cells V a)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "refcols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y₀

omit [DecidableEq G] [Fintype α] [DecidableEq α] in
include x in
theorem allocatedPrincipalColumns_difference_sum_bound (i : Unit ⊕ α) :
    (∑ j, |((cols i j - refcols i j : ℤ) : ℝ)|) ≤
      Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
        (2 * allocatedPhysicalEntryBudget B U basis S c) := by
  have hentry (z : PrincipalIntegerTuples B (layerSamplerDegree I n) α
      (allocatedPrincipalSides B U basis S)) (j) :
      |(principalSpatialColumns (fun j => c (Sum.inr j)) id z i j : ℝ)| ≤
        allocatedPhysicalEntryBudget B U basis S c := by
    rw [← allocatedPhysicalCube_principal_columns B U basis S c x z i j]
    exact allocatedPhysicalCube_coefficient_entry_bound B U basis S c x z i (some (Sum.inr j))
  calc
    _ ≤ ∑ _j : PrincipalTupleIndex B (layerSamplerDegree I n),
        2 * allocatedPhysicalEntryBudget B U basis S c := by
      apply Finset.sum_le_sum
      intro j _
      rw [Int.cast_sub]
      exact (abs_sub _ _).trans (by linarith [hentry y j, hentry y₀ j])
    _ = _ := by simp

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSpatialProxyCap
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel

theorem narrowTrimmedSpatial_scale_lower {X : Type*}
    {W τ ξ ρ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1) (hρ : 0 ≤ ρ)
    (N q : X → ℕ) (x : X) (hN : 0 < N x) (hq : 0 < q x)
    (hsize : 8 * (1 + W) * (q x : ℝ) * ρ ≤ (ξ * τ) * (N x : ℝ)) :
    ρ ≤ trimmedSpatialRootScale τ N q x ∧
      ρ ≤ trimmedSpatialSlopeScale W τ N q x ∧
      ρ ≤ ξ * trimmedSpatialSlopeScale W τ N q x := by
  have h := trimmedSpatial_scale_lower hW hρ N q x hq hsize
  have hH : trimmedSpatialRootScale (ξ * τ) N q x = ξ * trimmedSpatialRootScale τ N q x := by
    unfold trimmedSpatialRootScale
    ring
  have hT : trimmedSpatialSlopeScale W (ξ * τ) N q x = ξ * trimmedSpatialSlopeScale W τ N q x := by
    unfold trimmedSpatialSlopeScale
    ring
  rw [hH, hT] at h
  have hp := trimmedSpatial_scales_pos hW hτ N q x hN hq
  exact ⟨h.1.trans (mul_le_of_le_one_left hp.1.le hξ1),
    h.2.trans (mul_le_of_le_one_left hp.2.le hξ1), h.2⟩

theorem narrowTrimmedSpatial_residue_width_lower {G J X : Type*}
    {W τ ξ ρ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1) (hρ : 0 ≤ ρ)
    (N q : X → ℕ) (hN : ∀ x, 0 < N x) (hq : ∀ x, 0 < q x)
    (hsize : ∀ x, 8 * (1 + W) * (q x : ℝ) * ρ ≤ (ξ * τ) * (N x : ℝ))
    (z : Option (G ⊕ J) × X) :
    ρ ≤ residueProfileWidth q (narrowTrimmedSpatialWidths W τ ξ N) z := by
  apply (trimmedSpatial_residue_width_lower hW hρ N q hq hsize z).trans
  exact div_le_div_of_nonneg_right (narrowTrimmedSpatialWidths_lower hW hτ hξ1 N hN z)
    (Nat.cast_nonneg _)

namespace BooleanCubeKernel

theorem centeredPhysicalCubeWindow_mono {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) {V W : Option K × X → ℝ}
    (hVW : ∀ z, V z ≤ W z) :
    centeredPhysicalCubeWindow root D V ⊆ centeredPhysicalCubeWindow root D W := by
  classical
  exact Finset.image_subset_image (rectangularWeightIndices_zero_mono hVW)

theorem narrowTrimmedSpatial_window_subset {G J X α : Type*}
    [Fintype G] [Fintype J] [Fintype X] [Fintype α]
    (root : G ⊕ J → ℤ) (D : Matrix α (G ⊕ J) ℤ)
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1)
    (N q : X → ℕ) (hN : ∀ x, 0 < N x) :
    centeredPhysicalCubeWindow root D (residueProfileWidth q (narrowTrimmedSpatialWidths W τ ξ N)) ⊆
      centeredPhysicalCubeWindow root D (residueProfileWidth q (trimmedSpatialWidths W τ N)) := by
  apply centeredPhysicalCubeWindow_mono
  intro z
  exact div_le_div_of_nonneg_right (narrowTrimmedSpatialWidths_le hW hτ hξ1 N hN z)
    (Nat.cast_nonneg _)

end BooleanCubeKernel
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedNarrowReferenceTest
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)

local notation "vars" => LayerSamplerVariables G I n B
local notation "sides" => allocatedPrincipalSides B U basis S

omit [DecidableEq α] in
theorem allocatedTrimmedSpatial_whole_reference_window
    (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides)
    {X : Type*} [Fintype X] (N q : X → ℕ)
    (hN : ∀ d, 0 < N d) (hq : ∀ d, 0 < q d)
    {W τ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (r : Option vars × X → ℤ) (hr : ∀ k d, |(r (k,d) : ℝ)| ≤ q d)
    (period modulus : ℕ) (hdiv : ∀ d, q d * period ∣ modulus)
    (hlabel : principalResidueLabel modulus y = principalResidueLabel modulus y₀)
    (hsmall : ∀ d, 2 * (Fintype.card (Option vars) *
      (2 * allocatedPhysicalEntryBudget B U basis S c)) ≤ trimmedSpatialRootScale τ N q d)
    (v : X → (Unit ⊕ α) → ℤ)
    (hv : v ∈ centeredPhysicalCubeWindow
      (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y)
      (residueProfileWidth q (trimmedSpatialWidths (K := vars) W τ N))) :
    v + physicalResidueOffsetShift
      (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeRoot B U basis S c x y₀)
      (allocatedPhysicalCubeDirections B U basis S x y)
      (allocatedPhysicalCubeDirections B U basis S x y₀) r q ∈
      spatialWindow (trimmedSpatialRootScale τ N q) 4 := by
  let H := trimmedSpatialRootScale τ N q
  let shift := physicalResidueOffsetShift
    (allocatedPhysicalCubeRoot B U basis S c x y)
    (allocatedPhysicalCubeRoot B U basis S c x y₀)
    (allocatedPhysicalCubeDirections B U basis S x y)
    (allocatedPhysicalCubeDirections B U basis S x y₀) r q
  have hH (d) : 0 < H d := (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).1
  have hbound := (allocatedPhysicalResidue_whole_offset_shift B U basis S c x y y₀
    (0 : X → ℤ) r q hq period modulus hdiv hlabel hr).2.2
  have hs : shift ∈ spatialWindow H 1 := by
    have hcoord : ∀ d i, |(shift d i : ℝ)| ≤ H d * (1/2) := by
      intro d i
      have h := hbound d i
      have hh := hsmall d
      change |(shift d i : ℝ)| ≤ _ at h
      change 2 * _ ≤ H d at hh
      linarith
    have h := spatialWindow_of_coordinate_bound H (fun d => (hH d).le)
      (by norm_num : (0 : ℝ) ≤ 1/2) shift hcoord
    norm_num only at h
    exact h
  have hv' : v ∈ spatialWindow H 3 :=
    (mem_spatialWindow_scaled_iff H hH 3 v).mpr
      (allocatedTrimmedSpatial_window_bound B U basis S c x y
        N q hN hq hW hτ hbudget v hv)
  have h := spatialWindow_add H hv' hs
  norm_num only at h
  exact h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α
  (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "refcols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y₀
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y
local notation "root₀" => allocatedPhysicalCubeRoot B U basis S c x y₀
local notation "dirs₀" => allocatedPhysicalCubeDirections B U basis S x y₀

theorem allocatedNarrowTrimmed_whole_reference_mass_test (selection : α ↪ G) {M : ℕ}
    {X : Type*} [Fintype X] (N q : X → ℕ) (hN : ∀ d, 0 < N d) (hq : ∀ d, 0 < q d)
    {W τ κ C₀ ρ ξ δ r : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hx : GoodScalarKernelTuple selection κ M x)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hsize : ∀ d, 8 * (1 + W) * (q d : ℝ) * ρ ≤ (ξ * τ) * (N d : ℝ))
    (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
    (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (modulus : ℕ) [NeZero modulus]
    (hperiod : integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection))
    (refined : ℕ) (hdiv : ∀ d, q d * modulus ∣ refined)
    (hlabel : principalResidueLabel refined y = principalResidueLabel refined y₀)
    (hδ : 0 ≤ δ)
    (hρshift : 2 * (Fintype.card (Option vars) *
      (2 * allocatedPhysicalEntryBudget B U basis S c)) ≤ ρ)
    (hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
      (2 * allocatedPhysicalEntryBudget B U basis S c) ≤ δ * ρ)
    (hr : 0 < r) (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option vars) X q))
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells (narrowTrimmedSpatialWidths W τ ξ N) z)
    (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {Cφ Z : ℝ}
    (hCφ : 0 ≤ Cφ) (hφ : ∀ v, ‖φ v‖ ≤ Cφ) (hZ : 0 < Z) :
    let H := fun d => trimmedSpatialRootScale τ N q d
    let T := fun d => trimmedSpatialSlopeScale W τ N q d
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let _Q := residueProfileWidth q V
    let hpivot := goodScalarKernelTuple_spatial_det_ne_zero selection x ker hκ hx
    let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hpivot W S.value
      hW (Nat.cast_pos.mpr S.positive)
    let ψ := fun v : X → (Unit ⊕ α) → ℤ => ∏ d,
      spatialSiteApprox (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection)
          (liftResidueMatrix (integerResidueMatrix refcols modulus))) modulus f (H d) 4 r (v d)
    let A := ∏ d, ∏ i, physicalSpatialOutputScale α (H d) (T d) S.value i
    let E₀ := anisotropicSpatialError selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M κ C₀ ρ ξ
    let G₀ := (modulus : ℝ) ^ Fintype.card (Unit ⊕ α)
    let E₁ := E₀ + G₀ * (anisotropicSpatialDensityLip selection κ * (1 + W)) * δ
    let E := Fintype.card X * (E₁ + 4 * G₀ * (anisotropicSpatialDensityLip selection κ * (1 + W)) * r) *
      (1 + G₀ * anisotropicSpatialDensityCap selection κ + E₁) ^ Fintype.card X
    let window := spatialWindow H 4
    let F := fun a : cells => physicalResidueReconstruction root₀ dirs₀ base
      (boundedColumnResidueRepresentative q a.val) q
    ‖(∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        φ (physicalCubeRootDifferences root dirs base z)) / (Z : ℂ) -
      (∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑ v ∈ window, (ψ v / (A : ℂ)) * φ (F a v)) / (Z : ℂ)‖ ≤
      Cφ * (24 * (probabilityProfileLipschitz : ℝ) * Fintype.card (Option vars × X) / ρ) / Z +
        (∑ a : cells, selectedResidueCellWeight q cells V a *
          ((E / A) * ∑ v ∈ window, ‖φ (F a v)‖)) / Z := by
  classical
  intro H T V hV Q hpivot f ψ A E₀ G₀ E₁ E window F
  have hH (d) : 0 < H d := (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).1
  have hT (d) : 0 < T d := (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).2
  have hshiftSmall (d) : 2 * (Fintype.card (Option vars) *
      (2 * allocatedPhysicalEntryBudget B U basis S c)) ≤ H d :=
    hρshift.trans (narrowTrimmedSpatial_scale_lower hW hτ hξ1 hρ.le N q d (hN d) (hq d) (hsize d)).1
  have hmoveSmall (d) : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
      (2 * allocatedPhysicalEntryBudget B U basis S c) ≤ δ * H d :=
    hρmove.trans (mul_le_mul_of_nonneg_left
      (narrowTrimmedSpatial_scale_lower hW hτ hξ1 hρ.le N q d (hN d) (hq d) (hsize d)).1 hδ)
  have hA : 0 < A := Finset.prod_pos (fun d _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos α (hH d) (hT d) (Nat.cast_pos.mpr S.positive) i))
  have hCR (d) : integerResidueMatrix cols (q d * modulus) =
      integerResidueMatrix refcols (q d * modulus) := by
    apply integerResidueMatrix_reduce _ _ (hdiv d)
    rw [principalSpatialColumns_residue, principalSpatialColumns_residue, hlabel]
  have hphysical (d) : integerResidueMatrix (physicalCubeCoefficient root dirs) (q d * modulus) =
      integerResidueMatrix (physicalCubeCoefficient root₀ dirs₀) (q d * modulus) :=
    integerResidueMatrix_reduce _ _ (hdiv d)
      (allocatedPhysicalCube_residue_of_whole_label B U basis S c x y y₀ refined hlabel)
  have hrep (a : cells) (k) (d) :
      |(boundedColumnResidueRepresentative q a.val (k,d) : ℝ)| ≤ q d := by
    have h := boundedColumnResidueRepresentative_bounds q hq a.val (k,d)
    rw [abs_of_nonneg (by exact_mod_cast h.1 :
      (0 : ℝ) ≤ boundedColumnResidueRepresentative q a.val (k,d))]
    exact_mod_cast h.2.le
  have hwindow (a : cells) (v) (hv : v ∈ centeredPhysicalCubeWindow root dirs Q) :
      v + physicalResidueOffsetShift root root₀ dirs dirs₀
        (boundedColumnResidueRepresentative q a.val) q ∈ window :=
    allocatedTrimmedSpatial_whole_reference_window B U basis S c x y y₀ N q hN hq hW hτ hbudget
      (boundedColumnResidueRepresentative q a.val) (hrep a) modulus refined hdiv hlabel hshiftSmall v
        (narrowTrimmedSpatial_window_subset root dirs hW hτ hξ1 N q hN hv)
  have he (a : cells) (v) (hv : v ∈ window) :
      ‖((A * (((smoothProductPMF Q (residueProfileWidth_pos q V hq hV)).map
        (centeredPhysicalCubeMap root dirs))
          (v - physicalResidueOffsetShift root root₀ dirs dirs₀
            (boundedColumnResidueRepresentative q a.val) q)).toReal : ℝ) : ℂ) - ψ v‖ ≤ E :=
    allocatedNarrowTrimmed_shifted_vector_site_error_s2 B U basis S c x y y₀ selection N q hN hq
      hW hτ hκ hρ hx hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh
      modulus hperiod (boundedColumnResidueRepresentative q a.val) (hrep a) hCR hδ
      (fun d i => (allocatedPrincipalColumns_difference_sum_bound B U basis S c x y y₀ i).trans (hmoveSmall d))
      (by norm_num : (0 : ℝ) < 4) hr v ((mem_spatialWindow_scaled_iff H hH 4 v).mp hv)
  have hwidth (z : Option vars × X) : ρ ≤ residueProfileWidth q V z :=
    narrowTrimmedSpatial_residue_width_lower hW hτ hξ1 hρ.le N q hN hq hsize z
  have hrec := physicalSelectedResidue_width_recenter_s2 root dirs base q hq cells V hV hmass
    hρ8 hwidth φ hCφ hφ hZ
  have hsite := physicalCenteredResidueMixture_reference_error root root₀ dirs dirs₀ base q hq modulus hphysical
    cells V hV window hwindow ψ φ hA hZ he
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hrec hsite)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedMassTupleComparison
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem complexMean_div_const {A : Type*} [Fintype A]
    (p : FiniteProbabilityWeights A) (f : A → ℂ) (Z : ℂ) :
    p.complexMean (fun a => f a / Z) = p.complexMean f / Z := by
  simp only [complexMean, mul_div_assoc, Finset.sum_div]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedLongResidueProfile
namespace OAI

section

namespace Erdos3

theorem principalResidueLabel_eq_of_dvd {D α : Type*} {B : D → Type*} {h : D → ℕ}
    {L : PrincipalTupleIndex B h → ℕ}
    (y y₀ : PrincipalIntegerTuples B h α L) {q refined : ℕ}
    (hdiv : q ∣ refined)
    (hlabel : principalResidueLabel refined y = principalResidueLabel refined y₀) :
    principalResidueLabel q y = principalResidueLabel q y₀ := by
  exact integerResidueMatrix_reduce (fun j i => (y j i : ℤ))
    (fun j i => (y₀ j i : ℤ)) hdiv hlabel

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSlicedSpatialToCoarse
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

variable (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t) (hτ : 0 < τ)
variable {C₀ ρ δ : ℝ} (hρ : 0 < ρ)
variable (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
variable (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
variable (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
variable (hsize : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
variable (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
variable (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
variable (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
  pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
    (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
variable (hδ : 0 ≤ δ)
variable (hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
variable (hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ * ρ)
variable (hmeshpos : 0 < mesh)
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (htest : ∀ v, ‖test v‖ ≤ 1)

local notation "spatialError" => allocatedTupleSpatialError (Fintype.card X) selection
  (PrincipalTupleIndex B (layerSamplerDegree I n)) M modulus C₀ ρ ξ W δ mesh
local notation "boundaryError" => (24 * (probabilityProfileLipschitz : ℝ) *
  Fintype.card (Option (LayerSamplerVariables G I n B) × X) / ρ)

include hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh hρ8 hperiod hδ hρshift hρmove hmeshpos htest in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedNarrowTrimmed_recentered_profile_error
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (y : fullTuple)
    (hwhole : principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) =
      principalResidueLabel refined y)
    {Cg Z : ℝ} (hCg : 0 ≤ Cg) (hcap : ∀ v, ‖profile y (point v)‖ ≤ Cg) (hZ : 0 < Z) :
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let root := allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y
    let dirs := allocatedPhysicalCubeDirections B U b S x y
    ‖(∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences root dirs base z) *
          profile y (point (physicalCubeRootDifferences root dirs base z)))) / (Z : ℂ) -
      allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile y / (Z : ℂ)‖ ≤
      Cg * boundaryError / Z + spatialError * allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x N base cells point profile y / Z := by
  intro V hV root dirs
  have hκ : 0 < 1 / (M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hE : 0 ≤ spatialError := by
    have he := anisotropicSpatialError_nonneg selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M
      hκ.le (zero_le_one.trans hC₀) hρ.le hξ.le
    have hl := anisotropicSpatialDensityLip_nonneg selection hκ.le
    have hc := anisotropicSpatialDensityCap_nonneg selection hκ.le
    unfold allocatedTupleSpatialError
    dsimp only
    positivity
  have hA : 0 < ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
      (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i := by
    apply Finset.prod_pos
    intro t _
    apply Finset.prod_pos
    intro i _
    have hp := trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)
    exact physicalSpatialOutputScale_pos (Fin dim) hp.1 hp.2 (Nat.cast_pos.mpr S.positive) i
  have he := allocatedNarrowTrimmed_whole_reference_mass_test B U b S (fun _ => 0) x y
    (wholeReference (principalResidueLabel refined y)) selection N q hN hq hW hτ hκ hρ hx
    hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh hρ8 modulus hperiod refined
    (stride_mul_dvd_residueRefinedPeriod modulus q) hwhole.symm hδ hρshift hρmove hmeshpos base cells hmass
    (fun v => test v * profile y (point v)) hCg
    (fun v => by rw [norm_mul]; exact (mul_le_mul_of_nonneg_right (htest v) (norm_nonneg _)).trans (by simpa using hcap v)) hZ
  dsimp only at he
  have hcoarse := principalResidueLabel_eq_of_dvd _ _
    (show modulus ∣ residueRefinedPeriod modulus q from ⟨∏ t, q t, rfl⟩) hwhole
  let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
    (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i
  let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
    (principalResidueLabel refined y)
  have hcompare : ‖(∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences root dirs base z) *
          profile y (point (physicalCubeRootDifferences root dirs base z)))) / (Z : ℂ) -
      allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile y / (Z : ℂ)‖ ≤
      Cg * boundaryError / Z +
        (∑ a : cells, selectedResidueCellWeight q cells V a * ((spatialError / A) *
          ∑ v ∈ window, ‖test (reconstruct a.val v) * profile y (point (reconstruct a.val v))‖)) / Z := by
    simpa only [allocatedRecenteredProfileTerm, allocatedWholeResidueReconstruction,
      allocatedResidueSpatialKernel, principalSpatialColumns_residue, hcoarse,
      allocatedTupleSpatialError, mul_assoc, A, reconstruct] using he
  refine hcompare.trans (add_le_add le_rfl ?_)
  apply div_le_div_of_nonneg_right _ hZ.le
  unfold allocatedRecenteredProfileMass
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [mul_left_comm spatialError]
  apply mul_le_mul_of_nonneg_left _ (selectedResidueCellWeight_nonneg _ _ _ _)
  change spatialError / _ * _ ≤ spatialError * (_ / _)
  rw [← mul_div_assoc, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hA.le
  apply mul_le_mul_of_nonneg_left _ hE
  apply Finset.sum_le_sum
  intro v _
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (htest _) (norm_nonneg _)).trans_eq (one_mul _)

include hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh hρ8 hperiod hδ hρshift hρmove hmeshpos htest in
theorem allocatedNarrowTrimmed_recentered_profile_error_law_s2_oai
    (law : FiniteProbabilityWeights fullTuple)
    (hwhole : ∀ y, law.weight y ≠ 0 →
      principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) = principalResidueLabel refined y)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    {Cg Z : ℝ} (hCg : 0 ≤ Cg)
    (hcap : ∀ y, law.weight y ≠ 0 → ∀ v, ‖profile y (point v)‖ ≤ Cg) (hZ : 0 < Z) :
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let projected := fun y => ∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) base z) *
          profile y (point (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) base z)))
    ‖law.complexMean projected / (Z : ℂ) -
      law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile) / (Z : ℂ)‖ ≤
      Cg * boundaryError / Z + spatialError * law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x N base cells point profile) / Z := by
  intro V hV projected
  let recentered := allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
    B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile
  let mass := allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
    B U b S X modulus q wholeReference x N base cells point profile
  have he := law.norm_complexMean_sub_le (fun y => projected y / (Z : ℂ))
    (fun y => recentered y / (Z : ℂ)) (fun y => Cg * boundaryError / Z + spatialError * mass y / Z)
    (fun y hy => allocatedNarrowTrimmed_recentered_profile_error B U b S X modulus q wholeReference
      x hM selection hx N hW mesh base cells point test hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1
      hsize hmesh hρ8 hperiod hδ hρshift hρmove hmeshpos hmass htest profile y (hwhole y hy) hCg (hcap y hy) hZ)
  rw [FiniteProbabilityWeights.complexMean_div_const, FiniteProbabilityWeights.complexMean_div_const,
    FiniteProbabilityWeights.mean_add, FiniteProbabilityWeights.mean_const] at he
  have hm : law.mean (fun y => spatialError * mass y / Z) = spatialError * law.mean mass / Z := by
    simp only [FiniteProbabilityWeights.mean, mul_div_assoc, Finset.sum_div]
    rw [Finset.mul_sum]
    congr 1
    funext y
    ring
  rw [hm] at he
  exact he

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedNarrowTrimmed_recentered_profile_error_law_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedNarrowTrimmed_recentered_profile_error_law_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
