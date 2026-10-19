-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.AllocatedModelPhysicalExpansionIdentity.exists_native_source_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:25:07.064717+00:00
-- url     : https://prove2.me/submissions/98f54a7d-53dc-4b2e-b980-b83bde780bda

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B277
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedModelPhysicalExpansionIdentity_exists_twisted_common_cover_source_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MatrixSupInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem matrixSupCLM_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (x : κ → ℝ) : matrixSupCLM A x = A.mulVec x := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.TranslatedMixtureL1
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype I] in
theorem pivotOutputDensity_formula (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ) (v : I → ℝ) :
    pivotOutputDensity A B f v = inverseJacobian A * ∫ y, f (y, A.symm (v - B y)) := by
  exact integral_const_mul _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFiberUniformBound
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem normalizedPivotEquiv_coe (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (S P : I → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    (normalizedPivotEquiv A hA S P hS hP).toContinuousLinearMap =
      matrixSupCLM (normalizedIntegerPivot A S P) :=
  (matrixSupCLM_inverse_spec (normalizedIntegerPivot A S P)
    (normalizedIntegerPivot_det_ne_zero A hA S P hS hP)).1.choose_spec

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueIntervalFactors
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem residueSiteIndicator_range {m : ℕ} (r : ZMod m) (u : ℤ) :
    0 ≤ residueSiteIndicator r u ∧ residueSiteIndicator r u ≤ 1 := by
  unfold residueSiteIndicator
  split_ifs <;> norm_num

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialSiteShift
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem spatialSiteTerm_zero_outside {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) (f : ((Unit ⊕ I) → ℝ) → ℝ) (H b r a : ℝ) (hr : 0 < r)
    (hsupport : ∀ v, (∃ i, a < |spatialStar v i|) → f v = 0)
    (t : SpatialSiteLabel I m b r) (v : (Unit ⊕ I) → ℤ)
    (hv : ∃ i, a + 2 * r < |((spatialStar v i : ℤ) : ℝ) / H|) :
    spatialSiteCoefficient A B m f b r t *
      (∏ i, (residueIntervalSiteWeight b r H (t.1 i) (t.2 i) (spatialStar v i) : ℂ)) = 0 := by
  by_cases hc : spatialSiteCoefficient A B m f b r t = 0
  · rw [hc, zero_mul]
  by_cases hw : (∏ i, (residueIntervalSiteWeight b r H (t.1 i) (t.2 i) (spatialStar v i) : ℂ)) = 0
  · rw [hw, mul_zero]
  obtain ⟨i, hi⟩ := hv
  have hwi := (Finset.prod_ne_zero_iff.mp hw) i (Finset.mem_univ i)
  have hreal : residueIntervalSiteWeight b r H (t.1 i) (t.2 i) (spatialStar v i) ≠ 0 := by
    exact_mod_cast hwi
  have hweight : intervalSiteWeight b r (t.2 i) ((spatialStar v i : ℤ) / H) ≠ 0 :=
    (mul_ne_zero_iff.mp hreal).2
  have hnear := intervalSiteWeight_near b r (t.2 i) ((spatialStar v i : ℤ) / H)
    (lt_of_le_of_ne (intervalSiteWeight_range b hr _ _).1 hweight.symm)
  have hcenter : a < |intervalSiteCenter b r (t.2 i)| := by
    rw [Real.dist_eq] at hnear
    have ht := abs_add_le (((spatialStar v i : ℤ) : ℝ) / H - intervalSiteCenter b r (t.2 i))
      (intervalSiteCenter b r (t.2 i))
    rw [sub_add_cancel] at ht
    linarith only [hi, hnear, ht]
  have hz : spatialStarDensity f (fun j => intervalSiteCenter b r (t.2 j)) = 0 := by
    unfold spatialStarDensity
    rw [hsupport _ (by simpa only [spatialStar_unstar] using (show ∃ j, a < |intervalSiteCenter b r (t.2 j)| from ⟨i, hcenter⟩))]
    rfl
  exact (hc (by simp only [spatialSiteCoefficient, hz, mul_zero])).elim

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalRowsSiteReconstruction
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem starVertexSiteFactor_prod {α V : Type*} [Fintype α]
    (factor : Unit ⊕ α → V → ℂ) (v : Finset α → V) :
    (∏ s, starVertexSiteFactor factor s (v s)) =
      ∏ i, factor i (v (spatialStarVertex i)) := by
  unfold starVertexSiteFactor
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  simp

theorem physicalCubeVertexValue_star {X α : Type*}
    (v : X → (Unit ⊕ α) → ℤ) (i : Unit ⊕ α) :
    physicalCubeVertexValue v (spatialStarVertex i) = fun x => spatialStar (v x) i := by
  funext x
  exact (spatialStar_vertex (v x) i).symm

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialShiftedWindowError
namespace OAI

section

namespace Erdos3

namespace BooleanCubeKernel

open scoped BigOperators

theorem mem_spatialWindow_scaled_iff {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) (hH : ∀ d, 0 < H d) (b : ℝ) (v : X → (Unit ⊕ α) → ℤ) :
    v ∈ spatialWindow H b ↔ ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / H d| ≤ b := by
  rw [mem_spatialWindow_iff]
  simp only [abs_div, abs_of_pos (hH _), div_le_iff₀ (hH _), mul_comm]

end BooleanCubeKernel
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSpatialResidueSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residueSiteIndicator_affine {m : ℕ} [NeZero m] (q : ℕ) (hq : 0 < q)
    (offset : ℤ) (a : ZMod m) (z : ℤ) :
    residueSiteIndicator (m := q * m)
        ((offset + (q : ℤ) * (a.val : ℤ) : ℤ) : ZMod (q * m))
        (offset + (q : ℤ) * z) = residueSiteIndicator a z := by
  have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hval : ((a.val : ℤ) : ZMod m) = a := by simp
  have heq :
      ((offset + (q : ℤ) * z : ℤ) : ZMod (q * m)) =
        ((offset + (q : ℤ) * (a.val : ℤ) : ℤ) : ZMod (q * m)) ↔
      (z : ZMod m) = a := by
    calc
      _ ↔ ((q * m : ℕ) : ℤ) ∣
          (offset + (q : ℤ) * (a.val : ℤ)) - (offset + (q : ℤ) * z) :=
        ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _
      _ ↔ (m : ℤ) ∣ (a.val : ℤ) - z := by
        rw [Nat.cast_mul, show
          (offset + (q : ℤ) * (a.val : ℤ)) - (offset + (q : ℤ) * z) =
            (q : ℤ) * ((a.val : ℤ) - z) by ring, mul_dvd_mul_iff_left hqz]
      _ ↔ (z : ZMod m) = ((a.val : ℤ) : ZMod m) :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).symm
      _ ↔ (z : ZMod m) = a := by rw [hval]
  unfold residueSiteIndicator
  simp only [heq]

theorem affineResidueIntervalSiteWeight_range (b H : ℝ) {r : ℝ} (hr : 0 < r)
    (q : ℕ) (offset : ℤ) {m : ℕ} (a : ZMod m)
    (k : Fin (intervalSiteCount b r)) (u : ℤ) :
    0 ≤ affineResidueIntervalSiteWeight b r H q offset a k u ∧
      affineResidueIntervalSiteWeight b r H q offset a k u ≤ 1 := by
  have ha := residueSiteIndicator_range
    (m := q * m) ((offset + (q : ℤ) * (a.val : ℤ) : ℤ) : ZMod (q * m)) u
  have hk := intervalSiteWeight_range b hr k (((u : ℝ) - offset) / ((q : ℝ) * H))
  exact ⟨mul_nonneg ha.1 hk.1,
    (mul_le_mul ha.2 hk.2 hk.1 zero_le_one).trans_eq (one_mul 1)⟩

theorem affineResidueIntervalSiteWeight_pullback (b r H : ℝ) (q : ℕ) (hq : 0 < q)
    (offset : ℤ) {m : ℕ} [NeZero m] (a : ZMod m)
    (k : Fin (intervalSiteCount b r)) (z : ℤ) :
    affineResidueIntervalSiteWeight b r H q offset a k (offset + (q : ℤ) * z) =
      residueIntervalSiteWeight b r H a k z := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold affineResidueIntervalSiteWeight residueIntervalSiteWeight
  rw [residueSiteIndicator_affine q hq]
  congr 2
  push_cast
  rw [add_sub_cancel_left, mul_div_mul_left _ _ hqR]

theorem affineVectorResidueSiteWeight_bound {X : Type*} [Fintype X]
    (b : ℝ) {r : ℝ} (hr : 0 < r) (H : X → ℝ) (q : X → ℕ) (offset : X → ℤ)
    {m : ℕ} (a : X → ZMod m) (k : X → Fin (intervalSiteCount b r)) (u : X → ℤ) :
    ‖affineVectorResidueSiteWeight b r H q offset a k u‖ ≤ 1 := by
  rw [affineVectorResidueSiteWeight, norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro x _
  have h := affineResidueIntervalSiteWeight_range b (H x) hr (q x) (offset x) (a x) (k x) (u x)
  simpa only [Complex.norm_real, Real.norm_of_nonneg h.1] using h.2

theorem affineVectorResidueSiteWeight_pullback {X : Type*} [Fintype X]
    (b r : ℝ) (H : X → ℝ) (q : X → ℕ) (hq : ∀ x, 0 < q x) (offset : X → ℤ)
    {m : ℕ} [NeZero m] (a : X → ZMod m) (k : X → Fin (intervalSiteCount b r))
    (z : X → ℤ) :
    affineVectorResidueSiteWeight b r H q offset a k (fun x => offset x + (q x : ℤ) * z x) =
      vectorResidueSiteWeight b r H a k z := by
  unfold affineVectorResidueSiteWeight vectorResidueSiteWeight
  apply Finset.prod_congr rfl
  intro x _
  rw [affineResidueIntervalSiteWeight_pullback b r (H x) (q x) (hq x)]

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalCubeVertexValue_residueReconstruction {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ)
    (v : X → (Unit ⊕ α) → ℤ) (s : Finset α) (x : X) :
    physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v) s x =
      physicalCubeVertexValue (physicalCubeRootDifferences root D base residue) s x +
        (q x : ℤ) * physicalCubeVertexValue v s x := by
  simp only [physicalCubeVertexValue, physicalResidueReconstruction,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem physicalResidueSpatialSiteFactor_bound {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (b : ℝ) {r : ℝ} (hr : 0 < r)
    (H : X → ℝ) {m : ℕ} (t : X → SpatialSiteLabel α m b r)
    (s : Finset α) (u : X → ℤ) :
    ‖physicalResidueSpatialSiteFactor root D base residue q b r H t s u‖ ≤ 1 := by
  apply starVertexSiteFactor_bound
  intro i y
  exact affineVectorResidueSiteWeight_bound b hr H q _ _ _ y

theorem physicalResidueStarFactor_pullback {K X α : Type*} [Fintype K] [Fintype X]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (b r : ℝ) (H : X → ℝ) {m : ℕ} [NeZero m]
    (t : X → SpatialSiteLabel α m b r) (i : Unit ⊕ α)
    (v : X → (Unit ⊕ α) → ℤ) :
    physicalResidueStarFactor root D base residue q b r H t i
        (physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v)
          (spatialStarVertex i)) =
      vectorResidueSiteWeight b r H (fun x => (t x).1 i) (fun x => (t x).2 i)
        (fun x => spatialStar (v x) i) := by
  unfold physicalResidueStarFactor
  have hvertex :
      physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v)
          (spatialStarVertex i) =
        fun x => physicalCubeVertexValue (physicalCubeRootDifferences root D base residue)
          (spatialStarVertex i) x + (q x : ℤ) * spatialStar (v x) i := by
    funext x
    rw [physicalCubeVertexValue_residueReconstruction, physicalCubeVertexValue_star v i]
  rw [hvertex]
  exact affineVectorResidueSiteWeight_pullback b r H q hq _ _ _ _

theorem physicalResidueSpatialSiteFactor_prod {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (b r : ℝ) (H : X → ℝ) {m : ℕ} [NeZero m]
    (t : X → SpatialSiteLabel α m b r) (v : X → (Unit ⊕ α) → ℤ) :
    (∏ s, physicalResidueSpatialSiteFactor root D base residue q b r H t s
      (physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v) s)) =
      ∏ i, vectorResidueSiteWeight b r H (fun x => (t x).1 i) (fun x => (t x).2 i)
        (fun x => spatialStar (v x) i) := by
  unfold physicalResidueSpatialSiteFactor
  rw [starVertexSiteFactor_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact physicalResidueStarFactor_pullback root D base residue q hq b r H t i v

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem physicalResidueReconstruction_quotient {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (u : X → (Unit ⊕ α) → ℤ)
    (hu : ∀ x i, (u x i : ZMod (q x)) =
      (physicalCubeRootDifferences root D base r x i : ZMod (q x))) :
    physicalResidueReconstruction root D base r q
      (physicalResidueQuotient root D base r q u) = u := by
  funext x i
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub
    (physicalCubeRootDifferences root D base r x i) (u x i) (q x)).mp (hu x i).symm
  simp only [physicalResidueReconstruction, physicalResidueQuotient,
    Int.mul_ediv_cancel' hd, add_sub_cancel]

theorem physicalResidueReconstruction_mem_range_iff {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (u : X → (Unit ⊕ α) → ℤ) :
    u ∈ Set.range (physicalResidueReconstruction root D base r q) ↔
      ∀ x i, (u x i : ZMod (q x)) =
        (physicalCubeRootDifferences root D base r x i : ZMod (q x)) := by
  constructor
  · rintro ⟨v, rfl⟩ x i
    simp [physicalResidueReconstruction]
  · intro hu
    exact ⟨physicalResidueQuotient root D base r q u,
      physicalResidueReconstruction_quotient root D base r q u hu⟩

theorem physicalResidueReconstruction_mem_range_star_iff {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (u : X → (Unit ⊕ α) → ℤ) :
    u ∈ Set.range (physicalResidueReconstruction root D base r q) ↔
      ∀ x i, ((spatialStar (u x) i : ℤ) : ZMod (q x)) =
        ((spatialStar (physicalCubeRootDifferences root D base r x) i : ℤ) : ZMod (q x)) := by
  rw [physicalResidueReconstruction_mem_range_iff]
  constructor
  · intro hu x i
    cases i with
    | inl i => cases i; exact hu x (.inl ())
    | inr i => simpa only [spatialStar, Sum.elim_inr, Int.cast_add] using
        congrArg₂ (· + ·) (hu x (.inl ())) (hu x (.inr i))
  · intro hu x i
    have hr := hu x (.inl ())
    change (u x (.inl ()) : ZMod (q x)) =
      (physicalCubeRootDifferences root D base r x (.inl ()) : ZMod (q x)) at hr
    cases i with
    | inl i => cases i; exact hr
    | inr i =>
      have hi := hu x (.inr i)
      simp only [spatialStar, Sum.elim_inr, Int.cast_add, hr] at hi
      exact add_left_cancel hi

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem affineResidueIntervalSiteWeight_nonzero_residue
    (b r H : ℝ) (q : ℕ) (offset : ℤ) {m : ℕ} (a : ZMod m)
    (k : Fin (intervalSiteCount b r)) (u : ℤ)
    (hu : affineResidueIntervalSiteWeight b r H q offset a k u ≠ 0) :
    (u : ZMod q) = (offset : ZMod q) := by
  have he : (u : ZMod (q * m)) =
      ((offset + (q : ℤ) * (a.val : ℤ) : ℤ) : ZMod (q * m)) := by
    by_contra h
    exact hu (by simp only [affineResidueIntervalSiteWeight, residueSiteIndicator, if_neg h, zero_mul])
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub u
    (offset + (q : ℤ) * (a.val : ℤ)) (q * m)).mp he
  have hq : (q : ℤ) ∣ ((q * m : ℕ) : ℤ) := by
    rw [Nat.cast_mul]
    exact dvd_mul_right _ _
  have hs := (hq.trans hd).sub (dvd_mul_right (q : ℤ) (a.val : ℤ))
  have heq : (offset + (q : ℤ) * (a.val : ℤ) - u) - (q : ℤ) * (a.val : ℤ) =
      offset - u := by ring
  rw [heq] at hs
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub u offset q).mpr hs

theorem affineVectorResidueSiteWeight_nonzero_residue {X : Type*} [Fintype X]
    (b r : ℝ) (H : X → ℝ) (q : X → ℕ) (offset : X → ℤ)
    {m : ℕ} (a : X → ZMod m) (k : X → Fin (intervalSiteCount b r)) (u : X → ℤ)
    (hu : affineVectorResidueSiteWeight b r H q offset a k u ≠ 0) :
    ∀ x, (u x : ZMod (q x)) = (offset x : ZMod (q x)) := by
  intro x
  have hx := (Finset.prod_ne_zero_iff.mp hu) x (Finset.mem_univ x)
  apply affineResidueIntervalSiteWeight_nonzero_residue b r (H x) (q x)
    (offset x) (a x) (k x) (u x)
  intro hz
  exact hx (by simp only [hz, Complex.ofReal_zero])

theorem physicalResidueSpatialSiteFactor_prod_nonzero_mem_range
    {K X α : Type*} [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (b r : ℝ) (H : X → ℝ)
    {m : ℕ} (t : X → SpatialSiteLabel α m b r) (u : X → (Unit ⊕ α) → ℤ)
    (hu : (∏ s, physicalResidueSpatialSiteFactor root D base residue q b r H t s
      (physicalCubeVertexValue u s)) ≠ 0) :
    u ∈ Set.range (physicalResidueReconstruction root D base residue q) := by
  simp only [physicalResidueSpatialSiteFactor, starVertexSiteFactor_prod] at hu
  apply (physicalResidueReconstruction_mem_range_star_iff root D base residue q u).mpr
  intro x i
  have hi := (Finset.prod_ne_zero_iff.mp hu) i (Finset.mem_univ i)
  have hx := affineVectorResidueSiteWeight_nonzero_residue b r H q
    (physicalCubeVertexValue (physicalCubeRootDifferences root D base residue) (spatialStarVertex i))
    (fun x => (t x).1 i) (fun x => (t x).2 i)
    (physicalCubeVertexValue u (spatialStarVertex i)) hi x
  simpa only [physicalCubeVertexValue_star] using hx

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalSupportedCubes
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem mem_physicalIntegerBoxCubes {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) (dim : ℕ) (v : X → (Unit ⊕ Fin dim) → ℤ) :
    v ∈ physicalIntegerBoxCubes N dim ↔ ∀ s, physicalCubeVertexValue v s ∈ integerBox N := by
  classical
  constructor
  · intro hv
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hv
    exact ((physicalSupportedCubeEquiv X dim (integerBox N : Set (X → ℤ))).symm p).property
  · intro hv
    let p := physicalSupportedCubeEquiv X dim (integerBox N : Set (X → ℤ)) ⟨v, hv⟩
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, Equiv.symm_apply_apply _ _⟩

theorem physicalIntegerBoxCubes_sum {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) (dim : ℕ) (φ : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) :
    (∑ v ∈ physicalIntegerBoxCubes N dim, φ v) =
      ∑ p : SupportedCube dim (integerBox N : Set (X → ℤ)),
        φ ((physicalCubeParametersEquiv X dim).symm p.val) := by
  classical
  rw [physicalIntegerBoxCubes, Finset.sum_image]
  intro p _ t _ h
  exact Subtype.ext ((physicalCubeParametersEquiv X dim).symm.injective h)

theorem physicalIntegerBoxCubes_sum_eq_count_mul_mean {X : Type*}
    [Fintype X] [DecidableEq X] (N : X → ℕ) (dim : ℕ)
    (φ : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) :
    (∑ v ∈ physicalIntegerBoxCubes N dim, φ v) =
      (integerBoxCubeCount N dim : ℂ) *
        𝔼 p : SupportedCube dim (integerBox N : Set (X → ℤ)),
          φ ((physicalCubeParametersEquiv X dim).symm p.val) := by
  rw [physicalIntegerBoxCubes_sum, integerBoxCubeCount, Nat.card_eq_fintype_card,
    ← nsmul_eq_mul, Fintype.card_smul_expect]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CanonicalSpatialSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem normalizedFiber_output_row
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    (z : I → ℝ) (y : J → ℝ) (i : I) :
    P i * ((normalizedPivotEquiv A hA S P hS hP z) i +
      (matrixSupCLM (normalizedIntegerColumns B T P) y) i) =
      (∑ j, (A i j : ℝ) * S j * z j) + ∑ j, (B i j : ℝ) * T j * y j := by
  change P i * (((normalizedPivotEquiv A hA S P hS hP).toContinuousLinearMap z) i + _) = _
  rw [normalizedPivotEquiv_coe, matrixSupCLM_apply, matrixSupCLM_apply]
  simp only [Matrix.mulVec, dotProduct, normalizedIntegerPivot_entry, normalizedIntegerColumns_entry_div]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> field_simp [(hP i).ne']

theorem normalizedFiberDensity_zero_of_row
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    (hT : ∀ j, 0 ≤ T j) (f : (J → ℝ) × (I → ℝ) → ℝ)
    (hsupport : ∀ p, 1 < ‖p‖ → f p = 0) (v : I → ℝ) (i : I)
    (hfar : (∑ j, |(A i j : ℝ)| * S j) + (∑ j, |(B i j : ℝ)| * T j) < |P i * v i|) :
    normalizedFiberDensity A hA B S P T hS hP f v = 0 := by
  let E := normalizedPivotEquiv A hA S P hS hP
  let C := matrixSupCLM (normalizedIntegerColumns B T P)
  have hzero (y : J → ℝ) : f (y, E.symm (v - C y)) = 0 := by
    by_contra hn
    let z := E.symm (v - C y)
    have hnorm : ‖(y, z)‖ ≤ 1 := le_of_not_gt (fun h => hn (hsupport _ h))
    have hy (j) : |y j| ≤ 1 := by
      exact (show |y j| ≤ ‖y‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y j).trans
        ((norm_fst_le (y,z)).trans hnorm)
    have hz (j) : |z j| ≤ 1 := by
      exact (show |z j| ≤ ‖z‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z j).trans
        ((norm_snd_le (y,z)).trans hnorm)
    have heq : (E z) i + (C y) i = v i := by
      dsimp only [z]
      rw [E.apply_symm_apply]
      simp only [Pi.sub_apply, sub_add_cancel]
    have hrow := normalizedFiber_output_row A hA B S P T hS hP z y i
    change P i * ((E z) i + (C y) i) = _ at hrow
    rw [heq] at hrow
    have hbound : |P i * v i| ≤
        (∑ j, |(A i j : ℝ)| * S j) + ∑ j, |(B i j : ℝ)| * T j := by
      rw [hrow]
      apply (abs_add_le _ _).trans
      apply add_le_add
      · apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_mul, abs_of_pos (hS j)]
        exact (mul_le_mul_of_nonneg_left (hz j) (mul_nonneg (abs_nonneg _) (hS j).le)).trans_eq (mul_one _)
      · apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_mul, abs_of_nonneg (hT j)]
        exact (mul_le_mul_of_nonneg_left (hy j) (mul_nonneg (abs_nonneg _) (hT j))).trans_eq (mul_one _)
    exact (not_le_of_gt hfar) hbound
  change pivotOutputDensity E C f v = 0
  rw [pivotOutputDensity_formula]
  simp only [hzero, integral_zero, mul_zero]

theorem normalizedFiberDensity_row_bound
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    (hT : ∀ j, 0 ≤ T j) (f : (J → ℝ) × (I → ℝ) → ℝ)
    (hsupport : ∀ p, 1 < ‖p‖ → f p = 0) (v : I → ℝ)
    (hne : normalizedFiberDensity A hA B S P T hS hP f v ≠ 0) (i : I) :
    |P i * v i| ≤ (∑ j, |(A i j : ℝ)| * S j) + ∑ j, |(B i j : ℝ)| * T j := by
  by_contra h
  exact hne (normalizedFiberDensity_zero_of_row A hA B S P T hS hP hT f hsupport v i (lt_of_not_ge h))

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [DecidableEq I] [DecidableEq J] in
theorem selectedColumn_sum (s : I ↪ J) (f : J → ℝ) :
    (∑ i, f (s i)) + (∑ j : UnselectedColumn s, f j.val) = ∑ j, f j := by
  calc
    _ = ∑ j : I ⊕ UnselectedColumn s, f (selectedColumnEquiv s j) := by
      rw [Fintype.sum_sum_type]
      rfl
    _ = _ := Equiv.sum_comp (selectedColumnEquiv s) f

omit [DecidableEq I] [DecidableEq J] in
theorem selectedSpatial_root_row_mass (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ) (H : ℝ) :
    (∑ j, |((selectedSpatialPivot root D s (.inl ()) j : ℤ) : ℝ)| * anisotropicSpatialScale I H 1 j) +
      (∑ j : UnselectedColumn s, |((selectedSpatialFreeColumns root D s (.inl ()) j : ℤ) : ℝ)| * 1) =
      H + ∑ j, |(root j : ℝ)| := by
  simpa [selectedSpatialPivot, rootDifferenceMatrix, selectedSpatialFreeColumns,
    anisotropicSpatialScale, Fintype.sum_sum_type, add_assoc] using
    congrArg (fun t : ℝ => H + t) (selectedColumn_sum s (fun j => |(root j : ℝ)|))

omit [DecidableEq I] [DecidableEq J] in
theorem selectedSpatial_slope_row_mass (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ) (H : ℝ) (i : I) :
    (∑ j, |((selectedSpatialPivot root D s (.inr i) j : ℤ) : ℝ)| * anisotropicSpatialScale I H 1 j) +
      (∑ j : UnselectedColumn s, |((selectedSpatialFreeColumns root D s (.inr i) j : ℤ) : ℝ)| * 1) =
      ∑ j, |(D i j : ℝ)| := by
  simpa [selectedSpatialPivot, rootDifferenceMatrix, selectedSpatialFreeColumns,
    anisotropicSpatialScale, Fintype.sum_sum_type] using
    selectedColumn_sum s (fun j => |(D i j : ℝ)|)

theorem canonicalSpatialSiteDensity_star_bound (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)
    (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
    (hD : ∀ i, (∑ j, |(D i j : ℝ)|) ≤ 1 + W)
    (v : (Unit ⊕ I) → ℝ) (hne : canonicalSpatialSiteDensity s root D hp W L hW hL v ≠ 0) :
    ∀ i, |spatialStar v i| ≤ 3 := by
  let H := 1 + W
  have hH : 0 < H := by dsimp only [H]; linarith
  let P := physicalSpatialOutputScale I H 1 L
  have hP : ∀ i, 0 < P i := physicalSpatialOutputScale_pos I hH zero_lt_one hL
  let w := fun i => H / P i * v i
  have hn : normalizedFiberDensity (selectedSpatialPivot root D s) hp
      (selectedSpatialFreeColumns root D s) (anisotropicSpatialScale I H 1) P (fun _ => 1)
      (anisotropicSpatialScale_pos I hH zero_lt_one) hP
      (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I)) w ≠ 0 := hne
  have hrow := normalizedFiberDensity_row_bound (selectedSpatialPivot root D s) hp
    (selectedSpatialFreeColumns root D s) (anisotropicSpatialScale I H 1) P (fun _ => 1)
    (anisotropicSpatialScale_pos I hH zero_lt_one) hP (fun _ => zero_le_one)
    (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I))
    (smoothSplitProfile_zero_outside (UnselectedColumn s) (Unit ⊕ I)) w hn
  have hscale (i) : P i * w i = H * v i := by
    dsimp only [w]
    field_simp [(hP i).ne']
  have hr : |H * v (.inl ())| ≤ H + W := by
    have h := hrow (.inl ())
    rw [hscale, selectedSpatial_root_row_mass] at h
    exact h.trans (add_le_add le_rfl hroot)
  have hd (i) : |H * v (.inr i)| ≤ H := by
    have h := hrow (.inr i)
    rw [hscale, selectedSpatial_slope_row_mass] at h
    exact h.trans (hD i)
  have hvroot : |v (.inl ())| ≤ 2 := by
    rw [abs_mul, abs_of_pos hH] at hr
    dsimp only [H] at hr hH
    nlinarith
  have hvdiff (i) : |v (.inr i)| ≤ 1 := by
    have h := hd i
    rw [abs_mul, abs_of_pos hH] at h
    nlinarith
  intro i
  cases i with
  | inl i => exact hvroot.trans (by norm_num)
  | inr i =>
    change |v (.inl ()) + v (.inr i)| ≤ 3
    exact (abs_add_le _ _).trans (by linarith [hvdiff i])

theorem canonicalSpatialSiteDensity_zero_outside (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)
    (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
    (hD : ∀ i, (∑ j, |(D i j : ℝ)|) ≤ 1 + W)
    (v : (Unit ⊕ I) → ℝ) (hv : ∃ i, 3 < |spatialStar v i|) :
    canonicalSpatialSiteDensity s root D hp W L hW hL v = 0 := by
  by_contra hn
  obtain ⟨i, hi⟩ := hv
  exact (not_lt_of_ge (canonicalSpatialSiteDensity_star_bound s root D hp hW hL hroot hD v hn i)) hi

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSpatialTermSupport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)

omit [DecidableEq G] in
theorem allocatedKernel_coefficient_sum {W : ℝ}
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (c : Option (Fin dim)) : (∑ g, |((x g c : ℤ) : ℝ)|) ≤ W := by
  have hcard : Fintype.card G ≤ Fintype.card (LayerSamplerVariables G I n B) :=
    Fintype.card_le_of_injective (Sum.inl : G → LayerSamplerVariables G I n B) Sum.inl_injective
  have hwb : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) * (S.value : ℝ) ≤ W := by
    simpa only [allocatedPhysicalRootBudget, Int.cast_zero, abs_zero, Finset.sum_const_zero, zero_add] using hbudget
  have hsum : (∑ g, |((x g c : ℤ) : ℝ)|) ≤ (Fintype.card G : ℝ) * S.value := by
    calc
      _ ≤ ∑ _g : G, (S.value : ℝ) := by
        apply Finset.sum_le_sum
        intro g _
        have hg := Finset.mem_Ico.mp (x g c).property
        exact_mod_cast abs_le.mpr ⟨hg.1, hg.2.le⟩
      _ = _ := by simp
  exact hsum.trans ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (Nat.cast_nonneg S.value)).trans hwb)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)

variable (X : Type*) [Fintype X] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] (H : X → ℝ) {W : ℝ} (hW : 0 ≤ W) (mesh : ℝ)

omit [NeZero modulus] in
theorem allocatedSpatialExpansionCoefficient_term_zero_outside
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hH : ∀ z, 0 < H z) (hmesh : 0 < mesh) (hmargin : 3 + 2 * mesh ≤ 4)
    (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus)
    (t : X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
    (hc : allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh r t ≠ 0)
    (v : X → (Unit ⊕ Fin dim) → ℤ) (hv : v ∉ spatialWindow H 4) :
    (∏ i, vectorResidueSiteWeight 4 mesh H (fun z => (t z).1 i) (fun z => (t z).2 i)
      (fun z => spatialStar (v z) i)) = 0 := by
  have hcoords : ¬ ∀ z i, |((spatialStar (v z) i : ℤ) : ℝ) / H z| ≤ 4 :=
    fun h => hv ((mem_spatialWindow_scaled_iff H hH 4 v).2 h)
  push Not at hcoords
  obtain ⟨z, i, hi⟩ := hcoords
  let root := fun g => (0 : ℤ) + (x g none : ℤ)
  let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x root
    (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
  have hroot : (∑ g, |(root g : ℝ)|) ≤ W := by
    simpa only [root, zero_add] using allocatedKernel_coefficient_sum B U b S x hbudget none
  have hD : ∀ i, (∑ g, |(scalarCubeDifferenceMatrix x i g : ℝ)|) ≤ 1 + W := by
    intro i
    have h := allocatedKernel_coefficient_sum B U b S x hbudget (some i)
    change (∑ g, |((x g (some i) : ℤ) : ℝ)|) ≤ 1 + W
    linarith only [h]
  let f := canonicalSpatialSiteDensity selection root (scalarCubeDifferenceMatrix x) hp W S.value
    hW (Nat.cast_pos.mpr S.positive)
  let A := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection
  let Bextra := Matrix.fromCols (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)
    (liftResidueMatrix (principalSpatialResidueColumns modulus (fun _ => (0 : ℤ)) id r))
  have hcz : spatialSiteCoefficient A Bextra modulus f 4 mesh (t z) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hc) z (Finset.mem_univ z)
  have hz := spatialSiteTerm_zero_outside A Bextra modulus f (H z) 4 mesh 3 hmesh
    (canonicalSpatialSiteDensity_zero_outside selection root (scalarCubeDifferenceMatrix x)
      hp hW (Nat.cast_pos.mpr S.positive) hroot hD) (t z) (v z) ⟨i, hmargin.trans_lt hi⟩
  simp only [vectorResidueSiteWeight]
  rw [Finset.prod_comm]
  exact Finset.prod_eq_zero (Finset.mem_univ z) ((mul_eq_zero.mp hz).resolve_left hcz)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalCubeWindowReindex
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem physicalResidueWindow_sum_eq_box_sum {K X : Type*} [Fintype K]
    [Fintype X] [DecidableEq X] {dim : ℕ}
    (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q N : X → ℕ) (hq : ∀ x, 0 < q x)
    (window : Finset (X → (Unit ⊕ Fin dim) → ℤ))
    (φ : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)
    (hbox : ∀ v ∈ window, φ (physicalResidueReconstruction root D base residue q v) ≠ 0 →
      ∀ s, physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v) s ∈ integerBox N)
    (hwindow : ∀ v, v ∉ window → φ (physicalResidueReconstruction root D base residue q v) = 0)
    (hresidue : ∀ u, φ u ≠ 0 → u ∈ Set.range (physicalResidueReconstruction root D base residue q)) :
    (∑ v ∈ window, φ (physicalResidueReconstruction root D base residue q v)) =
      ∑ u ∈ physicalIntegerBoxCubes N dim, φ u := by
  have hi := physicalResidueReconstruction_injective root D base residue q hq
  calc
    _ = ∑ u ∈ window.image (physicalResidueReconstruction root D base residue q), φ u := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => hi h
    _ = _ := by
      apply Finset.sum_congr_of_eq_on_inter
      · intro u hu hn
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
        by_contra hne
        exact hn ((mem_physicalIntegerBoxCubes N dim _).mpr (hbox v hv hne))
      · intro u _ hn
        by_contra hne
        obtain ⟨v, rfl⟩ := hresidue u hne
        have hv : v ∉ window := fun hv => hn (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
        exact hne (hwindow v hv)
      · intro _ _ _
        rfl

theorem physicalResidueWindow_sum_eq_count_mul_mean {K X : Type*} [Fintype K]
    [Fintype X] [DecidableEq X] {dim : ℕ}
    (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q N : X → ℕ) (hq : ∀ x, 0 < q x)
    (window : Finset (X → (Unit ⊕ Fin dim) → ℤ))
    (φ : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)
    (hbox : ∀ v ∈ window, φ (physicalResidueReconstruction root D base residue q v) ≠ 0 →
      ∀ s, physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v) s ∈ integerBox N)
    (hwindow : ∀ v, v ∉ window → φ (physicalResidueReconstruction root D base residue q v) = 0)
    (hresidue : ∀ u, φ u ≠ 0 → u ∈ Set.range (physicalResidueReconstruction root D base residue q)) :
    (∑ v ∈ window, φ (physicalResidueReconstruction root D base residue q v)) =
      (integerBoxCubeCount N dim : ℂ) *
        𝔼 p : SupportedCube dim (integerBox N : Set (X → ℤ)),
          φ ((physicalCubeParametersEquiv X dim).symm p.val) := by
  rw [physicalResidueWindow_sum_eq_box_sum root D base residue q N hq window φ hbox hwindow hresidue,
    physicalIntegerBoxCubes_sum_eq_count_mul_mean]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReconstructedCubeNativePartner
namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical
attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem native_partner_of_physical_cube_norm {s n : ℕ} (N : Fin n → ℕ)
    [∀ i, NeZero (N i)] (p : ℝ) (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p)
    (f : (Fin n → ℤ) → ℂ) (twist : Finset (Fin (s + 1)) → (Fin n → ℤ) → ℂ)
    (hf : ∀ x ∈ integerBox N, ‖f x‖ ≤ 1)
    (ht : ∀ site x, x ∈ integerBox N → ‖twist site x‖ ≤ 1)
    (hsource : Real.exp (-p) ≤ ‖𝔼 cube : SupportedCube (s + 1) (integerBox N : Set (Fin n → ℤ)),
      let u := (physicalCubeParametersEquiv (Fin n) (s + 1)).symm cube.val
      ∏ site, conjugationPower site.card (f (physicalCubeVertexValue u site)) *
        twist site (physicalCubeVertexValue u site)‖) :
    ∃ V : NativeSampleCorrelation (fun _ : Fin n => 1) s
      ((p + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))
      (integerBox N) id (fun x => f x * twist ∅ x),
      V.test.normBound ≤ 1 ∧
      Real.exp (-((p + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))) ≤
        ‖𝔼 x ∈ integerBox N, f x * star (star (twist ∅ x) * V.test.eval x)‖ := by
  let z : ℂ := 𝔼 cube : SupportedCube (s + 1) (integerBox N : Set (Fin n → ℤ)),
    let u := (physicalCubeParametersEquiv (Fin n) (s + 1)).symm cube.val
    ∏ site, conjugationPower site.card (f (physicalCubeVertexValue u site)) *
      twist site (physicalCubeVertexValue u site)
  obtain ⟨c, hc, hcz⟩ := Complex.exists_norm_eq_mul_self z
  have hmass : (∑ _ : Unit, ‖c‖) ≤ Real.exp p := by
    simpa only [Finset.univ_unique, Finset.sum_singleton, hc] using Real.one_le_exp hp
  have hpositive : Real.exp (-p) ≤ (c * z).re := by
    rw [← hcz, Complex.ofReal_re]
    exact hsource
  have he : ‖c * z - ∑ _ : Unit, c * z‖ ≤ Real.exp (-p) / 2 := by
    simp only [Finset.univ_unique, Finset.sum_singleton, sub_self, norm_zero]
    positivity
  obtain ⟨i, V, hV, hcorr⟩ :=
    (Classical.choose_spec (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s)).2
      N p hp hn f (fun _ : Unit => c) (fun _ => twist) hf (fun _ => ht) hmass (c * z) hpositive he
  exact ⟨V, hV, hcorr⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialSiteNativePartner
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

variable {K X : Type*} [Fintype K] [Fintype X] [DecidableEq X] {dim : ℕ}
variable (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
variable (residue : Option K × X → ℤ) (q N : X → ℕ) (H : X → ℝ) (radius mesh : ℝ)
variable {modulus : ℕ} (t : X → SpatialSiteLabel (Fin dim) modulus radius mesh)
variable (input : (X → ℤ) → ℂ) (analytic : Finset (Fin dim) → (X → ℤ) → ℂ)
local notation "spatial" => physicalResidueSpatialSiteFactor root D base residue q radius mesh H t

theorem physicalSpatialProduct_support
    (hinput : ∀ u, u ∉ integerBox N → input u = 0)
    (u : X → (Unit ⊕ Fin dim) → ℤ)
    (hproduct : (∏ site, conjugationPower site.card (input (physicalCubeVertexValue u site)) *
      (spatial site (physicalCubeVertexValue u site) * analytic site (physicalCubeVertexValue u site))) ≠ 0) :
    (∀ site, physicalCubeVertexValue u site ∈ integerBox N) ∧
      u ∈ Set.range (physicalResidueReconstruction root D base residue q) := by
  have hsite (site : Finset (Fin dim)) := (Finset.prod_ne_zero_iff.mp hproduct) site (Finset.mem_univ site)
  constructor
  · intro site
    by_contra hnot
    apply hsite site
    simp only [hinput _ hnot, map_zero, zero_mul]
  · apply physicalResidueSpatialSiteFactor_prod_nonzero_mem_range root D base residue q radius mesh H t u
    apply Finset.prod_ne_zero_iff.mpr
    intro site _
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (hsite site)).2).1

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical
attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {s n : ℕ} {K : Type*} [Fintype K]
variable (root : K → ℤ) (D : Matrix (Fin (s + 1)) K ℤ) (base : Fin n → ℤ)
variable (residue : Option K × Fin n → ℤ) (stride N : Fin n → ℕ)
variable [∀ i, NeZero (N i)] (H : Fin n → ℝ) (radius mesh : ℝ)
variable {modulus : ℕ} (t : Fin n → SpatialSiteLabel (Fin (s + 1)) modulus radius mesh)
variable (f : (Fin n → ℤ) → ℂ) (analytic : Finset (Fin (s + 1)) → (Fin n → ℤ) → ℂ)
local notation "spatial" => physicalResidueSpatialSiteFactor root D base residue stride radius mesh H t
local notation "twist" => (fun site u => spatial site u * analytic site u)

theorem native_partner_of_supported_spatial_site_source
    (hstride : ∀ i, 0 < stride i) (hmesh : 0 < mesh)
    (hf : ∀ x ∈ integerBox N, ‖f x‖ ≤ 1)
    (hzero : ∀ x, x ∉ integerBox N → f x = 0)
    (ha : ∀ site x, x ∈ integerBox N → ‖analytic site x‖ ≤ 1)
    (hwindow : ∀ v, v ∉ spatialWindow H radius →
      (∏ site, spatial site (physicalCubeVertexValue
        (physicalResidueReconstruction root D base residue stride v) site)) = 0)
    {p q volume : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hn : (n : ℝ) ≤ p + q)
    (hvolume : 0 < volume) (hratio : (integerBoxCubeCount N (s + 1) : ℝ) / volume ≤ Real.exp q)
    (hsource : Real.exp (-p) ≤ ‖(∑ v ∈ spatialWindow H radius,
      let u := physicalResidueReconstruction root D base residue stride v
      ∏ site, conjugationPower site.card (f (physicalCubeVertexValue u site)) *
        (spatial site (physicalCubeVertexValue u site) * analytic site (physicalCubeVertexValue u site))) /
          (volume : ℂ)‖) :
    ∃ V : NativeSampleCorrelation (fun _ : Fin n => 1) s
      ((p + q + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))
      (integerBox N) id (fun x => f x * (spatial ∅ x * analytic ∅ x)),
      V.test.normBound ≤ 1 ∧
      Real.exp (-((p + q + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))) ≤
        ‖𝔼 x ∈ integerBox N, f x * star (star (spatial ∅ x * analytic ∅ x) * V.test.eval x)‖ := by
  let φ := fun u => ∏ site, conjugationPower site.card (f (physicalCubeVertexValue u site)) *
    (spatial site (physicalCubeVertexValue u site) * analytic site (physicalCubeVertexValue u site))
  have hsupport := physicalSpatialProduct_support root D base residue stride N H radius mesh t f analytic hzero
  have hwindow' (v) (hv : v ∉ spatialWindow H radius) :
      φ (physicalResidueReconstruction root D base residue stride v) = 0 := by
    dsimp only [φ]
    simp only [Finset.prod_mul_distrib]
    rw [hwindow v hv, zero_mul, mul_zero]
  have he := physicalResidueWindow_sum_eq_count_mul_mean root D base residue stride N hstride
    (spatialWindow H radius) φ (fun v _ hv => (hsupport _ hv).1) hwindow'
    (fun u hu => (hsupport u hu).2)
  let z : ℂ := 𝔼 cube : SupportedCube (s + 1) (integerBox N : Set (Fin n → ℤ)),
    φ ((physicalCubeParametersEquiv (Fin n) (s + 1)).symm cube.val)
  have hbound : Real.exp (-p) ≤ Real.exp q * ‖z‖ := by
    change Real.exp (-p) ≤ ‖(∑ v ∈ spatialWindow H radius,
      φ (physicalResidueReconstruction root D base residue stride v)) / (volume : ℂ)‖ at hsource
    rw [he, norm_div, norm_mul] at hsource
    have hc : 0 ≤ (integerBoxCubeCount N (s + 1) : ℝ) := Nat.cast_nonneg _
    simp only [Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg hvolume.le] at hsource
    calc
      _ ≤ (integerBoxCubeCount N (s + 1) : ℝ) / volume * ‖z‖ := by
        simpa only [z, div_mul_eq_mul_div] using hsource
      _ ≤ _ := mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
  have hnorm : Real.exp (-(p + q)) ≤ ‖z‖ := by
    have hexp : Real.exp (-(p + q)) = Real.exp (-p) / Real.exp q := by
      rw [← Real.exp_sub]
      congr 1
      ring
    rw [hexp]
    exact (div_le_iff₀ (Real.exp_pos q)).mpr (by simpa only [mul_comm] using hbound)
  apply native_partner_of_physical_cube_norm N (p + q) (add_nonneg hp hq) hn f twist hf ?_ hnorm
  intro site u hu
  rw [norm_mul]
  exact (mul_le_mul (physicalResidueSpatialSiteFactor_bound root D base residue stride radius hmesh H t site u)
    (ha site u hu) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedNormalizedNativeModel
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin (s + 1))))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin (s + 1)) → (LayerSamplerAxis I n → ℝ) → ℂ)
local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : (Fin nX) → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1))
  (allocatedPrincipalSides B U b S))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) {M : ℕ} (hM : 0 < M) (selection : Fin (s + 1) ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W τ ξ mesh : ℝ} (hW : 0 ≤ W) (base : (Fin nX) → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
local notation "window" => spatialWindow (α := Fin (s + 1)) (trimmedSpatialRootScale τ N stride) 4
local notation "widths" => narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin (s + 1))
  (trimmedSpatialRootScale τ N stride z) (trimmedSpatialSlopeScale W τ N stride z) S.value i
local notation "terms" => ((Fin nX) → SpatialSiteLabel (Fin (s + 1)) spatialModulus 4 mesh)
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S (Fin nX) spatialModulus stride wholeReference x N mesh base label

variable [∀ i, NeZero (N i)]
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference label)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (wholeReference label)
attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem AllocatedModelPhysicalExpansionIdentity.exists_native_source_s2_oai
    (g : (Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
      T → (∀ a, (e a).Term) → Finset (Fin (s + 1)) → LongSpace × GridSpace → ℂ)
    (hidentity : AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    {L : ℝ≥0} (hg : ∀ label i k site, LipschitzWith L (g label i k site))
    (hgb : ∀ label i k site z, ‖g label i k site z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Vmax : ℝ≥0) (hVmax : ∀ a, V a ≤ Vmax)
    (hstride : ∀ z, 0 < stride z) (hmesh : 0 < mesh) (hmargin : 3 + 2 * mesh ≤ 4)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin (s + 1)) (spatialModulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (hV : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
    (signal : ((Fin nX) → ℤ) → ℂ)
    (hsignal : ∀ u ∈ integerBox N, ‖signal u‖ ≤ 1)
    (hzero : ∀ u, u ∉ integerBox N → signal u = 0)
    (hτ : 0 < τ)
    {Psource Pvolume : ℝ} (hPsource : 0 ≤ Psource) (hPvolume : 0 ≤ Pvolume)
    (hdim : (nX : ℝ) ≤ Psource + Pvolume)
    (hvolumeRatio : (integerBoxCubeCount N (s + 1) : ℝ) / volume ≤ Real.exp Pvolume)
    {δ Cmodel Cspatial : ℝ} (hδ : 0 < δ) (hCmodel : 0 < Cmodel) (hCspatial : 0 < Cspatial)
    (hmass : (∑ label : Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i, ∑ k,
      ‖((2 : ℂ) ^ Fintype.card (Finset (Fin (s + 1))) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
        coverSiteCoefficient e k‖) ≤ Cmodel)
    (hspatial : allocatedSpatialCoefficientCap (Fin nX) selection M spatialModulus mesh ≤ Cspatial)
    (hpositive : δ ≤ (allocatedRecenteredFiniteModelSource (τ := τ) (ξ := ξ) (mesh := mesh)
      B U b S x y₀ q d period r hr hb o bW e a f p hm spatialModulus stride N wholeReference label
      hM selection hx hW base cells (integerSelfSiteTest (s + 1) signal)).re)
    (hgain : Real.exp (-Psource) ≤ δ / (Cmodel * Cspatial)) :
    ∃ cover : ℕ, 0 < cover ∧
      (cover : ℝ) ≤ period * (Vmax : ℝ) ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} ∧
    ∃ F : Finset (Fin (s + 1)) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ site, LipschitzWith (L * (period * Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a})) (F site)) ∧
      (∀ site z, ‖F site z‖ ≤ 1) ∧
    ∃ (cell : cells) (t : terms),
      let ψ := fun u : (Fin nX) → ℤ =>
        twist cell.val t ∅ u * F ∅ (physicalGridFactorInput cover p (fun i => (u i : ℝ)))
      (∀ u, ‖ψ u‖ ≤ 1) ∧
      ∃ V : NativeSampleCorrelation (fun _ : (Fin nX) => 1) s
        ((Psource + Pvolume + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))
        (integerBox N) id (fun u => signal u * ψ u),
        V.test.normBound ≤ 1 ∧
        Real.exp (-((Psource + Pvolume + 2) ^ Classical.choose
          (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))) ≤
          ‖𝔼 u ∈ integerBox N, signal u * star (star (ψ u) * V.test.eval u)‖ := by
  obtain ⟨cover, hcover, hcoverBound, F, hF, hFb, cell, t, hct, ht, hsource⟩ :=
    hidentity.exists_twisted_common_cover_source_s2 B U b S x y₀ q d period r hr hb o bW e a f p hm
      spatialModulus stride N wholeReference label hM selection hx hW base cells g hg hgb he Vmax hVmax
      hstride hmesh hbudget hperiod hV hZ (integerSelfSiteTest (s + 1) signal)
      hδ hCmodel hCspatial hmass hspatial hpositive
  let analytic := fun site (u : (Fin nX) → ℤ) => F site (physicalGridFactorInput cover p (fun i => (u i : ℝ)))
  have hvol : 0 < volume := by
    apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j _
    have hsc := trimmedSpatial_scales_pos hW hτ N stride i (NeZero.pos (N i)) (hstride i)
    exact physicalSpatialOutputScale_pos (Fin (s + 1)) hsc.1 hsc.2 (Nat.cast_pos.mpr S.positive) j
  have hwindow (v) (hv : v ∉ window) :
      (∏ site, physicalResidueSpatialSiteFactor root dirs base
        (boundedColumnResidueRepresentative stride cell.val) stride 4 mesh
        (trimmedSpatialRootScale τ N stride) t site
        (physicalCubeVertexValue (physicalResidueReconstruction root dirs base
          (boundedColumnResidueRepresentative stride cell.val) stride v) site)) = 0 := by
    rw [physicalResidueSpatialSiteFactor_prod root dirs base
      (boundedColumnResidueRepresentative stride cell.val) stride hstride]
    exact allocatedSpatialExpansionCoefficient_term_zero_outside B U b S x (Fin nX) hM selection hx
      spatialModulus (trimmedSpatialRootScale τ N stride) hW mesh hbudget
      (fun i => (trimmedSpatial_scales_pos hW hτ N stride i (NeZero.pos (N i)) (hstride i)).1)
      hmesh hmargin (principalResidueLabel spatialModulus (wholeReference label)) t hct v hv
  have hnative := native_partner_of_supported_spatial_site_source root dirs base
    (boundedColumnResidueRepresentative stride cell.val) stride N (trimmedSpatialRootScale τ N stride) 4 mesh t
    signal analytic hstride hmesh hsignal hzero (fun site u _ => hFb site _) hwindow hPsource hPvolume hdim hvol hvolumeRatio
  have hsource' := hgain.trans hsource
  simp only [integerSelfSiteTest, Int.floor_intCast, ← Finset.prod_mul_distrib, mul_assoc] at hsource'
  obtain ⟨V, hnorm, hcorr⟩ := hnative hsource'
  refine ⟨cover, hcover, hcoverBound, F, hF, hFb, cell, t, ?_, V, hnorm, hcorr⟩
  intro u
  rw [norm_mul]
  exact (mul_le_mul (ht ∅ u) (hFb ∅ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.AllocatedModelPhysicalExpansionIdentity.exists_native_source_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.AllocatedModelPhysicalExpansionIdentity.exists_native_source_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
