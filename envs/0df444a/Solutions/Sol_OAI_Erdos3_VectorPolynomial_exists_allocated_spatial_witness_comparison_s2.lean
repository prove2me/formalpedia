-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocated_spatial_witness_comparison_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:16:44.651986+00:00
-- url     : https://prove2.me/submissions/1482e186-90b9-4db5-8237-a98f72fee893

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B176
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedCoefficientDeckSample_density_law_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedMaskedCoefficientDensity_sample_ae_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_spatial_chart_event_comparison_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientPairCover
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory

variable {K : Type*} [finiteK : Fintype K] {m : ℕ} {J : Fin m → Type*}
  [finiteCoordinates : ∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

omit finiteK finiteCoordinates in
theorem coefficientAmbientTorus_cover [Fintype K] [∀ j, Fintype (J j)]
    (a : ℕ) (z : CoefficientTorus (K := K) U) :
    coefficientAmbientTorus U (quotientIntegerCover (coefficientIntegerLattice U) a z) =
      a • coefficientAmbientTorus U z := by
  funext t
  change subspaceAmbientTorus (U t.1.1) (coefficientCoordinateTorus U (a • z) t.1) t.2 =
    a • subspaceAmbientTorus (U t.1.1) (coefficientCoordinateTorus U z t.1) t.2
  simp only [map_nsmul, Pi.smul_apply]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ControlledJointGrid
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem realDensityMeasure_integral_complex {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (φ : X → ℂ) :
    (∫ x, φ x ∂realDensityMeasure μ f) = ∫ x, (f x : ℂ) * φ x ∂μ := by
  unfold realDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hf0 _), Complex.real_smul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MaskedIntegerPeriodization
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal

variable {D : Type*} [Fintype D]

omit [Fintype D] in
private theorem masked_shift_nonzero (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (H : (D → ℝ) → ℝ) (x : D → ℝ) (n : D → ℤ)
    (h : mask (fun i => (n i : ZMod q)) * H (fun i => x i + (n i : ℝ)) ≠ 0) :
    H (fun i => x i + (n i : ℝ)) ≠ 0 := (mul_ne_zero_iff.mp h).2

theorem maskedIntegerPeriodization_lipschitz (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1)
    (H : (D → ℝ) → ℝ) {L : ℝ≥0} (hH : LipschitzWith L H)
    (h0 : ∀ x, 0 ≤ H x) (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) :
    LipschitzWith L (maskedIntegerPeriodization q mask H) := by
  apply separated_tsum_lipschitz
  · intro n
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := hH.dist_le_mul (x + fun i => (n i : ℝ)) (y + fun i => (n i : ℝ))
    rw [dist_add_right] at h
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (hmask _).1]
    calc
      _ ≤ 1 * |H (fun i => x i + (n i : ℝ)) - H (fun i => y i + (n i : ℝ))| :=
        mul_le_mul_of_nonneg_right (hmask _).2 (abs_nonneg _)
      _ ≤ L * dist x y := by simpa only [one_mul, Real.dist_eq, Pi.add_def] using h
  · intro n x
    exact mul_nonneg (hmask _).1 (h0 _)
  · intro x n k hn hk
    exact integer_shifts_small_box_injective x n k
      (hs _ (masked_shift_nonzero q mask H x n hn))
      (hs _ (masked_shift_nonzero q mask H x k hk))

omit [Fintype D] in
theorem maskedIntegerPeriodization_range (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1)
    (H : (D → ℝ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ x, H x ∈ Set.Icc (0 : ℝ) B)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) (x : D → ℝ) :
    maskedIntegerPeriodization q mask H x ∈ Set.Icc (0 : ℝ) B := by
  refine ⟨tsum_nonneg (fun n => mul_nonneg (hmask _).1 (hH _).1), ?_⟩
  by_cases hx : ∃ n : D → ℤ, H (fun i => x i + (n i : ℝ)) ≠ 0
  · obtain ⟨n, hn⟩ := hx
    unfold maskedIntegerPeriodization
    rw [tsum_eq_single n]
    · exact (mul_le_of_le_one_left (hH _).1 (hmask _).2).trans (hH _).2
    · intro k hk
      have hz : H (fun i => x i + (k i : ℝ)) = 0 := by
        by_contra hh
        exact hk (integer_shifts_small_box_injective x k n (hs _ hh) (hs _ hn))
      rw [hz, mul_zero]
  · have hz : ∀ n : D → ℤ, H (fun i => x i + (n i : ℝ)) = 0 := by simpa using hx
    simpa only [maskedIntegerPeriodization, hz, mul_zero, tsum_zero] using hB

omit [Fintype D] in
theorem maskedIntegerPeriodization_periodic (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (H : (D → ℝ) → ℝ) (x : D → ℝ) (k : D → ℤ) :
    maskedIntegerPeriodization q mask H (fun i => x i + q * (k i : ℝ)) =
      maskedIntegerPeriodization q mask H x := by
  unfold maskedIntegerPeriodization
  let v : D → ℤ := fun i => q * k i
  have h := (Equiv.addRight v).tsum_eq (fun n : D → ℤ =>
    mask (fun i => (n i : ZMod q)) * H (fun i => x i + (n i : ℝ)))
  convert h using 1
  apply tsum_congr
  intro n
  congr 1
  · congr 1
    funext i
    simp [v]
  · congr 1
    funext i
    simp [v]
    ring

omit [Fintype D] in
private theorem maskedIntegerPeriodization_rescale_periodic (q : ℕ)
    (mask : (D → ZMod q) → ℝ) (H : (D → ℝ) → ℝ)
    (x : D → ℝ) (k : D → ℤ) :
    maskedIntegerPeriodization q mask H (fun i => q * (x i + (k i : ℝ))) =
      maskedIntegerPeriodization q mask H (fun i => q * x i) := by
  simp_rw [mul_add]
  exact maskedIntegerPeriodization_periodic q mask H _ k

omit [Fintype D] in
theorem maskedIntegerTorusKernel_coe (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (H : (D → ℝ) → ℝ) (x : D → ℝ) :
    maskedIntegerTorusKernel q mask H (fun i => (x i : UnitAddCircle)) =
      maskedIntegerPeriodization q mask H (fun i => q * x i) :=
  realPeriodicTorusLift_coe _ (maskedIntegerPeriodization_rescale_periodic q mask H) x

theorem maskedIntegerTorusKernel_lipschitz (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1)
    (H : (D → ℝ) → ℝ) {L : ℝ≥0} (hH : LipschitzWith L H)
    (h0 : ∀ x, 0 ≤ H x) (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) :
    LipschitzWith ((q : ℝ≥0) * L) (maskedIntegerTorusKernel q mask H) := by
  apply realPeriodicTorusLift_lipschitz _ _ (maskedIntegerPeriodization_rescale_periodic q mask H)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (maskedIntegerPeriodization_lipschitz q mask hmask H hH h0 hs).dist_le_mul
    ((q : ℝ) • x) ((q : ℝ) • y)
  rw [dist_smul₀] at h
  simpa only [Pi.smul_def, smul_eq_mul, Real.norm_natCast, NNReal.coe_mul,
    NNReal.coe_natCast, mul_assoc, mul_left_comm] using h

omit [Fintype D] in
theorem maskedIntegerTorusKernel_range (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1)
    (H : (D → ℝ) → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ x, H x ∈ Set.Icc (0 : ℝ) B)
    (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2) (x : D → UnitAddCircle) :
    maskedIntegerTorusKernel q mask H x ∈ Set.Icc (0 : ℝ) B :=
  realPeriodicTorusLift_range _ (fun y =>
    maskedIntegerPeriodization_range q mask hmask H hB hH hs (fun i => q * y i)) x

omit [Fintype D] in
theorem maskedIntegerPeriodization_le (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ≤ 1) (H : (D → ℝ) → ℝ)
    (h0 : ∀ x, 0 ≤ H x) (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2)
    (x : D → ℝ) :
    maskedIntegerPeriodization q mask H x ≤ positiveIntegerPeriodization H x := by
  by_cases hx : ∃ n : D → ℤ, H (fun i => x i + (n i : ℝ)) ≠ 0
  · obtain ⟨n, hn⟩ := hx
    have hz (k : D → ℤ) (hk : k ≠ n) : H (fun i => x i + (k i : ℝ)) = 0 := by
      by_contra hh
      exact hk (integer_shifts_small_box_injective x k n (hs _ hh) (hs _ hn))
    unfold maskedIntegerPeriodization positiveIntegerPeriodization
    rw [tsum_eq_single n (fun k hk => by rw [hz k hk, mul_zero]), tsum_eq_single n hz]
    exact mul_le_of_le_one_left (h0 _) (hmask _)
  · have hz : ∀ n : D → ℤ, H (fun i => x i + (n i : ℝ)) = 0 := by simpa using hx
    simp only [maskedIntegerPeriodization, positiveIntegerPeriodization, hz, mul_zero, tsum_zero, le_refl]

omit [Fintype D] in
theorem maskedIntegerTorusKernel_le (q : ℕ) (mask : (D → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ≤ 1) (H : (D → ℝ) → ℝ)
    (h0 : ∀ x, 0 ≤ H x) (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1/2)
    (z : D → UnitAddCircle) :
    maskedIntegerTorusKernel q mask H z ≤ smallBoxTorusKernel H (q • z) := by
  let x : D → ℝ := fun i => centeredCircleLift (z i)
  have hx : (fun i => (x i : UnitAddCircle)) = z := funext (fun i => coe_centeredCircleLift _)
  have hqx : (fun i => (((q : ℝ) * x i : ℝ) : UnitAddCircle)) = q • z := by
    funext i
    simp only [← nsmul_eq_mul, AddCircle.coe_nsmul, x, coe_centeredCircleLift, Pi.smul_apply]
  rw [← hx, maskedIntegerTorusKernel_coe, hx, ← hqx]
  rw [smallBoxTorusKernel, realPeriodicTorusLift_coe _ (positiveIntegerPeriodization_periodic H)]
  exact maskedIntegerPeriodization_le q mask hmask H h0 hs _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SigmaProductPeriodization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {A : Type*} [Fintype A] {D : A → Type*}

theorem sigmaProductKernel_small_box (H : ∀ a, (D a → ℝ) → ℝ)
    (hs : ∀ a x, H a x ≠ 0 → ∀ i, |x i| < 1 / 2)
    (x : (Σ a, D a) → ℝ) (hx : sigmaProductKernel H x ≠ 0) :
    ∀ i, |x i| < 1 / 2 := by
  classical
  intro ⟨a, i⟩
  apply hs a _ _ i
  exact Finset.prod_ne_zero_iff.mp hx a (Finset.mem_univ a)

theorem positiveIntegerPeriodization_eq_nonzero_shift {I : Type*}
    (H : (I → ℝ) → ℝ) (hs : ∀ x, H x ≠ 0 → ∀ i, |x i| < 1 / 2)
    (x : I → ℝ) (n : I → ℤ) (hn : H (fun i => x i + (n i : ℝ)) ≠ 0) :
    positiveIntegerPeriodization H x = H (fun i => x i + (n i : ℝ)) := by
  apply tsum_eq_single n
  intro m hm
  by_contra hnonzero
  exact hm (integer_shifts_small_box_injective x m n (hs _ hnonzero) (hs _ hn))

theorem positiveIntegerPeriodization_sigmaProductKernel
    (H : ∀ a, (D a → ℝ) → ℝ)
    (hs : ∀ a x, H a x ≠ 0 → ∀ i, |x i| < 1 / 2)
    (x : (Σ a, D a) → ℝ) :
    positiveIntegerPeriodization (sigmaProductKernel H) x =
      ∏ a, positiveIntegerPeriodization (H a) (fun i => x ⟨a, i⟩) := by
  classical
  by_cases hall : ∀ a, ∃ n : D a → ℤ,
      H a (fun i => x ⟨a, i⟩ + (n i : ℝ)) ≠ 0
  · choose n hn using hall
    let N : (Σ a, D a) → ℤ := fun i => n i.1 i.2
    have hN : sigmaProductKernel H (fun i => x i + (N i : ℝ)) ≠ 0 := by
      exact Finset.prod_ne_zero_iff.mpr (fun a _ => hn a)
    rw [positiveIntegerPeriodization_eq_nonzero_shift _
      (sigmaProductKernel_small_box H hs) x N hN]
    unfold sigmaProductKernel
    apply Finset.prod_congr rfl
    intro a _
    exact (positiveIntegerPeriodization_eq_nonzero_shift (H a) (hs a)
      (fun i => x ⟨a, i⟩) (n a) (hn a)).symm
  · push Not at hall
    obtain ⟨a, ha⟩ := hall
    have hleft : positiveIntegerPeriodization (sigmaProductKernel H) x = 0 := by
      have hz (n : (Σ a, D a) → ℤ) :
          sigmaProductKernel H (fun i => x i + (n i : ℝ)) = 0 := by
        unfold sigmaProductKernel
        exact Finset.prod_eq_zero (Finset.mem_univ a) (ha (fun i => n ⟨a, i⟩))
      simp only [positiveIntegerPeriodization, hz, tsum_zero]
    have hright : positiveIntegerPeriodization (H a) (fun i => x ⟨a, i⟩) = 0 := by
      simp only [positiveIntegerPeriodization, ha, tsum_zero]
    rw [hleft]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ a) hright

theorem smallBoxTorusKernel_sigmaProductKernel
    (H : ∀ a, (D a → ℝ) → ℝ)
    (hs : ∀ a x, H a x ≠ 0 → ∀ i, |x i| < 1 / 2)
    (z : (Σ a, D a) → UnitAddCircle) :
    smallBoxTorusKernel (sigmaProductKernel H) z =
      ∏ a, smallBoxTorusKernel (H a) (fun i => z ⟨a, i⟩) := by
  have hcoe (x : (Σ a, D a) → ℝ) :
      smallBoxTorusKernel (sigmaProductKernel H) (fun i => (x i : UnitAddCircle)) =
        ∏ a, smallBoxTorusKernel (H a) (fun i => (x ⟨a, i⟩ : UnitAddCircle)) := by
    simp only [smallBoxTorusKernel,
      realPeriodicTorusLift_coe _ (positiveIntegerPeriodization_periodic _)]
    exact positiveIntegerPeriodization_sigmaProductKernel H hs x
  simpa only [coe_centeredCircleLift] using hcoe (fun i => centeredCircleLift (z i))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedJointAmbientKernel
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators NNReal

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (f : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → ℝ → ℝ)

theorem coefficientJointAmbientKernel_support (v : CoefficientAmbientIndex K J → ℝ)
    (hv : coefficientJointAmbientKernel U b o c w f v ≠ 0) :
    ∀ i, |v i| < 1/2 := by
  rintro ⟨s,i⟩
  exact canonicalAmbientKernel_support _ _ _ _ _ _ _
    ((Finset.prod_ne_zero_iff.mp hv) s (Finset.mem_univ s)) i

theorem coefficientJointAmbientKernel_bounds {B L : ℝ≥0} (hB : 1 ≤ B)
    (hcap : ∀ (s : CoefficientSlot K m) x,
      0 ≤ canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
        (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => f s.1 i s.2) x ∧
      canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
        (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => f s.1 i s.2) x ≤ B)
    (hlip : ∀ s : CoefficientSlot K m, LipschitzWith L
      (canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
        (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => f s.1 i s.2))) :
    (∀ x, 0 ≤ coefficientJointAmbientKernel U b o c w f x ∧
      coefficientJointAmbientKernel U b o c w f x ≤ (B : ℝ)^Fintype.card (CoefficientSlot K m)) ∧
    LipschitzWith (Fintype.card (CoefficientSlot K m) * L * B^Fintype.card (CoefficientSlot K m))
      (coefficientJointAmbientKernel U b o c w f) := by
  let H := fun (s : CoefficientSlot K m) (x : CoefficientAmbientIndex K J → ℝ) =>
    canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
      (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => f s.1 i s.2)
      (fun i => x ⟨s,i⟩)
  have hL : ∀ s, LipschitzWith L (H s) := by
    intro s
    apply LipschitzWith.of_dist_le_mul
    intro x y
    refine ((hlip s).dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ L.coe_nonneg)
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    exact dist_le_pi_dist x y ⟨s,i⟩
  obtain ⟨hbnd, hprod⟩ := bounded_lipschitz_real_prod H hB hL
    (fun s x => by rw [abs_of_nonneg (hcap s _).1]; exact (hcap s _).2)
  refine ⟨?_, hprod⟩
  intro x
  have h0 : 0 ≤ coefficientJointAmbientKernel U b o c w f x :=
    Finset.prod_nonneg (fun s _ => (hcap s _).1)
  exact ⟨h0, (le_abs_self _).trans (hbnd x)⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in
theorem allocatedAmbientKernelFactor_bounds (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (s : CoefficientSlot (LayerSamplerVariables G I n B) m) :
    (∀ x, 0 ≤ canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
        (fun i => allocatedLayerCenters B U b S s.1 i s.2)
        (fun i => allocatedLayerWidths B U b S s.1 i s.2)
        (fun i => allocatedLayerIntegerInterpolation B U b S s.1 i s.2) x ∧
      canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
        (fun i => allocatedLayerCenters B U b S s.1 i s.2)
        (fun i => allocatedLayerWidths B U b S s.1 i s.2)
        (fun i => allocatedLayerIntegerInterpolation B U b S s.1 i s.2) x ≤
          allocatedAmbientFactorCap (G := G) B R σ S.value V) ∧
    LipschitzWith (allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V)
      (canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
        (fun i => allocatedLayerCenters B U b S s.1 i s.2)
        (fun i => allocatedLayerWidths B U b S s.1 i s.2)
        (fun i => allocatedLayerIntegerInterpolation B U b S s.1 i s.2)) := by
  obtain ⟨hcap, hlip⟩ := allocatedLayerMixedInterpolation_bounds B U b S hR hσ s.1 s.2
  obtain ⟨ha, hl⟩ := canonicalAmbientKernel_bounds (euclideanSubspace (U s.1)) (b s.1) (o s.1)
    _ _ _ hcap hlip (hC s.1) (hV s.1)
  have hcaple : V s.1 * allocatedLayerMixedCap (G := G) B R σ S.value s.1 ≤
      allocatedAmbientFactorCap (G := G) B R σ S.value V := by
    apply le_trans (Finset.single_le_sum
      (f := fun j => V j * allocatedLayerMixedCap (G := G) B R σ S.value j)
      (fun _ _ => zero_le) (Finset.mem_univ s.1))
    exact le_add_of_nonneg_left (by norm_num)
  have hliple : allocatedAmbientLayerLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V s.1 ≤
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V := by
    unfold allocatedAmbientFactorLip
    exact Finset.single_le_sum
      (f := fun j => allocatedAmbientLayerLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V j)
      (fun _ _ => zero_le) (Finset.mem_univ s.1)
  refine ⟨fun x => ⟨(ha x).1, (ha x).2.trans ?_⟩, hl.weaken hliple⟩
  exact_mod_cast hcaple

include hC hV in
theorem allocatedCoefficientJointAmbientKernel_bounds
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) :
    let A := allocatedAmbientFactorCap (G := G) B R σ S.value V
    let L := allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V
    let N := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    (∀ x, 0 ≤ allocatedCoefficientJointAmbientKernel B U b S o x ∧
      allocatedCoefficientJointAmbientKernel B U b S o x ≤ (A : ℝ)^N) ∧
    LipschitzWith (N * L * A^N) (allocatedCoefficientJointAmbientKernel B U b S o) := by
  have h := allocatedAmbientKernelFactor_bounds B U b S o C V hC hV hR hσ
  exact coefficientJointAmbientKernel_bounds U b o _ _ _
    (allocatedAmbientFactorCap_one_le (G := G) B R σ S.value V)
    (fun s x => (h s).1 x) (fun s => (h s).2)

theorem allocatedCoefficientJointAmbientKernel_support
    (x : CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ℝ)
    (hx : allocatedCoefficientJointAmbientKernel B U b S o x ≠ 0) :
    ∀ i, |x i| < 1/2 := coefficientJointAmbientKernel_support U b o _ _ _ x hx

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedJointAmbientDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators NNReal

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (f : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → ℝ → ℝ)

theorem coefficientJointAmbientKernel_periodization
    (x : CoefficientAmbientIndex K J → UnitAddCircle) :
    smallBoxTorusKernel (coefficientJointAmbientKernel U b o c w f) x =
      coefficientAmbientDensity U b o c w f x := by
  exact smallBoxTorusKernel_sigmaProductKernel
    (fun s : CoefficientSlot K m => canonicalAmbientKernel (euclideanSubspace (U s.1))
      (b s.1) (o s.1) (fun i => c s.1 i s.2) (fun i => w s.1 i s.2)
      (fun i => f s.1 i s.2))
    (fun s => canonicalAmbientKernel_support _ _ _ _ _ _) x

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedCoefficientJointAmbientKernel_density
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (x : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    smallBoxTorusKernel (allocatedCoefficientJointAmbientKernel B U b S o)
      (coefficientAmbientTorus U x) = allocatedCoefficientDensity B U b hb o hR hσ S x := by
  change smallBoxTorusKernel (coefficientJointAmbientKernel U b o _ _ _)
    (coefficientAmbientTorus U x) = _
  rw [coefficientJointAmbientKernel_periodization]
  exact allocatedCoefficientAmbientDensity_eq B U b hb o S hR hσ hσ1 C hC hchart hsmall x

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedJointMaskedDensityComparison
namespace OAI

section

namespace Erdos3
open MeasureTheory

theorem dominatedDensityRatio_mul {X : Type*} (D A : X → ℝ)
    (hA : ∀ x, 0 ≤ A x) (hAD : ∀ x, A x ≤ D x) (x : X) :
    (D x : ℂ) * dominatedDensityRatio D A x = (A x : ℂ) := by
  by_cases hD : D x = 0
  · have hAx : A x = 0 := le_antisymm (by simpa [hD] using hAD x) (hA x)
    simp [dominatedDensityRatio, hD, hAx]
  · simp only [dominatedDensityRatio, Complex.ofReal_div]
    field_simp [hD]

theorem dominatedDensityRatio_measurable {X : Type*} [MeasurableSpace X]
    (D A : X → ℝ) (hD : Measurable D) (hA : Measurable A) :
    Measurable (dominatedDensityRatio D A) :=
  Complex.measurable_ofReal.comp (hA.div hD)

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

theorem maskedDensity_integral_of_sample_law
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ρ : Measure X) (μ : Measure Y) (sample : X → Y) (hsample : Measurable sample)
    (D A : Y → ℝ) (hDm : Measurable D) (hAm : Measurable A)
    (hA0 : ∀ y, 0 ≤ A y) (hAD : ∀ y, A y ≤ D y)
    (hlaw : ρ.map sample = realDensityMeasure μ D)
    (f : X → ℝ) (hmask : ∀ᵐ x ∂ρ, A (sample x) = f x * D (sample x)) :
    (∫ y, A y ∂μ) = ∫ x, f x ∂ρ := by
  have hD0 : ∀ y, 0 ≤ D y := fun y => (hA0 y).trans (hAD y)
  have hDae : ∀ᵐ y ∂realDensityMeasure μ D, D y ≠ 0 :=
    realDensityMeasure_ae_of_support μ D hDm _ (fun y hy => hy)
  rw [← hlaw] at hDae
  have hDs : ∀ᵐ x ∂ρ, D (sample x) ≠ 0 :=
    ae_of_ae_map hsample.aemeasurable hDae
  let φ := dominatedDensityRatio D A
  have hφ : Measurable φ := dominatedDensityRatio_measurable D A hDm hAm
  have hφsample : (fun x => φ (sample x)) =ᵐ[ρ] fun x => (f x : ℂ) := by
    filter_upwards [hDs, hmask] with x hx hAx
    simp only [φ, dominatedDensityRatio, hAx, mul_div_cancel_right₀ _ hx]
  apply Complex.ofReal_injective
  calc
    Complex.ofReal (∫ y, A y ∂μ) = ∫ y, (A y : ℂ) ∂μ := integral_ofReal.symm
    _ = ∫ y, (D y : ℂ) * φ y ∂μ := by
      simp only [φ, dominatedDensityRatio_mul D A hA0 hAD]
    _ = ∫ y, φ y ∂realDensityMeasure μ D :=
      (realDensityMeasure_integral_complex μ D hDm hD0 φ).symm
    _ = ∫ x, φ (sample x) ∂ρ := by
      rw [← hlaw]
      exact integral_map hsample.aemeasurable hφ.aestronglyMeasurable
    _ = ∫ x, (f x : ℂ) ∂ρ := integral_congr_ae hφsample
    _ = Complex.ofReal (∫ x, f x ∂ρ) := integral_ofReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in
theorem allocatedMaskedCoefficientDensity_continuous
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (q : ℕ) (mask : (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1) :
    Continuous (allocatedMaskedCoefficientDensity B U b o S q mask) := by
  have hk := allocatedCoefficientJointAmbientKernel_bounds B U b S o C V hC hV hR hσ
  exact (maskedIntegerTorusKernel_lipschitz q mask hmask _ hk.2 (fun x => (hk.1 x).1)
    (allocatedCoefficientJointAmbientKernel_support B U b S o)).continuous.comp
    (coefficientAmbientTorus_continuous U)

include hC hV in
theorem allocatedMaskedCoefficientDensity_le_density
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) (mask : (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1)
    (x : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    0 ≤ allocatedMaskedCoefficientDensity B U b o S q mask x ∧
      allocatedMaskedCoefficientDensity B U b o S q mask x ≤
        allocatedCoefficientDensity B U b hb o hR hσ S
          (quotientIntegerCover (coefficientIntegerLattice U) q x) := by
  have hk := allocatedCoefficientJointAmbientKernel_bounds B U b S o C V hC hV hR hσ
  have hrange := maskedIntegerTorusKernel_range q mask hmask
    (allocatedCoefficientJointAmbientKernel B U b S o)
    (show 0 ≤ (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) by positivity)
    hk.1 (allocatedCoefficientJointAmbientKernel_support B U b S o) (coefficientAmbientTorus U x)
  refine ⟨hrange.1, ?_⟩
  have hle := maskedIntegerTorusKernel_le q mask (fun r => (hmask r).2)
    (allocatedCoefficientJointAmbientKernel B U b S o) (fun z => (hk.1 z).1)
    (allocatedCoefficientJointAmbientKernel_support B U b S o) (coefficientAmbientTorus U x)
  rw [← coefficientAmbientTorus_cover,
    allocatedCoefficientJointAmbientKernel_density B U b hb o S hR hσ hσ1 Cinv hCinv hchart hsmall] at hle
  exact hle

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientDeckMaskedIntegral
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped Classical

variable {K : Type*} [Fintype K] {m : ℕ} {J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U))

theorem CoefficientDeckDensityLaw.masked_integral
    (source : Measure (CoefficientSamplerArrays (K := K) I n))
    (density : CoefficientTorus (K := K) U → ℝ) (d : ℕ) [NeZero d]
    (hlaw : CoefficientDeckDensityLaw U bW b hb o μ source density d)
    (hdensity : Measurable density)
    (A : CoefficientTorus (K := K) U → ℝ) (hA : Measurable A)
    (hA0 : ∀ y, 0 ≤ A y)
    (hAD : ∀ y, A y ≤ density (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d y))
    (f : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d → ℝ)
    (hmask : ∀ᵐ p ∂source.prod (PMF.uniformOfFintype
      (CoefficientDeckResidues (K := K) B d)).toMeasure,
      A (canonicalCoefficientDeckSample U bW b hb o d (NeZero.pos d) p.1 p.2) =
        f p * density (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d
          (canonicalCoefficientDeckSample U bW b hb o d (NeZero.pos d) p.1 p.2))) :
    (∫ y, A y ∂μ) = ∫ p, f p ∂source.prod
      (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure := by
  exact maskedDensity_integral_of_sample_law
    (source.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure) μ
    (fun p => canonicalCoefficientDeckSample U bW b hb o d (NeZero.pos d) p.1 p.2)
    (canonicalCoefficientDeckSample_measurable U bW b hb o d)
    (fun y => density (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d y)) A
    (hdensity.comp (quotientIntegerCover_continuous _ d).measurable) hA hA0 hAD hlaw f hmask

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedMaskedCoefficientHaarLaw
namespace OAI

section

namespace Erdos3

theorem allocatedUniformPMF_fintype_transport (α : Type*) [Fintype α] [Nonempty α] :
    PMF.uniformOfFintype α = allocatedUniformPMFCanonical α := by
  unfold allocatedUniformPMFCanonical
  congr 1
  exact Subsingleton.elim _ _

end Erdos3

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped NNReal Classical
attribute [local irreducible] coefficientDeckKernelEquiv canonicalCoefficientDeckSample
  coefficientSamplerAmbientPoint allocatedMaskedCoefficientDensity
  allocatedCoefficientSource allocatedCoefficientDensity

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)]
variable [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
  [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)] in
include hC hV in
theorem allocatedMaskedCoefficientDensity_haar_data
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) [NeZero q]
    (test : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → ℝ)
    (htest : ∀ r, test r ∈ Set.Icc (0 : ℝ) 1) :
    Measurable (allocatedMaskedCoefficientDensity B U b o S q
      (coefficientDeckResidueMask U bW b hb q test)) ∧
    ∀ y, 0 ≤ allocatedMaskedCoefficientDensity B U b o S q
      (coefficientDeckResidueMask U bW b hb q test) y ∧
      allocatedMaskedCoefficientDensity B U b o S q
        (coefficientDeckResidueMask U bW b hb q test) y ≤
      allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice U) q y) := by
  let mask := coefficientDeckResidueMask U bW b hb q test
  have hm : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1 := fun r => htest _
  refine ⟨?_, ?_⟩
  · exact (allocatedMaskedCoefficientDensity_continuous B U b o S C V hC hV hR hσ q mask hm).measurable
  · exact allocatedMaskedCoefficientDensity_le_density B U b o S C V hC hV hb hR hσ hσ1
      Cinv hCinv hchart hsmall q mask hm

include hC hV ν in
theorem allocatedMaskedCoefficientDensity_haar_integral
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) [NeZero q]
    (test : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → ℝ)
    (htest : ∀ r, test r ∈ Set.Icc (0 : ℝ) 1) :
    (∫ y, allocatedMaskedCoefficientDensity B U b o S q
      (coefficientDeckResidueMask U bW b hb q test) y ∂μ) =
    ∫ p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
        CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q,
      test (coefficientSamplerChartResidues q p.1 p.2)
      ∂(allocatedCoefficientSource B U b hR hσ S).prod
        (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q)).toMeasure := by
  have hdata := allocatedMaskedCoefficientDensity_haar_data B U bW b hb o S C V hC hV
    hR hσ hσ1 Cinv hCinv hchart hsmall q test htest
  have hdm := (allocatedCoefficientDensity_spec B U b hb o hR hσ S hσ1
    Cinv hCinv hchart hsmall μ ν).1
  have hlaw := allocatedCoefficientDeckSample_density_law_s2 B U b hR hσ S E hb o bW q μ ν
    hσ1 Cinv hCinv hchart hsmall
  have hae := allocatedMaskedCoefficientDensity_sample_ae_s2 B U bW b hb o S hR hσ hσ1
    Cinv hCinv hchart hsmall q test
  have hresult := CoefficientDeckDensityLaw.masked_integral (K := LayerSamplerVariables G I n B)
    U bW b hb o μ (allocatedCoefficientSource B U b hR hσ S)
    (allocatedCoefficientDensity B U b hb o hR hσ S) q hlaw hdm
    (allocatedMaskedCoefficientDensity B U b o S q (coefficientDeckResidueMask U bW b hb q test))
    hdata.1 (fun y => (hdata.2 y).1) (fun y => (hdata.2 y).2)
    (fun p => test (coefficientSamplerChartResidues q p.1 p.2))
    (by simpa only [allocatedUniformPMF_fintype_transport] using hae)
  simpa only [allocatedUniformPMF_fintype_transport] using hresult

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSpatialWitnessComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in

theorem exists_allocated_spatial_witness_comparison_s2_oai
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) [NeZero q] (hq : 0 < q)
    {P δ : ℝ} (hP : 0 ≤ P) (hmP : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hqP : (q : ℝ) ≤ Real.exp P) (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {X : Type} [Fintype X] [DecidableEq X]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {Ps ε ρ Rs Smax : ℝ} (hPs : 0 ≤ Ps) (hX : (Fintype.card X : ℝ) ≤ Ps)
    (hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Ps)
    (hqPs : (q : ℝ) ≤ Real.exp Ps)
    (hε : 0 < ε) (hρ : 0 < ρ) (hεPs : 1 / ε ≤ Real.exp Ps) (hρPs : 1 / ρ ≤ Real.exp Ps)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (hSmax : 0 ≤ Smax) (hSmaxPs : Smax ≤ Real.exp Ps) (hstrideMax : ∀ x, ((stride x * q : ℕ) : ℝ) ≤ Smax)
    (H : X → ℝ)
    (hsize : ∀ x, Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (hcells : cells.Nonempty)
    (event : ((Option (LayerSamplerVariables G I n B) × X) → ZMod q) →
      CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop)
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)
    (hfreqPs : (4 * allocatedFourierLogBudget m P + 2)^4 ≤ Ps)
    (hmassPs : 4 * allocatedFourierLogBudget m P * (4 * allocatedFourierLogBudget m P + 2)^4 +
      allocatedFourierLogBudget m P ≤ Ps)
    (hsmallError : 2 * δ + ε ≤ 1 / 2) :
    let Dphysical := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      allocatedCoefficientDensity B U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    let sample := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      affineCoefficientCoverSample U poly hm q (fun k x => (z (k, x) : ℝ))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 2 * δ + ε ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      |(∑' z, (selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal *
          (if coefficientDeckChartEvent U bW b hb o q (event (fun v => (z v : ZMod q))) (sample z) then 1 else 0)) -
        ∑' z, (selectedResidueSmoothPMF stride cells width hwidth hZ z).toReal *
          ∫ p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
              CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q,
            (if event (fun v => (z v : ZMod q)) (coefficientSamplerChartResidues q p.1 p.2) then (1 : ℝ) else 0)
            ∂(allocatedCoefficientSource B U b hR hσ S).prod
              (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q)).toMeasure| ≤
        12 * (2 * δ + ε) := by
  dsimp only
  obtain ⟨hD0, hZ, hDpos, hmass, hlower, hupper, he⟩ :=
    exists_allocated_spatial_chart_event_comparison_s2 B U bW b hb o S C V hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall q hq hP hmP hK hRP hσP hcount hI hn hJ hAP hLP
      hCP hVP hqP hδ hδP μ ν poly hp hm hPs hX hframe hqPs hε hρ hεPs hρPs stride hstride
      hSmax hSmaxPs hstrideMax H hsize hrank hRs cells hcells event width hwidth hwide
      hfreqPs hmassPs hsmallError
  have hhaar (r) := allocatedMaskedCoefficientDensity_haar_integral B U bW b hb o S C V hC hV μ ν
    hR hσ hσ1 Cinv hCinv hchart hsmall q
    (fun a => if event r a then (1 : ℝ) else 0)
    (fun a => by split_ifs <;> constructor <;> norm_num)
  simp_rw [hhaar] at he
  exact ⟨hD0, hZ, hDpos, hmass, hlower, hupper, he⟩

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocated_spatial_witness_comparison_s2_oai := @OAI.Erdos3.VectorPolynomial.exists_allocated_spatial_witness_comparison_s2_oai
