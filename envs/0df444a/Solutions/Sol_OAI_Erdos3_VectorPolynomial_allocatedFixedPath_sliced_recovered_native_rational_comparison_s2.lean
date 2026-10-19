-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_recovered_native_rational_comparison_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:44:29.859806+00:00
-- url     : https://prove2.me/submissions/d7c29be6-673f-4990-a8cf-f30e3240807b

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B236
import Definitions.Def_OAIE3v2B254
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPath_sliced_physical_rational_density_comparison_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPath_sliced_recovered_native_atom_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTest
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem complexMean_congr_support {f g : X → ℂ}
    (h : ∀ x, p.weight x ≠ 0 → f x = g x) : p.complexMean f = p.complexMean g := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : p.weight x = 0
  · simp only [hx, Complex.ofReal_zero, zero_mul]
  · rw [h x hx]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleQuadratureUniformBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

theorem allocatedShortIntegerSelection_small (a : AllocatedShortIntegerAxis U b L) :
    basisAxisScale (b (allocatedShortIntegerSelection U b L a).1)
      (allocatedShortIntegerSelection U b L a).2 ≤
      L ^ ((allocatedShortIntegerSelection U b L a).1.val + 1) := a.property

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastNativePullbackBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical NNReal BigOperators

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R : Fin m → ℝ)

theorem forecastNativeAmbientLinear_lipschitz :
    LipschitzWith (forecastNativeAmbientLip U b o R) (forecastNativeAmbientLinear U b o R) :=
  (forecastNativeAmbientLinear U b o R).toContinuousLinearMap.lipschitz

variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
local notation "Active" => {a : LayerSamplerAxis I n // ¬P a}
local notation "Output" => (Σ _a : Active, Unit)

theorem forecastNativeFillAxes_lipschitz (frozen : {a : LayerSamplerAxis I n // P a} → ℝ) :
    LipschitzWith 1 (forecastNativeFillAxes P frozen) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro a
  by_cases ha : P a
  · simp only [forecastNativeFillAxes, ha, ↓reduceDIte, dist_self, dist_nonneg]
  · simpa only [forecastNativeFillAxes, ha, ↓reduceDIte] using dist_le_pi_dist v w ⟨⟨a, ha⟩, ()⟩

variable {X : Type*} [Fintype X]
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Domain" => ((Spatial → ℝ) × (Output → ℝ))

theorem forecastNativeSpatialInverse_lipschitz (center : X → ℝ) (τ : ℝ) :
    LipschitzWith ‖τ / 8‖₊ (forecastNativeSpatialInverse center τ) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (mul_nonneg (norm_nonneg _) dist_nonneg)).mpr
  intro x
  change dist (center x + τ / 8 * z ⟨x, Sum.inl ()⟩)
    (center x + τ / 8 * w ⟨x, Sum.inl ()⟩) ≤ _
  rw [dist_add_left, dist_eq_norm, ← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left (dist_le_pi_dist z w _) (norm_nonneg _)

theorem forecastNativeTorusInverse_lipschitz (d : ℕ) [NeZero d]
    (deck : (Σ j, J j) → ZMod d)
    (frozen : {a : LayerSamplerAxis I n // P a} → ℝ) :
    LipschitzWith (forecastNativeAmbientLip U b o R)
      (forecastNativeTorusInverse U b o R P d deck frozen) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  have h := ((forecastNativeAmbientLinear_lipschitz U b o R).comp
    (forecastNativeFillAxes_lipschitz P frozen)).dist_le_mul v w
  simp only [mul_one] at h
  apply (dist_pi_le_iff (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)).mpr
  intro a
  rw [forecastNativeTorusInverse, forecastNativeTorusInverse, dist_add_right,
    dist_eq_norm, ← AddCircle.coe_sub]
  apply QuotientAddGroup.norm_mk_le_norm.trans
  rw [← sub_div, norm_div]
  have hd : (1 : ℝ) ≤ ‖(d : ℝ)‖ := by
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  exact (div_le_self (norm_nonneg _) hd).trans
    ((dist_le_pi_dist _ _ a).trans h)

namespace NormalizedPolynomialTwist

variable {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem forecastPullback_norm_le
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (deck : (Σ j, J j) → ZMod W.cover)
    (center : X → ℝ) (τ : ℝ) (frozen : {a : LayerSamplerAxis I n // P a} → ℝ)
    (y : Domain) : ‖W.forecastPullback U b o R P residue deck center τ frozen y‖ ≤ 1 := by
  unfold forecastPullback
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.mask_bound _)).trans (W.smooth_bound _)

theorem forecastPullback_lipschitz
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (deck : (Σ j, J j) → ZMod W.cover)
    (center : X → ℝ) (τ : ℝ) (frozen : {a : LayerSamplerAxis I n // P a} → ℝ) :
    LipschitzWith (L * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R))
      (W.forecastPullback U b o R P residue deck center τ frozen) := by
  let : NeZero W.cover := ⟨W.cover_pos.ne'⟩
  have hin := ((forecastNativeSpatialInverse_lipschitz center τ).comp LipschitzWith.prod_fst).prodMk
    ((forecastNativeTorusInverse_lipschitz U b o R P W.cover deck frozen).comp LipschitzWith.prod_snd)
  simp only [mul_one] at hin
  have h := W.smooth_lipschitz.comp hin
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [dist_eq_norm]
  change ‖W.mask residue * W.smooth _ - W.mask residue * W.smooth _‖ ≤ _
  rw [← mul_sub, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.mask_bound _)).trans
    (by simpa only [Function.comp_apply, dist_eq_norm] using h.dist_le_mul y z)

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastNativeResidueTest
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module
open scoped Classical NNReal
variable {m : ℕ} {X : Type*} [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (R : Fin m → ℝ) (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E P)

namespace NormalizedPolynomialTwist
variable {periodCap coverCap : ℝ} {L : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)

theorem forecastResidueTest_bounds (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (sheet : ∀ j, {i : Fin (n j) // P ⟨j, .inr i⟩} → ℤ)
    (frozen : {a : LayerSamplerAxis I n // P a} → ℝ)
    (center : X → ℝ) (τ : ℝ) (out : Out → ZMod q) :
    (∀ y, ‖W.forecastResidueTest U b hb o bW R P q hm hperiod hcover sheet frozen center τ out y‖ ≤ 1) ∧
      LipschitzWith (L * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R))
        (W.forecastResidueTest U b hb o bW R P q hm hperiod hcover sheet frozen center τ out) :=
  ⟨W.forecastPullback_norm_le U b o R P _ _ center τ frozen,
    W.forecastPullback_lipschitz U b o R P _ _ center τ frozen⟩

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastNativeJointTestBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module
open scoped Classical NNReal
variable {m : ℕ} {X : Type*} [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ)
local notation "short" => allocatedShortAxis (I := I) U b Lsize
local notation "Grid" => AllocatedShortIntegerAxis U b Lsize →
  ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ

variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (R : Fin m → ℝ)
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)

namespace NormalizedPolynomialTwist
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)

theorem forecastShortGridTest_bounds (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (center : X → ℝ) (τ : ℝ) (grid : Grid) (out : Out → ZMod q) :
    (∀ y, ‖W.forecastShortGridTest U b Lsize hb o bW R q hm hperiod hcover center τ grid out y‖ ≤ 1) ∧
      LipschitzWith (Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R))
        (W.forecastShortGridTest U b Lsize hb o bW R q hm hperiod hcover center τ grid out) :=
  W.forecastResidueTest_bounds U b hb o bW R short q hm hperiod hcover _ _ center τ out

end NormalizedPolynomialTwist

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedNativeAmbientComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {T : Type*} [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
local notation "selected" => allocatedShortIntegerSelection U basis S.value

attribute [local instance] OAI.Erdos3.VectorPolynomial.slicedNativeSourceMeanCoverNeZero
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
  (allocatedLayerWidths B U basis S j)
  (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable (base : X → ℤ) (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (box : X → ℕ) (hbox : ∀ a, 0 < box a) {τ : ℝ} (hτ : τ ≠ 0)
variable (q : ℕ) [NeZero q] (hm : 0 < m)
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
variable (hbase : canonicalCoefficientSample U basis hb o sample =
  affineSampleCoefficientTorus U nativePoly hmem
    (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
      integerFrame) (k, x) : ℝ)))
variable (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)
variable (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hread : ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E W.cover → Prop,
  coefficientDeckChartEvent U bW basis hb o W.cover event
    (affineCoefficientCoverSample U nativePoly hmem W.cover
      (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
        integerFrame) (k, x) : ℝ))) ↔
    event (allocatedReadCoefficientChartResidues (fun i => (read i : ZMod W.cover))))

variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)
variable (HG : G → ℕ) (hHG : ∀ g, 2 ≤ HG g) (cG : G → ℤ) (stepG : ℕ)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
  Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (S.value : ℤ))

include hs hbox hτ hdegree hbase hsmallChart hread in

theorem allocatedSlicedPhysicalSourceMean_eq_native :
    allocatedSlicedPhysicalSourceMean B U basis S HP stepP cP hinsideP hHP
      τ box integerFrame HG hHG cG stepG hcontainedG sample H c hH hsubset q selected base
      (allocatedReadDeck read) (allocatedOriginalSampleCongruenceProjection B U basis S sample)
      (W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
        (fun a => (base a : ℝ) / box a) τ) =
      allocatedSlicedNativeEvalMean B U basis S W base integerFrame box nativePoly
        HP stepP cP hinsideP hHP HG hHG cG stepG hcontainedG H c hH hsubset := by
  unfold allocatedSlicedPhysicalSourceMean allocatedSlicedNativeEvalMean
  apply FiniteProbabilityWeights.complexMean_congr_support
  intro u _
  apply FiniteProbabilityWeights.complexMean_congr_support
  intro x hx
  apply FiniteProbabilityWeights.complexMean_congr_support
  intro v hv
  exact allocatedFixedPath_sliced_recovered_native_atom_s2 B U basis hR hσ S hb o bW W
    sample hs base integerFrame box hbox hτ q hm hperiod hcover nativePoly hmem hdegree
    hbase hsmallChart read hread HG
    (fun g => lt_of_lt_of_le (by decide : 0 < 2) (hHG g)) cG stepG hcontainedG
    (fun _ => stepG) H c (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset u x hx v hv

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype T] [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "Ncrt" => (∏ l, primes l ^ exponent l)
local instance slicedRecoveredNativeCRTNeZero_rc7cc9a_1 : NeZero Ncrt :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (primes l)))⟩
variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)

variable (τ ξ : ℝ)
variable (hτ : 0 < τ)
variable (hξ : 0 < ξ)
variable (box : X → ℕ)
variable (hbox : ∀ x, 0 < box x)
variable (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) τ ξ box) 1)
variable (HG : G → ℕ)
variable (hHG : ∀ g, 2 ≤ HG g)
variable (cG : G → ℤ)
variable (stepG : ℕ)
variable (hstepG : 0 < stepG)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (e : G ≃ X ⊕ (X ⊕ T))
variable (h0 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (sample : (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n))
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable {t : ℝ}
variable (ht : 0 < t)
variable (hσbound : ∀ j, |σ j| ≤ t)
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable {δ : ℝ}
variable (hδ : 0 < δ)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ))
variable (q : ℕ)
variable [NeZero q]
variable (hsizeG : ∀ g, q ≤ HG g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1)
variable (hsize : ∀ j, q ≤ H j)
variable (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
variable {ε : ℝ}
variable (hε : 0 ≤ ε)
variable (hmesh : ∀ _j : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)), (stepG : ℝ) / S.value ≤ ε)
variable (hδone : δ ≤ 1)
variable (b : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val)
variable {η : ℝ}
variable (hη : 0 < η)
variable (A : ℝ≥0)
variable (hA : LipschitzWith A Real.smoothTransition)
variable (htail : |t| * polynomialMassC2Budget (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (hm : 0 < m) (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable (base : X → ℤ)
variable (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hp : ∀ l, (primes l).Prime)
variable (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
variable (hqN : q ∣ (∏ l, primes l ^ exponent l))
variable {gridVolume : ℝ} (hV : gridVolume ≠ 0)

local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "nativeTest" => W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
  (fun a => (base a : ℝ) / box a) τ
local notation "Knative" => Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
local notation "actualDensity" => allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box
  integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c
local notation "projection" => allocatedOriginalSampleCongruenceProjection B U basis S sample
local notation "sourceMean" => allocatedSlicedPhysicalSourceMean B U basis S HP stepP cP hinsideP hHP
  τ box integerFrame HG hHG cG stepG hcontainedG sample H c hH hsubset q selected base
  (allocatedReadDeck read) projection nativeTest
local notation "rationalReference" => allocatedSlicedPhysicalRationalMean B U basis S primes exponent
  HP stepP cP hinsideP hHP integerFrame cG stepG sample c q selected xref base
  (allocatedReadDeck read) projection hcoprime hqN (gridVolume := gridVolume) nativeTest actualDensity
local notation "comparisonError" => allocatedSlicedPhysicalComparisonError B U basis S ξ HG
  (t := t) H q (ε := ε) (η := η) (Kφ := Knative)

include hR hσ hs ht hσbound hδ hsubset hdense hsizeG hsmallG hsize hsmall hε hmesh
  hδone b hη hA htail hp hV hτ hξ hbox hframe in
theorem allocatedFixedPath_sliced_native_test_rational_comparison :
    ‖sourceMean - rationalReference‖ ≤ comparisonError := by
  have htest := W.forecastShortGridTest_bounds U basis S.value hb o bW R q hm hperiod hcover
    (fun a => (base a : ℝ) / box a) τ
  exact allocatedFixedPath_sliced_physical_rational_density_comparison_s2 B U basis hR hσ S primes exponent
    HP stepP cP hinsideP hHP τ ξ hτ hξ box hbox integerFrame hframe HG hHG cG stepG hstepG
    hcontainedG e h0 h1 hB sample hs ht hσbound H c hH hδ hsubset hdense q hsizeG hsmallG
    hsize hsmall hε hmesh hδone b hη A hA htail selected
    (allocatedShortIntegerSelection_small U basis S.value) xref base (allocatedReadDeck read)
    projection hp hcoprime hqN hV nativeTest (fun grid residue => (htest grid residue).2)
    (fun grid residue => (htest grid residue).1)

attribute [local instance] OAI.Erdos3.VectorPolynomial.slicedNativeRecoveredCoverNeZero
variable (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
variable (hbase : canonicalCoefficientSample U basis hb o sample =
  affineSampleCoefficientTorus U nativePoly hmem
    (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
      integerFrame) (k, x) : ℝ)))
variable (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)
variable (hread : ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E W.cover → Prop,
  coefficientDeckChartEvent U bW basis hb o W.cover event
    (affineCoefficientCoverSample U nativePoly hmem W.cover
      (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
        integerFrame) (k, x) : ℝ))) ↔
    event (allocatedReadCoefficientChartResidues (fun i => (read i : ZMod W.cover))))

include hR hσ hs ht hσbound hδ hsubset hdense hsizeG hsmallG hsize hsmall hε hmesh
  hδone b hη hA htail hp hV hτ hξ hbox hframe hmem hdegree hbase hsmallChart hread in

theorem allocatedFixedPath_sliced_recovered_native_rational_comparison_s2_oai :
    ‖allocatedSlicedNativeEvalMean B U basis S W base integerFrame box nativePoly
        HP stepP cP hinsideP hHP HG hHG cG stepG hcontainedG H c hH hsubset -
      rationalReference‖ ≤ comparisonError := by
  have he := allocatedFixedPath_sliced_native_test_rational_comparison B U basis hR hσ S
    primes exponent HP stepP cP hinsideP hHP τ ξ hτ hξ box hbox integerFrame hframe HG hHG cG
    stepG hstepG hcontainedG e h0 h1 hB sample hs ht hσbound H c hH hδ hsubset hdense q
    hsizeG hsmallG hsize hsmall hε hmesh hδone b hη A hA htail hb o bW W hm hperiod hcover
    xref base read hp hcoprime hqN hV
  rw [allocatedSlicedPhysicalSourceMean_eq_native B U basis hR hσ S hb o bW W sample hs
    base integerFrame box hbox hτ.ne' q hm hperiod hcover nativePoly hmem hdegree
    hbase hsmallChart read hread HP stepP cP hinsideP hHP HG hHG cG stepG hcontainedG
    H c hH hsubset] at he
  exact he

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_recovered_native_rational_comparison_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8} := @OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_recovered_native_rational_comparison_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8}
