-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.forecastLawNativeHaarMean_eq_jointMean
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-13T03:32:38.179221+00:00
-- url     : https://prove2.me/submissions/694f114e-8de0-44c8-9a00-30f1c6cb5a33
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B181
import Definitions.Def_OAIErdos3B185
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastLawDensityPhysicalChartSource_haar_integral_unrestricted
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastLawDensityPhysicalChartSource_integrable
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastLawNativeRawSum_eq_jointMean

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedCoveredChart
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped Classical

variable {D R : Type*} [Fintype D] [Fintype R] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (bW : Basis R ℤ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup)
variable (d : ℕ) [NeZero d]

theorem normalizedCoveredChart_continuous :
    Continuous (normalizedCoveredChart W b hb bW d) := by
  have hk : Continuous (fun r : R → ZMod d =>
      (coverKernelBasisEquiv (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
        bW d (Nat.pos_of_ne_zero (NeZero.ne d)) r).val) := continuous_of_discreteTopology
  exact ((normalizedCoverLift_continuous W b hb d).comp continuous_fst).add
    (hk.comp continuous_snd)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoveredJetChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {O J B : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem coveredJetChart_continuous : Continuous (coveredJetChart (O := O) U b hb bW d) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro t
  exact (normalizedCoveredChart_continuous _ (b j) (hb j) (bW j) d).comp
    ((continuous_apply t).comp (continuous_apply j))

variable [∀ j, Fintype (O j)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CoveredJetSampler
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped Classical Matrix

namespace VectorPolynomial

variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem mixedCoveredJetCoordinates_measurable (d : ℕ) :
    Measurable (mixedCoveredJetCoordinates (O := O) (B := B) (n := n) U o d) := by
  apply measurable_pi_iff.mpr
  intro j
  apply measurable_pi_iff.mpr
  intro t
  exact ((orthonormalMixedChart (o j)).measurable.comp
    (((measurable_pi_apply t).comp (mixedArrayRegroup _ _ _).measurable).comp
      ((measurable_pi_apply j).comp measurable_fst))).prodMk
    ((measurable_pi_apply t).comp ((measurable_pi_apply j).comp measurable_snd))

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)

variable [∀ j, Fintype (B j)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

variable [∀ j, Fintype (O j)]

end VectorPolynomial

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativePhysicalHaarExpansion
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset (Fin q))

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3
open scoped NNReal

namespace VectorPolynomial
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped BigOperators Classical NNReal

variable {X : Type*} {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open scoped BigOperators Classical NNReal

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable {pw cw pv cv : ℝ} {Lw Lv : ℝ≥0}

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped Classical NNReal

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [CompactSpace (CoefficientTorus (K := Fin q) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
variable [BorelSpace (CoefficientTorus (K := Fin q) U)]
variable (μ : Measure (CoefficientTorus (K := Fin q) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "Row" => (fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (Fin.val j + 1)})
local notation "rows" => (fun j => (Subtype.val : Row j → Finset (Fin q)))

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped Classical BigOperators NNReal

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {X : Type*} [Fintype X] {pw cw : ℝ} {Lw : ℝ≥0}

theorem nativeSingleSiteCoverObservable_continuous
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (physicalN : X → ℕ) (u : X → ℤ) (Q : ℕ) :
    Continuous (nativeSingleSiteCoverObservable U W physicalN u Q) := by
  apply (W.frozenTorus_lipschitz _ _).continuous.comp
  apply continuous_pi
  intro a
  exact (continuous_apply (⟨a.1, (), a.2⟩ : JetAmbientIndex (fun _ => Unit) J)).comp
    (coveredJetAmbientTorus_continuous U (Q / W.cover))

theorem norm_nativeSingleSiteCoverObservable_le
    (W : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
    (physicalN : X → ℕ) (u : X → ℤ) (Q : ℕ)
    (y : EuclideanJetLayers U (fun _ => Unit)) :
    ‖nativeSingleSiteCoverObservable U W physicalN u Q y‖ ≤ 1 :=
  W.norm_frozenTorus_le _ _ _

variable [CompactSpace (EuclideanJetLayers U (fun _ => Unit))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedOriginalForecastSpatialIntegral
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem translatedForecastSpatialPoint_mem_integerBox
    {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) (hN : ∀ i, 0 < N i) {τ : ℝ} (hτ : 0 < τ)
    (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (base : X → ℤ) (hbase : base ∈ trimmedIntegerBox N (spatialTrimMargin τ N))
    (u : X → ℤ)
    (hsupport : ∀ i, |((u i : ℝ) - base i) / (τ * N i / 8)| ≤ 2) :
    u ∈ integerBox N := by
  have hdelta (i : X) : |(u - base) i| ≤ (spatialTrimMargin τ N i : ℤ) := by
    have hNi : 0 < (N i : ℝ) := by exact_mod_cast hN i
    have hscale : 0 < τ * (N i : ℝ) / 8 := by positivity
    have habs : |(u i : ℝ) - base i| ≤ τ * N i / 4 := by
      have h := hsupport i
      rw [abs_div, abs_of_pos hscale] at h
      have h' := (div_le_iff₀ hscale).mp h
      linarith
    have hceil : τ * (N i : ℝ) / 4 ≤ (spatialTrimMargin τ N i : ℝ) := Nat.le_ceil _
    have hr : |((u - base) i : ℝ)| ≤ (spatialTrimMargin τ N i : ℝ) := by
      simpa only [Pi.sub_apply, Int.cast_sub] using habs.trans hceil
    exact_mod_cast hr
  have h := trimmedIntegerBox_add_mem N (spatialTrimMargin τ N) hmargin hbase (u - base) hdelta
  simpa only [add_sub_cancel] using h

theorem translatedForecastDensity_zero_outside_integerBox
    {X Y : Type*} [Fintype X] [DecidableEq X]
    (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) × Y) → ℝ)
    (hsupport : ∀ z, density z ≠ 0 → ∀ i : X, |z.1 ⟨i, .inl ()⟩| ≤ 2)
    (N : X → ℕ) (hN : ∀ i, 0 < N i) {τ : ℝ} (hτ : 0 < τ)
    (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (base : X → ℤ) (hbase : base ∈ trimmedIntegerBox N (spatialTrimMargin τ N))
    (u : X → ℤ) (y : Y) (hu : u ∉ integerBox N) :
    density ((fun a => ((u a.1 : ℝ) - base a.1) / (τ * N a.1 / 8)), y) = 0 := by
  by_contra hn
  apply hu
  exact translatedForecastSpatialPoint_mem_integerBox N hN hτ hmargin base hbase u
    (hsupport _ hn)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)

variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

variable [DecidableEq X]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3
open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical Matrix

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)

variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

variable [∀ a, DecidableEq (B a)] [DecidableEq X]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastJointScaleNormalization
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {X : Type*} [Fintype X]

theorem forecastJointGridScale_prod (R : Fin m → ℝ) (L : ℕ)
    (physicalN : X → ℕ) (τ : ℝ) :
    (∏ j, forecastJointGridScale U basis R L physicalN τ j) =
      (τ / 8) ^ Fintype.card X * (∏ i, (physicalN i : ℝ)) *
        ∏ a, allocatedActiveIntegerGridScale U basis R L a := by
  rw [Fintype.prod_sum_type]
  change (∏ i : X, τ * physicalN i / 8) * _ = _
  have hterm (i : X) : τ * physicalN i / 8 = (τ / 8) * physicalN i := by ring
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rfl

theorem forecastJointGridScale_prod_eq_card [DecidableEq X]
    (R : Fin m → ℝ) (L : ℕ) (physicalN : X → ℕ) (τ : ℝ) :
    (∏ j, forecastJointGridScale U basis R L physicalN τ j) =
      (τ / 8) ^ Fintype.card X * (integerBox physicalN).card *
        ∏ a, allocatedActiveIntegerGridScale U basis R L a := by
  rw [forecastJointGridScale_prod, card_integerBox, Nat.cast_prod]

theorem forecastJointGridScale_prod_div_card [DecidableEq X]
    (R : Fin m → ℝ) (L : ℕ) (physicalN : X → ℕ) (τ : ℝ)
    (hN : ∀ i, 0 < physicalN i) :
    (∏ j, forecastJointGridScale U basis R L physicalN τ j) / (integerBox physicalN).card =
      (τ / 8) ^ Fintype.card X * ∏ a, allocatedActiveIntegerGridScale U basis R L a := by
  have hc : ((integerBox physicalN).card : ℝ) ≠ 0 := by
    rw [card_integerBox, Nat.cast_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast (hN i).ne')
  rw [forecastJointGridScale_prod_eq_card]
  field_simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {X : Type*} [Fintype X]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} [Fintype X]
variable {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

 theorem forecastGeometricJacobian_cancel {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    (L : ℕ) {gridVolume τ : ℝ} (hgrid : 0 < gridVolume) (hτ : 0 < τ) :
    forecastGeometricJacobian (X := X) (I := I) U basis R L gridVolume τ *
      (coveredJetArrayScale (O := fun _ : Fin m => Unit) U * gridVolume *
        (τ / 8) ^ Fintype.card X * (∏ a : Σ j, I j, R a.1) *
        (∏ a, allocatedActiveIntegerGridScale U basis R L a)) = 1 := by
  have hp := forecastGeometricJacobian_pos (X := X) (I := I) U basis hR L hgrid hτ
  unfold forecastGeometricJacobian at hp ⊢
  exact inv_mul_cancel₀ (inv_pos.mp hp).ne'

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
variable {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem forecastJointScale_normalization {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    (L : ℕ) (physicalN : X → ℕ) (hN : ∀ x, 0 < physicalN x)
    {gridVolume τ : ℝ} (hgrid : 0 < gridVolume) (hτ : 0 < τ) :
    forecastGeometricJacobian (X := X) (I := I) U basis R L gridVolume τ *
      coveredJetArrayScale (O := fun _ : Fin m => Unit) U *
      (∏ a : Σ j, I j, R a.1) * gridVolume *
      (∏ j, forecastJointGridScale U basis R L physicalN τ j) /
      (integerBox physicalN).card = 1 := by
  rw [mul_div_assoc, forecastJointGridScale_prod_div_card U basis R L physicalN τ hN]
  convert forecastGeometricJacobian_cancel (X := X) (I := I) U basis hR L hgrid hτ using 1; ring

theorem forecastJointScale_complex_normalization {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    (L : ℕ) (physicalN : X → ℕ) (hN : ∀ x, 0 < physicalN x)
    {gridVolume τ : ℝ} (hgrid : 0 < gridVolume) (hτ : 0 < τ) :
    (forecastGeometricJacobian (X := X) (I := I) U basis R L gridVolume τ : ℂ) *
      (coveredJetArrayScale (O := fun _ : Fin m => Unit) U : ℂ) *
      ((∏ a : Σ j, I j, R a.1) : ℂ) * (gridVolume : ℂ) *
      ((∏ j, forecastJointGridScale U basis R L physicalN τ j) : ℂ) /
      ((integerBox physicalN).card : ℂ) = 1 := by
  exact_mod_cast forecastJointScale_normalization U basis hR L physicalN hN hgrid hτ

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastNativeRawSpatialFamily
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))


variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}

theorem forecastNativeRawMean_normalization
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
      (euclideanSubspace (U j)))]
    (hR : ∀ j, 0 < R j) (hN : ∀ x, 0 < physicalN x)
    (hV : 0 < volume) (hτ : 0 < τ) (rawSum jointMean : ℂ)
    (hraw : rawSum = ((∏ a : Σ j, I j, R a.1 : ℝ) : ℂ) *
      ((volume : ℂ) *
        ((∏ j, forecastJointGridScale U basis R S.value physicalN τ j : ℝ) : ℂ) *
        jointMean)) :
    ((forecastGeometricJacobian (X := X) (I := I) U basis R S.value volume τ : ℂ) *
      (coveredJetArrayScale (O := single) U : ℂ) /
      ((integerBox physicalN).card : ℂ)) * rawSum = jointMean := by
  rw [hraw]
  have hn := forecastJointScale_complex_normalization (I := I) U basis hR S.value
    physicalN hN hV hτ
  calc
    _ = ((forecastGeometricJacobian (X := X) (I := I) U basis R S.value volume τ : ℂ) *
      (coveredJetArrayScale (O := single) U : ℂ) *
      ((∏ a : Σ j, I j, R a.1 : ℝ) : ℂ) * (volume : ℂ) *
      ((∏ j, forecastJointGridScale U basis R S.value physicalN τ j : ℝ) : ℂ) /
      ((integerBox physicalN).card : ℂ)) * jointMean := by ring
    _ = jointMean := by rw [Complex.ofReal_prod, Complex.ofReal_prod, hn, one_mul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "law" => principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))


variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {pw cw : ℝ} {Lw : ℝ≥0}
variable (Wtest : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)

section OriginalDensity

variable [DecidableEq X] [∀ a, DecidableEq (B a)]
variable {Zsp : Type*} [Fintype Zsp] [DecidableEq Zsp]
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {Wgeo Lgeo : ℝ} (hW : 0 ≤ Wgeo) (hL : 0 < Lgeo)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

end OriginalDensity

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawOriginalNativeHaarJointMean
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "chart" => mixedCoveredJetChart (O := single) U o basis hb bW N

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

local notation "chartSource" => forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
  active Y N volume base physicalN τ

theorem forecastLawDensityPhysicalChartSource_mul_test_integrable
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (hexhaustive : ∀ a, short a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a)
    (hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hdensity : Continuous density) (u : X → ℤ)
    (test : EuclideanJetLayers U single → ℂ) (htest : Measurable test)
    {testCap : ℝ} (hbound : ∀ y, ‖test y‖ ≤ testCap) :
    Integrable (fun z => chartSource u z * test (mixedCoveredJetChart U o basis hb bW N z))
      (mixedCoveredJetRawReference (I := I) (O := single) (E := Eout) (n := n) N) := by
  have hsource := forecastLawDensityPhysicalChartSource_integrable B U basis S law density selected sample x
    active Y N volume base physicalN τ o hR hσ hs hσ1 hexhaustive hactive r hr hr3 hradius
    C hC hchart hbudget hdensity u
  have hm : Measurable (mixedCoveredJetChart (O := single) U o basis hb bW N) :=
    (coveredJetChart_continuous (O := single) U basis hb bW N).measurable.comp
      (mixedCoveredJetCoordinates_measurable (O := single) (B := Eout) (n := n) U o N)
  exact hsource.mul_bdd (htest.comp hm).aestronglyMeasurable
    (ae_of_all _ (fun z => hbound _))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chartSource" => forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
  active Y N volume base physicalN τ

variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}

theorem forecastLawNativeHaarMean_eq_rawSum
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
      (euclideanSubspace (U j)))]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hdensity : Continuous density) (κ : ℂ) :
    let chart := mixedCoveredJetChart (O := single) U o basis hb bW N
    κ * (𝔼 u ∈ integerBox physicalN,
      ∫ y, restrictedComplexChartDensity chart region 1 (chartSource u) y *
        nativeSingleSiteCoverObservable U W physicalN u N y
        ∂Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))) =
      (κ * (coveredJetArrayScale (O := single) U : ℂ) /
        ((integerBox physicalN).card : ℂ)) *
      ∑ u ∈ integerBox physicalN,
        ∫ z, chartSource u z * nativeSingleSiteCoverObservable U W physicalN u N (chart z)
          ∂mixedCoveredJetRawReference (I := I) (O := single) (E := Eout) (n := n) N := by
  intro chart
  have hexhaustive : ∀ a, short a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a := by
    intro a ha
    obtain ⟨i, hi⟩ := (allocatedShortIntegerAxisEquiv (I := I) U basis S.value).surjective ⟨a, ha⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  have hpoint (u : X → ℤ) :=
    forecastLawDensityPhysicalChartSource_haar_integral_unrestricted B U basis S law density selected
      sample x active Y N volume base physicalN τ o hR hσ hs hσ1 hexhaustive hactive
      r hr hr3 hradius C hC hchart hbudget hb bW ν hdensity.measurable u
      (nativeSingleSiteCoverObservable U W physicalN u N)
      (nativeSingleSiteCoverObservable_continuous U W physicalN u N).measurable
  rw [Finset.expect_eq_sum_div_card]
  calc
    _ = κ * ((∑ u ∈ integerBox physicalN,
        (coveredJetArrayScale (O := single) U : ℂ) *
        ∫ z, chartSource u z * nativeSingleSiteCoverObservable U W physicalN u N (chart z)
          ∂mixedCoveredJetRawReference (I := I) (O := single) (E := Eout) (n := n) N) /
        ((integerBox physicalN).card : ℂ)) := by
      congr 2
      apply Finset.sum_congr rfl
      intro u hu
      exact hpoint u
    _ = _ := by rw [← Finset.mul_sum]; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))


variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {pw cw : ℝ} {Lw : ℝ≥0}
variable (Wtest : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := single) (E := Eout) (n := n) N

omit [∀ j, Fintype (I j)] in
theorem allShortSelection_exhaustive_p0 (T : ℕ) :
    ∀ a : LayerSamplerAxis I n, allocatedShortAxis U basis T a →
      ∃ i : AllocatedShortIntegerAxis U basis T,
      (⟨i.val.1, Sum.inr i.val.2⟩ : LayerSamplerAxis I n) = a := by
  rintro ⟨j, i | i⟩ ha
  · exact False.elim ha
  · exact ⟨⟨⟨j, i⟩, ha⟩, rfl⟩

theorem forecastLawNativeRawSpatialFamily_integrable
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a : AllocatedShortIntegerAxis U basis S.value, σ a.val.1 ≤ 1)
    (hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (hdensity : Continuous density) (u : X → ℤ) :
    Integrable (forecastLawNativeRawSpatialFamily B U basis S law density sample x active Y N volume
      base physicalN τ o hb bW Wtest u) raw := by
  exact forecastLawDensityPhysicalChartSource_mul_test_integrable B U basis S law density selected
    sample x active Y N volume base physicalN τ o hR hσ hs hσ1
    (allShortSelection_exhaustive_p0 (I := I) U basis S.value) hactive r hr hr3 hradius
    C hC hchart hbudget hb bW hdensity u
    (nativeSingleSiteCoverObservable U Wtest physicalN u N)
    (nativeSingleSiteCoverObservable_continuous U Wtest physicalN u N).measurable
    (norm_nativeSingleSiteCoverObservable_le U Wtest physicalN u N)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

local notation "chartSource" => forecastLawDensityPhysicalChartSource B U basis S law density selected sample x
  active Y N volume base physicalN τ

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {pw cw : ℝ} {Lw : ℝ≥0}
variable (Wtest : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := single) (E := Eout) (n := n) N
local notation "RawSource" => MixedCoveredJetSource I single Eout n N

variable [DecidableEq X]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "chart" => mixedCoveredJetChart (O := single) U o basis hb bW N
local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))

theorem forecastLawNativeHaarMean_eq_jointMean
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a : AllocatedShortIntegerAxis U basis S.value, σ a.val.1 ≤ 1)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (hdensity : Continuous density)
    (hsupport : ∀ y, 2 < ‖y‖ → density y = 0)
    (hN : ∀ i, 0 < physicalN i) (hτ : 0 < τ)
    (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
    (hbase : base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))
    (q : ℕ) [NeZero q] (hq : q ∣ N) (hm : 0 < m)
    (hperiod : Wtest.modulus ∣ q) (hcover : Wtest.cover ∣ q) (hV : 0 < volume) :
    (forecastGeometricJacobian (X := X) (I := I) U basis R S.value volume τ : ℂ) *
      (𝔼 u ∈ integerBox physicalN,
        ∫ y, restrictedComplexChartDensity chart region 1 (chartSource u) y *
          nativeSingleSiteCoverObservable U Wtest physicalN u N y ∂haar) =
        forecastJointOriginalGridMean U basis S.value hm law active
          (forecastInactiveFixedOutput B U basis S selected
            (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
          Y N q hq volume density
          (Wtest.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
            (fun x => (base x : ℝ) / physicalN x) τ)
          (fun j => (forecastJointGridCenter U basis S.value base j : ℝ))
          (forecastJointGridScale U basis R S.value physicalN τ) := by
  have hbox : @integerBox X inferInstance (Classical.decEq X) physicalN = integerBox physicalN := by
    ext u
    simp only [mem_integerBox]
  have hnorm (y) (hy : density y ≠ 0) : ‖y‖ ≤ 2 :=
    le_of_not_gt (fun h => hy (hsupport y h))
  have hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3 := by
    intro y hy a
    have hc : |y.2 a| ≤ ‖y.2‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm y.2 a
    exact (hc.trans ((le_max_right ‖y.1‖ ‖y.2‖).trans (hnorm y hy))).trans (by norm_num)
  have hspatial : ∀ y, density y ≠ 0 → ∀ i : X, |y.1 ⟨i, .inl ()⟩| ≤ 2 := by
    intro y hy i
    have hc : |y.1 ⟨i, .inl ()⟩| ≤ ‖y.1‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm y.1 ⟨i, .inl ()⟩
    exact hc.trans ((le_max_left ‖y.1‖ ‖y.2‖).trans (hnorm y hy))
  have hf (u : X → ℤ) : Integrable (fun z => chartSource u z *
      nativeSingleSiteCoverObservable U Wtest physicalN u N (chart z)) raw :=
    forecastLawNativeRawSpatialFamily_integrable B U basis S law density sample x active Y N volume
      base physicalN τ o hb bW Wtest hR hσ hs hσ1 hactive r hr hr3 hradius
      C hC hchart hbudget hdensity u
  have hzero (u : X → ℤ) (hu : u ∉ integerBox physicalN) (z : RawSource) :
      chartSource u z * nativeSingleSiteCoverObservable U Wtest physicalN u N (chart z) = 0 := by
    unfold forecastLawDensityPhysicalChartSource forecastLawDensityPhysicalDeckSource
    rw [translatedForecastDensity_zero_outside_integerBox density hspatial physicalN hN hτ
      hmargin base hbase u _ hu, Complex.ofReal_zero, zero_mul, zero_mul]
  have hhaar := forecastLawNativeHaarMean_eq_rawSum B U basis S law density sample x active Y N volume
    base physicalN τ o Wtest hR hσ hs hσ1 hactive r hr hr3 hradius C hC hchart hbudget
    hb bW ν hdensity
    (forecastGeometricJacobian (X := X) (I := I) U basis R S.value volume τ : ℂ)
  have hraw := forecastLawNativeRawSum_eq_jointMean U basis B S law density sample x active Y N volume
    base physicalN τ hb o bW Wtest hR q hq hm hperiod hcover hN hτ hV.ne'
    (fun u _ => hf u) (fun u hu z => hzero u (by simpa only [hbox] using hu) z)
  simpa only [hbox] using hhaar.trans (forecastNativeRawMean_normalization (B := B) (U := U) (basis := basis) (S := S)
    (volume := volume) (physicalN := physicalN) (τ := τ) hR hN hV hτ _ _ hraw)

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.forecastLawNativeHaarMean_eq_jointMean.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.forecastLawNativeHaarMean_eq_jointMean.{u_1, u_2, u_3, u_4, u_5, u_6, u_7}
