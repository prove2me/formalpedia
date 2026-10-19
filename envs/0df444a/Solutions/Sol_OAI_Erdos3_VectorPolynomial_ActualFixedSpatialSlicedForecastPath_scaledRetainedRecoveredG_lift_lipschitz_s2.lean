-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.scaledRetainedRecoveredG_lift_lipschitz_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:00:13.76028+00:00
-- url     : https://prove2.me/submissions/8aa0a513-5650-439b-9f70-2d8cb2cf31d5

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B247
import Definitions.Def_OAIE3v2B303

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedFullSiteSupport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

theorem allocatedFullAmbientSiteCoordinates_lipschitz (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ≥0)
    (hC : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ C j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) :
    LipschitzWith (K * ∑ j, C j * Fintype.card (J j))
      (allocatedFullAmbientSiteCoordinates (R := R) U b o) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  intro a
  let pz := mixedRealCoordinates (euclideanSubspace (U a.1)) (b a.1) (o a.1)
    ((EuclideanSpace.equiv (J a.1) ℝ).symm (fun k => z ⟨a.1, (), k⟩))
  let pw := mixedRealCoordinates (euclideanSubspace (U a.1)) (b a.1) (o a.1)
    ((EuclideanSpace.equiv (J a.1) ℝ).symm (fun k => w ⟨a.1, (), k⟩))
  have hout : dist (Sum.elim pz.1 pz.2 a.2) (Sum.elim pw.1 pw.2 a.2) ≤ dist pz pw := by
    rcases a.2 with i | i
    · exact (dist_le_pi_dist pz.1 pw.1 i).trans (le_max_left _ _)
    · exact (dist_le_pi_dist pz.2 pw.2 i).trans (le_max_right _ _)
  have hrow := ((mixedRealCoordinates_lipschitz (euclideanSubspace (U a.1)) (b a.1) (o a.1) (hC a.1)).comp
    (euclideanFromCoordinates_lipschitz (D := J a.1))).dist_le_mul
      (fun k => z ⟨a.1, (), k⟩) (fun k => w ⟨a.1, (), k⟩)
  have hin : dist (fun k => z ⟨a.1, (), k⟩) (fun k => w ⟨a.1, (), k⟩) ≤ dist z w :=
    (dist_pi_le_iff dist_nonneg).mpr (fun k => dist_le_pi_dist z w ⟨a.1, (), k⟩)
  have hc : C a.1 * Fintype.card (J a.1) ≤ ∑ j, C j * Fintype.card (J j) :=
    Finset.single_le_sum (f := fun j => C j * Fintype.card (J j))
      (fun _ _ => by positivity) (Finset.mem_univ a.1)
  have hd : dist (Sum.elim pz.1 pz.2 a.2) (Sum.elim pw.1 pw.2 a.2) ≤
      ((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w :=
    (hout.trans hrow).trans ((mul_le_mul_of_nonneg_left hin (NNReal.coe_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) dist_nonneg))
  change |Sum.elim pz.1 pz.2 a.2 / R a.1 - Sum.elim pw.1 pw.2 a.2 / R a.1| ≤ _
  rw [← sub_div, abs_div, abs_of_pos (hR a.1)]
  calc
    _ ≤ (((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w) / R a.1 :=
      div_le_div_of_nonneg_right hd (hR a.1).le
    _ = (R a.1)⁻¹ * (((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w) := by ring
    _ ≤ (K : ℝ) * (((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w) :=
      mul_le_mul_of_nonneg_right (hK a.1) (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)
    _ = _ := by rw [NNReal.coe_mul, mul_assoc]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastNativePullbackBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal BigOperators

variable {X : Type*} [Fintype X]

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (P : LayerSamplerAxis I n → Prop)
variable {A : Type*} [Fintype A] (selected : A → Σ j : Fin m, Fin (n j))
variable (R : Fin m → ℝ)

theorem forecastNormalizedActiveCoordinates_lipschitz :
    LipschitzWith 1 (forecastNormalizedActiveCoordinates P) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul]
  exact (dist_pi_le_iff dist_nonneg).mpr (fun a => dist_le_pi_dist v w a.1.val)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawRecoveredRationalCardinalityCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators NNReal Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

private theorem taggedAmbient_lipschitz :
    LipschitzWith 1 (fun v : (Σ j, J j) → ℝ =>
      fun a : JetAmbientIndex (fun _ : Fin m => Unit) J => v ⟨a.1,a.2.2⟩) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul]
  exact (dist_pi_le_iff dist_nonneg).mpr (fun a => dist_le_pi_dist v w ⟨a.1,a.2.2⟩)

theorem forecastFrozenIntegerMixedValue_lipschitz
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ≥0)
    (hC : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ C j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (z : ∀ j, Fin (n j) → ℤ) :
    LipschitzWith (K * ∑ j, C j * Fintype.card (J j))
      (fun v => allocatedFullMixedSiteValue (R := R) U b
        (forecastFrozenIntegerMixedValue U b o z v)) := by
  have hf := (allocatedFullAmbientSiteCoordinates_lipschitz U b o hR C hC K hK).comp
    (taggedAmbient_lipschitz (J := J))
  apply LipschitzWith.of_dist_le_mul
  intro v w
  apply (dist_pi_le_iff (by positivity)).mpr
  rintro ⟨j, i | i⟩
  · have h := (dist_le_pi_dist _ _ (⟨j, Sum.inl i⟩ : LayerSamplerAxis I n)).trans
      (hf.dist_le_mul v w)
    simpa only [Function.comp_apply, allocatedFullAmbientSiteCoordinates,
      allocatedFullMixedSiteValue, forecastFrozenIntegerMixedValue, Sum.elim_inl,
      mul_one] using h
  · change dist ((z j i : ℝ) / _ / _) ((z j i : ℝ) / _ / _) ≤ _
    simp only [dist_self]
    positivity

theorem forecastFrozenIntegerActiveCoordinates_lipschitz
    (inactive : LayerSamplerAxis I n → Prop)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ≥0)
    (hC : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ C j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (z : ∀ j, Fin (n j) → ℤ) :
    LipschitzWith (K * ∑ j, C j * Fintype.card (J j))
      (fun v => forecastNormalizedActiveCoordinates inactive
        (allocatedFullMixedSiteValue (R := R) U b
          (forecastFrozenIntegerMixedValue U b o z v))) := by
  simpa only [one_mul, Function.comp_def] using (forecastNormalizedActiveCoordinates_lipschitz inactive).comp
    (forecastFrozenIntegerMixedValue_lipschitz U b o hR C hC K hK z)

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

local notation "rat" => forecastLawRecoveredRationalFactor B U basis S law selected sample x
  active Y N volume hb bW
local notation "kernel" => forecastLawRecoveredKernel B U basis S law density selected sample x
  active Y N volume base physicalN τ o hb bW

theorem forecastLawRecoveredKernel_lift_lipschitz
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {Dlip Rcap : ℝ≥0} (hdensity : LipschitzWith Dlip density)
    (hcap : ∀ r β, |rat r β| ≤ Rcap)
    (v : X → ℝ) (r : X → ZMod N) (β : (Σ j, J j) → ℤ) :
    LipschitzWith (Rcap * (Dlip * (K * ∑ j, C j * Fintype.card (J j))))
      (kernel v r β) := by
  have hc := forecastFrozenIntegerActiveCoordinates_lipschitz U basis o short hR C hC K hK
    (fun j i => forecastRecoveredIntegerLabels U basis hb bW β j (Sum.inl i))
  have hpair := (LipschitzWith.const (forecastNormalizedSpatialCoordinates base physicalN τ v)).prodMk hc
  have hd := hdensity.comp hpair
  apply LipschitzWith.of_dist_le_mul
  intro y z
  change |density _ * rat r β - density _ * rat r β| ≤ _
  rw [← sub_mul, abs_mul, mul_comm]
  calc
    _ ≤ (Rcap : ℝ) * |density _ - density _| :=
      mul_le_mul_of_nonneg_right (hcap r β) (abs_nonneg _)
    _ ≤ (Rcap : ℝ) * ((Dlip * (K * ∑ j, C j * Fintype.card (J j)) : ℝ≥0) * dist y z) := by
      apply mul_le_mul_of_nonneg_left _ Rcap.coe_nonneg
      simpa only [Function.comp_apply, zero_max, Real.dist_eq] using hd.dist_le_mul y z
    _ = _ := by simp only [NNReal.coe_mul]; ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastLawCenteredRecoveredKernel
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

variable (law : FiniteProbabilityWeights
  (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)))

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

local notation "rat" => forecastLawRecoveredRationalFactor B U basis S law selected sample x
  active Y N volume hb bW

variable {d : ℕ} (e : Fin d ≃ Σ j, J j) (c : (Σ j, J j) → ℝ)

private theorem centeredTagCoordinates_lipschitz :
    LipschitzWith 1 (fun y : Fin d → ℝ => fun a => y (e.symm a) + c a) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro a
  simpa only [dist_add_right] using dist_le_pi_dist y z (e.symm a)

private theorem centeredTagPullback_lipschitz {L : ℝ≥0}
    {f : ((Σ j, J j) → ℝ) → ℝ} (hf : LipschitzWith L f) :
    LipschitzWith L (centeredTagPullback e c f) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  exact (hf.dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left
      (by simpa only [NNReal.coe_one, one_mul] using
        (centeredTagCoordinates_lipschitz e c).dist_le_mul y z) L.coe_nonneg)

local notation "centered" => forecastLawCenteredRecoveredKernel B U basis S law density selected sample x
  active Y N volume base physicalN τ o hb bW e c

theorem forecastLawCenteredRecoveredKernel_lift_lipschitz
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {Dlip Rcap : ℝ≥0} (hdensity : LipschitzWith Dlip density)
    (hcap : ∀ r β, |rat r β| ≤ Rcap)
    (v : X → ℝ) (r : X → ZMod N) (β : Fin d → ℤ) :
    LipschitzWith (Rcap * (Dlip * (K * ∑ j, C j * Fintype.card (J j))))
      (centered v r β) := by
  exact centeredTagPullback_lipschitz e c
    (forecastLawRecoveredKernel_lift_lipschitz B U basis S law density selected sample x
      active Y N volume base physicalN τ o hb bW hR C hC K hK hdensity hcap v r
      (fun a => β (e.symm a)))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualFixedSpatialSlicedRetainedKernelComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.retainedBoundsReferenceNonzero
variable (cutoff : ℕ)
local notation "q" => slice.path.referenceRetainedCRTModulus cutoff
local notation "vol" => (∏ a, (basisAxisScale (b (Sigma.fst (selected a))) (Sigma.snd (selected a)) : ℝ))
local notation "Y" => (fun z t j => integerLongPolynomialOutput slice.path.referencePolynomial
  (fun k => (z (Prod.fst k) (Prod.snd k) : ℤ)) q t j)
local notation "rat" => forecastLawRecoveredRationalFactor B U b S slice.principalLaw selected
  slice.path.sample slice.path.commonTuple (fun _ => slice.path.referenceRetainedCRTInputLaw cutoff)
  Y q vol hb bW
local notation "centered" => forecastLawCenteredRecoveredKernel B U b S slice.principalLaw
  (slice.density hB) selected slice.path.sample slice.path.commonTuple
  (fun _ => slice.path.referenceRetainedCRTInputLaw cutoff) Y q vol
  slice.path.base physicalN τ o hb bW e (fun _ => 0)

private theorem retainedRecoveredG_eq_centered :
    slice.retainedRecoveredG selected hB o bW hb e cutoff = centered := by
  funext v r β y
  change forecastLawRecoveredKernel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun a => y (e.symm a)) =
    forecastLawRecoveredKernel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun a => y (e.symm a) + 0)
  simp only [add_zero]

omit [Fintype Tsp] in
private theorem retainedRational_abs_le_layered {Rcap : ℝ≥0}
    (hcap : ∀ r β, |slice.retainedRecoveredRationalFactor selected bW hb e cutoff r β| ≤ Rcap)
    (r : X → ZMod q) (β : (Σ j, J j) → ℤ) : |rat r β| ≤ Rcap := by
  have h := hcap r (fun i => β (e i))
  simpa only [retainedRecoveredRationalFactor, Equiv.apply_symm_apply] using h

theorem retainedRecoveredG_lift_lipschitz
    (C : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {Dlip Rcap : ℝ≥0} (hdensity : LipschitzWith Dlip (slice.density hB))
    (hcap : ∀ r β, |slice.retainedRecoveredRationalFactor selected bW hb e cutoff r β| ≤ Rcap)
    (v : X → ℝ) (r : X → ZMod q) (β : Fin d → ℤ) :
    LipschitzWith (Rcap * (Dlip * (K * ∑ j, C j * Fintype.card (J j))))
      (slice.retainedRecoveredG selected hB o bW hb e cutoff v r β) := by
  rw [slice.retainedRecoveredG_eq_centered selected hB o bW hb e cutoff]
  exact forecastLawCenteredRecoveredKernel_lift_lipschitz B U b S slice.principalLaw
    (slice.density hB) selected slice.path.sample slice.path.commonTuple
    (fun _ => slice.path.referenceRetainedCRTInputLaw cutoff) Y q vol
    slice.path.base physicalN τ o hb bW e (fun _ => 0) hR C hC K hK hdensity
    (slice.retainedRational_abs_le_layered selected bW hb e cutoff hcap) v r β

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualFixedSpatialScaledRetainedKernelBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

private theorem lipschitzWith_nnreal_mul {Y : Type*} [PseudoMetricSpace Y]
    {F : Y → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (κ : ℝ≥0) :
    LipschitzWith (κ * L) (fun y => (κ : ℝ) * F y) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist ((κ : ℝ) * F x) ((κ : ℝ) * F y) = (κ : ℝ) * dist (F x) (F y) := by
      simp only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg κ.coe_nonneg]
    _ ≤ (κ : ℝ) * ((L : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left (hF.dist_le_mul x y) κ.coe_nonneg
    _ = ((κ * L : ℝ≥0) : ℝ) * dist x y := by rw [NNReal.coe_mul, mul_assoc]

variable (cutoff : ℕ) (κ : ℝ≥0)

theorem scaledRetainedRecoveredG_lift_lipschitz_s2_oai
    (C : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {Dlip Rcap : ℝ≥0} (hdensity : LipschitzWith Dlip (slice.density hB))
    (hcap : ∀ residue β,
      |slice.retainedRecoveredRationalFactor selected bW hb e cutoff residue β| ≤ Rcap)
    (v : X → ℝ) (residue : X → ZMod (slice.path.referenceRetainedCRTModulus cutoff))
    (β : Fin d → ℤ) :
    LipschitzWith (κ * (Rcap * (Dlip * (K * ∑ j, C j * Fintype.card (J j)))))
      (slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue β) :=
  lipschitzWith_nnreal_mul
    (slice.retainedRecoveredG_lift_lipschitz selected hB o bW hb e cutoff C hC K hK
      hdensity hcap v residue β) κ

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.scaledRetainedRecoveredG_lift_lipschitz_s2_oai := @OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.scaledRetainedRecoveredG_lift_lipschitz_s2_oai
