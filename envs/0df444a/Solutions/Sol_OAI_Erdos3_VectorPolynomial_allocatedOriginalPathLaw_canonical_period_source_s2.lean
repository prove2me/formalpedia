-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedOriginalPathLaw_canonical_period_source_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:20:45.500259+00:00
-- url     : https://prove2.me/submissions/7b501100-ef60-4c66-9615-476f2ad918b5

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B234
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedOriginalPathLaw_niltest_good_sliced_source_s2
import Theorems.Thm_OAI_Erdos3_canonicalSlicedModulus_good_s2
import Theorems.Thm_OAI_Erdos3_exists_containedSupportedProgressionReference_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateDeterminant
namespace OAI

section

namespace Erdos3

theorem coordinateDeterminantVariation_nonneg (I X : Type*) [Fintype I] [Fintype X] :
    0 ≤ coordinateDeterminantVariation I X := by
  unfold coordinateDeterminantVariation
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3

theorem integerScalarCubeDensityCap_pos (I : Type*) [Fintype I] :
    0 < integerScalarCubeDensityCap I := by
  unfold integerScalarCubeDensityCap
  positivity


open scoped BigOperators Classical

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.JointKernelCutoffBudget
namespace OAI


namespace Erdos3

theorem jointKernelCutoff_bounds (n b : ℕ) {K T ε κ : ℝ}
    (hK : 0 ≤ K) (hT : 0 ≤ T) (hε : 0 < ε) (hκ : 0 < κ) :
    0 < jointKernelCutoff n b K T ε κ ∧
    n ≤ jointKernelCutoff n b K T ε κ ∧
    b ≤ jointKernelCutoff n b K T ε κ ∧
    1 / κ ≤ (jointKernelCutoff n b K T ε κ : ℝ) ∧
    K / κ ≤ (jointKernelCutoff n b K T ε κ : ℝ) ∧
    2 * T / ε ≤ (jointKernelCutoff n b K T ε κ : ℝ) := by
  have h1 : 0 < 1 / κ := one_div_pos.mpr hκ
  have h2 : 0 ≤ K / κ := div_nonneg hK hκ.le
  have h3 : 0 ≤ 2 * T / ε := div_nonneg (by positivity) hε.le
  have hc := Nat.le_ceil (1 + (n : ℝ) + b + (1 + K) / κ + 2 * T / ε)
  change 1 + (n : ℝ) + b + (1 + K) / κ + 2 * T / ε ≤
    (jointKernelCutoff n b K T ε κ : ℝ) at hc
  rw [add_div] at hc
  have hn : (n : ℝ) ≤ jointKernelCutoff n b K T ε κ := by linarith
  have hb : (b : ℝ) ≤ jointKernelCutoff n b K T ε κ := by linarith
  have hp : (0 : ℝ) < jointKernelCutoff n b K T ε κ := by
    have := Nat.cast_nonneg n (α := ℝ)
    have := Nat.cast_nonneg b (α := ℝ)
    linarith
  exact ⟨by exact_mod_cast hp, by exact_mod_cast hn, by exact_mod_cast hb,
    by linarith, by linarith, by linarith⟩

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget
namespace OAI


namespace Erdos3

theorem scalarKernelConditioningConstant_pos (I J : Type*) [Fintype I] [Fintype J]
    {M D : ℕ} (hM : 0 < M) (hD : 0 < D) : 0 < scalarKernelConditioningConstant I J M D :=
  pow_pos (scalarCubeResidueDensityCap_pos I (M * D) (Nat.mul_pos hM hD)) _

theorem scalarKernelTailConstant_pos (I J : Type*) [Fintype I] [Fintype J] :
    0 < scalarKernelTailConstant I J := by
  unfold scalarKernelTailConstant
  exact pow_pos (mul_pos (integerScalarCubeDensityCap_pos I) (by positivity)) _

theorem scalarKernelAdjustedAccuracy_pos (I J : Type*) [Fintype I] [Fintype J]
    {M D : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) :
    0 < scalarKernelAdjustedAccuracy I J M D η :=
  div_pos hη (scalarKernelConditioningConstant_pos I J hM hD)

theorem scalarKernelThreshold_pos (I J : Type*) [Fintype I] [Fintype J]
    {M D : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) :
    0 < scalarKernelThreshold I J M D η := by
  unfold scalarKernelThreshold discreteScalarMinorThreshold
  apply polynomialSublevelThreshold_pos
  · apply mul_nonneg (pow_nonneg (integerScalarCubeDensityCap_pos I).le _)
    unfold multivariateSublevelConstant
    exact mul_nonneg (by positivity) (univariateSublevelConstant_pos _).le
  · positivity
  · exact scalarKernelAdjustedAccuracy_pos I J hM hD hη

theorem scalarKernelCutoff_bounds (I J : Type*) [Fintype I] [Fintype J]
    {M D : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) :
    0 < scalarKernelCutoff I J M D η ∧
    Fintype.card I + 1 ≤ scalarKernelCutoff I J M D η ∧
    D * ((Fintype.card I + 1) * M) ≤ scalarKernelCutoff I J M D η ∧
    1 / scalarKernelThreshold I J M D η ≤ (scalarKernelCutoff I J M D η : ℝ) ∧
    coordinateDeterminantVariation I (Fin (Fintype.card (J × Option I))) /
        scalarKernelThreshold I J M D η ≤ (scalarKernelCutoff I J M D η : ℝ) ∧
    2 * scalarKernelTailConstant I J / scalarKernelAdjustedAccuracy I J M D η ≤
      (scalarKernelCutoff I J M D η : ℝ) :=
  jointKernelCutoff_bounds _ _ (coordinateDeterminantVariation_nonneg _ _)
    (scalarKernelTailConstant_pos I J).le (scalarKernelAdjustedAccuracy_pos I J hM hD hη)
    (scalarKernelThreshold_pos I J hM hD hη)


end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProgressionInnerFamily
namespace OAI

section

namespace Erdos3

theorem progression_slice_step_le_inverse_density {L step H : ℕ} (c : ℤ)
    (hL : 0 < L) (hstep : 0 < step) (hH : 2 ≤ H) {δ : ℝ} (hδ : 0 < δ)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (hdense : δ * L ≤ ((integerProgressionSupport c (step : ℤ) H).card : ℝ)) :
    (step : ℝ) ≤ 4 / δ := by
  have hg := (progression_slice_endpoint_geometry c hL hstep hH hδ hsubset hdense).2.2.2
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hH2 : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hstep0 : (0 : ℝ) ≤ step := Nat.cast_nonneg _
  have he := (le_div_iff₀ (by linarith : 0 < (H : ℝ) - 1)).mp hg
  rw [div_mul_eq_mul_div] at he
  have he' := (div_le_iff₀ hLp).mp he
  rw [card_integerProgressionSupport c step H hstep] at hdense
  have hh := mul_le_mul_of_nonneg_left (show (H : ℝ) ≤ 2 * ((H : ℝ) - 1) by linarith) hstep0
  have hd := mul_le_mul_of_nonneg_left hdense hstep0
  apply (le_div_iff₀ hδ).mpr
  apply (mul_le_mul_iff_left₀ hLp).mp
  nlinarith only [he', hh, hd]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ScalarKernelDenseSliceStride
namespace OAI

section

namespace Erdos3

theorem scalarKernelCutoff_dense_slice_stride (s : ℕ) (G : Type*) [Fintype G]
    {p η : ℝ} (hη : 0 < η) {S step H : ℕ} (c : ℤ)
    (hcutoff : scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊ η ≤ S)
    (hstep : 0 < step)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (S : ℤ))
    (hdense : Real.exp (-(p + 1)) * S ≤ (H : ℝ)) :
    2 ≤ H ∧ (step : ℝ) ≤ 4 * Real.exp (p + 1) := by
  have hD : 0 < ⌈Real.exp (p + 1)⌉₊ := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hc := ((scalarKernelCutoff_bounds (Fin (s + 1)) G (by norm_num : 0 < (1 : ℕ)) hD hη).2.2.1).trans hcutoff
  have hcR : (⌈Real.exp (p + 1)⌉₊ : ℝ) * ((s : ℝ) + 2) ≤ S := by
    simpa only [Fintype.card_fin, mul_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      add_assoc, one_add_one_eq_two, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ).mpr hc)
  have hS : 2 * Real.exp (p + 1) ≤ S := by
    have hceil := Nat.le_ceil (Real.exp (p + 1))
    have hnonneg : 0 ≤ (⌈Real.exp (p + 1)⌉₊ : ℝ) * (s : ℝ) := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    nlinarith only [hcR, hceil, hnonneg]
  have hSpos : 0 < S := by
    have h := (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.exp_pos (p + 1))).trans_le hS
    exact_mod_cast h
  have hH : 2 ≤ H := by
    have hmul := (mul_le_mul_of_nonneg_left hS (Real.exp_pos (-(p + 1))).le).trans hdense
    have he : Real.exp (-(p + 1)) * (2 * Real.exp (p + 1)) = 2 := by
      rw [mul_left_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    rw [he] at hmul
    exact_mod_cast hmul
  refine ⟨hH, ?_⟩
  have h := progression_slice_step_le_inverse_density c hSpos hstep hH (Real.exp_pos (-(p + 1)))
    hsubset (by simpa only [card_integerProgressionSupport c step H hstep] using hdense)
  simpa only [div_eq_mul_inv, ← Real.exp_neg, neg_neg] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedDetectedCanonicalPeriod
namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

variable {α G X : Type*} [Fintype α] [DecidableEq α] [Fintype G] [Fintype X]
variable {L M : ℕ} (selection : α ↪ G) (stride : X → ℕ) (height : ℕ)

theorem canonicalSlicedModulus_pos (hs : ∀ i, 0 < stride i)
    (x : G → IntegerScalarCubeBox α L) :
    0 < canonicalSlicedModulus (M := M) selection stride height x := by
  unfold canonicalSlicedModulus
  split_ifs with hx
  · exact residueRefinedPeriod_pos (kernelPeriodCandidate_pos _ _) stride hs
  · norm_num

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {s : ℕ} (X : Type) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

local notation "Path" => bases × rectangularWeightIndices 0 widths 1
local notation "pathLaw" => allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem
  N hN hW hτ hξ stride cells hmass bases hbases htotal

theorem allocatedOriginalPathLaw_canonical_sliced_source
    (P : Polynomial ℕ)
    {T : Type} [Fintype T] [Nonempty T]
    (e : T → LayerSamplerVariables G I n B → ℤ) (he : Function.Injective e)
    {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
    {L : ∀ z, Tests z → Type} [∀ z j, LieRing (L z j)] [∀ z j, LieAlgebra ℚ (L z j)]
    {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] L z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] L z j)]
    (D : ∀ z j, RationalFilteredNilmanifold (L z j) s (dims z j))
    (V : ∀ z j, (D z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
    (slices : ∀ z, Tests z → Finset T)
    (c : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
    (step : ∀ z, Tests z → ℕ)
    (H : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ)
    (hstep : ∀ z j, 0 < step z j)
    (hslices : ∀ z j, (slices z j).image e = commonStrideBox (c z j) (step z j) (H z j))
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hdense : ∀ z j, IsDenseCommonStrideBox sides p ((slices z j).image e))
    (hdimension : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) q)
    (hcomplexity : ∀ z j, (V z j).ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) q))
    (hcap : ∀ z j, ((V z j).normBound : ℝ) ≤ 1)
    (f : (X → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (hmesh : Fintype.card (LayerSamplerVariables G I n B) * Real.exp (-p) ≤ α / 8)
    (hthreshold : Real.exp (-q) ≤ α / 4)
    (hdetected : α ≤ sampledSliceSeminorm (pathLaw)
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((V z j).eval (commonStrideIndex (c z j) (step z j) (e t)))) f)
    (selection : Fin (s + 1) ↪ G) (hG : (s + 1) * (s + 3) ≤ Fintype.card G)
    (hkernel : scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊
      (((Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
        Real.exp (-((q + sampledSupportedSlicedDetectionConstant s P) ^ sampledSupportedSlicedDetectionConstant s P)) ^
          (2 ^ (s + 1))) / 2) ≤ S.value)
    (hstride : ∀ i, 0 < stride i) :
    let gain := (Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
      Real.exp (-((q + sampledSupportedSlicedDetectionConstant s P) ^ sampledSupportedSlicedDetectionConstant s P)) ^
        (2 ^ (s + 1))
    let Mk := scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊ (gain / 2)
    let modulus := canonicalSlicedModulus (M := Mk) selection stride m
    ∃ (c₀ : LayerSamplerVariables G I n B → ℤ) (step₀ : ℕ)
      (H₀ : LayerSamplerVariables G I n B → ℕ) (_hstep₀ : 0 < step₀) (hH₀ : ∀ k, 0 < H₀ k),
      (∀ i, integerProgressionSupport (c₀ i) (step₀ : ℤ) (H₀ i) ⊆ Finset.Ico (0 : ℤ) (sides i : ℤ)) ∧
      (∀ i, Real.exp (-(p + 1)) * sides i ≤ (H₀ i : ℝ)) ∧
      (step₀ : ℝ) ≤ 4 * Real.exp (p + 1) ∧
    ∃ (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value),
      GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x ∧
    ∃ (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (modulus x))
      (hr : 0 < (principalTupleWeights (α := Fin (s + 1)) B (layerSamplerDegree I n)
        (fun j => H₀ (Sum.inr j)) (fun j => hH₀ (Sum.inr j))).mass
          (Finset.univ.filter (fun y => principalResidueLabel (modulus x) y = r))),
      ∃ hsubset : ∀ j, integerProgressionSupport (c₀ (Sum.inr j)) (step₀ : ℤ) (H₀ (Sum.inr j)) ⊆
        Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ),
      let law := containedSupportedProgressionLaw B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (fun j => H₀ (Sum.inr j)) (fun _ => step₀)
        (fun j => c₀ (Sum.inr j)) (allocatedPrincipalSides_pos B U b S)
        (fun j => hH₀ (Sum.inr j)) hsubset (modulus x) r hr
      gain / 2 ≤ (law.complexMean (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
        N hN hW hτ hξ stride cells hmass bases x y f)).re ∧
      ∃ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S),
        0 < law.weight y₀ ∧
        (∀ j, IntegerScalarCube (allocatedPrincipalSides B U b S j) (fun a => (y₀ j a : ℤ))) ∧
        (∀ axis : LayerSamplerAxis I n → Prop,
          0 < (containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
            (allocatedPrincipalSides B U b S) (fun j => H₀ (Sum.inr j)) (fun _ => step₀)
            (fun j => c₀ (Sum.inr j)) (allocatedPrincipalSides_pos B U b S)
            (fun j => hH₀ (Sum.inr j)) hsubset (modulus x) r hr axis).weight (principalAxisRestrict axis y₀)) ∧
        (∀ y, law.weight y ≠ 0 → principalResidueLabel (modulus x) y = principalResidueLabel (modulus x) y₀) := by
  intro gain Mk modulus
  let : ∀ x, NeZero (modulus x) := fun x =>
    ⟨(canonicalSlicedModulus_pos selection stride m hstride x).ne'⟩
  obtain ⟨c₀, step₀, H₀, hstep₀, hH₀, hsubset₀, hdense₀, x, hx, r, hr, hsubset, hsource⟩ :=
    allocatedOriginalPathLaw_niltest_good_sliced_source_s2 B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases hbases htotal P e he D V slices c step H hstep hslices
    p q hp hq hdense hdimension hcomplexity hcap f hf α hα hαone hmesh hthreshold hdetected
    selection hG hkernel modulus
  have hgain : 0 < gain := by
    dsimp only [gain]
    exact mul_pos (mul_pos (Real.exp_pos _) (half_pos hα)) (pow_pos (Real.exp_pos _) _)
  let g₀ : G := selection ⟨0, by omega⟩
  have hstrideBound := (scalarKernelCutoff_dense_slice_stride s G (half_pos hgain)
    (c₀ (Sum.inl g₀)) hkernel hstep₀ (hsubset₀ (Sum.inl g₀)) (hdense₀ (Sum.inl g₀))).2
  refine ⟨c₀, step₀, H₀, hstep₀, hH₀, hsubset₀, hdense₀, hstrideBound, x, hx, r, hr, hsubset, hsource, ?_⟩
  exact exists_containedSupportedProgressionReference_s2 B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (fun j => H₀ (Sum.inr j)) (fun _ => step₀)
    (fun j => c₀ (Sum.inr j)) (allocatedPrincipalSides_pos B U b S)
    (fun j => hH₀ (Sum.inr j)) hsubset (modulus x) r hr

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {s : ℕ} (X : Type) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

local notation "Path" => bases × rectangularWeightIndices 0 widths 1
local notation "pathLaw" => allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem
  N hN hW hτ hξ stride cells hmass bases hbases htotal

theorem allocatedOriginalPathLaw_canonical_period_source_s2_oai
    (P : Polynomial ℕ)
    {T : Type} [Fintype T] [Nonempty T]
    (e : T → LayerSamplerVariables G I n B → ℤ) (he : Function.Injective e)
    {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
    {L : ∀ z, Tests z → Type} [∀ z j, LieRing (L z j)] [∀ z j, LieAlgebra ℚ (L z j)]
    {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] L z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] L z j)]
    (D : ∀ z j, RationalFilteredNilmanifold (L z j) s (dims z j))
    (V : ∀ z j, (D z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
    (slices : ∀ z, Tests z → Finset T)
    (c : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
    (step : ∀ z, Tests z → ℕ)
    (H : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ)
    (hstep : ∀ z j, 0 < step z j)
    (hslices : ∀ z j, (slices z j).image e = commonStrideBox (c z j) (step z j) (H z j))
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hdense : ∀ z j, IsDenseCommonStrideBox sides p ((slices z j).image e))
    (hdimension : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) q)
    (hcomplexity : ∀ z j, (V z j).ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) q))
    (hcap : ∀ z j, ((V z j).normBound : ℝ) ≤ 1)
    (f : (X → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (hmesh : Fintype.card (LayerSamplerVariables G I n B) * Real.exp (-p) ≤ α / 8)
    (hthreshold : Real.exp (-q) ≤ α / 4)
    (hdetected : α ≤ sampledSliceSeminorm (pathLaw)
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((V z j).eval (commonStrideIndex (c z j) (step z j) (e t)))) f)
    (selection : Fin (s + 1) ↪ G) (hG : (s + 1) * (s + 3) ≤ Fintype.card G)
    (hkernel : scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊
      (((Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
        Real.exp (-((q + sampledSupportedSlicedDetectionConstant s P) ^ sampledSupportedSlicedDetectionConstant s P)) ^
          (2 ^ (s + 1))) / 2) ≤ S.value)
    (hstride : ∀ i, 0 < stride i) :
    let gain := (Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
      Real.exp (-((q + sampledSupportedSlicedDetectionConstant s P) ^ sampledSupportedSlicedDetectionConstant s P)) ^
        (2 ^ (s + 1))
    let Mk := scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊ (gain / 2)
    ∃ (c₀ : LayerSamplerVariables G I n B → ℤ) (step₀ : ℕ)
      (H₀ : LayerSamplerVariables G I n B → ℕ) (_hstep₀ : 0 < step₀) (hH₀ : ∀ k, 0 < H₀ k),
      (∀ i, integerProgressionSupport (c₀ i) (step₀ : ℤ) (H₀ i) ⊆ Finset.Ico (0 : ℤ) (sides i : ℤ)) ∧
      (∀ i, Real.exp (-(p + 1)) * sides i ≤ (H₀ i : ℝ)) ∧
      (step₀ : ℝ) ≤ 4 * Real.exp (p + 1) ∧
    ∃ (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value),
      ∃ hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x,
      let period := kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m)
      0 < Mk ∧ 0 < period ∧ period ≤ Mk ^ (m + 1) ∧
    ∃ (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod period stride))
      (hr : 0 < (principalTupleWeights (α := Fin (s + 1)) B (layerSamplerDegree I n)
        (fun j => H₀ (Sum.inr j)) (fun j => hH₀ (Sum.inr j))).mass
          (Finset.univ.filter (fun y => principalResidueLabel (residueRefinedPeriod period stride) y = r))),
      ∃ hsubset : ∀ j, integerProgressionSupport (c₀ (Sum.inr j)) (step₀ : ℤ) (H₀ (Sum.inr j)) ⊆
        Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ),
      let law := containedSupportedProgressionLaw B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (fun j => H₀ (Sum.inr j)) (fun _ => step₀)
        (fun j => c₀ (Sum.inr j)) (allocatedPrincipalSides_pos B U b S)
        (fun j => hH₀ (Sum.inr j)) hsubset (residueRefinedPeriod period stride) r hr
      gain / 2 ≤ (law.complexMean (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
        N hN hW hτ hξ stride cells hmass bases x y f)).re ∧
      ∃ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S),
        0 < law.weight y₀ ∧
        (∀ j, IntegerScalarCube (allocatedPrincipalSides B U b S j) (fun a => (y₀ j a : ℤ))) ∧
        (∀ axis : LayerSamplerAxis I n → Prop,
          0 < (containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
            (allocatedPrincipalSides B U b S) (fun j => H₀ (Sum.inr j)) (fun _ => step₀)
            (fun j => c₀ (Sum.inr j)) (allocatedPrincipalSides_pos B U b S)
            (fun j => hH₀ (Sum.inr j)) hsubset (residueRefinedPeriod period stride) r hr axis).weight (principalAxisRestrict axis y₀)) ∧
        (∀ y, law.weight y ≠ 0 → principalResidueLabel (residueRefinedPeriod period stride) y = principalResidueLabel (residueRefinedPeriod period stride) y₀) := by
  intro gain Mk
  obtain ⟨c₀, step₀, H₀, hstep₀, hH₀, hsubset₀, hdense₀, hstrideBound, x, hx, htail⟩ :=
    allocatedOriginalPathLaw_canonical_sliced_source B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases hbases htotal P e he D V slices c step H hstep hslices
      p q hp hq hdense hdimension hcomplexity hcap f hf α hα hαone hmesh hthreshold hdetected
      selection hG hkernel hstride
  have hMk : 0 < Mk := Nat.zero_lt_of_lt (goodKernelUniformCandidate selection x hx m).isLt
  refine ⟨c₀, step₀, H₀, hstep₀, hH₀, hsubset₀, hdense₀, hstrideBound, x, hx,
    hMk, kernelPeriodCandidate_pos _ _, kernelPeriodCandidate_le _ _, ?_⟩
  erw [canonicalSlicedModulus_good_s2 selection stride m x hx] at htail
  exact htail

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.allocatedOriginalPathLaw_canonical_period_source_s2_oai := @OAI.Erdos3.VectorPolynomial.allocatedOriginalPathLaw_canonical_period_source_s2_oai
