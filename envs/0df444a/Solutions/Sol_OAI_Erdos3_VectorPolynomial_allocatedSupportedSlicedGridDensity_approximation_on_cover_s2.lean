-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedGridDensity_approximation_on_cover_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:41:17.993751+00:00
-- url     : https://prove2.me/submissions/812b719e-d994-465c-bca4-6ab59f34ad05

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedResidueJetPMF_source_s2
import Theorems.Thm_OAI_Erdos3_positiveAffineModerate_grid_approximation_on_cover_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteDependentPMFBind
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

theorem toPMF_toReal (p : FiniteProbabilityWeights X) (x : X) :
    (p.toPMF x).toReal = p.weight x := by
  rw [toPMF_apply, ENNReal.toReal_ofReal (p.nonneg x)]

theorem toPMF_bind_apply {Y : Type*} (p : FiniteProbabilityWeights X)
    (q : X → PMF Y) (y : Y) :
    (p.toPMF.bind q) y = ∑ x, ENNReal.ofReal (p.weight x) * q x y := by
  rw [PMF.bind_apply, tsum_fintype]
  simp only [toPMF_apply]

theorem toPMF_bind_toReal {Y : Type*} (p : FiniteProbabilityWeights X)
    (q : X → PMF Y) (y : Y) :
    ((p.toPMF.bind q) y).toReal = p.mean (fun x => (q x y).toReal) := by
  rw [toPMF_bind_apply, ENNReal.toReal_sum (fun x _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((q x).apply_ne_top y))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (p.nonneg _), mean]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.NormalizedExpectationWeights
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem ofDensity_mean {X : Type*} [Fintype X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (htotal : (𝔼 x, w x) = 1) (f : X → ℝ) :
    (ofDensity w hw htotal).mean f = 𝔼 x, w x * f x := by
  simp only [mean, ofDensity, Fintype.expect_eq_sum_div_card, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem reweight_mean {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (htotal : p.mean w = 1) (f : X → ℝ) :
    (p.reweight w hw htotal).mean f = p.mean (fun x => w x * f x) := by
  simp only [mean, reweight, mul_assoc]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NormalizedScalarCubeSource

theorem source_coefficient_mean (s : NormalizedScalarCubeSource Empty) (f : ℤ → ℝ) :
    s.source.mean (fun x => f (x none : ℤ)) = (s.coefficientWeights).mean (fun z => f z) := by
  apply (FiniteProbabilityWeights.reweight_mean s.baseLaw
    (fun z => s.weight (fun i => (z i : ℝ) / s.length))
    (fun z => (s.weight_range (fun i => (z i : ℝ) / s.length)).1) s.normalized
    (fun x => f (x none : ℤ))).trans
  rw [coefficientWeights, FiniteProbabilityWeights.ofDensity_mean]
  simp only [s.weight_empty_coordinate, coefficientDensity]
  exact s.baseLaw_coefficient_mean (fun z => s.weight (fun _ => (z : ℝ) / s.length) * f z)

end NormalizedScalarCubeSource

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerPMFNormalizedSource
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

namespace FiniteProbabilityWeights

theorem toPMF_map_toReal {X Y : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (f : X → Y) (y : Y) :
    ((p.toPMF.map f) y).toReal = p.mean (fun x => if f x = y then 1 else 0) := by
  change ((p.toPMF.bind (fun x => PMF.pure (f x))) y).toReal = _
  rw [toPMF_bind_toReal]
  congr 1
  funext x
  by_cases h : f x = y
  · simp [PMF.pure_apply, h]
  · have h' : y ≠ f x := Ne.symm h
    simp [PMF.pure_apply, h, h']

end FiniteProbabilityWeights

section IntegerSourceLaw

variable (L : ℕ) (hL : 0 < L) (p : PMF ℤ)
variable (hs : ∀ k, p k ≠ 0 → k ∈ Finset.Ico 0 (L : ℤ))
variable (w : (Option Empty → ℝ) → ℝ) (B T : ℝ≥0) (hB : 0 < B)
variable (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
variable (hgrid : ∀ k : ℤ, w (fun _ => (k : ℝ) / L) = L * (p k).toReal)

local notation "intervalSource" =>
  normalizedScalarCubeSourceOfIntegerPMF L hL p hs w B T hB hw hLip hgrid

theorem normalizedScalarCubeSourceOfIntegerPMF_mean (f : ℤ → ℝ) :
    (intervalSource).source.mean (fun x => f (x none : ℤ)) =
      ∑ k ∈ Finset.Ico 0 (L : ℤ), (p k).toReal * f k := by
  apply ((intervalSource).source_coefficient_mean f).trans
  change (FiniteProbabilityWeights.ofDensity _ _ _).mean _ = _
  rw [FiniteProbabilityWeights.ofDensity_mean]
  change (𝔼 k : coefficientResidueSet L 1 0,
    w (fun _ => (k.val : ℝ) / L) * f k.val) = _
  have hr : coefficientResidueSet L 1 0 = Finset.Ico 0 (L : ℤ) := by
    ext k
    simp only [coefficientResidueSet, Finset.mem_filter]
    exact ⟨And.left, fun hk => ⟨hk, Subsingleton.elim _ _⟩⟩
  rw [hr, Fintype.expect_eq_sum_div_card]
  simp only [Fintype.card_coe, Int.card_Ico, sub_zero, Int.toNat_natCast]
  simp_rw [hgrid, mul_assoc]
  rw [← Finset.mul_sum]
  field_simp
  exact Finset.sum_coe_sort (Finset.Ico 0 (L : ℤ)) (fun k => (p k).toReal * f k)

theorem normalizedScalarCubeSourceOfIntegerPMF_law :
    (intervalSource).source.toPMF.map (fun x => (x none : ℤ)) = p := by
  ext z
  let q := (intervalSource).source.toPMF.map (fun x => (x none : ℤ))
  have hreal : (q z).toReal = (p z).toReal := by
    change (((intervalSource).source.toPMF.map (fun x => (x none : ℤ))) z).toReal = _
    rw [FiniteProbabilityWeights.toPMF_map_toReal]
    refine (normalizedScalarCubeSourceOfIntegerPMF_mean L hL p hs w B T hB hw hLip hgrid
      (fun k => @ite ℝ (k = z) (Classical.propDecidable (k = z)) 1 0)).trans ?_
    by_cases hz : z ∈ Finset.Ico 0 (L : ℤ)
    · simp [mul_ite, hz]
    · have hpz : p z = 0 := by
        by_contra h
        exact hz (hs z h)
      simp [mul_ite, hz, hpz]
  exact (ENNReal.ofReal_toReal (q.apply_ne_top z)).symm.trans
    ((congrArg ENNReal.ofReal hreal).trans (ENNReal.ofReal_toReal (p.apply_ne_top z)))

end IntegerSourceLaw

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.WeightedModeratePointMass
namespace OAI

section

namespace Erdos3

open scoped Classical

theorem finiteImageMass_eq_toPMF {X H : Type*} [Fintype X] [DecidableEq H]
    (p : FiniteProbabilityWeights X) (Y : X → H) (z : H) :
    finiteImageMass p Y z = ((p.toPMF.map Y) z).toReal := by
  have he : finiteImageMass p Y z = p.mean (fun x =>
      @ite ℝ (Y x = z) (Classical.propDecidable (Y x = z)) 1 0) := by
    unfold finiteImageMass
    apply congrArg (fun f : X → ℝ => p.mean f)
    funext x
    by_cases hx : Y x = z <;> simp [hx]
  exact he.trans (FiniteProbabilityWeights.toPMF_map_toReal p Y z).symm

theorem integerGridMass_eq_toPMF {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) (z : J → ℤ) :
    integerGridMass p Y M z =
      ((p.toPMF.map (fun x => integerGridResidue M (Y x))) (integerGridResidue M z)).toReal :=
  finiteImageMass_eq_toPMF p (fun x => integerGridResidue M (Y x)) (integerGridResidue M z)

theorem integerGridMass_eq_of_pmf_image {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (μ : PMF (J → ℤ))
    (hμ : p.toPMF.map Y = μ) (M : ℕ) (z : J → ℤ) :
    integerGridMass p Y M z = ((μ.map (integerGridResidue M)) (integerGridResidue M z)).toReal := by
  have ht : p.toPMF.map (fun x => integerGridResidue M (Y x)) = μ.map (integerGridResidue M) :=
    (PMF.map_comp Y p.toPMF (integerGridResidue M)).symm.trans
      (congrArg (fun ν : PMF (J → ℤ) => ν.map (integerGridResidue M)) hμ)
  exact (integerGridMass_eq_toPMF p Y M z).trans
    (congrArg (fun ν : PMF (J → ZMod M) => (ν (integerGridResidue M z)).toReal) ht)

theorem integerGridDensity_eq_of_pmf_image {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (μ : PMF (J → ℤ))
    (hμ : p.toPMF.map Y = μ) (K M : ℕ) (z : J → ℤ) :
    integerGridDensity p Y K M z =
      (K : ℝ) ^ Fintype.card J * ((μ.map (integerGridResidue M)) (integerGridResidue M z)).toReal :=
  congrArg (fun t : ℝ => (K : ℝ) ^ Fintype.card J * t)
    (integerGridMass_eq_of_pmf_image p Y μ hμ M z)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalScalarSourceEnvelope
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem paddedResidueDensityCap_mono (I : Type*) [Fintype I] {M N : ℕ} (hMN : M ≤ N) :
    paddedResidueDensityCap I M ≤ paddedResidueDensityCap I N := by
  unfold paddedResidueDensityCap scalarCubeResidueDensityCap
  gcongr

theorem ScalarCubePrimitiveBudget.mono {I : Type*} [Fintype I] [DecidableEq I]
    {s : NormalizedScalarCubeSource I} {A : ℝ≥0} {U V : ℝ}
    (h : ScalarCubePrimitiveBudget s A U) (hUV : U ≤ V) : ScalarCubePrimitiveBudget s A V :=
  ⟨h.one_le.trans hUV, h.dimension_le.trans hUV, h.modulus_le.trans hUV,
    h.weight_le.trans hUV, h.weightLipschitz_le.trans hUV, h.boundary_le.trans hUV,
    h.grid_le.trans hUV, h.derivative_le.trans hUV, h.density_le.trans hUV⟩

theorem scalarCubePrimitiveBudget_of_raw_bounds {I : Type*} [Fintype I] [DecidableEq I]
    (s : NormalizedScalarCubeSource I) (A B T : ℝ≥0) (M : ℕ)
    (hM : s.modulusBound ≤ M) (hB : s.weightBound ≤ B) (hT : s.weightLipschitz ≤ T) :
    ScalarCubePrimitiveBudget s A (scalarCubePrimitiveEnvelope I A B T M) := by
  let q := (Fintype.card I : ℝ) + 1
  let V := (2 * q) ^ (Fintype.card I + 1)
  let X := 4 * V * ((2 : ℝ) ^ Fintype.card I) ^ 2
  let Y := 2 * scalarCubeGridBoundaryConstant I * V
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hX : 0 ≤ X := by dsimp only [X, V]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y, V, scalarCubeGridBoundaryConstant]; positivity
  have hZ : 0 ≤ scalarCubeCutoffDerivativeNumerator I A := by
    unfold scalarCubeCutoffDerivativeNumerator; positivity
  have hP : 0 ≤ paddedResidueDensityCap I M := by
    unfold paddedResidueDensityCap scalarCubeResidueDensityCap; positivity
  have hparts :
      1 ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      q ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      (M : ℝ) ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      (B : ℝ) ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      (T : ℝ) ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      X ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      Y ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      scalarCubeCutoffDerivativeNumerator I A ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      paddedResidueDensityCap I M ≤ scalarCubePrimitiveEnvelope I A B T M := by
    change 1 ≤ 1 + q + M + B + T + X + Y + _ + _ ∧ _
    dsimp only [scalarCubePrimitiveEnvelope]
    change 1 ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      q ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      (M : ℝ) ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      (B : ℝ) ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      (T : ℝ) ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      X ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      Y ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      scalarCubeCutoffDerivativeNumerator I A ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      paddedResidueDensityCap I M ≤ 1 + q + M + B + T + X + Y + _ + _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      linarith only [hq, hX, hY, hZ, hP, Nat.cast_nonneg (α := ℝ) M, B.coe_nonneg, T.coe_nonneg]
  obtain ⟨h1, hq', hM', hB', hT', hX', hY', hZ', hP'⟩ := hparts
  have hvol : scalarCubeDomainDensity I ≤ V := scalarCubeDomainDensity_le_power I
  have hboundary : scalarCubeBoundaryConstant I ≤ X := by
    unfold scalarCubeBoundaryConstant
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvol (by norm_num)) (by positivity)
  have hgrid : 2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) ≤ Y := by
    have hh := mul_le_mul_of_nonneg_left hvol
      (show 0 ≤ 2 * scalarCubeGridBoundaryConstant I by unfold scalarCubeGridBoundaryConstant; positivity)
    simpa only [scalarCubeDomainDensity, div_eq_mul_inv, Y] using hh
  refine ⟨h1, hq', ?_, ?_, ?_, hboundary.trans hX', hgrid.trans hY', hZ', ?_⟩
  · exact (by exact_mod_cast hM : (s.modulusBound : ℝ) ≤ M).trans hM'
  · exact (by exact_mod_cast hB : (s.weightBound : ℝ) ≤ B).trans hB'
  · exact (by exact_mod_cast hT : (s.weightLipschitz : ℝ) ≤ T).trans hT'
  · exact (paddedResidueDensityCap_mono I hM).trans hP'

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem normalizedUniformCubeSource_primitive (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L) (A : ℝ≥0) :
    ScalarCubePrimitiveBudget (normalizedUniformCubeSource I L M hL m r hm hmM hsize) A
      (scalarCubePrimitiveEnvelope I A 1 0 M) :=
  scalarCubePrimitiveBudget_of_raw_bounds _ A 1 0 M le_rfl le_rfl le_rfl

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
variable (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))

theorem principalNormalizedSource_law :
    (principalNormalizedSource hK hT hγ hlarge).source.toPMF.map (fun x => (x none : ℤ)) =
      principalIntegerPMF K T γ hK hT hγ hlarge :=
  normalizedScalarCubeSourceOfIntegerPMF_law
    (principalIntervalLength K T γ) (principalIntervalLength_pos hK hT hγ)
    (principalIntegerPMF K T γ hK hT hγ hlarge)
    (fun k hk => principalIntervalLength_support hK hT hγ hlarge hk)
    (principalIntervalWeight K T γ) 16 (128 * probabilityProfileLipschitz) (by norm_num)
    (principalIntervalWeight_range hK hT hγ hlarge)
    (principalIntervalWeight_lipschitz hK hT hγ hlarge)
    (principalIntervalWeight_grid hK hT hγ hlarge)

theorem principalNormalizedSource_primitive (A : ℝ≥0) :
    ScalarCubePrimitiveBudget (principalNormalizedSource hK hT hγ hlarge) A
      (scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1) :=
  scalarCubePrimitiveBudget_of_raw_bounds _ A 16 (128 * probabilityProfileLipschitz) 1
    le_rfl le_rfl le_rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedScalarLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)

theorem allocatedPrincipalNormalizedSource_primitive (A : ℝ≥0) :
    ScalarCubePrimitiveBudget (allocatedPrincipalNormalizedSource B U basis hR S j i hactive) A
      (scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1) :=
  principalNormalizedSource_primitive _ _ _ _ A

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3

theorem principalIntervalLength_mul_scale_bounds {K T γ : ℝ}
    (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T)) :
    2 * γ * K ≤ (principalIntervalLength K T γ : ℝ) * T ∧
      (principalIntervalLength K T γ : ℝ) * T ≤ 4 * γ * K := by
  have hb := principalIntervalLength_bounds hK hT hγ hlarge
  constructor
  · calc
      2 * γ * K = (2 * γ * (K / T)) * T := by field_simp
      _ ≤ (principalIntervalLength K T γ : ℝ) * T := mul_le_mul_of_nonneg_right hb.1 hT.le
  · calc
      (principalIntervalLength K T γ : ℝ) * T ≤ (4 * γ * (K / T)) * T :=
        mul_le_mul_of_nonneg_right hb.2 hT.le
      _ = 4 * γ * K := by field_simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PrincipalCoefficientPositiveSupport
namespace OAI

section

namespace Erdos3

theorem principalNormalizedSource_positive_support {K T γ : ℝ}
    (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))
    (z : IntegerScalarCubeBox Empty (principalNormalizedSource hK hT hγ hlarge).length)
    (hz : (principalNormalizedSource hK hT hγ hlarge).source.weight z ≠ 0) :
    ((principalNormalizedSource hK hT hγ hlarge).length : ℝ) / 4 ≤ (z none : ℝ) := by
  have hsupport : z ∈ (principalNormalizedSource hK hT hγ hlarge).source.toPMF.support := by
    intro hzero
    apply hz
    rw [← FiniteProbabilityWeights.toPMF_toReal, hzero]
    rfl
  have hmap : (z none : ℤ) ∈
      ((principalNormalizedSource hK hT hγ hlarge).source.toPMF.map
        (fun x => (x none : ℤ))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨z, hsupport, rfl⟩
  rw [principalNormalizedSource_law] at hmap
  have hb := (principalIntegerPMF_support hK hT hγ hlarge hmap).1
  have he : T * (z none : ℝ) / K = (z none : ℝ) / (K / T) := by field_simp
  rw [he] at hb
  have hlo := (lt_div_iff₀ (div_pos hK hT)).mp hb
  have hlength := (principalIntervalLength_bounds hK hT hγ hlarge).2
  change (principalIntervalLength K T γ : ℝ) / 4 ≤ _
  linarith

namespace VectorPolynomial

theorem allocatedPrincipalNormalizedSource_positive_support {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (z : IntegerScalarCubeBox Empty (allocatedPrincipalNormalizedSource B U basis hR S j i hactive).length)
    (hz : (allocatedPrincipalNormalizedSource B U basis hR S j i hactive).source.weight z ≠ 0) :
    ((allocatedPrincipalNormalizedSource B U basis hR S j i hactive).length : ℝ) / 4 ≤
      (z none : ℝ) :=
  principalNormalizedSource_positive_support _ _ _ _ z hz

end VectorPolynomial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPrincipalSourceScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)

local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

theorem allocatedPrincipalNormalizedSource_scale_bounds :
    2 * gamma * (basisAxisScale (basis j) i : ℝ) ≤
        ((csource).length : ℝ) * (S.value : ℝ) ^ (j.val + 1) ∧
      ((csource).length : ℝ) * (S.value : ℝ) ^ (j.val + 1) ≤
        4 * gamma * (basisAxisScale (basis j) i : ℝ) := by
  change 2 * gamma * (basisAxisScale (basis j) i : ℝ) ≤
      (principalIntervalLength (basisAxisScale (basis j) i) ((S.value : ℝ) ^ (j.val + 1)) gamma : ℝ) *
        (S.value : ℝ) ^ (j.val + 1) ∧ _
  exact principalIntervalLength_mul_scale_bounds
    (by exact_mod_cast basisAxisScale_pos (basis j) i)
    (pow_pos (by exact_mod_cast S.positive) _) (principalProfileSize_pos (hR j) _)
    (integerAxisPrincipal_width (Nat.zero_lt_succ _) S.positive
      (principalProfileSize_pos (hR j) _) (S.gap j i hactive))

theorem allocatedPrincipalNormalizedSource_grid_ratio {M : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hM : (M : ℝ) ≤ C * basisAxisScale (basis j) i) :
    (M : ℝ) / (((csource).length : ℝ) * (S.value : ℝ) ^ (j.val + 1)) ≤
      C / (2 * gamma) := by
  have hgamma : 0 < gamma := principalProfileSize_pos (hR j) _
  have hlength : 0 < ((csource).length : ℝ) := Nat.cast_pos.mpr (csource).length_pos
  have hscale : 0 < (S.value : ℝ) ^ (j.val + 1) :=
    pow_pos (by exact_mod_cast S.positive) _
  apply (div_le_iff₀ (mul_pos hlength hscale)).mpr
  calc
    (M : ℝ) ≤ C * basisAxisScale (basis j) i := hM
    _ = (C / (2 * gamma)) * (2 * gamma * basisAxisScale (basis j) i) := by field_simp
    _ ≤ (C / (2 * gamma)) * (((csource).length : ℝ) * (S.value : ℝ) ^ (j.val + 1)) :=
      mul_le_mul_of_nonneg_left
        (allocatedPrincipalNormalizedSource_scale_bounds B U basis hR S j i hactive).1
        (div_nonneg hC (by positivity))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedGridSpectrumSize
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedGrid_modulus_cardinality (j : Fin m) (i : Fin (n j))
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    {C : ℝ} {M : ℕ} (hC : 0 ≤ C) (hM : (M : ℝ) ≤ C * basisAxisScale (basis j) i)
    (d : ℕ) :
    (M : ℝ) ^ d ≤ C ^ d * (S.value : ℝ) ^ ((layerTailDegree m + 1) * d) := by
  change basisAxisScale (basis j) i ≤ S.value ^ (layerTailDegree m + 1) at hgrid
  have hK : (basisAxisScale (basis j) i : ℝ) ≤
      (S.value : ℝ) ^ (layerTailDegree m + 1) := by exact_mod_cast hgrid
  calc
    (M : ℝ) ^ d ≤ (C * (S.value : ℝ) ^ (layerTailDegree m + 1)) ^ d :=
      pow_le_pow_left₀ (Nat.cast_nonneg M)
        (hM.trans (mul_le_mul_of_nonneg_left hK hC)) d
    _ = C ^ d * (S.value : ℝ) ^ ((layerTailDegree m + 1) * d) := by
      rw [mul_pow, ← pow_mul]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedResidueInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (a : D) (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ L ⟨a, b, v⟩)

local notation "sources" => principalSupportedAxisSources B h L hL q hq r a hsize

omit [Fintype D] [DecidableEq D] [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] in
theorem principalSupportedAxisSources_primitive (b : B a) (v : Fin (h a)) (A : ℝ≥0) :
    ScalarCubePrimitiveBudget ((sources) b v) A (scalarCubePrimitiveEnvelope α A 1 0 q) :=
  normalizedUniformCubeSource_primitive α (L ⟨a, b, v⟩) q (hL ⟨a, b, v⟩) (fun _ => q)
    (r ⟨a, b, v⟩) (fun _ => hq) (fun _ => le_rfl) (hsize b v) A

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.DenseSliceGridScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem dense_slice_product_ratio {n : ℕ} {δ S C M V : ℝ} (H : Fin n → ℝ)
    (hδ : 0 < δ) (hS : 0 < S) (hC : 0 < C) (hM : 0 ≤ M)
    (hH : ∀ j, δ * S ≤ H j)
    (hbase : M / (C * S ^ n) ≤ V) :
    M / (C * ∏ j, H j) ≤ V / δ ^ n := by
  have hp : δ ^ n * S ^ n ≤ ∏ j, H j := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow] using
      Finset.prod_le_prod (s := Finset.univ) (f := fun _ : Fin n => δ * S) (g := H)
        (fun _ _ => (mul_pos hδ hS).le) (fun j _ => hH j)
  have hd : 0 < δ ^ n * (C * S ^ n) := by positivity
  have hden : δ ^ n * (C * S ^ n) ≤ C * ∏ j, H j := by
    simpa only [mul_left_comm, mul_assoc] using mul_le_mul_of_nonneg_left hp hC.le
  calc
    M / (C * ∏ j, H j) ≤ M / (δ ^ n * (C * S ^ n)) :=
      div_le_div_of_nonneg_left hM hd hden
    _ = (M / (C * S ^ n)) / δ ^ n := by ring
    _ ≤ V / δ ^ n := div_le_div_of_nonneg_right hbase (pow_pos hδ _).le

theorem dense_slice_grid_cardinality {M C S δ : ℝ} (d t : ℕ)
    (hδ : 0 < δ) (hbase : M ^ d ≤ C ^ d * S ^ t) :
    M ^ d ≤ (C ^ d / δ ^ t) * (δ * S) ^ t := by
  calc
    M ^ d ≤ C ^ d * S ^ t := hbase
    _ = _ := by rw [mul_pow]; field_simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidueGrid
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "coeff" => (fun _ : B (Sigma.mk j (Sum.inr i)) =>
  allocatedPrincipalNormalizedSource B U basis hR S j i hactive)
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) hsize
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

theorem allocatedSupportedSlicedGridDensity_approximation_on_cover_s2_oai
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * S.value ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {C ε : ℝ} {M : ℕ} [NeZero M] (hC : 0 ≤ C)
    (hMK : (M : ℝ) ≤ C * basisAxisScale (basis j) i)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let V := (C / (2 * gamma)) / δ ^ (j.val + 1)
    let t := (layerTailDegree m + 1) * rows.card
    let W := C ^ rows.card / δ ^ t
    let F := positiveModerateSpectrumCover rows M j.val P V (δ * S.value)
      (positiveModerateRetainedBias j.val rows.card t P V W ε);
      (F.card : ℝ) ≤ positiveModerateSpectrumCardBudget j.val rows.card t P V W ε ∧
      ∀ shift z : rows → ℤ,
        ‖(allocatedSupportedSlicedGridDensity B U basis hR hσ S q r H step c hH hsubset hcell j i M rows shift z : ℂ) -
          weightedAffineModerateGridApproximation coeff sources lower strides
            (basisAxisScale (basis j) i) M rows (fun _ => 0) shift z F‖ ≤
          ((basisAxisScale (basis j) i : ℝ) / M) ^ rows.card * ε := by
  intro V t W F
  have hc := (allocatedPrincipalNormalizedSource_primitive B U basis hR S j i hactive A).mono hcP
  have hs (b : B ⟨j,Sum.inr i⟩) (v : Fin (j.val + 1)) :=
    (principalSupportedAxisSources_primitive B (layerSamplerDegree I n) H hH q hq r
      ⟨j,Sum.inr i⟩ hsize b v A).mono hsP
  have hgamma : 0 < gamma := principalProfileSize_pos (hR j) _
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hscale (b : B ⟨j,Sum.inr i⟩) :
      (M : ℝ) / (((coeff b).length : ℝ) * ∏ v, (((sources) b v).length : ℝ)) ≤ V := by
    exact dense_slice_product_ratio (fun v => (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)) hδ
      (Nat.cast_pos.mpr S.positive) (Nat.cast_pos.mpr (coeff b).length_pos) (Nat.cast_nonneg M)
      (hlength b) (allocatedPrincipalNormalizedSource_grid_ratio B U basis hR S j i hactive hC hMK)
  have hcard : (M : ℝ) ^ rows.card ≤ W * (δ * S.value) ^ t :=
    dense_slice_grid_cardinality rows.card t hδ
      (allocatedGrid_modulus_cardinality B U basis S j i hgrid hC hMK rows.card)
  obtain ⟨hF, he⟩ := positiveAffineModerate_grid_approximation_on_cover_s2 coeff sources lower strides A hA
    hc.one_le (fun _ => hc) hs (fun b v _ => hstep b v) (fun b v _ => hstride b v)
    (fun _ z hz => allocatedPrincipalNormalizedSource_positive_support B U basis hR S j i hactive z hz)
    hV hW (mul_pos hδ (Nat.cast_pos.mpr S.positive)).le hε hε1 hlength
    (basisAxisScale (basis j) i) M t hscale rows hrows hB hcard
  refine ⟨hF,fun shift z => ?_⟩
  have hlaw := allocatedSupportedSlicedResidueJetPMF_source_s2 B U basis hR hσ S q hq r H step c hH hsubset hcell
    j i hactive hsize rows shift
  have hd := integerGridDensity_eq_of_pmf_image (weightedModerateIntegerProductSource coeff sources)
    (weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift)
    _ hlaw (basisAxisScale (basis j) i) M z
  have hd' : integerGridDensity (weightedModerateIntegerProductSource coeff sources)
      (weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift)
      (basisAxisScale (basis j) i) M z =
        allocatedSupportedSlicedGridDensity B U basis hR hσ S q r H step c hH hsubset hcell j i M rows shift z := by
    simpa only [allocatedSupportedSlicedGridDensity, Fintype.card_coe] using hd
  rw [← hd']
  exact he shift z

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedGridDensity_approximation_on_cover_s2_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedGridDensity_approximation_on_cover_s2_oai.{u_1, u_2, u_3, u_4, u_5}
