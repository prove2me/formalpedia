-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocated_short_physical_certified_bad_product_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:45:24.569019+00:00
-- url     : https://prove2.me/submissions/eb66aca9-0f3e-408a-8506-d1545b20e3b3

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218
import Definitions.Def_OAIE3v2B261
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineProductMixed_primePower_event_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_spatial_witness_comparison_s2
import Theorems.Thm_OAI_Erdos3_selectedResidueDensityPMF_stride_quantitative_badPrimeProduct_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SigmaProductMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem sigmaProductMeasure_flatten {D : Type*} [Fintype D] {I : D → Type*}
    [∀ d, Fintype (I d)] {X : (Σ d, I d) → Type*}
    [∀ s, MeasurableSpace (X s)] (μ : ∀ s, Measure (X s)) [∀ s, IsProbabilityMeasure (μ s)] :
    (Measure.pi (fun d => Measure.pi (fun i => μ ⟨d, i⟩))).map
      (fun x (s : Σ d, I d) => x s.1 s.2) = Measure.pi μ := by
  have hm : Measurable (fun (x : ∀ d i, X ⟨d, i⟩) (s : Σ d, I d) => x s.1 s.2) :=
    measurable_pi_iff.mpr (fun index =>
      (measurable_pi_apply index.2).comp (measurable_pi_apply index.1))
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have he : (fun (x : ∀ d i, X ⟨d, i⟩) (s : Σ d, I d) => x s.1 s.2) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun d => Set.univ.pi (fun i => s ⟨d, i⟩)) := by
    ext x
    constructor
    · intro hx d _ i _
      exact hx ⟨d, i⟩ (Set.mem_univ _)
    · intro hx t _
      exact hx t.1 (Set.mem_univ _) t.2 (Set.mem_univ _)
  rw [he, Measure.pi_pi]
  simp only [Measure.pi_pi, Fintype.prod_sigma]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueApproximation
namespace OAI

section

namespace Erdos3

theorem residueSmoothIndexPMF_eq_independent {K I : Type*} [Fintype K] [Fintype I]
    (residue : K × I → ℤ) (modulus : I → ℕ) (hmodulus : ∀ j, 0 < modulus j)
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) :
    residueSmoothIndexPMF residue modulus hmodulus V hV hZ =
      independentProductPMF (residueSmoothScalarPMFs residue modulus hmodulus V hV hZ) :=
  shiftedSmoothProductPMF_eq_independent
    (residueProfileCenter residue modulus) (residueProfileWidth modulus V)
    (residueProfileWidth_pos modulus V hmodulus hV) hZ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteDependentPMFBind
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pmf_bind_pair_apply {X Y : Type*} (p : PMF X) (q : PMF Y) (z : X × Y) :
    (p.bind (fun x => q.map (fun y => (x, y)))) z = p z.1 * q z.2 := by
  rw [PMF.bind_apply, tsum_eq_single z.1]
  · congr 1
    exact pmf_map_injective_at q (fun y => (z.1, y))
      (fun _ _ h => congrArg Prod.snd h) z.2
  · intro x hx
    have hr : z ∉ Set.range (fun y => (x, y)) := by
      rintro ⟨y, he⟩
      exact hx (congrArg Prod.fst he)
    rw [pmf_map_zero_off_range _ _ _ hr, mul_zero]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StrideSelectedResidueBadProduct
namespace OAI

section

namespace Erdos3

theorem quantitativeBadPrimeRadius_error {E : ℝ} (hE : 0 ≤ E) (Q : ℕ) (hQ : 1 ≤ Q) :
    let R := quantitativeBadPrimeRadius E
    0 < Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2)) ∧
    2 / (9 * (R : ℝ) ^ 9) + ((Q : ℝ) + (R : ℝ) ^ 2) *
      (Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))) ≤ Real.exp (-E) := by
  dsimp only
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hden : 0 < (Q : ℝ) + (quantitativeBadPrimeRadius E : ℝ) ^ 2 := by positivity
  refine ⟨by positivity, ?_⟩
  have heq : ((Q : ℝ) + (quantitativeBadPrimeRadius E : ℝ) ^ 2) *
      (Real.exp (-E) / (2 * ((Q : ℝ) + (quantitativeBadPrimeRadius E : ℝ) ^ 2))) =
      Real.exp (-E) / 2 := by field_simp
  rw [heq]
  linarith [(quantitativeBadPrimeRadius_bounds hE).2.2]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem column_stride_factorization_le_product {X : Type*} [Fintype X]
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x) (x : X) (p : ℕ) :
    (stride x).factorization p ≤ (∏ x, stride x).factorization p := by
  have hprod : (∏ x, stride x) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun x _ => (hstride x).ne')
  exact (Nat.factorization_le_iff_dvd (hstride x).ne' hprod).mpr
    (Finset.dvd_prod_of_mem stride (Finset.mem_univ x)) p

theorem column_stride_depth_lt_of_product_stride {X : Type*} [Fintype X]
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x) {p a : ℕ}
    (ha : 2 * (∏ x, stride x).factorization p < a) (x : X) :
    2 * (stride x).factorization p < a :=
  (Nat.mul_le_mul_left 2 (column_stride_factorization_le_product stride hstride x p)).trans_lt ha

theorem column_stride_depth_le_of_product_stride {X : Type*} [Fintype X]
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x) {p a : ℕ}
    (ha : 2 * (∏ x, stride x).factorization p < a) (x : X) :
    2 * (stride x).factorization p ≤ a :=
  (column_stride_depth_lt_of_product_stride stride hstride ha x).le

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PhysicalBadProductErrorBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem physicalBadProductAccuracy_pos (E Vlog : ℝ) :
    0 < physicalBadProductAccuracy E Vlog := Real.exp_pos _

theorem physicalBadProductAccuracy_inv (E Vlog : ℝ) :
    (physicalBadProductAccuracy E Vlog)⁻¹ = Real.exp (Vlog + 3 * E + 16) := by
  unfold physicalBadProductAccuracy
  rw [Real.exp_neg, inv_inv]

private theorem exp_eight_ge : (128 : ℝ) ≤ Real.exp 8 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h1 8
  have he : Real.exp (8 : ℝ) = Real.exp 1 ^ 8 := by
    simp
  rw [he]
  norm_num at hpow ⊢
  linarith

theorem physicalBadProductAccuracy_budget {E Vlog : ℝ}
    (hE : 0 ≤ E) (hVlog : 0 ≤ Vlog) (Q : ℕ) (hQ : 1 ≤ Q)
    (hQexp : (Q : ℝ) ≤ Real.exp Vlog) :
    let κ := physicalBadProductAccuracy E Vlog
    let R := quantitativeBadPrimeRadius E
    let η := Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))
    0 < κ ∧ κ⁻¹ = Real.exp (Vlog + 3 * E + 16) ∧
      2 * κ + κ ≤ 1 / 2 ∧ 128 * κ ≤ η ∧
      12 * (2 * κ + κ) + κ ≤ η := by
  dsimp only
  let T := Vlog + 3 * E + 8
  let η := Real.exp (-E) / (2 * ((Q : ℝ) + (quantitativeBadPrimeRadius E : ℝ) ^ 2))
  have hη : 0 < η := (quantitativeBadPrimeRadius_error hE Q hQ).1
  have hi : 1 / η ≤ Real.exp T :=
    (quantitativeBadPrimeRadius_witness_budget hE hVlog Q hQexp).2
  have hlo : Real.exp (-T) ≤ η := by
    rw [Real.exp_neg, ← one_div]
    apply (div_le_iff₀ (Real.exp_pos T)).mpr
    have hh := (div_le_iff₀ hη).mp hi
    simpa only [mul_comm] using hh
  have heq : physicalBadProductAccuracy E Vlog = Real.exp (-T) / Real.exp 8 := by
    rw [physicalBadProductAccuracy, ← Real.exp_sub]
    congr 1
    dsimp [T]
    ring
  have h128 : 128 * physicalBadProductAccuracy E Vlog ≤ η := by
    rw [heq]
    apply le_trans _ hlo
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (Real.exp_pos 8)).mpr
    have h := mul_le_mul_of_nonneg_left exp_eight_ge (Real.exp_pos (-T)).le
    nlinarith
  have hκ := physicalBadProductAccuracy_pos E Vlog
  have hκsmall : physicalBadProductAccuracy E Vlog ≤ 1 / 128 := by
    have hT : 0 ≤ T := by dsimp [T]; linarith
    have hl : Real.exp (-T) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hT)
    have hh : physicalBadProductAccuracy E Vlog * Real.exp 8 = Real.exp (-T) := by
      rw [heq, div_mul_cancel₀ _ (Real.exp_pos 8).ne']
    have h := mul_le_mul_of_nonneg_left exp_eight_ge hκ.le
    nlinarith
  refine ⟨hκ, physicalBadProductAccuracy_inv E Vlog, ?_, h128, ?_⟩
  · linarith
  · linarith

end Erdos3

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalScalarSourceEnvelope
namespace OAI

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedArrayReference
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem mixedScalarArrayLaw_probability {I Z J : Type*} [Fintype I] [Fintype Z] [Fintype J]
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Z → J → PMF ℤ) :
    IsProbabilityMeasure (mixedScalarArrayLaw c w p) := by
  let : ∀ i j, IsProbabilityMeasure (affineCoefficientMeasure (c i j) (w i j)) :=
    fun i j => affineCoefficientMeasure_probability _ (hw i j)
  unfold mixedScalarArrayLaw
  infer_instance

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

theorem allocatedPrincipalNormalizedSource_law (b : B ⟨j, Sum.inr i⟩) :
    (allocatedPrincipalNormalizedSource B U basis hR S j i hactive).source.toPMF.map
      (fun x => (x none : ℤ)) =
      allocatedLayerIntegerPMFs B U basis hR hσ S j i
        (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) := by
  have hmem : principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b ∈
      layerIntegerPrincipalSlots (G := G) B j i :=
    (mem_principalCoefficientSlots _ _ _).mpr ⟨b, rfl⟩
  have hne : principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b ≠
      constantCoefficientSlot (LayerSamplerVariables G I n B) (j.val + 1) := by
    intro he
    rw [he] at hmem
    exact (layerIntegerPrincipalSlots_not_constant B j i) hmem
  unfold allocatedPrincipalNormalizedSource
  rw [principalNormalizedSource_law]
  symm
  simp only [allocatedLayerIntegerPMFs, allocatedProjectionPMFs,
    allocatedIntegerPolynomialCoordinatePMF, integerPolynomialCoordinatePMF]
  split_ifs with hc hp
  · exact False.elim (hne hc)
  · simp only [integerAxisPrincipalPMF, hactive, ↓reduceDIte]
  · exact False.elim (hp hmem)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndependentProductPMFSum
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem independentProductPMF_sum {A B X : Type*} [Fintype A] [Fintype B]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : A ⊕ B → PMF X) :
    independentProductPMF p =
      (independentProductPMF (fun a => p (Sum.inl a))).bind (fun a =>
        (independentProductPMF (fun b => p (Sum.inr b))).map (Sum.elim a)) := by
  ext z
  have hz : Sum.elim (fun a => z (Sum.inl a)) (fun b => z (Sum.inr b)) = z := by
    funext q
    cases q <;> rfl
  have hinj (a : A → X) : Function.Injective (Sum.elim a : (B → X) → A ⊕ B → X) := by
    intro x y h
    funext b
    exact congrFun h (Sum.inr b)
  rw [PMF.bind_apply, tsum_eq_single (fun a => z (Sum.inl a))]
  · have hm := pmf_map_injective_at (independentProductPMF (fun b => p (Sum.inr b)))
      (Sum.elim (fun a => z (Sum.inl a))) (hinj (fun a => z (Sum.inl a)))
      (fun b => z (Sum.inr b))
    rw [hz] at hm
    rw [hm]
    simp only [independentProductPMF_apply, Fintype.prod_sum_type]
  · intro a ha
    have hr : z ∉ Set.range (Sum.elim a : (B → X) → A ⊕ B → X) := by
      rintro ⟨b, he⟩
      apply ha
      funext i
      exact congrFun he (Sum.inl i)
    rw [pmf_map_zero_off_range _ _ _ hr, mul_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedCoefficientSampler
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedCoefficientSource_probability :
    IsProbabilityMeasure (allocatedCoefficientSource B U b hR hσ S) := by
  let : ∀ j, IsProbabilityMeasure (mixedScalarArrayLaw (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j)) :=
    fun j => mixedScalarArrayLaw_probability _ _ (allocatedLayerWidths_pos B U b hR hσ S j) _
  exact Measure.pi.instIsProbabilityMeasure _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ModularCoefficientBadPrimeProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem modularCoefficientPrimeThreshold_two_le (s : ℕ) :
    2 ≤ modularCoefficientPrimeThreshold s := le_max_left _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedCoefficientIntegerMarginal
namespace OAI

section

namespace Erdos3
open MeasureTheory

theorem mixedScalarArrayLaw_integer_marginal {I Z Q : Type*}
    [Fintype I] [Fintype Z] [Fintype Q]
    (c w : I → Q → ℝ) (hw : ∀ i q, 0 < w i q) (p : Z → Q → PMF ℤ) :
    MeasurePreserving Prod.snd (mixedScalarArrayLaw c w p)
      (Measure.pi (fun z => Measure.pi (fun q => (p z q).toMeasure))) := by
  let : ∀ i q, IsProbabilityMeasure (affineCoefficientMeasure (c i q) (w i q)) :=
    fun i q => affineCoefficientMeasure_probability _ (hw i q)
  exact measurePreserving_snd

theorem pmf_bind_pair_toMeasure {X Y : Type*} [Countable X] [Countable Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (p : PMF X) (q : PMF Y) :
    (p.bind (fun x => q.map (fun y => (x, y)))).toMeasure = p.toMeasure.prod q.toMeasure := by
  apply Measure.ext_of_singleton
  rintro ⟨x, y⟩
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), pmf_bind_pair_apply,
    ← Set.singleton_prod_singleton, Measure.prod_prod]
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

namespace VectorPolynomial
open Module Submodule
open scoped BigOperators Classical

theorem coefficientIntegerScalars_measurePreserving {K : Type*} [Fintype K] {m : ℕ}
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (hw : ∀ j i q, 0 < w j i q)
    (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ) :
    MeasurePreserving coefficientIntegerScalars
      (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j)))
      (Measure.pi (fun q : CoefficientIntegerScalarIndex K n => (p q.1 q.2.2 q.2.1).toMeasure)) := by
  let μ := fun q : CoefficientIntegerScalarIndex K n => (p q.1 q.2.2 q.2.1).toMeasure
  have hrow (j : Fin m) : MeasurePreserving
      (fun a : (I j → BoundedCoefficientExponent K (j.val + 1) → ℝ) ×
        (Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → ℤ) =>
          fun q : BoundedCoefficientExponent K (j.val + 1) × Fin (n j) => a.2 q.2 q.1)
      (mixedScalarArrayLaw (c j) (w j) (p j))
      (Measure.pi (fun q => μ ⟨j, q⟩)) := by
    exact ((finiteArray_uncurry_measurePreserving (fun q i => (p j i q).toMeasure)).comp
      (finiteArrayTranspose_measurePreserving (fun i q => (p j i q).toMeasure))).comp
        (mixedScalarArrayLaw_integer_marginal (c j) (w j) (hw j) (p j))
  have houter := measurePreserving_pi
    (fun j => mixedScalarArrayLaw (c j) (w j) (p j))
    (fun j => Measure.pi (fun q => μ ⟨j, q⟩)) hrow
  have hflat : MeasurePreserving
      (fun (x : ∀ j : Fin m, BoundedCoefficientExponent K (j.val + 1) × Fin (n j) → ℤ)
        (q : CoefficientIntegerScalarIndex K n) => x q.1 q.2)
      (Measure.pi (fun j => Measure.pi (fun q => μ ⟨j, q⟩))) (Measure.pi μ) :=
    ⟨measurable_pi_iff.mpr (fun q => (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)),
      sigmaProductMeasure_flatten μ⟩
  exact hflat.comp houter

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedCoefficientSource_integer_measurePreserving :
    MeasurePreserving coefficientIntegerScalars
      (allocatedCoefficientSource B U b hR hσ S)
      (allocatedCoefficientIntegerPMF B U b hR hσ S).toMeasure := by
  simpa only [allocatedCoefficientSource, allocatedCoefficientIntegerPMF,
    independentProductPMF, Measure.toPMF_toMeasure] using
    coefficientIntegerScalars_measurePreserving
      (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
      (allocatedLayerWidths_pos B U b hR hσ S) (allocatedLayerIntegerPMFs B U b hR hσ S)

theorem allocatedCoefficientSource_integer_prod_measurePreserving
    {Deck : Type*} [Countable Deck] [MeasurableSpace Deck] [MeasurableSingletonClass Deck]
    (q : PMF Deck) :
    MeasurePreserving (Prod.map coefficientIntegerScalars id)
      ((allocatedCoefficientSource B U b hR hσ S).prod q.toMeasure)
      ((allocatedCoefficientIntegerPMF B U b hR hσ S).bind
        (fun a => q.map (fun deck => (a, deck)))).toMeasure := by
  let : IsProbabilityMeasure (allocatedCoefficientSource B U b hR hσ S) :=
    allocatedCoefficientSource_probability B U b hR hσ S
  rw [pmf_bind_pair_toMeasure]
  exact (allocatedCoefficientSource_integer_measurePreserving B U b hR hσ S).prod
    (MeasurePreserving.id q.toMeasure)

theorem allocatedCoefficientSource_integer_prod_eventProbability
    {Deck : Type*} [Countable Deck] [MeasurableSpace Deck] [MeasurableSingletonClass Deck]
    (q : PMF Deck)
    (E : (CoefficientIntegerScalarIndex (LayerSamplerVariables G I n B) n → ℤ) → Deck → Prop) :
    (((allocatedCoefficientSource B U b hR hσ S).prod q.toMeasure)
      {a | E (coefficientIntegerScalars a.1) a.2}).toReal =
      (((allocatedCoefficientIntegerPMF B U b hR hσ S).bind
        (fun a => q.map (fun deck => decide (E a deck)))) true).toReal := by
  let p := (allocatedCoefficientIntegerPMF B U b hR hσ S).bind
    (fun a => q.map (fun deck => (a, deck)))
  let obs := fun a : (CoefficientIntegerScalarIndex (LayerSamplerVariables G I n B) n → ℤ) × Deck =>
    decide (E a.1 a.2)
  have hp := allocatedCoefficientSource_integer_prod_measurePreserving B U b hR hσ S q
  have hset :
      ((allocatedCoefficientSource B U b hR hσ S).prod q.toMeasure)
        {a | E (coefficientIntegerScalars a.1) a.2} = p.toMeasure {a | E a.1 a.2} := by
    rw [← hp.map_eq, Measure.map_apply hp.measurable (Set.to_countable _).measurableSet]
    rfl
  have hobs : (p.map obs) true = p.toMeasure {a | E a.1 a.2} := by
    rw [← PMF.toMeasure_apply_singleton _ true (measurableSet_singleton _),
      ← PMF.toMeasure_map _ _ (measurable_of_countable _),
      Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    congr 1
    ext a
    simp [obs]
  rw [hset, ← hobs]
  congr 1
  simp only [p, PMF.map_bind, PMF.map_comp, obs, Function.comp_def]

theorem allocatedCoefficientSource_integer_prod_indicator
    {Deck : Type*} [Countable Deck] [MeasurableSpace Deck] [MeasurableSingletonClass Deck]
    (q : PMF Deck)
    (E : (CoefficientIntegerScalarIndex (LayerSamplerVariables G I n B) n → ℤ) → Deck → Prop) :
    (∫ a, (if E (coefficientIntegerScalars a.1) a.2 then (1 : ℝ) else 0)
      ∂(allocatedCoefficientSource B U b hR hσ S).prod q.toMeasure) =
      (((allocatedCoefficientIntegerPMF B U b hR hσ S).bind
        (fun a => q.map (fun deck => decide (E a deck)))) true).toReal := by
  have hp := allocatedCoefficientSource_integer_prod_measurePreserving B U b hR hσ S q
  have hs : MeasurableSet
      {a : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n × Deck |
        E (coefficientIntegerScalars a.1) a.2} :=
    (Set.to_countable {a : (CoefficientIntegerScalarIndex (LayerSamplerVariables G I n B) n → ℤ) × Deck |
      E a.1 a.2}).measurableSet.preimage hp.measurable
  calc
    _ = (((allocatedCoefficientSource B U b hR hσ S).prod q.toMeasure)
        {a | E (coefficientIntegerScalars a.1) a.2}).toReal := by
      simpa only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply, Measure.real] using
        integral_indicator_one (μ := (allocatedCoefficientSource B U b hR hσ S).prod q.toMeasure) hs
    _ = _ := allocatedCoefficientSource_integer_prod_eventProbability B U b hR hσ S q E

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankFullProductLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))

theorem allocatedLayerIntegerPMFs_principal_shiftedSmooth
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (b : B ⟨j, Sum.inr i⟩) :
    allocatedLayerIntegerPMFs B U basis hR hσ S j i
      (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) =
      shiftedSmoothCoefficientPMF (allocatedPrincipalRankCenter B U basis S j i)
        (allocatedPrincipalRankWidth B U basis S j i)
        (allocatedPrincipalRankWidth_pos B U basis hR S j i)
        (allocatedPrincipalRankMass_pos B U basis hR S j i hactive) := by
  have h := allocatedPrincipalNormalizedSource_law B U basis hR hσ S j i hactive b
  rw [allocatedPrincipalNormalizedSource, principalNormalizedSource_law] at h
  exact h.symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)

variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩)
    (noiseCenter noiseWidth : Fin L → X → ℝ)

theorem allocatedFullSmoothScalarPMF_selected
    (noisePMF : Option (LayerSamplerVariables G I n B) × X → PMF ℤ)
    (hnoiseWidth : ∀ l x, 0 < noiseWidth l x)
    (hnoiseMass : ∀ l x, 0 < shiftedSmoothSampleSum (noiseCenter l x) (noiseWidth l x))
    (hnoise : ∀ l x, noisePMF (some (.inl (spatial l)), x) =
      shiftedSmoothCoefficientPMF (noiseCenter l x) (noiseWidth l x)
        (hnoiseWidth l x) (hnoiseMass l x))
    (hactive : ∀ j (i : AllocatedCongruenceIntegerAxis inactive j),
      S.value ^ (j.val + 1) < basisAxisScale (basis j) i.val)
    (a : AllocatedSmoothRankCoefficientIndex X inactive L) :
    allocatedFullSmoothScalarPMF B U basis hR hσ S noisePMF
      (allocatedSmoothFullEmbedding inactive spatial block a) =
      shiftedSmoothCoefficientPMF
        (allocatedSelectedSmoothCenter B U basis S inactive noiseCenter a)
        (allocatedSelectedSmoothWidth B U basis S inactive noiseWidth a)
        (allocatedSelectedSmoothWidth_pos B U basis hR S inactive noiseWidth hnoiseWidth a)
        (allocatedSelectedSmoothMass_pos B U basis hR S inactive noiseCenter noiseWidth
          hnoiseMass hactive a) := by
  rcases a with ⟨j,(x | i),l⟩
  · exact hnoise l x.val
  · exact allocatedLayerIntegerPMFs_principal_shiftedSmooth B U basis hR hσ S j i.val
      (hactive j i) (block j ⟨.inr i.val,i.property⟩ l)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

theorem allocatedFullSmoothProductPMF_factorization
    {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)
    (noisePMF : Option (LayerSamplerVariables G I n B) × X → PMF ℤ) :
    independentProductPMF (allocatedFullSmoothScalarPMF B U basis hR hσ S noisePMF) =
      (independentProductPMF noisePMF).bind (fun noise =>
        (allocatedCoefficientIntegerPMF B U basis hR hσ S).map (Sum.elim noise)) :=
  independentProductPMF_sum (allocatedFullSmoothScalarPMF B U basis hR hσ S noisePMF)

theorem coefficientDeckScalar_uniform_test {K : Type*}
    {m : ℕ} {E : Fin m → Type*} (N : ℕ)
    [Fintype (CoefficientDeckResidues (K := K) E N)]
    [Fintype (CoefficientDeckScalarIndex K E → ZMod N)]
    {Y : Type*} (test : (CoefficientDeckScalarIndex K E → ZMod N) → Y) :
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) E N)).map
      (fun deck => test (coefficientDeckScalarEquiv deck)) =
      (PMF.uniformOfFintype (CoefficientDeckScalarIndex K E → ZMod N)).map test := by
  let e := coefficientDeckScalarEquiv (K := K) (E := E) (N := N)
  have he : (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) E N)).map e =
      PMF.uniformOfFintype (CoefficientDeckScalarIndex K E → ZMod N) := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [pmf_map_injective_at _ _ e.injective]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_congr e]
  have h := congrArg (fun p => p.map test) he
  simpa only [PMF.map_comp, Function.comp_def] using h

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedSpatialCoefficientReferenceLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedSpatialCoefficientReferenceLaw
    {X : Type*} [Fintype X] (q : ℕ) [NeZero q]
    (spatial : PMF (Option (LayerSamplerVariables G I n B) × X → ℤ))
    (deck : PMF (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q))
    (event : ((Option (LayerSamplerVariables G I n B) × X) → ZMod q) →
      CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop) :
    (∑' z, (spatial z).toReal *
      ∫ a : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
          CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q,
        (if event (fun v => (z v : ZMod q)) (coefficientSamplerChartResidues q a.1 a.2)
          then (1 : ℝ) else 0)
        ∂(allocatedCoefficientSource B U b hR hσ S).prod deck.toMeasure) =
    ((spatial.bind fun z => (allocatedCoefficientIntegerPMF B U b hR hσ S).bind
      fun a => deck.map fun r => decide
        (event (fun v => (z v : ZMod q)) (coefficientIntegerDeckChartResidues q a r))) true).toReal := by
  rw [pmf_bind_toReal]
  apply tsum_congr
  intro z
  congr 1
  exact allocatedCoefficientSource_integer_prod_indicator B U b hR hσ S deck
    (fun a r => event (fun v => (z v : ZMod q)) (coefficientIntegerDeckChartResidues q a r))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedShortRankWitnessWidth
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

theorem allocatedChartResiduePrimePowerWitness_integerDeck_iff
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,b.val⟩)
    (C : ℝ) (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (q : ℕ) [NeZero q] (hdiv : ∀ p : P, p.val ^ A p.val ∣ q)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (a : CoefficientIntegerScalarIndex (LayerSamplerVariables G I n B) n → ℤ)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q) :
    allocatedChartResiduePrimePowerWitness inactive C P A q hdiv
      (fun v => (noise v : ZMod q)) (coefficientIntegerDeckChartResidues q a r) ↔
    ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
      (allocatedMixedFullArray (Sum.elim noise a)
        (fun ⟨j,e,i⟩ => ((r j e i).val : ℤ)) (fun _ => 0)) := by
  let f := allocatedMixedFullArray (Sum.elim noise a)
    (fun ⟨j,e,i⟩ => ((r j e i).val : ℤ)) (fun _ => 0)
  have hchart : allocatedReadCoefficientChartResidues (fun i => (f i : ZMod q)) =
      coefficientIntegerDeckChartResidues q a r := by
    funext j e i
    cases i with
    | inl i => rfl
    | inr i =>
      change (((r j e i).val : ℤ) : ZMod q) = r j e i
      simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  have h := allocatedChartResiduePrimePowerWitness_iff_actual
    inactive spatial kernel block C P A q hdiv f
  rw [hchart] at h
  exact h

variable (B) {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedSpatialRankReferenceLaw
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,b.val⟩)
    (C : ℝ) (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (q : ℕ) [NeZero q] (hdiv : ∀ p : P, p.val ^ A p.val ∣ q)
    (noiseLaw : PMF (Option (LayerSamplerVariables G I n B) × X → ℤ)) :
    (∑' z, (noiseLaw z).toReal *
      ∫ a : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
          CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q,
        (if allocatedChartResiduePrimePowerWitness inactive C P A q hdiv
          (fun v => (z v : ZMod q)) (coefficientSamplerChartResidues q a.1 a.2)
          then (1 : ℝ) else 0)
        ∂(allocatedCoefficientSource B U b hR hσ S).prod
          (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q)).toMeasure) =
    ((noiseLaw.bind fun z => (allocatedCoefficientIntegerPMF B U b hR hσ S).bind
      fun a => (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q)).map
        fun r => decide (∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
          (allocatedMixedFullArray (Sum.elim z a)
            (fun ⟨j,e,i⟩ => ((r j e i).val : ℤ)) (fun _ => 0)))) true).toReal := by
  have h := allocatedSpatialCoefficientReferenceLaw B U b hR hσ S q noiseLaw
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q))
    (allocatedChartResiduePrimePowerWitness inactive C P A q hdiv)
  simpa only [allocatedChartResiduePrimePowerWitness_integerDeck_iff
    inactive spatial kernel block C P A q hdiv] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)

attribute [local instance] OAI.Erdos3.VectorPolynomial.spatialReferenceSmoothFintype
attribute [local instance] OAI.Erdos3.VectorPolynomial.spatialReferenceDeckFintype
attribute [local instance] OAI.Erdos3.VectorPolynomial.spatialReferenceDeckDecidableEq
theorem allocatedSpatialRank_cell_bind_eq
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (residue : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (V : Option (LayerSamplerVariables G I n B) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V)) (N : ℕ) [NeZero N]
    {Y : Type*}
    (test : (AllocatedFullSmoothCoefficientIndex G X I n B → ℤ) →
      (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N) → Y) :
    ((residueSmoothPMF residue stride hstride V hV hZ).bind fun noise =>
      (allocatedCoefficientIntegerPMF B U basis hR hσ S).bind fun a =>
        (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)).map
          fun deck => test (Sum.elim noise a) (coefficientDeckScalarEquiv deck)) =
    ((independentProductPMF (allocatedFullSmoothScalarPMF B U basis hR hσ S
      (residueSmoothScalarPMFs residue stride hstride V hV hZ))).bind fun z =>
        (PMF.uniformOfFintype
          (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N)).map
          fun deck => test (allocatedFullSmoothAffine (fun x => (stride x : ℤ)) residue z) deck) := by
  rw [allocatedFullSmoothProductPMF_factorization, PMF.bind_bind]
  simp_rw [PMF.bind_map]
  rw [residueSmoothPMF, residueSmoothIndexPMF_eq_independent, PMF.bind_map]
  apply congrArg (PMF.bind _)
  funext noise
  apply congrArg (PMF.bind _)
  funext a
  simp only [Function.comp_apply]
  have haff : Sum.elim (residueLatticeArray residue stride noise) a =
      allocatedFullSmoothAffine (fun x => (stride x : ℤ)) residue (Sum.elim noise a) := by
    funext t
    cases t <;> rfl
  rw [haff]
  exact coefficientDeckScalar_uniform_test N
    (test (allocatedFullSmoothAffine (fun x => (stride x : ℤ)) residue (Sum.elim noise a)))

end Erdos3.VectorPolynomial

end

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

theorem exists_allocated_physical_rank_witness_comparison
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
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ}
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
    (rankC : ℝ) (primes : Finset ℕ) [∀ p : primes, NeZero p.val] (depth : ℕ → ℕ)
    (hdiv : ∀ p : primes, p.val ^ depth p.val ∣ q)
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
          (if coefficientDeckChartEvent U bW b hb o q (allocatedChartResiduePrimePowerWitness inactive rankC primes depth q hdiv
            (fun v => (z v : ZMod q))) (sample z) then 1 else 0)) -
        (((selectedResidueSmoothPMF stride cells width hwidth hZ).bind fun z =>
          (allocatedCoefficientIntegerPMF B U b hR hσ S).bind fun a =>
            (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q)).map
              fun r => decide (∀ p : primes, allocatedActualModulusBad inactive spatial kernel block
                rankC (p.val ^ depth p.val) (allocatedMixedFullArray (Sum.elim z a)
                  (fun ⟨j,e,i⟩ => ((r j e i).val : ℤ)) (fun _ => 0)))) true).toReal| ≤
        12 * (2 * δ + ε) := by
  dsimp only
  obtain ⟨hD0, hZ, hDpos, hmass, hlower, hupper, he⟩ :=
    exists_allocated_spatial_witness_comparison_s2 B U bW b hb o S C V hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall q hq hP hmP hK hRP hσP hcount hI hn hJ hAP hLP
      hCP hVP hqP hδ hδP μ ν poly hp hm hPs hX hframe hqPs hε hρ hεPs hρPs stride hstride
      hSmax hSmaxPs hstrideMax H hsize hrank hRs cells hcells
      (allocatedChartResiduePrimePowerWitness inactive rankC primes depth q hdiv)
      width hwidth hwide hfreqPs hmassPs hsmallError
  have href := allocatedSpatialRankReferenceLaw (E := E) B U b hR hσ S inactive spatial kernel block
    rankC primes depth q hdiv (selectedResidueSmoothPMF stride cells width hwidth hZ)
  rw [href] at he
  exact ⟨hD0, hZ, hDpos, hmass, hlower, hupper, he⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable local instance shortSpatialReferenceSmoothFintype_recb3de_1 :
    Fintype (AllocatedFullSmoothCoefficientIndex G X I n B) := inferInstance
noncomputable local instance shortSpatialReferenceDeckFintype_recb3de_1 :
    Fintype (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := inferInstance
noncomputable local instance shortSpatialReferenceDeckDecidableEq_recb3de_1 :
    DecidableEq (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := Classical.decEq _
theorem allocatedShortPrincipalRank_active (j : Fin m)
    (i : AllocatedCongruenceIntegerAxis (allocatedShortAxis (I := I) U basis S.value) j) :
    S.value ^ (j.val + 1) < basisAxisScale (basis j) i.val := by
  exact Nat.lt_of_not_ge i.property

theorem allocatedShortRank_cell_event {L N D : ℕ} [NeZero N]
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis
      (allocatedShortAxis (I := I) U basis S.value) j, Fin L ↪ B ⟨j,b.val⟩)
    (hm : 0 < m) (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (residue : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (V : Option (LayerSamplerVariables G I n B) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue stride)
      (residueProfileWidth stride V))
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (hprime : ∀ p ∈ P, p.Prime) (hcover : ∀ p ∈ P, p ^ A p ∣ N)
    (hpositive : ∀ p ∈ P, 0 < A p)
    (hdeep : ∀ p ∈ P, ∀ x, 2 * (stride x).factorization p ≤ A p)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (hthreshold : ∀ p ∈ P, modularCoefficientPrimeThreshold m ≤ p ^ A p)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : P, p.val ^ A p.val) ≤ allocatedShortRankSelectedWidth B U basis S spatial stride V j) :
    (((residueSmoothPMF residue stride hstride V hV hZ).bind fun noise =>
      (allocatedCoefficientIntegerPMF B U basis hR hσ S).bind fun a =>
      (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)).map
        fun deck => decide (∀ p : P, allocatedActualModulusBad
          (allocatedShortAxis (I := I) U basis S.value) spatial kernel block C (p.val ^ A p.val)
          (allocatedMixedFullArray (Sum.elim noise a)
            (fun ⟨j,e,i⟩ => ((deck j e i).val : ℤ)) (fun _ => 0)))) true).toReal ≤
      1 / ((∏ p : P, p.val ^ A p.val : ℕ) : ℝ) ^ 10 +
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (∏ p : P, p.val ^ A p.val) /
          allocatedShortRankSelectedWidth B U basis S spatial stride V j := by
  let inactive := allocatedShortAxis (I := I) U basis S.value
  let noiseCenter : Fin L → X → ℝ :=
    fun l x => residueProfileCenter residue stride (some (.inl (spatial l)),x)
  let noiseWidth : Fin L → X → ℝ :=
    fun l x => residueProfileWidth stride V (some (.inl (spatial l)),x)
  let center := allocatedSelectedSmoothCenter B U basis S inactive noiseCenter
  let width := allocatedSelectedSmoothWidth B U basis S inactive noiseWidth
  let noisePMF := residueSmoothScalarPMFs residue stride hstride V hV hZ
  let laws := allocatedFullSmoothScalarPMF B U basis hR hσ S noisePMF
  have hnw : ∀ l x, 0 < noiseWidth l x :=
    fun l x => residueProfileWidth_pos stride V hstride hV _
  have hnm : ∀ l x, 0 < shiftedSmoothSampleSum (noiseCenter l x) (noiseWidth l x) :=
    fun l x => shiftedSmoothProductMass_coordinate_pos _ _
      (residueProfileWidth_pos stride V hstride hV) hZ _
  have hactive := allocatedShortPrincipalRank_active B U basis S
  have hw : ∀ j, 0 < width j :=
    allocatedSelectedSmoothWidth_pos B U basis hR S inactive noiseWidth hnw
  have hmasses : ∀ j, 0 < shiftedSmoothSampleSum (center j) (width j) :=
    allocatedSelectedSmoothMass_pos B U basis hR S inactive noiseCenter noiseWidth hnm hactive
  have hz : 0 < shiftedSmoothProductMass center width := by
    rw [shiftedSmoothProductMass_eq_prod _ _ hw]
    exact Finset.prod_pos (fun j _ => hmasses j)
  have hcoordinate : ∀ i, laws (allocatedSmoothFullEmbedding inactive spatial block i) =
      shiftedSmoothCoefficientPMF (center i) (width i) (hw i)
        (shiftedSmoothProductMass_coordinate_pos center width hw hz i) := by
    intro i
    exact allocatedFullSmoothScalarPMF_selected B U basis hR hσ S inactive spatial block
      noiseCenter noiseWidth noisePMF hnw hnm (fun _ _ => rfl) hactive i
  have h := allocatedAffineProductMixed_primePower_event_s2 inactive spatial kernel block
    (fun _ => 0) stride hstride residue laws hm center width hw hz hcoordinate
    P A hprime hcover hpositive hdeep hD hC hL hthreshold hlarge
  let test := fun (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → ℤ)
      (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N) =>
    decide (∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
      (allocatedMixedFullArray smooth (fun t => ((deck t).val : ℤ)) (fun _ => 0)))
  have he := allocatedSpatialRank_cell_bind_eq B U basis hR hσ S stride hstride residue V hV hZ N test
  exact (congrArg (fun p : PMF Bool => (p true).toReal) he).trans_le h

theorem allocatedShortRank_reference_event {L N D : ℕ} [NeZero N]
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis
      (allocatedShortAxis (I := I) U basis S.value) j, Fin L ↪ B ⟨j,b.val⟩)
    (hm : 0 < m) (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (V : Option (LayerSamplerVariables G I n B) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth stride V z)
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (hprime : ∀ p ∈ P, p.Prime) (hcover : ∀ p ∈ P, p ^ A p ∣ N)
    (hpositive : ∀ p ∈ P, 0 < A p)
    (hdeep : ∀ p ∈ P, ∀ x, 2 * (stride x).factorization p ≤ A p)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (hthreshold : ∀ p ∈ P, modularCoefficientPrimeThreshold m ≤ p ^ A p)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : P, p.val ^ A p.val) ≤ allocatedShortRankSelectedWidth B U basis S spatial stride V j) :
    (((selectedResidueSmoothPMF stride cells V hV hZ).bind fun noise =>
      (allocatedCoefficientIntegerPMF B U basis hR hσ S).bind fun a =>
      (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)).map
        fun deck => decide (∀ p : P, allocatedActualModulusBad
          (allocatedShortAxis (I := I) U basis S.value) spatial kernel block C (p.val ^ A p.val)
          (allocatedMixedFullArray (Sum.elim noise a)
            (fun ⟨j,e,i⟩ => ((deck j e i).val : ℤ)) (fun _ => 0)))) true).toReal ≤
      1 / ((∏ p : P, p.val ^ A p.val : ℕ) : ℝ) ^ 10 +
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (∏ p : P, p.val ^ A p.val) /
          allocatedShortRankSelectedWidth B U basis S spatial stride V j := by
  have hc (r : cells) : 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative stride r.val) stride)
      (residueProfileWidth stride V) := by
    rw [shiftedSmoothProductMass_eq_prod _ _ (residueProfileWidth_pos stride V hstride hV)]
    exact Finset.prod_pos (fun z _ => shiftedSmoothSampleSum_pos _ (hscale z))
  apply selectedResidueSmoothPMF_bind_le_of_cells stride hstride cells V hV hZ hc
  intro r
  exact allocatedShortRank_cell_event B U basis hR hσ S spatial kernel block hm stride hstride
    (boundedColumnResidueRepresentative stride r.val) V hV (hc r) P A hprime hcover hpositive
    hdeep hD hC hL hthreshold hlarge

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedPhysicalIntegerRankLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem exists_allocatedPhysical_integer_coefficient_read :
    ∃ read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        AllocatedActualCoefficientIndex G X I E n B → ℤ,
      ∀ z, allocatedReadNoise (read z) = z ∧
        (allocatedCoefficientDensity B U b hb o hR hσ S
          (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) ≠ 0 →
        ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
          ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
            coefficientDeckChartEvent U bW b hb o q event
              (affineCoefficientCoverSample U poly hm q (fun k x => (z (k,x) : ℝ))) ↔
            event (allocatedReadCoefficientChartResidues (fun i => (read z i : ZMod q)))) := by
  have hex (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
      ∃ f : AllocatedActualCoefficientIndex G X I E n B → ℤ,
        allocatedReadNoise f = z ∧
        (allocatedCoefficientDensity B U b hb o hR hσ S
          (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) ≠ 0 →
        ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
          ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
            coefficientDeckChartEvent U bW b hb o q event
              (affineCoefficientCoverSample U poly hm q (fun k x => (z (k,x) : ℝ))) ↔
            event (allocatedReadCoefficientChartResidues (fun i => (f i : ZMod q)))) := by
    by_cases hz : allocatedCoefficientDensity B U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) = 0
    · refine ⟨allocatedMixedFullArray (Sum.elim z (fun _ => 0)) (fun _ => 0) (fun _ => 0), rfl, ?_⟩
      intro h
      exact (h hz).elim
    · obtain ⟨x, hx, _⟩ := canonicalCoefficientDensity_recover_unique U b hb o
        (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
        (allocatedLayerIntegerPMFs B U b hR hσ S) hz
      have hsmall : ∀ a, |coefficientSamplerAmbientPoint U b o x a| < 1/2 := by
        intro a
        exact (hx.2 a.1.1).1 a.1.2 a.2
      obtain ⟨f, hfnoise, _hfint, hfevent⟩ := exists_allocatedCoefficient_integer_event_read
        U bW b hb o (affineSampleCoefficientArray U poly hm (fun k x => (z (k,x) : ℝ)))
        x hx.1 hsmall z
      refine ⟨f, hfnoise, ?_⟩
      intro _ q hq
      exact hfevent q hq
  choose read hread using hex
  exact ⟨read, hread⟩

variable [Fintype X]

theorem exists_allocatedPhysical_integer_rank_read
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
    (C : ℝ) :
    ∃ read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        AllocatedActualCoefficientIndex G X I E n B → ℤ,
      ∀ z, allocatedReadNoise (read z) = z ∧
        (allocatedCoefficientDensity B U b hb o hR hσ S
          (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) ≠ 0 →
        ∀ (P : Finset ℕ) (hP : ∀ p : P, NeZero p.val), letI := hP
          ∀ (A : ℕ → ℕ) (M : ℕ) (hM : 0 < M), letI : NeZero M := ⟨hM.ne'⟩
            ∀ hdiv : ∀ p : P, p.val ^ A p.val ∣ M,
              coefficientDeckChartEvent U bW b hb o M
                (allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
                  (fun v => (z v : ZMod M)))
                (affineCoefficientCoverSample U poly hm M (fun k x => (z (k,x) : ℝ))) ↔
              ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C
                (p.val ^ A p.val) (read z)) := by
  obtain ⟨read, hread⟩ := exists_allocatedPhysical_integer_coefficient_read
    B U bW b hb o S hR hσ poly hm
  refine ⟨read, ?_⟩
  intro z
  refine ⟨(hread z).1, ?_⟩
  intro hz P hP
  let := hP
  intro A M hM
  let : NeZero M := ⟨hM.ne'⟩
  intro hdiv
  have he := (hread z).2 hz M hM
    (allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
      (fun v => (z v : ZMod M)))
  apply he.trans
  have hn : allocatedReadNoise (fun i => (read z i : ZMod M)) =
      fun v => (z v : ZMod M) := by
    funext v
    change ((allocatedReadNoise (read z) v : ℤ) : ZMod M) = _
    rw [(hread z).1]
  rw [← hn]
  exact allocatedChartResiduePrimePowerWitness_iff_actual
    inactive spatial kernel block C P A M hdiv (read z)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedPhysicalCertifiedRankWitnessLaw
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

include bW hC hV in

theorem exists_allocated_physical_certified_rank_witness_law
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (cap : ℕ) (hcap : 0 < cap)
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
    (hcapP : (cap : ℝ) ≤ Real.exp P) (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
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
    (hcapPs : (cap : ℝ) ≤ Real.exp Ps)
    (hε : 0 < ε) (hρ : 0 < ρ) (hεPs : 1 / ε ≤ Real.exp Ps) (hρPs : 1 / ρ ≤ Real.exp Ps)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (hSmax : 0 ≤ Smax) (hSmaxPs : Smax ≤ Real.exp Ps) (hstrideMax : ∀ x, ((stride x * cap : ℕ) : ℝ) ≤ Smax)
    (H : X → ℝ)
    (hsize : ∀ x, Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (hcells : cells.Nonempty)
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ}
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
    (rankC : ℝ)
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)
    (hfreqPs : (4 * allocatedFourierLogBudget m P + 2)^4 ≤ Ps)
    (hmassPs : 4 * allocatedFourierLogBudget m P * (4 * allocatedFourierLogBudget m P + 2)^4 +
      allocatedFourierLogBudget m P ≤ Ps)
    (hsmallError : 2 * δ + ε ≤ 1 / 2) :
    let Dphysical := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      allocatedCoefficientDensity B U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
    ∃ read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        AllocatedActualCoefficientIndex G X I E n B → ℤ,
      (∀ z, allocatedReadNoise (read z) = z) ∧
      (∀ z, Dphysical z ≠ 0 →
        ∀ (primes : Finset ℕ) (hprimes : ∀ p : primes, NeZero p.val), letI := hprimes
          ∀ (depth : ℕ → ℕ) (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
            ∀ hdiv : ∀ p : primes, p.val ^ depth p.val ∣ q,
              coefficientDeckChartEvent U bW b hb o q
                (allocatedChartResiduePrimePowerWitness inactive rankC primes depth q hdiv
                  (fun v => (z v : ZMod q)))
                (affineCoefficientCoverSample U poly hm q (fun k x => (z (k,x) : ℝ))) ↔
              ∀ p : primes, allocatedActualModulusBad inactive spatial kernel block rankC
                (p.val ^ depth p.val) (read z)) ∧
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 2 * δ + ε ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      ∀ (primes : Finset ℕ) (hprimes : ∀ p : primes, NeZero p.val), letI := hprimes
        ∀ (depth : ℕ → ℕ) (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
        ∀ (_hqcap : q ≤ cap) (_hdiv : ∀ p : primes, p.val ^ depth p.val ∣ q),
        |(∑' z, (selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal *
            (if ∀ p : primes, allocatedActualModulusBad inactive spatial kernel block
              rankC (p.val ^ depth p.val) (read z) then (1 : ℝ) else 0)) -
          (((selectedResidueSmoothPMF stride cells width hwidth hZ).bind fun z =>
            (allocatedCoefficientIntegerPMF B U b hR hσ S).bind fun a =>
              (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q)).map
                fun r => decide (∀ p : primes, allocatedActualModulusBad inactive spatial kernel block
                  rankC (p.val ^ depth p.val) (allocatedMixedFullArray (Sum.elim z a)
                    (fun ⟨j,e,i⟩ => ((r j e i).val : ℤ)) (fun _ => 0)))) true).toReal| ≤
          12 * (2 * δ + ε) := by
  dsimp only
  let : NeZero cap := ⟨hcap.ne'⟩
  let emptyPrimes : Finset ℕ := ∅
  let : ∀ p : emptyPrimes, NeZero p.val := fun p =>
    False.elim (Finset.notMem_empty p.val p.property)
  obtain ⟨hD0, hZ, hDpos, hmass, hlower, hupper, _⟩ :=
    exists_allocated_physical_rank_witness_comparison B U bW b hb o S C V hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall cap hcap hP hmP hK hRP hσP hcount hI hn hJ hAP hLP
      hCP hVP hcapP hδ hδP μ ν poly hp hm hPs hX hframe hcapPs hε hρ hεPs hρPs stride hstride
      hSmax hSmaxPs hstrideMax H hsize hrank hRs cells hcells inactive spatial kernel block
      rankC emptyPrimes (fun _ => 0) (fun p => False.elim (Finset.notMem_empty p.val p.property))
      width hwidth hwide hfreqPs hmassPs hsmallError
  obtain ⟨read, hread⟩ := exists_allocatedPhysical_integer_rank_read
    B U bW b hb o S hR hσ poly hm inactive spatial kernel block rankC
  refine ⟨hD0, hZ, hDpos, read, fun z => (hread z).1,
    fun z hz => (hread z).2 hz, hmass, hlower, hupper, ?_⟩
  intro primes hprimes
  let := hprimes
  intro depth q hq
  let : NeZero q := ⟨hq.ne'⟩
  intro hqcap hdiv
  have hqP : (q : ℝ) ≤ Real.exp P := (Nat.cast_le.mpr hqcap).trans hcapP
  have hqPs : (q : ℝ) ≤ Real.exp Ps := (Nat.cast_le.mpr hqcap).trans hcapPs
  have hstrideq : ∀ x, ((stride x * q : ℕ) : ℝ) ≤ Smax := fun x =>
    (Nat.cast_le.mpr (Nat.mul_le_mul_left (stride x) hqcap)).trans (hstrideMax x)
  obtain ⟨_, _, _, _, _, _, he⟩ :=
    exists_allocated_physical_rank_witness_comparison B U bW b hb o S C V hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall q hq hP hmP hK hRP hσP hcount hI hn hJ hAP hLP
      hCP hVP hqP hδ hδP μ ν poly hp hm hPs hX hframe hqPs hε hρ hεPs hρPs stride hstride
      hSmax hSmaxPs hstrideq H hsize hrank hRs cells hcells inactive spatial kernel block
      rankC primes depth hdiv width hwidth hwide hfreqPs hmassPs hsmallError
  have hevent := selectedResidueDensityPMF_event_congr_of_density_ne_zero
    stride cells width hwidth hZ _ hD0 hDpos _ _
    (fun z hz => (hread z).2 hz primes hprimes depth q hq hdiv)
  rw [hevent] at he
  exact he

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCertifiedPhysicalBadProduct
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

variable (Elog Vlog : ℝ) (Q : ℕ)
local notation "κ" => physicalBadProductAccuracy Elog Vlog
local notation "Rbad" => quantitativeBadPrimeRadius Elog
local notation "cap" => (max Q (Rbad ^ 2) : ℕ)
local notation "inactive" => allocatedShortAxis (I := I) U b S.value

include bW hC hV in

theorem exists_allocated_short_physical_certified_bad_product_s2_oai
    (hElog : 0 ≤ Elog) (hVlog : 0 ≤ Vlog) (hQ : 1 ≤ Q)
    (hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (hmpos : 0 < m)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    {P : ℝ} (hP : 0 ≤ P) (hmP : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hbudgetP : Vlog + 3 * Elog + 16 ≤ P)
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
    {Ps ρ Rs Smax : ℝ} (hPs : 0 ≤ Ps) (hX : (Fintype.card X : ℝ) ≤ Ps)
    (hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Ps)
    (hbudgetPs : Vlog + 3 * Elog + 16 ≤ Ps)
    (hρ : 0 < ρ) (hρPs : 1 / ρ ≤ Real.exp Ps)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (hSmax : 0 ≤ Smax) (hSmaxPs : Smax ≤ Real.exp Ps) (hstrideMax : ∀ x, ((stride x * cap : ℕ) : ℝ) ≤ Smax)
    (H : X → ℝ)
    (hsize : ∀ x, Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (hcells : cells.Nonempty)
    {L D : ℕ}
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
    (rankC : ℝ) (hrankC : 0 ≤ rankC)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    (hL : ⌈2 * (rankC + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)
    (hfreqPs : (4 * allocatedFourierLogBudget m P + 2)^4 ≤ Ps)
    (hmassPs : 4 * allocatedFourierLogBudget m P * (4 * allocatedFourierLogBudget m P + 2)^4 +
      allocatedFourierLogBudget m P ≤ Ps)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth stride width z)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * (cap : ℝ) ≤
      allocatedShortRankSelectedWidth B U b S spatial stride width j)
    (hresidueError : (∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (cap : ℝ) /
      allocatedShortRankSelectedWidth B U b S spatial stride width j) ≤ κ) :
    let Dphysical := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      allocatedCoefficientDensity B U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
    ∃ read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        AllocatedActualCoefficientIndex G X I E n B → ℤ,
      (∀ z, allocatedReadNoise (read z) = z) ∧
      (∀ z, Dphysical z ≠ 0 →
        ∀ (primes : Finset ℕ) (hne : ∀ p : primes, NeZero p.val),
          letI := hne
          ∀ (depth : ℕ → ℕ) (q : ℕ) (hq : 0 < q),
            letI : NeZero q := ⟨hq.ne'⟩
            ∀ hdiv : ∀ p : primes, p.val ^ depth p.val ∣ q,
              coefficientDeckChartEvent U bW b hb o q
                (allocatedChartResiduePrimePowerWitness inactive rankC primes depth q hdiv
                  (fun v => (z v : ZMod q)))
                (affineCoefficientCoverSample U poly hm q (fun k x => (z (k, x) : ℝ))) ↔
              ∀ p : primes, allocatedActualModulusBad inactive spatial kernel block rankC
                (p.val ^ depth p.val) (read z)) ∧
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 3 * κ ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      0 < Rbad ∧ (Rbad : ℝ) ≤ Real.exp (Elog + 3) ∧
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
          (∑' z, (selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal *
            (if (∏ x, stride x) ^ 2 *
              (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * Rbad) <
                ∏ p ∈ primes, p ^ largestTestedBadDepth depth
                  (fun p a z => allocatedActualPrimeBad inactive spatial kernel block primes rankC p a (read z)) p z
              then (1 : ℝ) else 0)) ≤ Real.exp (-Elog) := by
  dsimp only
  obtain ⟨hκ, hκinv, hsmallError, _, herrors⟩ :=
    physicalBadProductAccuracy_budget hElog hVlog Q hQ hQexp
  obtain ⟨hcapexp, _⟩ := quantitativeBadPrimeRadius_witness_budget hElog hVlog Q hQexp
  have hcap : 0 < cap := lt_of_lt_of_le (by omega : 0 < Q) (le_max_left _ _)
  have hcapP : (cap : ℝ) ≤ Real.exp P := hcapexp.trans
    (Real.exp_le_exp.mpr (by linarith))
  have hcapPs : (cap : ℝ) ≤ Real.exp Ps := hcapexp.trans
    (Real.exp_le_exp.mpr (by linarith))
  have hκP : κ⁻¹ ≤ Real.exp P := by rw [hκinv]; exact Real.exp_le_exp.mpr hbudgetP
  have hκPs : 1 / κ ≤ Real.exp Ps := by
    rw [one_div, hκinv]; exact Real.exp_le_exp.mpr hbudgetPs
  obtain ⟨hD0, hZ, hDpos, read, hnoise, hread, hmass, hlower, hupper, hcompare⟩ :=
    exists_allocated_physical_certified_rank_witness_law B U bW b hb o S C V hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall cap hcap hP hmP hK hRP hσP hcount hI hn hJ hAP hLP
      hCP hVP hcapP hκ hκP μ ν poly hp hm hPs hX hframe hcapPs hκ hρ hκPs hρPs stride hstride
      hSmax hSmaxPs hstrideMax H hsize hrank hRs cells hcells inactive spatial kernel block
      rankC width hwidth hwide hfreqPs hmassPs hsmallError
  have hRbad := quantitativeBadPrimeRadius_bounds hElog
  refine ⟨hD0, hZ, hDpos, read, hnoise, hread, ?_, hlower, hupper, hRbad.1, hRbad.2.1, ?_⟩
  · linarith
  intro primes hprime
  let : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
  intro depth hdepth
  let bad := fun p a z => allocatedActualPrimeBad inactive spatial kernel block primes rankC p a (read z)
  have hstrideprod : 0 < ∏ x, stride x := Finset.prod_pos (fun x _ => hstride x)
  apply (selectedResidueDensityPMF_stride_quantitative_badPrimeProduct_s2 stride cells width hwidth
    hZ _ hD0 hDpos primes depth bad hstrideprod hprime
    (modularCoefficientPrimeThreshold_two_le m) hQ hdepth hElog hVlog hQexp ?_).2.2.2.2.2
  dsimp only
  intro T hT a ha hbound
  let hTprime : ∀ p ∈ T, p.Prime := fun p hp => hprime p (hT hp)
  let hTne : ∀ p : T, NeZero p.val := fun p => ⟨(hTprime p.val p.property).ne_zero⟩
  let := hTne
  let M : ℕ := ∏ p ∈ T, p ^ a p
  have hM : 0 < M := Finset.prod_pos (fun p hp => pow_pos (hTprime p hp).pos _)
  let : NeZero M := ⟨hM.ne'⟩
  have hdiv : ∀ p : T, p.val ^ a p.val ∣ M :=
    fun p => Finset.dvd_prod_of_mem (fun p => p ^ a p) p.property
  have hprod : (∏ p : T, p.val ^ a p.val) = M := by
    exact (Finset.prod_subtype T (fun _ => Iff.rfl) (fun p => p ^ a p)).symm
  have hMbound : (M : ℝ) ≤ cap := Nat.cast_le.mpr hbound
  have hlargeM : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : T, p.val ^ a p.val) ≤ allocatedShortRankSelectedWidth B U b S spatial stride width j := by
    intro j
    rw [hprod]
    exact (mul_le_mul_of_nonneg_left hMbound (by positivity)).trans (hlarge j)
  have hreference := allocatedShortRank_reference_event (N := M) B U b hR hσ S spatial kernel block
    hmpos stride hstride cells width hwidth hZ hscale T a hTprime
    (fun p hp => hdiv ⟨p,hp⟩) (fun p hp => (ha p hp).1)
    (fun p hp x => column_stride_depth_le_of_product_stride stride hstride (ha p hp).2.2.2 x)
    hD hrankC hL (fun p hp => (ha p hp).2.2.1) hlargeM
  have hsum : (∑ j, 16 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : T, p.val ^ a p.val) / allocatedShortRankSelectedWidth B U b S spatial stride width j) ≤ κ := by
    apply le_trans (Finset.sum_le_sum (fun j _ => ?_)) hresidueError
    rw [hprod]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hMbound (by positivity))
      ((by positivity : (0 : ℝ) ≤ 8 * (probabilityProfileLipschitz : ℝ) * (cap : ℝ)).trans (hlarge j))
  have hc := hcompare T hTne a M hM hbound hdiv
  have hevent (z) : (∀ p ∈ T, bad p (a p) z) ↔
      ∀ p : T, allocatedActualModulusBad inactive spatial kernel block rankC (p.val ^ a p.val) (read z) := by
    constructor
    · intro h p
      obtain ⟨_, hh⟩ := h p.val p.property
      exact hh
    · intro h p hp
      exact ⟨hT hp, h ⟨p,hp⟩⟩
  simp_rw [hevent]
  rw [hprod] at hreference hsum
  have hup := (abs_le.mp hc).2
  dsimp only [M] at hreference
  linarith

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocated_short_physical_certified_bad_product_s2_oai := @OAI.Erdos3.VectorPolynomial.exists_allocated_short_physical_certified_bad_product_s2_oai
