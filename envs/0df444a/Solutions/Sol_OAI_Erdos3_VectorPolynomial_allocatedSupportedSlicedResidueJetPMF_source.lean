-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedResidueJetPMF_source
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T17:33:29.342276+00:00
-- url     : https://prove2.me/submissions/bb1d1d7b-ddd1-42db-8b1a-185cb131d507

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B145
import Theorems.Thm_OAI_Erdos3_containedSupportedProgressionLaw_axis_integer_law

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductPMFMap
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem dependentProductPMF_apply {D : Type*} [Fintype D] {X : D → Type*}
    [∀ d, Countable (X d)] [∀ d, MeasurableSpace (X d)] [∀ d, MeasurableSingletonClass (X d)]
    (p : ∀ d, PMF (X d)) (x : ∀ d, X d) : dependentProductPMF p x = ∏ d, p d (x d) := by
  simp only [dependentProductPMF, Measure.toPMF_apply, Measure.pi_singleton]
  exact Finset.prod_congr rfl (fun d _ => (p d).toMeasure_apply_singleton (x d) (measurableSet_singleton _))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

theorem dependentProductPMF_map {J : Type*} [Fintype J] {X Y : J → Type*}
    [∀ j, Countable (X j)] [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSingletonClass (X j)]
    [∀ j, Countable (Y j)] [∀ j, MeasurableSpace (Y j)] [∀ j, MeasurableSingletonClass (Y j)]
    (p : ∀ j, PMF (X j)) (f : ∀ j, X j → Y j) :
    (dependentProductPMF p).map (fun x j => f j (x j)) =
      dependentProductPMF (fun j => (p j).map (f j)) := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  simp only [dependentProductPMF, Measure.toPMF_toMeasure]
  rw [Measure.pi_map_pi (fun j => (measurable_of_countable (f j)).aemeasurable)]
  congr 1
  funext j
  exact PMF.toMeasure_map (f j) (p j) (measurable_of_countable _)

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

theorem dependentProductPMF_pair {B : Type*} [Fintype B] {X Y : B → Type*}
    [∀ b, Countable (X b)] [∀ b, Countable (Y b)]
    [∀ b, MeasurableSpace (X b)] [∀ b, MeasurableSpace (Y b)]
    [∀ b, MeasurableSingletonClass (X b)] [∀ b, MeasurableSingletonClass (Y b)]
    (p : ∀ b, PMF (X b)) (q : ∀ b, PMF (Y b)) :
    (dependentProductPMF p).bind (fun x => (dependentProductPMF q).map
      (fun y b => (x b, y b))) =
      dependentProductPMF (fun b => (p b).bind (fun x => (q b).map (fun y => (x, y)))) := by
  ext z
  have hinj (x : ∀ b, X b) : Function.Injective (fun (y : ∀ b, Y b) b => (x b, y b)) := by
    intro y v h
    funext b
    exact congrArg Prod.snd (congrFun h b)
  rw [PMF.bind_apply, tsum_eq_single (fun b => (z b).1)]
  · have hm := pmf_map_injective_at (dependentProductPMF q)
      (fun (y : ∀ b, Y b) b => ((z b).1, y b)) (hinj (fun b => (z b).1))
      (fun b => (z b).2)
    rw [hm]
    simp only [dependentProductPMF_apply, pmf_bind_pair_apply, Finset.prod_mul_distrib]
  · intro x hx
    have hr : z ∉ Set.range (fun (y : ∀ b, Y b) b => (x b, y b)) := by
      rintro ⟨y, he⟩
      apply hx
      funext b
      exact congrArg Prod.fst (congrFun he b)
    rw [pmf_map_zero_off_range _ _ _ hr, mul_zero]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

end Erdos3.FiniteProbabilityWeights

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

theorem toPMF_pi {J : Type*} [Fintype J] {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    [∀ j, MeasurableSpace (Ω j)] [∀ j, MeasurableSingletonClass (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) :
    (pi p).toPMF = Erdos3.dependentProductPMF (fun j => (p j).toPMF) := by
  ext x
  rw [toPMF_apply, Erdos3.dependentProductPMF_apply]
  change ENNReal.ofReal (∏ j, (p j).weight (x j)) = ∏ j, ENNReal.ofReal ((p j).weight (x j))
  exact ENNReal.ofReal_prod_of_nonneg (fun j _ => (p j).nonneg (x j))

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

theorem toPMF_prod {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y) :
    (p.prod q).toPMF = p.toPMF.bind (fun x => q.toPMF.map (fun y => (x, y))) := by
  ext z
  rw [Erdos3.pmf_bind_pair_apply]
  change ENNReal.ofReal (p.weight z.1 * q.weight z.2) =
    ENNReal.ofReal (p.weight z.1) * ENNReal.ofReal (q.weight z.2)
  exact ENNReal.ofReal_mul (p.nonneg z.1)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

namespace ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

end ScalarCubeLocalizationData

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

namespace NormalizedScalarCubeSource

variable {I : Type*} [Fintype I] [DecidableEq I] (s : NormalizedScalarCubeSource I)

end NormalizedScalarCubeSource

end Erdos3

end

section

namespace Erdos3.ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

end Erdos3.ScalarCubeLocalizationData

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

end ScalarCubeLocalizationData

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

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

section

namespace Erdos3

namespace FiniteCoefficientSlice

end FiniteCoefficientSlice

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

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

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedScalarLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

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

local notation "profile" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

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

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators NNReal

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedActiveAxisSourceLaw
namespace OAI

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3

open scoped Classical

universe uX uY uZ uW

variable {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
variable (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))
variable {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

local notation "csource" => principalNormalizedSource hK hT hγ hlarge
local notation "pcoeff" => principalIntegerPMF K T γ hK hT hγ hlarge

section UniformTuples

variable (L : Fin n → ℕ) (hL : ∀ j, 0 < L j) (hsize : ∀ j, Fintype.card I + 1 ≤ L j)

end UniformTuples

end Erdos3

end

section

namespace Erdos3

theorem weightedModerateSource_pair_law {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I) :
    ((weightedModerateIntegerSource c s).toPMF).map (fun x => ((x.1 none : ℤ), x.2)) =
      (c.source.toPMF.map (fun x => (x none : ℤ))).bind (fun a =>
        (dependentProductPMF (fun j => (s j).source.toPMF)).map (fun y => (a, y))) := by
  rw [weightedModerateIntegerSource, FiniteProbabilityWeights.toPMF_prod, PMF.map_bind, PMF.bind_map]
  simp_rw [PMF.map_comp]
  simp only [Function.comp_def]
  exact congrArg (fun q : PMF (∀ j, IntegerScalarCubeBox I (s j).length) =>
    c.source.toPMF.bind (fun x => q.map (fun y => ((x none : ℤ), y))))
    (FiniteProbabilityWeights.toPMF_pi (fun j => (s j).source))

theorem weightedModerateSource_integer_pair_law {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I) :
    ((weightedModerateIntegerSource c s).toPMF).map
      (fun x => ((x.1 none : ℤ), fun j q => (x.2 j q : ℤ))) =
      (c.source.toPMF.map (fun x => (x none : ℤ))).bind (fun a =>
        (dependentProductPMF (fun j => (s j).source.toPMF)).map
          (fun y => (a, fun j q => (y j q : ℤ)))) := by
  have hp := congrArg (fun p : PMF (ℤ × (∀ j, IntegerScalarCubeBox I (s j).length)) =>
    p.map (fun ay => (ay.1, fun j q => (ay.2 j q : ℤ))))
    (weightedModerateSource_pair_law c s)
  rw [PMF.map_comp, PMF.map_bind] at hp
  simpa only [PMF.map_comp, Function.comp_def] using hp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

universe uB uX uY uZ

theorem dependentProductPMF_pair_transport
    {B : Type uB} [Fintype B] {X : B → Type uX} {Y : B → Type uY} {Z : B → Type uZ}
    [∀ b, Countable (X b)] [∀ b, Countable (Y b)] [∀ b, Countable (Z b)]
    [∀ b, MeasurableSpace (X b)] [∀ b, MeasurableSpace (Y b)] [∀ b, MeasurableSpace (Z b)]
    [∀ b, MeasurableSingletonClass (X b)] [∀ b, MeasurableSingletonClass (Y b)]
    [∀ b, MeasurableSingletonClass (Z b)]
    (p : ∀ b, PMF (X b)) (c : ∀ b, PMF (Y b)) (q : ∀ b, PMF (Z b))
    (f : ∀ b, X b → Y b × Z b)
    (h : ∀ b, (p b).map (f b) = (c b).bind (fun y => (q b).map (fun z => (y, z)))) :
    (dependentProductPMF p).map (fun x b => f b (x b)) =
      (dependentProductPMF c).bind (fun y => (dependentProductPMF q).map
        (fun z b => (y b, z b))) := by
  exact (dependentProductPMF_map p f).trans
    ((congrArg (fun r : ∀ b, PMF (Y b × Z b) => dependentProductPMF r) (funext h)).trans
      (dependentProductPMF_pair c q).symm)

theorem finiteWeights_pi_pair_transport
    {B : Type uB} [Fintype B] [DecidableEq B]
    {X : B → Type uX} {Y : B → Type uY} {Z : B → Type uZ}
    [∀ b, Fintype (X b)] [∀ b, Countable (Y b)] [∀ b, Countable (Z b)]
    [∀ b, MeasurableSpace (X b)] [∀ b, MeasurableSpace (Y b)] [∀ b, MeasurableSpace (Z b)]
    [∀ b, MeasurableSingletonClass (X b)] [∀ b, MeasurableSingletonClass (Y b)]
    [∀ b, MeasurableSingletonClass (Z b)]
    (p : ∀ b, FiniteProbabilityWeights (X b)) (c : ∀ b, PMF (Y b)) (q : ∀ b, PMF (Z b))
    (f : ∀ b, X b → Y b × Z b)
    (h : ∀ b, (p b).toPMF.map (f b) = (c b).bind (fun y => (q b).map (fun z => (y, z)))) :
    (FiniteProbabilityWeights.pi p).toPMF.map (fun x b => f b (x b)) =
      (dependentProductPMF c).bind (fun y => (dependentProductPMF q).map
        (fun z b => (y b, z b))) := by
  have hp : (FiniteProbabilityWeights.pi p).toPMF =
      dependentProductPMF (fun b => (p b).toPMF) := FiniteProbabilityWeights.toPMF_pi p
  have hm := congrArg (fun r : PMF (∀ b, X b) => r.map (fun x b => f b (x b))) hp
  exact hm.trans (dependentProductPMF_pair_transport (fun b => (p b).toPMF) c q f h)

variable {B : Type*} [Fintype B] [DecidableEq B]
variable {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
variable (c : B → NormalizedScalarCubeSource Empty)
variable (s : B → Fin n → NormalizedScalarCubeSource I)

theorem weightedModerateProductSource_pair_law :
    ((weightedModerateIntegerProductSource c s).toPMF).map
      (fun x b => (((x b).1 none : ℤ), fun j q => ((x b).2 j q : ℤ))) =
      (dependentProductPMF (fun b => (c b).source.toPMF.map (fun x => (x none : ℤ)))).bind
        (fun a => (dependentProductPMF (fun b =>
          (dependentProductPMF (fun j => (s b j).source.toPMF)).map
            (fun y j q => (y j q : ℤ)))).map (fun y b => (a b, y b))) := by
  apply finiteWeights_pi_pair_transport
    (X := fun b => IntegerScalarCubeBox Empty (c b).length ×
      (∀ j, IntegerScalarCubeBox I (s b j).length))
    (Y := fun _ => ℤ) (Z := fun _ => Fin n → Option I → ℤ)
    (fun b => weightedModerateIntegerSource (c b) (s b))
    (fun b => (c b).source.toPMF.map (fun x => (x none : ℤ)))
    (fun b => (dependentProductPMF (fun j => (s b j).source.toPMF)).map
      (fun y j q => (y j q : ℤ)))
    (fun b (x : IntegerScalarCubeBox Empty (c b).length ×
      (∀ j, IntegerScalarCubeBox I (s b j).length)) =>
        ((x.1 none : ℤ), fun j q => (x.2 j q : ℤ)))
  intro b
  simpa only [PMF.map_comp, Function.comp_def] using
    (weightedModerateSource_integer_pair_law (c b) (s b))

end Erdos3

end

section

namespace Erdos3

open scoped Classical

universe uP uQ uV

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "sides" => allocatedPrincipalSides B U basis S

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
variable (b : B ⟨j, Sum.inr i⟩)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (hsize : Fintype.card α + 1 ≤ S.value)

local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "pcoeff" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientSlot (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) b)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (hsize : Fintype.card α + 1 ≤ S.value)

local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineModeratePlateauModel
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {A J : Type*} [Fintype A] [Fintype J]
variable (D : A → ℕ) [∀ a, NeZero (D a)] (frequency : A → J → ℤ)
variable (coefficient : A → ℂ) (mode : A → (J → ℝ) → ℂ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {B : Type*} [Fintype B] [DecidableEq B]
variable {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
variable (c : B → NormalizedScalarCubeSource Empty)
variable (s : B → Fin n → NormalizedScalarCubeSource I)

theorem weightedAffineModerateProductSource_jet_sum_law
    (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (J : Finset (Finset I)) (offset : B → ℤ) (shift : J → ℤ) :
    ((weightedModerateIntegerProductSource c s).toPMF).map
      (weightedAffineModerateIntegerJetSum c s u v J offset shift) =
      (dependentProductPMF (fun b => (c b).source.toPMF.map (fun x => (x none : ℤ)))).bind
        (fun a => (dependentProductPMF (fun b =>
          (dependentProductPMF (fun j => (s b j).source.toPMF)).map
            (fun y j q => (y j q : ℤ)))).map
              (fun y => shift + ∑ b, fun r : J => (offset b + a b) * integerBooleanBlockJet (fun j => affineIntegerCubeCoordinates (u b j) (v b j) (y b j)) r)) := by
  have hp := congrArg (fun p : PMF (B → ℤ × (Fin n → Option I → ℤ)) =>
    p.map (fun z => shift + ∑ b, fun r : J =>
      (offset b + (z b).1) * integerBooleanBlockJet (fun j => affineIntegerCubeCoordinates (u b j) (v b j) ((z b).2 j)) r))
    (weightedModerateProductSource_pair_law c s)
  rw [PMF.map_comp, PMF.map_bind] at hp
  change ((weightedModerateIntegerProductSource c s).toPMF).map
    (fun x => shift + ∑ b, fun r : J => (offset b + ((x b).1 none : ℤ)) *
      integerBooleanBlockJet (fun j => affineIntegerCubeCoordinates (u b j) (v b j) (fun q => ((x b).2 j q : ℤ))) r) = _
  simpa only [PMF.map_comp, Function.comp_def] using hp

theorem weightedAffineModerateProductSource_affine_law
    (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
    (J : Finset (Finset I)) (offset : B → ℤ) (shift : J → ℤ) :
    (weightedModerateIntegerProductSource c s).toPMF.map
      (weightedAffineModerateIntegerJetSum c s u v J offset shift) =
      (dependentProductPMF (fun b => (c b).source.toPMF.map (fun x => (x none : ℤ)))).bind
        (fun a => (dependentProductPMF (fun b =>
          (dependentProductPMF (fun j => (s b j).source.toPMF)).map
            (fun y j => affineIntegerCubeCoordinates (u b j) (v b j) (fun i => (y j i : ℤ))))).map
              (fun y => shift + ∑ b, fun r : J => (offset b + a b) * integerBooleanBlockJet (y b) r)) := by
  have hm := dependentProductPMF_map
    (fun b => (dependentProductPMF (fun j => (s b j).source.toPMF)).map
      (fun y j i => (y j i : ℤ)))
    (fun b y j => affineIntegerCubeCoordinates (u b j) (v b j) (y j))
  simp only [PMF.map_comp, Function.comp_def] at hm
  have ht := congrArg (fun p : PMF (B → Fin n → Option I → ℤ) =>
    (dependentProductPMF (fun b => (c b).source.toPMF.map (fun x => (x none : ℤ)))).bind
      (fun a => p.map (fun y => shift + ∑ b, fun r : J =>
        (offset b + a b) * integerBooleanBlockJet (y b) r))) hm
  refine (weightedAffineModerateProductSource_jet_sum_law c s u v J offset shift).trans ?_
  simpa only [PMF.map_comp, Function.comp_def] using ht

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B I T : Type*} [Fintype B] [Fintype I] [DecidableEq I]
variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
variable {n K M : ℕ} [NeZero M]
variable (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
variable (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
variable (offset : B → ℤ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ContainedSupportedProgressionJetLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "weights" => FiniteProbabilityWeights.condition (principalTupleWeights B h H hH)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell
local notation "tupleMap" => containedProgressionTupleMap B h L H step c hL hsubset

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "law" => containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell

theorem containedSupportedProgressionLaw_jet_sum_law (a : D)
    (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨a,b,v⟩)
    (coeff : B a → NormalizedScalarCubeSource Empty)
    (rows : Finset (Finset α)) (offset : B a → ℤ) (shift : rows → ℤ) :
    let sources := principalSupportedAxisSources B h H hH q hq r a hsize
    let lower := fun (b : B a) (v : Fin (h a)) (i : Option α) => if i = none then c ⟨a,b,v⟩ else 0
    let strides := fun (b : B a) (v : Fin (h a)) (_ : Option α) => step ⟨a,b,v⟩
    (weightedModerateIntegerProductSource coeff sources).toPMF.map
      (weightedAffineModerateIntegerJetSum coeff sources lower strides rows offset shift) =
      (dependentProductPMF (fun b => (coeff b).source.toPMF.map (fun z => (z none : ℤ)))).bind
        (fun z => (law).toPMF.map (fun y => shift + ∑ b, fun t : rows =>
          (offset b + z b) * integerBooleanBlockJet (fun v i => (y ⟨a,b,v⟩ i : ℤ)) t)) := by
  intro sources lower strides
  refine (weightedAffineModerateProductSource_affine_law coeff sources lower strides rows offset shift).trans ?_
  have hp := congrArg (fun p : PMF (B a → Fin (h a) → Option α → ℤ) =>
    (dependentProductPMF (fun b => (coeff b).source.toPMF.map (fun z => (z none : ℤ)))).bind
      (fun z => p.map (fun y => shift + ∑ b, fun t : rows =>
        (offset b + z b) * integerBooleanBlockJet (y b) t)))
    (containedSupportedProgressionLaw_axis_integer_law B h L H step c hL hH hsubset q r hcell hq a hsize).symm
  simp only [PMF.map_comp, Function.comp_def] at hp
  convert hp using 1
  rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidueJet
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

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

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

theorem allocatedSupportedSlicedResidueJetPMF_source
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (rows : Finset (Finset α)) (shift : rows → ℤ) :
    let sources := principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
      ⟨j, Sum.inr i⟩ hsize
    let coeff := fun _ : B ⟨j,Sum.inr i⟩ => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
    let lower := fun (b : B ⟨j,Sum.inr i⟩) (v : Fin (j.val + 1)) (a : Option α) =>
      if a = none then c ⟨⟨j,Sum.inr i⟩,b,v⟩ else 0
    let strides := fun (b : B ⟨j,Sum.inr i⟩) (v : Fin (j.val + 1)) (_ : Option α) =>
      step ⟨⟨j,Sum.inr i⟩,b,v⟩
    (weightedModerateIntegerProductSource coeff sources).toPMF.map
      (weightedAffineModerateIntegerJetSum coeff sources lower strides rows (fun _ => 0) shift) =
      allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows shift := by
  intro sources coeff lower strides
  have hp := containedSupportedProgressionLaw_jet_sum_law B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S)
    hH hsubset q hq r hcell ⟨j,Sum.inr i⟩ hsize coeff rows (fun _ => 0) shift
  dsimp only at hp
  have hc := congrArg (fun p : B ⟨j,Sum.inr i⟩ → PMF ℤ => dependentProductPMF p)
    (funext (fun b => allocatedPrincipalNormalizedSource_law B U basis hR hσ S j i hactive b))
  rw [hc] at hp
  simp only [zero_add] at hp
  convert hp using 1 <;> rfl

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedResidueJetPMF_source.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedResidueJetPMF_source.{u_1, u_2, u_3, u_4, u_5}
