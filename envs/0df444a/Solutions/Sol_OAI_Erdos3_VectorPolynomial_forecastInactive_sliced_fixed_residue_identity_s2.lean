-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.forecastInactive_sliced_fixed_residue_identity_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:50:03.851859+00:00
-- url     : https://prove2.me/submissions/3b861f80-2482-4a96-a29d-2faba2642b55

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B196
import Definitions.Def_OAIE3v2B197
import Theorems.Thm_OAI_Erdos3_principalSupportedResidue_selected_kernels_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTest
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X R : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem fiberMean_eq_mass_mul_condition [DecidableEq X] [DecidableEq R]
    (F : X → R) (r : R) (f : X → ℝ)
    (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))) :
    p.fiberMean F r f = p.mass (Finset.univ.filter (fun x => F x = r)) *
      (p.condition (Finset.univ.filter (fun x => F x = r)) hr).mean f := by
  rw [p.mass_mul_condition_mean]
  simp only [fiberMean, Finset.mem_filter, Finset.mem_univ, true_and]
  congr 1
  funext x
  by_cases hx : F x = r <;> simp [hx]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_const {α R : Type*} [DecidableEq α] [CommRing R]
    (c : R) (s : Finset α) : booleanCoefficient (fun _ => c) s = if s = ∅ then c else 0 := by
  have h1 := booleanCoefficient_monomial (R := R) ∅ s
  simp only [Finset.empty_subset, ite_true] at h1
  have hc := booleanCoefficient_const_mul s c (fun _ => (1 : R))
  simpa only [mul_one, h1, mul_ite, mul_zero] using hc

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductPMFMap
namespace OAI

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

end OAI
end

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

theorem integerMonomialArrayPolynomial_principal_sum {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (a : J → ℤ) (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
    (hzero : ∀ j, j ≠ j₀ → j ∉ P → a j = 0) :
    integerMonomialArrayPolynomial e a =
      MvPolynomial.C (a j₀) + ∑ j ∈ P, MvPolynomial.monomial (e j) (a j) := by
  classical
  have hsum : (∑ j ∈ insert j₀ P, MvPolynomial.monomial (e j) (a j)) =
      ∑ j, MvPolynomial.monomial (e j) (a j) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hne : j ≠ j₀ := fun he => hj (he ▸ Finset.mem_insert_self _ _)
    have hnot : j ∉ P := fun hp => hj (Finset.mem_insert_of_mem hp)
    simp [hzero j hne hnot]
  rw [integerMonomialArrayPolynomial, ← hsum, Finset.sum_insert hj₀, he₀]
  rfl

theorem productBlockExponent_monomial_int {V : Type*} {h : ℕ}
    (principal : Fin h → V) (c : ℤ) :
    MvPolynomial.monomial (productBlockExponent principal) c =
      MvPolynomial.C c * ∏ v, MvPolynomial.X (principal v) := by
  rw [productBlockExponent, MvPolynomial.monomial_sum_index]
  rfl

theorem integerPrincipalPolynomial_eval {D G : Type*} [Fintype D] [Fintype G]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (d : D) (hd : 0 < h d)
    (a : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → ℤ)
    (hzero : ∀ e, e ≠ constantCoefficientSlot _ _ → e ∉ principalCoefficientSlots h d → a e = 0)
    (x : SamplerTupleIndex G B h → ℤ) :
    MvPolynomial.eval x (integerMonomialArrayPolynomial Subtype.val a) =
      a (constantCoefficientSlot _ _) + ∑ b : B d,
        a (principalCoefficientSlot h d b) * ∏ v : Fin (h d), x (.inr ⟨d, b, v⟩) := by
  classical
  rw [integerMonomialArrayPolynomial_principal_sum Subtype.val a
    (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
    (constantCoefficientSlot_not_principal h d hd) rfl hzero]
  simp only [map_add, map_sum, MvPolynomial.eval_C]
  congr 1
  rw [principalCoefficientSlots, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro b _
    change MvPolynomial.eval x
      (MvPolynomial.monomial (productBlockExponent (fun v => .inr ⟨d, b, v⟩)) _) = _
    rw [productBlockExponent_monomial_int]
    simp only [map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
  · intro b _ b' _ hb
    exact principalCoefficientSlot_injective h d hd hb

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedIntegerTailZero
namespace OAI

section

namespace Erdos3

section Coordinate

variable {J V : Type*} [Fintype J]
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)
variable (hgap : L^h < K → (principalSamplingGapRatio (principalProfileSize R P.card)*L)^h ≤ K)
variable (hεL : 8*(probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J)*L)

local notation "laws" => allocatedIntegerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL
  e he R σ hR hσ hgap hεL

theorem allocatedIntegerCoordinate_tail_pure (hsmall : K ≤ L^(s+1))
    (j : J) (hj₀ : j ≠ j₀) (hjP : j ∉ P) : laws j = PMF.pure 0 := by
  classical
  unfold allocatedIntegerPolynomialCoordinatePMF integerPolynomialCoordinatePMF
  simp only [hj₀, hjP, ↓reduceIte]
  exact integerAxisTailPMF_small T hT hK hL hTL (tailProfileSize_pos hR hσ _) hεL (e j) (he j) hsmall

theorem allocatedIntegerCoordinate_tail_zero (hsmall : K ≤ L^(s+1))
    (j : J) (hj₀ : j ≠ j₀) (hjP : j ∉ P) {k : ℤ} (hk : k ∈ (laws j).support) : k = 0 := by
  rw [allocatedIntegerCoordinate_tail_pure P j₀ h K L s hh hK hL T hT hTL e he R σ hR hσ
    hgap hεL hsmall j hj₀ hjP] at hk
  simpa only [PMF.support_pure, Set.mem_singleton_iff] using hk

theorem allocatedIntegerCoordinate_principal_inactive (hsmall : K ≤ L^h)
    (j : J) (hj₀ : j ≠ j₀) (hjP : j ∈ P) {k : ℤ} (hk : k ∈ (laws j).support) :
    k = inactivePrincipalCoefficient K (inactiveDenominator (principalProfileSize R P.card)) := by
  classical
  unfold allocatedIntegerPolynomialCoordinatePMF integerPolynomialCoordinatePMF at hk
  simp only [hj₀, hjP, ↓reduceIte] at hk
  rw [integerAxisPrincipalPMF_inactive hh hK hL (principalProfileSize_pos hR _) hgap hsmall] at hk
  exact inactivePrincipalPMF_support hk

end Coordinate

namespace VectorPolynomial

theorem allocatedLayerInteger_inactive_structure {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
    (hsmall : basisAxisScale (basis j) i ≤ S.value^(j.val+1))
    (a : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support) :
    (∀ d, d ≠ constantCoefficientSlot _ _ → d ∉ layerIntegerPrincipalSlots B j i → a d = 0) ∧
      ∀ d ∈ layerIntegerPrincipalSlots B j i,
        a d = inactivePrincipalCoefficient (basisAxisScale (basis j) i)
          (inactiveDenominator (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)) := by
  have hpow : basisAxisScale (basis j) i ≤ S.value^(layerTailDegree m+1) :=
    hsmall.trans (Nat.pow_le_pow_right S.positive
      ((layerDegree_le_tailDegree j).trans (Nat.le_succ _)))
  have hconst := layerIntegerPrincipalSlots_not_constant (G := G) B j i
  constructor
  · intro d hd₀ hdP
    exact allocatedIntegerCoordinate_tail_zero (layerIntegerPrincipalSlots B j i)
      (constantCoefficientSlot _ _) (j.val+1) (basisAxisScale (basis j) i) S.value (layerTailDegree m)
      (Nat.zero_lt_succ _) (basisAxisScale_pos (basis j) i) S.positive
      (layerSamplerBox B U basis S)
      (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v))
      (layerSamplerBox_le B U basis S) Subtype.val
      (fun d => d.property.trans (layerDegree_le_tailDegree j))
      (R j) (σ j) (hR j) (hσ j) (S.gap j i) (S.width j) hpow d hd₀ hdP (ha d)
  · intro d hd
    have hd₀ : d ≠ constantCoefficientSlot _ _ := fun he => hconst (he ▸ hd)
    exact allocatedIntegerCoordinate_principal_inactive (layerIntegerPrincipalSlots B j i)
      (constantCoefficientSlot _ _) (j.val+1) (basisAxisScale (basis j) i) S.value (layerTailDegree m)
      (Nat.zero_lt_succ _) (basisAxisScale_pos (basis j) i) S.positive
      (layerSamplerBox B U basis S)
      (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v))
      (layerSamplerBox_le B U basis S) Subtype.val
      (fun d => d.property.trans (layerDegree_le_tailDegree j))
      (R j) (σ j) (hR j) (hσ j) (S.gap j i) (S.width j) hsmall d hd₀ hd (ha d)

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedShortDependence
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))

local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)

theorem allocatedLayerInteger_moderate_tail_zero
    (hmoderate : basisAxisScale (basis j) i ≤ S.value^(layerTailDegree m+1))
    (a : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (d : Slots) (hd₀ : d ≠ constantCoefficientSlot _ _)
    (hdP : d ∉ layerIntegerPrincipalSlots B j i) : a d = 0 := by
  exact allocatedIntegerCoordinate_tail_zero (layerIntegerPrincipalSlots B j i)
    (constantCoefficientSlot _ _) (j.val+1) (basisAxisScale (basis j) i) S.value (layerTailDegree m)
    (Nat.zero_lt_succ _) (basisAxisScale_pos (basis j) i) S.positive
    (layerSamplerBox B U basis S)
    (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v))
    (layerSamplerBox_le B U basis S) Subtype.val
    (fun e => e.property.trans (layerDegree_le_tailDegree j))
    (R j) (σ j) (hR j) (hσ j) (S.gap j i) (S.width j) hmoderate d hd₀ hdP (ha d)

theorem allocatedLayerInteger_moderate_eval
    (hmoderate : basisAxisScale (basis j) i ≤ S.value^(layerTailDegree m+1))
    (a : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (x : LayerSamplerVariables G I n B → ℤ) :
    MvPolynomial.eval x (integerMonomialArrayPolynomial Subtype.val a) =
      a (constantCoefficientSlot _ _) + ∑ b : B ⟨j, Sum.inr i⟩,
        a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) *
          ∏ v : Fin (j.val+1), x (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩) := by
  exact integerPrincipalPolynomial_eval (layerSamplerDegree I n) ⟨j, Sum.inr i⟩
    (Nat.zero_lt_succ _) a
    (allocatedLayerInteger_moderate_tail_zero B U basis hR hσ S j i hmoderate a ha) x

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProgressionTupleSliceSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

namespace FiniteProbabilityWeights

theorem condition_weight_pos_iff {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (S : Finset Ω) (hS : 0 < p.mass S) (x : Ω) :
    0 < (p.condition S hS).weight x ↔ x ∈ S ∧ 0 < p.weight x := by
  change 0 < (if x ∈ S then p.weight x else 0) / p.mass S ↔ _
  rw [lt_div_iff₀ hS, zero_mul]
  by_cases hx : x ∈ S <;> simp [hx]

theorem pi_weight_pos_component {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (x : ∀ j, Ω j) (hx : 0 < (pi p).weight x) (j : J) : 0 < (p j).weight (x j) := by
  apply lt_of_le_of_ne ((p j).nonneg (x j))
  intro he
  have hz : (pi p).weight x = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ j) he.symm
  linarith

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ContainedProgressionCubeMap
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem containedProgressionCubeMap_value (I : Type*) [Fintype I] [DecidableEq I]
    (L H step : ℕ) (c : ℤ) (hL : 0 < L)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : IntegerScalarCubeBox I H) (hz : IntegerScalarCube H (fun i => (z i : ℤ)))
    (i : Option I) :
    (containedProgressionCubeMap I L H step c hL hsubset z i : ℤ) =
      (if i = none then c else 0) + (step : ℤ) * (z i : ℤ) := by
  rw [containedProgressionCubeMap, dif_pos hz]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberPMF
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped Classical

theorem toPMF_fiberLaw {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (f : X → Y) :
    (p.fiberLaw f).toPMF = p.toPMF.map f := by
  ext y
  apply (ENNReal.toReal_eq_toReal_iff' ((p.fiberLaw f).toPMF.apply_ne_top y)
    ((p.toPMF.map f).apply_ne_top y)).mp
  rw [toPMF_toReal, toPMF_map_toReal]
  rfl

end Erdos3.FiniteProbabilityWeights

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

theorem allocatedPhysicalCube_vertex (t : Finset α) :
    integerAffineCube (allocatedPhysicalCubeRoot B U basis S c x y)
        (allocatedPhysicalCubeDirections B U basis S x y) t =
      fun k => c k + Sum.elim
        (fun g => integerScalarCubeValue (fun i => (x g i : ℤ)) t)
        (fun j => integerScalarCubeValue (fun i => (y j i : ℤ)) t) k := by
  funext k
  cases k <;> simp only [integerAffineCube, allocatedPhysicalCubeRoot,
    allocatedPhysicalCubeDirections, Sum.elim_inl, Sum.elim_inr, integerScalarCubeValue] <;> ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedWeightedGridMixture
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))

local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) ((j : ℕ) + 1)

theorem allocatedLayerInteger_moderate_jet_blocks
    (hmoderate : basisAxisScale (basis j) i ≤ S.value ^ (layerTailDegree m + 1))
    (a : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    {α O : Type*} [Fintype α] [DecidableEq α]
    (x : LayerSamplerVariables G I n B → Option α → ℤ)
    (rows : O → Finset α) (o : O) :
    (integerJetMatrix (fun d : Slots => MvPolynomial.monomial d.val (1 : ℤ))
      (fun t v => ∑ r, (booleanFeature r t : ℤ) * x v r) rows *ᵥ a) o =
      booleanCoefficient (fun _ => a (constantCoefficientSlot _ _)) (rows o) +
        ∑ b : B ⟨j, Sum.inr i⟩,
          a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) *
            integerBooleanBlockJet (fun v r => x (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩) r) (rows o) := by
  simp only [integerJetMatrix_apply_coefficients, MvPolynomial.C_mul_monomial, mul_one]
  change booleanCoefficient (fun t => MvPolynomial.eval
      (fun v => ∑ r, (booleanFeature r t : ℤ) * x v r)
      (integerMonomialArrayPolynomial Subtype.val a)) (rows o) = _
  have he (t : Finset α) := allocatedLayerInteger_moderate_eval B U basis hR hσ S j i
    hmoderate a ha (fun v => ∑ r, (booleanFeature r t : ℤ) * x v r)
  simp_rw [he, booleanCoefficient_add, booleanCoefficient_sum, booleanCoefficient_const_mul]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))

local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) ((j : ℕ) + 1)

theorem allocatedPhysicalGridJet_blocks
    (hmoderate : basisAxisScale (basis j) i ≤ S.value ^ (layerTailDegree m + 1))
    (a : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    {α O : Type*} [Fintype α] [DecidableEq α]
    (x : G → IntegerScalarCubeBox α S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    (rows : O → Finset α) (o : O) :
    (boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1) rows *ᵥ a) o =
      booleanCoefficient (fun _ => a (constantCoefficientSlot _ _)) (rows o) +
        ∑ b : B ⟨j, Sum.inr i⟩,
          a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) *
            integerBooleanBlockJet (fun v r => (y ⟨⟨j, Sum.inr i⟩, b, v⟩ r : ℤ)) (rows o) := by
  let tuple : LayerSamplerVariables G I n B → Option α → ℤ := fun v r =>
    Sum.elim (fun g => (x g r : ℤ)) (fun q => (y q r : ℤ)) v
  have hvert : integerAffineCube (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) =
      (fun t v => ∑ r, (booleanFeature r t : ℤ) * tuple v r) := by
    funext t v
    rw [allocatedPhysicalCube_vertex]
    cases v <;> simp [tuple, integerScalarCubeValue, Fintype.sum_option, booleanFeature, ite_mul]
  change (integerJetMatrix (fun d : Slots => MvPolynomial.monomial d.val (1 : ℤ))
    (integerAffineCube (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y)) rows *ᵥ a) o = _
  rw [hvert]
  exact allocatedLayerInteger_moderate_jet_blocks B U basis hR hσ S j i hmoderate a ha tuple rows o

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedInactiveResidueScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : ∀ (a : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)),
  (Fintype.card α + 1) * q ≤ allocatedPrincipalSides B U b S ⟨⟨j, Sum.inr i⟩, a, v⟩)

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedInactivePrincipalPMF
    (hsmall : basisAxisScale (b j) i ≤ S.value ^ (j.val + 1)) (a : B ⟨j, Sum.inr i⟩) :
    allocatedLayerIntegerPMFs B U b hR hσ S j i
      (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ a) =
    PMF.pure (inactivePrincipalCoefficient (basisAxisScale (b j) i)
      (inactiveDenominator (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card))) := by
  have hmem : principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ a ∈
      layerIntegerPrincipalSlots (G := G) B j i := (mem_principalCoefficientSlots _ _ _).mpr ⟨a, rfl⟩
  have hne : principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ a ≠
      constantCoefficientSlot (LayerSamplerVariables G I n B) (j.val + 1) := by
    intro he
    exact (layerIntegerPrincipalSlots_not_constant B j i) (he ▸ hmem)
  simp only [allocatedLayerIntegerPMFs, allocatedProjectionPMFs,
    allocatedIntegerPolynomialCoordinatePMF, integerPolynomialCoordinatePMF]
  split_ifs with hc hp
  · exact False.elim (hne hc)
  · exact integerAxisPrincipalPMF_inactive (Nat.zero_lt_succ _)
      (basisAxisScale_pos (b j) i) S.positive (principalProfileSize_pos (hR j) _) (S.gap j i) hsmall
  · exact False.elim (hp hmem)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ContainedSupportedProgressionKernels
namespace OAI

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

theorem containedSupportedProgressionLaw_selected_kernels {A : Type*} [Fintype A]
    (e : A → D) (he : Function.Injective e) {Y : A → Type*}
    [∀ a, Countable (Y a)] [∀ a, MeasurableSpace (Y a)] [∀ a, MeasurableSingletonClass (Y a)]
    (k : ∀ a, (∀ b : B (e a), ∀ v : Fin (h (e a)), IntegerScalarCubeBox α (L ⟨e a,b,v⟩)) → PMF (Y a)) :
    (law).toPMF.bind (fun y => dependentProductPMF (fun a => k a (fun b v => y ⟨e a,b,v⟩))) =
      dependentProductPMF (fun a => (law).toPMF.bind (fun y => k a (fun b v => y ⟨e a,b,v⟩))) := by
  simp only [containedSupportedProgressionLaw, FiniteProbabilityWeights.toPMF_fiberLaw, PMF.bind_map]
  exact principalSupportedResidue_selected_kernels_s2 B h H hH q r hcell e he
    (fun a y => k a (fun b v => containedProgressionCubeMap α (L ⟨e a,b,v⟩) (H ⟨e a,b,v⟩)
      (step ⟨e a,b,v⟩) (c ⟨e a,b,v⟩) (hL _) (hsubset _) (y b v)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveFiberLaw
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (degree : D → ℕ)
variable (L : PrincipalTupleIndex B (fun a => degree a + 1) → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (fun a => degree a + 1) → Option α → ZMod q) (a : D)
variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ L ⟨a, b, v⟩)
variable (hcell : 0 < (principalTupleWeights (α := α) B (fun a => degree a + 1) L hL).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

omit [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] in

theorem forecastInactive_fiber_kernel
    {Ω Z R : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq R]
    (p : FiniteProbabilityWeights Ω) (residue : Ω → R) (r : R)
    (hr : 0 < p.mass (Finset.univ.filter (fun x => residue x = r)))
    (kernel : Ω → PMF Z) (z : Z) :
    p.fiberMean residue r (fun x => (kernel x z).toReal) =
      p.mass (Finset.univ.filter (fun x => residue x = r)) *
        (((p.condition (Finset.univ.filter (fun x => residue x = r)) hr).toPMF.bind kernel) z).toReal := by
  rw [FiniteProbabilityWeights.fiberMean_eq_mass_mul_condition _ _ _ _ hr,
    FiniteProbabilityWeights.toPMF_bind_toReal]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedOriginalSampleResidueMixtureForecast
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem forecastInactive_kernel_disintegration
    {Ω Z R : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype R] [DecidableEq R]
    (p : FiniteProbabilityWeights Ω) (residue : Ω → R)
    (kernel : Ω → PMF Z) (z : Z) (coefficient : R → ℂ) :
    p.complexMean (fun x => coefficient (residue x) * ((kernel x z).toReal : ℂ)) =
      ∑ r : {r : R // 0 < p.mass (Finset.univ.filter (fun x => residue x = r))},
        (p.mass (Finset.univ.filter (fun x => residue x = r.val)) : ℂ) * coefficient r.val *
          ((((p.condition (Finset.univ.filter (fun x => residue x = r.val)) r.property).toPMF.bind
            kernel) z).toReal : ℂ) := by
  calc
    _ = p.complexMean (fun x => ((kernel x z).toReal : ℂ) * coefficient (residue x)) := by
      congr 1
      funext x
      exact mul_comm _ _
    _ = ∑ r, (p.fiberMean residue r (fun x => (kernel x z).toReal) : ℂ) * coefficient r :=
      p.complexMean_fiber_factor residue (fun x => (kernel x z).toReal) coefficient
    _ = _ := by
      apply Finset.sum_congr_set
        {r : R | 0 < p.mass (Finset.univ.filter (fun x => residue x = r))}
      · intro r hr
        rw [forecastInactive_fiber_kernel p residue r hr kernel z, Complex.ofReal_mul]
        ring
      · intro r hr
        have hzero : p.mass (Finset.univ.filter (fun x => residue x = r)) = 0 :=
          le_antisymm (le_of_not_gt hr) (p.mass_nonneg _)
        have hf : p.fiberMean residue r (fun x => (kernel x z).toReal) = 0 := by
          simpa only [FiniteProbabilityWeights.fiberMean, Finset.mem_filter,
            Finset.mem_univ, true_and] using p.mean_mask_zero
            (Finset.univ.filter (fun x => residue x = r)) hzero
            (fun x => (kernel x z).toReal)
        rw [hf, Complex.ofReal_zero, zero_mul]

theorem forecastInactive_indicator_disintegration
    {Ω Z R : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype R] [DecidableEq R]
    [DecidableEq Z] (p : FiniteProbabilityWeights Ω) (residue : Ω → R)
    (F : Ω → Z) (z : Z) (coefficient : R → ℂ) :
    p.complexMean (fun y => coefficient (residue y) * (if F y = z then 1 else 0)) =
      ∑ r : {r : R // 0 < p.mass (Finset.univ.filter (fun y => residue y = r))},
        (p.mass (Finset.univ.filter (fun y => residue y = r.val)) : ℂ) * coefficient r.val *
          ((((p.condition (Finset.univ.filter (fun y => residue y = r.val)) r.property).toPMF.map
            F) z).toReal : ℂ) := by
  have hp (y : Ω) : ((PMF.pure (F y) z).toReal : ℂ) = if F y = z then 1 else 0 := by
    by_cases hy : F y = z
    · simp [PMF.pure_apply, hy]
    · simp [PMF.pure_apply, hy, Ne.symm hy]
  simpa only [PMF.bind_pure_comp, Function.comp_apply, hp] using
    forecastInactive_kernel_disintegration p residue (PMF.pure ∘ F) z coefficient

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ContainedProgressionForecastDisintegration
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

include hH hsubset in
 theorem containedProgressionTupleMap_residue_of_weight_ne_zero
    (q : ℕ) (y : PrincipalIntegerTuples B h α H)
    (hy : (principalTupleWeights B h H hH).weight y ≠ 0) :
    principalResidueLabel q (containedProgressionTupleMap B h L H step c hL hsubset y) =
      progressionPrincipalResidue B h step c q (principalResidueLabel q y) := by
  have hpos := lt_of_le_of_ne ((principalTupleWeights B h H hH).nonneg y) hy.symm
  funext j a
  have hj := FiniteProbabilityWeights.pi_weight_pos_component
    (fun j => integerScalarCubeWeights α (H j) (hH j)) y hpos j
  have hcube := (mem_integerScalarCubeSet (H j) (y j)).mp
    ((FiniteProbabilityWeights.condition_weight_pos_iff _ _ _ (y j)).mp hj).1
  change ((containedProgressionCubeMap α (L j) (H j) (step j) (c j) (hL j)
    (hsubset j) (y j) a : ℤ) : ZMod q) = _
  rw [containedProgressionCubeMap_value _ _ _ _ _ _ _ _ hcube]
  simp only [progressionPrincipalResidue, principalResidueLabel, Int.cast_add,
    Int.cast_mul, Int.cast_natCast, apply_ite, Int.cast_zero]

theorem containedProgressionForecast_indicator_disintegration
    {Z : Type*} [DecidableEq Z] (q : ℕ) [NeZero q]
    (F : PrincipalIntegerTuples B h α L → Z) (z : Z)
    (coefficient : (PrincipalTupleIndex B h → Option α → ZMod q) → ℂ) :
    let p := principalTupleWeights (α := α) B h H hH
    let map := containedProgressionTupleMap B h L H step c hL hsubset
    (p.fiberLaw map).complexMean (fun y => coefficient (principalResidueLabel q y) *
      (if F y = z then 1 else 0)) =
      ∑ r : {r : PrincipalTupleIndex B h → Option α → ZMod q //
          0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))},
        (p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r.val)) : ℂ) *
          coefficient (progressionPrincipalResidue B h step c q r.val) *
          (((containedSupportedProgressionLaw B h L H step c hL hH hsubset q r.val r.property).toPMF.map
            F z).toReal : ℂ) := by
  intro p map
  rw [p.fiberLaw_complexMean]
  have hcongr : p.complexMean (fun y => coefficient (principalResidueLabel q (map y)) *
      (if F (map y) = z then 1 else 0)) =
      p.complexMean (fun y => coefficient (progressionPrincipalResidue B h step c q
        (principalResidueLabel q y)) * (if F (map y) = z then 1 else 0)) := by
    unfold FiniteProbabilityWeights.complexMean
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : p.weight y = 0
    · simp only [hy, Complex.ofReal_zero, zero_mul]
    · dsimp only [map]
      rw [containedProgressionTupleMap_residue_of_weight_ne_zero B h L H step c hL hH hsubset q y hy]
  have hd := forecastInactive_indicator_disintegration p (principalResidueLabel q)
    (fun y => F (map y)) z (fun r => coefficient (progressionPrincipalResidue B h step c q r))
  refine hcongr.trans (hd.trans ?_)
  apply Finset.sum_congr rfl
  intro r _
  have hm :
      (containedSupportedProgressionLaw B h L H step c hL hH hsubset q r.val r.property).toPMF.map F =
      (p.condition (Finset.univ.filter (fun y => principalResidueLabel q y = r.val)) r.property).toPMF.map
        (fun y => F (map y)) := by
    rw [containedSupportedProgressionLaw, FiniteProbabilityWeights.toPMF_fiberLaw, PMF.map_comp]
    rfl
  rw [hm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedFixedPath
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

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
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (lower : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (lower t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  H hH).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step lower
  (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

theorem forecastInactiveSlicedFixedPath_law (j : Fin m) (i : Fin (n j))
    (hsmall : basisAxisScale (basis j) i ≤ S.value ^ (j.val + 1))
    (c : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (hc : ∀ d, c d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (x : G → IntegerScalarCubeBox α S.value) (rows : Finset (Finset α)) :
    (conditioned).toPMF.map (fun y =>
      boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1)
        (fun t : rows => (t : Finset α)) *ᵥ c) =
      allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step lower hH hsubset hcell j i rows
        (fun t => booleanCoefficient (fun _ : Finset α => c (constantCoefficientSlot _ _)) t) := by
  have hdet := (allocatedLayerInteger_inactive_structure B U basis hR hσ S j i hsmall c hc).2
  let pc (b : B ⟨j, Sum.inr i⟩) :=
    c (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b)
  have hprincipal (b : B ⟨j, Sum.inr i⟩) :
      allocatedLayerIntegerPMFs B U basis hR hσ S j i
        (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) =
        PMF.pure (pc b) := by
    rw [allocatedInactivePrincipalPMF B U basis S j i hR hσ hsmall]
    congr 1
    exact (hdet _ ((mem_principalCoefficientSlots _ _ _).mpr ⟨b, rfl⟩)).symm
  have hcoeff : (dependentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
      allocatedLayerIntegerPMFs B U basis hR hσ S j i
        (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))) =
      PMF.pure pc := by
    ext a
    rw [dependentProductPMF_apply]
    simp_rw [hprincipal]
    by_cases ha : a = pc
    · subst a
      simp
    · obtain ⟨b, hb⟩ : ∃ b, a b ≠ pc b := by
        by_contra hn
        apply ha
        funext b
        exact not_not.mp (fun h => hn ⟨b, h⟩)
      rw [PMF.pure_apply_of_ne _ _ ha]
      exact Finset.prod_eq_zero (Finset.mem_univ b) (PMF.pure_apply_of_ne _ _ hb)
  have hmoderate : basisAxisScale (basis j) i ≤ S.value ^ (layerTailDegree m + 1) :=
    hsmall.trans (Nat.pow_le_pow_right S.positive
      ((layerDegree_le_tailDegree j).trans (Nat.le_succ _)))
  unfold allocatedSupportedSlicedResidueJetPMF
  rw [hcoeff, PMF.pure_bind]
  apply congrArg (fun f => (conditioned).toPMF.map f)
  funext y t
  simpa only [Pi.add_apply, Finset.sum_apply, pc] using
    allocatedPhysicalGridJet_blocks B U basis hR hσ S j i hmoderate c hc x y
      (fun t : rows => (t : Finset α)) t

theorem forecastInactiveSlicedFixedPath_joint_law
    {A : Type*} [Fintype A] (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (x : G → IntegerScalarCubeBox α S.value) (rows : A → Finset (Finset α)) :
    (conditioned).toPMF.map (fun y a =>
      boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U basis S x y) ((selected a).1.val + 1)
        (fun t : rows a => (t : Finset α)) *ᵥ c a) =
      dependentProductPMF (fun a =>
        allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step lower hH hsubset hcell
          (selected a).1 (selected a).2 (rows a)
          (fun t => booleanCoefficient (fun _ : Finset α => c a (constantCoefficientSlot _ _)) t)) := by
  let e (a : A) : LayerSamplerAxis I n := ⟨(selected a).1, Sum.inr (selected a).2⟩
  have he : Function.Injective e := by
    have hi : Function.Injective (fun z : (Σ j : Fin m, Fin (n j)) =>
        (⟨z.1, Sum.inr z.2⟩ : LayerSamplerAxis I n)) := by
      rintro ⟨j, i⟩ ⟨k, l⟩ h
      have hj : j = k := congrArg Sigma.fst h
      subst k
      have hsum : (Sum.inr i : I j ⊕ Fin (n j)) = Sum.inr l :=
        eq_of_heq (Sigma.mk.inj_iff.mp h).2
      have hl : i = l := Sum.inr.inj hsum
      subst l
      rfl
    exact hi.comp hselected
  let out (a : A) (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α
      (allocatedPrincipalSides B U basis S)) : rows a → ℤ :=
    boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) ((selected a).1.val + 1)
      (fun t : rows a => (t : Finset α)) *ᵥ c a
  let k (a : A) (y : ∀ b : B (e a), ∀ v : Fin (layerSamplerDegree I n (e a)),
      IntegerScalarCubeBox α (allocatedPrincipalSides B U basis S ⟨e a, b, v⟩)) : PMF (rows a → ℤ) :=
    PMF.pure (fun t => booleanCoefficient (fun _ : Finset α => c a (constantCoefficientSlot _ _)) t +
      ∑ b, c a (principalCoefficientSlot (G := G) (layerSamplerDegree I n) (e a) b) *
        integerBooleanBlockJet (fun v i => (y b v i : ℤ)) t)
  have hpoint (a : A) (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α
      (allocatedPrincipalSides B U basis S)) :
      k a (fun b v => y ⟨e a, b, v⟩) = PMF.pure (out a y) := by
    apply congrArg PMF.pure
    funext t
    have hmoderate := (hsmall a).trans (Nat.pow_le_pow_right S.positive
      ((layerDegree_le_tailDegree (selected a).1).trans (Nat.le_succ _)))
    exact (allocatedPhysicalGridJet_blocks B U basis hR hσ S (selected a).1 (selected a).2
      hmoderate (c a) (hc a) x y (fun t : rows a => (t : Finset α)) t).symm
  have hpure (z : ∀ a, rows a → ℤ) :
      dependentProductPMF (fun a => PMF.pure (z a)) = PMF.pure z := by
    ext z'
    rw [dependentProductPMF_apply]
    by_cases hz : z' = z
    · subst z'
      simp
    · obtain ⟨a, ha⟩ : ∃ a, z' a ≠ z a := by
        by_contra hn
        apply hz
        funext a
        exact not_not.mp (fun h => hn ⟨a, h⟩)
      rw [PMF.pure_apply_of_ne _ _ hz]
      exact Finset.prod_eq_zero (Finset.mem_univ a) (PMF.pure_apply_of_ne _ _ ha)
  have hj := containedSupportedProgressionLaw_selected_kernels B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) H step lower
    (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell e he k
  simp_rw [hpoint, hpure] at hj
  change (conditioned).toPMF.map (fun y a => out a y) =
    dependentProductPMF (fun a => (conditioned).toPMF.map (out a)) at hj
  refine hj.trans ?_
  apply congrArg dependentProductPMF
  funext a
  exact forecastInactiveSlicedFixedPath_law B U basis hR hσ S q r H step lower hH hsubset hcell
    (selected a).1 (selected a).2 (hsmall a) (c a) (hc a) x (rows a)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastInactiveAffineIntervalFixedResidueSite
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {A : Type*} [Fintype A]

attribute [local instance] ScalarSiteExpansion.termFinite

theorem forecastInactive_sliced_fixed_residue_identity_s2_oai
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (q : ℕ) [NeZero q]
    (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
    (lower : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
    (hH : ∀ t, 0 < H t)
    (hsubset : ∀ t, integerProgressionSupport (lower t) (step t : ℤ) (H t) ⊆
      Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S t : ℤ))
    (coefficient : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q) → ℂ)
    (hsmall : ∀ a, basisAxisScale (b (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (c : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hc : ∀ a d, c a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S
      (selected a).1 (selected a).2 d).support)
    (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ) :
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let map := containedProgressionTupleMap B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) H step lower (allocatedPrincipalSides_pos B U b S) hsubset
    (p.fiberLaw map).complexMean (fun y => coefficient (principalResidueLabel q y) *
      (if forecastInactiveFixedOutput B U b S selected c x y = (fun a _ => z a) then 1 else 0)) =
      ∑ r : {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q //
          0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))},
        (p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r.val)) : ℂ) *
          coefficient (progressionPrincipalResidue B (layerSamplerDegree I n) step lower q r.val) *
          ((dependentProductPMF (fun a => allocatedSupportedSlicedResidueJetPMF B U b hR hσ S q r.val
            H step lower hH hsubset r.property (selected a).1 (selected a).2
            (Finset.univ : Finset (Finset Empty)) (fun _ => c a (constantCoefficientSlot _ _)))
            (fun a _ => z a)).toReal : ℂ) := by
  intro p map
  rw [containedProgressionForecast_indicator_disintegration]
  apply Finset.sum_congr rfl
  intro r _
  have hj := forecastInactiveSlicedFixedPath_joint_law B U b hR hσ S q r.val
    H step lower hH hsubset r.property selected hselected hsmall c hc x
    (fun _ => (Finset.univ : Finset (Finset Empty)))
  have hconst (v : ℤ) (t : Finset Empty) : booleanCoefficient (fun _ : Finset Empty => v) t = v := by
    simp only [booleanCoefficient_const, (Subsingleton.elim t ∅ : t = ∅), ↓reduceIte]
  simp only [hconst] at hj
  rw [show (containedSupportedProgressionLaw B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) H step lower (allocatedPrincipalSides_pos B U b S)
      hH hsubset q r.val r.property).toPMF.map (forecastInactiveFixedOutput B U b S selected c x) = _
    from hj]

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.forecastInactive_sliced_fixed_residue_identity_s2_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.forecastInactive_sliced_fixed_residue_identity_s2_oai.{u_1, u_2, u_3, u_4, u_5}
