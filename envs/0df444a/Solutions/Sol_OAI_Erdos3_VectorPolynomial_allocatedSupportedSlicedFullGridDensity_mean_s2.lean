-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedFullGridDensity_mean_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:40:22.093985+00:00
-- url     : https://prove2.me/submissions/5fb78c18-613e-41b9-9373-1955d996f887

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196
import Theorems.Thm_OAI_Erdos3_principalSupportedResidue_selected_kernels_s2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalCoefficientMarginal
namespace OAI

section

namespace Erdos3

open MeasureTheory ProbabilityTheory

theorem dependentProductPMF_marginal {I J : Type*} [Fintype I] [Fintype J]
    {X : I → Type*} [∀ i, Countable (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, MeasurableSingletonClass (X i)]
    (p : ∀ i, PMF (X i)) (e : J → I) (he : Function.Injective e) :
    (dependentProductPMF p).map (fun (x : ∀ i, X i) (j : J) => x (e j)) =
      dependentProductPMF (fun j => p (e j)) := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (fun (x : ∀ i, X i) (j : J) => x (e j)) _ (by fun_prop)]
  simp only [dependentProductPMF, Measure.toPMF_toMeasure]
  have hind : iIndepFun (fun i (x : ∀ i, X i) => x i)
      (Measure.pi (fun i => (p i).toMeasure)) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hsel := iIndepFun.precomp he hind
  have hm := hsel.map_fun_eq_pi_map (fun j => (measurable_pi_apply (e j)).aemeasurable)
  apply hm.trans
  congr 1
  funext j
  exact (measurePreserving_eval (fun i => (p i).toMeasure) (e j)).map_eq

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

theorem principalCoefficientChoice_injective {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (d : D) (hd : 0 < h d) :
    Function.Injective (principalCoefficientChoice (G := G) (B := B) h d) := by
  intro x y hxy
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some b =>
      exact False.elim (canonicalPrincipalExponent_ne_zero h d hd b
        (congrArg Subtype.val hxy).symm)
  | some b =>
    cases y with
    | none =>
      exact False.elim (canonicalPrincipalExponent_ne_zero h d hd b
        (congrArg Subtype.val hxy))
    | some b' =>
      exact congrArg some (principalCoefficientSlot_injective h d hd hxy)

theorem principalCoefficientMarginal {D G : Type*} [Fintype D] [Fintype G]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (d : D) (hd : 0 < h d)
    (p : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → PMF ℤ) :
    (independentProductPMF p).map (fun a r => a (principalCoefficientChoice h d r)) =
      independentProductPMF (fun r => p (principalCoefficientChoice h d r)) :=
  independentProductPMF_marginal p _ (principalCoefficientChoice_injective h d hd)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndependentFiniteConditioning
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {Ω : J → Type*} [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]

theorem pi_condition (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (G : ∀ j, Finset (Ω j)) (hG : ∀ j, 0 < (p j).mass (G j)) :
    pi (fun j => (p j).condition (G j) (hG j)) =
      (pi p).condition (piRestrictionSet G) (piRestriction_mass_pos p G hG) := by
  classical
  apply ext_weight
  funext x
  change (∏ j, (if x j ∈ G j then (p j).weight (x j) else 0) / (p j).mass (G j)) =
    (if x ∈ piRestrictionSet G then ∏ j, (p j).weight (x j) else 0) /
      (pi p).mass (piRestrictionSet G)
  rw [piRestriction_mass, Finset.prod_div_distrib]
  congr 1
  by_cases hx : ∀ j, x j ∈ G j
  · simp only [hx, ite_true, (mem_piRestrictionSet G x).mpr hx]
  · rw [if_neg ((mem_piRestrictionSet G x).not.mpr hx)]
    obtain ⟨j, hj⟩ := not_forall.mp hx
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

end Erdos3.FiniteProbabilityWeights

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

end Coordinate

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.IndependentEmbeddedMixture
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {X R : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
  [∀ j, DecidableEq (R j)]

theorem pi_condition_fiber (p : ∀ j, FiniteProbabilityWeights (X j))
    (F : ∀ j, X j → R j) (r : ∀ j, R j)
    (hr : ∀ j, 0 < (p j).mass (Finset.univ.filter (fun x => F j x = r j))) :
    (pi p).condition (Finset.univ.filter (fun x => (fun j => F j (x j)) = r))
        (pi_fiber_mass_pos p F r hr) =
      pi (fun j => (p j).condition (Finset.univ.filter (fun x => F j x = r j)) (hr j)) := by
  simpa only [← pi_fiber_set F r] using
    (pi_condition p (fun j => Finset.univ.filter (fun x => F j x = r j)) hr).symm

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveFiberMarginal
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {J : Type*} [Fintype J] [DecidableEq J]
variable {X R : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
variable [∀ j, DecidableEq (R j)]
variable (p : ∀ j, FiniteProbabilityWeights (X j))
variable (F : ∀ j, X j → R j) (r : ∀ j, R j)
variable (hcell : 0 < (pi p).mass
  (Finset.univ.filter (fun x => (fun j => F j (x j)) = r)))

theorem pi_condition_positive_fiber :
    (pi p).condition (Finset.univ.filter (fun x => (fun j => F j (x j)) = r)) hcell =
      pi (fun j => (p j).condition (Finset.univ.filter (fun x => F j x = r j))
        (coordinate_fiber_mass_pos p F r hcell j)) :=
  pi_condition_fiber p F r (coordinate_fiber_mass_pos p F r hcell)

theorem pi_condition_positive_fiber_marginal
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSingletonClass (X j)]
    {V : Type*} [Fintype V] (e : V → J) (he : Function.Injective e) :
    ((pi p).condition (Finset.univ.filter (fun x => (fun j => F j (x j)) = r)) hcell).toPMF.map
        (fun x v => x (e v)) =
      dependentProductPMF (fun v =>
        ((p (e v)).condition (Finset.univ.filter (fun x => F (e v) x = r (e v)))
          (coordinate_fiber_mass_pos p F r hcell (e v))).toPMF) := by
  rw [pi_condition_positive_fiber]
  have hp := toPMF_pi (fun j =>
    (p j).condition (Finset.univ.filter (fun x => F j x = r j))
      (coordinate_fiber_mass_pos p F r hcell j))
  exact (congrArg (fun μ : PMF (∀ j, X j) => μ.map (fun x v => x (e v))) hp).trans
    (dependentProductPMF_marginal _ e he)

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

theorem allocatedPhysicalGridJetPMF_blocks
    (hmoderate : basisAxisScale (basis j) i ≤ S.value ^ (layerTailDegree m + 1))
    {α O : Type*} [Fintype α] [DecidableEq α]
    (x : G → IntegerScalarCubeBox α S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    (rows : O → Finset α) :
    integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1) rows)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j i) =
      (independentProductPMF (allocatedLayerIntegerPMFs B U basis hR hσ S j i)).map
        (fun a o => booleanCoefficient (fun _ => a (constantCoefficientSlot _ _)) (rows o) +
          ∑ b : B ⟨j, Sum.inr i⟩,
            a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) *
              integerBooleanBlockJet (fun v r => (y ⟨⟨j, Sum.inr i⟩, b, v⟩ r : ℤ)) (rows o)) := by
  unfold integerMatrixImagePMF
  ext z
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : independentProductPMF (allocatedLayerIntegerPMFs B U basis hR hσ S j i) a = 0
  · simp only [ha, ite_self]
  · have hs : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support := by
      intro d
      change allocatedLayerIntegerPMFs B U basis hR hσ S j i d (a d) ≠ 0
      rw [independentProductPMF_apply] at ha
      exact (Finset.prod_ne_zero_iff.mp ha) d (Finset.mem_univ d)
    have he := funext (fun o => allocatedPhysicalGridJet_blocks B U basis hR hσ S j i
      hmoderate a hs x y rows o)
    rw [he]

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

theorem allocatedPhysicalGridJetPMF_principal
    (hmoderate : basisAxisScale (basis j) i ≤ S.value ^ (layerTailDegree m + 1))
    {α O : Type*} [Fintype α] [DecidableEq α]
    (x : G → IntegerScalarCubeBox α S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    (rows : O → Finset α) :
    integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1) rows)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j i) =
      (independentProductPMF (fun r : Option (B ⟨j, Sum.inr i⟩) =>
        allocatedLayerIntegerPMFs B U basis hR hσ S j i
          (principalCoefficientChoice (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ r))).map
        (fun c o => booleanCoefficient (fun _ => c none) (rows o) +
          ∑ b : B ⟨j, Sum.inr i⟩, c (some b) *
            integerBooleanBlockJet (fun v r => (y ⟨⟨j, Sum.inr i⟩, b, v⟩ r : ℤ)) (rows o)) := by
  rw [allocatedPhysicalGridJetPMF_blocks B U basis hR hσ S j i hmoderate x y rows]
  rw [← principalCoefficientMarginal (G := G) (B := B) (layerSamplerDegree I n)
    ⟨j, Sum.inr i⟩ (Nat.zero_lt_succ _) (allocatedLayerIntegerPMFs B U basis hR hσ S j i)]
  rw [PMF.map_comp]
  rfl

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PrincipalCubeSupportedCell
namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (P : D → Prop) [DecidablePred P]

local notation "BP" => (fun a : {a // P a} => B (Subtype.val a))
local notation "hP" => (fun a : {a // P a} => h (Subtype.val a))
local notation "embed" => (fun j : PrincipalTupleIndex BP hP => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B h))
local notation "conditioned" => FiniteProbabilityWeights.condition (principalTupleWeights B h H hH)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

theorem containedSupportedProgressionLaw_axis_marginal :
    (containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell).toPMF.map
      (principalAxisRestrict P) =
      (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).toPMF := by
  let w := principalSupportedCoordinateWeights B h H hH q r hcell
  have hinj : Function.Injective embed := by
    intro a b hab
    rcases a with ⟨⟨a, ha⟩, av⟩
    rcases b with ⟨⟨b, hb⟩, bv⟩
    cases hab
    rfl
  have hraw := FiniteProbabilityWeights.pi_condition_positive_fiber_marginal
    (fun j => integerScalarCubeWeights α (H j) (hH j))
    (fun j (z : IntegerScalarCubeBox α (H j)) a => ((z a : ℤ) : ZMod q)) r hcell embed hinj
  have hpi := FiniteProbabilityWeights.toPMF_pi (fun j : PrincipalTupleIndex BP hP => w (embed j))
  have hraw' : (conditioned).toPMF.map (principalAxisRestrict P) =
      (FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex BP hP => w (embed j))).toPMF := hraw.trans hpi.symm
  have hm := congrArg (fun p => p.map (containedProgressionTupleMap BP hP
      (principalAxisLength P L) (principalAxisLength P H) (principalAxisLength P step)
      (fun j => c (embed j)) (fun j => hL (embed j)) (fun j => hsubset (embed j)))) hraw'
  rw [PMF.map_comp] at hm
  have hout := FiniteProbabilityWeights.toPMF_fiberLaw
    (FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex BP hP => w (embed j)))
    (containedProgressionTupleMap BP hP (principalAxisLength P L) (principalAxisLength P H)
      (principalAxisLength P step) (fun j => c (embed j)) (fun j => hL (embed j)) (fun j => hsubset (embed j)))
  simp only [containedSupportedProgressionLaw, containedSupportedProgressionAxisLaw,
    FiniteProbabilityWeights.toPMF_fiberLaw, PMF.map_comp]
  refine Eq.trans ?_ (hm.trans hout.symm)
  apply congrArg (fun f : PrincipalIntegerTuples B h α H → PrincipalAxisTuples (α := α) P L =>
    (conditioned).toPMF.map f)
  funext y j
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedActiveGridPlateau
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
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}

local notation "ig" => allocatedGridIntegerAxis B U b S

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedGridIntegerAxis_grid (a : gridAxes) :
    allocatedGridAxis (I := I) U b S.value ⟨(ig a).1, Sum.inr (ig a).2⟩ := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact ha

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedGridIntegerAxis_injective : Function.Injective ig := by
  have hinv (a : gridAxes) : (⟨(ig a).1, Sum.inr (ig a).2⟩ : LayerSamplerAxis I n) = a.val := by
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact False.elim ha
    · rfl
  intro a c h
  apply Subtype.ext
  rw [← hinv a, ← hinv c, h]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSupportedSlicedGridMarginal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
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

variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (rows : A → Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value)

variable (hselected : Function.Injective selected)
variable (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value
  ⟨(selected a).1, Sum.inr (selected a).2⟩)

include hselected hgrid in
theorem allocatedSupportedSlicedPhysicalGrid_joint_law :
    allocatedSupportedSlicedPhysicalJointPMF B U basis hR hσ S q r H step c hH hsubset hcell selected rows x =
      dependentProductPMF (fun a => allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell
        (selected a).1 (selected a).2 (rows a) x) := by
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
  let k (a : A) (y : ∀ b : B (e a), ∀ v : Fin (layerSamplerDegree I n (e a)),
      IntegerScalarCubeBox α (allocatedPrincipalSides B U basis S ⟨e a, b, v⟩)) : PMF (rows a → ℤ) :=
    (independentProductPMF (fun c : Option (B (e a)) =>
      allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2
        (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (e a) c))).map
      (fun c t => booleanCoefficient (fun _ : Finset α => c none) t +
        ∑ b, c (some b) * integerBooleanBlockJet (fun v i => (y b v i : ℤ)) t)
  have hpoint (a : A) (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α
      (allocatedPrincipalSides B U basis S)) :
      integerMatrixImagePMF (boundedCoefficientJetMatrix
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U basis S x y) ((selected a).1.val + 1)
        (fun t : rows a => (t : Finset α)))
        (allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2) =
      k a (fun b v => y ⟨e a, b, v⟩) := by
    exact allocatedPhysicalGridJetPMF_principal B U basis hR hσ S (selected a).1 (selected a).2
      (hgrid a) x y (fun t : rows a => (t : Finset α))
  unfold allocatedSupportedSlicedPhysicalJointPMF allocatedSupportedSlicedPhysicalGridPMF
  simp_rw [hpoint]
  exact containedSupportedProgressionLaw_selected_kernels B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell e he k

include hselected hgrid in
theorem allocatedSupportedSlicedPhysicalGrid_joint_mass (z : ∀ a, rows a → ℤ) :
    (allocatedSupportedSlicedPhysicalJointPMF B U basis hR hσ S q r H step c hH hsubset hcell selected rows x z).toReal =
      ∏ a, (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell
        (selected a).1 (selected a).2 (rows a) x (z a)).toReal := by
  rw [allocatedSupportedSlicedPhysicalGrid_joint_law B U basis hR hσ S q r H step c hH hsubset hcell selected rows x
    hselected hgrid, dependentProductPMF_apply, ENNReal.toReal_prod]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
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
local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (rows : A → Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell grid

omit [∀ index, DecidableEq (I index)] [∀ axis, DecidableEq (B axis)] in
theorem allocatedPhysicalGridJetPMF_restrict_join (j : Fin m) (i : Fin (n j))
    (hgrid : grid ⟨j, Sum.inr i⟩)
    (row : Finset (Finset α))
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)) :
    integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1) (fun t : row => (t : Finset α)))
      (allocatedLayerIntegerPMFs B U basis hR hσ S j i) =
    integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin grid (principalAxisRestrict grid y) v₀))
      (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid (principalAxisRestrict grid y) v₀))
      (j.val + 1) (fun t : row => (t : Finset α))) (allocatedLayerIntegerPMFs B U basis hR hσ S j i) := by
  rw [allocatedPhysicalGridJetPMF_principal B U basis hR hσ S j i hgrid x y,
    allocatedPhysicalGridJetPMF_principal B U basis hR hσ S j i hgrid x (principalAxisJoin grid (principalAxisRestrict grid y) v₀)]
  congr 1
  funext c t
  simp only [principalAxisJoin, principalAxisRestrict, hgrid, ↓reduceDIte]

theorem allocatedSupportedSlicedPhysicalJointPMF_grid_marginal
    (hgrid : ∀ a, grid ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)) :
    allocatedSupportedSlicedPhysicalJointPMF B U basis hR hσ S q r H step c hH hsubset hcell selected rows x =
      (gridLaw).toPMF.bind (fun u => dependentProductPMF (fun a =>
        integerMatrixImagePMF (boundedCoefficientJetMatrix
          (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin grid u v₀))
          (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u v₀)) ((selected a).1.val + 1)
          (fun t : rows a => (t : Finset α)))
          (allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2))) := by
  let k (u : PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U basis S)) : PMF (∀ a, rows a → ℤ) :=
    dependentProductPMF (fun a => integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin grid u v₀))
      (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u v₀)) ((selected a).1.val + 1)
      (fun t : rows a => (t : Finset α)))
      (allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2))
  have hm := congrArg (fun p => p.bind k)
    (containedSupportedProgressionLaw_axis_marginal B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S)
      hH hsubset q r hcell grid)
  rw [PMF.bind_map] at hm
  refine Eq.trans ?_ hm
  apply congrArg (conditioned).toPMF.bind
  funext y
  apply congrArg dependentProductPMF
  funext a
  exact allocatedPhysicalGridJetPMF_restrict_join B U basis hR hσ S x (selected a).1 (selected a).2
    (hgrid a) (rows a) y v₀

theorem allocatedSupportedSlicedPhysicalJointPMF_grid_mean
    (hgrid : ∀ a, grid ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (z : ∀ a, rows a → ℤ) :
    (allocatedSupportedSlicedPhysicalJointPMF B U basis hR hσ S q r H step c hH hsubset hcell selected rows x z).toReal =
      (gridLaw).mean (fun u => ∏ a,
        (integerMatrixImagePMF (boundedCoefficientJetMatrix
          (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin grid u v₀))
          (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u v₀)) ((selected a).1.val + 1)
          (fun t : rows a => (t : Finset α)))
          (allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2) (z a)).toReal) := by
  rw [allocatedSupportedSlicedPhysicalJointPMF_grid_marginal B U basis hR hσ S q r H step c hH hsubset hcell
    selected rows x hgrid v₀, FiniteProbabilityWeights.toPMF_bind_toReal]
  apply congrArg (gridLaw).mean
  funext u
  rw [dependentProductPMF_apply, ENNReal.toReal_prod]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedClippedFullGridGlobal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid

theorem allocatedSupportedSlicedFullGridDensity_mean_s2_oai (x : G → IntegerScalarCubeBox α S.value)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U b S))
    (z : AllocatedFrozenJetRows B U b S rowTypes) :
    (gridLaw).mean (fun u => allocatedGridJetDensity B U b hR hσ S x u v₀ rows z) =
      allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x z := by
  have hm := allocatedSupportedSlicedPhysicalJointPMF_grid_mean B U b hR hσ S q r H step c hH hsubset hcell
    ig (fun a => rowSets (ig a).1) x (allocatedGridIntegerAxis_grid B U b S) v₀
    (fun a => allocatedGridIntegerValues B U b S rowSets a (z a))
  have hp := allocatedSupportedSlicedPhysicalGrid_joint_mass B U b hR hσ S q r H step c hH hsubset hcell
    ig (fun a => rowSets (ig a).1) x (allocatedGridIntegerAxis_injective B U b S)
    (allocatedGridIntegerAxis_grid B U b S) (fun a => allocatedGridIntegerValues B U b S rowSets a (z a))
  refine Eq.trans ?_ (hm.symm.trans hp)
  apply congrArg (gridLaw).mean
  funext u
  apply Finset.prod_congr rfl
  intro a _
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · rfl

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uα, u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedFullGridDensity_mean_s2_oai.{uα, u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedFullGridDensity_mean_s2_oai.{uα, u_1, u_2, u_3, u_4}
