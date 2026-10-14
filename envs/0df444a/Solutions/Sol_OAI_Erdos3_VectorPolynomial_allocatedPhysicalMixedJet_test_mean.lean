-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedPhysicalMixedJet_test_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-11T13:42:56.544722+00:00
-- url     : https://prove2.me/submissions/ad269aad-33e2-4254-84e5-283f9306cc6f

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B169
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedLongJet_variable_test_mean

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTest
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace FiniteProbabilityWeights

variable (p : FiniteProbabilityWeights Ω) (G : Finset Ω)

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem complexMean_ofReal_mul (f : X → ℝ) (z : ℂ) :
    p.complexMean (fun x => (f x : ℂ) * z) = (p.mean f : ℂ) * z := by
  simp only [complexMean, mean, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.sum_mul, mul_assoc]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X R : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory
open scoped BigOperators

variable {X C : Type*} [Fintype X] [MeasurableSpace C] (p : FiniteProbabilityWeights X)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] (law : FiniteProbabilityWeights I)
variable (P : I → Prop) (hP : ∀ i, P i ↔ 0 < law.weight i)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

variable {Ω R : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω) (F : Ω → R)

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityMixtureAELaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem pmf_support_ae {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : PMF X) : ∀ᵐ x ∂p.toMeasure, x ∈ p.support := by
  rw [ae_iff]
  change p.toMeasure p.supportᶜ = 0
  rw [p.toMeasure_apply_eq_zero_iff p.support_countable.measurableSet.compl]
  exact disjoint_compl_right

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Function _root_.Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

end OAI

end

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport
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

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial VectorPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

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

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J V : Type*} [Fintype J]
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
variable (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)


end Erdos3

end

section

namespace Erdos3

variable {J V : Type*}
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
variable (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)

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

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedShortDependence
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (hσ1 : ∀ j, σ j ≤ 1)
variable (j : Fin m) (i : Fin (n j))
variable {X α O : Type} [Fintype X] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (p : FiniteProbabilityWeights X)
variable (a : X → BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℤ)
variable (ha : ∀ x, p.weight x ≠ 0 → ∀ d,
  a x d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
variable (vertices : X → Finset α → LayerSamplerVariables G I n B → ℤ)
variable (rows : O → Finset α) (q : ℕ) (hrows : ∀ o, (rows o).card ≤ q)
variable (hx : ∀ x, p.weight x ≠ 0 → ∀ o t, t ∈ (rows o).powerset →
  ∀ v, |(vertices x t v : ℝ)| ≤ layerSamplerBox B U basis S v)

include hR hσ S hσ1 ha hrows hx

variable {T : ℕ} (hT : 0 < T) (hTS : T ≤ S.value)
variable (hshort : integerAxisSideLength (j.val+1) (basisAxisScale (basis j) i) S.value
  (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card) < T)

include hT hTS hshort

end VectorPolynomial
end Erdos3

end

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

theorem allocatedLayerInteger_moderate_eval_congr
    (hmoderate : basisAxisScale (basis j) i ≤ S.value^(layerTailDegree m+1))
    (a a' : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (ha' : ∀ d, a' d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (hconstant : a (constantCoefficientSlot _ _) = a' (constantCoefficientSlot _ _))
    (hcoeff : ∀ b : B ⟨j, Sum.inr i⟩,
      a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) =
        a' (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))
    (x x' : LayerSamplerVariables G I n B → ℤ)
    (hprincipal : ∀ (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val+1)),
      x (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩) = x' (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩)) :
    MvPolynomial.eval x (integerMonomialArrayPolynomial Subtype.val a) =
      MvPolynomial.eval x' (integerMonomialArrayPolynomial Subtype.val a') := by
  rw [allocatedLayerInteger_moderate_eval B U basis hR hσ S j i hmoderate a ha x,
    allocatedLayerInteger_moderate_eval B U basis hR hσ S j i hmoderate a' ha' x', hconstant]
  simp only [hcoeff, hprincipal]

theorem allocatedLayerInteger_moderateJet_congr
    (hmoderate : basisAxisScale (basis j) i ≤ S.value^(layerTailDegree m+1))
    (a a' : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (ha' : ∀ d, a' d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (hconstant : a (constantCoefficientSlot _ _) = a' (constantCoefficientSlot _ _))
    (hcoeff : ∀ b : B ⟨j, Sum.inr i⟩,
      a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) =
        a' (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))
    {α O : Type*} [DecidableEq α]
    (vertices vertices' : Finset α → LayerSamplerVariables G I n B → ℤ)
    (rows : O → Finset α)
    (hprincipal : ∀ o t, t ∈ (rows o).powerset →
      ∀ (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val+1)),
        vertices t (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩) =
          vertices' t (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩)) :
    integerJetMatrix (fun d : Slots => MvPolynomial.monomial d.val (1 : ℤ)) vertices rows *ᵥ a =
      integerJetMatrix (fun d : Slots => MvPolynomial.monomial d.val (1 : ℤ)) vertices' rows *ᵥ a' := by
  funext o
  simp only [integerJetMatrix_apply_coefficients, MvPolynomial.C_mul_monomial, mul_one]
  change booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
      (integerMonomialArrayPolynomial Subtype.val a)) (rows o) =
    booleanCoefficient (fun t => MvPolynomial.eval (vertices' t)
      (integerMonomialArrayPolynomial Subtype.val a')) (rows o)
  unfold booleanCoefficient
  apply Finset.sum_congr rfl
  intro t ht
  exact congrArg (fun v : ℤ => (-1) ^ (rows o \ t).card * v)
    (allocatedLayerInteger_moderate_eval_congr B U basis hR hσ S j i hmoderate
      a a' ha ha' hconstant hcoeff (vertices t) (vertices' t) (hprincipal o t ht))

end Erdos3.VectorPolynomial

end

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


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientJetScalar
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {K : Type*} {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val+1) → ℝ)
variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val+1) → PMF ℤ)

theorem coefficientAxisLaw_probability [Fintype K]
    (hw : ∀ j i d, 0 < w j i d) (a : LayerSamplerAxis I n) :
    IsProbabilityMeasure (coefficientAxisLaw c w p a) := by
  rcases a with ⟨j, a⟩
  cases a with
  | inl i =>
    let : ∀ d, IsProbabilityMeasure (affineCoefficientMeasure (c j i d) (w j i d)) :=
      fun d => affineCoefficientMeasure_probability _ (hw j i d)
    change IsProbabilityMeasure (Measure.pi (fun d => affineCoefficientMeasure (c j i d) (w j i d)))
    infer_instance
  | inr i =>
    change IsProbabilityMeasure (Measure.pi (fun d => (p j i d).toMeasure))
    infer_instance

theorem coefficientAxisEquiv_measurePreserving [Fintype K] [∀ j, Fintype (I j)]
    (hw : ∀ j i d, 0 < w j i d) :
    MeasurePreserving (coefficientAxisEquiv K I n)
      (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j)))
      (Measure.pi (coefficientAxisLaw c w p)) := by
  let laws := coefficientAxisLaw c w p
  let : ∀ a, IsProbabilityMeasure (laws a) := coefficientAxisLaw_probability c w p hw
  have hinner (j : Fin m) : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun a : I j ⊕ Fin (n j) => CoefficientAxisRow K ⟨j, a⟩)).symm
      (mixedScalarArrayLaw (c j) (w j) (p j))
      (Measure.pi (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)) :=
    measurePreserving_sumPiEquivProdPi_symm (fun a => laws ⟨j, a⟩)
  have houter := measurePreserving_pi
    (fun j => mixedScalarArrayLaw (c j) (w j) (p j))
    (fun j => Measure.pi (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)) hinner
  have hflat : MeasurePreserving
      (MeasurableEquiv.piCurry (fun j (a : I j ⊕ Fin (n j)) => CoefficientAxisRow K ⟨j, a⟩)).symm
      (Measure.pi (fun j => Measure.pi (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)))
      (Measure.pi laws) :=
    ⟨(MeasurableEquiv.piCurry (fun j (a : I j ⊕ Fin (n j)) => CoefficientAxisRow K ⟨j, a⟩)).symm.measurable,
      sigmaProductMeasure_flatten laws⟩
  exact hflat.comp houter

theorem coefficientAxisSplitEquiv_symm_left
    (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
    (u : ∀ a : {a // P a}, CoefficientAxisRow K a.val)
    (v : ∀ a : {a // ¬P a}, CoefficientAxisRow K a.val) (a : {a // P a}) :
    coefficientAxisEquiv K I n ((coefficientAxisSplitEquiv K I n P).symm (u, v)) a.val = u a := by
  exact congrArg (fun z => z.1 a) ((coefficientAxisSplitEquiv K I n P).apply_symm_apply (u, v))

theorem coefficientAxisSplitEquiv_symm_right
    (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
    (u : ∀ a : {a // P a}, CoefficientAxisRow K a.val)
    (v : ∀ a : {a // ¬P a}, CoefficientAxisRow K a.val) (a : {a // ¬P a}) :
    coefficientAxisEquiv K I n ((coefficientAxisSplitEquiv K I n P).symm (u, v)) a.val = v a := by
  exact congrArg (fun z => z.2 a) ((coefficientAxisSplitEquiv K I n P).apply_symm_apply (u, v))

theorem coefficientAxisSplitEquiv_measurePreserving [Fintype K] [∀ j, Fintype (I j)]
    (hw : ∀ j i d, 0 < w j i d) (P : LayerSamplerAxis I n → Prop) [DecidablePred P] :
    MeasurePreserving (coefficientAxisSplitEquiv K I n P)
      (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j)))
      ((Measure.pi (fun a : {a // P a} => coefficientAxisLaw c w p a.val)).prod
        (Measure.pi (fun a : {a // ¬P a} => coefficientAxisLaw c w p a.val))) := by
  let : ∀ a, IsProbabilityMeasure (coefficientAxisLaw c w p a) := coefficientAxisLaw_probability c w p hw
  exact (measurePreserving_piEquivPiSubtypeProd (coefficientAxisLaw c w p) P).comp
    (coefficientAxisEquiv_measurePreserving c w p hw)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}

theorem coefficientJetAxisMap_measurable {K : Type*} [Fintype K] {O : Fin m → Type*}
    [∀ j, Fintype (O j)]
    (A : ∀ j, Matrix (O j) (BoundedCoefficientExponent K (j.val+1)) ℤ)
    (a : LayerSamplerAxis I n) : Measurable (coefficientJetAxisMap A a) := by
  rcases a with ⟨j, a⟩
  cases a with
  | inl i =>
    exact (matrixSupCLM ((A j).map (Int.cast : ℤ → ℝ))).continuous.measurable
  | inr i =>
    change Measurable (fun c : BoundedCoefficientExponent K (j.val+1) → ℤ => A j *ᵥ c)
    exact measurable_of_countable _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory

variable {m : ℕ} {I O O' : Fin m → Type*} {n : Fin m → ℕ}
variable (e : ∀ j, O' j ≃ O j)

variable [∀ j, Fintype (O j)] [∀ j, Fintype (O' j)]

variable (P : LayerSamplerAxis I n → Prop)

variable [∀ j, Fintype (I j)] [DecidablePred P]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.JetAxisCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (O I : Fin m → Type*) (n : Fin m → ℕ)

theorem canonicalCoefficientJetArrays_axis {α K : Type*} [DecidableEq α] [Fintype K]
    (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
    (x : CoefficientSamplerArrays (K := K) I n) (a : LayerSamplerAxis I n) :
    coefficientJetAxisEquiv O I n (canonicalCoefficientJetArrays root A rows x) a =
      coefficientJetAxisMap (fun j => boundedCoefficientJetMatrix root A (j.val + 1) (rows j)) a
        (coefficientAxisEquiv K I n x a) := by
  rcases a with ⟨j, i | i⟩ <;> rfl

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D α : Type*} {B : D → Type*} {h : D → ℕ}

variable [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped Classical

variable {D α : Type*} [Fintype α] [DecidableEq α]
variable (B : D → Type*) (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

end Erdos3

end

section

namespace Erdos3

variable {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}

theorem partitionedPrincipalInput_value (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z) (z : Z → ℤ) {L : PrincipalTupleIndex B h → ℕ}
    (u : PrincipalAxisTuples (α := α) P L) (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) L)
    (k : SamplerTupleIndex G B h) (a : Option α) :
    Sum.elim (Sum.elim z (principalTupleIntegers u)) (principalTupleIntegers v)
        (partitionedPrincipalInput P extra k a) =
      Sum.elim z (principalTupleIntegers (principalAxisJoin P u v)) (canonicalTupleInput extra k a) := by
  rcases k with g | ⟨d, b, r⟩
  · rfl
  · by_cases hp : P d <;>
      simp [partitionedPrincipalInput, canonicalTupleInput, principalTupleIntegers, principalAxisJoin, hp]

theorem partitionedPrincipalInput_frozen_cube (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z)
    (z : Z ⊕ PrincipalAxisParameter (B := B) (h := h) (α := α) P → ℤ)
    (x y : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℤ)
    (t : Finset α) (d : D) (hd : P d) (b : B d) (v : Fin (h d)) :
    integerMappedCubeTuple (partitionedPrincipalInput P extra) z x t (.inr ⟨d, b, v⟩) =
      integerMappedCubeTuple (partitionedPrincipalInput P extra) z y t (.inr ⟨d, b, v⟩) := by
  simp only [integerMappedCubeTuple, integerAffineCube, partitionedPrincipalInput, hd, ↓reduceDIte,
    Sum.elim_inl]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable {G : Type*} [Fintype G] [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "gridAxes" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "degree" => layerSamplerDegree I n

section Law

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]

end Law

theorem allocatedGridAxis_jet_frozen
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (j : Fin m) (i : Fin (n j)) (hgrid : gridAxes ⟨j, Sum.inr i⟩)
    (a : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    {Z α O : Type*} [DecidableEq α] (extra : G → Option α → Z)
    (z : Z ⊕ PrincipalAxisParameter (B := B) (h := degree) (α := α) gridAxes → ℤ)
    (x y : PrincipalAxisParameter (B := B) (h := degree) (α := α) (fun d => ¬gridAxes d) → ℤ)
    (rows : O → Finset α) :
    integerMappedJetMatrix Subtype.val (partitionedPrincipalInput gridAxes extra) z rows x *ᵥ a =
      integerMappedJetMatrix Subtype.val (partitionedPrincipalInput gridAxes extra) z rows y *ᵥ a := by
  apply allocatedLayerInteger_moderateJet_congr B U basis hR hσ S j i hgrid
    a a ha ha rfl (fun _ => rfl)
    (integerMappedCubeTuple (partitionedPrincipalInput gridAxes extra) z x)
    (integerMappedCubeTuple (partitionedPrincipalInput gridAxes extra) z y) rows
  intro o t _ b v
  exact partitionedPrincipalInput_frozen_cube gridAxes extra z x y t ⟨j, Sum.inr i⟩ hgrid b v

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

theorem allocatedCoefficientAxisLaw_probability (a : LayerSamplerAxis I n) :
    IsProbabilityMeasure (allocatedCoefficientAxisLaw B U basis hR hσ S a) :=
  coefficientAxisLaw_probability _ _ _ (allocatedLayerWidths_pos B U basis hR hσ S) a

theorem allocatedFrozenCoefficientSource_probability :
    IsProbabilityMeasure (allocatedFrozenCoefficientSource B U basis hR hσ S) := by
  let : ∀ a, IsProbabilityMeasure (allocatedCoefficientAxisLaw B U basis hR hσ S a) :=
    allocatedCoefficientAxisLaw_probability B U basis hR hσ S
  exact Measure.pi.instIsProbabilityMeasure _

theorem allocatedLongCoefficientSource_probability :
    IsProbabilityMeasure (allocatedLongCoefficientSource B U basis hR hσ S) := by
  let : ∀ a, IsProbabilityMeasure (allocatedCoefficientAxisLaw B U basis hR hσ S a) :=
    allocatedCoefficientAxisLaw_probability B U basis hR hσ S
  exact Measure.pi.instIsProbabilityMeasure _

theorem allocatedCoefficientSplit_measurePreserving :
    MeasurePreserving (allocatedCoefficientSplit B U basis S)
      (allocatedCoefficientSource B U basis hR hσ S)
      ((allocatedFrozenCoefficientSource B U basis hR hσ S).prod
        (allocatedLongCoefficientSource B U basis hR hσ S)) :=
  coefficientAxisSplitEquiv_measurePreserving _ _ _
    (allocatedLayerWidths_pos B U basis hR hσ S) grid

theorem allocatedCoefficientReconstruct_measurePreserving :
    MeasurePreserving (allocatedCoefficientSplit B U basis S).symm
      ((allocatedFrozenCoefficientSource B U basis hR hσ S).prod
        (allocatedLongCoefficientSource B U basis hR hσ S))
      (allocatedCoefficientSource B U basis hR hσ S) :=
  (allocatedCoefficientSplit_measurePreserving B U basis hR hσ S).symm
    (allocatedCoefficientSplit B U basis S)

theorem allocatedCoefficientReconstruct_long
    (u : AllocatedFrozenCoefficients B U basis S) (v : AllocatedLongCoefficients B U basis S)
    (a : {a // ¬grid a}) :
    coefficientAxisEquiv vars I n ((allocatedCoefficientSplit B U basis S).symm (u, v)) a.val = v a :=
  coefficientAxisSplitEquiv_symm_right grid u v a

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedLongJetMixture
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)


variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

omit [Fintype α] [∀ j, DecidableEq (O j)] in
theorem allocatedLongJetMap_measurable : Measurable (allocatedLongJetMap B U basis S x u v rows) :=
  measurable_pi_iff.mpr (fun a =>
    (coefficientJetAxisMap_measurable (allocatedPartitionedJetMatrix B U basis S x u v rows) a.val).comp
      (measurable_pi_apply a))

variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α) (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)


variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPhysicalLongImage
namespace OAI

section

namespace Erdos3

theorem translatedIntegerMappedJetMatrix_zero {Z X K α O N : Type*} [DecidableEq α]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℤ)
    (rows : O → Finset α) (x : X → ℤ) :
    translatedIntegerMappedJetMatrix e input z rows x (fun _ => 0) =
      integerMappedJetMatrix e input z rows x := by
  simp only [translatedIntegerMappedJetMatrix, zero_add, integerMappedJetMatrix]

theorem translatedIntegerMappedJetMatrix_eq_boundedCoefficient {Z X K α O : Type*}
    [DecidableEq α] [Fintype K] (h : ℕ) (input : K → Option α → Z ⊕ X)
    (z : Z → ℤ) (rows : O → Finset α) (x : X → ℤ) (c : K → ℤ) :
    translatedIntegerMappedJetMatrix (fun e : VectorPolynomial.BoundedCoefficientExponent K h => e.val)
      input z rows x c =
      boundedCoefficientJetMatrix (fun k => c k + Sum.elim z x (input k none))
        (fun i k => Sum.elim z x (input k (some i))) h rows := by
  have hv : (fun t k => c k + integerMappedCubeTuple input z x t k) =
      integerAffineCube (fun k => c k + Sum.elim z x (input k none))
        (fun i k => Sum.elim z x (input k (some i))) := by
    funext t k
    simp only [integerMappedCubeTuple, integerAffineCube, add_assoc]
  change integerJetMatrix
      (fun e : VectorPolynomial.BoundedCoefficientExponent K h => MvPolynomial.monomial e.val 1)
      (fun t k => c k + integerMappedCubeTuple input z x t k) rows =
    integerJetMatrix
      (fun e : VectorPolynomial.BoundedCoefficientExponent K h => MvPolynomial.monomial e.val 1)
      (integerAffineCube (fun k => c k + Sum.elim z x (input k none))
        (fun i k => Sum.elim z x (input k (some i)))) rows
  rw [hv]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

omit [DecidableEq α] in
theorem allocatedPhysicalCube_mapped_root (c : LayerSamplerVariables G I n B → ℤ) :
    (fun k => c k + Sum.elim (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u)) (principalTupleIntegers v) ((partitionedPrincipalInput grid (fun g a => (g, a))) k none)) =
      allocatedPhysicalCubeRoot B U b S c x (principalAxisJoin grid u v) := by
  funext k
  rw [partitionedPrincipalInput_value]
  cases k <;> rfl

omit [DecidableEq α] in
theorem allocatedPhysicalCube_mapped_directions :
    (fun i k => Sum.elim (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u)) (principalTupleIntegers v) ((partitionedPrincipalInput grid (fun g a => (g, a))) k (some i))) = (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) := by
  funext i k
  rw [partitionedPrincipalInput_value]
  cases k <;> rfl

theorem allocatedTranslatedPartitionedJetMatrix_eq_physical
    (c : LayerSamplerVariables G I n B → ℤ) (j : Fin m) :
    allocatedTranslatedPartitionedJetMatrix B U b S x u v rows c j =
      boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S c x (principalAxisJoin grid u v)) (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) (j.val + 1) (rows j) := by
  unfold allocatedTranslatedPartitionedJetMatrix
  rw [translatedIntegerMappedJetMatrix_eq_boundedCoefficient,
    allocatedPhysicalCube_mapped_root, allocatedPhysicalCube_mapped_directions]

theorem allocatedPartitionedJetMatrix_eq_physical (j : Fin m) :
    allocatedPartitionedJetMatrix B U b S x u v rows j =
      boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) (j.val + 1) (rows j) := by
  rw [← allocatedTranslatedPartitionedJetMatrix_eq_physical B U b S x u v rows (fun _ => 0) j]
  exact (translatedIntegerMappedJetMatrix_zero _ (partitionedPrincipalInput grid (fun g a => (g, a))) (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u)) (rows j) (principalTupleIntegers v)).symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "split" => allocatedCoefficientSplit B U b S
local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "longSource" => allocatedLongCoefficientSource B U b hR hσ S

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "joined" => principalAxisJoin grid u v
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x joined
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x joined

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedPhysicalLongJetMap_reconstruct
    (a₀ : AllocatedFrozenCoefficients B U b S) (a₁ : AllocatedLongCoefficients B U b S) :
    allocatedPhysicalLongJetMap B U b S x u v rows ((split).symm (a₀, a₁)) =
      allocatedLongJetMap B U b S x u v rows a₁ := by
  have hmatrix : (fun j => boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j)) =
      allocatedPartitionedJetMatrix B U b S x u v rows :=
    funext (fun j => (allocatedPartitionedJetMatrix_eq_physical B U b S x u v rows j).symm)
  funext i
  change coefficientJetAxisEquiv O I n (canonicalCoefficientJetArrays root dirs rows _) i.val = _
  rw [canonicalCoefficientJetArrays_axis, hmatrix, allocatedCoefficientReconstruct_long]
  rfl

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedPhysicalLongJetMap_split
    (a : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n) :
    allocatedPhysicalLongJetMap B U b S x u v rows a =
      allocatedLongJetMap B U b S x u v rows (split a).2 := by
  simpa only [Prod.mk.eta, MeasurableEquiv.symm_apply_apply] using
    allocatedPhysicalLongJetMap_reconstruct B U b S x u v rows (split a).1 (split a).2

variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

theorem allocatedPhysicalLongJet_variable_test_mean
    (w : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (φ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides →
      AllocatedFrozenCoefficients B U b S → AllocatedLongJetRows B U b S O → ℂ)
    (hφ : ∀ v, Measurable (fun p : AllocatedFrozenCoefficients B U b S × AllocatedLongJetRows B U b S O =>
      φ v p.1 p.2)) {C : ℝ} (hbound : ∀ v a z, ‖φ v a z‖ ≤ C) :
    (∫ a, w.complexMean (fun v => φ v (split a).1
      (allocatedPhysicalLongJetMap B U b S x u v rows a)) ∂source) =
      ∫ a₀, ∫ z, w.complexMean (fun v =>
        (allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z : ℂ) * φ v a₀ z)
        ∂allocatedLongJetReference B U b S O ∂frozenSource := by
  classical
  let : IsProbabilityMeasure frozenSource := allocatedFrozenCoefficientSource_probability B U b hR hσ S
  let : IsProbabilityMeasure longSource := allocatedLongCoefficientSource_probability B U b hR hσ S
  have hi : Integrable (fun a : AllocatedFrozenCoefficients B U b S × AllocatedLongCoefficients B U b S =>
      w.complexMean (fun v => φ v a.1 (allocatedLongJetMap B U b S x u v rows a.2)))
      ((frozenSource).prod longSource) := by
    apply w.complexMean_integrable
    intro v
    exact (integrable_const C).mono'
      ((hφ v).comp (measurable_fst.prodMk
        ((allocatedLongJetMap_measurable B U b S x u v rows).comp measurable_snd))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun a => hbound v a.1 _))
  calc
    _ = ∫ a, w.complexMean (fun v => φ v (split ((split).symm a)).1
        (allocatedPhysicalLongJetMap B U b S x u v rows ((split).symm a))) ∂((frozenSource).prod longSource) :=
      (allocatedCoefficientReconstruct_measurePreserving B U b hR hσ S).integral_comp' _ |>.symm
    _ = ∫ a₀, ∫ a₁, w.complexMean (fun v => φ v a₀
        (allocatedLongJetMap B U b S x u v rows a₁)) ∂longSource ∂frozenSource := by
      simp only [allocatedPhysicalLongJetMap_split, MeasurableEquiv.apply_symm_apply]
      exact integral_prod _ hi
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro a₀
      exact allocatedLongJet_variable_test_mean B U b hR hσ S x u rows s hA hσ1 w
        (fun v => φ v a₀) (fun v => (hφ v).comp (measurable_const.prodMk measurable_id))
        (fun v z => hbound v a₀ z)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedFrozenGridLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

theorem allocatedFrozenCoefficientSource_supported :
    ∀ᵐ a ∂allocatedFrozenCoefficientSource B U b hR hσ S,
      AllocatedFrozenSupported B U b hR hσ S a := by
  classical
  let : ∀ a, IsProbabilityMeasure (allocatedCoefficientAxisLaw B U b hR hσ S a) :=
    allocatedCoefficientAxisLaw_probability B U b hR hσ S
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro hi
  have hrow : ∀ᵐ a ∂allocatedCoefficientAxisLaw B U b hR hσ S ⟨j, Sum.inr i⟩,
      ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S j i d).support := by
    change ∀ᵐ a ∂Measure.pi (fun d => (allocatedLayerIntegerPMFs B U b hR hσ S j i d).toMeasure), _
    exact ae_all_iff.mpr (fun d => (Measure.quasiMeasurePreserving_eval _ d).ae (pmf_support_ae _))
  exact (Measure.quasiMeasurePreserving_eval
    (fun a : {a // grid a} => allocatedCoefficientAxisLaw B U b hR hσ S a.val)
    ⟨⟨j, Sum.inr i⟩, hi⟩).ae hrow

variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v w : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

theorem allocatedFrozenJetMap_measurable [∀ j, Fintype (O j)] :
    Measurable (allocatedFrozenJetMap B U b S x u v rows) :=
  measurable_pi_iff.mpr (fun i =>
    (coefficientJetAxisMap_measurable (allocatedPartitionedJetMatrix B U b S x u v rows) i.val).comp
      (measurable_pi_apply i))

theorem allocatedFrozenJetMap_eq_of_supported (a : AllocatedFrozenCoefficients B U b S)
    (ha : AllocatedFrozenSupported B U b hR hσ S a) :
    allocatedFrozenJetMap B U b S x u v rows a = allocatedFrozenJetMap B U b S x u w rows a := by
  funext i
  rcases i with ⟨⟨j, i | i⟩, hi⟩
  · exact False.elim hi
  · exact allocatedGridAxis_jet_frozen B U b S hR hσ j i hi
      (a ⟨⟨j, Sum.inr i⟩, hi⟩) (ha j i hi) (fun g t => (g, t))
      (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u))
      (principalTupleIntegers v) (principalTupleIntegers w) (rows j)

theorem allocatedPhysicalJet_grid_reconstruct
    (a₀ : AllocatedFrozenCoefficients B U b S) (a₁ : AllocatedLongCoefficients B U b S)
    (i : {a // grid a}) :
    coefficientJetAxisEquiv O I n
      (canonicalCoefficientJetArrays
        (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) rows
        ((allocatedCoefficientSplit B U b S).symm (a₀, a₁))) i.val =
      allocatedFrozenJetMap B U b S x u v rows a₀ i := by
  rw [canonicalCoefficientJetArrays_axis]
  have hm : (fun j => boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v))
      (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v))
      (j.val + 1) (rows j)) = allocatedPartitionedJetMatrix B U b S x u v rows :=
    funext (fun j => (allocatedPartitionedJetMatrix_eq_physical B U b S x u v rows j).symm)
  have hc : coefficientAxisEquiv (LayerSamplerVariables G I n B) I n
      ((allocatedCoefficientSplit B U b S).symm (a₀, a₁)) i.val = a₀ i :=
    coefficientAxisSplitEquiv_symm_left grid a₀ a₁ i
  rw [hm, hc]
  rfl

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCoveredFixedTest
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v w : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "axis" => coefficientJetAxisEquiv O I n
local notation "join" => MeasurableEquiv.piEquivPiSubtypeProd (CoefficientJetAxisRow O) grid
local notation "split" => allocatedCoefficientSplit B U b S
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

theorem allocatedMixedJetReconstruct_measurable [∀ j, Fintype (O j)] :
    Measurable (fun p : AllocatedFrozenCoefficients B U b S × AllocatedLongJetRows B U b S O =>
      allocatedMixedJetReconstruct B U b S x u w rows p.1 p.2) :=
  (axis).symm.measurable.comp ((join).symm.measurable.comp
    (((allocatedFrozenJetMap_measurable B U b S x u w rows).comp measurable_fst).prodMk measurable_snd))

theorem allocatedMixedJetReconstruct_physical
    (a₀ : AllocatedFrozenCoefficients B U b S) (a₁ : AllocatedLongCoefficients B U b S)
    (ha : AllocatedFrozenSupported B U b hR hσ S a₀) :
    allocatedMixedJetReconstruct B U b S x u w rows a₀
        (allocatedLongJetMap B U b S x u v rows a₁) =
      canonicalCoefficientJetArrays (root v) (dirs v) rows ((split).symm (a₀, a₁)) := by
  apply (axis).injective
  apply (join).injective
  simp only [allocatedMixedJetReconstruct, MeasurableEquiv.apply_symm_apply]
  apply Prod.ext
  · funext i
    change allocatedFrozenJetMap B U b S x u w rows a₀ i =
      axis (canonicalCoefficientJetArrays (root v) (dirs v) rows ((split).symm (a₀, a₁))) i.val
    rw [allocatedPhysicalJet_grid_reconstruct]
    exact congrFun (allocatedFrozenJetMap_eq_of_supported B U b hR hσ S x u w v rows a₀ ha) i
  · funext i
    change allocatedLongJetMap B U b S x u v rows a₁ i =
      allocatedPhysicalLongJetMap B U b S x u v rows ((split).symm (a₀, a₁)) i
    exact congrFun (allocatedPhysicalLongJetMap_reconstruct B U b S x u v rows a₀ a₁).symm i

theorem allocatedMixedJetReconstruct_physical_split
    (a : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (ha : AllocatedFrozenSupported B U b hR hσ S (split a).1) :
    allocatedMixedJetReconstruct B U b S x u w rows (split a).1
        (allocatedPhysicalLongJetMap B U b S x u v rows a) =
      canonicalCoefficientJetArrays (root v) (dirs v) rows a := by
  rw [allocatedPhysicalLongJetMap_split]
  simpa only [Prod.mk.eta, MeasurableEquiv.symm_apply_apply] using
    allocatedMixedJetReconstruct_physical B U b hR hσ S x u v w rows (split a).1 (split a).2 ha

theorem allocatedCoefficientSource_frozen_supported :
    ∀ᵐ a ∂allocatedCoefficientSource B U b hR hσ S,
      AllocatedFrozenSupported B U b hR hσ S (split a).1 := by
  let : IsProbabilityMeasure (allocatedLongCoefficientSource B U b hR hσ S) :=
    allocatedLongCoefficientSource_probability B U b hR hσ S
  exact (allocatedCoefficientSplit_measurePreserving B U b hR hσ S).quasiMeasurePreserving.ae
    (Measure.quasiMeasurePreserving_fst.ae (allocatedFrozenCoefficientSource_supported B U b hR hσ S))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α) (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "split" => allocatedCoefficientSplit B U b S
local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "reference" => allocatedLongJetReference B U b S O
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

theorem allocatedPhysicalMixedJet_test_mean
    (weights : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (φ : AllocatedFrozenCoefficients B U b S →
      (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) → ℂ)
    (hφ : Measurable (fun p : AllocatedFrozenCoefficients B U b S ×
      (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) => φ p.1 p.2))
    {C : ℝ} (hbound : ∀ a t, ‖φ a t‖ ≤ C) :
    (∫ a, weights.complexMean (fun v => φ (split a).1
      (canonicalCoefficientJetArrays (root v) (dirs v) rows a)) ∂source) =
      ∫ a₀, ∫ z,
        (weights.mean (fun v => allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z) : ℂ) *
          φ a₀ (allocatedMixedJetReconstruct B U b S x u v₀ rows a₀ z) ∂reference ∂frozenSource := by
  have htest : Measurable (fun p : AllocatedFrozenCoefficients B U b S × AllocatedLongJetRows B U b S O =>
      φ p.1 (allocatedMixedJetReconstruct B U b S x u v₀ rows p.1 p.2)) :=
    hφ.comp (measurable_fst.prodMk (allocatedMixedJetReconstruct_measurable B U b S x u v₀ rows))
  calc
    _ = ∫ a, weights.complexMean (fun v => φ (split a).1
        (allocatedMixedJetReconstruct B U b S x u v₀ rows (split a).1
          (allocatedPhysicalLongJetMap B U b S x u v rows a))) ∂source := by
      apply integral_congr_ae
      filter_upwards [allocatedCoefficientSource_frozen_supported B U b hR hσ S] with a ha
      apply congrArg weights.complexMean
      funext v
      rw [allocatedMixedJetReconstruct_physical_split B U b hR hσ S x u v v₀ rows a ha]
    _ = ∫ a₀, ∫ z, weights.complexMean (fun v =>
        (allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z : ℂ) *
          φ a₀ (allocatedMixedJetReconstruct B U b S x u v₀ rows a₀ z)) ∂reference ∂frozenSource :=
      allocatedPhysicalLongJet_variable_test_mean B U b hR hσ S x u rows s hA hσ1 weights
        (fun _ a₀ z => φ a₀ (allocatedMixedJetReconstruct B U b S x u v₀ rows a₀ z))
        (fun _ => htest) (fun _ a₀ z => hbound a₀ _)
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro a₀
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      exact weights.complexMean_ofReal_mul _ _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

variable (φ : (AllocatedFrozenCoefficients B U b S ×
  (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))) × (∀ j, O j → Q j → ZMod d) → ℂ)

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : AllocatedFrozenCoefficients B U b S × EuclideanJetLayers U O → ℂ)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedPhysicalMixedJet_test_mean.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedPhysicalMixedJet_test_mean.{u_1, u_2, u_3, u_4, u_5, u_6}
