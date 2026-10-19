-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedFiniteModelPhysicalCoefficientMass_le_exp_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:01:44.047325+00:00
-- url     : https://prove2.me/submissions/019b8213-4661-40f8-81c8-d072c0a7fee3

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B216

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BufferedSiteExpansion
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal

theorem finiteNestedSiteExpansion_mass {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (c : ℂ) (a : A → B → ℂ) (b : C → ℂ) :
    (∑ i, ∑ j, ∑ k, ‖(c * a i j) * b k‖) =
      ‖c‖ * (∑ i, ∑ j, ‖a i j‖) * (∑ k, ‖b k‖) := by
  simp only [norm_mul, ← Finset.mul_sum, ← Finset.sum_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedResidueLabelCount
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {n : Fin m → ℕ}
variable {J E : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

include hb bW in
theorem allocatedResidueLabel_card (period : ℕ) [NeZero period] :
    Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) =
      period ^ (∑ j, Fintype.card (J j)) := by
  have hc (j) : n j + Fintype.card (E j) = Fintype.card (J j) := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using
      standardLatticeCoordinates_card (euclideanSubspace (U j)) (bW j) (b j) (hb j)
  simp only [Fintype.card_prod, Fintype.card_pi, ZMod.card,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.prod_mul_distrib]
  simp_rw [← pow_add, hc]
  exact Finset.prod_pow_eq_pow_sum _ _ _

include hb bW in
theorem allocatedResidueLabels_le_exp {S : Type*} [Fintype S]
    (period : ℕ) [NeZero period] {P : ℝ} (hperiod : (period : ℝ) ≤ Real.exp P) :
    (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ Fintype.card S ≤
      Real.exp (Fintype.card S * ((∑ j, Fintype.card (J j) : ℕ) * P)) := by
  rw [allocatedResidueLabel_card U b hb bW, Nat.cast_pow, Real.exp_nat_mul, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by positivity)
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hperiod _) _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {A S : Type*} [Fintype A] [Fintype S]
variable {I : A → Type*} [∀ a, Fintype (I a)]

theorem finite_site_product_coefficient_norm (c : ∀ a, I a → ℂ) :
    (∑ k : ∀ a, I a, ‖∏ a, c a (k a)‖) = ∏ a, ∑ k, ‖c a k‖ := by
  simp only [norm_prod, Fintype.prod_sum]

theorem finite_site_product_coefficient_norm_le (c : ∀ a, I a → ℂ)
    (C : A → ℝ) (hc : ∀ a, (∑ k, ‖c a k‖) ≤ C a) :
    (∑ k : ∀ a, I a, ‖∏ a, c a (k a)‖) ≤ ∏ a, C a := by
  rw [finite_site_product_coefficient_norm]
  exact Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (fun a _ => hc a)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

attribute [local instance] ScalarSiteExpansion.termFinite

universe u v w

variable {A : Type u} {S : Type v} [Fintype A] [Fintype S]
variable (e : A → ScalarSiteExpansion.{v,w} S)

variable {T D C H : A → ℝ} {L : ℝ≥0}
variable (h : ∀ a, (e a).Bounds (T a) (D a) (C a) L (H a))

include h in
omit [Fintype S] in
theorem siteFamily_coefficient_le : (∑ k, ‖siteFamilyCoefficient e k‖) ≤ ∏ a, C a :=
  finite_site_product_coefficient_norm_le (fun a => (e a).coefficient) C
    (fun a => (h a).coefficient_le)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedIdealPhysicalCover
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

theorem coverSiteCoefficient_bound {A S : Type*} [Fintype A] [Fintype S]
    (e : A → ScalarSiteExpansion S) {T V C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a)) :
    (∑ k, ‖coverSiteCoefficient e k‖) ≤ (2 : ℝ) ^ Fintype.card S * ∏ a, C a := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  simp only [coverSiteCoefficient, norm_mul, norm_pow, h2, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (siteFamily_coefficient_le e he) (by positivity)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedPhysicalExpansionMass
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

theorem allocatedFiniteModelPhysicalCoefficientMass_le
    {A : ℝ} (hA : (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
      ∑ i, ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤ A)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a)) :
    (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
      ∑ i, ∑ k, ‖((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) * coverSiteCoefficient e k‖) ≤
      (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * A *
        ((2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, Cc a) := by
  rw [finiteNestedSiteExpansion_mass]
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [norm_pow, htwo]
  have hA0 : 0 ≤ A := (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))).trans hA
  exact mul_le_mul (mul_le_mul_of_nonneg_left hA (by positivity))
    (coverSiteCoefficient_bound e he) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (mul_nonneg (by positivity) hA0)

include hb bW in

theorem allocatedFiniteModelPhysicalCoefficientMass_le_exp_s2_oai
    {M F A Pper Op : ℝ} (hM : 0 ≤ M)
    (hpref : ‖inverseNormalizer‖ *
      (M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period) ≤ Real.exp F)
    (hperiod : (period : ℝ) ≤ Real.exp Pper)
    (hA : (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
      ∑ i, ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤
      ‖inverseNormalizer‖ *
        ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^
          Fintype.card (Finset (Fin dim)) *
          (M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period) * Real.exp A))
    {Nt V Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Real.exp Op) Lg (Hs a)) :
    (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
      ∑ i, ∑ k, ‖((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) * coverSiteCoefficient e k‖) ≤
      Real.exp (2 * Fintype.card (Finset (Fin dim)) + F +
        Fintype.card (Finset (Fin dim)) * ((∑ j, Fintype.card (J j) : ℕ) * Pper) + A +
        Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} * Op) := by
  let sites := Fintype.card (Finset (Fin dim))
  let labelLog : ℝ := sites * ((∑ j, Fintype.card (J j) : ℕ) * Pper)
  have hlabels := allocatedResidueLabels_le_exp (S := Finset (Fin dim)) U b hb bW period hperiod
  have hlong : (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
      ∑ i, ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤
      Real.exp (F + labelLog + A) := by
    apply hA.trans
    calc
      _ = (‖inverseNormalizer‖ *
          (M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period)) *
          ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ sites * Real.exp A) := by ring
      _ ≤ Real.exp F * (Real.exp labelLog * Real.exp A) :=
        mul_le_mul hpref (mul_le_mul_of_nonneg_right hlabels (Real.exp_nonneg _))
          (by positivity) ((mul_nonneg (norm_nonneg _)
            (mul_nonneg (pow_nonneg hM _) (coefficientDeckPeriodCap_nonneg rowTypes E period))).trans hpref)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, add_assoc]
  have htwo : (2 : ℝ) ^ sites ≤ Real.exp sites := by
    rw [show (sites : ℝ) = sites * (1 : ℝ) by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) _
  apply (allocatedFiniteModelPhysicalCoefficientMass_le B U b S x y₀ q d period e a hlong he).trans
  simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
  calc
    _ ≤ (Real.exp sites * Real.exp (F + labelLog + A)) *
        (Real.exp sites * Real.exp (Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} * Op)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _))
        (mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)) (by positivity) (by positivity)
    _ = _ := by simp only [← Real.exp_add]; congr 1; dsimp [sites, labelLog]; ring

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedFiniteModelPhysicalCoefficientMass_le_exp_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedFiniteModelPhysicalCoefficientMass_le_exp_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
