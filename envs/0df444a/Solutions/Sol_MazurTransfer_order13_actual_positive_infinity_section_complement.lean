-- Prove2me | solution 1 for MazurTransfer.order13_actual_positive_infinity_section_complement
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T07:20:44.084824+00:00
-- url     : https://prove2.me/submissions/c80eefe9-0e93-43a3-901c-e54fba82ffc4

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual section and its exact open complement on the
literal two-chart curve over every commutative ring. Named downstream
consumer: affine identification and single-section FiniteMapData.
Per-file attribution and complete selected source declarations follow.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve

open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: two actual infinity sections of the literal order-13 curve
for every commutative base ring, constructed from reciprocal coordinates.
Named downstream consumer: integral Picard representability with a section.
No rational-point classification or Picard representability is assumed.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13IntegralSections
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
variable (R : Type u) [CommRing R]

private theorem reciprocalEquation_eval (a : R) (ha : a ^ 2 = 1) :
    (reciprocalEquation R).eval₂ (Polynomial.evalRingHom (0 : R)) a = 0 := by
  simp [reciprocalEquation, reciprocalPolynomial, ha, eval₂_pow, eval₂_C]

noncomputable def reciprocalInfinityEvaluation (a : R) (ha : a ^ 2 = 1) :
    ReciprocalRing R →+* R :=
  AdjoinRoot.lift (Polynomial.evalRingHom (0 : R)) a
    (reciprocalEquation_eval R a ha)

theorem reciprocalInfinityEvaluation_z (a : R) (ha : a ^ 2 = 1) :
    reciprocalInfinityEvaluation R a ha (zCoordinate R) = 0 := by
  simp [reciprocalInfinityEvaluation, zCoordinate, AdjoinRoot.lift_of]

theorem reciprocalInfinityEvaluation_w (a : R) (ha : a ^ 2 = 1) :
    reciprocalInfinityEvaluation R a ha (wCoordinate R) = a := by
  simp [reciprocalInfinityEvaluation, wCoordinate, AdjoinRoot.lift_root]

theorem reciprocalInfinityEvaluation_comp_algebraMap (a : R) (ha : a ^ 2 = 1) :
    (reciprocalInfinityEvaluation R a ha).comp
      (algebraMap R (ReciprocalRing R)) = RingHom.id R := by
  ext r
  simp [reciprocalInfinityEvaluation, AdjoinRoot.algebraMap_eq',
    AdjoinRoot.lift_of]

noncomputable def infinityMorphism (a : R) (ha : a ^ 2 = 1) :
    Spec (.of R) ⟶ curveScheme R :=
  Spec.map (CommRingCat.ofHom (reciprocalInfinityEvaluation R a ha)) ≫ reciprocalChartMap R

theorem infinityMorphism_curveToBase (a : R) (ha : a ^ 2 = 1) :
    infinityMorphism R a ha ≫ curveToBase R = 𝟙 _ := by
  rw [infinityMorphism, Category.assoc, reciprocalChartMap_curveToBase]
  unfold reciprocalChartToBase
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap R (ReciprocalRing R)) ≫
      CommRingCat.ofHom (reciprocalInfinityEvaluation R a ha) = 𝟙 _ := by
    exact congrArg CommRingCat.ofHom
      (reciprocalInfinityEvaluation_comp_algebraMap R a ha)
  rw [h, Spec.map_id]


end MazurTransfer.Order13IntegralSections

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: exact integral coordinate identities for the candidate
single-infinity pole function and a rank-three finite algebra presentation.
Named downstream consumer: actual single-section FiniteMapData.
These are coordinate-ring identities only. No pole order, affine-open
identification, freeness or finite scheme morphism is claimed here.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13SingleSectionFiniteMapIdentities
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
variable (R : Type u) [CommRing R]

def a : CoordinateRing R := xCoordinate R ^ 3 + xCoordinate R ^ 2 + 1
def t : CoordinateRing R := yCoordinate R + a R
def p : CoordinateRing R := xCoordinate R * t R
def q : CoordinateRing R := xCoordinate R * (p R + 2)

theorem candidate_equation :
    t R ^ 2 - 2 * t R * (xCoordinate R ^ 3 + xCoordinate R ^ 2 + 1) -
      4 * xCoordinate R * (xCoordinate R + 1) = 0 := by
  have hy := yCoordinate_sq R
  simp only [sexticPolynomial, map_add, map_mul, map_pow, _root_.map_ofNat, _root_.map_one, aeval_X] at hy
  dsimp [t, a]
  linear_combination hy

theorem p_squared : p R ^ 2 = t R * q R - 2 * p R := by
  dsimp [p, q]
  ring

theorem twice_p_mul_q :
    2 * p R * q R = t R ^ 3 - 2 * t R ^ 2 - 2 * t R * q R := by
  have h := candidate_equation R
  dsimp [p, q]
  linear_combination -(t R) * h

theorem twice_q_squared :
    2 * q R ^ 2 = (t R ^ 2 - 2 * t R) * p R + (2 * t R - 4) * q R +
      (2 - t R) * (t R ^ 2 - 2 * t R) := by
  have h := candidate_equation R
  dsimp [p, q]
  linear_combination (-(t R) * xCoordinate R + t R - 2) * h

theorem reciprocal_difference_of_squares :
    (wCoordinate R + (1 + zCoordinate R + zCoordinate R ^ 3)) *
      (wCoordinate R - (1 + zCoordinate R + zCoordinate R ^ 3)) =
      4 * zCoordinate R ^ 4 * (1 + zCoordinate R) := by
  have hw := wCoordinate_sq R
  simp only [reciprocalPolynomial, map_add, map_mul, map_pow, _root_.map_ofNat, _root_.map_one, aeval_X] at hw
  linear_combination hw

theorem reciprocal_second_difference_of_squares :
    (wCoordinate R + (1 + zCoordinate R - zCoordinate R ^ 3)) *
      (wCoordinate R - (1 + zCoordinate R - zCoordinate R ^ 3)) =
      4 * zCoordinate R ^ 3 * (1 + zCoordinate R) ^ 2 := by
  have hw := wCoordinate_sq R
  simp only [reciprocalPolynomial, map_add, map_mul, map_pow, _root_.map_ofNat, _root_.map_one, aeval_X] at hw
  linear_combination hw

end MazurTransfer.Order13SingleSectionFiniteMapIdentities
#print axioms MazurTransfer.Order13SingleSectionFiniteMapIdentities.candidate_equation
#print axioms MazurTransfer.Order13SingleSectionFiniteMapIdentities.p_squared
#print axioms MazurTransfer.Order13SingleSectionFiniteMapIdentities.twice_p_mul_q
#print axioms MazurTransfer.Order13SingleSectionFiniteMapIdentities.twice_q_squared
#print axioms MazurTransfer.Order13SingleSectionFiniteMapIdentities.reciprocal_difference_of_squares
#print axioms MazurTransfer.Order13SingleSectionFiniteMapIdentities.reciprocal_second_difference_of_squares

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a literal reciprocal principal-open neighborhood of the
negative infinity section, its unit denominators and regular parameter
coordinates. Named downstream consumer: the third chart in the actual
single-section complement comparison. No algebra or scheme isomorphism
with the candidate algebra is assumed or asserted here.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13SingleSectionReciprocalPatch
open Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
variable (R : Type u) [CommRing R]

def d : ReciprocalRing R := wCoordinate R - 1 - zCoordinate R - zCoordinate R ^ 3
def dPrime : ReciprocalRing R := wCoordinate R - 1 - zCoordinate R + zCoordinate R ^ 3
def remainingFactor : ReciprocalRing R :=
  1 + zCoordinate R + zCoordinate R ^ 3 + 2 * zCoordinate R ^ 4 - wCoordinate R

theorem denominator_product_factorization :
    d R * dPrime R = 2 * (1 + zCoordinate R) * remainingFactor R := by
  have hw := wCoordinate_sq R
  simp only [reciprocalPolynomial,map_add,map_mul,map_pow,_root_.map_ofNat,_root_.map_one,aeval_X] at hw
  dsimp [d,dPrime,remainingFactor]
  linear_combination hw

abbrev PatchRing := Localization.Away (d R * dPrime R)
def z : PatchRing R := algebraMap (ReciprocalRing R) (PatchRing R) (zCoordinate R)
def w : PatchRing R := algebraMap (ReciprocalRing R) (PatchRing R) (wCoordinate R)
def D : PatchRing R := algebraMap (ReciprocalRing R) (PatchRing R) (d R)
def DPrime : PatchRing R := algebraMap (ReciprocalRing R) (PatchRing R) (dPrime R)

theorem D_mul_DPrime_isUnit : IsUnit (D R * DPrime R) := by
  change IsUnit (algebraMap (ReciprocalRing R) (PatchRing R) (d R) *
    algebraMap (ReciprocalRing R) (PatchRing R) (dPrime R))
  rw [← map_mul]
  exact IsLocalization.Away.algebraMap_isUnit (d R * dPrime R)

theorem D_isUnit : IsUnit (D R) := isUnit_of_mul_isUnit_left (D_mul_DPrime_isUnit R)
theorem DPrime_isUnit : IsUnit (DPrime R) := isUnit_of_mul_isUnit_right (D_mul_DPrime_isUnit R)

theorem one_add_z_isUnit : IsUnit (1 + z R) := by
  let φ : ReciprocalRing R →+* PatchRing R := algebraMap _ _
  have heq : D R * DPrime R = 2 * (1 + z R) * φ (remainingFactor R) := by
    calc
      _ = φ (d R * dPrime R) := (φ.map_mul _ _).symm
      _ = φ (2 * (1 + zCoordinate R) * remainingFactor R) :=
        congrArg φ (denominator_product_factorization R)
      _ = _ := by simp only [map_mul,map_add,map_one,_root_.map_ofNat]; rfl
  have h := D_mul_DPrime_isUnit R
  rw [heq] at h
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h)

def dInverse : PatchRing R := DPrime R * IsLocalization.Away.invSelf (d R * dPrime R)
def dPrimeInverse : PatchRing R := D R * IsLocalization.Away.invSelf (d R * dPrime R)

theorem D_mul_dInverse : D R * dInverse R = 1 := by
  rw [dInverse,← mul_assoc]
  change algebraMap (ReciprocalRing R) (PatchRing R) (d R) *
    algebraMap (ReciprocalRing R) (PatchRing R) (dPrime R) * _ = 1
  rw [← map_mul,IsLocalization.Away.mul_invSelf]

theorem DPrime_mul_dPrimeInverse : DPrime R * dPrimeInverse R = 1 := by
  rw [dPrimeInverse,← mul_assoc,mul_comm (DPrime R) (D R)]
  change algebraMap (ReciprocalRing R) (PatchRing R) (d R) *
    algebraMap (ReciprocalRing R) (PatchRing R) (dPrime R) * _ = 1
  rw [← map_mul,IsLocalization.Away.mul_invSelf]

def tau : PatchRing R := 4 * z R * (1 + z R) * dInverse R
def mu : PatchRing R := 4 * (1 + z R) * dInverse R
def nu : PatchRing R := 8 * z R ^ 2 * (1 + z R) ^ 2 * dInverse R * dPrimeInverse R

theorem tau_eq_z_mul_mu : tau R = z R * mu R := by dsimp [tau,mu]; ring

theorem z_mul_nu : z R * nu R = mu R + 2 := by
  have hz := congrArg (algebraMap (ReciprocalRing R) (PatchRing R))
    (Order13SingleSectionFiniteMapIdentities.reciprocal_second_difference_of_squares R)
  simp only [map_mul,map_add,map_sub,map_pow,map_one,_root_.map_ofNat] at hz
  have hD := D_mul_dInverse R
  have hDP := DPrime_mul_dPrimeInverse R
  simp only [D,DPrime,d,dPrime,z,w,map_sub,map_add,map_pow,map_one] at hD hDP
  dsimp [tau,mu,nu,z,w]
  linear_combination
    -(2 * dInverse R * dPrimeInverse R) * hz +
      (2 * (algebraMap (ReciprocalRing R) (PatchRing R) (wCoordinate R) +
        1 + algebraMap (ReciprocalRing R) (PatchRing R) (zCoordinate R) -
          algebraMap (ReciprocalRing R) (PatchRing R) (zCoordinate R) ^ 3) * dInverse R) * hDP +
      2 * hD

theorem mu_squared : mu R ^ 2 = tau R * nu R - 2 * mu R := by
  rw [tau_eq_z_mul_mu]
  have h := z_mul_nu R
  linear_combination -(mu R) * h

theorem mu_mul_D : mu R * D R = 4 * (1 + z R) := by
  rw [mu]
  calc
    _ = 4 * (1 + z R) * (D R * dInverse R) := by ring
    _ = _ := by rw [D_mul_dInverse,mul_one]

theorem mu_isUnit (h2 : IsUnit (2 : R)) : IsUnit (mu R) := by
  have h4 : IsUnit (4 : PatchRing R) := by
    have h := (h2.map (algebraMap R (PatchRing R))).pow 2
    simpa only [_root_.map_ofNat,show (2 : PatchRing R) ^ 2 = 4 by ring] using h
  have h := h4.mul (one_add_z_isUnit R)
  rw [← mu_mul_D] at h
  exact isUnit_of_mul_isUnit_left h

theorem mu_mul_mu_add_tau_isUnit (h2 : IsUnit (2 : R)) :
    IsUnit (mu R * (mu R + tau R)) := by
  have heq : mu R + tau R = mu R * (1 + z R) := by rw [tau_eq_z_mul_mu]; ring
  rw [heq]
  exact (mu_isUnit R h2).mul ((mu_isUnit R h2).mul (one_add_z_isUnit R))

theorem negative_infinity_denominator :
    Order13IntegralSections.reciprocalInfinityEvaluation R (-1) (by simp) (d R * dPrime R) = 4 := by
  simp [d,dPrime,Order13IntegralSections.reciprocalInfinityEvaluation_z,
    Order13IntegralSections.reciprocalInfinityEvaluation_w]
  ring

theorem positive_infinity_denominator :
    Order13IntegralSections.reciprocalInfinityEvaluation R 1 (by simp) (d R * dPrime R) = 0 := by
  simp [d,dPrime,Order13IntegralSections.reciprocalInfinityEvaluation_z,
    Order13IntegralSections.reciprocalInfinityEvaluation_w]

end MazurTransfer.Order13SingleSectionReciprocalPatch
#print axioms MazurTransfer.Order13SingleSectionReciprocalPatch.z_mul_nu
#print axioms MazurTransfer.Order13SingleSectionReciprocalPatch.mu_squared
#print axioms MazurTransfer.Order13SingleSectionReciprocalPatch.mu_mul_mu_add_tau_isUnit
#print axioms MazurTransfer.Order13SingleSectionReciprocalPatch.negative_infinity_denominator
#print axioms MazurTransfer.Order13SingleSectionReciprocalPatch.positive_infinity_denominator

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact prime-spectrum complement identity of the actual
reciprocal denominator patch together with the punctured reciprocal chart.
Named downstream consumer: identifying the chosen positive-infinity
complement after proving its evaluation kernel and global chart images.
No section-image or whole-curve complement identification is asserted.
-/

noncomputable section
namespace MazurTransfer.Order13ReciprocalPatchPrimeComplement
variable {A : Type*} [CommRing A]

theorem denominator_mod_z_identity (z w : A) :
    (w - 1 - z - z ^ 3) * (w - 1 - z + z ^ 3) =
      (w - 1) ^ 2 + z * (-2 * w + 2 + z - z ^ 5) := by ring

theorem denominator_mem_prime_iff (z w : A) (I : Ideal A) [I.IsPrime] (hz : z ∈ I) :
    (w - 1 - z - z ^ 3) * (w - 1 - z + z ^ 3) ∈ I ↔ w - 1 ∈ I := by
  rw [denominator_mod_z_identity]
  have hm : z * (-2 * w + 2 + z - z ^ 5) ∈ I := I.mul_mem_right _ hz
  constructor
  · intro h
    have hs : (w - 1) ^ 2 ∈ I := by
      have hh := I.sub_mem h hm
      simpa only [add_sub_cancel_right] using hh
    rw [pow_two] at hs
    exact (Ideal.IsPrime.mem_or_mem (inferInstance : I.IsPrime) hs).elim id id
  · intro hw
    exact I.add_mem (by simpa only [pow_two] using I.mul_mem_left (w - 1) hw) hm

universe u
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13SingleSectionReciprocalPatch
variable (R : Type u) [CommRing R]

theorem actual_denominator_mem_prime_iff (I : Ideal (ReciprocalRing R)) [I.IsPrime]
    (hz : zCoordinate R ∈ I) : d R * dPrime R ∈ I ↔ wCoordinate R - 1 ∈ I :=
  denominator_mem_prime_iff (zCoordinate R) (wCoordinate R) I hz

theorem actual_reciprocal_two_open_union :
    PrimeSpectrum.basicOpen (zCoordinate R) ⊔ PrimeSpectrum.basicOpen (d R * dPrime R) =
      PrimeSpectrum.basicOpen (zCoordinate R) ⊔ PrimeSpectrum.basicOpen (wCoordinate R - 1) := by
  ext p
  change (zCoordinate R ∉ p.asIdeal ∨ d R * dPrime R ∉ p.asIdeal) ↔
    (zCoordinate R ∉ p.asIdeal ∨ wCoordinate R - 1 ∉ p.asIdeal)
  by_cases hz : zCoordinate R ∈ p.asIdeal
  · have h := actual_denominator_mem_prime_iff R p.asIdeal hz
    simp only [hz,not_true_eq_false,false_or,h]
  · simp only [hz,not_false_eq_true,true_or]

end MazurTransfer.Order13ReciprocalPatchPrimeComplement
#print axioms MazurTransfer.Order13ReciprocalPatchPrimeComplement.denominator_mem_prime_iff
#print axioms MazurTransfer.Order13ReciprocalPatchPrimeComplement.actual_reciprocal_two_open_union

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact kernel and surjectivity of the actual positive
infinity evaluation on the reciprocal chart over every commutative ring.
Named downstream consumer: its closed image and the single-section complement.
No whole-curve complement or global gluing is asserted.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13PositiveInfinityEvaluationKernel
open Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13IntegralSections
variable (R : Type u) [CommRing R]

def evaluation : ReciprocalRing R →+* R := reciprocalInfinityEvaluation R 1 (by simp)
def evaluationAlgHom : ReciprocalRing R →ₐ[R] R where
  __ := evaluation R
  commutes' r := by
    exact RingHom.congr_fun (reciprocalInfinityEvaluation_comp_algebraMap R 1 (by simp)) r

def sectionIdeal : Ideal (ReciprocalRing R) := Ideal.span {zCoordinate R,wCoordinate R - 1}
def quotientMap : ReciprocalRing R →ₐ[R] ReciprocalRing R ⧸ sectionIdeal R :=
  Ideal.Quotient.mkₐ R (sectionIdeal R)

theorem quotientMap_z : quotientMap R (zCoordinate R) = 0 := by
  exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (by simp))
theorem quotientMap_w : quotientMap R (wCoordinate R) = 1 := by
  have h : quotientMap R (wCoordinate R - 1) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (by simp))
  rw [map_sub,map_one] at h
  exact sub_eq_zero.mp h

theorem quotientMap_factorization : quotientMap R =
    (Algebra.ofId R (ReciprocalRing R ⧸ sectionIdeal R)).comp (evaluationAlgHom R) := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change quotientMap R (zCoordinate R) =
      algebraMap R (ReciprocalRing R ⧸ sectionIdeal R) (reciprocalInfinityEvaluation R 1 (by simp) (zCoordinate R))
    rw [quotientMap_z,reciprocalInfinityEvaluation_z,map_zero]
  · change quotientMap R (wCoordinate R) =
      algebraMap R (ReciprocalRing R ⧸ sectionIdeal R) (reciprocalInfinityEvaluation R 1 (by simp) (wCoordinate R))
    rw [quotientMap_w,reciprocalInfinityEvaluation_w,map_one]

theorem sectionIdeal_le_kernel : sectionIdeal R ≤ RingHom.ker (evaluation R) := by
  apply Ideal.span_le.mpr
  intro b hb
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl
  · change reciprocalInfinityEvaluation R 1 (by simp) (zCoordinate R) = 0
    exact reciprocalInfinityEvaluation_z R 1 (by simp)
  · change evaluation R (wCoordinate R - 1) = 0
    simp only [evaluation,map_sub,map_one,reciprocalInfinityEvaluation_w,sub_self]

theorem evaluation_kernel : RingHom.ker (evaluation R) = sectionIdeal R := by
  apply le_antisymm
  · intro a ha
    change evaluation R a = 0 at ha
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change quotientMap R a = 0
    have h := DFunLike.congr_fun (quotientMap_factorization R) a
    change quotientMap R a = algebraMap R (ReciprocalRing R ⧸ sectionIdeal R) (evaluation R a) at h
    rw [ha,map_zero] at h
    exact h
  · exact sectionIdeal_le_kernel R

theorem evaluation_surjective : Function.Surjective (evaluation R) := by
  intro r
  refine ⟨algebraMap R (ReciprocalRing R) r,?_⟩
  exact RingHom.congr_fun (reciprocalInfinityEvaluation_comp_algebraMap R 1 (by simp)) r

end MazurTransfer.Order13PositiveInfinityEvaluationKernel
#print axioms MazurTransfer.Order13PositiveInfinityEvaluationKernel.evaluation_kernel
#print axioms MazurTransfer.Order13PositiveInfinityEvaluationKernel.evaluation_surjective

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual positive infinity closed image in the reciprocal
chart and its exact principal-open complement. Named downstream consumer:
identification of the positive section complement in the glued curve.
No whole-curve gluing or single-section affine identification is asserted.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13PositiveInfinityReciprocalImage
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13PositiveInfinityEvaluationKernel
open Order13SingleSectionReciprocalPatch
variable (R : Type u) [CommRing R]

def evaluationSchemeMap : Spec (.of R) ⟶ reciprocalScheme R :=
  Spec.map (CommRingCat.ofHom (evaluation R))

theorem evaluationSchemeMap_isClosedImmersion : IsClosedImmersion (evaluationSchemeMap R) :=
  IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (evaluation R)) (evaluation_surjective R)

theorem evaluationSchemeMap_range : Set.range (evaluationSchemeMap R) =
    PrimeSpectrum.zeroLocus (sectionIdeal R : Set (ReciprocalRing R)) := by
  change Set.range (PrimeSpectrum.comap (evaluation R)) = _
  rw [range_comap_of_surjective R (evaluation R) (evaluation_surjective R),evaluation_kernel]

theorem mem_evaluationSchemeMap_range (p : PrimeSpectrum (ReciprocalRing R)) :
    p ∈ Set.range (evaluationSchemeMap R) ↔ zCoordinate R ∈ p.asIdeal ∧ wCoordinate R - 1 ∈ p.asIdeal := by
  change p ∈ Set.range (PrimeSpectrum.comap (evaluation R)) ↔ _
  have h : Set.range (PrimeSpectrum.comap (evaluation R)) =
      PrimeSpectrum.zeroLocus (sectionIdeal R : Set (ReciprocalRing R)) := evaluationSchemeMap_range R
  rw [h,sectionIdeal,PrimeSpectrum.zeroLocus_span,PrimeSpectrum.mem_zeroLocus]
  simp only [Set.insert_subset_iff,Set.singleton_subset_iff]
  rfl

theorem evaluationSchemeMap_range_complement :
    (Set.range (evaluationSchemeMap R))ᶜ =
      (PrimeSpectrum.basicOpen (zCoordinate R) ⊔
        PrimeSpectrum.basicOpen (d R * dPrime R) : Set (PrimeSpectrum (ReciprocalRing R))) := by
  change (Set.range (PrimeSpectrum.comap (evaluation R)))ᶜ =
    (PrimeSpectrum.basicOpen (zCoordinate R) : Set (PrimeSpectrum (ReciprocalRing R))) ∪
      (PrimeSpectrum.basicOpen (d R * dPrime R) : Set (PrimeSpectrum (ReciprocalRing R)))
  ext p
  change ¬ p ∈ Set.range (PrimeSpectrum.comap (evaluation R)) ↔
    zCoordinate R ∉ p.asIdeal ∨ d R * dPrime R ∉ p.asIdeal
  have he : p ∈ Set.range (PrimeSpectrum.comap (evaluation R)) ↔
      zCoordinate R ∈ p.asIdeal ∧ wCoordinate R - 1 ∈ p.asIdeal :=
    mem_evaluationSchemeMap_range R p
  rw [he]
  by_cases hz : zCoordinate R ∈ p.asIdeal
  · have hd := Order13ReciprocalPatchPrimeComplement.actual_denominator_mem_prime_iff R p.asIdeal hz
    simp only [hz,true_and,not_true_eq_false,false_or,hd]
  · simp only [hz,false_and,not_false_eq_true,true_or]

end MazurTransfer.Order13PositiveInfinityReciprocalImage
#print axioms MazurTransfer.Order13PositiveInfinityReciprocalImage.evaluationSchemeMap_isClosedImmersion
#print axioms MazurTransfer.Order13PositiveInfinityReciprocalImage.evaluationSchemeMap_range_complement

end
end

section
noncomputable section
universe u
namespace MazurTransfer.Order13IntegralHyperellipticMap
open CategoryTheory AlgebraicGeometry MazurTorsion
variable (K : Type u) [CommRing K]
private theorem ordinary_ne_reciprocal :
    (XOneThirteenProjectiveCurve.Chart.ordinary :
      XOneThirteenProjectiveCurve.Chart.{u}) ≠
      XOneThirteenProjectiveCurve.Chart.reciprocal := by
  intro h
  cases h

private theorem reciprocal_ne_ordinary :
    (XOneThirteenProjectiveCurve.Chart.reciprocal :
      XOneThirteenProjectiveCurve.Chart.{u}) ≠
      XOneThirteenProjectiveCurve.Chart.ordinary := by
  intro h
  cases h

private theorem ordinaryReciprocalOverlapInclusion_eq :
    XOneThirteenProjectiveCurve.overlapInclusion K
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal =
      Spec.map (CommRingCat.ofHom
        (algebraMap (XOneThirteenAffineCurve.CoordinateRing K)
          (XOneThirteenProjectiveCurve.OrdinaryOverlapRing K))) := by
  rfl

private theorem reciprocalOrdinaryOverlapInclusion_eq :
    XOneThirteenProjectiveCurve.overlapInclusion K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary =
      Spec.map (CommRingCat.ofHom
        (algebraMap (XOneThirteenProjectiveCurve.ReciprocalRing K)
          (XOneThirteenProjectiveCurve.ReciprocalOverlapRing K))) := by
  rfl

private theorem ordinaryReciprocalOverlapTransition_eq :
    XOneThirteenProjectiveCurve.overlapTransition K
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal =
      (XOneThirteenProjectiveCurve.overlapSchemeIso K).hom := by
  rfl

private theorem reciprocalOrdinaryOverlapTransition_eq :
    XOneThirteenProjectiveCurve.overlapTransition K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary =
      (XOneThirteenProjectiveCurve.overlapSchemeIso K).inv := by
  rfl

private instance reciprocalOverlapInclusion_isOpenImmersion :
    IsOpenImmersion
      (XOneThirteenProjectiveCurve.overlapInclusion K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        reciprocal_ne_ordinary) := by
  rw [reciprocalOrdinaryOverlapInclusion_eq]
  exact IsOpenImmersion.of_isLocalization
    (XOneThirteenProjectiveCurve.zCoordinate K)

private noncomputable abbrev reciprocalOverlapOpen :
    (XOneThirteenProjectiveCurve.chartScheme K
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})).Opens :=
  PrimeSpectrum.basicOpen (XOneThirteenProjectiveCurve.zCoordinate K)

private theorem reciprocalOverlapInclusion_opensRange :
    (XOneThirteenProjectiveCurve.overlapInclusion K
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})
      reciprocal_ne_ordinary).opensRange =
        reciprocalOverlapOpen K := by
  rw [SetLike.ext'_iff]
  exact PrimeSpectrum.localization_away_comap_range
    (XOneThirteenProjectiveCurve.ReciprocalOverlapRing K)
    (XOneThirteenProjectiveCurve.zCoordinate K)

private instance reciprocalGlueOverlap_isOpenImmersion :
    IsOpenImmersion
      ((XOneThirteenProjectiveCurve.glueData K).f
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})) :=
  (XOneThirteenProjectiveCurve.glueData K).f_open _ _

private theorem reciprocalGlueOverlap_opensRange :
    ((XOneThirteenProjectiveCurve.glueData K).f
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})).opensRange =
      reciprocalOverlapOpen K := by
  dsimp [XOneThirteenProjectiveCurve.glueData,
    XOneThirteenProjectiveCurve.categoricalGlueData,
    CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f',
    ordinary_ne_reciprocal, reciprocal_ne_ordinary]
  simp only [dif_neg reciprocal_ne_ordinary]
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact reciprocalOverlapInclusion_opensRange K

private theorem reciprocalChartMap_preimage_ordinaryChartMap_opensRange :
    XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange =
      ((XOneThirteenProjectiveCurve.glueData K).f
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})).opensRange := by
  apply TopologicalSpace.Opens.ext
  ext q
  change (XOneThirteenProjectiveCurve.reciprocalChartMap K q ∈
      (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange) ↔
    q ∈ ((XOneThirteenProjectiveCurve.glueData K).f
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})).opensRange
  constructor
  · rintro ⟨r, hr⟩
    have hrel :=
      ((XOneThirteenProjectiveCurve.glueData K).ι_eq_iff
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}) q r).mp hr.symm
    obtain ⟨x, hx, -⟩ := hrel
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    refine ⟨((XOneThirteenProjectiveCurve.glueData K).t
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u}) ≫
        (XOneThirteenProjectiveCurve.glueData K).f
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})) x, ?_⟩
    exact congrArg (fun f ↦ f x)
      ((XOneThirteenProjectiveCurve.glueData K).glue_condition
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}))

private theorem reciprocalOverlapOpen_eq_chartMap_preimage :
    reciprocalOverlapOpen K =
      XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange :=
  (reciprocalGlueOverlap_opensRange K).symm.trans
    (reciprocalChartMap_preimage_ordinaryChartMap_opensRange K).symm

/-- On the reciprocal chart, the overlap with the ordinary chart is exactly
the principal open where the reciprocal coordinate `z` is nonzero. -/
@[simp]
theorem reciprocalChartMap_preimage_ordinaryChartMap_opensRange_eq_basicOpen :
    XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange =
      PrimeSpectrum.basicOpen
        (XOneThirteenProjectiveCurve.zCoordinate K) := by
  exact (reciprocalOverlapOpen_eq_chartMap_preimage K).symm


end MazurTransfer.Order13IntegralHyperellipticMap

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: consume the retained exact chart-overlap proof as a set
range identity. Named downstream consumer: the actual positive infinity
complement in the whole two-chart curve. No affine identification is assumed.
Complete owned overlap proof retained in Order13IntegralCurveProperViaHyperellipticMap,
source SHA256 d0824f30d9fdce54da798e955c01eb49d50aacbaaaaa095490fa7585b4466856.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13ActualTwoChartRangeOverlap
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
variable (R : Type u) [CommRing R]

theorem reciprocalChartMap_preimage_ordinary_range :
    reciprocalChartMap R ⁻¹' Set.range (ordinaryChartMap R) =
      (PrimeSpectrum.basicOpen (zCoordinate R) : Set (PrimeSpectrum (ReciprocalRing R))) := by
  exact congrArg (fun U : (reciprocalScheme R).Opens => (U : Set (reciprocalScheme R)))
    (Order13IntegralHyperellipticMap.reciprocalChartMap_preimage_ordinaryChartMap_opensRange_eq_basicOpen R)

end MazurTransfer.Order13ActualTwoChartRangeOverlap
#print axioms MazurTransfer.Order13ActualTwoChartRangeOverlap.reciprocalChartMap_preimage_ordinary_range

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact positive infinity section complement as an actual
open of the retained two-chart curve over every commutative base ring.
Named downstream consumer: gluing Spec B onto the chosen single-section
complement for FiniteMapData. No affine identification is assumed here.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13ActualPositiveInfinityComplement
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTorsion.XOneThirteenAffineCurve
open Order13SingleSectionReciprocalPatch
open Order13PositiveInfinityReciprocalImage
variable (R : Type u) [CommRing R]

def reciprocalPatchInclusion : Spec (.of (PatchRing R)) ⟶ reciprocalScheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing R) (PatchRing R)))
instance reciprocalPatchInclusion_isOpenImmersion : IsOpenImmersion (reciprocalPatchInclusion R) :=
  IsOpenImmersion.of_isLocalization (d R * dPrime R)

def reciprocalPatchChartMap : Spec (.of (PatchRing R)) ⟶ curveScheme R :=
  reciprocalPatchInclusion R ≫ reciprocalChartMap R
instance reciprocalPatchChartMap_isOpenImmersion : IsOpenImmersion (reciprocalPatchChartMap R) :=
  IsOpenImmersion.comp (reciprocalPatchInclusion R) (reciprocalChartMap R)

def sectionComplementOpen : (curveScheme R).Opens :=
  (ordinaryChartMap R).opensRange ⊔ (reciprocalPatchChartMap R).opensRange

theorem reciprocalPatchInclusion_range : Set.range (reciprocalPatchInclusion R) =
    (PrimeSpectrum.basicOpen (d R * dPrime R) : Set (PrimeSpectrum (ReciprocalRing R))) := by
  exact PrimeSpectrum.localization_away_comap_range (PatchRing R) (d R * dPrime R)

theorem reciprocalPatchChartMap_range : Set.range (reciprocalPatchChartMap R) =
    reciprocalChartMap R '' (PrimeSpectrum.basicOpen (d R * dPrime R) : Set (PrimeSpectrum (ReciprocalRing R))) := by
  change Set.range (reciprocalChartMap R ∘ reciprocalPatchInclusion R) = _
  rw [Set.range_comp,reciprocalPatchInclusion_range]

theorem reciprocal_preimage_section_image : reciprocalChartMap R ⁻¹'
    Set.range (Order13IntegralSections.infinityMorphism R 1 (by simp)) =
      Set.range (evaluationSchemeMap R) := by
  change reciprocalChartMap R ⁻¹' Set.range (reciprocalChartMap R ∘ evaluationSchemeMap R) = _
  rw [Set.range_comp]
  exact Set.preimage_image_eq _ (reciprocalChartMap R).isOpenEmbedding.injective

theorem reciprocal_preimage_complement_open :
    reciprocalChartMap R ⁻¹' (sectionComplementOpen R : Set (curveScheme R)) =
      (Set.range (evaluationSchemeMap R))ᶜ := by
  change reciprocalChartMap R ⁻¹'
    (Set.range (ordinaryChartMap R) ∪ Set.range (reciprocalPatchChartMap R)) = _
  rw [Set.preimage_union,Order13ActualTwoChartRangeOverlap.reciprocalChartMap_preimage_ordinary_range,
    reciprocalPatchChartMap_range]
  have hi : (reciprocalChartMap R : PrimeSpectrum (ReciprocalRing R) → curveScheme R) ⁻¹'
      (reciprocalChartMap R '' (PrimeSpectrum.basicOpen (d R * dPrime R) : Set (PrimeSpectrum (ReciprocalRing R)))) =
        (PrimeSpectrum.basicOpen (d R * dPrime R) : Set (PrimeSpectrum (ReciprocalRing R))) :=
    Set.preimage_image_eq _ (reciprocalChartMap R).isOpenEmbedding.injective
  exact (congrArg (fun s : Set (PrimeSpectrum (ReciprocalRing R)) =>
    (PrimeSpectrum.basicOpen (zCoordinate R) : Set (PrimeSpectrum (ReciprocalRing R))) ∪ s) hi).trans
      (evaluationSchemeMap_range_complement R).symm

theorem ordinary_chart_disjoint_section_image (a : PrimeSpectrum (CoordinateRing R)) :
    ordinaryChartMap R a ∉ Set.range (Order13IntegralSections.infinityMorphism R 1 (by simp)) := by
  intro h
  change ordinaryChartMap R a ∈ Set.range (reciprocalChartMap R ∘ evaluationSchemeMap R) at h
  rw [Set.range_comp] at h
  obtain ⟨p,hp,heq⟩ := h
  have ho : p ∈ reciprocalChartMap R ⁻¹' Set.range (ordinaryChartMap R) := by
    exact ⟨a,heq.symm⟩
  rw [Order13ActualTwoChartRangeOverlap.reciprocalChartMap_preimage_ordinary_range] at ho
  have hz := (mem_evaluationSchemeMap_range R p).mp hp
  exact ho hz.1

theorem ordinary_chart_mem_complement_open (a : PrimeSpectrum (CoordinateRing R)) :
    ordinaryChartMap R a ∈ sectionComplementOpen R := by
  change ordinaryChartMap R a ∈ Set.range (ordinaryChartMap R) ∪ Set.range (reciprocalPatchChartMap R)
  exact Or.inl ⟨a,rfl⟩

theorem sectionComplementOpen_eq_section_image_complement :
    (sectionComplementOpen R : Set (curveScheme R)) =
      (Set.range (Order13IntegralSections.infinityMorphism R 1 (by simp)))ᶜ := by
  ext q
  obtain ⟨i,p,rfl⟩ := (glueData R).openCover.exists_eq q
  cases i with
  | ordinary =>
    exact iff_of_true (ordinary_chart_mem_complement_open R p) (ordinary_chart_disjoint_section_image R p)
  | reciprocal =>
    have hu := Set.ext_iff.mp (reciprocal_preimage_complement_open R) p
    have hs := Set.ext_iff.mp (reciprocal_preimage_section_image R) p
    exact hu.trans (not_congr hs).symm


end MazurTransfer.Order13ActualPositiveInfinityComplement

end
end

theorem solution.{u}
    (R : Type u) [CommRing R] :
    let ε : ReciprocalRing R →+* R :=
      AdjoinRoot.lift (Polynomial.evalRingHom (0 : R)) (1 : R)
        (by simp [reciprocalEquation, reciprocalPolynomial, eval₂_pow, eval₂_C])
    let s : Spec (.of R) ⟶ curveScheme R :=
      Spec.map (CommRingCat.ofHom ε) ≫ reciprocalChartMap R
    let δ : ReciprocalRing R :=
      (wCoordinate R - 1 - zCoordinate R - zCoordinate R ^ 3) *
        (wCoordinate R - 1 - zCoordinate R + zCoordinate R ^ 3)
    let j : Spec (.of (Localization.Away δ)) ⟶ curveScheme R :=
      Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing R) (Localization.Away δ))) ≫
        reciprocalChartMap R
    s ≫ curveToBase R = 𝟙 _ ∧
      IsClosedImmersion (Spec.map (CommRingCat.ofHom ε)) ∧
      IsOpenImmersion j ∧
      Set.range (ordinaryChartMap R) ∪ Set.range j = (Set.range s)ᶜ := by
  dsimp only
  refine ⟨MazurTransfer.Order13IntegralSections.infinityMorphism_curveToBase R 1 (by simp),
    MazurTransfer.Order13PositiveInfinityReciprocalImage.evaluationSchemeMap_isClosedImmersion R,
    MazurTransfer.Order13ActualPositiveInfinityComplement.reciprocalPatchChartMap_isOpenImmersion R,
    ?_⟩
  exact MazurTransfer.Order13ActualPositiveInfinityComplement.sectionComplementOpen_eq_section_image_complement R

#print axioms solution
