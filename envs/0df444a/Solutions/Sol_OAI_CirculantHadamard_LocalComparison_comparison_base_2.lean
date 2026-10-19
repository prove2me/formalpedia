-- Prove2me | solution 2 for OAI.CirculantHadamard.LocalComparison.comparison_base
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:39:51.528423+00:00
-- url     : https://prove2.me/submissions/7569e5c7-8956-4b94-8f8a-aefd30e8b264

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/LocalComparisonInduction.lean:L56-L88
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.LocalComparison.comparison_base. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeComponents
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeCharacterEvaluations
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalizationMaps
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalization
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingProducts
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryProductTransport
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_FirstOrderResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalFamily
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_ResidueOneAssociation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicLocalBase
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicAwayLocal
import Theorems.Thm_OAI_CirculantHadamard_LocalComparison_isUnit_or_isUnit_of_mul_prime_unit

-- ---- from OAI.LinearAlgebra.CirculantHadamard.ResidueOneAssociation ----
namespace OAI

universe uS uk

/-!
# Association by a unit with residue one

This algebraic relation expresses the local comparison conclusion without
introducing division in the coefficient ring. The scalar-cancellation lemmas
require regularity explicitly; they do not give group rings a domain instance.
For a local ring, the residue map is the quotient by its maximal ideal.
-/

namespace CirculantHadamard.LocalComparison

variable {S : Type uS} {k : Type uk} [CommRing S] [CommRing k]

namespace ResidueOneAssociated

variable {residue : S →+* k} {x y z c x' y' : S}

/-- With equal nonzero products, a comparison for one factor gives the inverse
unit as comparison for the other factor. Only regularity of `y` is needed. -/
theorem product_complement_of_regular (h : ResidueOneAssociated residue x y)
    (hprod : x * x' = y * y') (hy : IsLeftRegular y) :
    ResidueOneAssociated residue x' y' := by
  obtain ⟨u, hxy, hu⟩ := h
  have hcancel : (u : S) * x' = y' := by
    apply hy
    calc
      y * ((u : S) * x') = ((u : S) * y) * x' := by ac_rfl
      _ = x * x' := by rw [← hxy]
      _ = y * y' := hprod
  refine ⟨u⁻¹, ?_, residue_inv_eq_one residue hu⟩
  rw [← hcancel, Units.inv_mul_cancel_left]

/-- The two-factor step used in the character-comparison base case. -/
theorem product_complement [IsDomain S] (h : ResidueOneAssociated residue x y)
    (hprod : x * x' = y * y') (hne : y * y' ≠ 0) :
    ResidueOneAssociated residue x' y' := by
  have hy : y ≠ 0 := fun hz => hne (by rw [hz, zero_mul])
  exact h.product_complement_of_regular hprod (fun _ _ h => mul_left_cancel₀ hy h)

/-- Two units with the same residue differ by a unit with residue one. -/
theorem of_isUnit_of_residue_eq (residue : S →+* k)
    (hx : IsUnit x) (hy : IsUnit y) (hres : residue x = residue y) :
    ResidueOneAssociated residue x y := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  refine ⟨u * v⁻¹, ?_, ?_⟩
  · simp only [Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  · rw [Units.val_mul, map_mul, hres, ← map_mul, Units.mul_inv, map_one]

end ResidueOneAssociated

section ActualResidueField

variable [IsLocalRing S] {x y : S}

/-- Equality to the residue of a unit forces an element of a local ring to be
a unit. The residue map is the actual quotient by the maximal ideal. -/
theorem isUnit_of_residue_eq (hy : IsUnit y)
    (hres : IsLocalRing.residue S x = IsLocalRing.residue S y) : IsUnit x := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit x).mp
  rw [hres]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit y).mpr hy

/-- Concrete local-ring base case: an augmentation unit and agreement in the
residue field suffice to construct the comparison unit. -/
theorem residueOneAssociated_of_isUnit_residue_eq (hy : IsUnit y)
    (hres : IsLocalRing.residue S x = IsLocalRing.residue S y) :
    ResidueOneAssociated (IsLocalRing.residue S) x y :=
  ResidueOneAssociated.of_isUnit_of_residue_eq (IsLocalRing.residue S)
    (isUnit_of_residue_eq hy hres) hy hres

end ActualResidueField

end CirculantHadamard.LocalComparison

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.LocalComparisonInduction ----
namespace OAI

universe uA uS

noncomputable section

namespace CirculantHadamard.LocalComparison

open CyclicRing

variable {A : Type uA} {S : Type uS} [CommRing A] [IsDomain A]
  [CommRing S] [domainS : IsDomain S] [IsLocalRing S]

/-- The exponent-one base case, using the actual residue field of `S`. -/
theorem comparison_base (n p : ℕ) (φ : A →+* S) (hp : Prime (p : A))
    (hpS : φ (p : A) ≠ 0)
    (v : Elem A n →+* S)
    (vscalar : ∀ a : A, v (scalar n a) = φ a)
    (vres : ∀ F : Elem A n,
      IsLocalRing.residue S (v F) =
        IsLocalRing.residue S (φ (augmentation n F)))
    (b : Aˣ) (F K : Elem A n)
    (hFK : F * K = scalar n ((p : A) * (b : A))) :
    ResidueOneAssociated (IsLocalRing.residue S) (v F) (φ (augmentation n F)) ∧
      ResidueOneAssociated (IsLocalRing.residue S) (v K) (φ (augmentation n K)) := by
  have haug : augmentation n F * augmentation n K = (p : A) * (b : A) := by
    simpa only [map_mul, augmentation_scalar] using congrArg (augmentation n) hFK
  have hv : v F * v K = φ ((p : A) * (b : A)) := by
    simpa only [map_mul, vscalar] using congrArg v hFK
  have hprod : v F * v K = φ (augmentation n F) * φ (augmentation n K) := by
    calc
      v F * v K = φ ((p : A) * (b : A)) := hv
      _ = φ (augmentation n F * augmentation n K) := congrArg φ haug.symm
      _ = φ (augmentation n F) * φ (augmentation n K) := φ.map_mul _ _
  have hne : φ (augmentation n F) * φ (augmentation n K) ≠ 0 := by
    rw [← map_mul, haug, map_mul]
    exact mul_ne_zero hpS (b.isUnit.map φ).ne_zero
  rcases isUnit_or_isUnit_of_mul_prime_unit hp b haug with hF | hK
  · have h := residueOneAssociated_of_isUnit_residue_eq (hF.map φ) (vres F)
    exact ⟨h, h.product_complement hprod hne⟩
  · have h := residueOneAssociated_of_isUnit_residue_eq (hK.map φ) (vres K)
    have hprod' : v K * v F = φ (augmentation n K) * φ (augmentation n F) := by
      simpa only [mul_comm] using hprod
    have hne' : φ (augmentation n K) * φ (augmentation n F) ≠ 0 := by
      simpa only [mul_comm] using hne
    exact ⟨h.product_complement hprod' hne', h⟩

end CirculantHadamard.LocalComparison

end

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard OAI.CirculantHadamard.LocalComparison
open CyclicRing


theorem solution.{uA,uS} : type_of% @_root_.OAI.CirculantHadamard.LocalComparison.comparison_base.{uA,uS} := @_root_.OAI.CirculantHadamard.LocalComparison.comparison_base.{uA,uS}
