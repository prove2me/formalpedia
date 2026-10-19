-- Prove2me | solution 2 for OAI.CirculantHadamard.LocalComparison.comparison_step_left
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:41:40.595807+00:00
-- url     : https://prove2.me/submissions/9ce9be15-3e56-4d6e-b1a0-4d7ca9902ca3

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/LocalComparisonInduction.lean:L90-L130
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.LocalComparison.comparison_step_left. The node keeps its source
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

theorem mul_left (h : ResidueOneAssociated residue x y) (c : S) :
    ResidueOneAssociated residue (c * x) (c * y) := by
  obtain ⟨u, hxy, hu⟩ := h
  refine ⟨u, ?_, hu⟩
  rw [hxy]
  ac_rfl

end ResidueOneAssociated

section ActualResidueField

variable [IsLocalRing S] {x y : S}

end ActualResidueField

end CirculantHadamard.LocalComparison

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclicScalarDivision ----
namespace OAI

universe uR uG uH

/-!
# Division by regular coefficient scalars in an additive monoid algebra

A finite group algebra usually has zero divisors. A nonzero scalar from a
domain nevertheless acts injectively, as is seen separately at each coefficient.
This is the cancellation needed when the projected norm equation is divided by
one power of the residue characteristic.
-/

noncomputable section

namespace CirculantHadamard

section DivisionExists

variable {R : Type uR} {G : Type uG} [CommRing R] [AddMonoid G] [finiteG : Finite G]

end DivisionExists

section Cancellation

variable {R : Type uR} {G : Type uG} [CommRing R] [IsDomain R] [AddMonoid G]

/-- A scalar is cancellable because its action at each coefficient is
injective. No domain structure is asserted for the group algebra. -/
theorem scalar_mul_left_cancel (p : R) (hp : p ≠ 0)
    {F K : AddMonoidAlgebra R G}
    (h : AddMonoidAlgebra.single (0 : G) p * F =
      AddMonoidAlgebra.single (0 : G) p * K) : F = K := by
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro g
  apply mul_left_cancel₀ hp
  simpa only [AddMonoidAlgebra.coeff_single_zero_mul] using
    congrArg (fun H : AddMonoidAlgebra R G => H.coeff g) h

/-- Cancelling one regular scalar lowers the exponent of the norm equation
by exactly one. This is valid although the group algebra has zero divisors. -/
theorem scalar_mul_norm_division (p : R) (hp : p ≠ 0) (e : ℕ) (b : R)
    (F K : AddMonoidAlgebra R G)
    (h : (AddMonoidAlgebra.single (0 : G) p * F) * K =
      AddMonoidAlgebra.single (0 : G) (p ^ (e + 1) * b)) :
    F * K = AddMonoidAlgebra.single (0 : G) (p ^ e * b) := by
  apply scalar_mul_left_cancel p hp
  calc
    AddMonoidAlgebra.single (0 : G) p * (F * K) =
        (AddMonoidAlgebra.single (0 : G) p * F) * K := (mul_assoc _ _ _).symm
    _ = AddMonoidAlgebra.single (0 : G) (p ^ (e + 1) * b) := h
    _ = AddMonoidAlgebra.single (0 : G) p *
        AddMonoidAlgebra.single (0 : G) (p ^ e * b) := by
      rw [AddMonoidAlgebra.single_mul_single, zero_add]
      rw [pow_succ', mul_assoc]

end Cancellation

section Quotient

variable {R : Type uR} {G : Type uG} {H : Type uH} [CommRing R] [IsDomain R]
  [AddMonoid G] [AddMonoid H]

/-- Project the norm equation along a genuine ring homomorphism and then
divide the chosen projected factor by one coefficient scalar. -/
theorem quotient_scalar_norm_division
    (q : AddMonoidAlgebra R G →+* AddMonoidAlgebra R H)
    (hscalar : ∀ r : R, q (AddMonoidAlgebra.single (0 : G) r) =
      AddMonoidAlgebra.single (0 : H) r)
    (p : R) (hp : p ≠ 0) (e : ℕ) (b : R)
    (F K : AddMonoidAlgebra R G) (F' : AddMonoidAlgebra R H)
    (hFK : F * K = AddMonoidAlgebra.single (0 : G) (p ^ (e + 1) * b))
    (hF : q F = AddMonoidAlgebra.single (0 : H) p * F') :
    F' * q K = AddMonoidAlgebra.single (0 : H) (p ^ e * b) := by
  apply scalar_mul_norm_division p hp e b F' (q K)
  calc
    (AddMonoidAlgebra.single (0 : H) p * F') * q K = q F * q K := by rw [hF]
    _ = q (F * K) := (q.map_mul F K).symm
    _ = q (AddMonoidAlgebra.single (0 : G) (p ^ (e + 1) * b)) := congrArg q hFK
    _ = AddMonoidAlgebra.single (0 : H) (p ^ (e + 1) * b) := hscalar _

end Quotient

end CirculantHadamard

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.LocalComparisonInduction ----
namespace OAI

universe uA uS

noncomputable section

namespace CirculantHadamard.LocalComparison

open CyclicRing

variable {A : Type uA} {S : Type uS} [CommRing A] [IsDomain A]
  [CommRing S] [domainS : IsDomain S] [IsLocalRing S]

omit domainS in
/-- Induction step when the first projected factor is divisible by `p`.
The other factor is left intact. The two output associations are both
transported, so the next step may divide either factor. -/
theorem comparison_step_left [IsDomain S] (p e : ℕ) (φ : A →+* S)
    (hp : (p : A) ≠ 0)
    (v : Elem A (p ^ (e + 1)) →+* S)
    (v' : Elem A (p ^ (e + 2)) →+* S)
    (vscalar : ∀ a : A, v (scalar (p ^ (e + 1)) a) = φ a)
    (vq : ∀ F : Elem A (p ^ (e + 2)),
      v (cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F) = v' F)
    (b : Aˣ) (F K : Elem A (p ^ (e + 2)))
    (hFK : F * K = scalar (p ^ (e + 2)) ((p : A) ^ (e + 2) * (b : A)))
    (F' : Elem A (p ^ (e + 1)))
    (hF : cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F =
      scalar (p ^ (e + 1)) (p : A) * F')
    (ih : ∀ U V : Elem A (p ^ (e + 1)),
      U * V = scalar (p ^ (e + 1)) ((p : A) ^ (e + 1) * (b : A)) →
        ResidueOneAssociated (IsLocalRing.residue S) (v U)
          (φ (augmentation (p ^ (e + 1)) U)) ∧
        ResidueOneAssociated (IsLocalRing.residue S) (v V)
          (φ (augmentation (p ^ (e + 1)) V))) :
    ResidueOneAssociated (IsLocalRing.residue S) (v' F)
      (φ (augmentation (p ^ (e + 2)) F)) ∧
    ResidueOneAssociated (IsLocalRing.residue S) (v' K)
      (φ (augmentation (p ^ (e + 2)) K)) := by
  let q := cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1)))
  have hdiv : F' * q K = scalar (p ^ (e + 1)) ((p : A) ^ (e + 1) * (b : A)) :=
    quotient_scalar_norm_division q (fun a => cyclicProjection_single_zero _ a)
      (p : A) hp (e + 1) (b : A) F K F' hFK hF
  obtain ⟨hiF, hiK⟩ := ih F' (q K) hdiv
  have heval : v' F = φ (p : A) * v F' := by
    rw [← vq F, hF, map_mul, vscalar]
  have haug : augmentation (p ^ (e + 2)) F =
      (p : A) * augmentation (p ^ (e + 1)) F' := by
    rw [← augmentation_cyclicProjection (pow_dvd_pow p (Nat.le_succ (e + 1))) F,
      hF, map_mul, augmentation_scalar]
  constructor
  · rw [heval, haug, map_mul]
    exact hiF.mul_left (φ (p : A))
  · simpa only [q, vq, augmentation_cyclicProjection] using hiK

end CirculantHadamard.LocalComparison

end

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard OAI.CirculantHadamard.LocalComparison
open CyclicRing


theorem solution.{uA,uS} : type_of% @_root_.OAI.CirculantHadamard.LocalComparison.comparison_step_left.{uA,uS} := @_root_.OAI.CirculantHadamard.LocalComparison.comparison_step_left.{uA,uS}
