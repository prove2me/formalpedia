-- Prove2me | solution 1 for OAI.CirculantHadamard.LocalComparison.projected_factor_divisible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:46:07.979781+00:00
-- url     : https://prove2.me/submissions/dd43d73b-2bd2-4f86-94f5-cdb67c07f486

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/CyclotomicFactorDivision.lean:L25-L61
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.LocalComparison.projected_factor_divisible. The node keeps its source
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
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjectionPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluationAt
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicProjection
import Theorems.Thm_OAI_CirculantHadamard_LocalDVR_dvd_or_dvd_of_mul_eq_pow_mul_unit

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclotomicRemainder ----
namespace OAI

universe uR uS

/-!
# Scalar divisibility and monic remainders

The canonical remainder map for a monic root extension is linear over the
coefficient ring. Consequently, divisibility by a scalar in the extension is
equivalent to divisibility of every coefficient of the monic remainder.

The actual polynomial quotient `AdjoinRoot f` is such an extension;
no additional representation hypothesis is required.
-/

noncomputable section

namespace CirculantHadamard.CyclotomicRemainder

open Polynomial

variable {R : Type uR} {S : Type uS} [CommRing R] [Ring S] [Algebra R S] {f : R[X]}

/-- Scalar divisibility in a monic root extension gives a constant-polynomial
factor of the canonical remainder. -/
theorem C_dvd_modByMonic_of_dvd_map (h : IsAdjoinRootMonic S f)
    (a : R) (F : R[X]) (hdiv : algebraMap R S a ∣ h.map F) :
    C a ∣ F %ₘ f := by
  obtain ⟨x, hx⟩ := hdiv
  refine ⟨h.modByMonicHom x, ?_⟩
  calc
    F %ₘ f = h.modByMonicHom (h.map F) := (h.modByMonicHom_map F).symm
    _ = h.modByMonicHom (a • x) := by rw [hx, Algebra.smul_def]
    _ = a • h.modByMonicHom x := h.modByMonicHom.map_smul a x
    _ = C a * h.modByMonicHom x := Polynomial.smul_eq_C_mul a

/-- A constant factor of the canonical remainder gives scalar divisibility
after passing to the monic root extension. -/
theorem dvd_map_of_C_dvd_modByMonic (h : IsAdjoinRootMonic S f)
    (a : R) (F : R[X]) (hdiv : C a ∣ F %ₘ f) :
    algebraMap R S a ∣ h.map F := by
  obtain ⟨G, hG⟩ := hdiv
  refine ⟨h.map G, ?_⟩
  calc
    h.map F = h.map (F %ₘ f) := (h.map_modByMonic F).symm
    _ = h.map (C a * G) := congrArg h.map hG
    _ = algebraMap R S a * h.map G := by rw [map_mul, ← h.algebraMap_apply]

/-- Exact divisibility equivalence for a monic root extension. -/
theorem map_dvd_iff_C_dvd_modByMonic (h : IsAdjoinRootMonic S f)
    (a : R) (F : R[X]) :
    algebraMap R S a ∣ h.map F ↔ C a ∣ F %ₘ f :=
  ⟨C_dvd_modByMonic_of_dvd_map h a F, dvd_map_of_C_dvd_modByMonic h a F⟩

/-- The actual quotient by a monic polynomial satisfies the constant-factor
criterion, using its concrete `IsAdjoinRootMonic` constructor. -/
theorem adjoinRoot_dvd_iff_C_dvd_modByMonic (f : R[X]) (hf : f.Monic)
    (a : R) (F : R[X]) :
    algebraMap R (AdjoinRoot f) a ∣ AdjoinRoot.mk f F ↔ C a ∣ F %ₘ f := by
  simpa only [AdjoinRoot.isAdjoinRootMonic_toAdjoinRoot,
    AdjoinRoot.isAdjoinRoot_map_eq_mkₐ, AdjoinRoot.coe_mkₐ] using
    map_dvd_iff_C_dvd_modByMonic (AdjoinRoot.isAdjoinRootMonic f hf) a F

/-- The concrete monic quotient has scalar divisibility exactly when all
coefficients of the monic remainder have that scalar factor. -/
theorem adjoinRoot_dvd_iff_dvd_coeff_modByMonic (f : R[X]) (hf : f.Monic)
    (a : R) (F : R[X]) :
    algebraMap R (AdjoinRoot f) a ∣ AdjoinRoot.mk f F ↔
      ∀ i, a ∣ (F %ₘ f).coeff i :=
  (adjoinRoot_dvd_iff_C_dvd_modByMonic f hf a F).trans
    (C_dvd_iff_dvd_coeff a (F %ₘ f))

/-- Scalar divisibility in a monic quotient implies coefficientwise
divisibility of the remainder. -/
theorem adjoinRoot_dvd_coeff_modByMonic (f : R[X]) (hf : f.Monic)
    (a : R) (F : R[X])
    (hdiv : algebraMap R (AdjoinRoot f) a ∣ AdjoinRoot.mk f F) (i : ℕ) :
    a ∣ (F %ₘ f).coeff i :=
  (adjoinRoot_dvd_iff_dvd_coeff_modByMonic f hf a F).mp hdiv i

end CirculantHadamard.CyclotomicRemainder

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclicProjectionPolynomial ----
namespace OAI

universe uR

/-! Polynomial evaluation commutes with the concrete cyclic quotient map. -/

noncomputable section

namespace CirculantHadamard

open CyclicRing

variable (R : Type uR) [CommRing R] {m n : ℕ}

/-- Polynomial evaluation at the generator commutes with the cyclic quotient. -/
theorem cyclicProjection_aeval (h : m ∣ n) (F : Polynomial R) :
    cyclicProjection R h (Polynomial.aeval (CyclicPolynomial.generator R n) F) =
      Polynomial.aeval (CyclicPolynomial.generator R m) F := by
  change cyclicProjectionAlgHom R h
    (Polynomial.aeval (CyclicPolynomial.generator R n) F) = _
  have hgen : cyclicProjectionAlgHom R h (CyclicPolynomial.generator R n) =
      CyclicPolynomial.generator R m := cyclicProjection_generator (R := R) h
  rw [← Polynomial.aeval_algHom_apply, hgen]

end CirculantHadamard

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclotomicProjection ----
namespace OAI

universe uR uS

/-!
# Integral division after projection to a smaller cyclic group

At an element of order dividing `p ^ e`, the prime-power cyclotomic polynomial
`cyclotomic (p ^ (e + 1)) R` evaluates to the scalar `p`. Consequently, if all
coefficients of a polynomial's monic remainder are divisible by `p`, its image
in the group algebra of `ZMod (p ^ e)` is divisible by the same scalar.

All divisions are witnessed inside the coefficient ring or group algebra.
No domain instance or cancellation assumption on a finite group algebra is used.
-/

noncomputable section

namespace CirculantHadamard

open Polynomial

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]

/-- Every actual cyclic group-ring element has a polynomial representative. -/
theorem exists_cyclic_polynomial (n : ℕ) [NeZero n]
    (F : AddMonoidAlgebra R (ZMod n)) :
    ∃ P : R[X], aeval (CyclicPolynomial.generator R n) P = F := by
  obtain ⟨P, hP⟩ := AdjoinRoot.mk_surjective (CyclicPolynomial.cyclicEquiv R n F)
  refine ⟨P, ?_⟩
  apply (CyclicPolynomial.cyclicEquiv R n).injective
  rw [CyclicPolynomial.cyclicEquiv_aeval, hP]

/-- A prime-power cyclotomic polynomial becomes `p` at every element whose
`p ^ e`th power is one. -/
theorem aeval_cyclotomic_prime_pow_of_pow_eq_one {p e : ℕ} (hp : p.Prime)
    (x : S) (hx : x ^ (p ^ e) = 1) :
    aeval x (cyclotomic (p ^ (e + 1)) R) = (p : S) := by
  rw [cyclotomic_prime_pow_eq_geom_sum hp]
  simp [hx]

/-- Evaluating a monic division identity preserves integral divisibility if
both the divisor's evaluation and the remainder have the stated scalar factor. -/
theorem aeval_divisible_of_modByMonic_coeff (x : S) (F Q : R[X]) (a : R)
    (_hQ : Q.Monic) (hQx : aeval x Q = algebraMap R S a)
    (hcoeff : ∀ i, a ∣ (F %ₘ Q).coeff i) :
    ∃ G : S, aeval x F = algebraMap R S a * G := by
  obtain ⟨T, hT⟩ := (C_dvd_iff_dvd_coeff a (F %ₘ Q)).2 hcoeff
  refine ⟨aeval x T + aeval x (F /ₘ Q), ?_⟩
  calc
    aeval x F = aeval x (F %ₘ Q) + aeval x Q * aeval x (F /ₘ Q) := by
      rw [← map_mul, ← map_add, modByMonic_add_div F Q]
    _ = algebraMap R S a * (aeval x T + aeval x (F /ₘ Q)) := by
      rw [hT, map_mul, aeval_C, hQx, mul_add]

/-- Integral divisibility at a `p ^ e`th root follows from coefficientwise
divisibility of the remainder modulo the next cyclotomic polynomial. -/
theorem aeval_divisible_of_cyclotomic_remainder_coeff {p e : ℕ} (hp : p.Prime)
    (x : S) (hx : x ^ (p ^ e) = 1) (F : R[X])
    (hcoeff : ∀ i, (p : R) ∣ (F %ₘ cyclotomic (p ^ (e + 1)) R).coeff i) :
    ∃ G : S, aeval x F = (p : S) * G := by
  have hQx : aeval x (cyclotomic (p ^ (e + 1)) R) =
      algebraMap R S (p : R) := by
    simpa only [map_natCast] using aeval_cyclotomic_prime_pow_of_pow_eq_one hp x hx
  simpa only [map_natCast] using aeval_divisible_of_modByMonic_coeff x F
    (cyclotomic (p ^ (e + 1)) R) (p : R) (cyclotomic.monic _ _) hQx hcoeff

/-- The concrete `p`-division step in the cyclic group algebra: project from
order `p ^ (e + 1)` to order `p ^ e`, then divide integrally by `p`. -/
theorem cyclicProjection_divisible_of_remainder_coeff {p e : ℕ} (hp : p.Prime)
    (F : R[X])
    (hcoeff : ∀ i, (p : R) ∣ (F %ₘ cyclotomic (p ^ (e + 1)) R).coeff i) :
    ∃ G : AddMonoidAlgebra R (ZMod (p ^ e)),
      cyclicProjection R (pow_dvd_pow p (Nat.le_succ e))
          (aeval (CyclicPolynomial.generator R (p ^ (e + 1))) F) =
        (p : AddMonoidAlgebra R (ZMod (p ^ e))) * G := by
  rw [cyclicProjection_aeval]
  exact aeval_divisible_of_cyclotomic_remainder_coeff hp
    (CyclicPolynomial.generator R (p ^ e)) (CyclicPolynomial.generator_pow R (p ^ e))
    F hcoeff

/-- Divisibility at the actual primitive-root quotient forces integral
divisibility after projecting the actual cyclic group-ring element.

The concrete monic quotient's linear remainder map supplies coefficientwise
divisibility of the remainder. -/
theorem cyclicProjection_divisible_of_cyclotomicEvaluation {p e : ℕ}
    [NeZero p] (hp : p.Prime) (F : AddMonoidAlgebra R (ZMod (p ^ (e + 1))))
    (hdiv : (p : AdjoinRoot (cyclotomic (p ^ (e + 1)) R)) ∣
      cyclicCyclotomicEvaluation R (p ^ (e + 1)) F) :
    ∃ G : AddMonoidAlgebra R (ZMod (p ^ e)),
      cyclicProjection R (pow_dvd_pow p (Nat.le_succ e)) F =
        (p : AddMonoidAlgebra R (ZMod (p ^ e))) * G := by
  obtain ⟨P, rfl⟩ := exists_cyclic_polynomial (p ^ (e + 1)) F
  rw [cyclicCyclotomicEvaluation_aeval] at hdiv
  apply cyclicProjection_divisible_of_remainder_coeff hp P
  intro i
  exact CyclotomicRemainder.adjoinRoot_dvd_coeff_modByMonic
    (cyclotomic (p ^ (e + 1)) R) (cyclotomic.monic _ _) (p : R) P
    (by simpa only [map_natCast] using hdiv) i

end CirculantHadamard

end

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclotomicFactorDivision ----
namespace OAI

universe uA

/-!
# A projected factor is integrally divisible by the residue prime

The primitive-character values live in the actual cyclotomic quotient. Their
product is evaluated from the actual group-ring product. The DVR inequality
chooses a factor, and the monic remainder theorem transfers its divisibility
to the smaller cyclic group ring.
-/

noncomputable section

namespace CirculantHadamard.LocalComparison

open CyclicRing Polynomial IsDiscreteValuationRing

variable {A : Type uA} [CommRing A]

/-- The ramified DVR and its value of `p` imply the concrete choice of a
divisible projected factor. These are local-ring properties, independent of
the input factors. The scalar and group exponents are both `e + 2`. -/
theorem projected_factor_divisible {p e D : ℕ} [NeZero p] (hp : p.Prime)
    [IsDomain (AdjoinRoot (cyclotomic (p ^ (e + 2)) A))]
    [IsDiscreteValuationRing (AdjoinRoot (cyclotomic (p ^ (e + 2)) A))]
    (hpS : (p : AdjoinRoot (cyclotomic (p ^ (e + 2)) A)) ≠ 0)
    (hD : 0 < D)
    (hpval : addVal (AdjoinRoot (cyclotomic (p ^ (e + 2)) A))
      (p : AdjoinRoot (cyclotomic (p ^ (e + 2)) A)) = (D : ℕ∞))
    (b : Aˣ) (F K : Elem A (p ^ (e + 2)))
    (hFK : F * K = scalar (p ^ (e + 2)) ((p : A) ^ (e + 2) * (b : A))) :
    (∃ F', cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F =
      scalar (p ^ (e + 1)) (p : A) * F') ∨
    (∃ K', cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) K =
      scalar (p ^ (e + 1)) (p : A) * K') := by
  let v := cyclicCyclotomicEvaluation A (p ^ (e + 2))
  have hscalar : ∀ a : A, v (scalar (p ^ (e + 2)) a) =
      algebraMap A (AdjoinRoot (cyclotomic (p ^ (e + 2)) A)) a := by
    intro a
    exact v.commutes a
  have hv : v F * v K =
      (p : AdjoinRoot (cyclotomic (p ^ (e + 2)) A)) ^ (e + 2) *
        algebraMap A (AdjoinRoot (cyclotomic (p ^ (e + 2)) A)) (b : A) := by
    have h := congrArg v hFK
    simpa only [map_mul, hscalar, map_pow, map_natCast] using h
  have hb : IsUnit (algebraMap A (AdjoinRoot (cyclotomic (p ^ (e + 2)) A))
      (b : A)) := b.isUnit.map _
  have hchoose := LocalDVR.dvd_or_dvd_of_mul_eq_pow_mul_unit
    hpS hD hpval (Nat.le_add_left 2 e) hb hv
  rcases hchoose with hF | hK
  · left
    simpa only [scalar_natCast] using
      cyclicProjection_divisible_of_cyclotomicEvaluation (e := e + 1) hp F hF
  · right
    simpa only [scalar_natCast] using
      cyclicProjection_divisible_of_cyclotomicEvaluation (e := e + 1) hp K hK

end CirculantHadamard.LocalComparison

end

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard OAI.CirculantHadamard.LocalComparison
open CyclicRing Polynomial IsDiscreteValuationRing


theorem solution.{uA} : type_of% @_root_.OAI.CirculantHadamard.LocalComparison.projected_factor_divisible.{uA} := @_root_.OAI.CirculantHadamard.LocalComparison.projected_factor_divisible.{uA}
