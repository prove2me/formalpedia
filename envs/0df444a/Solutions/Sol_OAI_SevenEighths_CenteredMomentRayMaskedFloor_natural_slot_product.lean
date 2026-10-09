-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentRayMaskedFloor.natural_slot_product
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:03:17.228624+00:00
-- url     : https://prove2.me/submissions/ec3b6e58-9f62-4b67-ade6-bc46c8aff6a3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B023
import Definitions.Def_OAIHecke78B024
import Theorems.Thm_OAI_SevenEighths_CenteredMomentPrimeHeight_ray_prime_all_height_large

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.RamifiedTracePhase
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical

namespace ActualEisensteinCubic

theorem finiteSquarefreeRow_sixth_power
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (a : O) :
    finiteSquarefreeRow P hgood S (a ^ 6) =
      if ∃ i ∈ S, a ∈ P i then 0 else 1 := by
  classical
  simp only [finiteSquarefreeRow]
  by_cases hex : ∃ i ∈ S, a ∈ P i
  · obtain ⟨i, hi, hai⟩ := hex
    rw [if_pos ⟨i, hi, hai⟩]
    apply Finset.prod_eq_zero hi
    rw [canonicalSextic_sixth_power_mask]
    simp [hai]
  · rw [if_neg hex]
    apply Finset.prod_eq_one
    intro i hi
    rw [canonicalSextic_sixth_power_mask]
    simp [show a ∉ P i by intro hai; exact hex ⟨i, hi, hai⟩]

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Arithmetic.SquarefreeDivisors
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical
namespace FirstPassCubeLabels
open ActualEisensteinCubic

section Rows
variable {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)

theorem row_pow (a : O) (m : ℕ) :
    finiteSquarefreeRow P hg S (a ^ m) = finiteSquarefreeRow P hg S a ^ m := by
  simp only [finiteSquarefreeRow, map_pow, Finset.prod_pow]

theorem row_sixth (a : O) :
    finiteSquarefreeRow P hg S a ^ 6 = rowCoprimeMask P S a := by
  rw [← row_pow, finiteSquarefreeRow_sixth_power]
  rfl

include hg

end Rows

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ConductorBounds
namespace OAI

namespace SevenEighths.FiniteConductor

open SevenEighths.FiniteFourier
open scoped Classical

noncomputable section

section QuotientBounds

variable {R : Type*} [CommRing R]

theorem quotient_inf_card_le_mul (I J : Ideal R) [Finite (R ⧸ I)] [Finite (R ⧸ J)] :
    Nat.card (R ⧸ I ⊓ J) ≤ Nat.card (R ⧸ I) * Nat.card (R ⧸ J) := by
  let f : R ⧸ I ⊓ J →+* (R ⧸ I) × (R ⧸ J) :=
    (Ideal.Quotient.factor inf_le_left).prod (Ideal.Quotient.factor inf_le_right)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact ⟨Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.fst hx),
      Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.snd hx)⟩
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hf

end QuotientBounds

variable {A : Type*} [CommRing A] [IsDedekindDomain A] [Infinite A]
  [Module.Free ℤ A] [Module.Finite ℤ A]

theorem absNorm_inf_le_mul (I J : Ideal A) [Finite (A ⧸ I)] [Finite (A ⧸ J)] :
    (I ⊓ J).absNorm ≤ I.absNorm * J.absNorm := by
  simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using
    quotient_inf_card_le_mul I J

end

end SevenEighths.FiniteConductor

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ConductorPresentation
namespace OAI

namespace SevenEighths

namespace FiniteConductor

variable {R : Type*} [CommRing R] [Finite R]

theorem FactorsThroughIdeal.bot (χ : MulChar R ℂ) : FactorsThroughIdeal χ ⊥ := by
  rw [factorsThroughIdeal_iff]
  intro u hu
  have hu1 : (u : R) = 1 := sub_eq_zero.mp hu
  rw [hu1, map_one]

end FiniteConductor

namespace ConductorPresentation

open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open scoped Classical

noncomputable section

variable {A : Type*} [CommRing A] [IsDedekindDomain A] [Infinite A]
  [Module.Free ℤ A] [Module.Finite ℤ A]

theorem exists_primitive_presentation (M : Ideal A) [Finite (A ⧸ M)]
    (χ : MulChar (A ⧸ M) ℂ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      M ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ M.absNorm ∧
      ∀ a : A, χ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 := by
  obtain ⟨K, φ, hMK, hbotK, hK, hprimitive, hnorm, hmask⟩ :=
    exists_primitive_presentation_above_quotient M χ ⊥ (FactorsThroughIdeal.bot χ)
  refine ⟨K, φ, hMK, hK, hprimitive, ?_, hmask⟩
  simpa only [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using hnorm

end

end ConductorPresentation

end SevenEighths

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.CompactEnergyFamilies
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open Filter MeasureTheory
open scoped BigOperators Classical Topology

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss (actualSextic)

theorem idealRowHom_product {ι : Type*} (p : ι → ActualEisensteinCubic.O)
    [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
    (S : Finset ι) (x : ActualEisensteinCubic.O) :
    idealRowHom x (Ideal.span {∏i∈S,p i}) =
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S x := by
  rw [FiniteGaussPhase.span_finset_prod,map_prod]
  simp only [finiteSquarefreeRow]
  apply Finset.prod_congr rfl
  intro i hi
  exact idealRowHom_prime x _ (hg i)

theorem rowTwist_product {ι : Type*} (p : ι → ActualEisensteinCubic.O)
    [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
    (S : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) :
    rowTwist Ψ m f z (∏i∈S,p i) =
      Ψ (∏i∈S,p i)*rowCoprimeMask (fun i=>Ideal.span {p i}) S m*
        finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S f^4*
        finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z := by
  change Ψ _ * idealRowHom _ (Ideal.span {∏i∈S,p i}) = _
  rw [idealRowHom_product p hg S,finiteSquarefreeRow_mul,finiteSquarefreeRow_mul,
    FirstPassCubeLabels.row_pow,FirstPassCubeLabels.row_pow,FirstPassCubeLabels.row_sixth]
  ring

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open SecondPassArithmetic hiding O

end CanonicalRowCompletion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ResidueCharacter
namespace OAI

namespace SevenEighths.ResidueCharacter

open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open SevenEighths.ConductorPresentation
open scoped Classical

noncomputable section

variable {A : Type*} [CommRing A]

theorem finite_quotient_inf (I J : Ideal A) [Finite (A ⧸ I)] [Finite (A ⧸ J)] :
    Finite (A ⧸ I ⊓ J) := by
  let f : A ⧸ I ⊓ J →+* (A ⧸ I) × (A ⧸ J) :=
    (Ideal.Quotient.factor inf_le_left).prod (Ideal.Quotient.factor inf_le_right)
  apply Finite.of_injective f
  apply (injective_iff_map_eq_zero f).mpr
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact ⟨Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.fst hx),
    Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.snd hx)⟩

end

end SevenEighths.ResidueCharacter

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.IdealCharacter
namespace OAI

namespace SevenEighths.IdealCharacter

open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open SevenEighths.ConductorPresentation
open Submodule.IsPrincipal
open scoped Classical

noncomputable section

variable {A : Type*} [CommRing A]

section Principal

variable [IsDomain A] [IsPrincipalIdealRing A]

theorem ofResidue_finite_deletion (M K : Ideal A)
    (χ : MulChar (A ⧸ M) ℂ) (φ : MulChar (A ⧸ K) ℂ)
    (hχ : UnitInvariant M χ) (hφ : UnitInvariant K φ)
    (hmask : ∀ a : A, χ (Ideal.Quotient.mk M a) =
      if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0)
    (I : Ideal A) :
    ofResidue M χ hχ I =
      ofResidue M 1 (one_unitInvariant M) I * ofResidue K φ hφ I := by
  rw [ofResidue_source_mask M K χ φ hχ hφ hmask, ofResidue_one]
  by_cases hI : I = ⊥
  · simp only [hI, ofResidue_bot, ite_true, ite_self, mul_zero]
  · simp only [hI, ite_false]
    split_ifs <;> simp only [one_mul, zero_mul]

section Primitive

variable [Infinite A] [Module.Free ℤ A] [Module.Finite ℤ A]

theorem exists_primitive_associate (M : Ideal A) [Finite (A ⧸ M)]
    (χ : MulChar (A ⧸ M) ℂ) (hχ : UnitInvariant M χ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ) (hφ : UnitInvariant K φ),
      M ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ M.absNorm ∧
      (∀ I : Ideal A, ofResidue M χ hχ I =
        if IsCoprime I M then ofResidue K φ hφ I else 0) ∧
      ∀ I : Ideal A, ofResidue M χ hχ I =
        ofResidue M 1 (one_unitInvariant M) I * ofResidue K φ hφ I := by
  obtain ⟨K, φ, hMK, hK, hprimitive, hnorm, hmask⟩ := exists_primitive_presentation M χ
  have hφ : UnitInvariant K φ := by
    intro u
    have h := hmask (u : A)
    simpa only [hχ u, u.isUnit.map (Ideal.Quotient.mk M), ite_true] using h.symm
  exact ⟨K, φ, hφ, hMK, hK, hprimitive, hnorm,
    ofResidue_source_mask M K χ φ hχ hφ hmask,
    ofResidue_finite_deletion M K χ φ hχ hφ hmask⟩

theorem exists_primitive_product_associate (M N : Ideal A)
    [Finite (A ⧸ M)] [Finite (A ⧸ N)]
    (χ : MulChar (A ⧸ M) ℂ) (ψ : MulChar (A ⧸ N) ℂ)
    (hχ : UnitInvariant M χ) (hψ : UnitInvariant N ψ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ) (hφ : UnitInvariant K φ),
      M ⊓ N ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧
      K.absNorm ≤ M.absNorm * N.absNorm ∧
      (∀ I : Ideal A, ofResidue M χ hχ I * ofResidue N ψ hψ I =
        if IsCoprime I (M ⊓ N) then ofResidue K φ hφ I else 0) ∧
      ∀ I : Ideal A, ofResidue M χ hχ I * ofResidue N ψ hψ I =
        ofResidue (M ⊓ N) 1 (one_unitInvariant (M ⊓ N)) I * ofResidue K φ hφ I := by
  let : Finite (A ⧸ M ⊓ N) := ResidueCharacter.finite_quotient_inf M N
  obtain ⟨K, φ, hφ, hMNK, hK, hprimitive, hnorm, hmask, hdelete⟩ :=
    exists_primitive_associate (M ⊓ N) (ResidueCharacter.product M N χ ψ)
      (ResidueCharacter.product_global_units M N χ ψ hχ hψ)
  refine ⟨K, φ, hφ, hMNK, hK, hprimitive, hnorm.trans (absNorm_inf_le_mul M N), ?_, ?_⟩
  · intro I
    exact (ofResidue_product M N χ ψ hχ hψ I).symm.trans (hmask I)
  · intro I
    exact (ofResidue_product M N χ ψ hχ hψ I).symm.trans (hdelete I)

end Primitive

end Principal

end

end SevenEighths.IdealCharacter

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Dyadic
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem norm_pos (I : NonzeroIdeal) : 0 < norm I := by
  unfold norm
  exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Operations
namespace OAI

noncomputable section
namespace SevenEighths.HeckeFamily

theorem elementCoeff_inverse (χ : Character) (z : O) :
    elementCoeff χ.inverse z = (elementCoeff χ z)⁻¹ := by
  exact MulChar.inv_apply_eq_inv' _ _

end SevenEighths.HeckeFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.IdealOperations
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeFamily

theorem exists_primitive_product_character (χ ψ : Character) :
    ∃ ρ : Character,
      χ.modulus ⊓ ψ.modulus ≤ ρ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ρ.residue ∧
      ρ.modulus.absNorm ≤ χ.modulus.absNorm * ψ.modulus.absNorm ∧
      ∀ I : Ideal O, idealCoeff χ I * idealCoeff ψ I =
        if IsCoprime I (χ.modulus ⊓ ψ.modulus) then idealCoeff ρ I else 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Finite (O ⧸ ψ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient ψ.modulus_ne_bot
  obtain ⟨M, φ, hφ, hM, hM₀, hprim, hnorm, hmask, _⟩ :=
    IdealCharacter.exists_primitive_product_associate χ.modulus ψ.modulus
      χ.residue ψ.residue χ.unit_trivial ψ.unit_trivial
  exact ⟨Character.ofResidue M hM₀ φ hφ, hM, hprim, hnorm, hmask⟩

end SevenEighths.HeckeFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeScale
namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace SevenEighths.HeckePrimeScale
open HeckeFamily

theorem product_modulus_bound (χ ψ : Character) :
    (χ.product ψ).modulus.absNorm≤χ.modulus.absNorm*ψ.modulus.absNorm := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Finite (O ⧸ ψ.modulus) := Ring.HasFiniteQuotients.finiteQuotient ψ.modulus_ne_bot
  exact FiniteConductor.absNorm_inf_le_mul χ.modulus ψ.modulus

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.HeckePrimeScale

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Twist
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentTwist
open ActualEisensteinCubic EisensteinSchwartzPoisson
open CenteredMomentLattice

lemma norm_real_imaginary_power (X t : ℝ) (hX : 0 < X) :
    ‖(X : ℂ) ^ (Complex.I * t)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
  simp

end SevenEighths.CenteredMomentTwist
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ExceptionalPair
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentExceptionalPair
open HeckeFamily CenteredExceptionalProfile CenteredMomentChildRows CenteredMomentFixedRay
open CanonicalRowCompletion CanonicalQuadraticSieve RayFourExpansion
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem fixed_primitive_product (χ ψ τ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hψ : Q ≤ ψ.modulus) (hτ : Q ≤ τ.modulus) :
    ∃ ρ : Character, FiniteFourier.IsPrimitiveOnIdeals ρ.residue ∧
      Q ≤ ρ.modulus ∧ InducedBy (χ.product τ) ρ := by
  obtain ⟨ρ,hmod,hprim,hnorm,hmask⟩ := exists_primitive_product_character ψ τ
  refine ⟨ρ,hprim,(le_inf hψ hτ).trans hmod,?_⟩
  intro I
  by_cases hI : I = 0
  · simp only [hI,idealCoeff_zero,ite_self]
  by_cases hc : IsCoprime I (χ.product τ).modulus
  · have hn := (idealCoeff_ne_zero_iff (χ.product τ) I).mpr ⟨hI,hc⟩
    rw [idealCoeff_product] at hn
    have hχ := (idealCoeff_ne_zero_iff χ I).mp (left_ne_zero_of_mul hn) |>.2
    have he : idealCoeff χ I = idealCoeff ψ I := by rw [h I,if_pos hχ]
    have hnψ : idealCoeff (ψ.product τ) I ≠ 0 := by
      rw [idealCoeff_product,← he]
      exact hn
    have hcψ := (idealCoeff_ne_zero_iff (ψ.product τ) I).mp hnψ |>.2
    change IsCoprime I (ψ.modulus ⊓ τ.modulus) at hcψ
    rw [if_pos hc,idealCoeff_product,he,hmask I,if_pos hcψ]
  · have hz : idealCoeff (χ.product τ) I = 0 := by
      by_contra hn
      exact hc ((idealCoeff_ne_zero_iff (χ.product τ) I).mp hn).2
    rw [hz,if_neg hc]

theorem fixedInducingRow_of_product (η₁ η₂ τ : Character) (Q : Ideal O)
    (m A z₁ z₂ : O) (hτ : Q ≤ τ.modulus)
    (he : ∀ n, rowTwist (HeckeRowClosure.elementHom η₂) m 1 (A*z₂) n =
      rowTwist (HeckeRowClosure.elementHom η₁) m 1 (A*z₁) n * elementCoeff τ n)
    (hx : FixedInducingRow η₁ Q m A z₁) : FixedInducingRow η₂ Q m A z₂ := by
  obtain ⟨χ,ψ,hprim,hind,hQ,hrow⟩ := hx
  obtain ⟨ρ,hρ,hQρ,hindρ⟩ := fixed_primitive_product χ ψ τ hind Q hQ hτ
  refine ⟨χ.product τ,ρ,hρ,hindρ,hQρ,?_⟩
  intro n
  rw [elementCoeff_product,hrow n,he n]

end SevenEighths.CenteredMomentExceptionalPair

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RayNonprincipal
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentRayNonprincipal
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CanonicalRowCompletion HeckePrimeRay
local notation "O" => HeckeFamily.O

theorem product_principal_descent (χ θ:Character)
    (hp:(χ.product θ).residue=1) :
    FiniteConductor.FactorsThroughIdeal χ.residue
      (θ.modulus.map (Ideal.Quotient.mk χ.modulus)) := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  rw [FiniteConductor.factorsThroughIdeal_iff]
  intro u hu
  obtain ⟨q,hq,hqu⟩ := (Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk χ.modulus) Ideal.Quotient.mk_surjective).mp hu
  let a:O := 1+q
  have ha:Ideal.Quotient.mk χ.modulus a=(u:O⧸χ.modulus) := by
    dsimp [a]; rw [map_add,map_one,hqu]; ring
  have hθa:Ideal.Quotient.mk θ.modulus a=1 := by
    simp only [a,map_add,map_one,Ideal.Quotient.eq_zero_iff_mem.mpr hq,add_zero]
  have hcχ:IsCoprime (Ideal.span {a}) χ.modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (ha ▸ u.isUnit)
  have hcθ:IsCoprime (Ideal.span {a}) θ.modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hθa ▸ isUnit_one)
  have hcp:IsCoprime (Ideal.span {a}) (χ.product θ).modulus :=
    (hcχ.mul_right hcθ).of_isCoprime_of_dvd_right
      (Ideal.dvd_iff_le.mpr Ideal.mul_le_inf)
  have hv:elementCoeff (χ.product θ) a=1 := by
    change (χ.product θ).residue _=1
    rw [hp]
    exact MulChar.one_apply ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hcp)
  rw [elementCoeff_product] at hv
  change χ.residue (Ideal.Quotient.mk χ.modulus a)*
    θ.residue (Ideal.Quotient.mk θ.modulus a)=1 at hv
  simpa only [ha,hθa,map_one,mul_one] using hv

theorem product_principal_inducing (χ θ:Character)
    (hp:(χ.product θ).residue=1) :
    ∃ψ:Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      θ.modulus≤ψ.modulus ∧ InducedBy χ ψ :=
  HeckeMaskDescent.exists_primitive_above χ θ.modulus
    (product_principal_descent χ θ hp)

theorem actual_row_twist_nonprincipal (η χ θ:Character) (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (hQ:Q≤θ.modulus) (hex:¬FixedInducingRow η Q m A z) :
    (χ.product θ).residue≠1 := by
  intro hp
  obtain ⟨ψ,hψ,hmod,hind⟩ := product_principal_inducing χ θ hp
  exact hex ⟨χ,ψ,hψ,hind,hQ.trans hmod,hrow⟩

variable (M:Ideal O) [NeZero M]
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.CenteredMomentRayNonprincipal.instFiniteQuotientOIdeal
theorem all_ray_twists_nonprincipal (η χ:Character) (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (hQ:Q≤M) (hex:¬FixedInducingRow η Q m A z) :
    ∀θ:RayQuotient.Characters M H, (twistedFamily M H hH χ θ).residue≠1 := by
  intro θ
  exact actual_row_twist_nonprincipal η χ (HeckeRayQuotient.character M H hH θ)
    Q m A z hrow hQ hex

end SevenEighths.CenteredMomentRayNonprincipal

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.PrimeSlot
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentPrimeSlot
open HeckeFamily HeckeRowClosure HeckePrimeRay HeckePrimeAnnular HeckeDyadic
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentTwist
local notation "O" => HeckeFamily.O

lemma norm_height_split (N D σ t:ℝ) (hN:0<N) (hD:0<D) :
    (((N/D:ℝ):ℂ)^(-shift σ 0))*(N:ℂ)^(Complex.I*t)=
      (D:ℂ)^(Complex.I*t)*((N/D:ℝ):ℂ)^(-shift σ t) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hD).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hD).ne'),
    ←Complex.ofReal_log (div_pos hN hD).le,←Complex.ofReal_log hN.le,
    ←Complex.ofReal_log hD.le,Real.log_div hN.ne' hD.ne',←Complex.exp_add,←Complex.exp_add]
  congr 1
  simp only [HeckeDyadic.shift,Complex.ofReal_sub,Complex.ofReal_zero,zero_mul,sub_zero]
  ring

lemma sqrt_inverse_cpow (D:ℝ) (hD:0<D) :
    (Real.sqrt D:ℂ)⁻¹=(D:ℂ)^(-(1/2:ℂ)) := by
  rw [Complex.cpow_neg,Real.sqrt_eq_rpow]
  congr 1
  simpa using (Complex.ofReal_cpow hD.le (1/2:ℝ))

end SevenEighths.CenteredMomentPrimeSlot

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.PrimeSlotShift
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentPrimeSlotShift
open HeckeFamily HeckeRowClosure HeckePrimeRay HeckePrimeAnnular HeckeDyadic
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentTwist
open CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

lemma norm_height_split (N D σ t v:ℝ) (hN:0<N) (hD:0<D) :
    (((N/D:ℝ):ℂ)^(-shift σ v))*(N:ℂ)^(Complex.I*t)=
      (D:ℂ)^(Complex.I*t)*((N/D:ℝ):ℂ)^(-shift σ (t+v)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hD).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hD).ne'),
    ←Complex.ofReal_log (div_pos hN hD).le,←Complex.ofReal_log hN.le,
    ←Complex.ofReal_log hD.le,Real.log_div hN.ne' hD.ne',←Complex.exp_add,←Complex.exp_add]
  congr 1
  simp only [HeckeDyadic.shift,Complex.ofReal_sub,Complex.ofReal_add]
  ring

theorem normalizedSlot_eq_ray (M:Ideal O) (H:Subgroup (O⧸M)ˣ)
    (η χ:Character) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W:ℝ→ℂ) (b D σ t v:ℝ) (hD:0<D) :
    normalizedSlot η m A z (primePool M H b D) (annularWeight W D σ v) t D=
      (D:ℂ)^(Complex.I*t)*rayPrimePolynomial M H χ W b D σ (t+v) := by
  unfold normalizedSlot rowSlot rayPrimePolynomial primePool
  rw [sqrt_inverse_cpow D hD]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  have hp:Prime I := (Finset.mem_filter.mp hI).2.1
  have hN:0<(I.absNorm:ℝ) := norm_pos ⟨I,hp.ne_zero⟩
  have hc:=idealCoeff_eq_row η χ m 1 (A*z) hrow I
  simp only [one_pow,mul_one] at hc
  rw [←hc]
  change (D:ℂ)^(-(1/2:ℂ))*
    ((W ((I.absNorm:ℝ)/D)*(((I.absNorm:ℝ)/D:ℝ):ℂ)^(-shift σ v))*idealCoeff χ I*
      (I.absNorm:ℂ)^(Complex.I*t))=_
  have hn:=norm_height_split (I.absNorm:ℝ) D σ t v hN hD
  simp only [Complex.ofReal_natCast] at hn
  calc
    _=(D:ℂ)^(-(1/2:ℂ))*(W ((I.absNorm:ℝ)/D)*idealCoeff χ I)*
      ((((I.absNorm:ℝ)/D:ℝ):ℂ)^(-shift σ v)*(I.absNorm:ℂ)^(Complex.I*t)) := by ring
    _=_ := by rw [hn]; unfold annularWeight; ring

end SevenEighths.CenteredMomentPrimeSlotShift

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryRelativeSlots
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

lemma normalizedSlot_character (η ν : Character) (m A z : O)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (t D : ℝ) :
    normalizedSlot η m A z S (fun P=>idealCoeff ν P*β P) t D=
      normalizedSlot (η.product ν) m A z S β t D := by
  unfold normalizedSlot rowSlot
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  rw [idealCoeff_product]
  ring

lemma product_row_presentation (η χ ν : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n) :
    ∀n,elementCoeff (χ.product ν) n=rowTwist (elementHom (η.product ν)) m 1 (A*z) n := by
  intro n
  rw [elementCoeff_product,hrow]
  change (elementCoeff η n*((idealRowHom (m^6*1^4*(A*z))).toMonoidHom.comp principalIdealHom.toMonoidHom) n)*elementCoeff ν n=
    elementCoeff (η.product ν) n*((idealRowHom (m^6*1^4*(A*z))).toMonoidHom.comp principalIdealHom.toMonoidHom) n
  rw [elementCoeff_product]
  ring

theorem relative_normalizedSlot_eq_ray (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ ν : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (W : ℝ→ℂ) (b D σ t v : ℝ) (hD : 0<D) :
    normalizedSlot η m A z (primePool M H b D)
      (fun P=>idealCoeff ν P*HeckePrimeAnnular.annularWeight W D σ v P) t D=
      (D:ℂ)^(Complex.I*t)*HeckePrimeRay.rayPrimePolynomial M H (χ.product ν) W b D σ (t+v) := by
  rw [normalizedSlot_character]
  exact CenteredMomentPrimeSlotShift.normalizedSlot_eq_ray M H (η.product ν) (χ.product ν)
    m A z (product_row_presentation η χ ν m A z hrow) W b D σ t v hD

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FixedRayInducingTransport
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFixedRayInducingTransport
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile
open CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentExceptionalPair CenteredMomentFixedRowMask
local notation "O" => HeckeFamily.O

theorem modulus_generator_ne_zero (ν : Character) :
    idealGenerator ν.modulus ≠ 0 :=
  idealGenerator_ne_zero ν.modulus ν.modulus_ne_bot

theorem modulus_unit_iff (ν : Character) (n : O) :
    IsUnit (Ideal.Quotient.mk ν.modulus n) ↔
      IsCoprime n (idealGenerator ν.modulus) := by
  rw [IdealCharacter.isUnit_mk_iff_isCoprime]
  conv_lhs => rw [←span_idealGenerator ν.modulus]
  rw [Ideal.isCoprime_span_singleton_iff]

theorem elementCoeff_product_inverse_mask (η ν : Character) (n : O) :
    elementCoeff ((η.product ν).product ν.inverse) n =
      if IsCoprime n (idealGenerator ν.modulus) then elementCoeff η n else 0 := by
  rw [elementCoeff_product,elementCoeff_product,elementCoeff_inverse]
  by_cases hn : IsCoprime n (idealGenerator ν.modulus)
  · have hv : elementCoeff ν n ≠ 0 :=
      MulChar.apply_ne_zero_iff.mpr ((modulus_unit_iff ν n).mpr hn)
    simp only [hn,ite_true,mul_assoc,mul_inv_cancel₀ hv,mul_one]
  · have hv : elementCoeff ν n = 0 :=
      MulChar.map_nonunit ν.residue (fun hu=>hn ((modulus_unit_iff ν n).mp hu))
    simp only [hn,ite_false,hv,mul_zero,zero_mul]

theorem rowTwist_product (η ν : Character) (m f z n : O) :
    rowTwist (elementHom (η.product ν)) m f z n =
      rowTwist (elementHom η) m f z n * elementCoeff ν n := by
  change elementCoeff (η.product ν) n * idealRowHom (m^6*f^4*z) (Ideal.span {n}) =
    (elementCoeff η n * idealRowHom (m^6*f^4*z) (Ideal.span {n})) * elementCoeff ν n
  rw [elementCoeff_product]
  ring

theorem rowTwist_product_inverse_mask (η ν : Character) (m A z n : O)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    rowTwist (elementHom ((η.product ν).product ν.inverse)) m 1 (A*z) n =
      rowTwist (elementHom η) (m*idealGenerator ν.modulus) 1 (A*z) n := by
  rw [row_mask_mul η m (idealGenerator ν.modulus) A z n hmLam hm2]
  change elementCoeff ((η.product ν).product ν.inverse) n *
    idealRowHom (m^6*1^4*(A*z)) (Ideal.span {n}) = _
  rw [elementCoeff_product_inverse_mask]
  split_ifs
  · rfl
  · exact zero_mul _

theorem fixedInducingRow_product_of (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (h : FixedInducingRow η Q m A z) :
    FixedInducingRow (η.product ν) Q m A z :=
  fixedInducingRow_of_product η (η.product ν) ν Q m A z z hν
    (fun n=>rowTwist_product η ν m 1 (A*z) n) h

theorem fixedInducingRow_product_iff (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    FixedInducingRow (η.product ν) Q m A z ↔ FixedInducingRow η Q m A z := by
  constructor
  · intro h
    have hi := fixedInducingRow_product_of (η.product ν) ν.inverse Q m A z hν h
    obtain ⟨χ,ψ,hprim,hind,hQ,hrow⟩ := hi
    apply (fixedInducingRow_mul_mask_iff η Q m (idealGenerator ν.modulus) A z
      hm (modulus_generator_ne_zero ν) hA hz hmLam hm2).mp
    exact ⟨χ,ψ,hprim,hind,hQ,fun n=>(hrow n).trans
      (rowTwist_product_inverse_mask η ν m A z n hmLam hm2)⟩
  · exact fixedInducingRow_product_of η ν Q m A z hν

theorem not_fixedInducingRow_product_iff (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    (¬FixedInducingRow (η.product ν) Q m A z) ↔ ¬FixedInducingRow η Q m A z :=
  not_congr (fixedInducingRow_product_iff η ν Q m A z hν hm hA hz hmLam hm2)

end SevenEighths.CenteredMomentFixedRayInducingTransport

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceFamily
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalRowSource
open HeckeFamily HeckeRowClosure CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentSecondHeightFamily CenteredMomentFixedRowMask CenteredExceptionalProfile
local notation "O" => HeckeFamily.O

lemma NaturalRow.ideal {η : Character} {z : O} (F : NaturalRow η z) (I : Ideal O) :
    idealCoeff F.character I=idealCoeff η I*idealRowHom (fixedBadMask^6*z) I := by
  simpa only [one_pow,mul_one] using idealCoeff_eq_row η F.character fixedBadMask 1 z F.element I

end SevenEighths.CenteredMomentNaturalRowSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCharacters
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeRowClosure ConcretePrimeRowBridge CanonicalRowCompletion
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentFixedRayInducingTransport CenteredMomentFixedRowMask CenteredExceptionalProfile
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.instFiniteQuotientOIdeal_solutions
lemma relativeCharacter_fixedQ (η₀ : Character) (θ : RayQuotient.Characters M H)
    (Q : Ideal O) (hQM : Q≤M) (hQη : Q≤η₀.modulus) :
    Q≤(relativeCharacter M H hH η₀ θ).modulus := le_inf hQM hQη

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.PrimeHeight
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.CenteredMomentPrimeHeight
open HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDyadic HeckeZeroSupremum
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.CenteredMomentPrimeHeight.instFiniteQuotientOIdeal
omit [NeZero M] in
theorem ray_prime_bounded_scale (W : ℝ→ℂ) (A B lo hi D : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : Continuous W) (_hD : 1≤D) :
    ∃C : ℝ,0<C ∧ ∀(χ : Character)(P σ freq : ℝ),1≤P → P≤D → lo≤σ → σ≤hi →
      ‖rayPrimePolynomial M H χ W B P σ freq‖≤C := by
  obtain ⟨Cw,hCw,hprofile⟩ := fixed_profile_norm_bound W hW A B lo hi hA
  let S := annulusSet B D
  refine ⟨((S.card:ℝ)+1)*Cw,by positivity,?_⟩
  intro χ P σ freq hP hPD hσ hσhi
  have hp : 0<P := zero_lt_one.trans_le hP
  have hsub : (annulusSet B P).filter (fun I=>Prime I ∧ I∈RayQuotient.identityClass M H)⊆S := by
    intro I hI
    have hi := ConcretePrimeRowBridge.mem_idealsUpTo.mp (Finset.mem_filter.mp hI).1
    apply ConcretePrimeRowBridge.mem_idealsUpTo.mpr
    exact ⟨hi.1,hi.2.trans (Nat.floor_mono (mul_le_mul_of_nonneg_left hPD (le_trans zero_le_one (le_max_left _ _))))⟩
  have hn (I : Ideal O) : ‖idealCoeff χ I*annularWeight W P σ freq I‖≤Cw := by
    have hc := idealCoeff_norm_le_one χ I
    apply (show ‖idealCoeff χ I*annularWeight W P σ freq I‖≤‖annularWeight W P σ freq I‖ by
      rw [norm_mul];exact mul_le_of_le_one_left (norm_nonneg _) hc).trans
    by_cases hz : W ((I.absNorm:ℝ)/P)=0
    · simp [annularWeight,hz,hCw.le]
    · have hs := hWs hz
      rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hA.trans_le hs.1)]
      simpa only [Complex.neg_re,shift_re] using hprofile σ ⟨hσ,hσhi⟩ _ hs
  have hpow : ‖(P:ℂ)^(-(1/2:ℂ))‖≤1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
    norm_num only [Complex.neg_re,show ((1/2:ℂ).re)=1/2 by norm_num]
    exact Real.rpow_le_one_of_one_le_of_nonpos hP (by norm_num)
  unfold rayPrimePolynomial
  rw [norm_mul]
  calc
    _ ≤ ‖∑ I∈(annulusSet B P).filter (fun I=>Prime I ∧ I∈RayQuotient.identityClass M H),
        idealCoeff χ I*annularWeight W P σ freq I‖ := mul_le_of_le_one_left (norm_nonneg _) hpow
    _ ≤ ∑ I∈(annulusSet B P).filter (fun I=>Prime I ∧ I∈RayQuotient.identityClass M H),Cw :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun I _=>hn I))
    _ ≤ ∑ _I∈S,Cw := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>hCw.le)
    _ ≤ _ := by simp only [Finset.sum_const,nsmul_eq_mul];nlinarith

theorem ray_prime_all_height_squared (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧ ∀ Z P : ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀χ : Character,(χ.modulus.absNorm:ℝ)≤Z^Lmod →
      (∀θ : RayQuotient.Characters M H,(twistedFamily M H hH χ θ).residue≠1) →
    ∀σ freq : ℝ,lo≤σ → σ≤hi →
      ‖rayPrimePolynomial M H χ W B P σ freq‖^2≤C*(1+|freq|)^degree*Z^loss*P^κ := by
  obtain ⟨Cbig,Z₀,hCbig,hZ₀,hbig⟩ := ray_prime_all_height_large M H hH W A B hA hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  let K := 2*(|Real.log A|+|Real.log B|)+1
  have hK : 0≤K := by dsimp [K];positivity
  obtain ⟨Csmall,hCs,hsmall⟩ := ray_prime_bounded_scale M H W A B lo hi (Real.exp K) hA hWs hW.continuous
    (Real.one_le_exp hK)
  let degree := ⌈loss⌉₊
  let C0 := Cbig+Csmall^2
  have hC0 : 0<C0 := by dsimp [C0];positivity
  refine ⟨degree,C0*(3:ℝ)^degree,Z₀,by positivity,hZ₀,?_⟩
  intro Z P hZ hP hPcap χ hχ hn σ freq hσ hσhi
  have hz1 : 1≤Z := hZ₀.le.trans hZ
  have hκ0 : 0≤κ := by linarith
  have hpκ : 1≤P^κ := Real.one_le_rpow hP hκ0
  have hzloss : 1≤Z^loss := Real.one_le_rpow hz1 hloss.le
  have htbase : 1≤3+|freq| := by linarith [abs_nonneg freq]
  have htloss : 1≤(3+|freq|)^loss := Real.one_le_rpow htbase hloss.le
  have hbase : ‖rayPrimePolynomial M H χ W B P σ freq‖^2≤C0*P^κ*Z^loss*(3+|freq|)^loss := by
    by_cases hlarge : K≤Real.log P
    · exact (hbig Z P hZ hP hPcap χ hχ hn σ freq hσ hσhi hlarge).trans
        (by dsimp [C0];gcongr; nlinarith [sq_nonneg Csmall])
    · have hPD : P≤Real.exp K := by
        have he := Real.exp_le_exp.mpr (le_of_not_ge hlarge)
        simpa only [Real.exp_log (zero_lt_one.trans_le hP)] using he
      have hb := pow_le_pow_left₀ (norm_nonneg _) (hsmall χ P σ freq hP hPD hσ hσhi) 2
      apply hb.trans
      calc
        Csmall^2 ≤ C0 := by dsimp [C0];linarith
        _ ≤ C0*P^κ := le_mul_of_one_le_right hC0.le hpκ
        _ ≤ C0*P^κ*Z^loss := le_mul_of_one_le_right (by positivity) hzloss
        _ ≤ _ := le_mul_of_one_le_right (by positivity) htloss
  have hheight : (3+|freq|)^loss≤(3:ℝ)^degree*(1+|freq|)^degree := by
    calc
      _ ≤ (3+|freq|)^(degree:ℝ) := Real.rpow_le_rpow_of_exponent_le htbase (Nat.le_ceil loss)
      _ = (3+|freq|)^degree := Real.rpow_natCast _ _
      _ ≤ (3*(1+|freq|))^degree := pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg freq]) _
      _ = _ := mul_pow _ _ _
  apply hbase.trans
  calc
    _ ≤ C0*P^κ*Z^loss*((3:ℝ)^degree*(1+|freq|)^degree) :=
      mul_le_mul_of_nonneg_left hheight (by positivity)
    _ = _ := by ring

end SevenEighths.CenteredMomentPrimeHeight
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceNaturalPrime
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeRowClosure HeckePrimeRay HeckeZeroSupremum
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentFixedRayInducingTransport CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.instFiniteQuotientOIdeal
lemma natural_relative_twists {η : Character} {z : O} (F : NaturalRow η z) (hz : z≠0)
    (η₀ : Character) (Q : Ideal O) (hQM : Q≤M)
    (hex : ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z) :
    ∀θ : RayQuotient.Characters M H,
      (twistedFamily M H hH (F.character.product η₀.inverse) θ).residue≠1 := by
  have hn : ¬FixedInducingRow (η.product η₀.inverse) (internalQ Q η₀) fixedBadMask 1 z :=
    (not_fixedInducingRow_product_iff η η₀.inverse _ fixedBadMask 1 z inf_le_right
      fixedBadMask_ne_zero one_ne_zero hz (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hex
  apply CenteredMomentRayNonprincipal.all_ray_twists_nonprincipal M H hH
    (η.product η₀.inverse) (F.character.product η₀.inverse) (internalQ Q η₀)
    fixedBadMask 1 z ?_ (inf_le_left.trans hQM) hn
  exact product_row_presentation η F.character η₀.inverse fixedBadMask 1 z
    (by simpa only [one_mul] using F.element)

include hH

theorem natural_relative_slot_bound (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
      ∀P : ℝ,1≤P → P≤Z^Lslot → ∀η : Character,∀z : O,z≠0 →
      ∀F : NaturalRow η z,(F.character.modulus.absNorm:ℝ)≤Z^Lmod →
      ∀Q : Ideal O,Q≤M → ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z →
      ∀σ t v : ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H b P)
        (fun I=>idealCoeff η₀.inverse I*HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2≤
        C*(1+|t|+|v|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩:=CenteredMomentPrimeHeight.ray_prime_all_height_squared
    M H hH W a b ha hWs hW (Lmod+1) Lslot loss lo hi κ (by linarith) hLs hloss hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀
  filter_upwards [eventually_ge_atTop Z₀,eventually_ge_atTop (η₀.modulus.absNorm:ℝ),
    eventually_gt_atTop (0:ℝ)] with Z hZ0 hη₀ hZ
  intro P hP hPcap η z hz F hcond Q hQM hex σ t v hσ hσhi
  have hc : ((F.character.product η₀.inverse).modulus.absNorm:ℝ)≤Z^(Lmod+1) := by
    have hb : ((F.character.product η₀.inverse).modulus.absNorm:ℝ)≤
        (F.character.modulus.absNorm:ℝ)*(η₀.modulus.absNorm:ℝ) := by
      exact_mod_cast HeckePrimeScale.product_modulus_bound F.character η₀.inverse
    apply hb.trans
    calc
      _≤Z^Lmod*Z := mul_le_mul hcond hη₀ (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
      _=Z^(Lmod+1) := by rw [Real.rpow_add hZ,Real.rpow_one]
  have hb:=hbound Z P hZ0 hP hPcap (F.character.product η₀.inverse) hc
    (natural_relative_twists M H hH F hz η₀ Q hQM hex) σ (t+v) hσ hσhi
  rw [relative_normalizedSlot_eq_ray M H η F.character η₀.inverse fixedBadMask 1 z
    (by simpa only [one_mul] using F.element) W b P σ t v (zero_lt_one.trans_le hP),norm_mul,
    CenteredMomentTwist.norm_real_imaginary_power P t (zero_lt_one.trans_le hP),one_mul]
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ.le _)
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact pow_le_pow_left₀ (by positivity) (by linarith [abs_add_le t v]) degree

theorem natural_character_slot_bound (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ν : Character,∀ᶠZ : ℝ in atTop,
      ∀P : ℝ,1≤P → P≤Z^Lslot → ∀η : Character,∀z : O,z≠0 →
      ∀F : NaturalRow η z,(F.character.modulus.absNorm:ℝ)≤Z^Lmod →
      ∀Q : Ideal O,Q≤M → Q≤ν.modulus → ¬FixedInducingRow η Q fixedBadMask 1 z →
      ∀σ t v : ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H b P)
        (fun I=>idealCoeff ν I*HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2≤
        C*(1+|t|+|v|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,hC,hbound⟩:=natural_relative_slot_bound M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro ν
  filter_upwards [hbound ν.inverse] with Z hz
  intro P hP hPcap η z hz0 F hcond Q hQM hQν hex σ t v hσ hσhi
  have hQeq : internalQ Q ν.inverse=Q := inf_eq_left.mpr hQν
  have he:=hz P hP hPcap η z hz0 F hcond Q hQM (by simpa only [hQeq] using hex) σ t v hσ hσhi
  simpa only [idealCoeff_inverse_conj,starRingEnd_self_apply] using he

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceRayPrime
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeZeroSupremum CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.instFiniteQuotientOIdeal_1
theorem natural_ray_slots_uniform (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
      ∀θ : RayQuotient.Characters M H,
      ∀P : ℝ,1≤P → P≤Z^Lslot → ∀η : Character,∀z : O,z≠0 →
      ∀F : NaturalRow η z,(F.character.modulus.absNorm:ℝ)≤Z^Lmod →
      ∀Q : Ideal O,Q≤M → ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z →
      ∀σ t v : ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H b P)
        (fun I=>idealCoeff (relativeCharacter M H hH η₀ θ) I*
          HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2≤
        C*(1+|t|+|v|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,hC,hbound⟩:=natural_character_slot_bound M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀
  have hall:=Filter.eventually_all.mpr (fun θ : RayQuotient.Characters M H=>
    hbound (relativeCharacter M H hH η₀ θ))
  filter_upwards [hall] with Z hz
  intro θ P hP hPcap η z hz0 F hcond Q hQM hex σ t v hσ hσhi
  exact hz θ P hP hPcap η z hz0 F hcond (internalQ Q η₀)
    (inf_le_left.trans hQM)
    (relativeCharacter_fixedQ M H hH η₀ θ (internalQ Q η₀) (inf_le_left.trans hQM) inf_le_right)
    hex σ t v hσ hσhi

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorSlots
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeZeroSupremum CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalRowSource CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentWholeSlotDeletion
open CenteredMomentHeckeSlots CenteredMomentPrimeSlot CenteredExceptionalProfile
open CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

lemma natural_slot_eq {η : Character} {z : O} (F : NaturalRow η z)
    (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P t : ℝ) :
    naturalSlot F.character pool (heightCoefficient β t) P=
      normalizedSlot η fixedBadMask 1 z pool β t P := by
  unfold naturalSlot normalizedSlot rowSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [F.ideal]
  simp only [heightCoefficient,one_mul]
  ring

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.CenteredMomentRayMaskedFloor.instFiniteQuotientOIdeal
theorem natural_slot_product_oai {α : Type*} [DecidableEq α]
    (F : Finset α) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤Lslot) →
      (∀i∈F,lo≤σ i) → (∀i∈F,σ i≤hi) → 0≤T → (∀i∈F,|v i|≤T) →
    ∀(η : Character)(z : O),z≠0 → ∀N : NaturalRow η z,
      (N.character.modulus.absNorm:ℝ)≤Z^Lmod →
    ∀Q : Ideal O,Q≤M → ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z →
    ∀A : Finset α,A⊆F →
      ‖∏i∈A,naturalSlot N.character (primePool M H b (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i))‖^2 ≤
      C*(1+|t|+T)^degree*Z^(loss+κ*(∑i∈F,w i)) := by
  let el : ℝ := loss/(F.card+1)
  have hel : 0<el := div_pos hloss (by positivity)
  obtain ⟨J,C,hC,hbound⟩ := natural_ray_slots_uniform M H hH W a b ha hWs hW
    Lmod Lslot el lo hi κ hLm hLs hel hbeta hκ
  let C₀ := max 1 C
  have hC₀ : 1≤C₀ := le_max_left _ _
  refine ⟨J*F.card,C₀^F.card,pow_pos (zero_lt_one.trans_le hC₀) _,?_⟩
  intro η₀
  filter_upwards [hbound η₀,eventually_gt_atTop (1:ℝ)] with Z hz hZ
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η z hz0 N hmod Q hQM hex A hAF
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hk : 0≤κ := by linarith
  have hh : 1≤1+|t|+T := by linarith [abs_nonneg t]
  have hslot (i : α) (hi : i∈A) :
      ‖naturalSlot N.character (primePool M H b (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i))‖^2 ≤
      (C₀*(1+|t|+T)^J)*Z^(el+κ*w i) := by
    rw [natural_slot_eq N]
    have he := hz (θ i) (Z^(w i)) (Real.one_le_rpow hZ.le (hw i (hAF hi)))
      (Real.rpow_le_rpow_of_exponent_le hZ.le (hwL i (hAF hi))) η z hz0 N hmod Q hQM hex
      (σ i) t (v i) (hσlo i (hAF hi)) (hσhi i (hAF hi))
    apply he.trans
    rw [←Real.rpow_mul hZ0.le]
    calc
      _ ≤ (C₀*(1+|t|+T)^J)*Z^el*Z^(w i*κ) := by
        gcongr
        · exact le_max_right 1 C
        · exact hv i (hAF hi)
      _ = _ := by rw [mul_assoc,←Real.rpow_add hZ0]; congr 2 ; ring
  rw [norm_prod,←Finset.prod_pow]
  apply (Finset.prod_le_prod (fun i _=>sq_nonneg _) hslot).trans
  rw [Finset.prod_mul_distrib,Finset.prod_const,←Real.rpow_sum_of_pos hZ0]
  have hexp : (∑i∈A,(el+κ*w i))≤loss+κ*(∑i∈F,w i) := by
    rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum]
    have hc : (A.card:ℝ)≤F.card+1 := by exact_mod_cast (Finset.card_le_card hAF).trans (Nat.le_succ _)
    have he : (A.card:ℝ)*el≤loss := by
      calc
        _ ≤ (F.card+1)*el := mul_le_mul_of_nonneg_right hc hel.le
        _ = _ := by dsimp [el]; field_simp
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hAF (fun i hi _=>hw i hi)
    nlinarith
  have hp : 1≤C₀*(1+|t|+T)^J := one_le_mul_of_one_le_of_one_le hC₀ (one_le_pow₀ hh)
  apply (mul_le_mul (pow_le_pow_right₀ hp (Finset.card_le_card hAF))
    (Real.rpow_le_rpow_of_exponent_le hZ.le hexp) (by positivity) (by positivity)).trans_eq
  rw [mul_pow,←pow_mul]

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CenteredMomentRayMaskedFloor.natural_slot_product_oai.{u_1} := @OAI.SevenEighths.CenteredMomentRayMaskedFloor.natural_slot_product_oai.{u_1}
