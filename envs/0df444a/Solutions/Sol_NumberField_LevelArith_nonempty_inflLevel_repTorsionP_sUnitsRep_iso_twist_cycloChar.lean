-- Prove2me | solution 1 for NumberField.LevelArith.nonempty_inflLevel_repTorsionP_sUnitsRep_iso_twist_cycloChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/63586b60-d5fe-5a88-b4ea-0acfb0120913

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_nonempty_inflLevel_repTorsionP_sUnitsRep_iso_twist_cycloChar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField.LevelArith

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation IsDedekindDomain NumberField NumberField.LevelArith"
open scoped Classical NumberField.LevelArith NumberField Pointwise

namespace TorsionUnits

section RootsOfUnity
variable {K : Type} [Field K] [NumberField K]

lemma valuation_eq_one_of_pow_eq_one {u : K} {n : ℕ} (hn : 0 < n) (hu : u ^ n = 1) (w : HeightOneSpectrum (𝓞 K)) :
    w.valuation K u = 1 := by
  have h1 : (w.valuation K u) ^ n = 1 := by rw [← map_pow, hu, map_one]
  have hu0 : u ≠ 0 := by rintro rfl; rw [zero_pow hn.ne'] at hu; exact zero_ne_one hu
  have hv0 : w.valuation K u ≠ 0 := (Valuation.ne_zero_iff _).2 hu0
  rcases lt_trichotomy (w.valuation K u) 1 with h | h | h
  · exfalso
    have : (w.valuation K u) ^ n < 1 := pow_lt_one₀ zero_le' h hn.ne'
    rw [h1] at this; exact lt_irrefl _ this
  · exact h
  · exfalso
    have : 1 < (w.valuation K u) ^ n := one_lt_pow₀ h hn.ne'
    rw [h1] at this; exact lt_irrefl _ this

variable (E : Type) [Field E] [NumberField E] [Algebra E K]

lemma mem_sUnits_of_pow_eq_one (S : Finset (HeightOneSpectrum (𝓞 E))) {u : Kˣ} {n : ℕ} (hn : 0 < n) (hu : u ^ n = 1) :
    u ∈ NumberField.SUnits.sUnits E K S := by
  rw [NumberField.SUnits.mem_sUnits_iff]
  intro σ w _
  apply valuation_eq_one_of_pow_eq_one hn
  rw [← map_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, map_one]

end RootsOfUnity

end TorsionUnits

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace TorsionUnits

section Module
variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
  (S : Finset (HeightOneSpectrum (𝓞 E))) (p : ℕ) [hp : Fact p.Prime]

abbrev T : Type := ↥(Submodule.torsionBy ℤ ↥(NumberField.SUnits.sUnitsSubmodule E K S) (p : ℤ))

abbrev tval (t : T E K S p) : Kˣ := NumberField.SUnits.val E K S t.1

lemma tval_injective : Function.Injective (tval E K S p) := fun t t' h =>
  Subtype.ext (Subtype.ext (Additive.toMul.injective h))

lemma tval_add (t t' : T E K S p) : tval E K S p (t + t') = tval E K S p t * tval E K S p t' := rfl

lemma tval_nsmul (k : ℕ) (t : T E K S p) : tval E K S p (k • t) = tval E K S p t ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero]; rfl
  | succ k ih => rw [add_smul, one_smul, tval_add, ih, pow_succ]

lemma tval_zmod_smul (a : ZMod p) (t : T E K S p) : tval E K S p (a • t) = tval E K S p t ^ a.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a, Nat.cast_smul_eq_nsmul]
  exact tval_nsmul E K S p a.val t

lemma tval_pow_p (t : T E K S p) : tval E K S p t ^ p = 1 := by
  have ht := (Submodule.mem_torsionBy_iff (p : ℤ) t.1).1 t.2
  have : NumberField.SUnits.val E K S ((p : ℤ) • t.1) = 1 := by rw [ht]; rfl
  have h2 : NumberField.SUnits.val E K S ((p : ℤ) • t.1) = NumberField.SUnits.val E K S t.1 ^ (p : ℤ) :=
    NumberField.SUnits.val_zsmul E K S (p : ℤ) t.1
  rw [h2, zpow_natCast] at this
  exact this

lemma tval_rho (σ : K ≃ₐ[E] K) (t : T E K S p) :
    tval E K S p ((repTorsionP p (NumberField.SUnits.sUnitsRep E K S)).ρ σ t) = σ • tval E K S p t := rfl

variable {K p}
variable (ζK : K) (hζ : IsPrimitiveRoot ζK p)

noncomputable def zu : Kˣ := (hζ.isUnit hp.out.ne_zero).unit

lemma coe_zu : ((zu ζK hζ : Kˣ) : K) = ζK := rfl

lemma zu_pow_p : zu ζK hζ ^ p = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_zu, hζ.pow_eq_one, Units.val_one]

noncomputable def g : T E K S p :=
  ⟨⟨Additive.ofMul (zu ζK hζ), mem_sUnits_of_pow_eq_one E S hp.out.pos (zu_pow_p ζK hζ)⟩, by
    rw [Submodule.mem_torsionBy_iff]
    apply Subtype.ext
    show ((p : ℤ) • Additive.ofMul (zu ζK hζ) : Additive Kˣ) = 0
    rw [← ofMul_zpow, zpow_natCast, zu_pow_p]; rfl⟩

lemma tval_g : tval E K S p (g E S ζK hζ) = zu ζK hζ := rfl

noncomputable def f : ZMod p →ₗ[ZMod p] T E K S p := LinearMap.toSpanSingleton (ZMod p) (T E K S p) (g E S ζK hζ)

lemma tval_f (a : ZMod p) : tval E K S p (f E S ζK hζ a) = zu ζK hζ ^ a.val := by
  show tval E K S p (a • g E S ζK hζ) = _
  rw [tval_zmod_smul, tval_g]

lemma zu_pow_eq_pow {m n : ℕ} (h : m % p = n % p) : zu ζK hζ ^ m = zu ζK hζ ^ n := by
  rw [← Nat.mod_add_div m p, ← Nat.mod_add_div n p, pow_add, pow_add, pow_mul, pow_mul, zu_pow_p, one_pow, one_pow, h]

lemma f_bijective : Function.Bijective (f E S ζK hζ) := by
  constructor
  · intro a b h
    have h' := congrArg (fun t => ((tval E K S p t : Kˣ) : K)) h
    simp only [tval_f, Units.val_pow_eq_pow_val, coe_zu] at h'
    exact ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h')
  · intro t
    have hu : ((tval E K S p t : Kˣ) : K) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, tval_pow_p, Units.val_one]
    obtain ⟨i, hi, hit⟩ := hζ.eq_pow_of_pow_eq_one hu
    refine ⟨(i : ZMod p), tval_injective E K S p (Units.ext ?_)⟩
    rw [tval_f, ZMod.val_natCast_of_lt hi, Units.val_pow_eq_pow_val, coe_zu, hit]

noncomputable def fEquiv : ZMod p ≃ₗ[ZMod p] T E K S p := LinearEquiv.ofBijective (f E S ζK hζ) (f_bijective E S ζK hζ)

end Module

end TorsionUnits

local instance TorsionUnits.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance TorsionUnits.isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance TorsionUnits.normalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

namespace TorsionUnits

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section Level
variable {p : ℕ} [hp : Fact p.Prime] (S : Finset Nat.Primes)
  (K L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
  (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
  (ζ : Qbar) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L)

def ζL : ↥(levelField K L hKL) := ⟨ζ, (IntermediateField.mem_extendScalars hKL).2 hζL⟩

include hζ in
lemma hζL' : IsPrimitiveRoot (ζL K L hKL ζ hζL) p :=
  IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥(levelField K L hKL) Qbar) (by exact hζ)
    (algebraMap ↥(levelField K L hKL) Qbar).injective

lemma smul_zu (γ : ↥K.fixingSubgroup) :
    (levelGal K L hKL γ) • zu (ζL K L hKL ζ hζL) (hζL' K L hKL ζ hζ hζL) =
      zu (ζL K L hKL ζ hζL) (hζL' K L hKL ζ hζ hζL) ^ ((cycloChar p (γ : Γ) : ZMod p)).val := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  apply Units.ext
  apply (algebraMap ↥(levelField K L hKL) Qbar).injective
  rw [Units.val_pow_eq_pow_val, map_pow]
  show (((levelGal K L hKL γ) (ζL K L hKL ζ hζL) : ↥(levelField K L hKL)) : Qbar) = (ζ : Qbar) ^ _
  rw [levelGal_apply_coe]
  show (γ : Γ) ζ = ζ ^ ((cycloChar p (γ : Γ) : ZMod p)).val
  have ht : (hζ.isUnit hp.out.ne_zero).unit ∈ rootsOfUnity p Qbar := by
    rw [mem_rootsOfUnity]; apply Units.ext
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hζ.pow_eq_one, Units.val_one]
  exact modularCyclotomicCharacter.spec Qbar (card_rootsOfUnity_eq_self p) ((γ : Γ) : Qbar ≃+* Qbar) ht

noncomputable def repEquiv :
    ((Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p)).ρ.twist ((cycloChar p).comp K.fixingSubgroup.subtype)).Equiv
      ((torsionP p (NumberField.SUnits.sUnitsRep ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S)).ρ).comp
        (levelGal K L hKL)) :=
  Representation.Equiv.mk
    (fEquiv ↥K (placesOverPrimesFinset ↥K S) (ζL K L hKL ζ hζL) (hζL' K L hKL ζ hζ hζL)) fun γ => by
    apply LinearMap.ext
    intro a
    apply tval_injective ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S) p
    show tval ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S) p
        (f ↥K (placesOverPrimesFinset ↥K S) (ζL K L hKL ζ hζL) (hζL' K L hKL ζ hζ hζL)
          ((((cycloChar p).comp K.fixingSubgroup.subtype γ : (ZMod p)ˣ) : ZMod p) • a)) =
      tval ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S) p
        ((repTorsionP p (NumberField.SUnits.sUnitsRep ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S))).ρ
          (levelGal K L hKL γ)
          (f ↥K (placesOverPrimesFinset ↥K S) (ζL K L hKL ζ hζL) (hζL' K L hKL ζ hζ hζL) a))
    rw [tval_rho, tval_f, tval_f, smul_pow', smul_zu K L hKL ζ hζ hζL γ, ← pow_mul, MonoidHom.comp_apply, Subgroup.coe_subtype, smul_eq_mul]
    apply zu_pow_eq_pow _ (hζL' K L hKL ζ hζ hζL)
    rw [ZMod.val_mul, Nat.mod_mod]

end Level

end TorsionUnits

open TorsionUnits in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L) :
    Nonempty (inflLevel K L hKL (repTorsionP p
        (NumberField.SUnits.sUnitsRep ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S))) ≅
      (Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp K.fixingSubgroup.subtype)) :=
  ⟨(Rep.mkIso (repEquiv S K L hKL ζ hζ hζL)).symm⟩

end S_NumberField_LevelArith_nonempty_inflLevel_repTorsionP_sUnitsRep_iso_twist_cycloChar
end P2MW
export P2MW.S_NumberField_LevelArith_nonempty_inflLevel_repTorsionP_sUnitsRep_iso_twist_cycloChar (solution)
