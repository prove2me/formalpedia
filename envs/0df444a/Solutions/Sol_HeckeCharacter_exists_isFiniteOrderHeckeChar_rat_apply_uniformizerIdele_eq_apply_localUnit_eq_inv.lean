-- Prove2me | solution 1 for HeckeCharacter.exists_isFiniteOrderHeckeChar_rat_apply_uniformizerIdele_eq_apply_localUnit_eq_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/db92ed29-7a92-5c97-be42-470bbe368027

import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import Mathlib.NumberTheory.Padics.RingHoms
import Theorems.Thm_DirichletCharacter_isFiniteOrderHeckeChar_dirichletIdeleChar
import Theorems.Thm_DirichletCharacter_admitsModulus_dirichletIdeleChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCharacter_exists_isFiniteOrderHeckeChar_rat_apply_uniformizerIdele_eq_apply_localUnit_eq_inv

set_option autoImplicit false

noncomputable section

namespace P124B

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open Rat.HeightOneSpectrum NumberField.AdelicLevel RatIdele AdelicDock

local notation "𝔸ℚ" => AdeleRing (𝓞 ℚ) ℚ

attribute [local instance] RatIdele.fact_prime_of_mem_primeFactors

section

variable (q : ℕ) [hq : Fact q.Prime] (b : ℕ)

theorem neZero_pow : NeZero (q ^ b) := ⟨pow_ne_zero _ hq.out.ne_zero⟩

attribute [local instance] neZero_pow

theorem natGenerator_padicPlace (ℓ : ℕ) [Fact ℓ.Prime] : natGenerator (padicPlace ℓ) = ℓ :=
  natGenerator_primesEquiv_symm ⟨ℓ, Fact.out⟩

theorem apply_uniformizerIdele (χ : DirichletCharacter ℂ (q ^ b)) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) :
    ((χ.dirichletIdeleChar (AutomorphicForm.uniformizerIdele ℚ (@padicPlace ℓ ⟨hℓ⟩)) : ℂˣ) : ℂ)
      = χ ((ℓ : ℕ) : ZMod (q ^ b)) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hv : ¬ natGenerator (padicPlace ℓ) ∣ q ^ b := by
    rw [natGenerator_padicPlace]
    intro h
    exact hℓq ((Nat.prime_dvd_prime_iff_eq hℓ hq.out).mp (hℓ.dvd_of_dvd_pow h))
  unfold AutomorphicForm.uniformizerIdele
  rw [DirichletCharacter.coe_dirichletIdeleChar_finIncl_localUnit_of_valued_exp_neg_one χ hv _
    (valued_uniformizerUnit ℚ (padicPlace ℓ)), natGenerator_padicPlace]

def unitAtQ (u : ℤ_[q]ˣ) : ((padicPlace q).adicCompletion ℚ)ˣ :=
  Units.map (padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u)

theorem coe_unitAtQ (u : ℤ_[q]ˣ) :
    (unitAtQ q u : (padicPlace q).adicCompletion ℚ) = padicRingEquiv q ((u : ℤ_[q]) : ℚ_[q]) := rfl

theorem norm_coe_units (u : ℤ_[q]ˣ) : ‖((u : ℤ_[q]) : ℚ_[q])‖ = 1 := by
  rw [← PadicInt.norm_def]
  exact PadicInt.isUnit_iff.mp u.isUnit

theorem valued_unitAtQ (u : ℤ_[q]ˣ) : Valued.v (unitAtQ q u : (padicPlace q).adicCompletion ℚ) = 1 := by
  have h1 : padicRingEquiv q (1 : ℚ_[q]) = 1 := map_one _
  apply le_antisymm
  · have h := (valued_le_valued_iff q ((u : ℤ_[q]) : ℚ_[q]) 1 one_ne_zero).mpr
      (by rw [norm_coe_units, norm_one])
    rwa [h1, map_one] at h
  · have h := (valued_le_valued_iff q 1 ((u : ℤ_[q]) : ℚ_[q])
      (by rw [← norm_ne_zero_iff, norm_coe_units]; exact one_ne_zero)).mpr (by rw [norm_coe_units, norm_one])
    rwa [h1, map_one] at h

def unitIdeleQ (u : ℤ_[q]ˣ) : (𝔸ℚ)ˣ :=
  Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ (padicPlace q) (unitAtQ q u))

theorem ρ_unitIdeleQ (u : ℤ_[q]ˣ) : ρ (unitIdeleQ q u) = 1 :=
  ρ_finIncl_localUnit_of_valued_one _ _ (valued_unitAtQ q u)

theorem unitIntAt_unitIdeleQ (u : ℤ_[q]ˣ) :
    unitIntAt (padicPlace q) (unitIdeleQ q u) = PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨q, hq.out⟩ (u : ℤ_[q]) := by
  apply Subtype.ext
  rw [coe_unitIntAt, PadicInt.coe_adicCompletionIntegersEquiv_apply]
  exact unitAt_finIncl_localUnit_self _ _ (valued_unitAtQ q u)

set_option maxHeartbeats 3200000 in
theorem unitPadicAt_unitIdeleQ (u : ℤ_[q]ˣ) : unitPadicAt q (unitIdeleQ q u) = (u : ℤ_[q]) := by
  unfold unitPadicAt
  show (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨q, hq.out⟩).symm (unitIntAt (padicPlace q) (unitIdeleQ q u)) = u
  rw [unitIntAt_unitIdeleQ]
  exact (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨q, hq.out⟩).symm_apply_apply _

theorem equivPi_apply_eq_cast (p : (q ^ b).primeFactors) (z : ZMod (q ^ b)) :
    ZMod.equivPi (q ^ b) (NeZero.ne _) z p
      = ZMod.castHom (show (p : ℕ) ^ (q ^ b).factorization p ∣ q ^ b from Nat.ordProj_dvd _ _) (ZMod _) z := by
  have h := RingHom.ext_zmod
    ((Pi.evalRingHom (fun p : (q ^ b).primeFactors => ZMod ((p : ℕ) ^ (q ^ b).factorization p)) p).comp
      (ZMod.equivPi (q ^ b) (NeZero.ne _)).toRingHom)
    (ZMod.castHom (show (p : ℕ) ^ (q ^ b).factorization p ∣ q ^ b from Nat.ordProj_dvd _ _) (ZMod _))
  exact congrFun (congrArg DFunLike.coe h) z

theorem factorization_pow_self : (q ^ b).factorization q = b := by
  rw [hq.out.factorization_pow, Finsupp.single_eq_same]

theorem unitResidue_unitIdeleQ (u : ℤ_[q]ˣ) :
    unitResidue (q ^ b) (unitIdeleQ q u) = PadicInt.toZModPow b (u : ℤ_[q]) := by
  apply (ZMod.equivPi (q ^ b) (NeZero.ne _)).injective
  rw [equivPi_unitResidue]
  funext p
  obtain ⟨p, hpmem⟩ := p
  have hpq : p = q := by
    have h := (Nat.mem_primeFactors.mp hpmem)
    exact (Nat.prime_dvd_prime_iff_eq h.1 hq.out).mp (h.1.dvd_of_dvd_pow h.2.1)
  subst hpq
  rw [equivPi_apply_eq_cast p b ⟨p, hpmem⟩, ZMod.castHom_apply]
  show PadicInt.toZModPow ((p ^ b).factorization p) (unitPadicAt p (unitIdeleQ p u)) = _
  rw [unitPadicAt_unitIdeleQ, PadicInt.cast_toZModPow _ _ (le_of_eq (factorization_pow_self p b))]

theorem toHomUnits_unitResidue_unitIdeleQ (u : ℤ_[q]ˣ) :
    (unitResidue (q ^ b)).toHomUnits (unitIdeleQ q u) = Units.map (PadicInt.toZModPow b).toMonoidHom u :=
  Units.ext (by rw [MonoidHom.coe_toHomUnits, unitResidue_unitIdeleQ, Units.coe_map]; rfl)

theorem apply_unitIdeleQ (χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ) (u : ℤ_[q]ˣ) :
    DirichletCharacter.dirichletIdeleChar (MulChar.ofUnitHom χ₀ : DirichletCharacter ℂ (q ^ b)) (unitIdeleQ q u)
      = (χ₀ (Units.map (PadicInt.toZModPow b).toMonoidHom u))⁻¹ := by
  have htoUnit : (MulChar.ofUnitHom χ₀ : DirichletCharacter ℂ (q ^ b)).toUnitHom = χ₀ :=
    MulChar.equivToUnitHom.apply_symm_apply χ₀
  show ((MulChar.ofUnitHom χ₀ : DirichletCharacter ℂ (q ^ b)).toUnitHom.comp (unitResidue (q ^ b)).toHomUnits)⁻¹
    (unitIdeleQ q u) = _
  rw [MonoidHom.inv_apply, MonoidHom.comp_apply, toHomUnits_unitResidue_unitIdeleQ, htoUnit]

theorem apply_localUnit_of_coe_eq (χ : DirichletCharacter ℂ (q ^ b)) (x : ℚ_[q]ˣ) (hx : (x : ℚ_[q]) = q) :
    χ.dirichletIdeleChar (Units.map (finIncl (𝓞 ℚ) ℚ)
      (localUnit (𝓞 ℚ) ℚ (padicPlace q) (Units.map (padicRingEquiv q).toMonoidHom x))) = 1 := by
  set t : ((padicPlace q).adicCompletion ℚ)ˣ := Units.map (padicRingEquiv q).toMonoidHom x with ht
  have htq : (t : (padicPlace q).adicCompletion ℚ) = ((q : ℕ) : (padicPlace q).adicCompletion ℚ) := by
    show padicRingEquiv q (x : ℚ_[q]) = _
    rw [hx, map_natCast]
  have htv : Valued.v (t : (padicPlace q).adicCompletion ℚ) = exp (-1 : ℤ) := by
    have h := valuation_natGenerator (padicPlace q)
    rw [natGenerator_padicPlace] at h
    rw [htq, ← map_natCast (algebraMap ℚ ((padicPlace q).adicCompletion ℚ)), valued_algebraMap_rat]
    exact h
  refine DirichletCharacter.dirichletIdeleChar_eq_one_of_unitResidue_eq_one χ
    (unitResidue_eq_one (q ^ b) fun w hw => ?_)
  have hwq : natGenerator w = q := (Nat.prime_dvd_prime_iff_eq (prime_natGenerator w) hq.out).mp
    ((prime_natGenerator w).dvd_of_dvd_pow hw)
  have hwv : w = padicPlace q := eq_of_natGenerator_eq (by rw [hwq, natGenerator_padicPlace])
  subst hwv
  unfold unitAt
  rw [ρ_finIncl_localUnit _ _ htv, Units.coe_map, finIncl_apply_snd, localUnit_apply_self, htq,
    natGenerator_padicPlace, map_natCast]
  exact mul_inv_cancel₀ (natCast_adicCompletion_ne_zero _ hq.out.ne_zero)

theorem main (χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ) :
    ∃ η : (𝔸ℚ)ˣ →* ℂˣ,
      HeckeCharacter.IsFiniteOrderHeckeChar ℚ η ∧
      HeckeCharacter.AdmitsModulus ℚ η (ratLevel (q ^ b)) ∧
      AutomorphicForm.IsUnitaryChar (𝓞 ℚ) ℚ η ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q),
        (η (AutomorphicForm.uniformizerIdele ℚ (@padicPlace ℓ ⟨hℓ⟩)) : ℂ) =
          χ₀ (ZMod.unitOfCoprime ℓ (((Nat.coprime_primes hℓ (Fact.out : q.Prime)).mpr hℓq).pow_right b))) ∧
      (∀ u : ℤ_[q]ˣ,
        η (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ (padicPlace q)
            (Units.map (padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) =
          (χ₀ (Units.map (PadicInt.toZModPow b).toMonoidHom u))⁻¹) ∧
      (∀ x : ℚ_[q]ˣ, (x : ℚ_[q]) = q →
        η (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ (padicPlace q)
            (Units.map (padicRingEquiv q).toMonoidHom x))) = 1) := by
  set χ : DirichletCharacter ℂ (q ^ b) := MulChar.ofUnitHom χ₀ with hχ
  refine ⟨χ.dirichletIdeleChar, DirichletCharacter.isFiniteOrderHeckeChar_dirichletIdeleChar χ,
    DirichletCharacter.admitsModulus_dirichletIdeleChar χ, fun x => DirichletCharacter.norm_coe_dirichletIdeleChar_apply χ x,
    fun ℓ hℓ hℓq => ?_, fun u => apply_unitIdeleQ q b χ₀ u, fun x hx => apply_localUnit_of_coe_eq q b χ x hx⟩
  rw [apply_uniformizerIdele q b χ ℓ hℓ hℓq,
    ← ZMod.coe_unitOfCoprime ℓ (((Nat.coprime_primes hℓ hq.out).mpr hℓq).pow_right b), hχ, MulChar.ofUnitHom_coe]

end

end P124B

end

theorem solution
    (q : ℕ) [Fact q.Prime] (b : ℕ) (χ₀ : (ZMod (q ^ b))ˣ →* ℂˣ) :
    ∃ η : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ →* ℂˣ,
      HeckeCharacter.IsFiniteOrderHeckeChar ℚ η ∧
      HeckeCharacter.AdmitsModulus ℚ η (AdelicDock.ratLevel (q ^ b)) ∧
      AutomorphicForm.IsUnitaryChar (NumberField.RingOfIntegers ℚ) ℚ η ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q),
        (η (AutomorphicForm.uniformizerIdele ℚ (@AdelicDock.padicPlace ℓ ⟨hℓ⟩)) : ℂ) =
          χ₀ (ZMod.unitOfCoprime ℓ (((Nat.coprime_primes hℓ (Fact.out : q.Prime)).mpr hℓq).pow_right b))) ∧
      (∀ u : ℤ_[q]ˣ,
        η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
          (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
            (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom (Units.map PadicInt.Coe.ringHom.toMonoidHom u)))) =
          (χ₀ (Units.map (PadicInt.toZModPow b).toMonoidHom u))⁻¹) ∧
      (∀ x : ℚ_[q]ˣ, (x : ℚ_[q]) = q →
        η (Units.map (NumberField.AdelicLevel.finIncl (NumberField.RingOfIntegers ℚ) ℚ)
          (NumberField.AdelicLevel.localUnit (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.padicPlace q)
            (Units.map (AdelicDock.padicRingEquiv q).toMonoidHom x))) = 1) :=
  P124B.main q b χ₀

end S_HeckeCharacter_exists_isFiniteOrderHeckeChar_rat_apply_uniformizerIdele_eq_apply_localUnit_eq_inv
end P2MW
export P2MW.S_HeckeCharacter_exists_isFiniteOrderHeckeChar_rat_apply_uniformizerIdele_eq_apply_localUnit_eq_inv (solution)
