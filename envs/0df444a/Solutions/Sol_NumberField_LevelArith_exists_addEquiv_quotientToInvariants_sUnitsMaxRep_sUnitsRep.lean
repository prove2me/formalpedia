-- Prove2me | solution 1 for NumberField.LevelArith.exists_addEquiv_quotientToInvariants_sUnitsMaxRep_sUnitsRep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8d309fd2-077d-5a69-b65c-d01bae984f1c

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SUnitsMax
import Theorems.Thm_NumberField_existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one
import Theorems.Thm_NumberField_natCast_mem_asIdeal_of_forall_map_mem_iff_valuation_le_one
import Theorems.Thm_NumberField_exists_valuationSubring_forall_map_mem_iff_valuation_le_one
import Theorems.Thm_NumberField_LevelArith_sUnitsMaxStable_eq_sUnitsMax
import Theorems.Thm_NumberField_LevelArith_levelGal_surjective_and_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_addEquiv_quotientToInvariants_sUnitsMaxRep_sUnitsRep
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology NumberField.LevelArith P2MW.S_NumberField_LevelArith_exists_addEquiv_quotientToInvariants_sUnitsMaxRep_sUnitsRep.NumberField.LevelArith"
p2m_open_scoped "NumberField.LevelArith P2MW.S_NumberField_LevelArith_exists_addEquiv_quotientToInvariants_sUnitsMaxRep_sUnitsRep.NumberField.LevelArith"
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
p2m_open "NumberField P2MW.S_NumberField_LevelArith_exists_addEquiv_quotientToInvariants_sUnitsMaxRep_sUnitsRep.NumberField"

noncomputable section
namespace NumberField
p2m_export "NumberField" "place SUnits.sUnits SUnits.mem_sUnits_iff SUnits.mem_sUnitsSubmodule SUnits.sUnitsRep existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one natCast_mem_asIdeal_of_forall_map_mem_iff_valuation_le_one exists_valuationSubring_forall_map_mem_iff_valuation_le_one"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField levelGal levelGal_apply_coe mem_placesOverPrimes_iff placesOverPrimesFinset mem_placesOverPrimesFinset IsSUnitMax sUnitsMaxStable sUnitsMaxStable_le smul_mem_sUnitsMaxStable sUnitsMaxRep sUnitsMaxRep.val sUnitsMaxRep.val_ρ sUnitsMaxStable_eq_sUnitsMax levelGal_surjective_and_ker"
p2m_open "NumberField.LevelArith NumberField"
namespace A6b
open IsDedekindDomain

variable (S : Finset Nat.Primes)

section Places
variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

lemma exists_prime_natCast_mem (w : HeightOneSpectrum (𝓞 K)) : ∃ q : Nat.Primes, ((q : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  classical

  have key : ∀ n : ℕ, 1 < n → ((n : ℕ) : 𝓞 K) ∈ w.asIdeal → ∃ q : Nat.Primes, ((q : ℕ) : 𝓞 K) ∈ w.asIdeal := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn hmem
      obtain ⟨q, hq, m, rfl⟩ : ∃ q, q.Prime ∧ ∃ m, n = q * m :=
        let ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hn.ne'
        ⟨q, hq, hqd⟩
      rw [Nat.cast_mul] at hmem
      rcases w.isPrime.mem_or_mem hmem with h | h
      · exact ⟨⟨q, hq⟩, h⟩
      · have hm1 : m ≠ 1 := by
          rintro rfl; rw [Nat.cast_one] at h; exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
        have hm0 : m ≠ 0 := by rintro rfl; simp at hn
        have hmlt : m < q * m := lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm0) hq.one_lt
        exact ih m hmlt (by omega) h
  have hN : (Ideal.absNorm w.asIdeal : 𝓞 K) ∈ w.asIdeal := Ideal.absNorm_mem w.asIdeal
  have hN1 : Ideal.absNorm w.asIdeal ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact w.isPrime.ne_top
  have hN0 : Ideal.absNorm w.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  exact key _ (by omega) hN

omit [NumberField K] in

lemma prime_unique {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (w : HeightOneSpectrum (𝓞 K))
    (hpw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal) (hqw : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) : p = q := by
  by_contra hne
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have : ((a * p + b * q : ℤ) : 𝓞 K) ∈ w.asIdeal := by
    push_cast
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ (by exact_mod_cast hpw)) (w.asIdeal.mul_mem_left _ (by exact_mod_cast hqw))
  rwa [hab, Int.cast_one] at this

end Places
end A6b
end NumberField.LevelArith
end

noncomputable section
namespace NumberField
p2m_export "NumberField" "place SUnits.sUnits SUnits.mem_sUnits_iff SUnits.mem_sUnitsSubmodule SUnits.sUnitsRep existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one natCast_mem_asIdeal_of_forall_map_mem_iff_valuation_le_one exists_valuationSubring_forall_map_mem_iff_valuation_le_one"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField levelGal levelGal_apply_coe mem_placesOverPrimes_iff placesOverPrimesFinset mem_placesOverPrimesFinset IsSUnitMax sUnitsMaxStable sUnitsMaxStable_le smul_mem_sUnitsMaxStable sUnitsMaxRep sUnitsMaxRep.val sUnitsMaxRep.val_ρ sUnitsMaxStable_eq_sUnitsMax levelGal_surjective_and_ker"
p2m_open "NumberField.LevelArith NumberField"
namespace A6b
open IsDedekindDomain

local notation "Qbar" => (AlgebraicClosure ℚ)

variable (S : Finset Nat.Primes)

section ValOne
variable {K : Type} [Field K] [NumberField K]

lemma valuation_eq_one_of_isSUnitMax (σ : K →+* Qbar) (y : Kˣ) (hy : IsSUnitMax S (Units.map (σ : K →* Qbar) y))
    (w : HeightOneSpectrum (𝓞 K)) (q : Nat.Primes) (hq : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) (hqS : q ∉ S) :
    w.valuation K (y : K) = 1 := by
  obtain ⟨B, hB⟩ := NumberField.exists_valuationSubring_forall_map_mem_iff_valuation_le_one K σ w
  have hq0 : ((q : ℕ) : Qbar) ≠ 0 := by exact_mod_cast q.2.ne_zero
  have hq0K : ((q : ℕ) : K) ≠ 0 := by exact_mod_cast q.2.ne_zero

  have hwq : w.valuation K ((q : ℕ) : K) < 1 := by
    have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) w ((q : ℕ) : 𝓞 K)).2 hq
    simpa using this

  have hninv : ((q : ℕ) : Qbar)⁻¹ ∉ B := by
    intro hinv
    have h : w.valuation K (((q : ℕ) : K)⁻¹) ≤ 1 := (hB _).1 (by simpa using hinv)
    rw [map_inv₀, inv_le_one₀ (lt_of_le_of_ne zero_le' (Ne.symm ((map_ne_zero _).2 hq0K)))] at h
    exact absurd hwq (not_lt.2 h)

  have hBq : B.LiesOverPrime q := by
    change ((q : ℕ) : Qbar) ∈ B.nonunits
    rw [ValuationSubring.mem_nonunits_iff]
    have h : ¬ B.valuation (((q : ℕ) : Qbar)⁻¹) ≤ 1 := fun h => hninv ((ValuationSubring.valuation_le_one_iff B _).1 h)
    rw [map_inv₀, inv_le_one₀ (lt_of_le_of_ne zero_le' (Ne.symm ((map_ne_zero _).2 hq0)))] at h
    exact lt_of_not_ge h
  obtain ⟨h1, h2⟩ := hy.2 q hqS B hBq
  have h1' : w.valuation K (y : K) ≤ 1 := (hB _).1 (by simpa using h1)
  have h2' : w.valuation K ((y⁻¹ : Kˣ) : K) ≤ 1 := (hB _).1 (by simpa using h2)
  have hy0 : w.valuation K (y : K) ≠ 0 := (map_ne_zero _).2 y.ne_zero
  rw [Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ (lt_of_le_of_ne zero_le' hy0.symm)] at h2'
  exact le_antisymm h1' h2'

end ValOne
end A6b
end NumberField.LevelArith
end

noncomputable section
namespace NumberField
p2m_export "NumberField" "place SUnits.sUnits SUnits.mem_sUnits_iff SUnits.mem_sUnitsSubmodule SUnits.sUnitsRep existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one natCast_mem_asIdeal_of_forall_map_mem_iff_valuation_le_one exists_valuationSubring_forall_map_mem_iff_valuation_le_one"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField levelGal levelGal_apply_coe mem_placesOverPrimes_iff placesOverPrimesFinset mem_placesOverPrimesFinset IsSUnitMax sUnitsMaxStable sUnitsMaxStable_le smul_mem_sUnitsMaxStable sUnitsMaxRep sUnitsMaxRep.val sUnitsMaxRep.val_ρ sUnitsMaxStable_eq_sUnitsMax levelGal_surjective_and_ker"
p2m_open "NumberField.LevelArith NumberField"
namespace A6b
open IsDedekindDomain

local instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
local instance isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) := ⟨⟩

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (S : Finset Nat.Primes) (L F : IntermediateField ℚ Qbar) (hLF : L ≤ F)
  [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] [Normal ℚ F] [Normal ↥L ↥(levelField L F hLF)]

abbrev UF : Subgroup ↥L.fixingSubgroup := F.fixingSubgroup.comap L.fixingSubgroup.subtype
abbrev Inv := ((sUnitsMaxRep S L).quotientToInvariants (UF L F))
abbrev K' := ↥(levelField L F hLF)
abbrev SU := NumberField.SUnits.sUnitsRep ↥L (K' L F hLF) (placesOverPrimesFinset ↥L S)

include hLF in
lemma val_mem (x : Inv S L F) : ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : Qbarˣ) : Qbar) ∈ F := by
  have h : ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : Qbarˣ) : Qbar) ∈ IntermediateField.fixedField F.fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro γ hγ
    have hγL : γ ∈ L.fixingSubgroup := IntermediateField.fixingSubgroup_antitone hLF hγ
    have hinv := x.2 ⟨⟨γ, hγL⟩, hγ⟩
    have := congrArg (fun y : sUnitsMaxRep S L => ((sUnitsMaxRep.val S L y : Qbarˣ) : Qbar)) hinv
    simp [sUnitsMaxRep.val_ρ] at this
    exact this
  have hle : IntermediateField.fixedField F.fixingSubgroup ≤ F := (InfiniteGalois.fixedField_fixingSubgroup F).le
  exact hle h

lemma val_mem_levelField (x : Inv S L F) : ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : Qbarˣ) : Qbar) ∈ levelField L F hLF :=
  (IntermediateField.mem_extendScalars hLF).2 (val_mem S L F hLF x)

lemma val_inv_mem_levelField (x : Inv S L F) : ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : Qbarˣ) : Qbar)⁻¹ ∈ levelField L F hLF :=
  inv_mem (val_mem_levelField S L F hLF x)

def toUnit (x : Inv S L F) : (K' L F hLF)ˣ where
  val := ⟨_, val_mem_levelField S L F hLF x⟩
  inv := ⟨_, val_inv_mem_levelField S L F hLF x⟩
  val_inv := Subtype.ext (mul_inv_cancel₀ (Units.ne_zero _))
  inv_val := Subtype.ext (inv_mul_cancel₀ (Units.ne_zero _))

lemma coe_toUnit (x : Inv S L F) : (((toUnit S L F hLF x : (K' L F hLF)ˣ) : K' L F hLF) : Qbar) = sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) := rfl

end A6b
end NumberField.LevelArith
end

set_option linter.unusedSectionVars false
noncomputable section
namespace NumberField
p2m_export "NumberField" "place SUnits.sUnits SUnits.mem_sUnits_iff SUnits.mem_sUnitsSubmodule SUnits.sUnitsRep existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one natCast_mem_asIdeal_of_forall_map_mem_iff_valuation_le_one exists_valuationSubring_forall_map_mem_iff_valuation_le_one"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField levelGal levelGal_apply_coe mem_placesOverPrimes_iff placesOverPrimesFinset mem_placesOverPrimesFinset IsSUnitMax sUnitsMaxStable sUnitsMaxStable_le smul_mem_sUnitsMaxStable sUnitsMaxRep sUnitsMaxRep.val sUnitsMaxRep.val_ρ sUnitsMaxStable_eq_sUnitsMax levelGal_surjective_and_ker"
p2m_open "NumberField.LevelArith NumberField"
namespace A6b
open IsDedekindDomain

local instance isAlgebraicQbar' : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar' : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar' : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (S : Finset Nat.Primes) (L F : IntermediateField ℚ Qbar) (hLF : L ≤ F)
  [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] [Normal ℚ F] [Normal ↥L ↥(levelField L F hLF)]

lemma natCast_mem_under_iff (w : HeightOneSpectrum (𝓞 (K' L F hLF))) (p : ℕ) :
    ((p : ℕ) : 𝓞 ↥L) ∈ (w.under (𝓞 ↥L)).asIdeal ↔ ((p : ℕ) : 𝓞 (K' L F hLF)) ∈ w.asIdeal := by
  change ((p : ℕ) : 𝓞 ↥L) ∈ Ideal.comap (algebraMap (𝓞 ↥L) (𝓞 (K' L F hLF))) w.asIdeal ↔ _
  rw [Ideal.mem_comap, map_natCast]

lemma prime_notMem_of_under_notMem (w : HeightOneSpectrum (𝓞 (K' L F hLF))) (hw : w.under (𝓞 ↥L) ∉ placesOverPrimesFinset ↥L S)
    (q : Nat.Primes) (hq : ((q : ℕ) : 𝓞 (K' L F hLF)) ∈ w.asIdeal) : q ∉ S := by
  intro hqS
  apply hw
  rw [mem_placesOverPrimesFinset, mem_placesOverPrimes_iff]
  exact ⟨q, hqS, (natCast_mem_under_iff L F hLF w q).2 hq⟩

lemma under_notMem_of_prime (w : HeightOneSpectrum (𝓞 (K' L F hLF))) (q : Nat.Primes) (hq : ((q : ℕ) : 𝓞 (K' L F hLF)) ∈ w.asIdeal) (hqS : q ∉ S) :
    w.under (𝓞 ↥L) ∉ placesOverPrimesFinset ↥L S := by
  rw [mem_placesOverPrimesFinset, mem_placesOverPrimes_iff]
  rintro ⟨p, hpS, hp⟩
  rw [natCast_mem_under_iff] at hp
  have := prime_unique p.2 q.2 w hp hq
  exact hqS (by rwa [show p = q from Subtype.ext this] at hpS)

lemma isSUnitMax_smul_val (γ : ↥L.fixingSubgroup) (x : Inv S L F) :
    IsSUnitMax S ((γ : Γ) • sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L)) := by
  have := smul_mem_sUnitsMaxStable S L γ (x.1 : sUnitsMaxRep S L).2
  exact sUnitsMaxStable_le S L this

lemma toUnit_mem_sUnits (x : Inv S L F) :
    toUnit S L F hLF x ∈ NumberField.SUnits.sUnits ↥L (K' L F hLF) (placesOverPrimesFinset ↥L S) := by
  rw [NumberField.SUnits.mem_sUnits_iff]
  intro τ w hw
  obtain ⟨γ, rfl⟩ := (levelGal_surjective_and_ker L F hLF).1 τ
  obtain ⟨q, hq⟩ := exists_prime_natCast_mem w
  have hqS := prime_notMem_of_under_notMem S L F hLF w hw q hq

  let y : (K' L F hLF)ˣ := Units.map (levelGal L F hLF γ : K' L F hLF ≃ₐ[↥L] K' L F hLF).toMonoidHom (toUnit S L F hLF x)
  have hy : Units.map (algebraMap (K' L F hLF) Qbar : K' L F hLF →* Qbar) y = (γ : Γ) • sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) := by
    apply Units.ext
    change (((levelGal L F hLF γ (toUnit S L F hLF x : K' L F hLF)) : K' L F hLF) : Qbar) = (γ : Γ) (sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : Qbar)
    rw [levelGal_apply_coe]
    rfl
  have := valuation_eq_one_of_isSUnitMax S (algebraMap (K' L F hLF) Qbar) y (hy ▸ isSUnitMax_smul_val S L F γ x) w q hq hqS
  exact this

lemma isSUnitMax_of_mem_sUnits (hF : F.IsUnramifiedOutside S) (u : (K' L F hLF)ˣ)
    (hu : u ∈ NumberField.SUnits.sUnits ↥L (K' L F hLF) (placesOverPrimesFinset ↥L S)) :
    IsSUnitMax S (Units.map (algebraMap (K' L F hLF) Qbar : K' L F hLF →* Qbar) u) := by
  refine ⟨⟨F, hF, (IntermediateField.mem_extendScalars hLF).1 (u : K' L F hLF).2⟩, fun q hqS A hA => ?_⟩

  have hAq : A.valuation ((q : ℕ) : Qbar) < 1 := (ValuationSubring.mem_nonunits_iff A).1 hA
  have hq0 : ((q : ℕ) : Qbar) ≠ 0 := by exact_mod_cast q.2.ne_zero
  have hninv : (algebraMap (K' L F hLF) Qbar) (((q : ℕ) : K' L F hLF)⁻¹) ∉ A := by
    rw [map_inv₀, map_natCast]
    intro h
    have h' := (ValuationSubring.valuation_le_one_iff A _).2 h
    rw [map_inv₀, inv_le_one₀ (lt_of_le_of_ne zero_le' (Ne.symm ((map_ne_zero _).2 hq0)))] at h'
    exact absurd hAq (not_lt.2 h')
  obtain ⟨v, hv, -⟩ := NumberField.existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one (K' L F hLF)
    (algebraMap (K' L F hLF) Qbar) A ⟨_, hninv⟩

  have hvq : ((q : ℕ) : 𝓞 (K' L F hLF)) ∈ v.asIdeal := by
    have := NumberField.natCast_mem_asIdeal_of_forall_map_mem_iff_valuation_le_one (K' L F hLF) (algebraMap (K' L F hLF) Qbar) A v hv q
      (by rwa [map_natCast])
    simpa using this
  have hvS := under_notMem_of_prime S L F hLF v q hvq hqS
  have h1 := (NumberField.SUnits.mem_sUnits_iff ↥L (K' L F hLF) _ u).1 hu 1 v hvS
  rw [AlgEquiv.one_apply] at h1
  refine ⟨(hv _).2 h1.le, ?_⟩
  rw [Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe, ← map_inv₀]
  apply (hv _).2
  rw [map_inv₀, h1, inv_one]

end A6b
end NumberField.LevelArith
end

noncomputable section
namespace NumberField
p2m_export "NumberField" "place SUnits.sUnits SUnits.mem_sUnits_iff SUnits.mem_sUnitsSubmodule SUnits.sUnitsRep existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one natCast_mem_asIdeal_of_forall_map_mem_iff_valuation_le_one exists_valuationSubring_forall_map_mem_iff_valuation_le_one"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField levelGal levelGal_apply_coe mem_placesOverPrimes_iff placesOverPrimesFinset mem_placesOverPrimesFinset IsSUnitMax sUnitsMaxStable sUnitsMaxStable_le smul_mem_sUnitsMaxStable sUnitsMaxRep sUnitsMaxRep.val sUnitsMaxRep.val_ρ sUnitsMaxStable_eq_sUnitsMax levelGal_surjective_and_ker"
p2m_open "NumberField.LevelArith NumberField"
namespace A6b
open IsDedekindDomain

local instance isAlgebraicQbar'' : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar'' : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar'' : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (S : Finset Nat.Primes) (L F : IntermediateField ℚ Qbar) (hLF : L ≤ F)
  [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] [Normal ℚ F] [Normal ↥L ↥(levelField L F hLF)]

def fwd (x : Inv S L F) : SU S L F hLF :=
  ⟨Additive.ofMul (toUnit S L F hLF x), (NumberField.SUnits.mem_sUnitsSubmodule _ _ _ _).2 (toUnit_mem_sUnits S L F hLF x)⟩

abbrev sval (u : SU S L F hLF) : Qbarˣ := Units.map (algebraMap (K' L F hLF) Qbar : K' L F hLF →* Qbar) (Additive.toMul u.1)

lemma sval_injective : Function.Injective (sval S L F hLF) := by
  intro u v h
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Units.ext
  apply Subtype.ext
  exact congrArg (fun z : Qbarˣ => (z : Qbar)) h

lemma sval_fwd (x : Inv S L F) : sval S L F hLF (fwd S L F hLF x) = sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) := Units.ext rfl

lemma val_injective' : Function.Injective (fun x : Inv S L F => sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L)) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact Additive.toMul.injective h

def bwd (hF : F.IsUnramifiedOutside S) (u : SU S L F hLF) : Inv S L F :=
  ⟨⟨Additive.ofMul (sval S L F hLF u), by
      change Additive.toMul (Additive.ofMul (sval S L F hLF u)) ∈ sUnitsMaxStable S L
      rw [toMul_ofMul, sUnitsMaxStable_eq_sUnitsMax]
      exact isSUnitMax_of_mem_sUnits S L F hLF hF _ u.2⟩, by
      intro s
      apply Subtype.ext
      apply Additive.toMul.injective
      change ((s : ↥L.fixingSubgroup) : Γ) • sval S L F hLF u = sval S L F hLF u
      apply Units.ext
      change ((s : ↥L.fixingSubgroup) : Γ) (((Additive.toMul u.1 : (K' L F hLF)ˣ) : K' L F hLF) : Qbar) = _
      have hs : (((s : ↥L.fixingSubgroup) : Γ)) ∈ F.fixingSubgroup := s.2
      rw [IntermediateField.mem_fixingSubgroup_iff] at hs
      exact hs _ ((IntermediateField.mem_extendScalars hLF).1 (((Additive.toMul u.1 : (K' L F hLF)ˣ) : K' L F hLF)).2)⟩

lemma val_bwd (hF : F.IsUnramifiedOutside S) (u : SU S L F hLF) :
    sUnitsMaxRep.val S L ((bwd S L F hLF hF u).1 : sUnitsMaxRep S L) = sval S L F hLF u := rfl

def equiv (hF : F.IsUnramifiedOutside S) : Inv S L F ≃+ SU S L F hLF where
  toFun := fwd S L F hLF
  invFun := bwd S L F hLF hF
  left_inv x := val_injective' S L F (show sUnitsMaxRep.val S L ((bwd S L F hLF hF (fwd S L F hLF x)).1 : sUnitsMaxRep S L) = sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) by
    rw [val_bwd, sval_fwd])
  right_inv u := sval_injective S L F hLF (by rw [sval_fwd, val_bwd])
  map_add' x y := sval_injective S L F hLF (by
    rw [sval_fwd]
    change sUnitsMaxRep.val S L ((x.1 : sUnitsMaxRep S L) + (y.1 : sUnitsMaxRep S L)) = sval S L F hLF (fwd S L F hLF x + fwd S L F hLF y)
    change sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) * sUnitsMaxRep.val S L (y.1 : sUnitsMaxRep S L) =
      Units.map (algebraMap (K' L F hLF) Qbar : K' L F hLF →* Qbar) (toUnit S L F hLF x * toUnit S L F hLF y)
    rw [map_mul]
    exact (congrArg₂ (· * ·) (sval_fwd S L F hLF x) (sval_fwd S L F hLF y)).symm)

lemma equiv_apply (hF : F.IsUnramifiedOutside S) (x : Inv S L F) : equiv S L F hLF hF x = fwd S L F hLF x := rfl

lemma coe_equiv (hF : F.IsUnramifiedOutside S) (x : Inv S L F) :
    (((Additive.toMul ((equiv S L F hLF hF x).1) : (K' L F hLF)ˣ) : K' L F hLF) : Qbar) =
      ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : Qbarˣ) : Qbar) := rfl

lemma equiv_ρ (hF : F.IsUnramifiedOutside S) (g : ↥L.fixingSubgroup) (x : Inv S L F) :
    equiv S L F hLF hF ((Inv S L F).ρ (g : ↥L.fixingSubgroup ⧸ UF L F) x) = (SU S L F hLF).ρ (levelGal L F hLF g) (equiv S L F hLF hF x) := by
  apply sval_injective S L F hLF
  rw [equiv_apply, sval_fwd]
  apply Units.ext
  change ((sUnitsMaxRep.val S L ((sUnitsMaxRep S L).ρ g (x.1 : sUnitsMaxRep S L)) : Qbarˣ) : Qbar) =
    (((levelGal L F hLF g (toUnit S L F hLF x : K' L F hLF)) : K' L F hLF) : Qbar)
  rw [sUnitsMaxRep.val_ρ, levelGal_apply_coe]
  rfl

end A6b
end NumberField.LevelArith
end

open _root_.NumberField _root_.P2MW.S_NumberField_LevelArith_exists_addEquiv_quotientToInvariants_sUnitsMaxRep_sUnitsRep.NumberField _root_.NumberField.LevelArith _root_.P2MW.S_NumberField_LevelArith_exists_addEquiv_quotientToInvariants_sUnitsMaxRep_sUnitsRep.NumberField.LevelArith in
theorem solution
    (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] [Normal ℚ F] [Normal ↥L ↥(levelField L F hLF)] (hF : F.IsUnramifiedOutside S) :
    ∃ e : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))
        ≃+ (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)),
      (∀ x, (((Additive.toMul ((e x).1) : (↥(levelField L F hLF))ˣ) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ) =
        ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) ∧
      ∀ (g : ↥L.fixingSubgroup) (x),
        e (((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)).ρ
            (g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype) x) =
          (NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).ρ (levelGal L F hLF g) (e x) :=
  ⟨A6b.equiv S L F hLF hF, A6b.coe_equiv S L F hLF hF, A6b.equiv_ρ S L F hLF hF⟩

end S_NumberField_LevelArith_exists_addEquiv_quotientToInvariants_sUnitsMaxRep_sUnitsRep
end P2MW
export P2MW.S_NumberField_LevelArith_exists_addEquiv_quotientToInvariants_sUnitsMaxRep_sUnitsRep (solution)
