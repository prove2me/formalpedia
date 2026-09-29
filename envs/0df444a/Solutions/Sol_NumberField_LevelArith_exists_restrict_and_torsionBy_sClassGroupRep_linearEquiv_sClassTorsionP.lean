-- Prove2me | solution 1 for NumberField.LevelArith.exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/db0ec8e2-f767-5432-b140-3608d92a5232

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Theorems.Thm_NumberField_LevelArith_sPrimeClasses_eq_closure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain"
open scoped Classical NumberField NumberField.LevelArith TensorProduct Pointwise

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false
set_option linter.unusedSectionVars false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain NumberField"
open scoped Classical NumberField NumberField.LevelArith TensorProduct Pointwise

namespace PairTransportCl

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (K L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
  (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]

noncomputable def γL (γ : ↥K.fixingSubgroup) : ↥L ≃+* ↥L :=
  (levelFieldEquiv K L hKL).trans (((levelGal K L hKL γ : ↥(levelField K L hKL) ≃ₐ[↥K] ↥(levelField K L hKL)).toRingEquiv).trans
    (levelFieldEquiv K L hKL).symm)

lemma coe_γL (γ : ↥K.fixingSubgroup) (y : ↥L) : ((γL K L hKL γ y : ↥L) : Qbar) = (γ : Γ) (y : Qbar) := by
  show (((levelFieldEquiv K L hKL).symm ((levelGal K L hKL γ) (levelFieldEquiv K L hKL y)) : ↥L) : Qbar) = _
  rw [coe_levelFieldEquiv_symm, levelGal_apply_coe, coe_levelFieldEquiv]

noncomputable def τL (γ : ↥K.fixingSubgroup) : ↥L ≃ₐ[ℚ] ↥L :=
  AlgEquiv.ofRingEquiv (f := γL K L hKL γ) fun q => by
    apply Subtype.ext
    rw [coe_γL]
    show (γ : Γ) (algebraMap ℚ Qbar q) = algebraMap ℚ Qbar q
    exact AlgEquiv.commutes _ q

lemma coe_τL (γ : ↥K.fixingSubgroup) (y : ↥L) : ((τL K L hKL γ y : ↥L) : Qbar) = (γ : Γ) (y : Qbar) := coe_γL K L hKL γ y

noncomputable def τ : ↥K.fixingSubgroup →* (↥L ≃ₐ[ℚ] ↥L) where
  toFun := τL K L hKL
  map_one' := AlgEquiv.ext fun y => Subtype.ext (by rw [coe_τL]; rfl)
  map_mul' γ γ' := AlgEquiv.ext fun y => Subtype.ext (by
    rw [coe_τL, AlgEquiv.mul_apply, coe_τL, coe_τL]; rfl)

lemma τ_apply (γ : ↥K.fixingSubgroup) : τ K L hKL γ = τL K L hKL γ := rfl

lemma τ_spec (γ : ↥K.fixingSubgroup) (y : ↥L) : (γ : Γ) (y : Qbar) = ((τ K L hKL γ y : ↥L) : Qbar) := (coe_τL K L hKL γ y).symm

noncomputable def eO : 𝓞 ↥L ≃+* 𝓞 ↥(levelField K L hKL) := NumberField.RingOfIntegers.mapRingEquiv (levelFieldEquiv K L hKL)

lemma coe_eO (y : 𝓞 ↥L) : (((eO K L hKL y : 𝓞 ↥(levelField K L hKL)) : ↥(levelField K L hKL)) : Qbar) = ((y : ↥L) : Qbar) := rfl

noncomputable def placeEquiv : HeightOneSpectrum (𝓞 ↥L) ≃ HeightOneSpectrum (𝓞 ↥(levelField K L hKL)) :=
  HeightOneSpectrum.equivOfRingEquiv (eO K L hKL)

lemma placeEquiv_asIdeal (w : HeightOneSpectrum (𝓞 ↥L)) :
    (placeEquiv K L hKL w).asIdeal = Ideal.map (eO K L hKL) w.asIdeal := by
  rw [← Ideal.comap_symm]; rfl

lemma mem_placesOverPrimes_placeEquiv_iff (S : Set Nat.Primes) (w : HeightOneSpectrum (𝓞 ↥L)) :
    placeEquiv K L hKL w ∈ placesOverPrimes ↥(levelField K L hKL) S ↔ w ∈ placesOverPrimes ↥L S := by
  rw [mem_placesOverPrimes_iff, mem_placesOverPrimes_iff]
  refine exists_congr fun q => and_congr_right fun _ => ?_
  show (eO K L hKL).symm _ ∈ w.asIdeal ↔ _
  rw [map_natCast]

noncomputable def Φ₀ : ClassGroup (𝓞 ↥L) ≃* ClassGroup (𝓞 ↥(levelField K L hKL)) := ClassGroup.mulEquiv (eO K L hKL)

lemma Φ₀_primeClass (w : HeightOneSpectrum (𝓞 ↥L)) :
    Φ₀ K L hKL (primeClass ↥L w) = primeClass ↥(levelField K L hKL) (placeEquiv K L hKL w) := by
  rw [Φ₀, primeClass, ClassGroup.mulEquiv_mk0, primeClass]
  congr 1
  apply Subtype.ext
  show Ideal.map (eO K L hKL : 𝓞 ↥L →+* 𝓞 ↥(levelField K L hKL)) w.asIdeal = (placeEquiv K L hKL w).asIdeal
  rw [placeEquiv_asIdeal]
  rfl

lemma Φ₀_image (S : Set Nat.Primes) :
    (Φ₀ K L hKL) '' (primeClass ↥L '' placesOverPrimes ↥L S) =
      primeClass ↥(levelField K L hKL) '' placesOverPrimes ↥(levelField K L hKL) S := by
  ext c
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨placeEquiv K L hKL w, (mem_placesOverPrimes_placeEquiv_iff K L hKL S w).2 hw, (Φ₀_primeClass K L hKL w).symm⟩
  · rintro ⟨w', hw', rfl⟩
    obtain ⟨w, rfl⟩ := (placeEquiv K L hKL).surjective w'
    exact ⟨_, ⟨w, (mem_placesOverPrimes_placeEquiv_iff K L hKL S w).1 hw', rfl⟩, Φ₀_primeClass K L hKL w⟩

lemma Φ₀_map_sPrimeClasses (S : Set Nat.Primes) :
    (sPrimeClasses ↥L ↥L S).map (Φ₀ K L hKL).toMonoidHom = sPrimeClasses ↥K ↥(levelField K L hKL) S := by
  rw [NumberField.LevelArith.sPrimeClasses_eq_closure, NumberField.LevelArith.sPrimeClasses_eq_closure, MonoidHom.map_closure]
  congr 1
  exact Φ₀_image K L hKL S

lemma mem_sPrimeClasses_iff_Φ₀ (S : Set Nat.Primes) (c : ClassGroup (𝓞 ↥L)) :
    c ∈ sPrimeClasses ↥L ↥L S ↔ Φ₀ K L hKL c ∈ sPrimeClasses ↥K ↥(levelField K L hKL) S := by
  rw [← Φ₀_map_sPrimeClasses K L hKL S, Subgroup.mem_map]
  constructor
  · intro h; exact ⟨c, h, rfl⟩
  · rintro ⟨c', h, hc'⟩
    rwa [← (Φ₀ K L hKL).injective hc']

end PairTransportCl

namespace PairTransportCl

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (K L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
  (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)] (S : Set Nat.Primes)

noncomputable def Φ₁ : Additive (ClassGroup (𝓞 ↥L)) ≃ₗ[ℤ] Additive (ClassGroup (𝓞 ↥(levelField K L hKL))) :=
  (MulEquiv.toAdditive (Φ₀ K L hKL)).toIntLinearEquiv

lemma Φ₁_apply (x : Additive (ClassGroup (𝓞 ↥L))) : Φ₁ K L hKL x = Additive.ofMul (Φ₀ K L hKL (Additive.toMul x)) := rfl

lemma map_sPrimeClassesSubmodule :
    (sPrimeClassesSubmodule ↥L ↥L S).map (Φ₁ K L hKL).toLinearMap = sPrimeClassesSubmodule ↥K ↥(levelField K L hKL) S := by
  ext y
  rw [Submodule.mem_map, mem_sPrimeClassesSubmodule]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_sPrimeClassesSubmodule, mem_sPrimeClasses_iff_Φ₀ K L hKL] at hx
    exact hx
  · intro hy
    refine ⟨(Φ₁ K L hKL).symm y, ?_, LinearEquiv.apply_symm_apply _ _⟩
    rw [mem_sPrimeClassesSubmodule, mem_sPrimeClasses_iff_Φ₀ K L hKL]
    have : Φ₀ K L hKL (Additive.toMul ((Φ₁ K L hKL).symm y)) = Additive.toMul y := by
      have h := LinearEquiv.apply_symm_apply (Φ₁ K L hKL) y
      rw [Φ₁_apply] at h
      exact congrArg Additive.toMul h
    rw [this]; exact hy

noncomputable def Φ₂ : sClassGroupRep ↥L ↥L S ≃ₗ[ℤ] sClassGroupRep ↥K ↥(levelField K L hKL) S :=
  Submodule.Quotient.equiv (sPrimeClassesSubmodule ↥L ↥L S) (sPrimeClassesSubmodule ↥K ↥(levelField K L hKL) S) (Φ₁ K L hKL)
    (map_sPrimeClassesSubmodule K L hKL S)

lemma Φ₂_mk (c : ClassGroup (𝓞 ↥L)) :
    Φ₂ K L hKL S (Submodule.Quotient.mk (Additive.ofMul c)) = Submodule.Quotient.mk (Additive.ofMul (Φ₀ K L hKL c)) := rfl

variable (p : ℕ) [Fact p.Prime]

lemma map_torsionBy :
    (Submodule.torsionBy ℤ (sClassGroupRep ↥L ↥L S) (p : ℤ)).map (Φ₂ K L hKL S).toLinearMap =
      Submodule.torsionBy ℤ (sClassGroupRep ↥K ↥(levelField K L hKL) S) (p : ℤ) := by
  ext y
  rw [Submodule.mem_map, Submodule.mem_torsionBy_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Submodule.mem_torsionBy_iff] at hx
    rw [LinearEquiv.coe_coe, ← map_smul, hx, map_zero]
  · intro hy
    refine ⟨(Φ₂ K L hKL S).symm y, ?_, LinearEquiv.apply_symm_apply _ _⟩
    rw [Submodule.mem_torsionBy_iff, ← map_smul, hy, map_zero]

noncomputable def Φ₃ : ↥(Submodule.torsionBy ℤ (sClassGroupRep ↥L ↥L S) (p : ℤ)) ≃ₗ[ℤ]
    ↥(Submodule.torsionBy ℤ (sClassGroupRep ↥K ↥(levelField K L hKL) S) (p : ℤ)) :=
  LinearEquiv.ofSubmodules (Φ₂ K L hKL S) _ _ (map_torsionBy K L hKL S p)

lemma coe_Φ₃ (x : ↥(Submodule.torsionBy ℤ (sClassGroupRep ↥L ↥L S) (p : ℤ))) :
    ((Φ₃ K L hKL S p x : ↥(Submodule.torsionBy ℤ (sClassGroupRep ↥K ↥(levelField K L hKL) S) (p : ℤ))) :
      sClassGroupRep ↥K ↥(levelField K L hKL) S) = Φ₂ K L hKL S x := rfl

end PairTransportCl

namespace PairTransportCl

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (K L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
  (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)] (S : Set Nat.Primes) (p : ℕ) [Fact p.Prime]

noncomputable def eT : ↥(Submodule.torsionBy ℤ (sClassGroupRep ↥L ↥L S) (p : ℤ)) ≃ₗ[ZMod p]
    ↥(Submodule.torsionBy ℤ (sClassGroupRep ↥K ↥(levelField K L hKL) S) (p : ℤ)) :=
  LinearEquiv.ofLinear ((Φ₃ K L hKL S p).toLinearMap.toAddMonoidHom.toZModLinearMap p)
    ((Φ₃ K L hKL S p).symm.toLinearMap.toAddMonoidHom.toZModLinearMap p)
    (LinearMap.ext fun x => (Φ₃ K L hKL S p).apply_symm_apply x)
    (LinearMap.ext fun x => (Φ₃ K L hKL S p).symm_apply_apply x)

lemma coe_eT (x : ↥(Submodule.torsionBy ℤ (sClassGroupRep ↥L ↥L S) (p : ℤ))) :
    ((eT K L hKL S p x : ↥(Submodule.torsionBy ℤ (sClassGroupRep ↥K ↥(levelField K L hKL) S) (p : ℤ))) :
      sClassGroupRep ↥K ↥(levelField K L hKL) S) = Φ₂ K L hKL S x := rfl

lemma ringOfIntegersAut_comm (γ : ↥K.fixingSubgroup) :
    (ringOfIntegersAut ℚ ↥L (τ K L hKL γ)).trans (eO K L hKL) =
      (eO K L hKL).trans (ringOfIntegersAut ↥K ↥(levelField K L hKL) (levelGal K L hKL γ)) := by
  apply RingEquiv.ext; intro y
  apply Subtype.ext; apply Subtype.ext
  show ((τ K L hKL γ (y : ↥L) : ↥L) : Qbar) = (((levelGal K L hKL γ) ((eO K L hKL y : 𝓞 ↥(levelField K L hKL)) : ↥(levelField K L hKL))) : Qbar)
  rw [levelGal_apply_coe, coe_eO, ← τ_spec]

lemma Φ₀_classGroupAut (γ : ↥K.fixingSubgroup) (c : ClassGroup (𝓞 ↥L)) :
    Φ₀ K L hKL (classGroupAut ℚ ↥L (τ K L hKL γ) c) =
      ClassGroup.mulEquiv (ringOfIntegersAut ↥K ↥(levelField K L hKL) (levelGal K L hKL γ)) (Φ₀ K L hKL c) := by
  show ClassGroup.mulEquiv (eO K L hKL) (ClassGroup.mulEquiv (ringOfIntegersAut ℚ ↥L (τ K L hKL γ)) c) = _
  rw [← ClassGroup.mulEquiv_trans_apply, ringOfIntegersAut_comm, ClassGroup.mulEquiv_trans_apply]
  rfl

end PairTransportCl

open PairTransportCl in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)] (hnorm : IsNormalLevel K L) :
    ∃ (τ : ↥K.fixingSubgroup →* (↥L ≃ₐ[ℚ] ↥L)) (_ : ∀ (γ : ↥K.fixingSubgroup) (y : ↥L), (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (y : AlgebraicClosure ℚ) = ((τ γ y : ↥L) : AlgebraicClosure ℚ))
      (e : ↥(Submodule.torsionBy ℤ (sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) (p : ℤ)) ≃ₗ[ZMod p] sClassTorsionP K L hKL S p),
      ∀ (γ : ↥K.fixingSubgroup) (x x' : ↥(Submodule.torsionBy ℤ (sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) (p : ℤ))) (c : ClassGroup (𝓞 ↥L)),
        (x : sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) = Submodule.Quotient.mk (Additive.ofMul c) →
        (x' : sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) = Submodule.Quotient.mk (Additive.ofMul (classGroupAut ℚ ↥L (τ γ) c)) →
          e x' = (sClassTorsionP K L hKL S p).ρ γ (e x) := by
  refine ⟨τ K L hKL, τ_spec K L hKL, eT K L hKL (S : Set Nat.Primes) p, fun γ x x' c hx hx' => ?_⟩
  apply Subtype.ext
  show Φ₂ K L hKL (S : Set Nat.Primes) x'.1 =
    (((torsionP p (sClassGroupRep ↥K ↥(levelField K L hKL) (S : Set Nat.Primes)).ρ (levelGal K L hKL γ))
      (eT K L hKL (S : Set Nat.Primes) p x) : ↥(Submodule.torsionBy ℤ _ (p : ℤ))) : sClassGroupRep ↥K ↥(levelField K L hKL) (S : Set Nat.Primes))
  rw [torsionP_apply_coe]
  show Φ₂ K L hKL (S : Set Nat.Primes) x'.1 =
    (sClassGroupRep ↥K ↥(levelField K L hKL) (S : Set Nat.Primes)).ρ (levelGal K L hKL γ) (Φ₂ K L hKL (S : Set Nat.Primes) x.1)
  rw [hx', hx]
  exact (Φ₂_mk K L hKL (S : Set Nat.Primes) _).trans
    ((congrArg (fun d => (Submodule.Quotient.mk (Additive.ofMul d) : sClassGroupRep ↥K ↥(levelField K L hKL) (S : Set Nat.Primes)))
      (Φ₀_classGroupAut K L hKL γ c)).trans
      (congrArg ((sClassGroupRep ↥K ↥(levelField K L hKL) (S : Set Nat.Primes)).ρ (levelGal K L hKL γ))
        (Φ₂_mk K L hKL (S : Set Nat.Primes) c).symm))

end S_NumberField_LevelArith_exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP
end P2MW
export P2MW.S_NumberField_LevelArith_exists_restrict_and_torsionBy_sClassGroupRep_linearEquiv_sClassTorsionP (solution)
