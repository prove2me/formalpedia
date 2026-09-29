-- Prove2me | solution 1 for ModularCurve.XOneP.exists_ringHom_zmod_castHom_comp_eq_algebraMap_of_isCyclotomicExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/76678141-d00d-59bd-8cac-2bdb16ffe434

import Mathlib
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ModularCurve_XOneP_exists_intCast_sub_mem_maximalIdeal_of_isCyclotomicExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_ringHom_zmod_castHom_comp_eq_algebraMap_of_isCyclotomicExtension

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ResMap

variable (p : ℕ) [Fact p.Prime]
  (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
  (ζ : L) (hζ : IsPrimitiveRoot ζ p)
  (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
  (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)

include hζ hAp hζA in

theorem exists_ringEquiv_residueField :
    ∃ e : ZMod p ≃+* IsLocalRing.ResidueField A, True := by
  have hp : p.Prime := Fact.out

  have hp0 : (p : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]
    exact hAp
  haveI : CharP (IsLocalRing.ResidueField A) p := by
    have h := CharP.ringChar_of_prime_eq_zero hp hp0
    exact h ▸ ringChar.charP (IsLocalRing.ResidueField A)
  let ι : ZMod p →+* IsLocalRing.ResidueField A := ZMod.castHom (dvd_refl p) _
  refine ⟨RingEquiv.ofBijective ι ⟨ι.injective, fun x => ?_⟩, trivial⟩
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨n, hn⟩ := ModularCurve.XOneP.exists_intCast_sub_mem_maximalIdeal_of_isCyclotomicExtension p L ζ hζ A hAp hζA a
  refine ⟨(n : ZMod p), ?_⟩
  rw [map_intCast, ← map_intCast (IsLocalRing.residue A), eq_comm, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff]
  exact hn

omit [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L] [Algebra A L] [IsFractionRing A L] in
include hAp in

theorem ker_algebraMap_eq (hpA : (p : A) ≠ 0) (k : Type) [Field k] [CharP k p] [Algebra A k] :
    RingHom.ker (algebraMap A k) = IsLocalRing.maximalIdeal A := by
  have hp : p.Prime := Fact.out

  obtain ⟨P, -, huniq⟩ := ((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime A).mp ‹_›).2
  have h1 : RingHom.ker (algebraMap A k) ≠ ⊥ ∧ (RingHom.ker (algebraMap A k)).IsPrime := by
    refine ⟨fun h => hpA ?_, RingHom.ker_isPrime _⟩
    have : (p : A) ∈ RingHom.ker (algebraMap A k) := by
      rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
    rwa [h, Ideal.mem_bot] at this
  have h2 : IsLocalRing.maximalIdeal A ≠ ⊥ ∧ (IsLocalRing.maximalIdeal A).IsPrime :=
    ⟨fun h => hpA (by have := hAp; rwa [h, Ideal.mem_bot] at this), inferInstance⟩
  rw [huniq _ h1, huniq _ h2]

include hζ hAp hζA in
theorem main (k : Type) [Field k] [CharP k p] [Algebra A k] :
    ∃ r : A →+* ZMod p, (ZMod.castHom (dvd_refl p) k).comp r = algebraMap A k := by
  obtain ⟨e, -⟩ := exists_ringEquiv_residueField p L ζ hζ A hAp hζA
  have hp : p.Prime := Fact.out

  have hpA : (p : A) ≠ 0 := by
    intro h
    have : (p : L) = 0 := by rw [← map_natCast (algebraMap A L), h, map_zero]
    exact hp.ne_zero (Nat.cast_eq_zero.mp this)

  have hker : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A k a = 0 := fun a ha => by
    rw [← RingHom.mem_ker, ker_algebraMap_eq p A hAp hpA k]; exact ha
  let φ : IsLocalRing.ResidueField A →+* k := Ideal.Quotient.lift _ (algebraMap A k) hker
  have hφ : φ.comp (IsLocalRing.residue A) = algebraMap A k := Ideal.Quotient.lift_comp_mk _ _ _
  refine ⟨(e.symm : IsLocalRing.ResidueField A →+* ZMod p).comp (IsLocalRing.residue A), ?_⟩
  rw [← RingHom.comp_assoc, ← hφ]
  congr 1

  have : ((ZMod.castHom (dvd_refl p) k).comp (e.symm : IsLocalRing.ResidueField A →+* ZMod p)).comp
      (e : ZMod p →+* IsLocalRing.ResidueField A) = φ.comp (e : ZMod p →+* IsLocalRing.ResidueField A) :=
    Subsingleton.elim _ _
  have h := congrArg (fun f => f.comp (e.symm : IsLocalRing.ResidueField A →+* ZMod p)) this
  simp only [RingHom.comp_assoc] at h
  have he : (e : ZMod p →+* IsLocalRing.ResidueField A).comp (e.symm : IsLocalRing.ResidueField A →+* ZMod p) =
      RingHom.id _ := by ext x; simp
  rw [he, RingHom.comp_id, RingHom.comp_id] at h
  exact h

end ResMap

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (k : Type) [Field k] [CharP k p] [Algebra A k] :
    ∃ r : A →+* ZMod p, (ZMod.castHom (dvd_refl p) k).comp r = algebraMap A k :=
  ResMap.main p L ζ hζ A hAp hζA k

end S_ModularCurve_XOneP_exists_ringHom_zmod_castHom_comp_eq_algebraMap_of_isCyclotomicExtension
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_ringHom_zmod_castHom_comp_eq_algebraMap_of_isCyclotomicExtension (solution)
