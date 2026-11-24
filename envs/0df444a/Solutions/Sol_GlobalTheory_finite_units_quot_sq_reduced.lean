-- Prove2me | solution 1 for GlobalTheory.finite_units_quot_sq_reduced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:07:26.92492+00:00
-- url     : https://prove2.me/submissions/cbe9c587-3d0c-4c36-aeb1-4d56fb78ad0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteUnitsQuotSqFiniteEtaleHermitianPair
import Theorems.Thm_GlobalTheory_finite_units_quot_sq_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (F : Type) [NontriviallyNormedField F] [CompleteSpace F]
    [ProperSpace F] [CharZero F] (K : Type) [CommRing K] [Algebra F K] [Module.Finite F K]
    [IsReduced K] : Finite (Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) := by
  classical
  have : IsArtinianRing K := IsArtinianRing.of_finite F K
  letI (I : MaximalSpectrum K) : Field (K ⧸ I.asIdeal) :=
    @Ideal.Quotient.field _ _ I.asIdeal I.isMaximal
  have hfin (I : MaximalSpectrum K) :
      Finite ((K ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (K ⧸ I.asIdeal)ˣ →* (K ⧸ I.asIdeal)ˣ).range) :=
    finite_units_quot_sq_field F (K ⧸ I.asIdeal)
  let φ : Kˣ →* ∀ I : MaximalSpectrum K,
      (K ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (K ⧸ I.asIdeal)ˣ →* (K ⧸ I.asIdeal)ˣ).range :=
    Pi.monoidHom fun I => (QuotientGroup.mk' _).comp
      (Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom)
  have hker : φ.ker = (powMonoidHom 2 : Kˣ →* Kˣ).range := by
    ext u
    simp only [MonoidHom.mem_ker, MonoidHom.mem_range, powMonoidHom_apply]
    constructor
    · intro hu
      have hI (I : MaximalSpectrum K) : ∃ s : (K ⧸ I.asIdeal)ˣ,
          s ^ 2 = Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom u := by
        have := congrFun hu I
        change ((Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom u : (K ⧸ I.asIdeal)ˣ) :
          (K ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (K ⧸ I.asIdeal)ˣ →* (K ⧸ I.asIdeal)ˣ).range) = 1 at this
        rw [QuotientGroup.eq_one_iff] at this
        obtain ⟨s, hs⟩ := this
        exact ⟨s, hs⟩
      choose s hs using hI
      let e := IsArtinianRing.equivPi K
      let x : K := e.symm fun I => (s I : K ⧸ I.asIdeal)
      let y : K := e.symm fun I => ((s I)⁻¹ : (K ⧸ I.asIdeal)ˣ)
      have hxy : x * y = 1 := e.injective (by
        rw [map_mul, map_one]
        funext I
        simp [x, y])
      refine ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, ?_⟩
      ext
      apply e.injective
      funext I
      have := congrArg Units.val (hs I)
      simp only [Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe] at this
      simp [x, this] <;> rfl
    · rintro ⟨w, rfl⟩
      funext I
      change ((Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom (w ^ 2) : (K ⧸ I.asIdeal)ˣ) :
        (K ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (K ⧸ I.asIdeal)ˣ →* (K ⧸ I.asIdeal)ˣ).range) = 1
      rw [QuotientGroup.eq_one_iff, map_pow]
      exact ⟨_, rfl⟩
  have := Finite.of_injective _ (QuotientGroup.kerLift_injective φ)
  rw [hker] at this
  exact this
end GlobalTheory
