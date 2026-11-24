-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.exists_fieldIdem_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:52:03.687813+00:00
-- url     : https://prove2.me/submissions/2d6df90d-a32c-49a8-b08e-a169d11e3493

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfSeparableMarkedCharpoly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvolutionIdempotentDecompositionOfSeparableChar
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_FieldIdem_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open Classical
variable {R : Type} [CommRing R]
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution [IsReduced R] [IsArtinianRing R] :
    ∃ (M : Type) (_ : Fintype M) (f : M → R), CompleteOrthogonalIdempotents f ∧ ∀ m, FieldIdem (f m) := by

  let φ := IsArtinianRing.equivPi R
  have : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  have hc : CompleteOrthogonalIdempotents (fun m : MaximalSpectrum R => φ.symm (Pi.single m 1)) :=
    (CompleteOrthogonalIdempotents.single (fun I : MaximalSpectrum R => R ⧸ I.asIdeal)).map
      φ.symm.toRingEquiv.toRingHom
  refine ⟨MaximalSpectrum R, inferInstance, fun m => φ.symm (Pi.single m 1), hc, fun m => ?_⟩
  refine ⟨hc.idem m, ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun x => φ x m) h0
    simp only [AlgEquiv.apply_symm_apply, map_zero, Pi.single_eq_same, Pi.zero_apply] at h1
    exact one_ne_zero h1
  · intro y hy
    have ha : φ y m ≠ 0 := by
      intro h0
      apply hy
      apply φ.injective
      rw [map_mul, AlgEquiv.apply_symm_apply, map_zero]
      funext j
      rw [Pi.mul_apply, Pi.zero_apply]
      by_cases hj : j = m
      · subst hj
        rw [Pi.single_eq_same, one_mul]
        exact h0
      · simp only [Pi.single_eq_of_ne hj, zero_mul]
    obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv ha
    refine ⟨φ.symm (Pi.single m b), ?_⟩
    apply φ.injective
    rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    funext j
    rw [Pi.mul_apply, Pi.mul_apply]
    by_cases hj : j = m
    · subst hj
      rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
      exact hb
    · simp only [Pi.single_eq_of_ne hj, zero_mul]
end GlobalTheory.UnitLemma.Desc
