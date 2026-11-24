-- Prove2me | solution 1 for GlobalTheory.ChebCross.exists_fixing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:10:49.09874+00:00
-- url     : https://prove2.me/submissions/083a73c2-8f94-4998-b7b8-c8ad8ef93980

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicCrossingFieldDecidingFrobenius
import Theorems.Thm_GlobalTheory_ChebCross_autToPow_eq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.ChebCross
variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
namespace GlobalTheory.ChebCross
theorem _root_.solution [CharZero Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω) {m : ℕ}
    [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m) (hirr : Irreducible (cyclotomic m L))
    (j : (ZMod m)ˣ) : ∃ u : Ω ≃ₐ[F] Ω, u ∈ L.fixingSubgroup ∧ hζ.autToPow F u = j := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := F) L
  haveI : IsAlgClosure L Ω := ⟨inferInstance, inferInstance⟩
  haveI : CharZero L := (algebraMap L Ω).charZero
  have hj : IsPrimitiveRoot (ζ ^ (j : ZMod m).val) m :=
    hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime j)
  have h1 : minpoly L (ζ ^ (j : ZMod m).val) = minpoly L ζ := by
    rw [← hζ.minpoly_eq_cyclotomic_of_irreducible hirr,
      ← hj.minpoly_eq_cyclotomic_of_irreducible hirr]
  obtain ⟨u, hu⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := L) Ω).1 h1
  refine ⟨u.restrictScalars F, ?_, ?_⟩
  · rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact u.commutes ⟨x, hx⟩
  · rw [autToPow_eq_iff]
    exact hu
end GlobalTheory.ChebCross
