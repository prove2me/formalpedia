-- Prove2me | solution 1 for GlobalTheory.ChebCross.irreducible_of_onto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:10:51.42273+00:00
-- url     : https://prove2.me/submissions/e6ff5012-8dc3-4497-957a-f3602230c5d0

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
theorem _root_.solution [CharZero Ω] (Z : IntermediateField F Ω) {m : ℕ}
    [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m)
    (h : ∀ j : (ZMod m)ˣ, ∃ u : Ω ≃ₐ[F] Ω, u ∈ Z.fixingSubgroup ∧ hζ.autToPow F u = j) :
    Irreducible (cyclotomic m Z) := by
  classical
  haveI : CharZero Z := (algebraMap Z Ω).charZero
  have hm : 0 < m := NeZero.pos m
  have h0 : aeval ζ (cyclotomic m Z) = 0 := by
    rw [aeval_def, ← eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hm
  have hint : IsIntegral Z ζ := ⟨_, cyclotomic.monic m Z, h0⟩
  have hdvd := minpoly.dvd Z ζ h0
  have hsub : primitiveRoots m Ω ⊆ ((minpoly Z ζ).aroots Ω).toFinset := by
    intro μ hμ
    rw [mem_primitiveRoots hm] at hμ
    obtain ⟨i, hi, hic, rfl⟩ := (hζ.isPrimitiveRoot_iff).1 hμ
    obtain ⟨u, hu, hj⟩ := h (ZMod.unitOfCoprime i hic)
    rw [autToPow_eq_iff, ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt hi] at hj
    rw [Multiset.mem_toFinset, mem_aroots]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    let v : Ω ≃ₐ[Z] Ω := Z.fixingSubgroupEquiv ⟨u, hu⟩
    have hv : v ζ = ζ ^ i := hj
    rw [← hv, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hdeg : (cyclotomic m Z).natDegree ≤ (minpoly Z ζ).natDegree := by
    rw [natDegree_cyclotomic, ← hζ.card_primitiveRoots]
    refine (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans ?_)
    refine (card_roots' _).trans ?_
    exact natDegree_map_le
  have := eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic m Z) hdvd hdeg
  rw [this]
  exact minpoly.irreducible hint
end GlobalTheory.ChebCross
