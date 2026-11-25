-- Prove2me | solution 1 for GlobalTheory.exists_padicInt_algebra_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:50:46.989813+00:00
-- url     : https://prove2.me/submissions/7a0648c7-0a00-45b4-8a57-98b647d3d43d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NonemptyPadicIntRingHomOfIsAdicComplete
import Theorems.Thm_GlobalTheory_nonempty_padicInt_ringHom_of_isAdicComplete
import Theorems.Thm_GlobalTheory_finite_of_forall_prime_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
open IsLocalRing
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (V : Type*) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V]
    [Finite (ResidueField V)] :
    ∃ (p : ℕ) (_ : Fact p.Prime) (_ : Algebra ℤ_[p] V), Module.Finite ℤ_[p] V := by
  obtain ⟨q, hq⟩ := CharP.exists (ResidueField V)
  have hprime : q.Prime := CharP.char_is_prime (ResidueField V) q
  haveI hfact : Fact q.Prime := ⟨hprime⟩
  have hmem : (q : V) ∈ maximalIdeal V := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ q
  obtain ⟨φ⟩ := _root_.GlobalTheory.nonempty_padicInt_ringHom_of_isAdicComplete (maximalIdeal V) q hmem
  letI : Algebra ℤ_[q] V := φ.toAlgebra
  refine ⟨q, hfact, this, ?_⟩
  haveI : Finite (V ⧸ maximalIdeal V) := ‹Finite (ResidueField V)›
  have hne : (q : V) ≠ 0 := Nat.cast_ne_zero.mpr hprime.ne_zero
  have himage : algebraMap ℤ_[q] V (q : ℤ_[q]) = (q : V) := map_natCast _ q
  refine _root_.GlobalTheory.finite_of_forall_prime_mem hne ?_ ?_ ?_
  · intro P hP hPne
    have hmax : P.IsMaximal := hP.isMaximal hPne
    rw [IsLocalRing.eq_maximalIdeal hmax]
    exact hmem
  · intro hbot
    apply hne
    rw [← himage, ← Ideal.mem_bot, ← hbot]
    apply Ideal.mem_map_of_mem
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  · apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal V).ne_top
    rw [Ideal.map_le_iff_le_comap, PadicInt.maximalIdeal_eq_span_p, Ideal.span_le,
      Set.singleton_subset_iff]
    change algebraMap ℤ_[q] V (q : ℤ_[q]) ∈ maximalIdeal V
    rw [himage]
    exact hmem
end _root_.GlobalTheory
end GlobalTheory
