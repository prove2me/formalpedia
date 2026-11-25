-- Prove2me | solution 1 for GlobalTheory.NormOneSplit.exists_forall_hom_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:12:01.068844+00:00
-- url     : https://prove2.me/submissions/c872a466-07a0-4a6c-b573-1983a229dbbe

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsForallHomEq
import Theorems.Thm_GlobalTheory_NormOneSplit_ker_isMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
open GlobalTheory GlobalTheory.NormOneSplit
open NumberField Module Matrix
open scoped ENNReal
namespace GlobalTheory.NormOneSplit
namespace _root_.GlobalTheory.NormOneSplit
theorem _root_.solution {R : Type} [CommRing R] {T : ℕ} [Fact T.Prime]
    [Finite (R →+* ZMod T)] (g : (R →+* ZMod T) → ZMod T) :
    ∃ x : R, ∀ φ : R →+* ZMod T, φ x = g φ := by
  classical
  have hcop : Pairwise (Function.onFun IsCoprime (fun φ : R →+* ZMod T => RingHom.ker φ)) := by
    intro φ ψ hne
    haveI := _root_.GlobalTheory.NormOneSplit.ker_isMaximal φ
    haveI := _root_.GlobalTheory.NormOneSplit.ker_isMaximal ψ
    exact Ideal.isCoprime_of_isMaximal (fun h => hne (ZMod.ringHom_eq_of_ker_eq φ ψ h))
  obtain ⟨y, hy⟩ := Ideal.quotientInfToPiQuotient_surj hcop
    (fun φ => Ideal.Quotient.mk (RingHom.ker φ) (((g φ).val : ℕ) : R))
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨x, fun φ => ?_⟩
  have h := congrFun hy φ
  rw [Ideal.quotientInfToPiQuotient_mk', Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero,
    map_natCast, ZMod.natCast_zmod_val] at h
  exact h
end _root_.GlobalTheory.NormOneSplit
end GlobalTheory.NormOneSplit
