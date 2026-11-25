-- Prove2me | solution 1 for GlobalTheory.SemilinearNullity.IndepOn.indepMod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:37:13.101874+00:00
-- url     : https://prove2.me/submissions/e8159e02-305a-484c-8f93-be8d7eb671a2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowerSemilinearRankNullityModMaxIdeal
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open GlobalTheory GlobalTheory.SemilinearNullity
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.SemilinearNullity
namespace IndepOn
theorem _root_.solution {m : ℕ} {σ : Type} {Y : Fin m → σ → C} {T : Finset (Fin m)}
    (h : IndepOn V Y T) {N : ℕ} (f : Fin N ↪ Fin m) (hf : ∀ ν, f ν ∈ T) :
    IndepMod V (fun ν => Y (f ν)) := by
  intro c hc hs ν
  have key := h (fun δ => ∑ ν, if f ν = δ then c ν else 0) (fun δ => VF.Ge.sum fun ν _ => by
      split_ifs
      · exact hc ν
      · exact VF.Ge.zero 0)
    (fun δ hδ => Finset.sum_eq_zero fun ν _ => if_neg (by rintro rfl; exact hδ (hf ν)))
    (fun s => by
      convert hs s using 1
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ν _ => ?_
      simp) (f ν)
  simpa using key
end IndepOn
end GlobalTheory.SemilinearNullity
