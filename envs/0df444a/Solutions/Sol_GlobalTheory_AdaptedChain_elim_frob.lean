-- Prove2me | solution 1 for GlobalTheory.AdaptedChain.elim_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:35:05.364626+00:00
-- url     : https://prove2.me/submissions/77ad9450-2214-41b1-be1e-206528a57fd7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Theorems.Thm_GlobalTheory_AdaptedChain_frob_sum
import Theorems.Thm_GlobalTheory_AdaptedChain_int_of_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_neg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.AdaptedChain
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
namespace GlobalTheory.AdaptedChain
theorem _root_.solution [IsAlgClosed C] {M : Type} (Q : Finset I) (w : I → M → C)
    (hw : ∀ x e, V.Ge 0 (w x e)) (E : Finset M) (k : ℕ) :
    ∃ (P : Matrix I I C) (Q' : Finset I), admitted V Q P ∧ Q' ⊆ Q ∧
    Q.card ≤ Q'.card + E.card ∧ ∀ c ∈ Q', ∀ e ∈ E, V.Ge 1 (∑ x, P c x ^ (V.l ^ k) * w x e) := by
  have hpos : 0 < V.l ^ k := pow_pos V.l_prime.pos k
  choose r hr using fun x e => IsAlgClosed.exists_pow_nat_eq (w x e) hpos
  obtain ⟨P, Q', hP, h1, h2, h3⟩ := elim (V := V) Q r E
  refine ⟨P, Q', hP, h1, h2, fun c hc e he => ?_⟩
  have := (frob_sum (V := V) Finset.univ (fun x => P c x * r x e)
    (fun x => (hP.1 c x).mul_int (int_of_pow hpos.ne' (by rw [hr]; exact hw x e))) k).neg
  rw [h3 c hc e he, zero_pow hpos.ne'] at this
  simpa [mul_pow, hr] using this
end GlobalTheory.AdaptedChain
