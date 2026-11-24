-- Prove2me | solution 1 for GlobalTheory.RowLev.extId_principal_and_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:02:46.394662+00:00
-- url     : https://prove2.me/submissions/6d5be25c-9c17-49bf-b2a8-d0b683d4d9d8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegralAdeleIdealOfIdealPrincipalAndInter
import Theorems.Thm_GlobalTheory_RowLev_exists_map_psi_eq_span
import Theorems.Thm_GlobalTheory_RowLev_psi_mem_map_iff
import Theorems.Thm_GlobalTheory_RowLev_extId_eq_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.RowLev
open Formalism.UG Formalism.UG.P Inhab
namespace GlobalTheory.RowLev
theorem _root_.solution : ∀ (I : AutInst) (𝔞 : Ideal (𝓞 I.E)), 𝔞 ≠ ⊥ → (∃ t : IntAf I.F I.E, IsUnit (t : (I.E ⊗[I.F] Af I.F)) ∧ extId I 𝔞 = Ideal.span {t}) ∧ ∀ (a : 𝓞 I.E) (h : Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E) ∈ IntAf I.F I.E), (⟨_, h⟩ : IntAf I.F I.E) ∈ extId I 𝔞 ↔ a ∈ 𝔞 := by
  intro I 𝔞 h𝔞
  rw [extId_eq_map]
  exact ⟨exists_map_psi_eq_span 𝔞 h𝔞, fun a _ => psi_mem_map_iff 𝔞 h𝔞 a⟩
end GlobalTheory.RowLev
