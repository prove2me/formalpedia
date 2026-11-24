-- Prove2me | solution 1 for GlobalTheory.FlagDim.dim_add_card_flagVar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:28:22.486119+00:00
-- url     : https://prove2.me/submissions/c3bd6e98-65f4-4b5e-9f5a-ec9c32b51f1c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FnTrdegOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_DimAddCardFlagVar
import Theorems.Thm_GlobalTheory_FlagDim_card_pairs_lt
import Theorems.Thm_GlobalTheory_PeriodCoord_card_cmType


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.FlagDim
open NumberField
namespace GlobalTheory.FlagDim
namespace _root_.GlobalTheory.FlagDim
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H), Dw.dim + Nat.card (_root_.Formalism.L2.Pj.FlagVar Dw) = Module.finrank ℚ E / 2 * (Dw.p * Dw.q + Dw.p * (Dw.p - 1) / 2 + Dw.q * (Dw.q - 1) / 2) := by
  intro E _ _ _ H Dw
  classical
  have hcard : Nat.card (_root_.Formalism.L2.Pj.FlagVar Dw) = ∑ τ : E →+* ℂ, Dw.mult τ * (Dw.mult τ - 1) / 2 := by
    show Nat.card ((τ : E →+* ℂ) × {p : Fin (Dw.mult τ) × Fin (Dw.mult τ) // p.1 < p.2}) = _
    rw [Nat.card_sigma]
    simp only [_root_.GlobalTheory.FlagDim.card_pairs_lt]
  have hdim : Dw.dim = Module.finrank ℚ E / 2 * Dw.p * Dw.q := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.dim; rfl
  have hall : Fintype.card (E →+* ℂ) = Module.finrank ℚ E := Embeddings.card E ℂ
  have hcm : (Finset.univ.filter fun τ : E →+* ℂ => τ H.rt = H.rt0).card = Module.finrank ℚ E / 2 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, _root_.GlobalTheory.PeriodCoord.card_cmType]
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (fun τ : E →+* ℂ => τ H.rt = H.rt0)
  obtain ⟨k, hk⟩ : Even (Module.finrank ℚ E) := by
    rw [IsTotallyComplex.finrank]; exact even_two_mul _
  rw [Finset.card_univ, hall] at hsplit
  have hk2 : Module.finrank ℚ E / 2 = k := by omega
  have hnot : (Finset.univ.filter fun τ : E →+* ℂ => ¬ τ H.rt = H.rt0).card = k := by omega
  have hterm : ∀ τ : E →+* ℂ, Dw.mult τ * (Dw.mult τ - 1) / 2 =
      if τ H.rt = H.rt0 then Dw.p * (Dw.p - 1) / 2 else Dw.q * (Dw.q - 1) / 2 := by
    intro τ; unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult; split_ifs <;> rfl
  rw [hcard, hdim, Finset.sum_congr rfl (fun τ _ => hterm τ), Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, hcm, hnot, hk2]
  ring
end _root_.GlobalTheory.FlagDim
end GlobalTheory.FlagDim
