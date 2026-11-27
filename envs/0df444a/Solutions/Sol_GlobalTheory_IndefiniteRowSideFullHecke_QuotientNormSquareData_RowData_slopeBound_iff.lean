-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData.RowData.slopeBound_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:29:41.329371+00:00
-- url     : https://prove2.me/submissions/e8c82efd-3591-413d-86bd-9265d9fad034

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_QuotientNormSquareData
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_QuotientNormSquareData_RowData_glued_fg
import Theorems.Thm_Formalism_HN_muChar
import Theorems.Thm_Formalism_HN_plLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData
variable {L : Type} [Field L] [NumberField L]
namespace GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData
namespace RowData
theorem _root_.solution [StarRing L] {T : Type} [Finite T] {κ : T → Type} [∀ t, Fintype (κ t)]
    [∀ t, DecidableEq (κ t)] {τ ε C : Type} [Fintype ε] [DecidableEq ε] {m : ℕ}
    (D : RowData L T κ τ ε C m) (h0 : D.glued ≠ ⊥) (hh : ℝ) :
    D.SlopeBound hh ↔ Formalism.HN.muMaxDef (Pi.basisFun L ε) D.XE D.glued ≤ hh - D.logKap := by
  have hl := fun N hN => Formalism.HN.plLat L (ε → L) ε (Pi.basisFun L ε) D.XE D.XE_unit N hN
  have hc := Formalism.HN.muChar (𝓞 L) _ _ _ _ (hl _ D.glued_fg).1 h0
  constructor
  · intro h
    obtain ⟨N, hN, hN0, hs⟩ := hc.2.2.1
    have := h N hN.1 hN0
    unfold Formalism.HN.muDef at this
    unfold Formalism.HN.muMaxDef
    rwa [← hs]
  · intro h N hN hN0
    refine le_trans ?_ h
    have h1 := (hc.1 _).1 le_rfl
    have hcN := Formalism.HN.muChar (𝓞 L) _ _ _ _ (hl _ (D.glued_fg.of_le hN)).1 hN0
    have h2 := (hcN.1 _).2 fun N' hN' => h1 N' (hN'.trans hN)
    have h3 := hcN.2.2.2.2
    unfold Formalism.HN.muDef Formalism.HN.muMaxDef
    linarith
end RowData
end GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData
