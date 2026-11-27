-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData.RowData.glued_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:23:41.014261+00:00
-- url     : https://prove2.me/submissions/2f2dda96-b654-408c-a695-626dc239b4d3

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_QuotientNormSquareData
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_QuotientNormSquareData_RowData_rowLat_fg

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
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData.RowData
variable {T : Type} {κ : T → Type} [∀ t, Fintype (κ t)] [∀ t, DecidableEq (κ t)]
  {τ ε C : Type} [Fintype ε] [DecidableEq ε] {m : ℕ} (D : RowData L T κ τ ε C m)
namespace GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData.RowData
theorem _root_.solution [Finite T] : D.glued.FG := by
  have hS : (⨆ t, D.rowLat t).FG := Submodule.fg_iSup _ D.rowLat_fg
  refine hS.of_le fun x hx => ?_
  by_contra hne
  let I : Ideal (𝓞 L) := (⨆ t, D.rowLat t).comap (LinearMap.toSpanSingleton (𝓞 L) _ x)
  have hI : I ≠ ⊤ := by
    intro h
    have : (1 : 𝓞 L) ∈ I := h ▸ Submodule.mem_top
    exact hne (by simpa [I] using this)
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨s, hs, hsx⟩ := hx ⟨P, hP.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField L)⟩
  exact hs (hle (show s • x ∈ ⨆ t, D.rowLat t from le_iSup D.rowLat _ hsx))
end GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData.RowData
