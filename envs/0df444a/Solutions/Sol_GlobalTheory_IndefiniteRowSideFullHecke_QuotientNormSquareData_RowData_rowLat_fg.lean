-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData.RowData.rowLat_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:15:48.017123+00:00
-- url     : https://prove2.me/submissions/5c8ad780-8535-4a03-b309-faa9b61f12ee

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_QuotientNormSquareData
import Theorems.Thm_Formalism_HN_PlaceDecomposition_psi_injective


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
theorem _root_.solution (t : T) : (D.rowLat t).FG := by
  have h1 : (D.M t ⊓ (D.V₀ t).restrictScalars (𝓞 L)).FG :=
    (D.M_lattice t).fg.of_le inf_le_left
  refine Submodule.fg_of_fg_map_injective (D.psi.mulVecLin.restrictScalars (𝓞 L))
    D.psi_injective ?_
  exact (h1.map _).of_le (Submodule.map_comap_le _ _)
end GlobalTheory.IndefiniteRowSideFullHecke.QuotientNormSquareData.RowData
