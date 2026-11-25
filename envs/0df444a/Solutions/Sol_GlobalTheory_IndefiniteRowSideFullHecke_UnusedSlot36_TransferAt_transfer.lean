-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.TransferAt.transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:03:10.255583+00:00
-- url     : https://prove2.me/submissions/0770966f-9efd-4774-864b-cccc68d5c891

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PtFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_OrderValuation
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnusedSlot36_NoCommonZero_at

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36
open Formalism.L2.Pj Formalism.L2.PjFree NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)
variable {Xo c}
variable (Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
variable {Xo c U}
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36
namespace TransferAt
theorem _root_.solution (h : TransferAt Xo c U) : Transfer Xo c U :=
  ⟨h.1, fun la aL nL aE nE hL hE m w hw hz => h.2.1 la aL nL aE nE hL hE m w hw (hz.at la),
    fun la aL nL hL m w hw hz => h.2.2 la aL nL hL m w hw (hz.at la)⟩
end TransferAt
end GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36
