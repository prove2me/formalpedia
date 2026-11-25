-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.ordVal_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:01:09.897086+00:00
-- url     : https://prove2.me/submissions/8da37b09-7b26-4b08-9b2b-5e04def093f7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PtFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_OrderValuation
import Theorems.Thm_Formalism_L2_Pj_evI_smul
import Theorems.Thm_Formalism_L2_Pj_nval_mul_unit


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
theorem _root_.solution {o : Rul Xo c → EReal} (ho : o ∈ ordVal Xo c) {a : c.F} (ha : a ≠ 0) (f : Rul Xo c) :
    o (a • f) = o f := by
  obtain ⟨T, ι, ht, y, rfl⟩ := ho
  show nval T.V 1 (evI y (a • f)) = nval T.V 1 (evI y f)
  rw [evI_smul]
  exact nval_mul_unit 1 ((map_ne_zero ι).2 ha) (ht a ha) _
end GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36
