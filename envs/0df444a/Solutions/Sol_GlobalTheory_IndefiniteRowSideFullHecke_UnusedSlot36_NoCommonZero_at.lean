-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero.at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:40:17.860437+00:00
-- url     : https://prove2.me/submissions/6e2f91f1-97be-475a-9a83-c13a0cb6fe9d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PtFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_OrderValuation
import Theorems.Thm_Formalism_L2_Pj_nval_of_ne


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
namespace NoCommonZero
theorem _root_.solution {κ : Type} {w : κ → Rul Xo c} (h : NoCommonZero w) (la : HeightOneSpectrum (𝓞 c.F)) :
    NoCommonZeroAt la w := by
  rintro _ ⟨⟨q, T, ι, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
  letI := ι.toAlgebra
  obtain ⟨k, hk⟩ := h T.Fr y.1 y.2.1
  refine ⟨k, ?_⟩
  show nval T.V e (evI y (w k)) ≠ ⊤
  have hk' : evI y (w k) ≠ 0 := hk
  rw [nval_of_ne hk']
  exact EReal.coe_ne_top _
end NoCommonZero
end GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36
