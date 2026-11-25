-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies.pmOf_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:54:12.640669+00:00
-- url     : https://prove2.me/submissions/30111e1d-3c2d-42af-a2eb-0ffb815b399e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ModelFamilies

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
variable {F : FamAt Xo c σ e} {r : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies
theorem _root_.solution (M : ModelsOf F r) (k : Fin F.n) (x : Frame (M.X k).Ψ r) (a : (F.Di k).La) (j : Fin g) :
    pmOf M k x a j = perFr (M.X k) x (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2 := rfl
end GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies
