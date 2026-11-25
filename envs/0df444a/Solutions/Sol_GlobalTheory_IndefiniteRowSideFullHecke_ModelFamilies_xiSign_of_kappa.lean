-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies.xiSign_of_kappa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:54:14.296322+00:00
-- url     : https://prove2.me/submissions/7201531f-acae-4e73-a93a-b41d1db49664

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
theorem _root_.solution (M : ModelsOf F r) (h : ∀ k, (M.X k).κ0 = 2 * (M.X k).ξ0) : XiSign M := by
  intro k τ hτ
  have h1 := (M.X k).κ0_sign ⟨τ, hτ⟩
  rw [h k] at h1
  have h2 : τ 2 = 2 := map_ofNat τ 2
  simp [h2] at h1
  linarith
end GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies
