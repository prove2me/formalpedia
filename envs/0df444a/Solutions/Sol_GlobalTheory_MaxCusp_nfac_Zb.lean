-- Prove2me | solution 1 for GlobalTheory.MaxCusp.nfac_Zb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:05:16.255911+00:00
-- url     : https://prove2.me/submissions/3018dc8a-7bf8-487a-9589-89853cff300d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientSupportHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsHermOfMemLZ
import Theorems.Thm_GlobalTheory_MaxCusp_dmin_Zb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_dmin_Zb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MaxCusp
open NumberField Complex MeasureTheory Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r d : ℕ}
variable (X : Data E r)
namespace GlobalTheory.MaxCusp
theorem _root_.solution (u : Fin d → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin d → Fin d → ℂ) (hb : IsHerm b) (la : Wt X.Ψ r) (x : Frame X.Ψ r) :
    X.nfac la (Zb X u b x) = X.nfac la x := by
  simp only [Data.nfac, dmin_Zb X u hu b hb]
end GlobalTheory.MaxCusp
