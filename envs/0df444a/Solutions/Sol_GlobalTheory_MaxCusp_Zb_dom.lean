-- Prove2me | solution 1 for GlobalTheory.MaxCusp.Zb_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:00:36.540208+00:00
-- url     : https://prove2.me/submissions/5a00125e-6bb0-4bdd-8c8a-2b6e023398a9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientSupportHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsHermOfMemLZ
import Theorems.Thm_GlobalTheory_MaxCusp_zmat_det
import Theorems.Thm_GlobalTheory_MaxCusp_mat_Zb
import Theorems.Thm_GlobalTheory_MaxCusp_dmin_Zb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_dmin_Zb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_mat_Zb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_zmat_det
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientMatrices_mat_Zb


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
    (b : X.Ψ → Fin d → Fin d → ℂ) (hb : IsHerm b) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Zb X u b x ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · rw [mat_Zb, Matrix.det_mul, zmat_det X u hu, one_mul]; exact (hx τ).1
  · rw [dmin_Zb X u hu b hb]; exact (hx τ).2 i
end GlobalTheory.MaxCusp
