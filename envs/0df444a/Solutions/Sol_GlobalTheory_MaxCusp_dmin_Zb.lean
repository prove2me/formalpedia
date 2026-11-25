-- Prove2me | solution 1 for GlobalTheory.MaxCusp.dmin_Zb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:09:55.525939+00:00
-- url     : https://prove2.me/submissions/5b498237-044d-46eb-8614-42e0ed09e3d1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientSupportHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsHermOfMemLZ
import Theorems.Thm_GlobalTheory_MaxCusp_zmat_unitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gram_unitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_zmat_unitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientMatrices_gram_unitary


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
    (b : X.Ψ → Fin d → Fin d → ℂ) (hb : IsHerm b) (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (Zb X u b x) τ i = dmin X.Gm x τ i := by
  have : gram τ.1 X.Gm (mat (Zb X u b x) τ) = gram τ.1 X.Gm (mat x τ) :=
    X.gram_unitary x τ _ (zmat_unitary X u hu b hb τ)
  simp only [dmin]; rw [this]
end GlobalTheory.MaxCusp
