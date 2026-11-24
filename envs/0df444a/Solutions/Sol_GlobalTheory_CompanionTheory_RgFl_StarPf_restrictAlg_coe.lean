-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgFl.StarPf.restrictAlg_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:09:20.523075+00:00
-- url     : https://prove2.me/submissions/d6fb80ce-d2f2-438c-a4e5-b0ad55443e5a

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_SmallPI
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_StatementStar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.Fl CompanionTheory.D.gk.admitted
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgFl GlobalTheory.CompanionTheory.RgFl.StarPf
variable {A V : Type} [Ring A] [Algebra ℂ A]
namespace GlobalTheory.CompanionTheory.RgFl.StarPf
theorem _root_.solution [AddCommGroup V] [Module ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V) (W : Submodule ℂ V)
    (hW : ∀ h, ∀ w ∈ W, ρ h w ∈ W) (h : A) (x : W) : ((restrictAlg ρ W hW h x : W) : V) = ρ h x := rfl
end GlobalTheory.CompanionTheory.RgFl.StarPf
