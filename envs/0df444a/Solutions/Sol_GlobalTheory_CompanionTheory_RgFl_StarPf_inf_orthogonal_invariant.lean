-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgFl.StarPf.inf_orthogonal_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:08:36.586356+00:00
-- url     : https://prove2.me/submissions/55e34234-fec4-416b-9a38-ead8b9b42dce

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
theorem _root_.solution [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : A →ₐ[ℂ] Module.End ℂ V) (hs : StarClosed ρ) {U W : Submodule ℂ V}
    (hU : ∀ h, ∀ u ∈ U, ρ h u ∈ U) (hW : ∀ h, ∀ w ∈ W, ρ h w ∈ W) :
    ∀ h, ∀ x ∈ Uᗮ ⊓ W, ρ h x ∈ Uᗮ ⊓ W := by
  intro h x hx
  obtain ⟨hxU, hxW⟩ := Submodule.mem_inf.mp hx
  refine Submodule.mem_inf.mpr ⟨?_, hW h x hxW⟩
  rw [Submodule.mem_orthogonal] at hxU ⊢
  intro u hu
  obtain ⟨h', hh'⟩ := hs h
  rw [← inner_conj_symm, hh' x u, inner_conj_symm]
  exact hxU _ (hU h' u hu)
end GlobalTheory.CompanionTheory.RgFl.StarPf
