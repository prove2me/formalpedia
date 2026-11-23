-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeBern.hk_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:12.679988+00:00
-- url     : https://prove2.me/submissions/0b233aea-042a-4727-9408-f100560a0100

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeAlgebraStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.Fl
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeBern
variable {G : Type} [Group G] {K : Subgroup G}
namespace GlobalTheory.CompanionTheory.HeckeBern
theorem _root_.solution (A : Hk K) (g : G) (v : (G ⧸ K) →₀ ℂ) : A.1 (lam K g v) = lam K g (A.1 v) := by
  have h : lam K g * A.1 = A.1 * lam K g :=
    (Subalgebra.mem_centralizer_iff ℂ).1 A.2 _ ⟨g, rfl⟩
  exact (LinearMap.congr_fun h v).symm
end GlobalTheory.CompanionTheory.HeckeBern
