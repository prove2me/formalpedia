-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeBern.R_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:54:08.548273+00:00
-- url     : https://prove2.me/submissions/867c988f-5f0f-40f3-854b-37d3de6b4c96

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeAlgebraStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_T_congr

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
variable (T : G → Hk K) (hp : IsHeckePair K)
variable (h1 : ∀ (g : G) (S : Finset (G ⧸ K)), (↑S : Set (G ⧸ K)) = MulAction.orbit K (g : G ⧸ K) →
    (T g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) =
      ∑ y ∈ S, Finsupp.single y (1 : ℂ))
  (h3 : ∀ h : Hk K, (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = 0 → h = 0)
include h1
include h3
namespace GlobalTheory.CompanionTheory.HeckeBern
theorem _root_.solution {g : G} {k k' : G} (hk : k ∈ K) (hk' : k' ∈ K) : R T hp (k * g * k') = R T hp g := by
  obtain ⟨a, b⟩ := T_congr T hp h1 h3 (g := g) hk hk'
  rw [R, R, a, b]
end GlobalTheory.CompanionTheory.HeckeBern
