-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeBern.R_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:37:03.900053+00:00
-- url     : https://prove2.me/submissions/7efe2192-9ef9-49fa-8ef5-ceafecf13a40

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeAlgebraStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_T_dd
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_ext_dd
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



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
theorem _root_.solution : R T hp 1 = 1 := by
  have hf : (hp 1).toFinset = {((1 : G) : G ⧸ K)} := by
    ext x
    simp only [Set.Finite.mem_toFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨k, rfl⟩
      exact QuotientGroup.eq.2 (by simp)
    · rintro rfl; exact MulAction.mem_orbit_self _
  have hq : q hp (1 : G) = 1 := by simp [q, hf]
  rw [R, hq, inv_one, one_smul]
  apply ext_dd T h1 h3
  rw [T_dd T hp h1, hf, Finset.sum_singleton]
  rfl
end GlobalTheory.CompanionTheory.HeckeBern
