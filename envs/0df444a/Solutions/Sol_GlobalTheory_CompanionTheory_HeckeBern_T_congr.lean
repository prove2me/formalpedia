-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeBern.T_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:37:04.885952+00:00
-- url     : https://prove2.me/submissions/47d544d1-e792-4d01-ae4c-7a0e47ede7aa

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
theorem _root_.solution {g : G} {k k' : G} (hk : k ∈ K) (hk' : k' ∈ K) : T (k * g * k') = T g ∧ q hp (k * g * k') = q hp g := by
  have e : ((k * g * k' : G) : G ⧸ K) = (⟨k, hk⟩ : K) • (g : G ⧸ K) := by
    show ((k * g * k' : G) : G ⧸ K) = ((k * g : G) : G ⧸ K)
    rw [QuotientGroup.eq]
    have : (k * g * k')⁻¹ * (k * g) = k'⁻¹ := by group
    rw [this]; exact K.inv_mem hk'
  have ho : MulAction.orbit K ((k * g * k' : G) : G ⧸ K) = MulAction.orbit K (g : G ⧸ K) := by
    rw [e, MulAction.orbit_smul]
  have hf : (hp (k * g * k')).toFinset = (hp g).toFinset := by
    ext x; simp [ho]
  refine ⟨ext_dd T h1 h3 ?_, by simp only [q, hf]⟩
  rw [T_dd T hp h1, T_dd T hp h1, hf]
end GlobalTheory.CompanionTheory.HeckeBern
