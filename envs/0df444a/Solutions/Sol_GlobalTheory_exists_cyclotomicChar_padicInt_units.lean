-- Prove2me | solution 1 for GlobalTheory.exists_cyclotomicChar_padicInt_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:17:52.606811+00:00
-- url     : https://prove2.me/submissions/2518a22a-ca04-425f-9979-b5e29da0a195

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapPadicIntFinExtInjective
import Theorems.Thm_GlobalTheory_exists_padicInt_of_mem_OL
import Theorems.Thm_GlobalTheory_algebraMap_padicInt_OL_injective
import Theorems.Thm_GlobalTheory_associated_of_v_sub_one
import Theorems.Thm_GlobalTheory_exists_units_hom_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ} (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n), ∃ χ : W.Gam →* ℤ_[l]ˣ, (∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL))) ∧ (W.s = 1 → Associated ((χ W.gam : ℤ_[l]) - 1) (l : ℤ_[l])) := by
  intro l _ P K LL n W
  have hex : ∀ g, ∃ y : ℤ_[l], algebraMap ℤ_[l] ↥(OL LL) y = (W.χΓ g : ↥(OL LL)) := by
    intro g
    obtain ⟨h, rfl⟩ := W.resΓ_onto g
    have hmem : algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ h : ℚ_[l]) ∈ OL LL := by
      rw [← W.χΓ_res h]
      exact (W.χΓ (W.resΓ h) : ↥(OL LL)).2
    obtain ⟨y, hy⟩ := exists_padicInt_of_mem_OL LL _ hmem
    refine ⟨y, Subtype.ext ?_⟩
    show algebraMap ℤ_[l] ↥LL.1 y = _
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1, hy, ← W.χΓ_res h]
    rfl
  obtain ⟨χ, hχ⟩ := exists_units_hom_lift (algebraMap ℤ_[l] ↥(OL LL))
    (algebraMap_padicInt_OL_injective LL) W.χΓ hex
  refine ⟨χ, hχ, fun hs => ?_⟩
  apply associated_of_v_sub_one P LL _ _ (hχ W.gam)
  have hg := W.gam_gen
  rw [hs, Nat.cast_one] at hg
  exact hg
end GlobalTheory
