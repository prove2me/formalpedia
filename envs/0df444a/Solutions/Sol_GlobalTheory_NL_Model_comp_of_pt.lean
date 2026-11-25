-- Prove2me | solution 1 for GlobalTheory.NL.Model.comp_of_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:02:20.420576+00:00
-- url     : https://prove2.me/submissions/f5613f54-3a15-463d-b0f6-6c06c8a200e4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NotFullBot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnramifiedSubfieldLeCyclotomicExt
import Theorems.Thm_GlobalTheory_NL_Model_ext_aux
import Theorems.Thm_GlobalTheory_NL_Model_zetaQ_mem
import Theorems.Thm_GlobalTheory_NL_Model_unramifiedSubfield_le_cyclotomicExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NL GlobalTheory.NL.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.NL
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} {F : LocFon l P AI H}
  {K : FinExt l} {s : ℕ} {LL : FinExt l}
namespace GlobalTheory.NL.Model
theorem _root_.solution (h : Good K s LL) (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hp : Pt H h i ζ τ) : ∃ ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR, Comp H h i ζ τ ι := by
  obtain ⟨τs, ⟨h1, h2⟩, h3⟩ := hp
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨σ, hσ'⟩ := ext_aux τs (Ks K s).val
  have hσ : ∀ y : ↥(Ks K s), σ (τs y) = (y : Om l) := hσ'
  refine ⟨(IsScalarTower.toAlgHom ℚ_[l] (Om l) P.R.BdR).comp σ, ?_, ?_, ?_⟩
  · intro c
    rw [← h1 c ⟨c, unramifiedSubfield_le_cyclotomicExt K s c.2⟩ rfl]
    change algebraMap (Om l) P.R.BdR (σ (τs _)) = _
    rw [hσ]; rfl
  · rw [← h2 ⟨_, zetaQ_mem P K s⟩ rfl]
    change algebraMap (Om l) P.R.BdR (σ (τs _)) = _
    rw [hσ]
  · intro c
    rw [h3 c ⟨c, h.2.2.1 c.2⟩ rfl]
    change algebraMap (Om l) P.R.BdR (σ (τs _)) = _
    rw [hσ]; rfl
end GlobalTheory.NL.Model
