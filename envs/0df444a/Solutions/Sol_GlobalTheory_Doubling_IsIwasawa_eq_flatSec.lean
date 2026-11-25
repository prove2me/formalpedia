-- Prove2me | solution 1 for GlobalTheory.Doubling.IsIwasawa.eq_flatSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:41:32.280021+00:00
-- url     : https://prove2.me/submissions/8a17b6c5-1f3b-481e-a155-8e76e368af2b

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_flatSec_of_mem
import Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_indLaw_flatSec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open scoped NNReal
open MeasureTheory
variable {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G) (χ : P →* Circle) (t : ℂ)
variable {K}
variable (K)
variable {δ K χ t}
open GlobalTheory.Doubling.IsIwasawa
variable (h : IsIwasawa δ K)
include h
namespace GlobalTheory.Doubling.IsIwasawa
theorem _root_.solution {Φ : ℂ → G → ℂ} {ρ : ℂ} (hΦ : ∀ s, IndLaw δ χ (s + ρ) (Φ s)) (hf : IsFlat K Φ) (s₀ s : ℂ) :
    Φ s = flatSec δ K (Φ s₀) s₀ s :=
  IndLaw.ext h.1 (hΦ s) (h.indLaw_flatSec (hΦ s₀) s) fun k hk => by rw [h.flatSec_of_mem _ _ _ hk, hf s s₀ k hk]
end GlobalTheory.Doubling.IsIwasawa
