-- Prove2me | solution 1 for GlobalTheory.Doubling.norm_flatSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:44:15.673982+00:00
-- url     : https://prove2.me/submissions/d1df8297-1816-4b5d-897b-f4ed52471817

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Theorems.Thm_GlobalTheory_Doubling_iwAbs_pos
import Theorems.Thm_GlobalTheory_Doubling_norm_npow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open scoped NNReal
open MeasureTheory
variable {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G) (χ : P →* Circle) (t : ℂ)
variable {K}
variable (K)
variable {δ K χ t}
namespace GlobalTheory.Doubling
theorem _root_.solution (Φ : G → ℂ) (s₀ s : ℂ) (g : G) :
    ‖flatSec δ K Φ s₀ s g‖ = ‖Φ g‖ * (iwAbs δ K g : ℝ) ^ (s.re - s₀.re) := by
  rw [flatSec, norm_mul, norm_npow (iwAbs_pos δ K g), Complex.sub_re]
end GlobalTheory.Doubling
