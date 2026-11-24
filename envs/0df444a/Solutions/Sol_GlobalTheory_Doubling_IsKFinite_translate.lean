-- Prove2me | solution 1 for GlobalTheory.Doubling.IsKFinite.translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:25:10.729687+00:00
-- url     : https://prove2.me/submissions/fb385670-5d68-4f73-9937-a49596608092

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact

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
namespace GlobalTheory.Doubling
namespace IsKFinite
theorem _root_.solution {Φ : G → ℂ} (h : IsKFinite K Φ) {k : G} (hk : k ∈ K) : IsKFinite K fun g => Φ (g * k) := by
  obtain ⟨W, _, hW⟩ := isKFinite_iff.1 h
  exact isKFinite_iff.2 ⟨W, inferInstance, fun k' hk' => by simpa only [mul_assoc] using hW _ (mul_mem hk' hk)⟩
end IsKFinite
end GlobalTheory.Doubling
