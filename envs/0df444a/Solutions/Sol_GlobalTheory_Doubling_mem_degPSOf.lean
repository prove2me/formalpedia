-- Prove2me | solution 1 for GlobalTheory.Doubling.mem_degPSOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:44:44.854399+00:00
-- url     : https://prove2.me/submissions/5fa4d5d6-a172-4da8-914c-67a31a3c8e89

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct

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
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
open scoped NNReal
open MeasureTheory
variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι] {G : Type} [Group G]
  (mat : G →* GL ι A) (ν : Aˣ →* ℝ≥0) (K : Subgroup G)
variable {e mat ν K}
namespace GlobalTheory.Doubling
theorem _root_.solution [TopologicalSpace G] {μ : Aˣ →* Circle} {s : ℂ} {Φ : G → ℂ} : Φ ∈ degPSOf e mat ν K μ s ↔
    (∀ (p : siegelOf e mat) (g : G),
      Φ (p * g) = μ (aOf e mat p) * npow (ν (aOf e mat p)) (s + (Fintype.card n : ℂ) / 2) * Φ g) ∧
      Continuous Φ ∧ IsKFinite K Φ := Iff.rfl
end GlobalTheory.Doubling
