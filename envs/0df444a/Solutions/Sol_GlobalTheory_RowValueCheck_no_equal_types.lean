-- Prove2me | solution 1 for GlobalTheory.RowValueCheck.no_equal_types
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:13:31.454082+00:00
-- url     : https://prove2.me/submissions/ee7edb71-3443-48b4-b9e9-403259577247

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_ValOfKindIndep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open GlobalTheory GlobalTheory.RowValueCheck
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
namespace GlobalTheory.RowValueCheck
theorem _root_.solution (G : ∀ g, Cart V d (I g) (J g)) (alt : Prop) {N : ℕ}
    (P : MvPolynomial (Fin N × WV I) C) (kind : Fin N → Option (Fin 2 × ZMod d × ZMod d))
    (h : RowsOK G alt P kind) (ρ : Fin N) (μ μ' : Fin N × WV I →₀ ℕ) (hμ : μ ∈ P.support)
    (hμ' : μ' ∈ P.support) (w w' : WV I) (hw : μ (ρ, w) ≠ 0) (hw' : μ' (ρ, w') ≠ 0)
    (hne : w.1 ≠ w'.1) : alt ∧ tyW G w ≠ tyW G w' := by
  rcases hk : kind ρ with _ | ⟨g, a, a'⟩
  · obtain ⟨g, hg⟩ := h.2 ρ hk
    exact absurd ((hg μ hμ w hw).trans (hg μ' hμ' w' hw').symm) hne
  · obtain ⟨ha, ho, hl⟩ := h.1 ρ g a a' hk
    have hab : a ≠ a' := by
      rintro rfl
      simp at ho
    refine ⟨ha, ?_⟩
    rcases hl μ hμ w hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hl μ' hμ' w' hw' with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact absurd (h1.trans h3.symm) hne
    · rw [h2, h4]; exact hab
    · rw [h2, h4]; exact hab.symm
    · exact absurd (h1.trans h3.symm) hne
end GlobalTheory.RowValueCheck
