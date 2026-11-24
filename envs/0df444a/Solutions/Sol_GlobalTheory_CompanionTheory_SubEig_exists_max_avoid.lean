-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SubEig.exists_max_avoid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:40:14.600311+00:00
-- url     : https://prove2.me/submissions/b0aa22a3-2bbb-4828-8481-6edf322c1707

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothQuot
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisLast
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SubquotientOfEigencharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SubEig
variable {G : Type} [Group G] {U : Type} [AddCommGroup U] [Module ℂ U]
namespace GlobalTheory.CompanionTheory.SubEig
theorem _root_.solution (ρ : Representation ℂ G U) {u : U} (hu : u ≠ 0) :
    ∃ T : Subrepresentation ρ, u ∉ T.toSubmodule ∧
      ∀ T' : Subrepresentation ρ, T ≤ T' → u ∉ T'.toSubmodule → T' = T := by
  have hbot : (⊥ : Subrepresentation ρ) ∈ {T : Subrepresentation ρ | u ∉ T.toSubmodule} := by
    show u ∉ (⊥ : Submodule ℂ U)
    simpa using hu
  have hz : ∀ c ⊆ {T : Subrepresentation ρ | u ∉ T.toSubmodule}, IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ ub ∈ {T : Subrepresentation ρ | u ∉ T.toSubmodule}, ∀ z ∈ c, z ≤ ub := by
    intro c hc hchain y hy
    have hne : (Subrepresentation.toSubmodule '' c).Nonempty := ⟨_, y, hy, rfl⟩
    have hdir : DirectedOn (· ≤ ·) (Subrepresentation.toSubmodule '' c) := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rcases hchain.total ha hb with h | h
      · exact ⟨_, ⟨b, hb, rfl⟩, h, le_rfl⟩
      · exact ⟨_, ⟨a, ha, rfl⟩, le_rfl, h⟩
    have hmem : ∀ x, x ∈ sSup (Subrepresentation.toSubmodule '' c) ↔
        ∃ a ∈ c, x ∈ Subrepresentation.toSubmodule a := by
      intro x
      rw [Submodule.mem_sSup_of_directed hne hdir]
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, hx⟩
        exact ⟨a, ha, hx⟩
      · rintro ⟨a, ha, hx⟩
        exact ⟨_, ⟨a, ha, rfl⟩, hx⟩
    refine ⟨⟨sSup (Subrepresentation.toSubmodule '' c), ?_⟩, ?_, ?_⟩
    · intro g v hv
      obtain ⟨a, ha, hx⟩ := (hmem v).1 hv
      exact (hmem _).2 ⟨a, ha, a.apply_mem_toSubmodule g hx⟩
    · intro h
      obtain ⟨a, ha, hx⟩ := (hmem u).1 h
      exact hc ha hx
    · intro z hz x hx
      exact (hmem x).2 ⟨z, hz, hx⟩
  obtain ⟨T, -, hT⟩ := zorn_le_nonempty₀ {T : Subrepresentation ρ | u ∉ T.toSubmodule} hz ⊥ hbot
  exact ⟨T, hT.prop, fun T' hle hu' => le_antisymm (hT.le_of_ge hu' hle) hle⟩
end GlobalTheory.CompanionTheory.SubEig
