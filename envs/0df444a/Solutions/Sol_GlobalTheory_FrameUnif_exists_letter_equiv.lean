-- Prove2me | solution 1 for GlobalTheory.FrameUnif.exists_letter_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:38:40.138805+00:00
-- url     : https://prove2.me/submissions/b11e5d2c-b228-409d-a89b-2511d4452328

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RelabelEmbeddingsGoodBijectiveConjCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmTypeLetterFrameColumnDictionary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.FrameUnif
namespace GlobalTheory.FrameUnif
theorem _root_.solution {E : Type} [Field E] (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (p q r : ℕ) (hr : r = p + q)
    (ρ : (E →+* ℂ) → (E →+* ℂ)) (hρ : Function.Bijective ρ) (m : (E →+* ℂ) → ℕ)
    (hp : ∀ τ, ρ τ ∈ Ψ → m τ = p) (hq : ∀ τ, ρ τ ∉ Ψ → m τ = q) :
    ∃ f : (Σ τ, Fin (m τ)) ≃ Ψ × Fin r, ∀ s,
      (ρ s.1 ∈ Ψ ∧ (f s).1.1 = ρ s.1 ∧ ((f s).2 : ℕ) = q + s.2) ∨
      (ρ s.1 ∉ Ψ ∧ (f s).1.1 = ComplexEmbedding.conjugate (ρ s.1) ∧ ((f s).2 : ℕ) = q - 1 - s.2 ∧ (s.2 : ℕ) < q) := by
  classical
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  have hf : ∀ s : Σ τ, Fin (m τ), ∃ t : Ψ × Fin r,
      (ρ s.1 ∈ Ψ ∧ t.1.1 = ρ s.1 ∧ (t.2 : ℕ) = q + s.2) ∨
      (ρ s.1 ∉ Ψ ∧ t.1.1 = ComplexEmbedding.conjugate (ρ s.1) ∧ (t.2 : ℕ) = q - 1 - s.2 ∧ (s.2 : ℕ) < q) := by
    rintro ⟨τ, i⟩
    have hi := i.2
    by_cases h : ρ τ ∈ Ψ
    · have := hp τ h
      exact ⟨(⟨ρ τ, h⟩, ⟨q + i, by omega⟩), Or.inl ⟨h, rfl, rfl⟩⟩
    · have := hq τ h
      have h' : ComplexEmbedding.conjugate (ρ τ) ∈ Ψ := by
        by_contra h'
        exact h ((hΨ _).2 h')
      exact ⟨(⟨_, h'⟩, ⟨q - 1 - i, by omega⟩), Or.inr ⟨h, rfl, rfl, by show (i : ℕ) < q; omega⟩⟩
  choose f hf using hf
  have hext : ∀ s s' : Σ τ, Fin (m τ), ρ s.1 = ρ s'.1 → (s.2 : ℕ) = s'.2 → s = s' := by
    rintro ⟨τ, i⟩ ⟨τ', i'⟩ h1 h2
    obtain rfl : τ = τ' := hρ.1 h1
    obtain rfl : i = i' := Fin.ext h2
    rfl
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩, hf⟩
  · intro s s' hss
    have h1 := hf s
    have h2 := hf s'
    rw [← hss] at h2
    rcases h1 with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1, d1⟩ <;> rcases h2 with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2, d2⟩
    · exact hext _ _ (b1.symm.trans b2) (by omega)
    · omega
    · omega
    · refine hext _ _ ?_ (by omega)
      rw [← hcc (ρ s.1), ← b1, b2, hcc]
  · rintro ⟨⟨τ, hτ⟩, j⟩
    have hj := j.2
    by_cases h : (j : ℕ) < q
    · obtain ⟨τ0, h0⟩ := hρ.2 (ComplexEmbedding.conjugate τ)
      have hn : ρ τ0 ∉ Ψ := h0 ▸ (hΨ τ).1 hτ
      have := hq τ0 hn
      refine ⟨⟨τ0, ⟨q - 1 - j, by omega⟩⟩, ?_⟩
      rcases hf ⟨τ0, ⟨q - 1 - j, by omega⟩⟩ with ⟨a, -⟩ | ⟨-, b, c, -⟩
      · exact absurd a hn
      · refine Prod.ext (Subtype.ext ?_) (Fin.ext ?_)
        · rw [b]; show ComplexEmbedding.conjugate (ρ τ0) = τ; rw [h0, hcc]
        · rw [c]; show q - 1 - (q - 1 - j) = j; omega
    · obtain ⟨τ0, h0⟩ := hρ.2 τ
      have hn : ρ τ0 ∈ Ψ := h0 ▸ hτ
      have := hp τ0 hn
      refine ⟨⟨τ0, ⟨j - q, by omega⟩⟩, ?_⟩
      rcases hf ⟨τ0, ⟨j - q, by omega⟩⟩ with ⟨-, b, c⟩ | ⟨a, -⟩
      · refine Prod.ext (Subtype.ext ?_) (Fin.ext ?_)
        · rw [b]; exact h0
        · rw [c]; show q + (j - q) = j; omega
      · exact absurd hn a
end GlobalTheory.FrameUnif
