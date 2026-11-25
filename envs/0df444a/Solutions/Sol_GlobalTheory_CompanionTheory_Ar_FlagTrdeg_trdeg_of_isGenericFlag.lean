-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.FlagTrdeg.trdeg_of_isGenericFlag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:32:06.629811+00:00
-- url     : https://prove2.me/submissions/87cf87c6-3a0d-4737-94c1-aad347fee203

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_GenericFlagTrdegFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagTrdeg_card_below_diagonal
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagTrdeg_isTranscendenceBasis_of_adjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.Ar
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagTrdeg
open scoped IntermediateField.algebraAdjoinAdjoin
namespace GlobalTheory.CompanionTheory.Ar.FlagTrdeg
theorem _root_.solution (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (E : Type) [AddCommGroup E]
    [Module Ω₀ E] (E' : Type) [AddCommGroup E'] [Module Ω E'] (j : E →+ E') (S : Type) [Fintype S]
    (r : S → ℕ) (V : S → Submodule Ω₀ E) (b₀ : ∀ σ, Fin (r σ) → E') (d : ℕ)
    (hg : IsGenericFlag (Ω' := Ω) j V b₀ d) :
    Algebra.trdeg Ω₀ Ω = ((∑ σ, r σ * (r σ - 1) / 2 : ℕ) : Cardinal) := by
  obtain ⟨c, u, -, -, -, -, hdiag, hup, -, hind, hd, hfr⟩ := hg
  have heq : IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨⟨σ, l, k⟩, rfl⟩
      rcases lt_trichotomy k l with hkl | hkl | hkl
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨σ, ⟨(l, k), hkl⟩⟩, rfl⟩
      · subst hkl
        simp only [hdiag]
        exact one_mem _
      · simp only [hup σ l k hkl]
        exact zero_mem _
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨⟨σ, ⟨⟨l, k⟩, hkl⟩⟩, rfl⟩
      exact IntermediateField.subset_adjoin _ _ ⟨⟨σ, (l, k)⟩, rfl⟩
  haveI : Module.Finite (IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) Ω :=
    Module.finite_of_finrank_pos (by rw [hfr]; exact hd)
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) Ω :=
    Algebra.IsAlgebraic.of_finite _ _
  rw [heq] at halg
  have hb := isTranscendenceBasis_of_adjoin hind halg
  rw [← hb.cardinalMk_eq_trdeg, Cardinal.mk_fintype, Fintype.card_sigma]
  simp only [card_below_diagonal]
end GlobalTheory.CompanionTheory.Ar.FlagTrdeg
