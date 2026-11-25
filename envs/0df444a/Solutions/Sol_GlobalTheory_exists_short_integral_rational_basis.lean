-- Prove2me | solution 1 for GlobalTheory.exists_short_integral_rational_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:03:02.547669+00:00
-- url     : https://prove2.me/submissions/da7055fc-3637-4410-b105-74eaa2cd4fc4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsShortIntegralRationalBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ (n : ℕ) (ω : Fin n → 𝓞 E),
      (∀ j (σ : E →+* ℂ), ‖σ (ω j)‖ ≤ omStar (E := E)) ∧
      ∀ α : 𝓞 E, (α : E) ∈ Submodule.span ℚ (Set.range fun j => (ω j : E))) →
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
      ∃ ω : Fin (Module.finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun j => (ω j : E)) ∧
        ∀ j (τ : E →+* ℂ), ‖τ (ω j : E)‖ ≤ omStar (E := E)) := by
  intro hex E _ _ _
  classical
  obtain ⟨n, ω, hωB, hsp⟩ := hex E
  have htop : Submodule.span ℚ (Set.range fun j => (ω j : E)) = ⊤ := by
    rw [eq_top_iff, ← (NumberField.integralBasis E).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [NumberField.integralBasis_apply]
    exact hsp _
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℚ (Set.range fun j => (ω j : E))
  have hbfin : b.Finite := hbli.setFinite
  have := hbfin.fintype
  have hcard : Fintype.card b = Module.finrank ℚ E := by
    have h := finrank_span_eq_card hbli
    rw [Subtype.range_coe, hbspan, htop, finrank_top] at h
    rw [h]
  let e : Fin (Module.finrank ℚ E) ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hmem : ∀ x : b, ∃ j, (ω j : E) = x := fun x => hbS x.2
  choose idx hidx using hmem
  refine ⟨fun i => ω (idx (e i)), ?_, fun i τ => hωB _ τ⟩
  have : (fun i => ((ω (idx (e i)) : 𝓞 E) : E)) = (fun x : b => (x : E)) ∘ e := by
    funext i; simp [hidx]
  rw [this]
  exact (linearIndependent_equiv e).mpr hbli
end GlobalTheory
