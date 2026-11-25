-- Prove2me | solution 1 for GlobalTheory.BetaCounterexample.betaIs_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:27:14.730166+00:00
-- url     : https://prove2.me/submissions/32d70c89-14ab-4826-bf4f-8bcea526526a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BetaIsPrincipal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BetaCounterexample
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l)
namespace GlobalTheory.BetaCounterexample
theorem _root_.solution {n : ℕ} (hn : 0 < n) (τ₀ : E →+* ℂ) (h0 : Dw.mult τ₀ ≠ 0) (β : c.F) :
    BetaIs (Dw := Dw) c (⟨⊥⟩ : GenLat E n) β := by
  have hd : ∀ τ, idealAt c (⊥ : Submodule (𝓞 E) (Fin n → E)) τ = 0 := by
    intro τ
    unfold idealAt
    rw [Submodule.zero_eq_bot, Submodule.span_eq_bot]
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    have : (Matrix.of fun i j => v j i) = 0 := by
      ext i j; simp [(Submodule.mem_bot _).1 (hv j)]
    have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [this, Matrix.det_zero, map_zero]
  have hL : (⟨⊥⟩ : GenLat E n).Ln = ⊥ := bot_inf_eq _
  unfold BetaIs
  rw [hL]
  have hz : ∏ τ : E →+* ℂ, idealAt c (⊥ : Submodule (𝓞 E) (Fin n → E)) τ ^ Dw.mult τ = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ τ₀) (by rw [hd, zero_pow h0])
  rw [hz, mul_zero]
end GlobalTheory.BetaCounterexample
