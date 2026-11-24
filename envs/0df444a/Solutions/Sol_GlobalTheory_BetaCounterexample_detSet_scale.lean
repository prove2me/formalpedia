-- Prove2me | solution 1 for GlobalTheory.BetaCounterexample.detSet_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:01:25.630799+00:00
-- url     : https://prove2.me/submissions/1fba1791-1b0e-4828-9490-9af716baeb2c

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
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.BetaCounterexample
theorem _root_.solution {n : ℕ} (M M' : Submodule (𝓞 E) (Fin n → E)) (a : E)
    (h : ∀ v, v ∈ M' ↔ ∃ w ∈ M, v = a • w) : detSet M' = (fun d => a ^ n * d) '' detSet M := by
  have key : ∀ w : Fin n → Fin n → E, Matrix.det (Matrix.of fun i j => (a • w j) i) =
      a ^ n * Matrix.det (Matrix.of fun i j => w j i) := by
    intro w
    have : (Matrix.of fun i j => (a • w j) i) = a • (Matrix.of fun i j => w j i) := by
      ext i j; simp
    rw [this, Matrix.det_smul, Fintype.card_fin]
  ext d
  constructor
  · rintro ⟨v, hv, rfl⟩
    choose w hw hw' using fun i => (h (v i)).1 (hv i)
    refine ⟨_, ⟨w, hw, rfl⟩, ?_⟩
    have : v = fun j => a • w j := funext hw'
    subst this
    exact (key w).symm
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨fun j => a • w j, fun i => (h _).2 ⟨w i, hw i, rfl⟩, (key w).symm⟩
end GlobalTheory.BetaCounterexample
