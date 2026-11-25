-- Prove2me | solution 1 for GlobalTheory.BetaCounterexample.betaIs_principal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:27:20.663503+00:00
-- url     : https://prove2.me/submissions/0bafffef-53d5-4d34-bd23-c2427053d957

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BetaIsPrincipal
import Theorems.Thm_GlobalTheory_BetaCounterexample_detSet_scale

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
theorem _root_.solution {n : ℕ} (Λ : GenLat E n) (a : E) (h : ∀ v, v ∈ Λ.Ln ↔ ∃ w ∈ Λ.La, v = a • w) :
    BetaIs (Dw := Dw) c Λ (∏ τ : E →+* ℂ, embF c τ (a ^ n) ^ Dw.mult τ) := by
  have h1 : ∀ τ, idealAt c Λ.Ln τ = Submodule.span (𝓞 c.F) {embF c τ (a ^ n)} * idealAt c Λ.La τ := by
    intro τ
    unfold idealAt
    rw [detSet_scale Λ.La Λ.Ln a h, Submodule.span_mul_span, Set.singleton_mul, Set.image_image, Set.image_image]
    simp only [map_mul]
  unfold BetaIs
  simp only [h1, mul_pow, Finset.prod_mul_distrib, Submodule.span_pow, Set.singleton_pow]
  rw [Submodule.prod_span_singleton]
end GlobalTheory.BetaCounterexample
