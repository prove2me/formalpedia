-- Prove2me | solution 1 for GlobalTheory.BetaEx.betaExists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:10:35.06309+00:00
-- url     : https://prove2.me/submissions/412da820-0345-4a67-bfb4-453e723174dc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
import Theorems.Thm_GlobalTheory_BetaEx_exists_index_ideal
import Theorems.Thm_GlobalTheory_BetaEx_exists_smul_std
import Theorems.Thm_GlobalTheory_BetaEx_bdd_of_unimod
import Theorems.Thm_GlobalTheory_BetaEx_span_image_span
import Theorems.Thm_GlobalTheory_BetaEx_span_image_smul

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
open GlobalTheory GlobalTheory.BetaEx
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
namespace GlobalTheory.BetaEx
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (n bad : ℕ), Formalism.L2.Pj.BetaExists (Dw := Dw) c n bad := by
  intro E _ _ _ H Dw l c n bad hK Λ hU _
  obtain ⟨𝔞, h0, h1, h2⟩ := exists_index_ideal Λ.Ln Λ.La inf_le_left (bdd_of_unimod Λ hU) (fun m hm => by
    obtain ⟨a, ha, h⟩ := exists_smul_std m
    exact ⟨a, ha, Λ.La.smul_mem a hm, h⟩)
  obtain ⟨β, hβ0, hβ1, hβ2⟩ := hK 𝔞 h0
  refine ⟨β, hβ0, ?_, fun σ => ?_⟩
  · have e : ∀ τ, idealAt c Λ.Ln τ =
        Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 E))) * idealAt c Λ.La τ := by
      intro τ
      unfold idealAt
      rw [← span_image_span (embF c τ) (detSet Λ.Ln), ← span_image_span (embF c τ) (detSet Λ.La)]
      have := span_image_smul (embF c τ) 𝔞 (detSpan Λ.La)
      rw [← h1] at this
      exact this
    unfold BetaIs
    simp only [e, mul_pow, Finset.prod_mul_distrib, hβ1]
  · rw [hβ2, h2]; rfl
end GlobalTheory.BetaEx
