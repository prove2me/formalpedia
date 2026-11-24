-- Prove2me | solution 1 for GlobalTheory.SW.GaussDict.exists_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:42:54.184226+00:00
-- url     : https://prove2.me/submissions/a24b9c4d-81a6-41d5-b4c1-1e9597ad2b9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_GaussianQuadFormRationalCoordsHermitian
import Theorems.Thm_GlobalTheory_SW_GaussDict_exists_emb_comb_transpose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.GaussDict
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
namespace GlobalTheory.SW.GaussDict
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (v v' : Ψ → Fin N → ℂ) :
    ∃ u : QI E N → ℂ, ∀ (τ : Ψ) (a : Fin N),
      ∑ j, τ.1 (Module.finBasis ℚ E j) * u (a, j) = v τ a ∧
      ∑ j, conj (τ.1 (Module.finBasis ℚ E j)) * u (a, j) = v' τ a := by
  classical
  have hc : ∀ σ : E →+* ℂ, σ ∉ Ψ → ComplexEmbedding.conjugate σ ∈ Ψ := fun σ hσ => by
    rw [hΨ, ComplexEmbedding.involutive_conjugate E σ]
    exact hσ

  let w : Fin N → (E →+* ℂ) → ℂ := fun a σ =>
    if h : σ ∈ Ψ then v ⟨σ, h⟩ a else v' ⟨_, hc σ h⟩ a
  choose c hc' using fun a => exists_emb_comb_transpose (w a)
  refine ⟨fun p => c p.1 p.2, fun τ a => ⟨?_, ?_⟩⟩
  · rw [hc' a τ.1]
    simp [w, τ.2]
  · have hn : ComplexEmbedding.conjugate τ.1 ∉ Ψ := (hΨ τ.1).mp τ.2
    have h := hc' a (ComplexEmbedding.conjugate τ.1)
    simp only [ComplexEmbedding.conjugate_coe_eq] at h
    rw [h]
    simp only [w, dif_neg hn]
    exact congrArg (fun t => v' t a) (Subtype.ext (ComplexEmbedding.involutive_conjugate E τ.1))
end GlobalTheory.SW.GaussDict
