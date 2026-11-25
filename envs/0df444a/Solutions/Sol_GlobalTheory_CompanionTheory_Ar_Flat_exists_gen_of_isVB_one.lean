-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Flat.exists_gen_of_isVB_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:31:25.655581+00:00
-- url     : https://prove2.me/submissions/7b0258cb-9af5-491b-a134-cb34be09cf12

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EtaleLocalizationAtPrimeTensorOfLowHeight
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsGenOfIsVBOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]
variable {L : Lat ξ E} {σ : E} {ϖ : Ω} {M M' : ℕ} {a a' : ℤ} {p : Cpt ξ}
namespace GlobalTheory.CompanionTheory.Ar.Flat
theorem _root_.solution {V : Submodule Ω E} (hL : L.IsVB 1 V) (p : Cpt ξ) :
    ∃ e : E, e ≠ 0 ∧ L p = Submodule.span (regAt ξ p) {e} ∧ V = Submodule.span Ω {e} := by
  obtain ⟨U, hU, b, hb, h⟩ := hL p trivial
  obtain ⟨h1, h2⟩ := h p trivial hU
  have hr : Set.range b = {b 0} := by
    ext x
    simp [Fin.exists_fin_one, eq_comm]
  exact ⟨b 0, h1.ne_zero 0, by rw [h2, hr], by rw [← hb, hr]⟩
end GlobalTheory.CompanionTheory.Ar.Flat
