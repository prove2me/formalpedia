-- Prove2me | solution 1 for GlobalTheory.SectionBasis.coords_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:15:55.572412+00:00
-- url     : https://prove2.me/submissions/7df3cf69-f8ee-400a-9add-0b4adefc9b6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PolyImgSuccAbove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDvdOfAlgebraic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SectionBasis
open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0 GlobalTheory.GenericSection
open scoped TensorProduct
namespace GlobalTheory.SectionBasis
theorem _root_.solution {K' M ι : Type} [Field K'] [AddCommGroup M] [Module K' M] {Q : ι → Type}
    [∀ Z, CommRing (Q Z)] (a : ∀ Z, K' →+* Q Z) {n : ℕ} (b : Fin n → M) (hli : LinearIndependent K' b)
    (hsp : Submodule.span K' (Set.range b) = ⊤)
    (E : letI : ∀ Z, Module K' (Q Z) := fun Z => (a Z).toModule; M ≃ₗ[K'] ∀ Z, Q Z) :
    (∀ c : Fin n → K', (∀ Z, ∑ k, a Z (c k) * E (b k) Z = 0) → ∀ k, c k = 0) ∧
    ∀ y : ∀ Z, Q Z, ∃ c : Fin n → K', ∀ Z, y Z = ∑ k, a Z (c k) * E (b k) Z := by
  letI : ∀ Z, Module K' (Q Z) := fun Z => (a Z).toModule
  have key : ∀ (c : Fin n → K') Z, E (∑ k, c k • b k) Z = ∑ k, a Z (c k) * E (b k) Z := by
    intro c Z
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul]
    rfl
  refine ⟨fun c hc => Fintype.linearIndependent_iff.1 hli c ?_, fun y => ?_⟩
  · apply E.injective
    rw [map_zero]
    exact funext fun Z => (key c Z).trans (hc Z)
  · have hy : E.symm y ∈ Submodule.span K' (Set.range b) := hsp ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hy
    exact ⟨c, fun Z => by rw [← key, hc, LinearEquiv.apply_symm_apply]⟩
end GlobalTheory.SectionBasis
