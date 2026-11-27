-- Prove2me | solution 1 for GlobalTheory.UnipChange.factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:36:11.406698+00:00
-- url     : https://prove2.me/submissions/fb76812d-8ca0-4038-aa9f-159b8541c362

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitriangularMapInduction
import Theorems.Thm_GlobalTheory_UnipChange_mem_filt_of_map
import Theorems.Thm_GlobalTheory_UnipChange_continuous_linear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped Pointwise
open GlobalTheory GlobalTheory.UnipChange
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointRadical
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k]
  {r : ℕ} {b : Fin r → ℕ}
namespace GlobalTheory.UnipChange
theorem _root_.solution (L : lieRadical k b ≃ₗ[k] lieRadical k b)
    (hL : ∀ t (X : lieRadical k b), X.1 ∈ filt k b t → (L X).1 ∈ filt k b t)
    (f : radical k b → radical k b) (hf : Continuous f)
    (hd : ∀ t n n', (lg n - lg n').1 ∈ filt k b t →
      ((lg (f n) - L (lg n)) - (lg (f n') - L (lg n'))).1 ∈ filt k b (t + 1)) :
    ∃ (L' : (Pos b → k) ≃ₗ[k] Pos b → k) (g : (Pos b → k) → Pos b → k),
      LinearMap.det (L' : (Pos b → k) →ₗ[k] Pos b → k)
        = LinearMap.det (L : lieRadical k b →ₗ[k] lieRadical k b) ∧ Continuous g ∧
      (∀ x y i, (∀ j : Pos b, b j.1.2 - b j.1.1 < b i.1.2 - b i.1.1 → x j = y j) → g x i = g y i) ∧
      f ∘ chart k b = chart k b ∘ L' ∘ fun x => x + g x := by
  set L' : (Pos b → k) ≃ₗ[k] Pos b → k := ((coord k b).symm.trans L).trans (coord k b) with hL'
  refine ⟨L', fun x => L'.symm ((chart k b).symm (f (chart k b x))) - x, ?_, ?_, ?_, ?_⟩
  · exact LinearMap.det_conj (L : lieRadical k b →ₗ[k] lieRadical k b) (coord k b)
  · exact ((continuous_linear (L'.symm : (Pos b → k) →ₗ[k] Pos b → k)).comp
      ((chart k b).symm.continuous.comp (hf.comp (chart k b).continuous))).sub continuous_id
  · intro x y i hxy
    have h1 : (lg (chart k b x) - lg (chart k b y)).1 ∈ filt k b (b i.1.2 - b i.1.1) := by
      intro p q hpq
      by_cases h : b p < b q
      · have := hxy ⟨(p, q), h⟩ (by simp only; omega)
        show ((lg (unip _) - lg (unip _) : lieRadical k b) : Matrix (Fin r) (Fin r) k) p q = 0
        rw [lg_unip, lg_unip]
        simp [coord, h, this]
      · exact (lg (chart k b x) - lg (chart k b y)).2 p q h
    have h2 := mem_filt_of_map L hL (b i.1.2 - b i.1.1 + 1)
      ((L.symm (lg (f (chart k b x))) - lg (chart k b x))
        - (L.symm (lg (f (chart k b y))) - lg (chart k b y)))
      (by simpa only [map_sub, LinearEquiv.apply_symm_apply] using hd _ _ _ h1) i.1.1 i.1.2
      (by have := i.2; omega)
    have h3 : ∀ z, L'.symm ((chart k b).symm (f (chart k b z))) - z
        = coord k b (L.symm (lg (f (chart k b z))) - lg (chart k b z)) := by
      intro z
      have e : coord k b (lg (chart k b z)) = z := (chart k b).symm_apply_apply z
      rw [map_sub, e]
      congr 1
      show L'.symm (coord k b (lg (f (chart k b z)))) = _
      simp [hL']
    rw [← sub_eq_zero]
    simp only [h3]
    exact h2
  · funext x
    simp
end GlobalTheory.UnipChange
