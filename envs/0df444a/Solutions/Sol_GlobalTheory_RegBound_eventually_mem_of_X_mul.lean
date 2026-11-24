-- Prove2me | solution 1 for GlobalTheory.RegBound.eventually_mem_of_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:55:13.554361+00:00
-- url     : https://prove2.me/submissions/9d9858a1-acc0-48ae-8d95-fd7d55c02f6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
namespace GlobalTheory.RegBound
theorem _root_.solution [Finite σ] {J L : Ideal (MvPolynomial σ K)}
    (hJ : ∀ F ∈ J, ∀ e, homogeneousComponent e F ∈ J) (hL : ∀ F ∈ L, ∀ i, X i * F ∈ J) :
    ∀ᶠ e in atTop, ∀ F ∈ L, F.IsHomogeneous e → F ∈ J := by
  obtain ⟨T, hT⟩ := IsNoetherian.noetherian L
  have key : ∀ A G, G ∈ L → (A - C (coeff 0 A)) * G ∈ J := by
    intro A G hG
    induction A using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq =>
      convert J.add_mem hp hq using 1
      simp only [coeff_add, map_add]; ring
    | mul_X p i _ =>
      have : coeff 0 (p * X i) = 0 := by
        have := map_mul (constantCoeff (σ := σ) (R := K)) p (X i)
        simpa [constantCoeff_eq] using this
      rw [this, map_zero, sub_zero, mul_assoc]
      exact J.mul_mem_left _ (hL G hG i)
  have key2 : ∀ F ∈ Submodule.span (MvPolynomial σ K) (T : Set (MvPolynomial σ K)),
      ∃ G ∈ L, G.totalDegree ≤ T.sup totalDegree ∧ F - G ∈ J := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem x hx => exact ⟨x, hT ▸ Submodule.subset_span hx, Finset.le_sup hx, by simp⟩
    | zero => exact ⟨0, L.zero_mem, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨G, h1, h2, h3⟩ := hx
      obtain ⟨G', h1', h2', h3'⟩ := hy
      refine ⟨G + G', L.add_mem h1 h1', (totalDegree_add _ _).trans (max_le h2 h2'), ?_⟩
      convert J.add_mem h3 h3' using 1
      ring
    | smul A x _ hx =>
      obtain ⟨G, h1, h2, h3⟩ := hx
      refine ⟨C (coeff 0 A) * G, L.mul_mem_left _ h1, ?_, ?_⟩
      · exact (totalDegree_mul _ _).trans (by simpa using h2)
      · convert J.add_mem (J.mul_mem_left A h3) (key A G h1) using 1
        rw [smul_eq_mul]; ring
  filter_upwards [eventually_gt_atTop (T.sup totalDegree)] with e he F hF hFe
  obtain ⟨G, -, h2, h3⟩ := key2 F (hT ▸ hF)
  have := hJ _ h3 e
  rwa [map_sub, homogeneousComponent_eq_self hFe,
    homogeneousComponent_eq_zero _ _ (h2.trans_lt he), sub_zero] at this
end GlobalTheory.RegBound
