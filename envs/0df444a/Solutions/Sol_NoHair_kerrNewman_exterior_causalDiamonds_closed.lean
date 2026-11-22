-- Prove2me | solution 1 for NoHair.kerrNewman_exterior_causalDiamonds_closed
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T20:43:37.149044+00:00
-- url     : https://prove2.me/submissions/2618ae7d-832b-4777-ad42-1e787b60755e

import Theorems.Thm_NoHair_kerrNewman_exterior_diamondCurveConfinement
import Theorems.Thm_NoHair_kerrNewman_exterior_compactLimitCurve

open NoHair Set

theorem solution (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    let U := kerrNewmanSpacetime a
    let D := (Subtype.val : U → E4) ⁻¹' kerrNewmanDOC m a e
    ∀ p ∈ D, ∀ q ∈ D, IsClosed ((Subtype.val : U → E4) ''
      (causalFuture (kerrNewmanMetricField m a e) T D p ∩ causalPast (kerrNewmanMetricField m a e) T D q)) := by
  dsimp only
  intro p hpD q hqD
  let U := kerrNewmanSpacetime a
  let g := kerrNewmanMetricField m a e
  let D := (Subtype.val : U → E4) ⁻¹' kerrNewmanDOC m a e
  let E := causalFuture g T D p ∩ causalPast g T D q
  obtain ⟨K,hK,hKD,hpK,hqK,hconf⟩ := kerrNewman_exterior_diamondCurveConfinement m a e hp T hT p hpD q hqD
  let J : Set (U × U) := {z | z.1 ∈ K ∧ z.2 ∈ K ∧ z.2 ∈ causalFuture g T K z.1}
  let B : Set U := (fun x => (p,x)) ⁻¹' closure J ∩ (fun x => (x,q)) ⁻¹' closure J
  have hB : IsClosed B := (isClosed_closure.preimage (continuous_const.prodMk continuous_id)).inter
    (isClosed_closure.preimage (continuous_id.prodMk continuous_const))
  have hlim := kerrNewman_exterior_compactLimitCurve m a e hp T hT K hK hKD
  have hE : E = K ∩ B := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxK,hpx,hxq⟩ := hconf x hx
      exact ⟨hxK,subset_closure (show (p,x) ∈ J from ⟨hpK,hxK,hpx⟩),
        subset_closure (show (x,q) ∈ J from ⟨hxK,hqK,hxq⟩)⟩
    · rintro ⟨_,hx,hx'⟩
      exact ⟨hlim (show (p,x) ∈ closure J from hx),hlim (show (x,q) ∈ closure J from hx')⟩
  change IsClosed ((Subtype.val : U → E4) '' E)
  rw [hE]
  exact ((hK.inter_right hB).image continuous_subtype_val).isClosed
