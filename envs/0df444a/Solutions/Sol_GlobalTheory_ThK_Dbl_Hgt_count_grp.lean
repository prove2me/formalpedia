-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.Hgt.count_grp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:34:03.656644+00:00
-- url     : https://prove2.me/submissions/6445da70-aac6-4424-99aa-ff331b9b3bcb

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_HgtCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Hgt
open scoped NNReal ENNReal
open MeasureTheory Topology
namespace GlobalTheory.ThK.Dbl.Hgt
theorem _root_.solution {R B κ : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Ring B] [Algebra R B] [TopologicalSpace B]
    [IsTopologicalRing B] [T2Space B] [Fintype κ] (c : B ≃ₗ[R] (κ → R)) (hc : Continuous c) (hc' : Continuous c.symm)
    (H : Subgroup Bˣ) (hH : IsClosed (H : Set Bˣ)) {Ω : Set B} (hΩ : IsCompact Ω) {W : Set R} (hW : IsCompact W) :
    ∃ (X : Set R) (U : Set H), IsCompact X ∧ IsCompact U ∧ ∀ (l : Rˣ) (s : Finset R),
      (∀ x ∈ X, ∃ y ∈ s, ∃ w ∈ W, x - y = l * l * w) → ∀ [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant],
        μ {g | l.1 • g.1.1 ∈ Ω ∧ l.1 • (g⁻¹).1.1 ∈ Ω} ≤ (s.card : ℝ≥0∞) ^ Fintype.card κ * μ U := by
  classical
  let W' : Set ((κ → R) × (κ → R)) := (Set.univ.pi fun _ => W) ×ˢ Set.univ.pi fun _ => W
  let Ω' : Set B := (fun y : B × (κ → R) × (κ → R) => 1 + y.1 * c.symm (y.2.1 - y.2.2)) '' Ω ×ˢ W'
  have hΩ' : IsCompact Ω' := (hΩ.prod ((isCompact_univ_pi fun _ => hW).prod (isCompact_univ_pi fun _ => hW))).image (by fun_prop)
  have em : IsClosedEmbedding (fun k : H => Units.embedProduct B k.1) :=
    Units.isClosedEmbedding_embedProduct.comp hH.isClosedEmbedding_subtypeVal
  refine ⟨⋃ k, (fun y => c y k) '' Ω, _, isCompact_iUnion fun k => hΩ.image (by fun_prop),
    em.isCompact_preimage (hΩ'.prod (hΩ'.image MulOpposite.continuous_op)), fun l s hs _ _ μ _ => ?_⟩
  let S : (κ → R) → Set H := fun y => {g | l.1 • (g⁻¹).1.1 ∈ Ω ∧ ∀ k, ∃ w ∈ W, c (l.1 • g.1.1) k - y k = l * l * w}
  have key : ∀ y, ∀ g ∈ S y, ∀ g' ∈ S y, (g⁻¹ * g').1.1 ∈ Ω' := fun y g hg g' hg' => by
    choose w hw e using hg.2
    choose w' hw' e' using hg'.2
    refine ⟨(_, w', w), ⟨hg.1, fun k _ => hw' k, fun k _ => hw k⟩, ?_⟩
    have e1 : g'.1.1 - g.1.1 = l.1 • c.symm (w' - w) := by
      refine c.injective (funext fun k => l.isUnit.mul_left_cancel ?_)
      have := e k
      have := e' k
      simp only [map_smul, map_sub, LinearEquiv.apply_symm_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at *
      linear_combination e' k - e k
    change 1 + l.1 • (g.1⁻¹).1 * c.symm (w' - w) = (g.1⁻¹).1 * g'.1.1
    rw [smul_mul_assoc, ← mul_smul_comm, ← e1, mul_sub, Units.inv_mul, add_sub_cancel]
  refine (measure_mono (t := ⋃ y ∈ Fintype.piFinset fun _ : κ => s, S y) fun g hg => ?_).trans
    ((measure_biUnion_finset_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (μ ((fun k : H => Units.embedProduct B k.1) ⁻¹'
      Ω' ×ˢ (MulOpposite.op '' Ω'))) fun y _ => ?_).trans_eq (by simp)))
  · choose y hy hy' using fun k => hs _ (Set.mem_iUnion.2 ⟨k, _, hg.1, rfl⟩)
    exact Set.mem_iUnion₂.2 ⟨y, Fintype.mem_piFinset.2 hy, hg.2, hy'⟩
  · rcases (S y).eq_empty_or_nonempty with e | ⟨g, hg⟩
    · simp [e]
    · refine (measure_mono ?_).trans_eq (measure_preimage_mul μ g⁻¹ _)
      exact fun g' hg' => ⟨key y g hg g' hg', _, key y g' hg' g hg, by simp⟩
end GlobalTheory.ThK.Dbl.Hgt
