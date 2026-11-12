-- Prove2me | solution 1 for GeometricDL.WL.flavours_are_local
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T19:03:09.26742+00:00
-- url     : https://prove2.me/submissions/cb23665f-1c5f-435e-a623-f8645293f6dc

import Mathlib
import Definitions.Def_GeometricDL_WL_convLayer
import Definitions.Def_GeometricDL_WL_attnLayer
import Definitions.Def_GeometricDL_WL_mpLayer

universe w

open GeometricDL.WL in
theorem solution {H M A H' : Type*} [AddCommMonoid M] [Module ℝ M] {M' : Type*}
    (κ : H → H → ℕ → ℕ → ℝ) (a : H → H → ℝ) (ψ : H → M) (ψmp : H → H → M')
    (agg : Multiset M → A) (aggmp : Multiset M' → A) (φ : H → A → H') :
    (∃ Φ : H → Multiset (H × ℕ) → H', ∀ (V : Type w) [Fintype V] (E : V → V → Prop)
        [DecidableRel E] (h : V → H) (u : V),
        convLayer κ ψ agg φ E h u =
          Φ (h u) ((nbhd E u).val.map (fun v => (h v, (nbhd E v).card)))) ∧
    (∃ Φ : H → Multiset H → H', ∀ (V : Type w) [Fintype V] (E : V → V → Prop)
        [DecidableRel E] (h : V → H) (u : V),
        attnLayer a ψ agg φ E h u = Φ (h u) ((nbhd E u).val.map h)) ∧
    (∃ Φ : H → Multiset H → H', ∀ (V : Type w) [Fintype V] (E : V → V → Prop)
        [DecidableRel E] (h : V → H) (u : V),
        mpLayer ψmp aggmp φ E h u = Φ (h u) ((nbhd E u).val.map h)) := by
  refine ⟨⟨fun x X => φ x (agg (X.map (fun p => κ x p.1 (Multiset.card X) p.2 • ψ p.1))), ?_⟩,
    ⟨fun x X => φ x (agg (X.map (fun y => a x y • ψ y))), ?_⟩,
    ⟨fun x X => φ x (aggmp (X.map (ψmp x))), ?_⟩⟩
  · intro V _ E _ h u
    simp only [convLayer, Multiset.map_map, Multiset.card_map, Function.comp_def] <;> rfl
  · intro V _ E _ h u
    simp only [attnLayer, Multiset.map_map, Function.comp_def] <;> rfl
  · intro V _ E _ h u
    simp only [mpLayer, Multiset.map_map, Function.comp_def] <;> rfl
