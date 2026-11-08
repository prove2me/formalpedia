-- Prove2me | solution 2 for GeometricDL.WL.gnn_not_more_powerful_than_wl
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:25:48.882773+00:00
-- url     : https://prove2.me/submissions/e31e9629-bf20-45e3-9c8f-ea246ae413a7

import Mathlib
import Definitions.Def_GeometricDL_WL_WLIndistinguishable
import Definitions.Def_GeometricDL_WL_LocalGNN_state

universe u v

namespace Aux_GNNWL

open GeometricDL.WL

/-- View a round-`ℓ+1` WL colour as a pair. -/
def un {F : Type u} (ℓ : ℕ) (c : WLColor F (ℓ + 1)) : WLColor F ℓ × Multiset (WLColor F ℓ) := c

/-- Read off the GNN state at layer `ℓ` from a WL colour at round `ℓ + 1`. -/
def hf {F : Type u} (N : LocalGNN.{u, v} F) : (ℓ : ℕ) → WLColor F (ℓ + 1) → N.H ℓ
  | 0 => fun c => N.enc (un 0 c).1
  | ℓ + 1 => fun c =>
      N.layer ℓ (hf N ℓ (un (ℓ + 1) c).1)
        ((un (ℓ + 1) c).2.map (fun c' => (hf N ℓ c', Multiset.card (un ℓ c').2)))

lemma state_eq {F : Type u} (N : LocalGNN.{u, v} F) {V : Type*} [Fintype V]
    (E : V → V → Prop) [DecidableRel E] (x : V → F) :
    ∀ (ℓ : ℕ) (w : V), N.state E x ℓ w = hf N ℓ (wlColor E x (ℓ + 1) w) := by
  intro ℓ
  induction ℓ with
  | zero => intro w; rfl
  | succ ℓ ih =>
    intro w
    have hc : ∀ y : V, Multiset.card (un ℓ (wlColor E x (ℓ + 1) y)).2 = (nbhd E y).card := by
      intro y
      show Multiset.card ((nbhd E y).val.map (wlColor E x ℓ)) = _
      rw [Multiset.card_map]
      rfl
    show N.layer ℓ (N.state E x ℓ w)
        ((nbhd E w).val.map (fun y => (N.state E x ℓ y, (nbhd E y).card))) =
      N.layer ℓ (hf N ℓ (wlColor E x (ℓ + 1) w))
        (((nbhd E w).val.map (wlColor E x (ℓ + 1))).map
          (fun c' => (hf N ℓ c', Multiset.card (un ℓ c').2)))
    rw [ih w, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro y _
    simp only [Function.comp_apply]
    rw [ih y, hc y]

end Aux_GNNWL

open GeometricDL.WL in
theorem solution {F : Type u} {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    (E₁ : V₁ → V₁ → Prop) [DecidableRel E₁] (x₁ : V₁ → F)
    (E₂ : V₂ → V₂ → Prop) [DecidableRel E₂] (x₂ : V₂ → F)
    (hWL : WLIndistinguishable E₁ x₁ E₂ x₂) (N : LocalGNN.{u, v} F) (L : ℕ) :
    (Finset.univ : Finset V₁).val.map (N.state E₁ x₁ L) =
      (Finset.univ : Finset V₂).val.map (N.state E₂ x₂ L) := by
  calc (Finset.univ : Finset V₁).val.map (N.state E₁ x₁ L)
      = ((Finset.univ : Finset V₁).val.map (wlColor E₁ x₁ (L + 1))).map (Aux_GNNWL.hf N L) := by
        rw [Multiset.map_map]
        congr 1
        funext w
        exact Aux_GNNWL.state_eq N E₁ x₁ L w
    _ = ((Finset.univ : Finset V₂).val.map (wlColor E₂ x₂ (L + 1))).map (Aux_GNNWL.hf N L) := by
        rw [hWL (L + 1)]
    _ = (Finset.univ : Finset V₂).val.map (N.state E₂ x₂ L) := by
        rw [Multiset.map_map]
        congr 1
        funext w
        exact (Aux_GNNWL.state_eq N E₂ x₂ L w).symm
