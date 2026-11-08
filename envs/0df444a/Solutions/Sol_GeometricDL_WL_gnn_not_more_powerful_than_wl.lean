-- Prove2me | solution 1 for GeometricDL.WL.gnn_not_more_powerful_than_wl
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T19:22:54.700676+00:00
-- url     : https://prove2.me/submissions/f2fa94a2-c2e8-48a9-8465-e3487a4a3e44

import Mathlib
import Definitions.Def_GeometricDL_WL_WLIndistinguishable
import Definitions.Def_GeometricDL_WL_LocalGNN_state

set_option autoImplicit false

universe u v

namespace GeometricDL.WL

/-- From a WL colour after `ℓ + 1` rounds, read off the GNN state after `ℓ` layers together with the
node's degree. -/
def gnnOfWL {F : Type u} (N : LocalGNN.{u, v} F) : (ℓ : ℕ) → WLColor F (ℓ + 1) → N.H ℓ × ℕ
  | 0 => fun (c : WLColor F 0 × Multiset (WLColor F 0)) => (N.enc c.1, Multiset.card c.2)
  | ℓ + 1 => fun (c : WLColor F (ℓ + 1) × Multiset (WLColor F (ℓ + 1))) =>
      (N.layer ℓ (gnnOfWL N ℓ c.1).1 (c.2.map (gnnOfWL N ℓ)), Multiset.card c.2)

theorem gnnOfWL_spec {F : Type u} (N : LocalGNN.{u, v} F) {V : Type*} [Fintype V]
    (E : V → V → Prop) [DecidableRel E] (x : V → F) (ℓ : ℕ) :
    ∀ w : V, gnnOfWL N ℓ (wlColor E x (ℓ + 1) w) = (N.state E x ℓ w, (nbhd E w).card) := by
  induction ℓ with
  | zero =>
    intro w
    change (N.enc (x w), Multiset.card ((nbhd E w).val.map (wlColor E x 0))) =
      (N.enc (x w), (nbhd E w).card)
    rw [Multiset.card_map]
    rfl
  | succ ℓ ih =>
    intro w
    have hc : gnnOfWL N ℓ ∘ wlColor E x (ℓ + 1) = fun v => (N.state E x ℓ v, (nbhd E v).card) :=
      funext ih
    change (N.layer ℓ (gnnOfWL N ℓ (wlColor E x (ℓ + 1) w)).1
          (((nbhd E w).val.map (wlColor E x (ℓ + 1))).map (gnnOfWL N ℓ)),
          Multiset.card ((nbhd E w).val.map (wlColor E x (ℓ + 1)))) =
        (N.layer ℓ (N.state E x ℓ w)
          ((nbhd E w).val.map (fun v => (N.state E x ℓ v, (nbhd E v).card))), (nbhd E w).card)
    rw [Multiset.map_map, Multiset.card_map, hc, ih w]
    rfl

theorem state_map_eq {F : Type u} (N : LocalGNN.{u, v} F) {V : Type*} [Fintype V]
    (E : V → V → Prop) [DecidableRel E] (x : V → F) (L : ℕ) :
    (Finset.univ : Finset V).val.map (N.state E x L) =
      ((Finset.univ : Finset V).val.map (wlColor E x (L + 1))).map (fun c => (gnnOfWL N L c).1) := by
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl (fun w _ => ?_)
  show N.state E x L w = (gnnOfWL N L (wlColor E x (L + 1) w)).1
  rw [gnnOfWL_spec]

end GeometricDL.WL

open GeometricDL.WL in
theorem solution {F : Type u} {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    (E₁ : V₁ → V₁ → Prop) [DecidableRel E₁] (x₁ : V₁ → F)
    (E₂ : V₂ → V₂ → Prop) [DecidableRel E₂] (x₂ : V₂ → F)
    (hWL : WLIndistinguishable E₁ x₁ E₂ x₂) (N : LocalGNN.{u, v} F) (L : ℕ) :
    (Finset.univ : Finset V₁).val.map (N.state E₁ x₁ L) =
      (Finset.univ : Finset V₂).val.map (N.state E₂ x₂ L) := by
  rw [state_map_eq N E₁ x₁ L, state_map_eq N E₂ x₂ L, hWL (L + 1)]
