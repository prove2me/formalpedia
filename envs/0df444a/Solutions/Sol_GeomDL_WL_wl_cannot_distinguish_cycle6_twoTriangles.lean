-- Prove2me | solution 1 for GeomDL.WL.wl_cannot_distinguish_cycle6_twoTriangles
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T19:53:52.356835+00:00
-- url     : https://prove2.me/submissions/49446d42-d5ca-4e90-8a5a-b1e3168d0d5b

import Mathlib
import Definitions.Def_WLIdentification
import Definitions.Def_GeomDL_WL_Defs

open GeomDL.WL OAI.WLIdentification

def regColor : (s : ℕ) → NeighborColor s
  | 0 => ()
  | s + 1 => ((regColor s, Multiset.replicate 2 (regColor s)) :
      NeighborColor s × Multiset (NeighborColor s))

theorem reg_color_aux (G : Graph)
    (hdeg : ∀ u, (Finset.univ.filter (fun w => G.edge u w = true)).card = 2) :
    ∀ s u, neighborColor G s u = regColor s := by
  intro s
  induction s with
  | zero => intro u; rfl
  | succ s ih =>
    intro u
    show ((neighborColor G s u,
        (Finset.univ.filter (fun w => G.edge u w = true)).val.map (neighborColor G s)) :
        NeighborColor s × Multiset (NeighborColor s)) =
      (regColor s, Multiset.replicate 2 (regColor s))
    rw [ih u, Multiset.map_congr rfl (fun v _ => ih v), Multiset.map_const', Finset.card_val, hdeg u]

theorem solution :
    (∀ s, neighborHistogram cycle6 s = neighborHistogram twoTriangles s) ∧
      ¬ Isomorphic cycle6 twoTriangles := by
  have d1 : ∀ u, (Finset.univ.filter (fun w => cycle6.edge u w = true)).card = 2 := by decide
  have d2 : ∀ u, (Finset.univ.filter (fun w => twoTriangles.edge u w = true)).card = 2 := by decide
  refine ⟨fun s => ?_, ?_⟩
  · simp only [neighborHistogram]
    rw [Multiset.map_congr rfl (fun v _ => reg_color_aux cycle6 d1 s v),
      Multiset.map_congr rfl (fun v _ => reg_color_aux twoTriangles d2 s v),
      Multiset.map_const', Multiset.map_const', Finset.card_val, Finset.card_val,
      Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
    rfl
  · rintro ⟨e, he⟩
    have notri : ∀ a b c : Fin cycle6.order,
        ¬ (cycle6.edge a b = true ∧ cycle6.edge b c = true ∧ cycle6.edge a c = true) := by
      decide
    let p0 : Fin twoTriangles.order := ⟨0, by decide⟩
    let p1 : Fin twoTriangles.order := ⟨1, by decide⟩
    let p2 : Fin twoTriangles.order := ⟨2, by decide⟩
    have t01 : twoTriangles.edge p0 p1 = true := by decide
    have t12 : twoTriangles.edge p1 p2 = true := by decide
    have t02 : twoTriangles.edge p0 p2 = true := by decide
    apply notri (e.symm p0) (e.symm p1) (e.symm p2)
    refine ⟨?_, ?_, ?_⟩
    · rw [he]; simpa using t01
    · rw [he]; simpa using t12
    · rw [he]; simpa using t02
