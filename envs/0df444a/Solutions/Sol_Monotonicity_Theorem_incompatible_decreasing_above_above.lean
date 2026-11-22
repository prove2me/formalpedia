-- Prove2me | solution 1 for Monotonicity_Theorem.incompatible_decreasing_above_above
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-11T16:05:28.232496+00:00
-- url     : https://prove2.me/submissions/a388db75-413a-4b4d-9cee-66fd0302469d

import Definitions.Def_Monotonicity_Theorem_Framework

open Monotonicity_Theorem

-- Strict decrease on a finite subwindow inside (a,b) contradicts above_above.
theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    {a b : Endpoint R} (hsubJ : forall x, openInterval D a b x -> I x)
    (hU : forall x (hxI : I x), openInterval D a b x ->
        exists c1 c2 : Power R 1, openInterval D a b c1 /\ openInterval D a b c2 /\
        Lt1 D c1 x /\ Lt1 D x c2 /\
        (forall y (hyI : I y), openInterval D a b y -> Lt1 D c1 y -> Lt1 D y x ->
          Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) /\
        (forall y (hyI : I y), openInterval D a b y -> Lt1 D x y -> Lt1 D y c2 ->
          Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1))
    {u v : R} (huv : D.lt u v)
    (hsub : forall x, openInterval D (Endpoint.finite u) (Endpoint.finite v) x ->
      openInterval D a b x)
    (hdec : forall x (hxI : I x) y (hyI : I y),
      openInterval D (Endpoint.finite u) (Endpoint.finite v) x ->
      openInterval D (Endpoint.finite u) (Endpoint.finite v) y ->
      Lt1 D x y -> Lt1 D (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1) :
    False := by
  obtain ⟨r1, hxr1, hr1v⟩ := D.dense huv
  have hxJ : openInterval D (Endpoint.finite u) (Endpoint.finite v) (fun _ => r1) :=
    ⟨hxr1, hr1v⟩
  have hxI : I (fun _ => r1) := hsubJ _ (hsub _ hxJ)
  obtain ⟨c1, c2, hc1J, hc2J, hc1x, hxc2, hleft, hright⟩ :=
    hU (fun _ => r1) hxI (hsub _ hxJ)
  have hxc2c : D.lt r1 (Power.coord1 c2) := hxc2
  have hpick : ∃ rr : R, D.lt r1 rr ∧ D.lt rr (Power.coord1 c2) ∧ D.lt rr v := by
    rcases D.trichotomy (Power.coord1 c2) v with h | h | h
    · obtain ⟨hlt1, -, -⟩ := h
      obtain ⟨s, hs1, hs2⟩ := D.dense hxc2c
      refine ⟨s, hs1, hs2, ?_⟩
      exact D.trans hs2 hlt1
    · obtain ⟨heq, -, -⟩ := h
      obtain ⟨s, hs1, hs2⟩ := D.dense hxc2c
      refine ⟨s, hs1, hs2, ?_⟩
      rw [← heq]
      exact hs2
    · obtain ⟨hlt1, -, -⟩ := h
      obtain ⟨s, hs1, hs2⟩ := D.dense hr1v
      exact ⟨s, hs1, D.trans hs2 hlt1, hs2⟩
  obtain ⟨rr, hrr1, hrr2, hrr3⟩ := hpick
  have hzJ : openInterval D (Endpoint.finite u) (Endpoint.finite v) (fun _ => rr) :=
    ⟨D.trans hxr1 hrr1, hrr3⟩
  have hzI : I (fun _ => rr) := hsubJ _ (hsub _ hzJ)
  have hxz : Lt1 D (fun _ => r1) (fun _ => rr) := hrr1
  have hdecXZ : Lt1 D (f.toFun (Subtype.mk (fun _ => rr) hzI)).1
      (f.toFun (Subtype.mk (fun _ => r1) hxI)).1 :=
    hdec _ hxI _ hzI hxJ hzJ hxz
  have hwin : Lt1 D (f.toFun (Subtype.mk (fun _ => r1) hxI)).1
      (f.toFun (Subtype.mk (fun _ => rr) hzI)).1 := by
    have hzJab : openInterval D a b (fun _ => rr) := hsub _ hzJ
    have hxzab : Lt1 D (fun _ => r1) (fun _ => rr) := hrr1
    have hzc2 : Lt1 D (fun _ => rr) c2 := hrr2
    exact hright _ hzI hzJab hxzab hzc2
  exact D.irrefl _ (D.trans hwin hdecXZ)
