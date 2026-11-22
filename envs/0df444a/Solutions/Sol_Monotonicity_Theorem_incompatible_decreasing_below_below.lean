-- Prove2me | solution 1 for Monotonicity_Theorem.incompatible_decreasing_below_below
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-11T18:38:19.011981+00:00
-- url     : https://prove2.me/submissions/ed9f4e88-b48c-443e-b59d-d264a3c4ccd6

import Definitions.Def_Monotonicity_Theorem_Framework

open Monotonicity_Theorem

-- Strict decrease on a finite subwindow inside (a,b) contradicts below_below.
theorem solution {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    {a b : Endpoint R} (hsubJ : forall x, openInterval D a b x -> I x)
    (hU : forall x (hxI : I x), openInterval D a b x ->
        exists c1 c2 : Power R 1, openInterval D a b c1 /\ openInterval D a b c2 /\
        Lt1 D c1 x /\ Lt1 D x c2 /\
        (forall y (hyI : I y), openInterval D a b y -> Lt1 D c1 y -> Lt1 D y x ->
          Lt1 D (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1) /\
        (forall y (hyI : I y), openInterval D a b y -> Lt1 D x y -> Lt1 D y c2 ->
          Lt1 D (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1))
    {u v : R} (huv : D.lt u v)
    (hsub : forall x, openInterval D (Endpoint.finite u) (Endpoint.finite v) x ->
      openInterval D a b x)
    (hdec : forall x (hxI : I x) y (hyI : I y),
      openInterval D (Endpoint.finite u) (Endpoint.finite v) x ->
      openInterval D (Endpoint.finite u) (Endpoint.finite v) y ->
      Lt1 D x y -> Lt1 D (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1) :
    False := by
  obtain ⟨r1, hxr1, hr1v⟩ := D.dense huv
  have hx0J : openInterval D (Endpoint.finite u) (Endpoint.finite v) (fun _ => r1) :=
    ⟨hxr1, hr1v⟩
  obtain ⟨r2, hxr2, hr2v⟩ := D.dense hr1v
  have hyJ : openInterval D (Endpoint.finite u) (Endpoint.finite v) (fun _ => r2) :=
    ⟨D.trans hxr1 hxr2, hr2v⟩
  have hx0I : I (fun _ => r1) := hsubJ _ (hsub _ hx0J)
  have hyI : I (fun _ => r2) := hsubJ _ (hsub _ hyJ)
  have hxy : Lt1 D (fun _ => r1) (fun _ => r2) := hxr2
  obtain ⟨c1, c2, hc1J, hc2J, hc1y, hyc2, hleft, hright⟩ :=
    hU (fun _ => r2) hyI (hsub _ hyJ)
  have hc1c : D.lt (Power.coord1 c1) r2 := hc1y
  have hpick : ∃ rr : R, D.lt (Power.coord1 (fun _ => r1)) rr ∧
      D.lt (Power.coord1 c1) rr ∧ D.lt rr r2 := by
    rcases D.trichotomy (Power.coord1 (fun _ => r1)) (Power.coord1 c1) with h | h | h
    · obtain ⟨hlt1, -, -⟩ := h
      obtain ⟨s, hs1, hs2⟩ := D.dense hc1c
      exact ⟨s, D.trans hlt1 hs1, hs1, hs2⟩
    · obtain ⟨heq, -, -⟩ := h
      obtain ⟨s, hs1, hs2⟩ := D.dense hc1c
      refine ⟨s, ?_, hs1, hs2⟩
      rw [heq]
      exact hs1
    · obtain ⟨hlt1, -, -⟩ := h
      obtain ⟨s, hs1, hs2⟩ := D.dense hxr2
      exact ⟨s, hs1, D.trans hlt1 hs1, hs2⟩
  obtain ⟨rr, hrr1, hrr2, hrr3⟩ := hpick
  have hzJ : openInterval D (Endpoint.finite u) (Endpoint.finite v) (fun _ => rr) :=
    ⟨D.trans hxr1 hrr1, D.trans hrr3 hr2v⟩
  have hzI : I (fun _ => rr) := hsubJ _ (hsub _ hzJ)
  have hzy : Lt1 D (fun _ => rr) (fun _ => r2) := hrr3
  have hdecZY : Lt1 D (f.toFun (Subtype.mk (fun _ => r2) hyI)).1
      (f.toFun (Subtype.mk (fun _ => rr) hzI)).1 :=
    hdec _ hzI _ hyI hzJ hyJ hzy
  have hwin : Lt1 D (f.toFun (Subtype.mk (fun _ => rr) hzI)).1
      (f.toFun (Subtype.mk (fun _ => r2) hyI)).1 := by
    have hzJab : openInterval D a b (fun _ => rr) := hsub _ hzJ
    have hc1z : Lt1 D c1 (fun _ => rr) := hrr2
    have hzyab : Lt1 D (fun _ => rr) (fun _ => r2) := hrr3
    exact hleft _ hzI hzJab hc1z hzyab
  exact D.irrefl _ (D.trans hdecZY hwin)
