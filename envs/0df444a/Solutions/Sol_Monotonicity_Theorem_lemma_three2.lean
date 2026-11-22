-- Prove2me | solution 1 for Monotonicity_Theorem.lemma_three2
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-15T15:39:48.626179+00:00
-- url     : https://prove2.me/submissions/d3dfb327-9d87-4731-be61-5d53cee54b94

import Definitions.Def_Monotonicity_Theorem_Framework2
import Theorems.Thm_Monotonicity_Theorem_infinite_definable_set_contains_interval2
import Mathlib.Order.Interval.Set.Infinite

open Monotonicity_Theorem
open Classical

theorem Monotonicity_Theorem.interval_is_infinite {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (a b : R) (hab : LT.lt a b) :
    Set.Infinite (openInterval (Endpoint.finite a) (Endpoint.finite b)) := by
  have hIoo : (Set.Ioo a b).Infinite := Set.Ioo_infinite hab
  have hInj : Set.InjOn (fun r : R => (fun _ => r : Power R 1)) (Set.Ioo a b) := by
    intro r1 _ r2 _ h
    exact congrArg (fun p : Power R 1 => p 0) h
  have hImg := hIoo.image hInj
  apply hImg.mono
  intro x hx
  obtain ⟨r, hrIoo, hrx⟩ := hx
  obtain ⟨hax, hxb⟩ := Set.mem_Ioo.mp hrIoo
  have e : x = (fun _ => r) := hrx.symm
  rw [e]
  exact ⟨hax, hxb⟩


namespace Monotonicity_Theorem

theorem appendLeftAux3 {R : Type} (x : Power R 1) (y : Power R 1) :
    Power.left (R := R) (n := 1) (m := 1) (Power.append x y) = x := by
  funext i
  simp [Power.left, Power.append, Fin.append_left]

theorem appendRightAux3 {R : Type} (x : Power R 1) (y : Power R 1) :
    Power.right (R := R) (n := 1) (m := 1) (Power.append x y) = y := by
  funext j
  exact Fin.append_right x y j

def swapIndexAux3 (i : Fin (1 + 1)) : Fin (1 + 1) :=
  if h : (i : Nat) < 1 then
    Fin.natAdd 1 (Fin.mk (i : Nat) h)
  else
    Fin.castAdd 1 (Fin.mk ((i : Nat) - 1) (by omega))

theorem swapLambdaAppend3 {R : Type} (y : Power R 1) (x : Power R 1) :
    (fun i => (Power.append y x) (swapIndexAux3 i)) = Power.append x y := by
  funext i
  by_cases h : (i : Nat) < 1
  · let im : Fin 1 := Fin.mk (i : Nat) h
    have hi : i = Fin.castAdd 1 im := by
      ext
      simp [im]
    have hidx : swapIndexAux3 i = Fin.natAdd 1 im := by
      simp [swapIndexAux3, h, im]
    calc
      (Power.append y x) (swapIndexAux3 i)
          = (Power.append y x) (Fin.natAdd 1 im) := by
              rw [hidx]
      _ = x im :=
              Fin.append_right y x im
      _ = (Power.append x y) (Fin.castAdd 1 im) :=
              (Fin.append_left x y im).symm
      _ = (Power.append x y) i := by
              rw [hi]
  · let jn : Fin 1 := Fin.mk ((i : Nat) - 1) (by omega)
    have hi : i = Fin.natAdd 1 jn := by
      ext
      simp [jn]
      omega
    have hidx : swapIndexAux3 i = Fin.castAdd 1 jn := by
      simp [swapIndexAux3, h, jn]
    calc
      (Power.append y x) (swapIndexAux3 i)
          = (Power.append y x) (Fin.castAdd 1 jn) := by
              rw [hidx]
      _ = y jn :=
              Fin.append_left y x jn
      _ = (Power.append x y) (Fin.natAdd 1 jn) :=
              (Fin.append_right x y jn).symm
      _ = (Power.append x y) i := by
              rw [hi]

-- The image of a definable function is definable.
theorem imageDefinableAux3 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R) {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) :
    M.S 1 (fun y : Power R 1 => ∃ x : Power R 1, ∃ hx : I x,
      (f.toFun (Subtype.mk x hx)).1 = y) := by
  have hSwap : M.S (1 + 1)
      (fun yx : Power R (1 + 1) =>
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun i => yx (swapIndexAux3 i))) :=
    M.reindex_mem swapIndexAux3 f.graph_mem
  have hProj : M.S 1
      (fun y : Power R 1 => ∃ x : Power R 1,
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun i => (Power.append y x) (swapIndexAux3 i))) :=
    M.existsLast_mem hSwap
  have heq : (fun y : Power R 1 => ∃ x : Power R 1,
        FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
          (fun i => (Power.append y x) (swapIndexAux3 i)))
      = (fun y : Power R 1 => ∃ x : Power R 1, ∃ hx : I x,
        (f.toFun (Subtype.mk x hx)).1 = y) := by
    funext y
    apply propext
    constructor
    · intro ⟨x, hG⟩
      have happ : (fun i => (Power.append y x) (swapIndexAux3 i))
          = Power.append x y :=
        swapLambdaAppend3 y x
      rw [happ] at hG
      obtain ⟨hx0, hEq0⟩ := hG
      have eL : Power.left (R := R) (n := 1) (m := 1) (Power.append x y) = x :=
        appendLeftAux3 x y
      have eR : Power.right (R := R) (n := 1) (m := 1) (Power.append x y) = y :=
        appendRightAux3 x y
      have hx : I x := by rw [← eL]; exact hx0
      have hSub : (⟨Power.left (Power.append x y), hx0⟩ : {x : Power R 1 // I x})
          = (⟨x, hx⟩ : {x : Power R 1 // I x}) := Subtype.ext eL
      have hEq1 : (Power.right (Power.append x y) : Power R 1)
          = ((f.toFun (⟨x, hx⟩ : {x : Power R 1 // I x})).1 : Power R 1) := by
        rw [hSub] at hEq0
        exact hEq0
      refine ⟨x, hx, ?_⟩
      have h1 : ((f.toFun (⟨x, hx⟩ : {x : Power R 1 // I x})).1 : Power R 1)
          = (Power.right (Power.append x y) : Power R 1) := hEq1.symm
      rw [eR] at h1
      exact h1
    · intro ⟨x, hx, hEq⟩
      have happ : (fun i => (Power.append y x) (swapIndexAux3 i))
          = Power.append x y :=
        swapLambdaAppend3 y x
      have eL : Power.left (R := R) (n := 1) (m := 1) (Power.append x y) = x :=
        appendLeftAux3 x y
      have eR : Power.right (R := R) (n := 1) (m := 1) (Power.append x y) = y :=
        appendRightAux3 x y
      refine ⟨x, ?_⟩
      rw [happ]
      have hWit : I (Power.left (Power.append x y)) := by
        rw [eL]
        exact hx
      have hSub2 : (⟨x, hx⟩ : {x : Power R 1 // I x})
          = (⟨Power.left (Power.append x y), hWit⟩
            : {x : Power R 1 // I x}) := Subtype.ext eL.symm
      have hEqW : (Power.right (Power.append x y) : Power R 1)
          = ((f.toFun (⟨Power.left (Power.append x y), hWit⟩
            : {x : Power R 1 // I x})).1 : Power R 1) := by
        rw [eR, ← hSub2]
        exact hEq.symm
      exact ⟨hWit, hEqW⟩
  rw [heq] at hProj
  exact hProj

theorem loTrans3 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R] (a : Endpoint R)
    {c d : R} (h : Endpoint.lt a (Endpoint.finite c)) (hlt : LT.lt c d) :
    Endpoint.lt a (Endpoint.finite d) := by
  cases a with
  | negInf => exact trivial
  | finite val => exact lt_trans h hlt
  | posInf => exact False.elim h

theorem hiTrans3 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R] (b : Endpoint R)
    {c d : R} (h : Endpoint.lt (Endpoint.finite d) b) (hlt : LT.lt c d) :
    Endpoint.lt (Endpoint.finite c) b := by
  cases b with
  | negInf => exact False.elim h
  | finite val => exact lt_trans hlt h
  | posInf => exact trivial

theorem ptEqAux3 {R : Type} {p q : Power R 1}
    (h : Power.coord1 p = Power.coord1 q) : p = q := by
  funext i
  have hiv : i.val < 1 := i.isLt
  have hi0 : i.val = 0 := by omega
  have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext hi0
  rw [hi]
  exact h

theorem ptLam3 {R : Type} (x : Power R 1) : x = fun _ => Power.coord1 x := by
  funext k
  have hk : k.val = 0 := by
    have := k.isLt
    omega
  have ek : k = (⟨0, by decide⟩ : Fin 1) := Fin.ext hk
  rw [ek]
  rfl

-- Restriction of a definable function to a definable subset of its domain.
theorem restrictDefAux3 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    {M : OMinimalStructure R} {I B : Set (Power R 1)}
    (f : DefinableFunction M I B)
    (A' : Set (Power R 1)) (hA' : M.S 1 A') (hsub : A'.Subset I) :
    ∃ f' : DefinableFunction M A' B,
      ∀ x (hx' : A' x), f'.toFun (Subtype.mk x hx') = f.toFun (Subtype.mk x (hsub hx')) := by
  refine ⟨⟨hA', f.codomain_mem, (fun x => f.toFun ⟨x.1, hsub x.2⟩), ?_⟩, fun x hx' => rfl⟩
  have heq : FunctionGraph (fun x : {x : Power R 1 // A' x} => f.toFun ⟨x.1, hsub x.2⟩)
      = ({z : Power R (1 + 1) | A' (Power.left z)} ∩
        (FunctionGraph f.toFun)) := by
    funext z
    apply propext
    constructor
    · intro h
      obtain ⟨hx', heq0⟩ := h
      refine ⟨hx', ?_⟩
      exact ⟨hsub hx', heq0⟩
    · intro h
      obtain ⟨ha', hx, heq0⟩ := h
      refine ⟨ha', ?_⟩
      have hrfl : (f.toFun ⟨Power.left z, hsub ha'⟩).1 = (f.toFun ⟨Power.left z, hx⟩).1 := rfl
      rw [hrfl]
      exact heq0
  rw [heq]
  exact M.inter_mem (M.reindex_mem (Fin.castAdd 1) hA') f.graph_mem

-- Value extraction from graph membership.
theorem graphValAux3 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    {M : OMinimalStructure R} {I B : Set (Power R 1)}
    (f : DefinableFunction M I B) (p' wp' : Power R 1) (hI : I p')
    (hG : FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun
      (Power.append p' wp')) :
    Power.coord1 wp' = Power.coord1 ((f.toFun (Subtype.mk p' hI)).1) := by
  obtain ⟨hx0, heq0⟩ := hG
  have eL : Power.left (Power.append p' wp') = p' := appendLeftAux3 _ _
  have eR : Power.right (Power.append p' wp') = wp' := appendRightAux3 _ _
  have heq1 : wp' = (f.toFun (Subtype.mk p' hI)).1 := by
    calc wp' = Power.right (Power.append p' wp') := eR.symm
      _ = (f.toFun (Subtype.mk (Power.left (Power.append p' wp')) hx0)).1 := heq0
      _ = (f.toFun (Subtype.mk p' hI)).1 := by simp only [eL]
  rw [heq1]

-- A window strictly between endpoints is nonempty given any ambient point.
theorem nonemptyWinAux3 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    {c d : Endpoint R} (hlt : Endpoint.lt c d) (p₀ : Power R 1) :
    (openInterval c d).Nonempty := by
  cases c with
  | negInf =>
    cases d with
    | negInf => exact False.elim hlt
    | finite val =>
      obtain ⟨y, hym⟩ := exists_lt val
      exact ⟨fun _ => y, trivial, hym⟩
    | posInf => exact ⟨p₀, trivial, trivial⟩
  | finite val =>
    cases d with
    | negInf => exact False.elim hlt
    | finite val2 =>
      have hlt2 : LT.lt val val2 := hlt
      obtain ⟨y, hy1, hy2⟩ := exists_between hlt2
      exact ⟨fun _ => y, hy1, hy2⟩
    | posInf =>
      obtain ⟨y, hym⟩ := exists_gt val
      exact ⟨fun _ => y, hym, trivial⟩
  | posInf => exact False.elim hlt

-- An infinite set is nonempty.
theorem nonEmptyOfInfinite3 {R : Type} {A : Set (Power R 1)} (hInf : Set.Infinite A) :
    ∃ x, A x := by
  by_contra hcon
  apply hInf
  apply Set.finite_empty.subset
  intro x hx
  exact False.elim (hcon ⟨x, hx⟩)

-- A window strictly between endpoints contains two ordered points.
theorem twoPointsInWin3 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (a b : Endpoint R) (hab : Endpoint.lt a b) (p₀ : Power R 1) :
    ∃ u v : R, Endpoint.lt a (Endpoint.finite u) ∧ LT.lt u v ∧
      Endpoint.lt (Endpoint.finite v) b := by
  obtain ⟨m, hm⟩ := nonemptyWinAux3 hab p₀
  obtain ⟨r, hr⟩ := nonemptyWinAux3 (c := a) (d := Endpoint.finite (Power.coord1 m)) hm.left p₀
  have hr1 : LT.lt (Power.coord1 r) (Power.coord1 m) := hr.right
  have hm2 : Endpoint.lt (Endpoint.finite (Power.coord1 m)) b := hm.right
  refine ⟨Power.coord1 r, Power.coord1 m, hr.left, hr1, ?_⟩
  exact hm2

end Monotonicity_Theorem

open Monotonicity_Theorem

theorem solution {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R] (M : OMinimalStructure R)
    {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (hmono : StrictlyMonotoneOn I B f.toFun) (hI : Set.Infinite I) :
    ∃ a b : Endpoint R, Endpoint.lt a b ∧
      (openInterval a b).Subset I ∧
      (openInterval a b).Subset (ContinuousPoints I
        (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) := by
  obtain ⟨pI, hpI⟩ := nonEmptyOfInfinite3 hI
  obtain ⟨a0, b0, hlt0, hsub0⟩ :=
    Monotonicity_Theorem.infinite_definable_set_contains_interval2 M I f.domain_mem hI
  obtain ⟨u, v, hu_lo, huv, hv_hi⟩ := twoPointsInWin3 a0 b0 hlt0 pI
  set W : Set (Power R 1) := openInterval (Endpoint.finite u) (Endpoint.finite v) with hWdef
  have hWmem : M.S 1 W :=
    (M.ominimal _).mpr (FiniteUnionOfPointsAndIntervals.interval _ _)
  have hWsub : W.Subset I := by
    intro x hx
    have hxL : LT.lt u (Power.coord1 x) := hx.left
    have hxR : LT.lt (Power.coord1 x) v := hx.right
    exact hsub0 ⟨loTrans3 a0 hu_lo hxL, hiTrans3 b0 hv_hi hxR⟩
  have hWinf : Set.Infinite W :=
    Monotonicity_Theorem.interval_is_infinite u v huv
  obtain ⟨g, hagree⟩ := restrictDefAux3 f W hWmem hWsub
  have gval : ∀ x (hx : W x),
      (g.toFun ⟨x, hx⟩).1 = (f.toFun ⟨x, hWsub hx⟩).1 :=
    fun x hx => congrArg Subtype.val (hagree x hx)
  rcases hmono with hinc | hdec
  · -- Strictly increasing case.
    have hincW : StrictlyIncreasingOn W B g.toFun := by
      intro x y hx hy hlt
      have h := hinc x y (hWsub hx) (hWsub hy) hlt
      rw [gval x hx, gval y hy]
      exact h
    have hinjW : ∀ x y (hx : W x) (hy : W y),
        (g.toFun ⟨x, hx⟩).1 = (g.toFun ⟨y, hy⟩).1 → x = y := by
      intro x y hx hy hval
      have hc : Power.coord1 ((g.toFun ⟨x, hx⟩).1)
          = Power.coord1 ((g.toFun ⟨y, hy⟩).1) := congrArg _ hval
      rcases lt_trichotomy (Power.coord1 x) (Power.coord1 y) with h | h | h
      · have hlt := h
        have hcon : LT.lt (Power.coord1 ((g.toFun ⟨x, hx⟩).1))
            (Power.coord1 ((g.toFun ⟨y, hy⟩).1)) := hincW x y hx hy hlt
        rw [hc] at hcon
        exact False.elim (lt_irrefl _ hcon)
      · have heq := h
        exact ptEqAux3 heq
      · have hlt := h
        have hcon : LT.lt (Power.coord1 ((g.toFun ⟨y, hy⟩).1))
            (Power.coord1 ((g.toFun ⟨x, hx⟩).1)) := hincW y x hy hx hlt
        rw [← hc] at hcon
        exact False.elim (lt_irrefl _ hcon)
    set Img : Set (Power R 1) :=
      fun y => ∃ x : Power R 1, ∃ hx : W x, (g.toFun (Subtype.mk x hx)).1 = y with hImgdef
    have hImgMem : M.S 1 Img := imageDefinableAux3 M g
    have hImgInf : Set.Infinite Img := by
      intro hfin
      obtain ⟨z0, hz0⟩ := nonEmptyOfInfinite3 hWinf
      set rep : R → Power R 1 := fun c =>
        if h : ∃ x : Power R 1, ∃ hx : W x, Power.coord1 ((g.toFun ⟨x, hx⟩).1) = c
        then Classical.choose h else z0 with hrepdef
      have repW : ∀ c, W (rep c) := by
        intro c
        simp only [hrepdef]
        by_cases h : ∃ x : Power R 1, ∃ hx : W x, Power.coord1 ((g.toFun ⟨x, hx⟩).1) = c
        · rw [dif_pos h]
          exact (Classical.choose_spec h).1
        · rw [dif_neg h]
          exact hz0
      have repVal : ∀ c (h : ∃ x : Power R 1, ∃ hx : W x,
          Power.coord1 ((g.toFun ⟨x, hx⟩).1) = c),
          Power.coord1 ((g.toFun ⟨rep c, repW c⟩).1) = c := by
        intro c h
        obtain ⟨hx0, hv0⟩ := Classical.choose_spec h
        have e : rep c = Classical.choose h := by
          simp only [hrepdef]
          exact dif_pos h
        have ept : (⟨rep c, repW c⟩ : {x : Power R 1 // W x})
            = ⟨Classical.choose h, hx0⟩ := Subtype.ext e
        rw [ept]
        exact hv0
      have hWfin : Set.Finite W := by
        have hImgFin : Set.Finite Img := hfin
        have hCFin : Set.Finite (Power.coord1 '' Img) := hImgFin.image _
        have hRFin : Set.Finite ((fun c => rep c) '' (Power.coord1 '' Img)) :=
          hCFin.image _
        apply hRFin.subset
        intro x hx
        have hmem : Img ((g.toFun ⟨x, hx⟩).1) := ⟨x, hx, rfl⟩
        have hcImg : Power.coord1 ((g.toFun ⟨x, hx⟩).1) ∈ Power.coord1 '' Img :=
          ⟨_, hmem, rfl⟩
        have h_ex : ∃ x' : Power R 1, ∃ hx' : W x',
            Power.coord1 ((g.toFun ⟨x', hx'⟩).1)
              = Power.coord1 ((g.toFun ⟨x, hx⟩).1) :=
          ⟨x, hx, rfl⟩
        have hxx : x = rep (Power.coord1 ((g.toFun ⟨x, hx⟩).1)) := by
          apply hinjW x _ hx (repW _)
          exact ptEqAux3 (repVal _ h_ex).symm
        exact ⟨Power.coord1 ((g.toFun ⟨x, hx⟩).1), hcImg, hxx.symm⟩
      exact hWinf hWfin
    obtain ⟨a1, b1, hlt1, hsub1⟩ :=
      Monotonicity_Theorem.infinite_definable_set_contains_interval2 M Img hImgMem hImgInf
    obtain ⟨pJ, hpJ⟩ := nonEmptyOfInfinite3 hImgInf
    obtain ⟨r, s, hr_lo, hrs, hs_hi⟩ := twoPointsInWin3 a1 b1 hlt1 pJ
    have hJr : openInterval a1 b1 (fun _ => r) := ⟨hr_lo, hiTrans3 b1 hs_hi hrs⟩
    have hJs : openInterval a1 b1 (fun _ => s) :=
      ⟨loTrans3 a1 hr_lo hrs, hs_hi⟩
    have hmemr : Img (fun _ => r) := hsub1 hJr
    have hmems : Img (fun _ => s) := hsub1 hJs
    obtain ⟨xr, hxr, hvr⟩ := hmemr
    obtain ⟨xs, hxs, hvs⟩ := hmems
    have hr_eq : Power.coord1 ((g.toFun ⟨xr, hxr⟩).1) = r := congrArg Power.coord1 hvr
    have hs_eq : Power.coord1 ((g.toFun ⟨xs, hxs⟩).1) = s := congrArg Power.coord1 hvs
    have hcd : LT.lt (Power.coord1 xr) (Power.coord1 xs) := by
      rcases lt_trichotomy (Power.coord1 xr) (Power.coord1 xs) with h | h | h
      · have hlt := h
        exact hlt
      · have heq := h
        exfalso
        have hcon : r = s := by
          have h1 : Power.coord1 ((g.toFun ⟨xr, hxr⟩).1) = r := hr_eq
          have h2 : Power.coord1 ((g.toFun ⟨xs, hxs⟩).1) = s := hs_eq
          have e : xr = xs := ptEqAux3 heq
          have ept : (⟨xr, hxr⟩ : {x : Power R 1 // W x}) = ⟨xs, hxs⟩ := Subtype.ext e
          rw [ept] at h1
          rw [h2] at h1
          exact h1.symm
        rw [hcon] at hrs
        exact lt_irrefl _ hrs
      · have hlt := h
        exfalso
        have hlt' : Lt1 xs xr := hlt
        have hcon := hincW xs xr hxs hxr hlt'
        have hcon' : LT.lt s r := by
          have h1 : Power.coord1 ((g.toFun ⟨xs, hxs⟩).1) = s := hs_eq
          have h2 : Power.coord1 ((g.toFun ⟨xr, hxr⟩).1) = r := hr_eq
          have hh : LT.lt (Power.coord1 ((g.toFun ⟨xs, hxs⟩).1))
              (Power.coord1 ((g.toFun ⟨xr, hxr⟩).1)) := hcon
          rw [h1, h2] at hh
          exact hh
        exact lt_irrefl _ (lt_trans hrs hcon')
    have honto : ∀ t : R, LT.lt r t → LT.lt t s →
        ∃ e : Power R 1, ∃ he : W e, (g.toFun ⟨e, he⟩).1 = (fun _ => t) ∧
          LT.lt (Power.coord1 xr) (Power.coord1 e) ∧
          LT.lt (Power.coord1 e) (Power.coord1 xs) := by
      intro t hrt hts
      have hJt : openInterval a1 b1 (fun _ => t) :=
        ⟨loTrans3 a1 hr_lo hrt, hiTrans3 b1 hs_hi hts⟩
      obtain ⟨e, heW, hve⟩ := (hsub1 hJt : Img (fun _ => t))
      have hce : LT.lt (Power.coord1 xr) (Power.coord1 e) := by
        rcases lt_trichotomy (Power.coord1 xr) (Power.coord1 e) with h | h | h
        · have hlt := h
          exact hlt
        · have heq := h
          exfalso
          have ept : (⟨e, heW⟩ : {x : Power R 1 // W x}) = ⟨xr, hxr⟩ :=
            Subtype.ext (ptEqAux3 heq.symm)
          have hcc : (g.toFun ⟨e, heW⟩).1 = (g.toFun ⟨xr, hxr⟩).1 := by
            rw [ept]
          have ht_eq_r : t = r := by
            have h1 := congrArg Power.coord1 hve
            have h2 := congrArg Power.coord1 hvr
            rw [hcc] at h1
            rw [h2] at h1
            exact h1.symm
          rw [ht_eq_r] at hrt
          exact lt_irrefl _ hrt
        · have hlt := h
          exfalso
          have hlt' : Lt1 e xr := hlt
          have hmo := hincW e xr heW hxr hlt'
          have hcon : LT.lt t r := by
            have h1 := congrArg Power.coord1 hve
            have h2 := congrArg Power.coord1 hvr
            have hmo' : LT.lt (Power.coord1 ((g.toFun ⟨e, heW⟩).1))
                (Power.coord1 ((g.toFun ⟨xr, hxr⟩).1)) := hmo
            rw [h1, h2] at hmo'
            exact hmo'
          exact lt_irrefl _ (lt_trans hrt hcon)
      have hed : LT.lt (Power.coord1 e) (Power.coord1 xs) := by
        rcases lt_trichotomy (Power.coord1 e) (Power.coord1 xs) with h | h | h
        · have hlt := h
          exact hlt
        · have heq := h
          exfalso
          have ept : (⟨e, heW⟩ : {x : Power R 1 // W x}) = ⟨xs, hxs⟩ :=
            Subtype.ext (ptEqAux3 heq)
          have hcc : (g.toFun ⟨e, heW⟩).1 = (g.toFun ⟨xs, hxs⟩).1 := by
            rw [ept]
          have ht_eq_s : t = s := by
            have h1 := congrArg Power.coord1 hve
            have h2 := congrArg Power.coord1 hvs
            rw [hcc] at h1
            rw [h2] at h1
            exact h1.symm
          rw [ht_eq_s] at hts
          exact lt_irrefl _ hts
        · have hlt := h
          exfalso
          have hlt' : Lt1 xs e := hlt
          have hmo := hincW xs e hxs heW hlt'
          have hcon : LT.lt s t := by
            have h1 := congrArg Power.coord1 hvs
            have h2 := congrArg Power.coord1 hve
            have hmo' : LT.lt (Power.coord1 ((g.toFun ⟨xs, hxs⟩).1))
                (Power.coord1 ((g.toFun ⟨e, heW⟩).1)) := hmo
            rw [h1, h2] at hmo'
            exact hmo'
          exact lt_irrefl _ (lt_trans hts hcon)
      exact ⟨e, heW, hve, hce, hed⟩
    have hcdW : (openInterval (Endpoint.finite (Power.coord1 xr))
        (Endpoint.finite (Power.coord1 xs))).Subset W := by
      intro y hy
      have hyL : LT.lt (Power.coord1 xr) (Power.coord1 y) := hy.left
      have hyR : LT.lt (Power.coord1 y) (Power.coord1 xs) := hy.right
      have huc : LT.lt u (Power.coord1 xr) := hxr.left
      have hcv : LT.lt (Power.coord1 xs) v := hxs.right
      exact ⟨lt_trans huc hyL, lt_trans hyR hcv⟩
    have hcont : ∀ x₀ : Power R 1,
        openInterval (Endpoint.finite (Power.coord1 xr)) (Endpoint.finite (Power.coord1 xs)) x₀ →
        ContinuousPoints I (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun) x₀ := by
      intro x₀ hx₀
      have hx₀W : W x₀ := hcdW hx₀
      have hx₀I : I x₀ := hWsub hx₀W
      refine ⟨hx₀I, ?_⟩
      intro w₀ hw₀ ε₁ ε₂ hε₁ hε₂
      obtain ⟨hxf, heqf⟩ := hw₀
      have eL : Power.left (R := R) (n := 1) (m := 1)
          (Power.append (fun _ => Power.coord1 x₀) (fun _ => w₀))
          = (fun _ => Power.coord1 x₀) := appendLeftAux3 _ _
      have eR : Power.right (R := R) (n := 1) (m := 1)
          (Power.append (fun _ => Power.coord1 x₀) (fun _ => w₀)) = (fun _ => w₀) :=
        appendRightAux3 _ _
      have hval0 : Power.left (R := R) (n := 1) (m := 1)
          (Power.append (fun _ => Power.coord1 x₀) (fun _ => w₀)) = x₀ := by
        rw [eL]
        exact (ptLam3 x₀).symm
      have ept0 : (⟨Power.left (R := R) (n := 1) (m := 1)
          (Power.append (fun _ => Power.coord1 x₀) (fun _ => w₀)), hxf⟩
          : {x : Power R 1 // I x}) = ⟨x₀, hx₀I⟩ :=
        Subtype.ext hval0
      rw [eR, ept0] at heqf
      have hw₀val : w₀ = Power.coord1 ((f.toFun ⟨x₀, hx₀I⟩).1) :=
        congrArg Power.coord1 heqf
      have hgval : (g.toFun ⟨x₀, hx₀W⟩).1 = (f.toFun ⟨x₀, hx₀I⟩).1 := by
        have h := hagree x₀ hx₀W
        have e : (⟨x₀, hWsub hx₀W⟩ : {x : Power R 1 // I x}) = ⟨x₀, hx₀I⟩ :=
          Subtype.ext rfl
        rw [e] at h
        exact congrArg Subtype.val h
      have hg0 : Power.coord1 ((g.toFun ⟨x₀, hx₀W⟩).1) = w₀ := by
        rw [hgval]
        exact hw₀val.symm
      have hmo1 : Lt1 xr x₀ := hx₀.left
      have hmo1u := hincW _ _ hxr hx₀W hmo1
      have hw₀r : LT.lt r w₀ := by
        have hh : LT.lt (Power.coord1 ((g.toFun ⟨xr, hxr⟩).1))
            (Power.coord1 ((g.toFun ⟨x₀, hx₀W⟩).1)) := hmo1u
        rw [hr_eq, hg0] at hh
        exact hh
      have hmo2 : Lt1 x₀ xs := hx₀.right
      have hmo2u := hincW _ _ hx₀W hxs hmo2
      have hw₀s : LT.lt w₀ s := by
        have hh : LT.lt (Power.coord1 ((g.toFun ⟨x₀, hx₀W⟩).1))
            (Power.coord1 ((g.toFun ⟨xs, hxs⟩).1)) := hmo2u
        rw [hg0, hs_eq] at hh
        exact hh
      obtain ⟨e1, he1lo, he1w, hre1⟩ : ∃ e1 : R, LT.lt ε₁ e1 ∧ LT.lt e1 w₀ ∧ LT.lt r e1 := by
        rcases lt_trichotomy ε₁ r with h | h | h
        · have hlt := h
          obtain ⟨m1, hrm1, hm1w⟩ := exists_between hw₀r
          exact ⟨m1, lt_trans hlt hrm1, hm1w, hrm1⟩
        · have heq := h
          obtain ⟨m1, hrm1, hm1w⟩ := exists_between hw₀r
          exact ⟨m1, by rw [heq]; exact hrm1, hm1w, hrm1⟩
        · have hlt := h
          obtain ⟨m1, hm1a, hm1w⟩ := exists_between hε₁
          exact ⟨m1, hm1a, hm1w, lt_trans hlt hm1a⟩
      obtain ⟨e2, hwe2, he2hi, he2s⟩ : ∃ e2 : R, LT.lt w₀ e2 ∧ LT.lt e2 ε₂ ∧ LT.lt e2 s := by
        rcases lt_trichotomy ε₂ s with h | h | h
        · have hlt := h
          obtain ⟨m2, hwm2, hm2e⟩ := exists_between (show LT.lt w₀ ε₂ from hε₂)
          exact ⟨m2, hwm2, hm2e, lt_trans hm2e hlt⟩
        · have heq := h
          obtain ⟨m2, hwm2, hm2e⟩ := exists_between (show LT.lt w₀ ε₂ from hε₂)
          exact ⟨m2, hwm2, hm2e, by rw [← heq]; exact hm2e⟩
        · have hlt := h
          obtain ⟨m2, hwm2, hm2e⟩ := exists_between hw₀s
          exact ⟨m2, hwm2, lt_trans hm2e hlt, hm2e⟩
      have hJe1 : openInterval a1 b1 (fun _ => e1) :=
        ⟨loTrans3 a1 hr_lo hre1, hiTrans3 b1 hs_hi (lt_trans he1w hw₀s)⟩
      have hJe2 : openInterval a1 b1 (fun _ => e2) :=
        ⟨loTrans3 a1 hr_lo (lt_trans hre1 (lt_trans he1w hwe2)), hiTrans3 b1 hs_hi he2s⟩
      obtain ⟨d1, hd1W, hvd1⟩ := (hsub1 hJe1 : Img (fun _ => e1))
      obtain ⟨d2, hd2W, hvd2⟩ := (hsub1 hJe2 : Img (fun _ => e2))
      have hd1v : Power.coord1 ((g.toFun ⟨d1, hd1W⟩).1) = e1 := congrArg Power.coord1 hvd1
      have hd2v : Power.coord1 ((g.toFun ⟨d2, hd2W⟩).1) = e2 := congrArg Power.coord1 hvd2
      have hd1x : LT.lt (Power.coord1 d1) (Power.coord1 x₀) := by
        rcases lt_trichotomy (Power.coord1 d1) (Power.coord1 x₀) with h | h | h
        · have hlt := h
          exact hlt
        · have heq := h
          exfalso
          have ept : (⟨d1, hd1W⟩ : {x : Power R 1 // W x}) = ⟨x₀, hx₀W⟩ :=
            Subtype.ext (ptEqAux3 heq)
          have hcc : (g.toFun ⟨d1, hd1W⟩).1 = (g.toFun ⟨x₀, hx₀W⟩).1 := by
            rw [ept]
          have hcc' : Power.coord1 ((g.toFun ⟨d1, hd1W⟩).1)
              = Power.coord1 ((g.toFun ⟨x₀, hx₀W⟩).1) := congrArg _ hcc
          rw [hd1v, hg0] at hcc'
          rw [hcc'] at he1w
          exact lt_irrefl _ he1w
        · have hlt := h
          exfalso
          have hlt' : Lt1 x₀ d1 := hlt
          have hmo := hincW x₀ d1 hx₀W hd1W hlt'
          have hmo' : LT.lt w₀ e1 := by
            have hh : LT.lt (Power.coord1 ((g.toFun ⟨x₀, hx₀W⟩).1))
                (Power.coord1 ((g.toFun ⟨d1, hd1W⟩).1)) := hmo
            rw [hg0, hd1v] at hh
            exact hh
          exact lt_irrefl _ (lt_trans he1w hmo')
      have hxd2 : LT.lt (Power.coord1 x₀) (Power.coord1 d2) := by
        rcases lt_trichotomy (Power.coord1 x₀) (Power.coord1 d2) with h | h | h
        · have hlt := h
          exact hlt
        · have heq := h
          exfalso
          have ept : (⟨x₀, hx₀W⟩ : {x : Power R 1 // W x}) = ⟨d2, hd2W⟩ :=
            Subtype.ext (ptEqAux3 heq)
          have hcc : (g.toFun ⟨x₀, hx₀W⟩).1 = (g.toFun ⟨d2, hd2W⟩).1 := by
            rw [ept]
          have hcc' : Power.coord1 ((g.toFun ⟨x₀, hx₀W⟩).1)
              = Power.coord1 ((g.toFun ⟨d2, hd2W⟩).1) := congrArg _ hcc
          rw [hg0, hd2v] at hcc'
          rw [hcc'] at hwe2
          exact lt_irrefl _ hwe2
        · have hlt := h
          exfalso
          have hlt' : Lt1 d2 x₀ := hlt
          have hmo := hincW d2 x₀ hd2W hx₀W hlt'
          have hmo' : LT.lt e2 w₀ := by
            have hh : LT.lt (Power.coord1 ((g.toFun ⟨d2, hd2W⟩).1))
                (Power.coord1 ((g.toFun ⟨x₀, hx₀W⟩).1)) := hmo
            rw [hd2v, hg0] at hh
            exact hh
          exact lt_irrefl _ (lt_trans hmo' hwe2)
      refine ⟨Power.coord1 d1, Power.coord1 d2, hd1x, hxd2, ?_⟩
      intro y v hyI hGyv hdy1 hdy2
      have hv_eq : v = Power.coord1 ((f.toFun ⟨fun _ => y, hyI⟩).1) :=
        graphValAux3 f _ _ hyI hGyv
      have hyWm : W (fun _ => y) :=
        ⟨lt_trans hd1W.left hdy1, lt_trans hdy2 hd2W.right⟩
      have hylt1 : Lt1 d1 (fun _ => y) := hdy1
      have hmo1y := hincW _ _ hd1W hyWm hylt1
      have hε1v : LT.lt ε₁ v := by
        have hh : LT.lt (Power.coord1 ((g.toFun ⟨d1, hd1W⟩).1))
            (Power.coord1 ((g.toFun ⟨fun _ => y, hyWm⟩).1)) := hmo1y
        rw [hd1v] at hh
        have hgy : Power.coord1 ((g.toFun ⟨fun _ => y, hyWm⟩).1) = v := by
          have h1 := gval (fun _ => y) hyWm
          have e : (⟨fun _ => y, hWsub hyWm⟩ : {x : Power R 1 // I x})
              = ⟨fun _ => y, hyI⟩ := Subtype.ext rfl
          rw [e] at h1
          rw [h1]
          exact hv_eq.symm
        rw [hgy] at hh
        exact lt_trans he1lo hh
      have hylt2 : Lt1 (fun _ => y) d2 := hdy2
      have hmo2y := hincW _ _ hyWm hd2W hylt2
      have hε2v : LT.lt v ε₂ := by
        have hh : LT.lt (Power.coord1 ((g.toFun ⟨fun _ => y, hyWm⟩).1))
            (Power.coord1 ((g.toFun ⟨d2, hd2W⟩).1)) := hmo2y
        have hgy : Power.coord1 ((g.toFun ⟨fun _ => y, hyWm⟩).1) = v := by
          have h1 := gval (fun _ => y) hyWm
          have e : (⟨fun _ => y, hWsub hyWm⟩ : {x : Power R 1 // I x})
              = ⟨fun _ => y, hyI⟩ := Subtype.ext rfl
          rw [e] at h1
          rw [h1]
          exact hv_eq.symm
        rw [hgy, hd2v] at hh
        exact lt_trans hh he2hi
      exact ⟨hε1v, hε2v⟩
    refine ⟨Endpoint.finite (Power.coord1 xr), Endpoint.finite (Power.coord1 xs),
      hcd, ?_, ?_⟩
    · intro y hy
      exact hWsub (hcdW hy)
    · intro x hx
      exact hcont x hx
  · -- Strictly decreasing case (mirror image).
    have hdecW : StrictlyDecreasingOn W B g.toFun := by
      intro x y hx hy hlt
      have h := hdec x y (hWsub hx) (hWsub hy) hlt
      rw [gval x hx, gval y hy]
      exact h
    have hinjW : ∀ x y (hx : W x) (hy : W y),
        (g.toFun ⟨x, hx⟩).1 = (g.toFun ⟨y, hy⟩).1 → x = y := by
      intro x y hx hy hval
      have hc : Power.coord1 ((g.toFun ⟨x, hx⟩).1)
          = Power.coord1 ((g.toFun ⟨y, hy⟩).1) := congrArg _ hval
      rcases lt_trichotomy (Power.coord1 x) (Power.coord1 y) with h | h | h
      · have hlt := h
        have hcon : LT.lt (Power.coord1 ((g.toFun ⟨y, hy⟩).1))
            (Power.coord1 ((g.toFun ⟨x, hx⟩).1)) := hdecW x y hx hy hlt
        rw [← hc] at hcon
        exact False.elim (lt_irrefl _ hcon)
      · have heq := h
        exact ptEqAux3 heq
      · have hlt := h
        have hcon : LT.lt (Power.coord1 ((g.toFun ⟨x, hx⟩).1))
            (Power.coord1 ((g.toFun ⟨y, hy⟩).1)) := hdecW y x hy hx hlt
        rw [hc] at hcon
        exact False.elim (lt_irrefl _ hcon)
    set ImgD : Set (Power R 1) :=
      fun y => ∃ x : Power R 1, ∃ hx : W x, (g.toFun (Subtype.mk x hx)).1 = y with hImgDdef
    have hImgDMem : M.S 1 ImgD := imageDefinableAux3 M g
    have hImgDInf : Set.Infinite ImgD := by
      intro hfin
      obtain ⟨z0, hz0⟩ := nonEmptyOfInfinite3 hWinf
      set rep : R → Power R 1 := fun c =>
        if h : ∃ x : Power R 1, ∃ hx : W x, Power.coord1 ((g.toFun ⟨x, hx⟩).1) = c
        then Classical.choose h else z0 with hrepdef
      have repW : ∀ c, W (rep c) := by
        intro c
        simp only [hrepdef]
        by_cases h : ∃ x : Power R 1, ∃ hx : W x, Power.coord1 ((g.toFun ⟨x, hx⟩).1) = c
        · rw [dif_pos h]
          exact (Classical.choose_spec h).1
        · rw [dif_neg h]
          exact hz0
      have repVal : ∀ c (h : ∃ x : Power R 1, ∃ hx : W x,
          Power.coord1 ((g.toFun ⟨x, hx⟩).1) = c),
          Power.coord1 ((g.toFun ⟨rep c, repW c⟩).1) = c := by
        intro c h
        obtain ⟨hx0, hv0⟩ := Classical.choose_spec h
        have e : rep c = Classical.choose h := by
          simp only [hrepdef]
          exact dif_pos h
        have ept : (⟨rep c, repW c⟩ : {x : Power R 1 // W x})
            = ⟨Classical.choose h, hx0⟩ := Subtype.ext e
        rw [ept]
        exact hv0
      have hWfin : Set.Finite W := by
        have hImgFin : Set.Finite ImgD := hfin
        have hCFin : Set.Finite (Power.coord1 '' ImgD) := hImgFin.image _
        have hRFin : Set.Finite ((fun c => rep c) '' (Power.coord1 '' ImgD)) :=
          hCFin.image _
        apply hRFin.subset
        intro x hx
        have hmem : ImgD ((g.toFun ⟨x, hx⟩).1) := ⟨x, hx, rfl⟩
        have hcImg : Power.coord1 ((g.toFun ⟨x, hx⟩).1) ∈ Power.coord1 '' ImgD :=
          ⟨_, hmem, rfl⟩
        have h_ex : ∃ x' : Power R 1, ∃ hx' : W x',
            Power.coord1 ((g.toFun ⟨x', hx'⟩).1)
              = Power.coord1 ((g.toFun ⟨x, hx⟩).1) :=
          ⟨x, hx, rfl⟩
        have hxx : x = rep (Power.coord1 ((g.toFun ⟨x, hx⟩).1)) := by
          apply hinjW x _ hx (repW _)
          exact ptEqAux3 (repVal _ h_ex).symm
        exact ⟨Power.coord1 ((g.toFun ⟨x, hx⟩).1), hcImg, hxx.symm⟩
      exact hWinf hWfin
    obtain ⟨a1, b1, hlt1, hsub1⟩ :=
      Monotonicity_Theorem.infinite_definable_set_contains_interval2 M ImgD hImgDMem hImgDInf
    obtain ⟨pJ, hpJ⟩ := nonEmptyOfInfinite3 hImgDInf
    obtain ⟨r, s, hr_lo, hrs, hs_hi⟩ := twoPointsInWin3 a1 b1 hlt1 pJ
    have hJr : openInterval a1 b1 (fun _ => r) := ⟨hr_lo, hiTrans3 b1 hs_hi hrs⟩
    have hJs : openInterval a1 b1 (fun _ => s) :=
      ⟨loTrans3 a1 hr_lo hrs, hs_hi⟩
    have hmemr : ImgD (fun _ => r) := hsub1 hJr
    have hmems : ImgD (fun _ => s) := hsub1 hJs
    obtain ⟨xr, hxr, hvr⟩ := hmemr
    obtain ⟨xs, hxs, hvs⟩ := hmems
    have hr_eq : Power.coord1 ((g.toFun ⟨xr, hxr⟩).1) = r := congrArg Power.coord1 hvr
    have hs_eq : Power.coord1 ((g.toFun ⟨xs, hxs⟩).1) = s := congrArg Power.coord1 hvs
    -- For decreasing f, the s-preimage lies LEFT of the r-preimage.
    have hcd : LT.lt (Power.coord1 xs) (Power.coord1 xr) := by
      rcases lt_trichotomy (Power.coord1 xr) (Power.coord1 xs) with h | h | h
      · have hlt := h
        exfalso
        have hlt' : Lt1 xr xs := hlt
        have hcon := hdecW xr xs hxr hxs hlt'
        have hcon' : LT.lt s r := by
          have h1 : Power.coord1 ((g.toFun ⟨xs, hxs⟩).1) = s := hs_eq
          have h2 : Power.coord1 ((g.toFun ⟨xr, hxr⟩).1) = r := hr_eq
          have hh : LT.lt (Power.coord1 ((g.toFun ⟨xs, hxs⟩).1))
              (Power.coord1 ((g.toFun ⟨xr, hxr⟩).1)) := hcon
          rw [h1, h2] at hh
          exact hh
        exact lt_irrefl _ (lt_trans hrs hcon')
      · have heq := h
        exfalso
        have hcon : r = s := by
          have h1 : Power.coord1 ((g.toFun ⟨xr, hxr⟩).1) = r := hr_eq
          have h2 : Power.coord1 ((g.toFun ⟨xs, hxs⟩).1) = s := hs_eq
          have e : xr = xs := ptEqAux3 heq
          have ept : (⟨xr, hxr⟩ : {x : Power R 1 // W x}) = ⟨xs, hxs⟩ := Subtype.ext e
          rw [ept] at h1
          rw [h2] at h1
          exact h1.symm
        rw [hcon] at hrs
        exact lt_irrefl _ hrs
      · have hlt := h
        exact hlt
    have honto : ∀ t : R, LT.lt r t → LT.lt t s →
        ∃ e : Power R 1, ∃ he : W e, (g.toFun ⟨e, he⟩).1 = (fun _ => t) ∧
          LT.lt (Power.coord1 xs) (Power.coord1 e) ∧
          LT.lt (Power.coord1 e) (Power.coord1 xr) := by
      intro t hrt hts
      have hJt : openInterval a1 b1 (fun _ => t) :=
        ⟨loTrans3 a1 hr_lo hrt, hiTrans3 b1 hs_hi hts⟩
      obtain ⟨e, heW, hve⟩ := (hsub1 hJt : ImgD (fun _ => t))
      have hce : LT.lt (Power.coord1 xs) (Power.coord1 e) := by
        rcases lt_trichotomy (Power.coord1 xs) (Power.coord1 e) with h | h | h
        · have hlt := h
          exact hlt
        · have heq := h
          exfalso
          have ept : (⟨e, heW⟩ : {x : Power R 1 // W x}) = ⟨xs, hxs⟩ :=
            Subtype.ext (ptEqAux3 heq.symm)
          have hcc : (g.toFun ⟨e, heW⟩).1 = (g.toFun ⟨xs, hxs⟩).1 := by
            rw [ept]
          have ht_eq_s : t = s := by
            have h1 := congrArg Power.coord1 hve
            have h2 := congrArg Power.coord1 hvs
            rw [hcc] at h1
            rw [h2] at h1
            exact h1.symm
          rw [ht_eq_s] at hts
          exact lt_irrefl _ hts
        · have hlt := h
          exfalso
          have hlt' : Lt1 e xs := hlt
          have hmo := hdecW e xs heW hxs hlt'
          have hcon : LT.lt s t := by
            have h1 := congrArg Power.coord1 hve
            have h2 := congrArg Power.coord1 hvs
            have hmo' : LT.lt (Power.coord1 ((g.toFun ⟨xs, hxs⟩).1))
                (Power.coord1 ((g.toFun ⟨e, heW⟩).1)) := hmo
            rw [h1, h2] at hmo'
            exact hmo'
          exact lt_irrefl _ (lt_trans hts hcon)
      have hed : LT.lt (Power.coord1 e) (Power.coord1 xr) := by
        rcases lt_trichotomy (Power.coord1 e) (Power.coord1 xr) with h | h | h
        · have hlt := h
          exact hlt
        · have heq := h
          exfalso
          have ept : (⟨e, heW⟩ : {x : Power R 1 // W x}) = ⟨xr, hxr⟩ :=
            Subtype.ext (ptEqAux3 heq)
          have hcc : (g.toFun ⟨e, heW⟩).1 = (g.toFun ⟨xr, hxr⟩).1 := by
            rw [ept]
          have ht_eq_r : t = r := by
            have h1 := congrArg Power.coord1 hve
            have h2 := congrArg Power.coord1 hvr
            rw [hcc] at h1
            rw [h2] at h1
            exact h1.symm
          rw [ht_eq_r] at hrt
          exact lt_irrefl _ hrt
        · have hlt := h
          exfalso
          have hlt' : Lt1 xr e := hlt
          have hmo := hdecW xr e hxr heW hlt'
          have hcon : LT.lt t r := by
            have h1 := congrArg Power.coord1 hve
            have h2 := congrArg Power.coord1 hvr
            have hmo' : LT.lt (Power.coord1 ((g.toFun ⟨e, heW⟩).1))
                (Power.coord1 ((g.toFun ⟨xr, hxr⟩).1)) := hmo
            rw [h1, h2] at hmo'
            exact hmo'
          exact lt_irrefl _ (lt_trans hrt hcon)
      exact ⟨e, heW, hve, hce, hed⟩
    have hcdW : (openInterval (Endpoint.finite (Power.coord1 xs))
        (Endpoint.finite (Power.coord1 xr))).Subset W := by
      intro y hy
      have hyL : LT.lt (Power.coord1 xs) (Power.coord1 y) := hy.left
      have hyR : LT.lt (Power.coord1 y) (Power.coord1 xr) := hy.right
      have huc : LT.lt u (Power.coord1 xs) := hxs.left
      have hcv : LT.lt (Power.coord1 xr) v := hxr.right
      exact ⟨lt_trans huc hyL, lt_trans hyR hcv⟩
    have hcont : ∀ x₀ : Power R 1,
        openInterval (Endpoint.finite (Power.coord1 xs)) (Endpoint.finite (Power.coord1 xr)) x₀ →
        ContinuousPoints I (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun) x₀ := by
      intro x₀ hx₀
      have hx₀W : W x₀ := hcdW hx₀
      have hx₀I : I x₀ := hWsub hx₀W
      refine ⟨hx₀I, ?_⟩
      intro w₀ hw₀ ε₁ ε₂ hε₁ hε₂
      obtain ⟨hxf, heqf⟩ := hw₀
      have eL : Power.left (R := R) (n := 1) (m := 1)
          (Power.append (fun _ => Power.coord1 x₀) (fun _ => w₀))
          = (fun _ => Power.coord1 x₀) := appendLeftAux3 _ _
      have eR : Power.right (R := R) (n := 1) (m := 1)
          (Power.append (fun _ => Power.coord1 x₀) (fun _ => w₀)) = (fun _ => w₀) :=
        appendRightAux3 _ _
      have hval0 : Power.left (R := R) (n := 1) (m := 1)
          (Power.append (fun _ => Power.coord1 x₀) (fun _ => w₀)) = x₀ := by
        rw [eL]
        exact (ptLam3 x₀).symm
      have ept0 : (⟨Power.left (R := R) (n := 1) (m := 1)
          (Power.append (fun _ => Power.coord1 x₀) (fun _ => w₀)), hxf⟩
          : {x : Power R 1 // I x}) = ⟨x₀, hx₀I⟩ :=
        Subtype.ext hval0
      rw [eR, ept0] at heqf
      have hw₀val : w₀ = Power.coord1 ((f.toFun ⟨x₀, hx₀I⟩).1) :=
        congrArg Power.coord1 heqf
      have hgval : (g.toFun ⟨x₀, hx₀W⟩).1 = (f.toFun ⟨x₀, hx₀I⟩).1 := by
        have h := hagree x₀ hx₀W
        have e : (⟨x₀, hWsub hx₀W⟩ : {x : Power R 1 // I x}) = ⟨x₀, hx₀I⟩ :=
          Subtype.ext rfl
        rw [e] at h
        exact congrArg Subtype.val h
      have hg0 : Power.coord1 ((g.toFun ⟨x₀, hx₀W⟩).1) = w₀ := by
        rw [hgval]
        exact hw₀val.symm
      have hmo1 : Lt1 xs x₀ := hx₀.left
      have hmo1u := hdecW _ _ hxs hx₀W hmo1
      have hw₀s : LT.lt w₀ s := by
        have hh : LT.lt (Power.coord1 ((g.toFun ⟨x₀, hx₀W⟩).1))
            (Power.coord1 ((g.toFun ⟨xs, hxs⟩).1)) := hmo1u
        rw [hg0, hs_eq] at hh
        exact hh
      have hmo2 : Lt1 x₀ xr := hx₀.right
      have hmo2u := hdecW _ _ hx₀W hxr hmo2
      have hw₀r : LT.lt r w₀ := by
        have hh : LT.lt (Power.coord1 ((g.toFun ⟨xr, hxr⟩).1))
            (Power.coord1 ((g.toFun ⟨x₀, hx₀W⟩).1)) := hmo2u
        rw [hr_eq, hg0] at hh
        exact hh
      obtain ⟨e1, he1lo, he1w, hre1⟩ : ∃ e1 : R, LT.lt ε₁ e1 ∧ LT.lt e1 w₀ ∧ LT.lt r e1 := by
        rcases lt_trichotomy ε₁ r with h | h | h
        · have hlt := h
          obtain ⟨m1, hrm1, hm1w⟩ := exists_between hw₀r
          exact ⟨m1, lt_trans hlt hrm1, hm1w, hrm1⟩
        · have heq := h
          obtain ⟨m1, hrm1, hm1w⟩ := exists_between hw₀r
          exact ⟨m1, by rw [heq]; exact hrm1, hm1w, hrm1⟩
        · have hlt := h
          obtain ⟨m1, hm1a, hm1w⟩ := exists_between hε₁
          exact ⟨m1, hm1a, hm1w, lt_trans hlt hm1a⟩
      obtain ⟨e2, hwe2, he2hi, he2s⟩ : ∃ e2 : R, LT.lt w₀ e2 ∧ LT.lt e2 ε₂ ∧ LT.lt e2 s := by
        rcases lt_trichotomy ε₂ s with h | h | h
        · have hlt := h
          obtain ⟨m2, hwm2, hm2e⟩ := exists_between (show LT.lt w₀ ε₂ from hε₂)
          exact ⟨m2, hwm2, hm2e, lt_trans hm2e hlt⟩
        · have heq := h
          obtain ⟨m2, hwm2, hm2e⟩ := exists_between (show LT.lt w₀ ε₂ from hε₂)
          exact ⟨m2, hwm2, hm2e, by rw [← heq]; exact hm2e⟩
        · have hlt := h
          obtain ⟨m2, hwm2, hm2e⟩ := exists_between hw₀s
          exact ⟨m2, hwm2, lt_trans hm2e hlt, hm2e⟩
      have hJe1 : openInterval a1 b1 (fun _ => e1) :=
        ⟨loTrans3 a1 hr_lo hre1, hiTrans3 b1 hs_hi (lt_trans he1w hw₀s)⟩
      have hJe2 : openInterval a1 b1 (fun _ => e2) :=
        ⟨loTrans3 a1 hr_lo (lt_trans hre1 (lt_trans he1w hwe2)), hiTrans3 b1 hs_hi he2s⟩
      obtain ⟨d1, hd1W, hvd1⟩ := (hsub1 hJe1 : ImgD (fun _ => e1))
      obtain ⟨d2, hd2W, hvd2⟩ := (hsub1 hJe2 : ImgD (fun _ => e2))
      have hd1v : Power.coord1 ((g.toFun ⟨d1, hd1W⟩).1) = e1 := congrArg Power.coord1 hvd1
      have hd2v : Power.coord1 ((g.toFun ⟨d2, hd2W⟩).1) = e2 := congrArg Power.coord1 hvd2
      -- For decreasing f, the below-value preimage lies RIGHT of x₀, above-value LEFT.
      have hxd1 : LT.lt (Power.coord1 x₀) (Power.coord1 d1) := by
        rcases lt_trichotomy (Power.coord1 x₀) (Power.coord1 d1) with h | h | h
        · have hlt := h
          exact hlt
        · have heq := h
          exfalso
          have ept : (⟨x₀, hx₀W⟩ : {x : Power R 1 // W x}) = ⟨d1, hd1W⟩ :=
            Subtype.ext (ptEqAux3 heq)
          have hcc : (g.toFun ⟨x₀, hx₀W⟩).1 = (g.toFun ⟨d1, hd1W⟩).1 := by
            rw [ept]
          have hcc' : Power.coord1 ((g.toFun ⟨x₀, hx₀W⟩).1)
              = Power.coord1 ((g.toFun ⟨d1, hd1W⟩).1) := congrArg _ hcc
          rw [hg0, hd1v] at hcc'
          rw [hcc'] at he1w
          exact lt_irrefl _ he1w
        · have hlt := h
          exfalso
          have hlt' : Lt1 d1 x₀ := hlt
          have hmo := hdecW d1 x₀ hd1W hx₀W hlt'
          have hmo' : LT.lt w₀ e1 := by
            have hh : LT.lt (Power.coord1 ((g.toFun ⟨x₀, hx₀W⟩).1))
                (Power.coord1 ((g.toFun ⟨d1, hd1W⟩).1)) := hmo
            rw [hg0, hd1v] at hh
            exact hh
          exact lt_irrefl _ (lt_trans hmo' he1w)
      have hd2x : LT.lt (Power.coord1 d2) (Power.coord1 x₀) := by
        rcases lt_trichotomy (Power.coord1 d2) (Power.coord1 x₀) with h | h | h
        · have hlt := h
          exact hlt
        · have heq := h
          exfalso
          have ept : (⟨d2, hd2W⟩ : {x : Power R 1 // W x}) = ⟨x₀, hx₀W⟩ :=
            Subtype.ext (ptEqAux3 heq)
          have hcc : (g.toFun ⟨d2, hd2W⟩).1 = (g.toFun ⟨x₀, hx₀W⟩).1 := by
            rw [ept]
          have hcc' : Power.coord1 ((g.toFun ⟨d2, hd2W⟩).1)
              = Power.coord1 ((g.toFun ⟨x₀, hx₀W⟩).1) := congrArg _ hcc
          rw [hd2v, hg0] at hcc'
          rw [hcc'] at hwe2
          exact lt_irrefl _ hwe2
        · have hlt := h
          exfalso
          have hlt' : Lt1 x₀ d2 := hlt
          have hmo := hdecW x₀ d2 hx₀W hd2W hlt'
          have hmo' : LT.lt e2 w₀ := by
            have hh : LT.lt (Power.coord1 ((g.toFun ⟨d2, hd2W⟩).1))
                (Power.coord1 ((g.toFun ⟨x₀, hx₀W⟩).1)) := hmo
            rw [hd2v, hg0] at hh
            exact hh
          exact lt_irrefl _ (lt_trans hmo' hwe2)
      refine ⟨Power.coord1 d2, Power.coord1 d1, hd2x, hxd1, ?_⟩
      intro y v hyI hGyv hdy1 hdy2
      have hv_eq : v = Power.coord1 ((f.toFun ⟨fun _ => y, hyI⟩).1) :=
        graphValAux3 f _ _ hyI hGyv
      have hyWm : W (fun _ => y) :=
        ⟨lt_trans hd2W.left hdy1, lt_trans hdy2 hd1W.right⟩
      have hylt1 : Lt1 (fun _ => y) d1 := hdy2
      have hmo1y := hdecW _ _ hyWm hd1W hylt1
      have hε1v : LT.lt ε₁ v := by
        have hh : LT.lt (Power.coord1 ((g.toFun ⟨d1, hd1W⟩).1))
            (Power.coord1 ((g.toFun ⟨fun _ => y, hyWm⟩).1)) := hmo1y
        rw [hd1v] at hh
        have hgy : Power.coord1 ((g.toFun ⟨fun _ => y, hyWm⟩).1) = v := by
          have h1 := gval (fun _ => y) hyWm
          have e : (⟨fun _ => y, hWsub hyWm⟩ : {x : Power R 1 // I x})
              = ⟨fun _ => y, hyI⟩ := Subtype.ext rfl
          rw [e] at h1
          rw [h1]
          exact hv_eq.symm
        rw [hgy] at hh
        exact lt_trans he1lo hh
      have hylt2 : Lt1 d2 (fun _ => y) := hdy1
      have hmo2y := hdecW _ _ hd2W hyWm hylt2
      have hε2v : LT.lt v ε₂ := by
        have hh : LT.lt (Power.coord1 ((g.toFun ⟨fun _ => y, hyWm⟩).1))
            (Power.coord1 ((g.toFun ⟨d2, hd2W⟩).1)) := hmo2y
        have hgy : Power.coord1 ((g.toFun ⟨fun _ => y, hyWm⟩).1) = v := by
          have h1 := gval (fun _ => y) hyWm
          have e : (⟨fun _ => y, hWsub hyWm⟩ : {x : Power R 1 // I x})
              = ⟨fun _ => y, hyI⟩ := Subtype.ext rfl
          rw [e] at h1
          rw [h1]
          exact hv_eq.symm
        rw [hgy, hd2v] at hh
        exact lt_trans hh he2hi
      exact ⟨hε1v, hε2v⟩
    refine ⟨Endpoint.finite (Power.coord1 xs), Endpoint.finite (Power.coord1 xr),
      hcd, ?_, ?_⟩
    · intro y hy
      exact hWsub (hcdW hy)
    · intro x hx
      exact hcont x hx
