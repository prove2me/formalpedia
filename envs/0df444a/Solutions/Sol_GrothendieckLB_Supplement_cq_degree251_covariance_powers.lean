-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_degree251_covariance_powers
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:40:01.382015+00:00
-- url     : https://prove2.me/submissions/7a517ae4-38e8-4940-bb3e-91deb6d9427c

import Definitions.Def_GrothendieckLB_Supplement_cqDegree251Tables
import Mathlib.Tactic.NormNum

open GrothendieckLB.Supplement.CQHeadArithmetic GrothendieckLB.Supplement.CQDegree251
namespace CQRowEncoding
set_option maxRecDepth 10000
set_option exponentiation.threshold 50000

def packNat {α : Type} (B : ℕ) (f : α → ℕ) : List α → ℕ
  | [] => 0
  | x::xs => f x + B*packNat B f xs

private theorem pack_digit {α : Type} (B : ℕ) (hB : 0<B) (f : α → ℕ) (xs : List α)
    (hs : ∀ x ∈ xs, f x < B) (i : ℕ) (hi : i<xs.length) :
    digit B (packNat B f xs) i = f xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    have hx := hs x (by simp)
    have ht (t) (hm : t∈xs) : f t<B := hs t (by simp [hm])
    cases i with
    | zero => simp [digit,packNat,Nat.add_mod,Nat.mod_eq_of_lt hx]
    | succ i =>
      have hj : i<xs.length := by simpa using hi
      have peel (w : ℕ) : digit B w (i+1) = digit B (w/B) i := by
        simp [digit,Nat.div_div_eq_div_mul,pow_succ']
      rw [peel,packNat,Nat.add_mul_div_left _ _ hB,Nat.div_eq_of_lt hx,Nat.zero_add,ih ht i hj]
      rfl

def admissible (B : ℕ) (x : Interval) :=
  x.lo.toNat<radix ∧ (-x.lo).toNat<radix ∧ x.lo≤x.hi ∧ (x.hi-x.lo).toNat<B

instance (B : ℕ) (x : Interval) : Decidable (admissible B x) :=
  inferInstanceAs (Decidable (_ ∧ _))

def valid (B : ℕ) (p : PackedRow) (xs : List Interval) : Prop :=
  (xs.all (fun x => decide (admissible B x)) = true) ∧
  packNat radix (fun x => x.lo.toNat) xs = p.pos ∧
  packNat radix (fun x => (-x.lo).toNat) xs = p.neg ∧
  packNat B (fun x => (x.hi-x.lo).toNat) xs = p.wid

instance (B : ℕ) (p : PackedRow) (xs : List Interval) : Decidable (valid B p xs) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem validRow (B : ℕ) (hB : 0<B) (p : PackedRow) (xs : List Interval) (h : valid B p xs)
    (n : ℕ) (hn : xs.length=n) : tab n (cell false B p)=xs.toArray := by
  obtain ⟨ha,hp,hn',hw⟩ := h
  have hc (x) (hx : x∈xs) : admissible B x := of_decide_eq_true (List.all_eq_true.mp ha x hx)
  apply Array.ext
  · simp [tab,hn]
  · intro i hi hx
    have hi' : i<n := by simpa [tab] using hi
    have hidx : i<xs.length := by omega
    have hr : 0<radix := by decide
    have eqp := pack_digit radix hr (fun (x : Interval) => x.lo.toNat) xs
      (fun x hm => (hc _ hm).1) i hidx
    have eqn := pack_digit radix hr (fun (x : Interval) => (-x.lo).toNat) xs
      (fun x hm => (hc _ hm).2.1) i hidx
    have eqw := pack_digit B hB (fun (x : Interval) => (x.hi-x.lo).toNat) xs
      (fun x hm => (hc _ hm).2.2.2) i hidx
    rw [hp] at eqp
    rw [hn'] at eqn
    rw [hw] at eqw
    have hord := (hc xs[i] (List.getElem_mem hidx)).2.2.1
    simp only [tab,Array.getElem_ofFn,List.getElem_toArray,cell,low,Bool.false_eq_true,if_false,
      one_mul,eqp,eqn,eqw]
    cases he : xs[i] with
    | mk lo hi =>
      rw [he] at hord
      simp at hord ⊢
      constructor <;> omega

theorem tabPush {α : Type} (n : ℕ) (f : ℕ → α) :
    (tab n f).push (f n) = tab (n+1) f := by
  apply Array.ext
  · simp [tab]
  · intro j h h'
    have hs : j<n+1 := by simpa [tab] using h'
    by_cases hj : j<n
    · rw [Array.getElem_push_lt (by simpa [tab] using hj)]
      simp [tab]
    · have he : j=n := by omega
      subst j
      simp [tab,Array.getElem_push]

theorem lookup {α : Type} (d : α) (n : ℕ) (f : ℕ → α) (i : ℕ) (hi : i<n) :
    entry d (tab n f) i = f i := by simp [entry,tab,hi]

end CQRowEncoding


open GrothendieckLB.Supplement.CQHeadArithmetic GrothendieckLB.Supplement.CQDegree251
namespace CQCovariance251
open CQRowEncoding
set_option maxRecDepth 10000
set_option exponentiation.threshold 50000

def applyRho (x y z : Interval) :=
  divideOut rhoDen (addInterval (subInterval (scaleInterval rho1 x) (scaleInterval rho3 y)) (scaleInterval rho5 z))

def pad (k : ℕ) (xs : List Interval) := List.replicate k zeroInterval ++ xs

def rhoShift (N : ℕ) (xs : List Interval) :=
  (List.zipWith (fun (p : Interval × Interval) z => applyRho p.1 p.2 z)
    ((pad 1 xs).zip (pad 3 xs)) (pad 5 xs)).take (N+1)

private theorem padAt (k : ℕ) (xs : List Interval) (j : ℕ) (hj : j<(pad k xs).length) :
    (pad k xs)[j] = shifted xs.toArray k j := by
  unfold pad at hj ⊢
  unfold shifted
  split
  next h =>
    rw [List.getElem_append_right (by simpa using h)]
    have hh : j-k<xs.length := by simp at hj; omega
    simp [entry,hh]
  next h =>
    rw [List.getElem_append_left (by simp; omega), List.getElem_replicate]

theorem streamCorrect (N : ℕ) (xs : List Interval) (h : xs.length=N+1) :
    rhoNext N xs.toArray=(rhoShift N xs).toArray := by
  have hlen : (rhoShift N xs).length=N+1 := by simp [rhoShift,pad,h]
  apply Array.ext
  · simp [rhoNext,tab,hlen]
  · intro j hj hj'
    have h1 : j<N+1 := by simpa [rhoNext,tab] using hj
    simp only [rhoNext, tab,Array.getElem_ofFn,List.getElem_toArray,rhoShift,List.getElem_take,
      List.getElem_zipWith,List.getElem_zip,padAt,applyRho]

noncomputable def row (a : ℕ) := rrow (entry default rp a) 252

theorem rowCert (a : ℕ) (x : List Interval) (h : valid 256 (entry default rp a) x)
    (hn : x.length=252) : row a=x.toArray :=
  validRow 256 (by decide) _ x h 252 hn

theorem base {x : List Interval} (h0 : row 0=x.toArray) (hx : x.toArray =
    tab 252 (fun j => if j=0 then fixed coefficientScale else zeroInterval)) :
    rhoPowers 251 0=tab 1 row := by
  have h : tab 1 row=#[row 0] := by
    apply Array.ext
    · simp [tab]
    · intro i hi _
      have : i=0 := by simp [tab] at hi; omega
      subst i; simp [tab]
  rw [h,h0,hx]
  rfl

theorem step {a : ℕ} {x y : List Interval} (ih : rhoPowers 251 a=tab (a+1) row)
    (hx : row a=x.toArray) (hy : row (a+1)=y.toArray) (hl : x.length=252)
    (ht : rhoShift 251 x=y) : rhoPowers 251 (a+1) = tab (a+1+1) row := by
  simp only [rhoPowers,ih,lookup _ _ _ _ (Nat.lt_succ_self a)]
  rw [hx,streamCorrect 251 x hl,ht,← hy,tabPush]

end CQCovariance251

open GrothendieckLB.Supplement.CQHeadArithmetic GrothendieckLB.Supplement.CQDegree251
open CQCovariance251 CQRowEncoding
namespace CovarianceArithmetic
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 50000
set_option Elab.async false
deriving instance Lean.ToExpr for Interval

private def candidates (lo len : ℕ) : List (List Interval) :=
  let rows := rhoPowers 251 (lo+len-1)
  (List.range' lo len).map (fun a => (entry #[] rows a).toList)

private noncomputable def chunk0 : List (List Interval) := eval% (candidates 0 8)
private noncomputable def x0 := chunk0[0]!
private theorem length0 : x0.length=252 := by decide +kernel
private theorem decoded0 : row 0=x0.toArray := rowCert 0 x0 (by decide +kernel) length0
private theorem first : rhoPowers 251 0 = tab 1 row := base decoded0 (by decide +kernel)
private noncomputable def x1 := chunk0[1]!
private theorem length1 : x1.length=252 := by decide +kernel
private theorem decoded1 : row 1=x1.toArray := rowCert 1 x1 (by decide +kernel) length1
private theorem powers1 : rhoPowers 251 1=tab 2 row :=
  step first decoded0 decoded1 length0 (by decide +kernel)
private noncomputable def x2 := chunk0[2]!
private theorem length2 : x2.length=252 := by decide +kernel
private theorem decoded2 : row 2=x2.toArray := rowCert 2 x2 (by decide +kernel) length2
private theorem powers2 : rhoPowers 251 2=tab 3 row :=
  step powers1 decoded1 decoded2 length1 (by decide +kernel)
private noncomputable def x3 := chunk0[3]!
private theorem length3 : x3.length=252 := by decide +kernel
private theorem decoded3 : row 3=x3.toArray := rowCert 3 x3 (by decide +kernel) length3
private theorem powers3 : rhoPowers 251 3=tab 4 row :=
  step powers2 decoded2 decoded3 length2 (by decide +kernel)
private noncomputable def x4 := chunk0[4]!
private theorem length4 : x4.length=252 := by decide +kernel
private theorem decoded4 : row 4=x4.toArray := rowCert 4 x4 (by decide +kernel) length4
private theorem powers4 : rhoPowers 251 4=tab 5 row :=
  step powers3 decoded3 decoded4 length3 (by decide +kernel)
private noncomputable def x5 := chunk0[5]!
private theorem length5 : x5.length=252 := by decide +kernel
private theorem decoded5 : row 5=x5.toArray := rowCert 5 x5 (by decide +kernel) length5
private theorem powers5 : rhoPowers 251 5=tab 6 row :=
  step powers4 decoded4 decoded5 length4 (by decide +kernel)
private noncomputable def x6 := chunk0[6]!
private theorem length6 : x6.length=252 := by decide +kernel
private theorem decoded6 : row 6=x6.toArray := rowCert 6 x6 (by decide +kernel) length6
private theorem powers6 : rhoPowers 251 6=tab 7 row :=
  step powers5 decoded5 decoded6 length5 (by decide +kernel)
private noncomputable def x7 := chunk0[7]!
private theorem length7 : x7.length=252 := by decide +kernel
private theorem decoded7 : row 7=x7.toArray := rowCert 7 x7 (by decide +kernel) length7
private theorem powers7 : rhoPowers 251 7=tab 8 row :=
  step powers6 decoded6 decoded7 length6 (by decide +kernel)

private noncomputable def chunk8 : List (List Interval) := eval% (candidates 8 8)
private noncomputable def x8 := chunk8[0]!
private theorem length8 : x8.length=252 := by decide +kernel
private theorem decoded8 : row 8=x8.toArray := rowCert 8 x8 (by decide +kernel) length8
private theorem powers8 : rhoPowers 251 8=tab 9 row :=
  step powers7 decoded7 decoded8 length7 (by decide +kernel)
private noncomputable def x9 := chunk8[1]!
private theorem length9 : x9.length=252 := by decide +kernel
private theorem decoded9 : row 9=x9.toArray := rowCert 9 x9 (by decide +kernel) length9
private theorem powers9 : rhoPowers 251 9=tab 10 row :=
  step powers8 decoded8 decoded9 length8 (by decide +kernel)
private noncomputable def x10 := chunk8[2]!
private theorem length10 : x10.length=252 := by decide +kernel
private theorem decoded10 : row 10=x10.toArray := rowCert 10 x10 (by decide +kernel) length10
private theorem powers10 : rhoPowers 251 10=tab 11 row :=
  step powers9 decoded9 decoded10 length9 (by decide +kernel)
private noncomputable def x11 := chunk8[3]!
private theorem length11 : x11.length=252 := by decide +kernel
private theorem decoded11 : row 11=x11.toArray := rowCert 11 x11 (by decide +kernel) length11
private theorem powers11 : rhoPowers 251 11=tab 12 row :=
  step powers10 decoded10 decoded11 length10 (by decide +kernel)
private noncomputable def x12 := chunk8[4]!
private theorem length12 : x12.length=252 := by decide +kernel
private theorem decoded12 : row 12=x12.toArray := rowCert 12 x12 (by decide +kernel) length12
private theorem powers12 : rhoPowers 251 12=tab 13 row :=
  step powers11 decoded11 decoded12 length11 (by decide +kernel)
private noncomputable def x13 := chunk8[5]!
private theorem length13 : x13.length=252 := by decide +kernel
private theorem decoded13 : row 13=x13.toArray := rowCert 13 x13 (by decide +kernel) length13
private theorem powers13 : rhoPowers 251 13=tab 14 row :=
  step powers12 decoded12 decoded13 length12 (by decide +kernel)
private noncomputable def x14 := chunk8[6]!
private theorem length14 : x14.length=252 := by decide +kernel
private theorem decoded14 : row 14=x14.toArray := rowCert 14 x14 (by decide +kernel) length14
private theorem powers14 : rhoPowers 251 14=tab 15 row :=
  step powers13 decoded13 decoded14 length13 (by decide +kernel)
private noncomputable def x15 := chunk8[7]!
private theorem length15 : x15.length=252 := by decide +kernel
private theorem decoded15 : row 15=x15.toArray := rowCert 15 x15 (by decide +kernel) length15
private theorem powers15 : rhoPowers 251 15=tab 16 row :=
  step powers14 decoded14 decoded15 length14 (by decide +kernel)

private noncomputable def chunk16 : List (List Interval) := eval% (candidates 16 8)
private noncomputable def x16 := chunk16[0]!
private theorem length16 : x16.length=252 := by decide +kernel
private theorem decoded16 : row 16=x16.toArray := rowCert 16 x16 (by decide +kernel) length16
private theorem powers16 : rhoPowers 251 16=tab 17 row :=
  step powers15 decoded15 decoded16 length15 (by decide +kernel)
private noncomputable def x17 := chunk16[1]!
private theorem length17 : x17.length=252 := by decide +kernel
private theorem decoded17 : row 17=x17.toArray := rowCert 17 x17 (by decide +kernel) length17
private theorem powers17 : rhoPowers 251 17=tab 18 row :=
  step powers16 decoded16 decoded17 length16 (by decide +kernel)
private noncomputable def x18 := chunk16[2]!
private theorem length18 : x18.length=252 := by decide +kernel
private theorem decoded18 : row 18=x18.toArray := rowCert 18 x18 (by decide +kernel) length18
private theorem powers18 : rhoPowers 251 18=tab 19 row :=
  step powers17 decoded17 decoded18 length17 (by decide +kernel)
private noncomputable def x19 := chunk16[3]!
private theorem length19 : x19.length=252 := by decide +kernel
private theorem decoded19 : row 19=x19.toArray := rowCert 19 x19 (by decide +kernel) length19
private theorem powers19 : rhoPowers 251 19=tab 20 row :=
  step powers18 decoded18 decoded19 length18 (by decide +kernel)
private noncomputable def x20 := chunk16[4]!
private theorem length20 : x20.length=252 := by decide +kernel
private theorem decoded20 : row 20=x20.toArray := rowCert 20 x20 (by decide +kernel) length20
private theorem powers20 : rhoPowers 251 20=tab 21 row :=
  step powers19 decoded19 decoded20 length19 (by decide +kernel)
private noncomputable def x21 := chunk16[5]!
private theorem length21 : x21.length=252 := by decide +kernel
private theorem decoded21 : row 21=x21.toArray := rowCert 21 x21 (by decide +kernel) length21
private theorem powers21 : rhoPowers 251 21=tab 22 row :=
  step powers20 decoded20 decoded21 length20 (by decide +kernel)
private noncomputable def x22 := chunk16[6]!
private theorem length22 : x22.length=252 := by decide +kernel
private theorem decoded22 : row 22=x22.toArray := rowCert 22 x22 (by decide +kernel) length22
private theorem powers22 : rhoPowers 251 22=tab 23 row :=
  step powers21 decoded21 decoded22 length21 (by decide +kernel)
private noncomputable def x23 := chunk16[7]!
private theorem length23 : x23.length=252 := by decide +kernel
private theorem decoded23 : row 23=x23.toArray := rowCert 23 x23 (by decide +kernel) length23
private theorem powers23 : rhoPowers 251 23=tab 24 row :=
  step powers22 decoded22 decoded23 length22 (by decide +kernel)

private noncomputable def chunk24 : List (List Interval) := eval% (candidates 24 8)
private noncomputable def x24 := chunk24[0]!
private theorem length24 : x24.length=252 := by decide +kernel
private theorem decoded24 : row 24=x24.toArray := rowCert 24 x24 (by decide +kernel) length24
private theorem powers24 : rhoPowers 251 24=tab 25 row :=
  step powers23 decoded23 decoded24 length23 (by decide +kernel)
private noncomputable def x25 := chunk24[1]!
private theorem length25 : x25.length=252 := by decide +kernel
private theorem decoded25 : row 25=x25.toArray := rowCert 25 x25 (by decide +kernel) length25
private theorem powers25 : rhoPowers 251 25=tab 26 row :=
  step powers24 decoded24 decoded25 length24 (by decide +kernel)
private noncomputable def x26 := chunk24[2]!
private theorem length26 : x26.length=252 := by decide +kernel
private theorem decoded26 : row 26=x26.toArray := rowCert 26 x26 (by decide +kernel) length26
private theorem powers26 : rhoPowers 251 26=tab 27 row :=
  step powers25 decoded25 decoded26 length25 (by decide +kernel)
private noncomputable def x27 := chunk24[3]!
private theorem length27 : x27.length=252 := by decide +kernel
private theorem decoded27 : row 27=x27.toArray := rowCert 27 x27 (by decide +kernel) length27
private theorem powers27 : rhoPowers 251 27=tab 28 row :=
  step powers26 decoded26 decoded27 length26 (by decide +kernel)
private noncomputable def x28 := chunk24[4]!
private theorem length28 : x28.length=252 := by decide +kernel
private theorem decoded28 : row 28=x28.toArray := rowCert 28 x28 (by decide +kernel) length28
private theorem powers28 : rhoPowers 251 28=tab 29 row :=
  step powers27 decoded27 decoded28 length27 (by decide +kernel)
private noncomputable def x29 := chunk24[5]!
private theorem length29 : x29.length=252 := by decide +kernel
private theorem decoded29 : row 29=x29.toArray := rowCert 29 x29 (by decide +kernel) length29
private theorem powers29 : rhoPowers 251 29=tab 30 row :=
  step powers28 decoded28 decoded29 length28 (by decide +kernel)
private noncomputable def x30 := chunk24[6]!
private theorem length30 : x30.length=252 := by decide +kernel
private theorem decoded30 : row 30=x30.toArray := rowCert 30 x30 (by decide +kernel) length30
private theorem powers30 : rhoPowers 251 30=tab 31 row :=
  step powers29 decoded29 decoded30 length29 (by decide +kernel)
private noncomputable def x31 := chunk24[7]!
private theorem length31 : x31.length=252 := by decide +kernel
private theorem decoded31 : row 31=x31.toArray := rowCert 31 x31 (by decide +kernel) length31
private theorem powers31 : rhoPowers 251 31=tab 32 row :=
  step powers30 decoded30 decoded31 length30 (by decide +kernel)

private noncomputable def chunk32 : List (List Interval) := eval% (candidates 32 8)
private noncomputable def x32 := chunk32[0]!
private theorem length32 : x32.length=252 := by decide +kernel
private theorem decoded32 : row 32=x32.toArray := rowCert 32 x32 (by decide +kernel) length32
private theorem powers32 : rhoPowers 251 32=tab 33 row :=
  step powers31 decoded31 decoded32 length31 (by decide +kernel)
private noncomputable def x33 := chunk32[1]!
private theorem length33 : x33.length=252 := by decide +kernel
private theorem decoded33 : row 33=x33.toArray := rowCert 33 x33 (by decide +kernel) length33
private theorem powers33 : rhoPowers 251 33=tab 34 row :=
  step powers32 decoded32 decoded33 length32 (by decide +kernel)
private noncomputable def x34 := chunk32[2]!
private theorem length34 : x34.length=252 := by decide +kernel
private theorem decoded34 : row 34=x34.toArray := rowCert 34 x34 (by decide +kernel) length34
private theorem powers34 : rhoPowers 251 34=tab 35 row :=
  step powers33 decoded33 decoded34 length33 (by decide +kernel)
private noncomputable def x35 := chunk32[3]!
private theorem length35 : x35.length=252 := by decide +kernel
private theorem decoded35 : row 35=x35.toArray := rowCert 35 x35 (by decide +kernel) length35
private theorem powers35 : rhoPowers 251 35=tab 36 row :=
  step powers34 decoded34 decoded35 length34 (by decide +kernel)
private noncomputable def x36 := chunk32[4]!
private theorem length36 : x36.length=252 := by decide +kernel
private theorem decoded36 : row 36=x36.toArray := rowCert 36 x36 (by decide +kernel) length36
private theorem powers36 : rhoPowers 251 36=tab 37 row :=
  step powers35 decoded35 decoded36 length35 (by decide +kernel)
private noncomputable def x37 := chunk32[5]!
private theorem length37 : x37.length=252 := by decide +kernel
private theorem decoded37 : row 37=x37.toArray := rowCert 37 x37 (by decide +kernel) length37
private theorem powers37 : rhoPowers 251 37=tab 38 row :=
  step powers36 decoded36 decoded37 length36 (by decide +kernel)
private noncomputable def x38 := chunk32[6]!
private theorem length38 : x38.length=252 := by decide +kernel
private theorem decoded38 : row 38=x38.toArray := rowCert 38 x38 (by decide +kernel) length38
private theorem powers38 : rhoPowers 251 38=tab 39 row :=
  step powers37 decoded37 decoded38 length37 (by decide +kernel)
private noncomputable def x39 := chunk32[7]!
private theorem length39 : x39.length=252 := by decide +kernel
private theorem decoded39 : row 39=x39.toArray := rowCert 39 x39 (by decide +kernel) length39
private theorem powers39 : rhoPowers 251 39=tab 40 row :=
  step powers38 decoded38 decoded39 length38 (by decide +kernel)

private noncomputable def chunk40 : List (List Interval) := eval% (candidates 40 8)
private noncomputable def x40 := chunk40[0]!
private theorem length40 : x40.length=252 := by decide +kernel
private theorem decoded40 : row 40=x40.toArray := rowCert 40 x40 (by decide +kernel) length40
private theorem powers40 : rhoPowers 251 40=tab 41 row :=
  step powers39 decoded39 decoded40 length39 (by decide +kernel)
private noncomputable def x41 := chunk40[1]!
private theorem length41 : x41.length=252 := by decide +kernel
private theorem decoded41 : row 41=x41.toArray := rowCert 41 x41 (by decide +kernel) length41
private theorem powers41 : rhoPowers 251 41=tab 42 row :=
  step powers40 decoded40 decoded41 length40 (by decide +kernel)
private noncomputable def x42 := chunk40[2]!
private theorem length42 : x42.length=252 := by decide +kernel
private theorem decoded42 : row 42=x42.toArray := rowCert 42 x42 (by decide +kernel) length42
private theorem powers42 : rhoPowers 251 42=tab 43 row :=
  step powers41 decoded41 decoded42 length41 (by decide +kernel)
private noncomputable def x43 := chunk40[3]!
private theorem length43 : x43.length=252 := by decide +kernel
private theorem decoded43 : row 43=x43.toArray := rowCert 43 x43 (by decide +kernel) length43
private theorem powers43 : rhoPowers 251 43=tab 44 row :=
  step powers42 decoded42 decoded43 length42 (by decide +kernel)
private noncomputable def x44 := chunk40[4]!
private theorem length44 : x44.length=252 := by decide +kernel
private theorem decoded44 : row 44=x44.toArray := rowCert 44 x44 (by decide +kernel) length44
private theorem powers44 : rhoPowers 251 44=tab 45 row :=
  step powers43 decoded43 decoded44 length43 (by decide +kernel)
private noncomputable def x45 := chunk40[5]!
private theorem length45 : x45.length=252 := by decide +kernel
private theorem decoded45 : row 45=x45.toArray := rowCert 45 x45 (by decide +kernel) length45
private theorem powers45 : rhoPowers 251 45=tab 46 row :=
  step powers44 decoded44 decoded45 length44 (by decide +kernel)
private noncomputable def x46 := chunk40[6]!
private theorem length46 : x46.length=252 := by decide +kernel
private theorem decoded46 : row 46=x46.toArray := rowCert 46 x46 (by decide +kernel) length46
private theorem powers46 : rhoPowers 251 46=tab 47 row :=
  step powers45 decoded45 decoded46 length45 (by decide +kernel)
private noncomputable def x47 := chunk40[7]!
private theorem length47 : x47.length=252 := by decide +kernel
private theorem decoded47 : row 47=x47.toArray := rowCert 47 x47 (by decide +kernel) length47
private theorem powers47 : rhoPowers 251 47=tab 48 row :=
  step powers46 decoded46 decoded47 length46 (by decide +kernel)

private noncomputable def chunk48 : List (List Interval) := eval% (candidates 48 8)
private noncomputable def x48 := chunk48[0]!
private theorem length48 : x48.length=252 := by decide +kernel
private theorem decoded48 : row 48=x48.toArray := rowCert 48 x48 (by decide +kernel) length48
private theorem powers48 : rhoPowers 251 48=tab 49 row :=
  step powers47 decoded47 decoded48 length47 (by decide +kernel)
private noncomputable def x49 := chunk48[1]!
private theorem length49 : x49.length=252 := by decide +kernel
private theorem decoded49 : row 49=x49.toArray := rowCert 49 x49 (by decide +kernel) length49
private theorem powers49 : rhoPowers 251 49=tab 50 row :=
  step powers48 decoded48 decoded49 length48 (by decide +kernel)
private noncomputable def x50 := chunk48[2]!
private theorem length50 : x50.length=252 := by decide +kernel
private theorem decoded50 : row 50=x50.toArray := rowCert 50 x50 (by decide +kernel) length50
private theorem powers50 : rhoPowers 251 50=tab 51 row :=
  step powers49 decoded49 decoded50 length49 (by decide +kernel)
private noncomputable def x51 := chunk48[3]!
private theorem length51 : x51.length=252 := by decide +kernel
private theorem decoded51 : row 51=x51.toArray := rowCert 51 x51 (by decide +kernel) length51
private theorem powers51 : rhoPowers 251 51=tab 52 row :=
  step powers50 decoded50 decoded51 length50 (by decide +kernel)
private noncomputable def x52 := chunk48[4]!
private theorem length52 : x52.length=252 := by decide +kernel
private theorem decoded52 : row 52=x52.toArray := rowCert 52 x52 (by decide +kernel) length52
private theorem powers52 : rhoPowers 251 52=tab 53 row :=
  step powers51 decoded51 decoded52 length51 (by decide +kernel)
private noncomputable def x53 := chunk48[5]!
private theorem length53 : x53.length=252 := by decide +kernel
private theorem decoded53 : row 53=x53.toArray := rowCert 53 x53 (by decide +kernel) length53
private theorem powers53 : rhoPowers 251 53=tab 54 row :=
  step powers52 decoded52 decoded53 length52 (by decide +kernel)
private noncomputable def x54 := chunk48[6]!
private theorem length54 : x54.length=252 := by decide +kernel
private theorem decoded54 : row 54=x54.toArray := rowCert 54 x54 (by decide +kernel) length54
private theorem powers54 : rhoPowers 251 54=tab 55 row :=
  step powers53 decoded53 decoded54 length53 (by decide +kernel)
private noncomputable def x55 := chunk48[7]!
private theorem length55 : x55.length=252 := by decide +kernel
private theorem decoded55 : row 55=x55.toArray := rowCert 55 x55 (by decide +kernel) length55
private theorem powers55 : rhoPowers 251 55=tab 56 row :=
  step powers54 decoded54 decoded55 length54 (by decide +kernel)

private noncomputable def chunk56 : List (List Interval) := eval% (candidates 56 8)
private noncomputable def x56 := chunk56[0]!
private theorem length56 : x56.length=252 := by decide +kernel
private theorem decoded56 : row 56=x56.toArray := rowCert 56 x56 (by decide +kernel) length56
private theorem powers56 : rhoPowers 251 56=tab 57 row :=
  step powers55 decoded55 decoded56 length55 (by decide +kernel)
private noncomputable def x57 := chunk56[1]!
private theorem length57 : x57.length=252 := by decide +kernel
private theorem decoded57 : row 57=x57.toArray := rowCert 57 x57 (by decide +kernel) length57
private theorem powers57 : rhoPowers 251 57=tab 58 row :=
  step powers56 decoded56 decoded57 length56 (by decide +kernel)
private noncomputable def x58 := chunk56[2]!
private theorem length58 : x58.length=252 := by decide +kernel
private theorem decoded58 : row 58=x58.toArray := rowCert 58 x58 (by decide +kernel) length58
private theorem powers58 : rhoPowers 251 58=tab 59 row :=
  step powers57 decoded57 decoded58 length57 (by decide +kernel)
private noncomputable def x59 := chunk56[3]!
private theorem length59 : x59.length=252 := by decide +kernel
private theorem decoded59 : row 59=x59.toArray := rowCert 59 x59 (by decide +kernel) length59
private theorem powers59 : rhoPowers 251 59=tab 60 row :=
  step powers58 decoded58 decoded59 length58 (by decide +kernel)
private noncomputable def x60 := chunk56[4]!
private theorem length60 : x60.length=252 := by decide +kernel
private theorem decoded60 : row 60=x60.toArray := rowCert 60 x60 (by decide +kernel) length60
private theorem powers60 : rhoPowers 251 60=tab 61 row :=
  step powers59 decoded59 decoded60 length59 (by decide +kernel)
private noncomputable def x61 := chunk56[5]!
private theorem length61 : x61.length=252 := by decide +kernel
private theorem decoded61 : row 61=x61.toArray := rowCert 61 x61 (by decide +kernel) length61
private theorem powers61 : rhoPowers 251 61=tab 62 row :=
  step powers60 decoded60 decoded61 length60 (by decide +kernel)
private noncomputable def x62 := chunk56[6]!
private theorem length62 : x62.length=252 := by decide +kernel
private theorem decoded62 : row 62=x62.toArray := rowCert 62 x62 (by decide +kernel) length62
private theorem powers62 : rhoPowers 251 62=tab 63 row :=
  step powers61 decoded61 decoded62 length61 (by decide +kernel)
private noncomputable def x63 := chunk56[7]!
private theorem length63 : x63.length=252 := by decide +kernel
private theorem decoded63 : row 63=x63.toArray := rowCert 63 x63 (by decide +kernel) length63
private theorem powers63 : rhoPowers 251 63=tab 64 row :=
  step powers62 decoded62 decoded63 length62 (by decide +kernel)

private noncomputable def chunk64 : List (List Interval) := eval% (candidates 64 8)
private noncomputable def x64 := chunk64[0]!
private theorem length64 : x64.length=252 := by decide +kernel
private theorem decoded64 : row 64=x64.toArray := rowCert 64 x64 (by decide +kernel) length64
private theorem powers64 : rhoPowers 251 64=tab 65 row :=
  step powers63 decoded63 decoded64 length63 (by decide +kernel)
private noncomputable def x65 := chunk64[1]!
private theorem length65 : x65.length=252 := by decide +kernel
private theorem decoded65 : row 65=x65.toArray := rowCert 65 x65 (by decide +kernel) length65
private theorem powers65 : rhoPowers 251 65=tab 66 row :=
  step powers64 decoded64 decoded65 length64 (by decide +kernel)
private noncomputable def x66 := chunk64[2]!
private theorem length66 : x66.length=252 := by decide +kernel
private theorem decoded66 : row 66=x66.toArray := rowCert 66 x66 (by decide +kernel) length66
private theorem powers66 : rhoPowers 251 66=tab 67 row :=
  step powers65 decoded65 decoded66 length65 (by decide +kernel)
private noncomputable def x67 := chunk64[3]!
private theorem length67 : x67.length=252 := by decide +kernel
private theorem decoded67 : row 67=x67.toArray := rowCert 67 x67 (by decide +kernel) length67
private theorem powers67 : rhoPowers 251 67=tab 68 row :=
  step powers66 decoded66 decoded67 length66 (by decide +kernel)
private noncomputable def x68 := chunk64[4]!
private theorem length68 : x68.length=252 := by decide +kernel
private theorem decoded68 : row 68=x68.toArray := rowCert 68 x68 (by decide +kernel) length68
private theorem powers68 : rhoPowers 251 68=tab 69 row :=
  step powers67 decoded67 decoded68 length67 (by decide +kernel)
private noncomputable def x69 := chunk64[5]!
private theorem length69 : x69.length=252 := by decide +kernel
private theorem decoded69 : row 69=x69.toArray := rowCert 69 x69 (by decide +kernel) length69
private theorem powers69 : rhoPowers 251 69=tab 70 row :=
  step powers68 decoded68 decoded69 length68 (by decide +kernel)
private noncomputable def x70 := chunk64[6]!
private theorem length70 : x70.length=252 := by decide +kernel
private theorem decoded70 : row 70=x70.toArray := rowCert 70 x70 (by decide +kernel) length70
private theorem powers70 : rhoPowers 251 70=tab 71 row :=
  step powers69 decoded69 decoded70 length69 (by decide +kernel)
private noncomputable def x71 := chunk64[7]!
private theorem length71 : x71.length=252 := by decide +kernel
private theorem decoded71 : row 71=x71.toArray := rowCert 71 x71 (by decide +kernel) length71
private theorem powers71 : rhoPowers 251 71=tab 72 row :=
  step powers70 decoded70 decoded71 length70 (by decide +kernel)

private noncomputable def chunk72 : List (List Interval) := eval% (candidates 72 8)
private noncomputable def x72 := chunk72[0]!
private theorem length72 : x72.length=252 := by decide +kernel
private theorem decoded72 : row 72=x72.toArray := rowCert 72 x72 (by decide +kernel) length72
private theorem powers72 : rhoPowers 251 72=tab 73 row :=
  step powers71 decoded71 decoded72 length71 (by decide +kernel)
private noncomputable def x73 := chunk72[1]!
private theorem length73 : x73.length=252 := by decide +kernel
private theorem decoded73 : row 73=x73.toArray := rowCert 73 x73 (by decide +kernel) length73
private theorem powers73 : rhoPowers 251 73=tab 74 row :=
  step powers72 decoded72 decoded73 length72 (by decide +kernel)
private noncomputable def x74 := chunk72[2]!
private theorem length74 : x74.length=252 := by decide +kernel
private theorem decoded74 : row 74=x74.toArray := rowCert 74 x74 (by decide +kernel) length74
private theorem powers74 : rhoPowers 251 74=tab 75 row :=
  step powers73 decoded73 decoded74 length73 (by decide +kernel)
private noncomputable def x75 := chunk72[3]!
private theorem length75 : x75.length=252 := by decide +kernel
private theorem decoded75 : row 75=x75.toArray := rowCert 75 x75 (by decide +kernel) length75
private theorem powers75 : rhoPowers 251 75=tab 76 row :=
  step powers74 decoded74 decoded75 length74 (by decide +kernel)
private noncomputable def x76 := chunk72[4]!
private theorem length76 : x76.length=252 := by decide +kernel
private theorem decoded76 : row 76=x76.toArray := rowCert 76 x76 (by decide +kernel) length76
private theorem powers76 : rhoPowers 251 76=tab 77 row :=
  step powers75 decoded75 decoded76 length75 (by decide +kernel)
private noncomputable def x77 := chunk72[5]!
private theorem length77 : x77.length=252 := by decide +kernel
private theorem decoded77 : row 77=x77.toArray := rowCert 77 x77 (by decide +kernel) length77
private theorem powers77 : rhoPowers 251 77=tab 78 row :=
  step powers76 decoded76 decoded77 length76 (by decide +kernel)
private noncomputable def x78 := chunk72[6]!
private theorem length78 : x78.length=252 := by decide +kernel
private theorem decoded78 : row 78=x78.toArray := rowCert 78 x78 (by decide +kernel) length78
private theorem powers78 : rhoPowers 251 78=tab 79 row :=
  step powers77 decoded77 decoded78 length77 (by decide +kernel)
private noncomputable def x79 := chunk72[7]!
private theorem length79 : x79.length=252 := by decide +kernel
private theorem decoded79 : row 79=x79.toArray := rowCert 79 x79 (by decide +kernel) length79
private theorem powers79 : rhoPowers 251 79=tab 80 row :=
  step powers78 decoded78 decoded79 length78 (by decide +kernel)

private noncomputable def chunk80 : List (List Interval) := eval% (candidates 80 8)
private noncomputable def x80 := chunk80[0]!
private theorem length80 : x80.length=252 := by decide +kernel
private theorem decoded80 : row 80=x80.toArray := rowCert 80 x80 (by decide +kernel) length80
private theorem powers80 : rhoPowers 251 80=tab 81 row :=
  step powers79 decoded79 decoded80 length79 (by decide +kernel)
private noncomputable def x81 := chunk80[1]!
private theorem length81 : x81.length=252 := by decide +kernel
private theorem decoded81 : row 81=x81.toArray := rowCert 81 x81 (by decide +kernel) length81
private theorem powers81 : rhoPowers 251 81=tab 82 row :=
  step powers80 decoded80 decoded81 length80 (by decide +kernel)
private noncomputable def x82 := chunk80[2]!
private theorem length82 : x82.length=252 := by decide +kernel
private theorem decoded82 : row 82=x82.toArray := rowCert 82 x82 (by decide +kernel) length82
private theorem powers82 : rhoPowers 251 82=tab 83 row :=
  step powers81 decoded81 decoded82 length81 (by decide +kernel)
private noncomputable def x83 := chunk80[3]!
private theorem length83 : x83.length=252 := by decide +kernel
private theorem decoded83 : row 83=x83.toArray := rowCert 83 x83 (by decide +kernel) length83
private theorem powers83 : rhoPowers 251 83=tab 84 row :=
  step powers82 decoded82 decoded83 length82 (by decide +kernel)
private noncomputable def x84 := chunk80[4]!
private theorem length84 : x84.length=252 := by decide +kernel
private theorem decoded84 : row 84=x84.toArray := rowCert 84 x84 (by decide +kernel) length84
private theorem powers84 : rhoPowers 251 84=tab 85 row :=
  step powers83 decoded83 decoded84 length83 (by decide +kernel)
private noncomputable def x85 := chunk80[5]!
private theorem length85 : x85.length=252 := by decide +kernel
private theorem decoded85 : row 85=x85.toArray := rowCert 85 x85 (by decide +kernel) length85
private theorem powers85 : rhoPowers 251 85=tab 86 row :=
  step powers84 decoded84 decoded85 length84 (by decide +kernel)
private noncomputable def x86 := chunk80[6]!
private theorem length86 : x86.length=252 := by decide +kernel
private theorem decoded86 : row 86=x86.toArray := rowCert 86 x86 (by decide +kernel) length86
private theorem powers86 : rhoPowers 251 86=tab 87 row :=
  step powers85 decoded85 decoded86 length85 (by decide +kernel)
private noncomputable def x87 := chunk80[7]!
private theorem length87 : x87.length=252 := by decide +kernel
private theorem decoded87 : row 87=x87.toArray := rowCert 87 x87 (by decide +kernel) length87
private theorem powers87 : rhoPowers 251 87=tab 88 row :=
  step powers86 decoded86 decoded87 length86 (by decide +kernel)

private noncomputable def chunk88 : List (List Interval) := eval% (candidates 88 8)
private noncomputable def x88 := chunk88[0]!
private theorem length88 : x88.length=252 := by decide +kernel
private theorem decoded88 : row 88=x88.toArray := rowCert 88 x88 (by decide +kernel) length88
private theorem powers88 : rhoPowers 251 88=tab 89 row :=
  step powers87 decoded87 decoded88 length87 (by decide +kernel)
private noncomputable def x89 := chunk88[1]!
private theorem length89 : x89.length=252 := by decide +kernel
private theorem decoded89 : row 89=x89.toArray := rowCert 89 x89 (by decide +kernel) length89
private theorem powers89 : rhoPowers 251 89=tab 90 row :=
  step powers88 decoded88 decoded89 length88 (by decide +kernel)
private noncomputable def x90 := chunk88[2]!
private theorem length90 : x90.length=252 := by decide +kernel
private theorem decoded90 : row 90=x90.toArray := rowCert 90 x90 (by decide +kernel) length90
private theorem powers90 : rhoPowers 251 90=tab 91 row :=
  step powers89 decoded89 decoded90 length89 (by decide +kernel)
private noncomputable def x91 := chunk88[3]!
private theorem length91 : x91.length=252 := by decide +kernel
private theorem decoded91 : row 91=x91.toArray := rowCert 91 x91 (by decide +kernel) length91
private theorem powers91 : rhoPowers 251 91=tab 92 row :=
  step powers90 decoded90 decoded91 length90 (by decide +kernel)
private noncomputable def x92 := chunk88[4]!
private theorem length92 : x92.length=252 := by decide +kernel
private theorem decoded92 : row 92=x92.toArray := rowCert 92 x92 (by decide +kernel) length92
private theorem powers92 : rhoPowers 251 92=tab 93 row :=
  step powers91 decoded91 decoded92 length91 (by decide +kernel)
private noncomputable def x93 := chunk88[5]!
private theorem length93 : x93.length=252 := by decide +kernel
private theorem decoded93 : row 93=x93.toArray := rowCert 93 x93 (by decide +kernel) length93
private theorem powers93 : rhoPowers 251 93=tab 94 row :=
  step powers92 decoded92 decoded93 length92 (by decide +kernel)
private noncomputable def x94 := chunk88[6]!
private theorem length94 : x94.length=252 := by decide +kernel
private theorem decoded94 : row 94=x94.toArray := rowCert 94 x94 (by decide +kernel) length94
private theorem powers94 : rhoPowers 251 94=tab 95 row :=
  step powers93 decoded93 decoded94 length93 (by decide +kernel)
private noncomputable def x95 := chunk88[7]!
private theorem length95 : x95.length=252 := by decide +kernel
private theorem decoded95 : row 95=x95.toArray := rowCert 95 x95 (by decide +kernel) length95
private theorem powers95 : rhoPowers 251 95=tab 96 row :=
  step powers94 decoded94 decoded95 length94 (by decide +kernel)

private noncomputable def chunk96 : List (List Interval) := eval% (candidates 96 8)
private noncomputable def x96 := chunk96[0]!
private theorem length96 : x96.length=252 := by decide +kernel
private theorem decoded96 : row 96=x96.toArray := rowCert 96 x96 (by decide +kernel) length96
private theorem powers96 : rhoPowers 251 96=tab 97 row :=
  step powers95 decoded95 decoded96 length95 (by decide +kernel)
private noncomputable def x97 := chunk96[1]!
private theorem length97 : x97.length=252 := by decide +kernel
private theorem decoded97 : row 97=x97.toArray := rowCert 97 x97 (by decide +kernel) length97
private theorem powers97 : rhoPowers 251 97=tab 98 row :=
  step powers96 decoded96 decoded97 length96 (by decide +kernel)
private noncomputable def x98 := chunk96[2]!
private theorem length98 : x98.length=252 := by decide +kernel
private theorem decoded98 : row 98=x98.toArray := rowCert 98 x98 (by decide +kernel) length98
private theorem powers98 : rhoPowers 251 98=tab 99 row :=
  step powers97 decoded97 decoded98 length97 (by decide +kernel)
private noncomputable def x99 := chunk96[3]!
private theorem length99 : x99.length=252 := by decide +kernel
private theorem decoded99 : row 99=x99.toArray := rowCert 99 x99 (by decide +kernel) length99
private theorem powers99 : rhoPowers 251 99=tab 100 row :=
  step powers98 decoded98 decoded99 length98 (by decide +kernel)
private noncomputable def x100 := chunk96[4]!
private theorem length100 : x100.length=252 := by decide +kernel
private theorem decoded100 : row 100=x100.toArray := rowCert 100 x100 (by decide +kernel) length100
private theorem powers100 : rhoPowers 251 100=tab 101 row :=
  step powers99 decoded99 decoded100 length99 (by decide +kernel)
private noncomputable def x101 := chunk96[5]!
private theorem length101 : x101.length=252 := by decide +kernel
private theorem decoded101 : row 101=x101.toArray := rowCert 101 x101 (by decide +kernel) length101
private theorem powers101 : rhoPowers 251 101=tab 102 row :=
  step powers100 decoded100 decoded101 length100 (by decide +kernel)
private noncomputable def x102 := chunk96[6]!
private theorem length102 : x102.length=252 := by decide +kernel
private theorem decoded102 : row 102=x102.toArray := rowCert 102 x102 (by decide +kernel) length102
private theorem powers102 : rhoPowers 251 102=tab 103 row :=
  step powers101 decoded101 decoded102 length101 (by decide +kernel)
private noncomputable def x103 := chunk96[7]!
private theorem length103 : x103.length=252 := by decide +kernel
private theorem decoded103 : row 103=x103.toArray := rowCert 103 x103 (by decide +kernel) length103
private theorem powers103 : rhoPowers 251 103=tab 104 row :=
  step powers102 decoded102 decoded103 length102 (by decide +kernel)

private noncomputable def chunk104 : List (List Interval) := eval% (candidates 104 8)
private noncomputable def x104 := chunk104[0]!
private theorem length104 : x104.length=252 := by decide +kernel
private theorem decoded104 : row 104=x104.toArray := rowCert 104 x104 (by decide +kernel) length104
private theorem powers104 : rhoPowers 251 104=tab 105 row :=
  step powers103 decoded103 decoded104 length103 (by decide +kernel)
private noncomputable def x105 := chunk104[1]!
private theorem length105 : x105.length=252 := by decide +kernel
private theorem decoded105 : row 105=x105.toArray := rowCert 105 x105 (by decide +kernel) length105
private theorem powers105 : rhoPowers 251 105=tab 106 row :=
  step powers104 decoded104 decoded105 length104 (by decide +kernel)
private noncomputable def x106 := chunk104[2]!
private theorem length106 : x106.length=252 := by decide +kernel
private theorem decoded106 : row 106=x106.toArray := rowCert 106 x106 (by decide +kernel) length106
private theorem powers106 : rhoPowers 251 106=tab 107 row :=
  step powers105 decoded105 decoded106 length105 (by decide +kernel)
private noncomputable def x107 := chunk104[3]!
private theorem length107 : x107.length=252 := by decide +kernel
private theorem decoded107 : row 107=x107.toArray := rowCert 107 x107 (by decide +kernel) length107
private theorem powers107 : rhoPowers 251 107=tab 108 row :=
  step powers106 decoded106 decoded107 length106 (by decide +kernel)
private noncomputable def x108 := chunk104[4]!
private theorem length108 : x108.length=252 := by decide +kernel
private theorem decoded108 : row 108=x108.toArray := rowCert 108 x108 (by decide +kernel) length108
private theorem powers108 : rhoPowers 251 108=tab 109 row :=
  step powers107 decoded107 decoded108 length107 (by decide +kernel)
private noncomputable def x109 := chunk104[5]!
private theorem length109 : x109.length=252 := by decide +kernel
private theorem decoded109 : row 109=x109.toArray := rowCert 109 x109 (by decide +kernel) length109
private theorem powers109 : rhoPowers 251 109=tab 110 row :=
  step powers108 decoded108 decoded109 length108 (by decide +kernel)
private noncomputable def x110 := chunk104[6]!
private theorem length110 : x110.length=252 := by decide +kernel
private theorem decoded110 : row 110=x110.toArray := rowCert 110 x110 (by decide +kernel) length110
private theorem powers110 : rhoPowers 251 110=tab 111 row :=
  step powers109 decoded109 decoded110 length109 (by decide +kernel)
private noncomputable def x111 := chunk104[7]!
private theorem length111 : x111.length=252 := by decide +kernel
private theorem decoded111 : row 111=x111.toArray := rowCert 111 x111 (by decide +kernel) length111
private theorem powers111 : rhoPowers 251 111=tab 112 row :=
  step powers110 decoded110 decoded111 length110 (by decide +kernel)

private noncomputable def chunk112 : List (List Interval) := eval% (candidates 112 8)
private noncomputable def x112 := chunk112[0]!
private theorem length112 : x112.length=252 := by decide +kernel
private theorem decoded112 : row 112=x112.toArray := rowCert 112 x112 (by decide +kernel) length112
private theorem powers112 : rhoPowers 251 112=tab 113 row :=
  step powers111 decoded111 decoded112 length111 (by decide +kernel)
private noncomputable def x113 := chunk112[1]!
private theorem length113 : x113.length=252 := by decide +kernel
private theorem decoded113 : row 113=x113.toArray := rowCert 113 x113 (by decide +kernel) length113
private theorem powers113 : rhoPowers 251 113=tab 114 row :=
  step powers112 decoded112 decoded113 length112 (by decide +kernel)
private noncomputable def x114 := chunk112[2]!
private theorem length114 : x114.length=252 := by decide +kernel
private theorem decoded114 : row 114=x114.toArray := rowCert 114 x114 (by decide +kernel) length114
private theorem powers114 : rhoPowers 251 114=tab 115 row :=
  step powers113 decoded113 decoded114 length113 (by decide +kernel)
private noncomputable def x115 := chunk112[3]!
private theorem length115 : x115.length=252 := by decide +kernel
private theorem decoded115 : row 115=x115.toArray := rowCert 115 x115 (by decide +kernel) length115
private theorem powers115 : rhoPowers 251 115=tab 116 row :=
  step powers114 decoded114 decoded115 length114 (by decide +kernel)
private noncomputable def x116 := chunk112[4]!
private theorem length116 : x116.length=252 := by decide +kernel
private theorem decoded116 : row 116=x116.toArray := rowCert 116 x116 (by decide +kernel) length116
private theorem powers116 : rhoPowers 251 116=tab 117 row :=
  step powers115 decoded115 decoded116 length115 (by decide +kernel)
private noncomputable def x117 := chunk112[5]!
private theorem length117 : x117.length=252 := by decide +kernel
private theorem decoded117 : row 117=x117.toArray := rowCert 117 x117 (by decide +kernel) length117
private theorem powers117 : rhoPowers 251 117=tab 118 row :=
  step powers116 decoded116 decoded117 length116 (by decide +kernel)
private noncomputable def x118 := chunk112[6]!
private theorem length118 : x118.length=252 := by decide +kernel
private theorem decoded118 : row 118=x118.toArray := rowCert 118 x118 (by decide +kernel) length118
private theorem powers118 : rhoPowers 251 118=tab 119 row :=
  step powers117 decoded117 decoded118 length117 (by decide +kernel)
private noncomputable def x119 := chunk112[7]!
private theorem length119 : x119.length=252 := by decide +kernel
private theorem decoded119 : row 119=x119.toArray := rowCert 119 x119 (by decide +kernel) length119
private theorem powers119 : rhoPowers 251 119=tab 120 row :=
  step powers118 decoded118 decoded119 length118 (by decide +kernel)

private noncomputable def chunk120 : List (List Interval) := eval% (candidates 120 8)
private noncomputable def x120 := chunk120[0]!
private theorem length120 : x120.length=252 := by decide +kernel
private theorem decoded120 : row 120=x120.toArray := rowCert 120 x120 (by decide +kernel) length120
private theorem powers120 : rhoPowers 251 120=tab 121 row :=
  step powers119 decoded119 decoded120 length119 (by decide +kernel)
private noncomputable def x121 := chunk120[1]!
private theorem length121 : x121.length=252 := by decide +kernel
private theorem decoded121 : row 121=x121.toArray := rowCert 121 x121 (by decide +kernel) length121
private theorem powers121 : rhoPowers 251 121=tab 122 row :=
  step powers120 decoded120 decoded121 length120 (by decide +kernel)
private noncomputable def x122 := chunk120[2]!
private theorem length122 : x122.length=252 := by decide +kernel
private theorem decoded122 : row 122=x122.toArray := rowCert 122 x122 (by decide +kernel) length122
private theorem powers122 : rhoPowers 251 122=tab 123 row :=
  step powers121 decoded121 decoded122 length121 (by decide +kernel)
private noncomputable def x123 := chunk120[3]!
private theorem length123 : x123.length=252 := by decide +kernel
private theorem decoded123 : row 123=x123.toArray := rowCert 123 x123 (by decide +kernel) length123
private theorem powers123 : rhoPowers 251 123=tab 124 row :=
  step powers122 decoded122 decoded123 length122 (by decide +kernel)
private noncomputable def x124 := chunk120[4]!
private theorem length124 : x124.length=252 := by decide +kernel
private theorem decoded124 : row 124=x124.toArray := rowCert 124 x124 (by decide +kernel) length124
private theorem powers124 : rhoPowers 251 124=tab 125 row :=
  step powers123 decoded123 decoded124 length123 (by decide +kernel)
private noncomputable def x125 := chunk120[5]!
private theorem length125 : x125.length=252 := by decide +kernel
private theorem decoded125 : row 125=x125.toArray := rowCert 125 x125 (by decide +kernel) length125
private theorem powers125 : rhoPowers 251 125=tab 126 row :=
  step powers124 decoded124 decoded125 length124 (by decide +kernel)
private noncomputable def x126 := chunk120[6]!
private theorem length126 : x126.length=252 := by decide +kernel
private theorem decoded126 : row 126=x126.toArray := rowCert 126 x126 (by decide +kernel) length126
private theorem powers126 : rhoPowers 251 126=tab 127 row :=
  step powers125 decoded125 decoded126 length125 (by decide +kernel)
private noncomputable def x127 := chunk120[7]!
private theorem length127 : x127.length=252 := by decide +kernel
private theorem decoded127 : row 127=x127.toArray := rowCert 127 x127 (by decide +kernel) length127
private theorem powers127 : rhoPowers 251 127=tab 128 row :=
  step powers126 decoded126 decoded127 length126 (by decide +kernel)

private noncomputable def chunk128 : List (List Interval) := eval% (candidates 128 8)
private noncomputable def x128 := chunk128[0]!
private theorem length128 : x128.length=252 := by decide +kernel
private theorem decoded128 : row 128=x128.toArray := rowCert 128 x128 (by decide +kernel) length128
private theorem powers128 : rhoPowers 251 128=tab 129 row :=
  step powers127 decoded127 decoded128 length127 (by decide +kernel)
private noncomputable def x129 := chunk128[1]!
private theorem length129 : x129.length=252 := by decide +kernel
private theorem decoded129 : row 129=x129.toArray := rowCert 129 x129 (by decide +kernel) length129
private theorem powers129 : rhoPowers 251 129=tab 130 row :=
  step powers128 decoded128 decoded129 length128 (by decide +kernel)
private noncomputable def x130 := chunk128[2]!
private theorem length130 : x130.length=252 := by decide +kernel
private theorem decoded130 : row 130=x130.toArray := rowCert 130 x130 (by decide +kernel) length130
private theorem powers130 : rhoPowers 251 130=tab 131 row :=
  step powers129 decoded129 decoded130 length129 (by decide +kernel)
private noncomputable def x131 := chunk128[3]!
private theorem length131 : x131.length=252 := by decide +kernel
private theorem decoded131 : row 131=x131.toArray := rowCert 131 x131 (by decide +kernel) length131
private theorem powers131 : rhoPowers 251 131=tab 132 row :=
  step powers130 decoded130 decoded131 length130 (by decide +kernel)
private noncomputable def x132 := chunk128[4]!
private theorem length132 : x132.length=252 := by decide +kernel
private theorem decoded132 : row 132=x132.toArray := rowCert 132 x132 (by decide +kernel) length132
private theorem powers132 : rhoPowers 251 132=tab 133 row :=
  step powers131 decoded131 decoded132 length131 (by decide +kernel)
private noncomputable def x133 := chunk128[5]!
private theorem length133 : x133.length=252 := by decide +kernel
private theorem decoded133 : row 133=x133.toArray := rowCert 133 x133 (by decide +kernel) length133
private theorem powers133 : rhoPowers 251 133=tab 134 row :=
  step powers132 decoded132 decoded133 length132 (by decide +kernel)
private noncomputable def x134 := chunk128[6]!
private theorem length134 : x134.length=252 := by decide +kernel
private theorem decoded134 : row 134=x134.toArray := rowCert 134 x134 (by decide +kernel) length134
private theorem powers134 : rhoPowers 251 134=tab 135 row :=
  step powers133 decoded133 decoded134 length133 (by decide +kernel)
private noncomputable def x135 := chunk128[7]!
private theorem length135 : x135.length=252 := by decide +kernel
private theorem decoded135 : row 135=x135.toArray := rowCert 135 x135 (by decide +kernel) length135
private theorem powers135 : rhoPowers 251 135=tab 136 row :=
  step powers134 decoded134 decoded135 length134 (by decide +kernel)

private noncomputable def chunk136 : List (List Interval) := eval% (candidates 136 8)
private noncomputable def x136 := chunk136[0]!
private theorem length136 : x136.length=252 := by decide +kernel
private theorem decoded136 : row 136=x136.toArray := rowCert 136 x136 (by decide +kernel) length136
private theorem powers136 : rhoPowers 251 136=tab 137 row :=
  step powers135 decoded135 decoded136 length135 (by decide +kernel)
private noncomputable def x137 := chunk136[1]!
private theorem length137 : x137.length=252 := by decide +kernel
private theorem decoded137 : row 137=x137.toArray := rowCert 137 x137 (by decide +kernel) length137
private theorem powers137 : rhoPowers 251 137=tab 138 row :=
  step powers136 decoded136 decoded137 length136 (by decide +kernel)
private noncomputable def x138 := chunk136[2]!
private theorem length138 : x138.length=252 := by decide +kernel
private theorem decoded138 : row 138=x138.toArray := rowCert 138 x138 (by decide +kernel) length138
private theorem powers138 : rhoPowers 251 138=tab 139 row :=
  step powers137 decoded137 decoded138 length137 (by decide +kernel)
private noncomputable def x139 := chunk136[3]!
private theorem length139 : x139.length=252 := by decide +kernel
private theorem decoded139 : row 139=x139.toArray := rowCert 139 x139 (by decide +kernel) length139
private theorem powers139 : rhoPowers 251 139=tab 140 row :=
  step powers138 decoded138 decoded139 length138 (by decide +kernel)
private noncomputable def x140 := chunk136[4]!
private theorem length140 : x140.length=252 := by decide +kernel
private theorem decoded140 : row 140=x140.toArray := rowCert 140 x140 (by decide +kernel) length140
private theorem powers140 : rhoPowers 251 140=tab 141 row :=
  step powers139 decoded139 decoded140 length139 (by decide +kernel)
private noncomputable def x141 := chunk136[5]!
private theorem length141 : x141.length=252 := by decide +kernel
private theorem decoded141 : row 141=x141.toArray := rowCert 141 x141 (by decide +kernel) length141
private theorem powers141 : rhoPowers 251 141=tab 142 row :=
  step powers140 decoded140 decoded141 length140 (by decide +kernel)
private noncomputable def x142 := chunk136[6]!
private theorem length142 : x142.length=252 := by decide +kernel
private theorem decoded142 : row 142=x142.toArray := rowCert 142 x142 (by decide +kernel) length142
private theorem powers142 : rhoPowers 251 142=tab 143 row :=
  step powers141 decoded141 decoded142 length141 (by decide +kernel)
private noncomputable def x143 := chunk136[7]!
private theorem length143 : x143.length=252 := by decide +kernel
private theorem decoded143 : row 143=x143.toArray := rowCert 143 x143 (by decide +kernel) length143
private theorem powers143 : rhoPowers 251 143=tab 144 row :=
  step powers142 decoded142 decoded143 length142 (by decide +kernel)

private noncomputable def chunk144 : List (List Interval) := eval% (candidates 144 8)
private noncomputable def x144 := chunk144[0]!
private theorem length144 : x144.length=252 := by decide +kernel
private theorem decoded144 : row 144=x144.toArray := rowCert 144 x144 (by decide +kernel) length144
private theorem powers144 : rhoPowers 251 144=tab 145 row :=
  step powers143 decoded143 decoded144 length143 (by decide +kernel)
private noncomputable def x145 := chunk144[1]!
private theorem length145 : x145.length=252 := by decide +kernel
private theorem decoded145 : row 145=x145.toArray := rowCert 145 x145 (by decide +kernel) length145
private theorem powers145 : rhoPowers 251 145=tab 146 row :=
  step powers144 decoded144 decoded145 length144 (by decide +kernel)
private noncomputable def x146 := chunk144[2]!
private theorem length146 : x146.length=252 := by decide +kernel
private theorem decoded146 : row 146=x146.toArray := rowCert 146 x146 (by decide +kernel) length146
private theorem powers146 : rhoPowers 251 146=tab 147 row :=
  step powers145 decoded145 decoded146 length145 (by decide +kernel)
private noncomputable def x147 := chunk144[3]!
private theorem length147 : x147.length=252 := by decide +kernel
private theorem decoded147 : row 147=x147.toArray := rowCert 147 x147 (by decide +kernel) length147
private theorem powers147 : rhoPowers 251 147=tab 148 row :=
  step powers146 decoded146 decoded147 length146 (by decide +kernel)
private noncomputable def x148 := chunk144[4]!
private theorem length148 : x148.length=252 := by decide +kernel
private theorem decoded148 : row 148=x148.toArray := rowCert 148 x148 (by decide +kernel) length148
private theorem powers148 : rhoPowers 251 148=tab 149 row :=
  step powers147 decoded147 decoded148 length147 (by decide +kernel)
private noncomputable def x149 := chunk144[5]!
private theorem length149 : x149.length=252 := by decide +kernel
private theorem decoded149 : row 149=x149.toArray := rowCert 149 x149 (by decide +kernel) length149
private theorem powers149 : rhoPowers 251 149=tab 150 row :=
  step powers148 decoded148 decoded149 length148 (by decide +kernel)
private noncomputable def x150 := chunk144[6]!
private theorem length150 : x150.length=252 := by decide +kernel
private theorem decoded150 : row 150=x150.toArray := rowCert 150 x150 (by decide +kernel) length150
private theorem powers150 : rhoPowers 251 150=tab 151 row :=
  step powers149 decoded149 decoded150 length149 (by decide +kernel)
private noncomputable def x151 := chunk144[7]!
private theorem length151 : x151.length=252 := by decide +kernel
private theorem decoded151 : row 151=x151.toArray := rowCert 151 x151 (by decide +kernel) length151
private theorem powers151 : rhoPowers 251 151=tab 152 row :=
  step powers150 decoded150 decoded151 length150 (by decide +kernel)

private noncomputable def chunk152 : List (List Interval) := eval% (candidates 152 8)
private noncomputable def x152 := chunk152[0]!
private theorem length152 : x152.length=252 := by decide +kernel
private theorem decoded152 : row 152=x152.toArray := rowCert 152 x152 (by decide +kernel) length152
private theorem powers152 : rhoPowers 251 152=tab 153 row :=
  step powers151 decoded151 decoded152 length151 (by decide +kernel)
private noncomputable def x153 := chunk152[1]!
private theorem length153 : x153.length=252 := by decide +kernel
private theorem decoded153 : row 153=x153.toArray := rowCert 153 x153 (by decide +kernel) length153
private theorem powers153 : rhoPowers 251 153=tab 154 row :=
  step powers152 decoded152 decoded153 length152 (by decide +kernel)
private noncomputable def x154 := chunk152[2]!
private theorem length154 : x154.length=252 := by decide +kernel
private theorem decoded154 : row 154=x154.toArray := rowCert 154 x154 (by decide +kernel) length154
private theorem powers154 : rhoPowers 251 154=tab 155 row :=
  step powers153 decoded153 decoded154 length153 (by decide +kernel)
private noncomputable def x155 := chunk152[3]!
private theorem length155 : x155.length=252 := by decide +kernel
private theorem decoded155 : row 155=x155.toArray := rowCert 155 x155 (by decide +kernel) length155
private theorem powers155 : rhoPowers 251 155=tab 156 row :=
  step powers154 decoded154 decoded155 length154 (by decide +kernel)
private noncomputable def x156 := chunk152[4]!
private theorem length156 : x156.length=252 := by decide +kernel
private theorem decoded156 : row 156=x156.toArray := rowCert 156 x156 (by decide +kernel) length156
private theorem powers156 : rhoPowers 251 156=tab 157 row :=
  step powers155 decoded155 decoded156 length155 (by decide +kernel)
private noncomputable def x157 := chunk152[5]!
private theorem length157 : x157.length=252 := by decide +kernel
private theorem decoded157 : row 157=x157.toArray := rowCert 157 x157 (by decide +kernel) length157
private theorem powers157 : rhoPowers 251 157=tab 158 row :=
  step powers156 decoded156 decoded157 length156 (by decide +kernel)
private noncomputable def x158 := chunk152[6]!
private theorem length158 : x158.length=252 := by decide +kernel
private theorem decoded158 : row 158=x158.toArray := rowCert 158 x158 (by decide +kernel) length158
private theorem powers158 : rhoPowers 251 158=tab 159 row :=
  step powers157 decoded157 decoded158 length157 (by decide +kernel)
private noncomputable def x159 := chunk152[7]!
private theorem length159 : x159.length=252 := by decide +kernel
private theorem decoded159 : row 159=x159.toArray := rowCert 159 x159 (by decide +kernel) length159
private theorem powers159 : rhoPowers 251 159=tab 160 row :=
  step powers158 decoded158 decoded159 length158 (by decide +kernel)

private noncomputable def chunk160 : List (List Interval) := eval% (candidates 160 8)
private noncomputable def x160 := chunk160[0]!
private theorem length160 : x160.length=252 := by decide +kernel
private theorem decoded160 : row 160=x160.toArray := rowCert 160 x160 (by decide +kernel) length160
private theorem powers160 : rhoPowers 251 160=tab 161 row :=
  step powers159 decoded159 decoded160 length159 (by decide +kernel)
private noncomputable def x161 := chunk160[1]!
private theorem length161 : x161.length=252 := by decide +kernel
private theorem decoded161 : row 161=x161.toArray := rowCert 161 x161 (by decide +kernel) length161
private theorem powers161 : rhoPowers 251 161=tab 162 row :=
  step powers160 decoded160 decoded161 length160 (by decide +kernel)
private noncomputable def x162 := chunk160[2]!
private theorem length162 : x162.length=252 := by decide +kernel
private theorem decoded162 : row 162=x162.toArray := rowCert 162 x162 (by decide +kernel) length162
private theorem powers162 : rhoPowers 251 162=tab 163 row :=
  step powers161 decoded161 decoded162 length161 (by decide +kernel)
private noncomputable def x163 := chunk160[3]!
private theorem length163 : x163.length=252 := by decide +kernel
private theorem decoded163 : row 163=x163.toArray := rowCert 163 x163 (by decide +kernel) length163
private theorem powers163 : rhoPowers 251 163=tab 164 row :=
  step powers162 decoded162 decoded163 length162 (by decide +kernel)
private noncomputable def x164 := chunk160[4]!
private theorem length164 : x164.length=252 := by decide +kernel
private theorem decoded164 : row 164=x164.toArray := rowCert 164 x164 (by decide +kernel) length164
private theorem powers164 : rhoPowers 251 164=tab 165 row :=
  step powers163 decoded163 decoded164 length163 (by decide +kernel)
private noncomputable def x165 := chunk160[5]!
private theorem length165 : x165.length=252 := by decide +kernel
private theorem decoded165 : row 165=x165.toArray := rowCert 165 x165 (by decide +kernel) length165
private theorem powers165 : rhoPowers 251 165=tab 166 row :=
  step powers164 decoded164 decoded165 length164 (by decide +kernel)
private noncomputable def x166 := chunk160[6]!
private theorem length166 : x166.length=252 := by decide +kernel
private theorem decoded166 : row 166=x166.toArray := rowCert 166 x166 (by decide +kernel) length166
private theorem powers166 : rhoPowers 251 166=tab 167 row :=
  step powers165 decoded165 decoded166 length165 (by decide +kernel)
private noncomputable def x167 := chunk160[7]!
private theorem length167 : x167.length=252 := by decide +kernel
private theorem decoded167 : row 167=x167.toArray := rowCert 167 x167 (by decide +kernel) length167
private theorem powers167 : rhoPowers 251 167=tab 168 row :=
  step powers166 decoded166 decoded167 length166 (by decide +kernel)

private noncomputable def chunk168 : List (List Interval) := eval% (candidates 168 8)
private noncomputable def x168 := chunk168[0]!
private theorem length168 : x168.length=252 := by decide +kernel
private theorem decoded168 : row 168=x168.toArray := rowCert 168 x168 (by decide +kernel) length168
private theorem powers168 : rhoPowers 251 168=tab 169 row :=
  step powers167 decoded167 decoded168 length167 (by decide +kernel)
private noncomputable def x169 := chunk168[1]!
private theorem length169 : x169.length=252 := by decide +kernel
private theorem decoded169 : row 169=x169.toArray := rowCert 169 x169 (by decide +kernel) length169
private theorem powers169 : rhoPowers 251 169=tab 170 row :=
  step powers168 decoded168 decoded169 length168 (by decide +kernel)
private noncomputable def x170 := chunk168[2]!
private theorem length170 : x170.length=252 := by decide +kernel
private theorem decoded170 : row 170=x170.toArray := rowCert 170 x170 (by decide +kernel) length170
private theorem powers170 : rhoPowers 251 170=tab 171 row :=
  step powers169 decoded169 decoded170 length169 (by decide +kernel)
private noncomputable def x171 := chunk168[3]!
private theorem length171 : x171.length=252 := by decide +kernel
private theorem decoded171 : row 171=x171.toArray := rowCert 171 x171 (by decide +kernel) length171
private theorem powers171 : rhoPowers 251 171=tab 172 row :=
  step powers170 decoded170 decoded171 length170 (by decide +kernel)
private noncomputable def x172 := chunk168[4]!
private theorem length172 : x172.length=252 := by decide +kernel
private theorem decoded172 : row 172=x172.toArray := rowCert 172 x172 (by decide +kernel) length172
private theorem powers172 : rhoPowers 251 172=tab 173 row :=
  step powers171 decoded171 decoded172 length171 (by decide +kernel)
private noncomputable def x173 := chunk168[5]!
private theorem length173 : x173.length=252 := by decide +kernel
private theorem decoded173 : row 173=x173.toArray := rowCert 173 x173 (by decide +kernel) length173
private theorem powers173 : rhoPowers 251 173=tab 174 row :=
  step powers172 decoded172 decoded173 length172 (by decide +kernel)
private noncomputable def x174 := chunk168[6]!
private theorem length174 : x174.length=252 := by decide +kernel
private theorem decoded174 : row 174=x174.toArray := rowCert 174 x174 (by decide +kernel) length174
private theorem powers174 : rhoPowers 251 174=tab 175 row :=
  step powers173 decoded173 decoded174 length173 (by decide +kernel)
private noncomputable def x175 := chunk168[7]!
private theorem length175 : x175.length=252 := by decide +kernel
private theorem decoded175 : row 175=x175.toArray := rowCert 175 x175 (by decide +kernel) length175
private theorem powers175 : rhoPowers 251 175=tab 176 row :=
  step powers174 decoded174 decoded175 length174 (by decide +kernel)

private noncomputable def chunk176 : List (List Interval) := eval% (candidates 176 8)
private noncomputable def x176 := chunk176[0]!
private theorem length176 : x176.length=252 := by decide +kernel
private theorem decoded176 : row 176=x176.toArray := rowCert 176 x176 (by decide +kernel) length176
private theorem powers176 : rhoPowers 251 176=tab 177 row :=
  step powers175 decoded175 decoded176 length175 (by decide +kernel)
private noncomputable def x177 := chunk176[1]!
private theorem length177 : x177.length=252 := by decide +kernel
private theorem decoded177 : row 177=x177.toArray := rowCert 177 x177 (by decide +kernel) length177
private theorem powers177 : rhoPowers 251 177=tab 178 row :=
  step powers176 decoded176 decoded177 length176 (by decide +kernel)
private noncomputable def x178 := chunk176[2]!
private theorem length178 : x178.length=252 := by decide +kernel
private theorem decoded178 : row 178=x178.toArray := rowCert 178 x178 (by decide +kernel) length178
private theorem powers178 : rhoPowers 251 178=tab 179 row :=
  step powers177 decoded177 decoded178 length177 (by decide +kernel)
private noncomputable def x179 := chunk176[3]!
private theorem length179 : x179.length=252 := by decide +kernel
private theorem decoded179 : row 179=x179.toArray := rowCert 179 x179 (by decide +kernel) length179
private theorem powers179 : rhoPowers 251 179=tab 180 row :=
  step powers178 decoded178 decoded179 length178 (by decide +kernel)
private noncomputable def x180 := chunk176[4]!
private theorem length180 : x180.length=252 := by decide +kernel
private theorem decoded180 : row 180=x180.toArray := rowCert 180 x180 (by decide +kernel) length180
private theorem powers180 : rhoPowers 251 180=tab 181 row :=
  step powers179 decoded179 decoded180 length179 (by decide +kernel)
private noncomputable def x181 := chunk176[5]!
private theorem length181 : x181.length=252 := by decide +kernel
private theorem decoded181 : row 181=x181.toArray := rowCert 181 x181 (by decide +kernel) length181
private theorem powers181 : rhoPowers 251 181=tab 182 row :=
  step powers180 decoded180 decoded181 length180 (by decide +kernel)
private noncomputable def x182 := chunk176[6]!
private theorem length182 : x182.length=252 := by decide +kernel
private theorem decoded182 : row 182=x182.toArray := rowCert 182 x182 (by decide +kernel) length182
private theorem powers182 : rhoPowers 251 182=tab 183 row :=
  step powers181 decoded181 decoded182 length181 (by decide +kernel)
private noncomputable def x183 := chunk176[7]!
private theorem length183 : x183.length=252 := by decide +kernel
private theorem decoded183 : row 183=x183.toArray := rowCert 183 x183 (by decide +kernel) length183
private theorem powers183 : rhoPowers 251 183=tab 184 row :=
  step powers182 decoded182 decoded183 length182 (by decide +kernel)

private noncomputable def chunk184 : List (List Interval) := eval% (candidates 184 8)
private noncomputable def x184 := chunk184[0]!
private theorem length184 : x184.length=252 := by decide +kernel
private theorem decoded184 : row 184=x184.toArray := rowCert 184 x184 (by decide +kernel) length184
private theorem powers184 : rhoPowers 251 184=tab 185 row :=
  step powers183 decoded183 decoded184 length183 (by decide +kernel)
private noncomputable def x185 := chunk184[1]!
private theorem length185 : x185.length=252 := by decide +kernel
private theorem decoded185 : row 185=x185.toArray := rowCert 185 x185 (by decide +kernel) length185
private theorem powers185 : rhoPowers 251 185=tab 186 row :=
  step powers184 decoded184 decoded185 length184 (by decide +kernel)
private noncomputable def x186 := chunk184[2]!
private theorem length186 : x186.length=252 := by decide +kernel
private theorem decoded186 : row 186=x186.toArray := rowCert 186 x186 (by decide +kernel) length186
private theorem powers186 : rhoPowers 251 186=tab 187 row :=
  step powers185 decoded185 decoded186 length185 (by decide +kernel)
private noncomputable def x187 := chunk184[3]!
private theorem length187 : x187.length=252 := by decide +kernel
private theorem decoded187 : row 187=x187.toArray := rowCert 187 x187 (by decide +kernel) length187
private theorem powers187 : rhoPowers 251 187=tab 188 row :=
  step powers186 decoded186 decoded187 length186 (by decide +kernel)
private noncomputable def x188 := chunk184[4]!
private theorem length188 : x188.length=252 := by decide +kernel
private theorem decoded188 : row 188=x188.toArray := rowCert 188 x188 (by decide +kernel) length188
private theorem powers188 : rhoPowers 251 188=tab 189 row :=
  step powers187 decoded187 decoded188 length187 (by decide +kernel)
private noncomputable def x189 := chunk184[5]!
private theorem length189 : x189.length=252 := by decide +kernel
private theorem decoded189 : row 189=x189.toArray := rowCert 189 x189 (by decide +kernel) length189
private theorem powers189 : rhoPowers 251 189=tab 190 row :=
  step powers188 decoded188 decoded189 length188 (by decide +kernel)
private noncomputable def x190 := chunk184[6]!
private theorem length190 : x190.length=252 := by decide +kernel
private theorem decoded190 : row 190=x190.toArray := rowCert 190 x190 (by decide +kernel) length190
private theorem powers190 : rhoPowers 251 190=tab 191 row :=
  step powers189 decoded189 decoded190 length189 (by decide +kernel)
private noncomputable def x191 := chunk184[7]!
private theorem length191 : x191.length=252 := by decide +kernel
private theorem decoded191 : row 191=x191.toArray := rowCert 191 x191 (by decide +kernel) length191
private theorem powers191 : rhoPowers 251 191=tab 192 row :=
  step powers190 decoded190 decoded191 length190 (by decide +kernel)

private noncomputable def chunk192 : List (List Interval) := eval% (candidates 192 8)
private noncomputable def x192 := chunk192[0]!
private theorem length192 : x192.length=252 := by decide +kernel
private theorem decoded192 : row 192=x192.toArray := rowCert 192 x192 (by decide +kernel) length192
private theorem powers192 : rhoPowers 251 192=tab 193 row :=
  step powers191 decoded191 decoded192 length191 (by decide +kernel)
private noncomputable def x193 := chunk192[1]!
private theorem length193 : x193.length=252 := by decide +kernel
private theorem decoded193 : row 193=x193.toArray := rowCert 193 x193 (by decide +kernel) length193
private theorem powers193 : rhoPowers 251 193=tab 194 row :=
  step powers192 decoded192 decoded193 length192 (by decide +kernel)
private noncomputable def x194 := chunk192[2]!
private theorem length194 : x194.length=252 := by decide +kernel
private theorem decoded194 : row 194=x194.toArray := rowCert 194 x194 (by decide +kernel) length194
private theorem powers194 : rhoPowers 251 194=tab 195 row :=
  step powers193 decoded193 decoded194 length193 (by decide +kernel)
private noncomputable def x195 := chunk192[3]!
private theorem length195 : x195.length=252 := by decide +kernel
private theorem decoded195 : row 195=x195.toArray := rowCert 195 x195 (by decide +kernel) length195
private theorem powers195 : rhoPowers 251 195=tab 196 row :=
  step powers194 decoded194 decoded195 length194 (by decide +kernel)
private noncomputable def x196 := chunk192[4]!
private theorem length196 : x196.length=252 := by decide +kernel
private theorem decoded196 : row 196=x196.toArray := rowCert 196 x196 (by decide +kernel) length196
private theorem powers196 : rhoPowers 251 196=tab 197 row :=
  step powers195 decoded195 decoded196 length195 (by decide +kernel)
private noncomputable def x197 := chunk192[5]!
private theorem length197 : x197.length=252 := by decide +kernel
private theorem decoded197 : row 197=x197.toArray := rowCert 197 x197 (by decide +kernel) length197
private theorem powers197 : rhoPowers 251 197=tab 198 row :=
  step powers196 decoded196 decoded197 length196 (by decide +kernel)
private noncomputable def x198 := chunk192[6]!
private theorem length198 : x198.length=252 := by decide +kernel
private theorem decoded198 : row 198=x198.toArray := rowCert 198 x198 (by decide +kernel) length198
private theorem powers198 : rhoPowers 251 198=tab 199 row :=
  step powers197 decoded197 decoded198 length197 (by decide +kernel)
private noncomputable def x199 := chunk192[7]!
private theorem length199 : x199.length=252 := by decide +kernel
private theorem decoded199 : row 199=x199.toArray := rowCert 199 x199 (by decide +kernel) length199
private theorem powers199 : rhoPowers 251 199=tab 200 row :=
  step powers198 decoded198 decoded199 length198 (by decide +kernel)

private noncomputable def chunk200 : List (List Interval) := eval% (candidates 200 8)
private noncomputable def x200 := chunk200[0]!
private theorem length200 : x200.length=252 := by decide +kernel
private theorem decoded200 : row 200=x200.toArray := rowCert 200 x200 (by decide +kernel) length200
private theorem powers200 : rhoPowers 251 200=tab 201 row :=
  step powers199 decoded199 decoded200 length199 (by decide +kernel)
private noncomputable def x201 := chunk200[1]!
private theorem length201 : x201.length=252 := by decide +kernel
private theorem decoded201 : row 201=x201.toArray := rowCert 201 x201 (by decide +kernel) length201
private theorem powers201 : rhoPowers 251 201=tab 202 row :=
  step powers200 decoded200 decoded201 length200 (by decide +kernel)
private noncomputable def x202 := chunk200[2]!
private theorem length202 : x202.length=252 := by decide +kernel
private theorem decoded202 : row 202=x202.toArray := rowCert 202 x202 (by decide +kernel) length202
private theorem powers202 : rhoPowers 251 202=tab 203 row :=
  step powers201 decoded201 decoded202 length201 (by decide +kernel)
private noncomputable def x203 := chunk200[3]!
private theorem length203 : x203.length=252 := by decide +kernel
private theorem decoded203 : row 203=x203.toArray := rowCert 203 x203 (by decide +kernel) length203
private theorem powers203 : rhoPowers 251 203=tab 204 row :=
  step powers202 decoded202 decoded203 length202 (by decide +kernel)
private noncomputable def x204 := chunk200[4]!
private theorem length204 : x204.length=252 := by decide +kernel
private theorem decoded204 : row 204=x204.toArray := rowCert 204 x204 (by decide +kernel) length204
private theorem powers204 : rhoPowers 251 204=tab 205 row :=
  step powers203 decoded203 decoded204 length203 (by decide +kernel)
private noncomputable def x205 := chunk200[5]!
private theorem length205 : x205.length=252 := by decide +kernel
private theorem decoded205 : row 205=x205.toArray := rowCert 205 x205 (by decide +kernel) length205
private theorem powers205 : rhoPowers 251 205=tab 206 row :=
  step powers204 decoded204 decoded205 length204 (by decide +kernel)
private noncomputable def x206 := chunk200[6]!
private theorem length206 : x206.length=252 := by decide +kernel
private theorem decoded206 : row 206=x206.toArray := rowCert 206 x206 (by decide +kernel) length206
private theorem powers206 : rhoPowers 251 206=tab 207 row :=
  step powers205 decoded205 decoded206 length205 (by decide +kernel)
private noncomputable def x207 := chunk200[7]!
private theorem length207 : x207.length=252 := by decide +kernel
private theorem decoded207 : row 207=x207.toArray := rowCert 207 x207 (by decide +kernel) length207
private theorem powers207 : rhoPowers 251 207=tab 208 row :=
  step powers206 decoded206 decoded207 length206 (by decide +kernel)

private noncomputable def chunk208 : List (List Interval) := eval% (candidates 208 8)
private noncomputable def x208 := chunk208[0]!
private theorem length208 : x208.length=252 := by decide +kernel
private theorem decoded208 : row 208=x208.toArray := rowCert 208 x208 (by decide +kernel) length208
private theorem powers208 : rhoPowers 251 208=tab 209 row :=
  step powers207 decoded207 decoded208 length207 (by decide +kernel)
private noncomputable def x209 := chunk208[1]!
private theorem length209 : x209.length=252 := by decide +kernel
private theorem decoded209 : row 209=x209.toArray := rowCert 209 x209 (by decide +kernel) length209
private theorem powers209 : rhoPowers 251 209=tab 210 row :=
  step powers208 decoded208 decoded209 length208 (by decide +kernel)
private noncomputable def x210 := chunk208[2]!
private theorem length210 : x210.length=252 := by decide +kernel
private theorem decoded210 : row 210=x210.toArray := rowCert 210 x210 (by decide +kernel) length210
private theorem powers210 : rhoPowers 251 210=tab 211 row :=
  step powers209 decoded209 decoded210 length209 (by decide +kernel)
private noncomputable def x211 := chunk208[3]!
private theorem length211 : x211.length=252 := by decide +kernel
private theorem decoded211 : row 211=x211.toArray := rowCert 211 x211 (by decide +kernel) length211
private theorem powers211 : rhoPowers 251 211=tab 212 row :=
  step powers210 decoded210 decoded211 length210 (by decide +kernel)
private noncomputable def x212 := chunk208[4]!
private theorem length212 : x212.length=252 := by decide +kernel
private theorem decoded212 : row 212=x212.toArray := rowCert 212 x212 (by decide +kernel) length212
private theorem powers212 : rhoPowers 251 212=tab 213 row :=
  step powers211 decoded211 decoded212 length211 (by decide +kernel)
private noncomputable def x213 := chunk208[5]!
private theorem length213 : x213.length=252 := by decide +kernel
private theorem decoded213 : row 213=x213.toArray := rowCert 213 x213 (by decide +kernel) length213
private theorem powers213 : rhoPowers 251 213=tab 214 row :=
  step powers212 decoded212 decoded213 length212 (by decide +kernel)
private noncomputable def x214 := chunk208[6]!
private theorem length214 : x214.length=252 := by decide +kernel
private theorem decoded214 : row 214=x214.toArray := rowCert 214 x214 (by decide +kernel) length214
private theorem powers214 : rhoPowers 251 214=tab 215 row :=
  step powers213 decoded213 decoded214 length213 (by decide +kernel)
private noncomputable def x215 := chunk208[7]!
private theorem length215 : x215.length=252 := by decide +kernel
private theorem decoded215 : row 215=x215.toArray := rowCert 215 x215 (by decide +kernel) length215
private theorem powers215 : rhoPowers 251 215=tab 216 row :=
  step powers214 decoded214 decoded215 length214 (by decide +kernel)

private noncomputable def chunk216 : List (List Interval) := eval% (candidates 216 8)
private noncomputable def x216 := chunk216[0]!
private theorem length216 : x216.length=252 := by decide +kernel
private theorem decoded216 : row 216=x216.toArray := rowCert 216 x216 (by decide +kernel) length216
private theorem powers216 : rhoPowers 251 216=tab 217 row :=
  step powers215 decoded215 decoded216 length215 (by decide +kernel)
private noncomputable def x217 := chunk216[1]!
private theorem length217 : x217.length=252 := by decide +kernel
private theorem decoded217 : row 217=x217.toArray := rowCert 217 x217 (by decide +kernel) length217
private theorem powers217 : rhoPowers 251 217=tab 218 row :=
  step powers216 decoded216 decoded217 length216 (by decide +kernel)
private noncomputable def x218 := chunk216[2]!
private theorem length218 : x218.length=252 := by decide +kernel
private theorem decoded218 : row 218=x218.toArray := rowCert 218 x218 (by decide +kernel) length218
private theorem powers218 : rhoPowers 251 218=tab 219 row :=
  step powers217 decoded217 decoded218 length217 (by decide +kernel)
private noncomputable def x219 := chunk216[3]!
private theorem length219 : x219.length=252 := by decide +kernel
private theorem decoded219 : row 219=x219.toArray := rowCert 219 x219 (by decide +kernel) length219
private theorem powers219 : rhoPowers 251 219=tab 220 row :=
  step powers218 decoded218 decoded219 length218 (by decide +kernel)
private noncomputable def x220 := chunk216[4]!
private theorem length220 : x220.length=252 := by decide +kernel
private theorem decoded220 : row 220=x220.toArray := rowCert 220 x220 (by decide +kernel) length220
private theorem powers220 : rhoPowers 251 220=tab 221 row :=
  step powers219 decoded219 decoded220 length219 (by decide +kernel)
private noncomputable def x221 := chunk216[5]!
private theorem length221 : x221.length=252 := by decide +kernel
private theorem decoded221 : row 221=x221.toArray := rowCert 221 x221 (by decide +kernel) length221
private theorem powers221 : rhoPowers 251 221=tab 222 row :=
  step powers220 decoded220 decoded221 length220 (by decide +kernel)
private noncomputable def x222 := chunk216[6]!
private theorem length222 : x222.length=252 := by decide +kernel
private theorem decoded222 : row 222=x222.toArray := rowCert 222 x222 (by decide +kernel) length222
private theorem powers222 : rhoPowers 251 222=tab 223 row :=
  step powers221 decoded221 decoded222 length221 (by decide +kernel)
private noncomputable def x223 := chunk216[7]!
private theorem length223 : x223.length=252 := by decide +kernel
private theorem decoded223 : row 223=x223.toArray := rowCert 223 x223 (by decide +kernel) length223
private theorem powers223 : rhoPowers 251 223=tab 224 row :=
  step powers222 decoded222 decoded223 length222 (by decide +kernel)

private noncomputable def chunk224 : List (List Interval) := eval% (candidates 224 8)
private noncomputable def x224 := chunk224[0]!
private theorem length224 : x224.length=252 := by decide +kernel
private theorem decoded224 : row 224=x224.toArray := rowCert 224 x224 (by decide +kernel) length224
private theorem powers224 : rhoPowers 251 224=tab 225 row :=
  step powers223 decoded223 decoded224 length223 (by decide +kernel)
private noncomputable def x225 := chunk224[1]!
private theorem length225 : x225.length=252 := by decide +kernel
private theorem decoded225 : row 225=x225.toArray := rowCert 225 x225 (by decide +kernel) length225
private theorem powers225 : rhoPowers 251 225=tab 226 row :=
  step powers224 decoded224 decoded225 length224 (by decide +kernel)
private noncomputable def x226 := chunk224[2]!
private theorem length226 : x226.length=252 := by decide +kernel
private theorem decoded226 : row 226=x226.toArray := rowCert 226 x226 (by decide +kernel) length226
private theorem powers226 : rhoPowers 251 226=tab 227 row :=
  step powers225 decoded225 decoded226 length225 (by decide +kernel)
private noncomputable def x227 := chunk224[3]!
private theorem length227 : x227.length=252 := by decide +kernel
private theorem decoded227 : row 227=x227.toArray := rowCert 227 x227 (by decide +kernel) length227
private theorem powers227 : rhoPowers 251 227=tab 228 row :=
  step powers226 decoded226 decoded227 length226 (by decide +kernel)
private noncomputable def x228 := chunk224[4]!
private theorem length228 : x228.length=252 := by decide +kernel
private theorem decoded228 : row 228=x228.toArray := rowCert 228 x228 (by decide +kernel) length228
private theorem powers228 : rhoPowers 251 228=tab 229 row :=
  step powers227 decoded227 decoded228 length227 (by decide +kernel)
private noncomputable def x229 := chunk224[5]!
private theorem length229 : x229.length=252 := by decide +kernel
private theorem decoded229 : row 229=x229.toArray := rowCert 229 x229 (by decide +kernel) length229
private theorem powers229 : rhoPowers 251 229=tab 230 row :=
  step powers228 decoded228 decoded229 length228 (by decide +kernel)
private noncomputable def x230 := chunk224[6]!
private theorem length230 : x230.length=252 := by decide +kernel
private theorem decoded230 : row 230=x230.toArray := rowCert 230 x230 (by decide +kernel) length230
private theorem powers230 : rhoPowers 251 230=tab 231 row :=
  step powers229 decoded229 decoded230 length229 (by decide +kernel)
private noncomputable def x231 := chunk224[7]!
private theorem length231 : x231.length=252 := by decide +kernel
private theorem decoded231 : row 231=x231.toArray := rowCert 231 x231 (by decide +kernel) length231
private theorem powers231 : rhoPowers 251 231=tab 232 row :=
  step powers230 decoded230 decoded231 length230 (by decide +kernel)

private noncomputable def chunk232 : List (List Interval) := eval% (candidates 232 8)
private noncomputable def x232 := chunk232[0]!
private theorem length232 : x232.length=252 := by decide +kernel
private theorem decoded232 : row 232=x232.toArray := rowCert 232 x232 (by decide +kernel) length232
private theorem powers232 : rhoPowers 251 232=tab 233 row :=
  step powers231 decoded231 decoded232 length231 (by decide +kernel)
private noncomputable def x233 := chunk232[1]!
private theorem length233 : x233.length=252 := by decide +kernel
private theorem decoded233 : row 233=x233.toArray := rowCert 233 x233 (by decide +kernel) length233
private theorem powers233 : rhoPowers 251 233=tab 234 row :=
  step powers232 decoded232 decoded233 length232 (by decide +kernel)
private noncomputable def x234 := chunk232[2]!
private theorem length234 : x234.length=252 := by decide +kernel
private theorem decoded234 : row 234=x234.toArray := rowCert 234 x234 (by decide +kernel) length234
private theorem powers234 : rhoPowers 251 234=tab 235 row :=
  step powers233 decoded233 decoded234 length233 (by decide +kernel)
private noncomputable def x235 := chunk232[3]!
private theorem length235 : x235.length=252 := by decide +kernel
private theorem decoded235 : row 235=x235.toArray := rowCert 235 x235 (by decide +kernel) length235
private theorem powers235 : rhoPowers 251 235=tab 236 row :=
  step powers234 decoded234 decoded235 length234 (by decide +kernel)
private noncomputable def x236 := chunk232[4]!
private theorem length236 : x236.length=252 := by decide +kernel
private theorem decoded236 : row 236=x236.toArray := rowCert 236 x236 (by decide +kernel) length236
private theorem powers236 : rhoPowers 251 236=tab 237 row :=
  step powers235 decoded235 decoded236 length235 (by decide +kernel)
private noncomputable def x237 := chunk232[5]!
private theorem length237 : x237.length=252 := by decide +kernel
private theorem decoded237 : row 237=x237.toArray := rowCert 237 x237 (by decide +kernel) length237
private theorem powers237 : rhoPowers 251 237=tab 238 row :=
  step powers236 decoded236 decoded237 length236 (by decide +kernel)
private noncomputable def x238 := chunk232[6]!
private theorem length238 : x238.length=252 := by decide +kernel
private theorem decoded238 : row 238=x238.toArray := rowCert 238 x238 (by decide +kernel) length238
private theorem powers238 : rhoPowers 251 238=tab 239 row :=
  step powers237 decoded237 decoded238 length237 (by decide +kernel)
private noncomputable def x239 := chunk232[7]!
private theorem length239 : x239.length=252 := by decide +kernel
private theorem decoded239 : row 239=x239.toArray := rowCert 239 x239 (by decide +kernel) length239
private theorem powers239 : rhoPowers 251 239=tab 240 row :=
  step powers238 decoded238 decoded239 length238 (by decide +kernel)

private noncomputable def chunk240 : List (List Interval) := eval% (candidates 240 8)
private noncomputable def x240 := chunk240[0]!
private theorem length240 : x240.length=252 := by decide +kernel
private theorem decoded240 : row 240=x240.toArray := rowCert 240 x240 (by decide +kernel) length240
private theorem powers240 : rhoPowers 251 240=tab 241 row :=
  step powers239 decoded239 decoded240 length239 (by decide +kernel)
private noncomputable def x241 := chunk240[1]!
private theorem length241 : x241.length=252 := by decide +kernel
private theorem decoded241 : row 241=x241.toArray := rowCert 241 x241 (by decide +kernel) length241
private theorem powers241 : rhoPowers 251 241=tab 242 row :=
  step powers240 decoded240 decoded241 length240 (by decide +kernel)
private noncomputable def x242 := chunk240[2]!
private theorem length242 : x242.length=252 := by decide +kernel
private theorem decoded242 : row 242=x242.toArray := rowCert 242 x242 (by decide +kernel) length242
private theorem powers242 : rhoPowers 251 242=tab 243 row :=
  step powers241 decoded241 decoded242 length241 (by decide +kernel)
private noncomputable def x243 := chunk240[3]!
private theorem length243 : x243.length=252 := by decide +kernel
private theorem decoded243 : row 243=x243.toArray := rowCert 243 x243 (by decide +kernel) length243
private theorem powers243 : rhoPowers 251 243=tab 244 row :=
  step powers242 decoded242 decoded243 length242 (by decide +kernel)
private noncomputable def x244 := chunk240[4]!
private theorem length244 : x244.length=252 := by decide +kernel
private theorem decoded244 : row 244=x244.toArray := rowCert 244 x244 (by decide +kernel) length244
private theorem powers244 : rhoPowers 251 244=tab 245 row :=
  step powers243 decoded243 decoded244 length243 (by decide +kernel)
private noncomputable def x245 := chunk240[5]!
private theorem length245 : x245.length=252 := by decide +kernel
private theorem decoded245 : row 245=x245.toArray := rowCert 245 x245 (by decide +kernel) length245
private theorem powers245 : rhoPowers 251 245=tab 246 row :=
  step powers244 decoded244 decoded245 length244 (by decide +kernel)
private noncomputable def x246 := chunk240[6]!
private theorem length246 : x246.length=252 := by decide +kernel
private theorem decoded246 : row 246=x246.toArray := rowCert 246 x246 (by decide +kernel) length246
private theorem powers246 : rhoPowers 251 246=tab 247 row :=
  step powers245 decoded245 decoded246 length245 (by decide +kernel)
private noncomputable def x247 := chunk240[7]!
private theorem length247 : x247.length=252 := by decide +kernel
private theorem decoded247 : row 247=x247.toArray := rowCert 247 x247 (by decide +kernel) length247
private theorem powers247 : rhoPowers 251 247=tab 248 row :=
  step powers246 decoded246 decoded247 length246 (by decide +kernel)

private noncomputable def chunk248 : List (List Interval) := eval% (candidates 248 4)
private noncomputable def x248 := chunk248[0]!
private theorem length248 : x248.length=252 := by decide +kernel
private theorem decoded248 : row 248=x248.toArray := rowCert 248 x248 (by decide +kernel) length248
private theorem powers248 : rhoPowers 251 248=tab 249 row :=
  step powers247 decoded247 decoded248 length247 (by decide +kernel)
private noncomputable def x249 := chunk248[1]!
private theorem length249 : x249.length=252 := by decide +kernel
private theorem decoded249 : row 249=x249.toArray := rowCert 249 x249 (by decide +kernel) length249
private theorem powers249 : rhoPowers 251 249=tab 250 row :=
  step powers248 decoded248 decoded249 length248 (by decide +kernel)
private noncomputable def x250 := chunk248[2]!
private theorem length250 : x250.length=252 := by decide +kernel
private theorem decoded250 : row 250=x250.toArray := rowCert 250 x250 (by decide +kernel) length250
private theorem powers250 : rhoPowers 251 250=tab 251 row :=
  step powers249 decoded249 decoded250 length249 (by decide +kernel)
private noncomputable def x251 := chunk248[3]!
private theorem length251 : x251.length=252 := by decide +kernel
private theorem decoded251 : row 251=x251.toArray := rowCert 251 x251 (by decide +kernel) length251
private theorem powers251 : rhoPowers 251 251=tab 252 row :=
  step powers250 decoded250 decoded251 length250 (by decide +kernel)
end CovarianceArithmetic

open CovarianceArithmetic
theorem solution : rhoPowers 251 251=GrothendieckLB.Supplement.CQDegree251.powers := powers251
