-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_sextic_nonlinear_rational_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T18:09:58.108287+00:00
-- url     : https://prove2.me/submissions/6ced4b79-2df5-46cd-91cc-4b3d293f1114

import Definitions.Def_GrothendieckLB_Supplement_cqSexticHead
import Theorems.Thm_GrothendieckLB_Supplement_cq_nonlinear_head_check
import Mathlib

open Polynomial GrothendieckLB.Supplement
open GrothendieckLB.Supplement.CQHeadArithmetic
namespace NonlinearHermite

private noncomputable def c : ℝ := (slopeNumerator:ℝ)/(slopeDenominator:ℝ)
private noncomputable def mom (M : ℕ → ℝ) : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum (fun k => LinearMap.mulRight ℝ (M k))

private theorem mom_def (M : ℕ → ℝ) (P : ℝ[X]) : mom M P = P.sum (fun k r => r*M k) := rfl

private theorem momC (M : ℕ → ℝ) (v : ℝ) (P : ℝ[X]) :
    mom M (C v*P) = v*mom M P := by
  rw [← Polynomial.smul_eq_C_mul,LinearMap.map_smul,smul_eq_mul]

private noncomputable def he (n : ℕ) : ℝ[X] := (hermite n).map (Int.castRingHom ℝ)

private theorem dh (n : ℕ) : derivative (hermite (n+1)) = C ((n+1:ℕ):ℤ)*hermite n := by
  induction n with
  | zero => simp [hermite_succ,hermite_zero]
  | succ n ih =>
    rw [hermite_succ (n+1),ih,derivative_sub,derivative_mul,derivative_X,
      derivative_mul,derivative_C,zero_mul,zero_add,one_mul,ih]
    rw [hermite_succ n]
    push_cast
    simp only [map_add,map_one]
    ring

private theorem herec (n : ℕ) : he (n+2) = X*he (n+1)-C ((n+1:ℕ):ℝ)*he n := by
  rw [he,hermite_succ (n+1),dh n]
  simp [he]

private theorem he0 : he 0 = 1 := by simp [he,hermite_zero]
private theorem he1 : he 1 = X := by simp [he,hermite_succ,hermite_zero]

private theorem Xhe (n : ℕ) : X*he n = he (n+1)+C (n:ℝ)*he (n-1) := by
  cases n with
  | zero => simp [he0,he1]
  | succ n => rw [show n.succ+1=n+2 by omega,herec]; simp

private theorem hcoeff_spec (n k : ℕ) (hk : k ≤ n) : (he n).coeff k = (hermiteCoeff n k:ℝ) := by
  rw [he,coeff_map,coeff_hermite,Nat.choose_eq_factorial_div_factorial hk]
  simp [hermiteCoeff,Nat.even_iff]

private theorem moment_he (M : ℕ → ℝ) (n : ℕ) :
    mom M (he n) = ∑ j ∈ Finset.range (n+1), (hermiteCoeff n j:ℝ)*M j := by
  rw [mom_def,Polynomial.sum_over_range' _ (fun _ => zero_mul _) (n+1)]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [hcoeff_spec n j (by have h := Finset.mem_range.mp hj; omega)]
  · unfold he
    exact (Polynomial.natDegree_map_le.trans_eq (natDegree_hermite (n:=n))).trans_lt (Nat.lt_succ_self n)

private noncomputable def cubic : ℝ[X] := C 3*X-X^3
private noncomputable def factor (p : ℕ) : ℝ := if p%2=0 then 1 else c
private noncomputable def parityScale (s : ℝ) (p : ℕ) : ℝ := if p%2=0 then 1 else s
private noncomputable def poly : ℕ → ℝ[X]
  | 0 => 1
  | 1 => cubic
  | p+2 => C (factor (p+1))*cubic*poly (p+1)-C ((p+1:ℕ):ℝ)*poly p

private theorem poly_step (p : ℕ) : poly (p+1) = C (factor p)*cubic*poly p-C (p:ℝ)*poly (p-1) := by
  cases p with
  | zero => simp [poly,factor]
  | succ p => rfl

private theorem squared_parity (s : ℝ) (hs : s^2=c) (p : ℕ) :
    (parityScale s p)^2 = factor p := by
  unfold parityScale factor
  split_ifs <;> simp_all

private theorem comp_he (s : ℝ) (hs : s^2=c) (p : ℕ) :
    (he p).comp (C s*cubic) = C (parityScale s p)*poly p := by
  induction p using Nat.twoStepInduction with
  | zero => simp [he0,poly,parityScale]
  | one => simp [he1,poly,parityScale]
  | more p ih ih' =>
    have hsame : parityScale s (p+2) = parityScale s p := by
      simp [parityScale,Nat.add_mod]
    have hcross : s*parityScale s (p+1) = parityScale s p*factor (p+1) := by
      by_cases hp : p%2=0
      · have hn : (p+1)%2 ≠ 0 := by omega
        simp [parityScale,factor,hp,hn,←hs,pow_two]
      · have hn : (p+1)%2 = 0 := by omega
        simp [parityScale,factor,hp,hn]
    rw [herec,sub_comp,mul_comp,mul_comp,X_comp,C_comp,ih',ih,hsame,poly]
    have hc := congrArg (C : ℝ → ℝ[X]) hcross
    simp only [C_mul] at hc
    linear_combination cubic*poly (p+1)*hc

private noncomputable def V (M : ℕ → ℝ) (p b : ℕ) : ℝ := mom M (poly p*he b)
private noncomputable def lifted (M : ℕ → ℝ) (P : ℝ[X]) (r b : ℕ) :=
  mom M (P*X^r*he b)

private theorem lift_succ (M : ℕ → ℝ) (P : ℝ[X]) (r b : ℕ) :
    lifted M P (r+1) b = lifted M P r (b+1)+(b:ℝ)*lifted M P r (b-1) := by
  unfold lifted
  rw [pow_succ,show P*(X^r*X)*he b = (P*X^r)*(X*he b) by ring,Xhe,mul_add,
    show P*X^r*(C (b:ℝ)*he (b-1)) = C (b:ℝ)*(P*X^r*he (b-1)) by ring,
    map_add,momC]

private theorem value_step (M : ℕ → ℝ) (p b : ℕ) :
    V M (p+1) b = factor p*(3*lifted M (poly p) 1 b-lifted M (poly p) 3 b)-
      (p:ℝ)*V M (p-1) b := by
  unfold V lifted
  rw [poly_step]
  have hp : (C (factor p)*cubic*poly p-C (p:ℝ)*poly (p-1))*he b =
      C (factor p)*(C 3*(poly p*X^1*he b)-poly p*X^3*he b)-C (p:ℝ)*(poly (p-1)*he b) := by
    unfold cubic; ring
  rw [hp,map_sub,momC,momC,map_sub,momC]

private theorem base_zero (M : ℕ → ℝ) (b : ℕ) : V M 0 b = mom M (he b) := by simp [V,poly]
private theorem lift_zero (M : ℕ → ℝ) (p b : ℕ) : lifted M (poly p) 0 b = V M p b := by simp [lifted,V]

private theorem numerator_pos (M : ℕ → ℝ) (s : ℝ) (hs : s^2=c) (p b : ℕ) :
    (mom M (cqSexticPoly s (p+1) b))^2 = factor p*(V M p b)^2 := by
  have hc : C (-s)*(X^3-C 3*X) = C s*cubic := by simp [cubic,C_neg]; ring
  change (mom M ((he p).comp (C (-s)*(X^3-C 3*X))*he b))^2 = _
  rw [hc,comp_he s hs,mul_assoc,momC,mul_pow,squared_parity s hs]
  rfl

private theorem numerator_zero (M : ℕ → ℝ) (s : ℝ) (hs : s^2=c) (b : ℕ) :
    (mom M (cqSexticPoly s 0 (b+1)))^2 = 9*c*(lifted M (poly 0) 2 b - V M 0 b)^2 := by
  change (mom M (C (3*s)*(X^2-1)*he b))^2 = _
  rw [mul_assoc,momC,sub_mul,one_mul,map_sub,mul_pow,mul_pow,hs]
  norm_num [V,lifted,poly]

private def rawC (b : Interval) (x : ℝ) : Prop := (b.lo:ℝ) ≤ x ∧ x ≤ (b.hi:ℝ)
private def covers (s : ℤ) (b : Interval) (x : ℝ) : Prop := rawC b ((s:ℝ)*x)

private theorem rawP {b c : Interval} {x y : ℝ} (hx : rawC b x) (hy : rawC c y) :
    rawC (addInterval b c) (x+y) := by
  simpa [rawC,addInterval] using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

private theorem rawM {b c : Interval} {x y : ℝ} (hx : rawC b x) (hy : rawC c y) :
    rawC (subInterval b c) (x-y) := by
  simpa [rawC,subInterval] using And.intro (sub_le_sub hx.1 hy.2) (sub_le_sub hx.2 hy.1)

private theorem rawTimes {b : Interval} {x : ℝ} (hx : rawC b x) (k : ℤ) :
    rawC (scaleInterval k b) ((k:ℝ)*x) := by
  by_cases hk : k=0
  · simp [hk,scaleInterval,zeroInterval,rawC]
  by_cases hp : 0 ≤ k
  · have ht : 0 ≤ (k:ℝ) := by exact_mod_cast hp
    simpa [scaleInterval,rawC,hp,hk] using And.intro (mul_le_mul_of_nonneg_left hx.1 ht)
      (mul_le_mul_of_nonneg_left hx.2 ht)
  · have ht : (k:ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hp)
    simpa [scaleInterval,rawC,hp,hk] using And.intro (mul_le_mul_of_nonpos_left hx.2 ht)
      (mul_le_mul_of_nonpos_left hx.1 ht)

private theorem rawQuo {b : Interval} {x : ℝ} (hx : rawC b x) {d : ℤ} (hd : 0 < d) :
    rawC (divideOut d b) (x/(d:ℝ)) := by
  have hp : 0 < (d:ℝ) := by exact_mod_cast hd
  have hl : (↑(b.lo/d):ℝ)*(d:ℝ) ≤ (b.lo:ℝ) := by exact_mod_cast Int.ediv_mul_le _ hd.ne'
  have hu : (↑((-b.hi)/d):ℝ)*(d:ℝ) ≤ -(b.hi:ℝ) := by exact_mod_cast Int.ediv_mul_le _ hd.ne'
  constructor
  · exact (le_div_iff₀ hp).2 (hl.trans hx.1)
  · apply (div_le_iff₀ hp).2
    simp only [divideOut,Int.cast_neg,neg_mul]
    linarith only [hu,hx.2]

private theorem lineLow {a b x t l : ℝ} (hal : l ≤ a*t) (hbl : l ≤ b*t)
    (ha : a ≤ x) (hb : x ≤ b) : l ≤ x*t := by
  rcases le_total 0 t with ht|ht
  · exact hal.trans (mul_le_mul_of_nonneg_right ha ht)
  · exact hbl.trans (mul_le_mul_of_nonpos_right hb ht)

private theorem lineHigh {a b x t l : ℝ} (hal : a*t ≤ l) (hbl : b*t ≤ l)
    (ha : a ≤ x) (hb : x ≤ b) : x*t ≤ l := by
  rcases le_total 0 t with ht|ht
  · exact (mul_le_mul_of_nonneg_right hb ht).trans hbl
  · exact (mul_le_mul_of_nonpos_right ha ht).trans hal

private theorem rawProd {b e : Interval} {x y : ℝ} (hx : rawC b x) (hy : rawC e y)
    {d : ℤ} (hd : 0 < d) : rawC (mulInterval d b e) (x*y/(d:ℝ)) := by
  unfold mulInterval
  apply rawQuo _ hd
  change _ ≤ x*y ∧ x*y ≤ _
  push_cast
  constructor
  · apply lineLow _ _ hx.1 hx.2
    · rw [mul_comm (b.lo:ℝ) y]
      apply lineLow _ _ hy.1 hy.2
      · rw [mul_comm (e.lo:ℝ)]; exact (min_le_left _ _).trans (min_le_left _ _)
      · rw [mul_comm (e.hi:ℝ)]; exact (min_le_left _ _).trans (min_le_right _ _)
    · rw [mul_comm (b.hi:ℝ) y]
      apply lineLow _ _ hy.1 hy.2
      · rw [mul_comm (e.lo:ℝ)]; exact (min_le_right _ _).trans (min_le_left _ _)
      · rw [mul_comm (e.hi:ℝ)]; exact (min_le_right _ _).trans (min_le_right _ _)
  · apply lineHigh _ _ hx.1 hx.2
    · rw [mul_comm (b.lo:ℝ) y]
      apply lineHigh _ _ hy.1 hy.2
      · rw [mul_comm (e.lo:ℝ)]; exact (le_max_left _ _).trans (le_max_left _ _)
      · rw [mul_comm (e.hi:ℝ)]; exact (le_max_right _ _).trans (le_max_left _ _)
    · rw [mul_comm (b.hi:ℝ) y]
      apply lineHigh _ _ hy.1 hy.2
      · rw [mul_comm (e.lo:ℝ)]; exact (le_max_left _ _).trans (le_max_right _ _)
      · rw [mul_comm (e.hi:ℝ)]; exact (le_max_right _ _).trans (le_max_right _ _)

private theorem rawSquare {b : Interval} {x : ℝ} (hx : rawC b x) : rawC (sqInterval b) (x^2) := by
  have h0 : (b.lo:ℝ) ≤ x := hx.1
  have h1 : x ≤ (b.hi:ℝ) := hx.2
  constructor
  · dsimp only [sqInterval]
    split_ifs with h
    · simpa using sq_nonneg x
    push_cast
    by_cases hp : 0 ≤ b.lo
    · have hpos : 0 ≤ (b.lo:ℝ) := by exact_mod_cast hp
      exact (min_le_left _ _).trans (by simpa [sq] using pow_le_pow_left₀ hpos h0 2)
    · have hn : b.hi ≤ 0 := by omega
      have hneg : (b.hi:ℝ) ≤ 0 := by exact_mod_cast hn
      apply le_trans (min_le_right _ _)
      have hh : 0 ≤ -(b.hi:ℝ)-x := by linarith only [h1,hneg]
      nlinarith only [mul_nonneg (sub_nonneg.mpr h1) hh]
  · dsimp only [sqInterval]
    push_cast
    rcases le_total 0 x with hp|hn
    · apply le_trans _ (le_max_right _ _)
      simpa [sq] using pow_le_pow_left₀ hp h1 2
    · apply le_trans _ (le_max_left _ _)
      nlinarith only [mul_nonneg (sub_nonneg.mpr h0) (by linarith only [h0,hn] : 0 ≤ -x-(b.lo:ℝ))]

private theorem cvZ (s : ℤ) : covers s zeroInterval 0 := by simp [covers,rawC,zeroInterval]
private theorem cvOne (s : ℤ) : covers s (fixed s) 1 := by simp [covers,rawC,fixed]
private theorem cvP {s : ℤ} {a b : Interval} {x y : ℝ} (hx : covers s a x) (hy : covers s b y) :
    covers s (addInterval a b) (x+y) := by simpa only [covers,mul_add] using rawP hx hy
private theorem cvM {s : ℤ} {a b : Interval} {x y : ℝ} (hx : covers s a x) (hy : covers s b y) :
    covers s (subInterval a b) (x-y) := by simpa only [covers,mul_sub] using rawM hx hy
private theorem cvTimes {s : ℤ} {a : Interval} {x : ℝ} (hx : covers s a x) (k : ℤ) :
    covers s (scaleInterval k a) ((k:ℝ)*x) := by simpa only [covers,mul_left_comm] using rawTimes hx k
private theorem cvQuo {s : ℤ} {a : Interval} {x : ℝ} (hx : covers s a x) {d : ℤ} (hd : 0 < d) :
    covers s (divideOut d a) (x/(d:ℝ)) := by simpa only [covers,mul_div_assoc] using rawQuo hx hd
private theorem cvProd {s : ℤ} (hs : 0 < s) {a b : Interval} {x y : ℝ} (hx : covers s a x) (hy : covers s b y) :
    covers s (mulInterval s a b) (x*y) := by
  have hp : (s:ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold covers
  rw [show (s:ℝ)*(x*y)=((s:ℝ)*x)*((s:ℝ)*y)/(s:ℝ) by field_simp [hp]]
  exact rawProd hx hy hs

private def affC (M : ℕ → ℝ) (b : MomentCombination) (x : ℝ) : Prop :=
  ∃ x0 x2 x4 : ℝ, covers momentScale b.e0 x0 ∧ covers momentScale b.e2 x2 ∧ covers momentScale b.e4 x4 ∧
    x=x0*M 0+x2*M 2+x4*M 4

private theorem affZ (M : ℕ → ℝ) : affC M zeroCombination 0 :=
  ⟨0,0,0,cvZ _,cvZ _,cvZ _,by ring⟩

private theorem affP {M : ℕ → ℝ} {a b : MomentCombination} {x y : ℝ} (hx : affC M a x) (hy : affC M b y) :
    affC M (addCombination a b) (x+y) := by
  obtain ⟨a0,a2,a4,h0,h2,h4,rfl⟩ := hx
  obtain ⟨b0,b2,b4,g0,g2,g4,rfl⟩ := hy
  exact ⟨_,_,_,cvP h0 g0,cvP h2 g2,cvP h4 g4,by ring⟩

private theorem affM {M : ℕ → ℝ} {a b : MomentCombination} {x y : ℝ} (hx : affC M a x) (hy : affC M b y) :
    affC M (subCombination a b) (x-y) := by
  obtain ⟨a0,a2,a4,h0,h2,h4,rfl⟩ := hx
  obtain ⟨b0,b2,b4,g0,g2,g4,rfl⟩ := hy
  exact ⟨_,_,_,cvM h0 g0,cvM h2 g2,cvM h4 g4,by ring⟩

private theorem affTimes {M : ℕ → ℝ} {a : MomentCombination} {x : ℝ} (hx : affC M a x) (k : ℤ) :
    affC M (scaleCombination k a) ((k:ℝ)*x) := by
  obtain ⟨a0,a2,a4,h0,h2,h4,rfl⟩ := hx
  exact ⟨_,_,_,cvTimes h0 k,cvTimes h2 k,cvTimes h4 k,by ring⟩

private theorem affQuo {M : ℕ → ℝ} {a : MomentCombination} {x : ℝ} (hx : affC M a x) {d : ℤ} (hd : 0 < d) :
    affC M (divideCombination d a) (x/(d:ℝ)) := by
  obtain ⟨a0,a2,a4,h0,h2,h4,rfl⟩ := hx
  exact ⟨_,_,_,cvQuo h0 hd,cvQuo h2 hd,cvQuo h4 hd,by ring⟩

private theorem seedSound (v : ℤ) (x : ℝ)
    (h : (v:ℝ) ≤ 2^384*x ∧ 2^384*x ≤ (v:ℝ)+1) : covers momentScale (seedBox v) x := by
  have hs : (momentScale:ℝ)=(2:ℝ)^2176*2^384 := by
    simp only [momentScale,Int.cast_pow,Int.cast_ofNat,←pow_add]
  simp only [covers,rawC,seedBox,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,Int.cast_add,Int.cast_one]
  rw [hs,mul_assoc,mul_comm (v:ℝ),mul_comm ((v:ℝ)+1)]
  exact ⟨mul_le_mul_of_nonneg_left h.1 (by positivity),mul_le_mul_of_nonneg_left h.2 (by positivity)⟩

private theorem collapseSound {M : ℕ → ℝ} (hseed : cqSexticSeedBounds M)
    {a : MomentCombination} {x : ℝ} (hx : affC M a x) : covers momentScale (collapse a) x := by
  obtain ⟨x0,x2,x4,h0,h2,h4,rfl⟩ := hx
  have hpos : 0 < momentScale := by unfold momentScale; positivity
  exact cvP (cvP (cvProd hpos h0 (seedSound _ _ hseed.1))
    (cvProd hpos h2 (seedSound _ _ hseed.2.1))) (cvProd hpos h4 (seedSound _ _ hseed.2.2))

private theorem scaledSqSound {M : ℕ → ℝ} (hseed : cqSexticSeedBounds M)
    {a : MomentCombination} {x : ℝ} (hx : affC M a x) (num den : ℤ) (hd : 0 < den) :
    covers coefficientScale (scaledSq num den a) ((num:ℝ)/(den:ℝ)*x^2) := by
  have hw : 0 < momentScale := by unfold momentScale; positivity
  have hwr : (momentScale:ℝ) ≠ 0 := by exact_mod_cast hw.ne'
  have hdr : (den:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have h := rawQuo (rawTimes (rawSquare (collapseSound hseed hx)) (coefficientScale*num)) (d:=momentScale*momentScale*den) (by positivity)
  unfold covers scaledSq
  convert h using 1
  push_cast
  field_simp [hwr,hdr] <;> ring

@[simp] private theorem tabSize {α : Type} (n : ℕ) (f : ℕ → α) : (tab n f).size=n := by simp [tab]
private theorem tabGet {α : Type} (d : α) {n i : ℕ} {f : ℕ → α} (hi : i < n) :
    entry d (tab n f) i = f i := by simp [entry,tab,Array.getElem?_ofFn,hi]
private theorem pushGet {α : Type} (d : α) (xs : Array α) (x : α) (i : ℕ) :
    entry d (xs.push x) i = if i=xs.size then x else entry d xs i := by
  by_cases h : i=xs.size <;> simp [entry,Array.getElem?_push,h]

private theorem sumA {M : ℕ → ℝ} {f : ℕ → MomentCombination} {g : ℕ → ℝ} (n : ℕ)
    (h : ∀ i, i < n → affC M (f i) (g i)) :
    affC M (sumCombinations f n) (∑ i ∈ Finset.range n, g i) := by
  induction n with
  | zero => simpa [sumCombinations] using affZ M
  | succ n ih =>
    rw [sumCombinations,Finset.sum_range_succ]
    exact affP (ih (fun i hi => h i (by omega))) (h n (by omega))

private theorem sumB {s : ℤ} {f : ℕ → Interval} {g : ℕ → ℝ} (n : ℕ)
    (h : ∀ i, i < n → covers s (f i) (g i)) :
    covers s (sumIntervals f n) (∑ i ∈ Finset.range n, g i) := by
  induction n with
  | zero => simpa [sumIntervals] using cvZ s
  | succ n ih =>
    rw [sumIntervals,Finset.sum_range_succ]
    exact cvP (ih (fun i hi => h i (by omega))) (h n (by omega))

private theorem rawSize (n : ℕ) : (momentRows n).size = n+6 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [momentRows,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private def Row (M : ℕ → ℝ) (xs : Array MomentCombination) (f : ℕ → ℝ) : Prop :=
  ∀ j, j < xs.size → affC M (entry zeroCombination xs j) (f j)

private theorem recurrence' (M : ℕ → ℝ)
    (hr : ∀ n : ℕ, n ≤ 751 → 3*c*M (n+6) =
      ((n:ℝ)+1)*M n - (1+9*c)*M (n+2)+12*c*M (n+4)) (n : ℕ) (hn : n ≤ 751) :
    M (n+6) = (((n:ℝ)+1)*(slopeDenominator:ℝ)*M n-((slopeDenominator:ℝ)+9*(slopeNumerator:ℝ))*M (n+2)+12*(slopeNumerator:ℝ)*M (n+4))/
      (3*(slopeNumerator:ℝ)) := by
  have h := hr n hn
  have hden : (slopeDenominator:ℝ) ≠ 0 := by norm_num [slopeDenominator]
  have hnum : (slopeNumerator:ℝ) ≠ 0 := by norm_num [slopeNumerator]
  unfold c at h
  field_simp [hden] at h
  field_simp [hnum]
  linear_combination h

private theorem basis0 (M : ℕ → ℝ) : affC M (basis 0) (M 0) := by
  refine ⟨1,0,0,cvOne _,cvZ _,cvZ _,?_⟩
  ring
private theorem basis2 (M : ℕ → ℝ) : affC M (basis 2) (M 2) := by
  refine ⟨0,1,0,cvZ _,cvOne _,cvZ _,?_⟩
  ring
private theorem basis4 (M : ℕ → ℝ) : affC M (basis 4) (M 4) := by
  refine ⟨0,0,1,cvZ _,cvZ _,cvOne _,?_⟩
  ring

private theorem rawSound (M : ℕ → ℝ) (hodd : ∀ n, n ≤ 757 → Odd n → M n=0)
    (hr : ∀ n : ℕ, n ≤ 751 → 3*c*M (n+6) =
      ((n:ℝ)+1)*M n-(1+9*c)*M (n+2)+12*c*M (n+4)) (n : ℕ) (hn : n ≤ 752) : Row M (momentRows n) M := by
  induction n with
  | zero =>
    intro i hi
    rw [rawSize] at hi
    have hz (k : ℕ) (hk : k ≤ 757) (ho : Odd k) : affC M zeroCombination (M k) := by
      rw [hodd k hk ho]; exact affZ M
    rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 by omega) with h|h|h|h|h|h <;> subst i
    · exact basis0 M
    · exact hz 1 (by decide) (by decide)
    · exact basis2 M
    · exact hz 3 (by decide) (by decide)
    · exact basis4 M
    · exact hz 5 (by decide) (by decide)
  | succ n ih =>
    intro i hi
    rw [rawSize] at hi
    change affC M (entry zeroCombination ((momentRows n).push _) i) (M i)
    rw [pushGet,rawSize]
    by_cases he : i=n+6
    · rw [if_pos he]
      subst i
      split_ifs with h
      · have H := ih (by omega)
        have h1 := affTimes (H n (by rw [rawSize]; omega)) (((n:ℤ)+1)*slopeDenominator)
        have h2 := affTimes (H (n+2) (by rw [rawSize]; omega)) (slopeDenominator+9*slopeNumerator)
        have h3 := affTimes (H (n+4) (by rw [rawSize]; omega)) (12*slopeNumerator)
        have hq := affQuo (affP (affM h1 h2) h3) (d:=3*slopeNumerator) (by decide)
        rw [recurrence' M hr n (by omega)]
        simpa only [Int.cast_mul,Int.cast_add,Int.cast_natCast,Int.cast_ofNat,Int.cast_one] using hq
      · rw [hodd (n+6) (by omega) (by rw [Nat.odd_iff]; omega)]
        exact affZ M
    · rw [if_neg he]
      exact ih (by omega) i (by rw [rawSize]; omega)

private theorem hStartSound (M : ℕ → ℝ) {xs : Array MomentCombination} (hxs : Row M xs M)
    (hodd : ∀ n, n ≤ 757 → Odd n → M n=0) (b : ℕ) (hb : b < xs.size) (hcut : b ≤ 757) :
    affC M (hStart xs b) (mom M (he b)) := by
  rw [hStart,moment_he]
  split_ifs with hp
  · apply sumA
    intro i hi
    exact affTimes (hxs i (by omega)) _
  · rw [Finset.sum_eq_zero]
    · exact affZ M
    · intro k hk
      have hkb := Finset.mem_range.mp hk
      by_cases ho : Odd k
      · rw [hodd k (by omega) ho,mul_zero]
      · have hpar : (b+k)%2 ≠ 0 := by rw [Nat.odd_iff] at ho; omega
        simp [hermiteCoeff,hpar]

private theorem shiftSound (M : ℕ → ℝ) (P : ℝ[X]) (r : ℕ) {xs : Array MomentCombination}
    (hx : Row M xs (lifted M P r)) : Row M (shift xs) (lifted M P (r+1)) := by
  intro j hj
  simp only [shift,tabSize] at hj
  rw [shift,tabGet _ hj,lift_succ]
  simpa only [Int.cast_natCast] using affP (hx (j+1) (by omega))
    (affTimes (hx (j-1) (by omega)) (j:ℤ))

private theorem facSound {M : ℕ → ℝ} {a : MomentCombination} {x : ℝ} (hx : affC M a x) (p : ℕ) :
    affC M (multiplyByParityFactor p a) (factor p*x) := by
  by_cases h : p%2=0
  · simpa [multiplyByParityFactor,factor,h] using hx
  · simp only [multiplyByParityFactor,factor,if_neg h,c]
    rw [div_mul_eq_mul_div]
    exact affQuo (affTimes hx slopeNumerator) (by decide)

private theorem nextSound (M : ℕ → ℝ) (p : ℕ) {prev cur : Array MomentCombination}
    (hprev : Row M prev (V M (p-1))) (hcur : Row M cur (V M p))
    (hlen : cur.size ≤ prev.size) : Row M (nextRow p prev cur) (V M (p+1)) := by
  have h0 : Row M cur (lifted M (poly p) 0) := by simpa only [Row,lift_zero] using hcur
  have h1 := shiftSound M _ _ h0
  have h3 := shiftSound M _ _ (shiftSound M _ _ h1)
  intro b hb
  simp only [nextRow,tabSize] at hb
  rw [nextRow,tabGet _ hb,value_step]
  have hs : (shift (shift (shift cur))).size ≤ (shift cur).size := by simp [shift]; omega
  have hp : (shift (shift (shift cur))).size ≤ prev.size := by simp [shift]; omega
  simpa only [Int.cast_ofNat,Int.cast_natCast] using affM
    (facSound (affM (affTimes (h1 b (by omega)) 3) (h3 b hb)) p)
    (affTimes (hprev b (by omega)) (p:ℤ))

private noncomputable def wVal (M : ℕ → ℝ) (s : ℝ) (a b : ℕ) : ℝ :=
  (mom M (cqSexticPoly s a b))^2/((a.factorial:ℝ)*(b.factorial:ℝ))

private theorem weightSound {M : ℕ → ℝ} (hseed : cqSexticSeedBounds M) (s : ℝ) (hs : s^2=c)
    (p b : ℕ) {t : MomentCombination} (ht : affC M t (V M p b)) :
    covers coefficientScale (toWeight (p+1) b t) (wVal M s (p+1) b) := by
  unfold wVal toWeight
  rw [numerator_pos M s hs,Nat.add_sub_cancel]
  let f : ℤ := ((p+1).factorial:ℤ)*(b.factorial:ℤ)
  have hf : 0 < f := by dsimp [f]; positivity
  have hcd : 0 < slopeDenominator := by decide
  have hcd' : (slopeDenominator:ℝ) ≠ 0 := by exact_mod_cast hcd.ne'
  by_cases hp : p%2=0
  · rw [if_pos hp,factor,if_pos hp,one_mul]
    have h := scaledSqSound hseed ht 1 f hf
    unfold f at h
    simpa only [Int.cast_mul,Int.cast_natCast,Int.cast_one,one_div,inv_mul_eq_div] using h
  · rw [if_neg hp,factor,if_neg hp]
    have h := scaledSqSound hseed ht slopeNumerator (slopeDenominator*f) (mul_pos hcd hf)
    convert h using 1
    dsimp only [f,c]
    push_cast
    field_simp [hcd'] <;> ring

private theorem zeroWeightSound {M : ℕ → ℝ} (hseed : cqSexticSeedBounds M) (s : ℝ) (hs : s^2=c)
    (N : ℕ) (xs : Array MomentCombination) (hx : Row M xs (V M 0)) (hlen : xs.size=3*N+1)
    (b : ℕ) (hb : b ≤ N) : covers coefficientScale (entry zeroInterval (zeroWeights N xs) b) (wVal M s 0 b) := by
  rw [zeroWeights,tabGet _ (by omega)]
  cases b with
  | zero => simpa [wVal,cqSexticPoly] using cvZ coefficientScale
  | succ b =>
    simp only [Nat.succ_ne_zero,if_false,Nat.add_sub_cancel]
    have hr : Row M xs (lifted M (poly 0) 0) := by simpa only [Row,lift_zero] using hx
    have h2 := shiftSound M _ _ (shiftSound M _ _ hr)
    have hz := affM (h2 b (by simp [shift,hlen]; omega)) (hx b (by omega))
    have hcd : 0 < slopeDenominator := by decide
    have hh := scaledSqSound hseed hz (9*slopeNumerator) (slopeDenominator*(b+1).factorial) (by positivity)
    unfold wVal
    rw [numerator_zero M s hs]
    convert hh using 1
    simp only [Int.cast_mul,Int.cast_natCast,Int.cast_ofNat,Nat.factorial_zero,Nat.cast_one,one_mul,c]
    field_simp [show (slopeDenominator:ℝ) ≠ 0 by exact_mod_cast hcd.ne'] <;> ring

private structure GridOK (M : ℕ → ℝ) (s : ℝ) (N p : ℕ) (st : Grid) : Prop where
  curSize : st.cur.size+3*p=3*N+1
  prevSize : st.cur.size ≤ st.prev.size
  prevRow : Row M st.prev (V M (p-1))
  curRow : Row M st.cur (V M p)
  wSize : st.weights.size=p+1
  wRow : ∀ a b, a ≤ p → a+b ≤ N → covers coefficientScale (entry zeroInterval (entry #[] st.weights a) b) (wVal M s a b)

private theorem gridSound {M : ℕ → ℝ} (hseed : cqSexticSeedBounds M) (s : ℝ) (hs : s^2=c)
    (N : ℕ) (xs : Array MomentCombination) (hx : Row M xs (V M 0)) (hlen : xs.size=3*N+1)
    (p : ℕ) (hp : p ≤ N) : GridOK M s N p (grid N xs p) := by
  induction p with
  | zero =>
    refine ⟨by simpa [grid],le_rfl,hx,hx,rfl,?_⟩
    intro a b ha hab
    obtain rfl : a=0 := by omega
    exact zeroWeightSound hseed s hs N xs hx hlen b (by omega)
  | succ p ih =>
    let st := grid N xs p
    have h : GridOK M s N p st := ih (by omega)
    have hsz : (nextRow p st.prev st.cur).size=st.cur.size-3 := by
      simp only [nextRow,tabSize,shift]; omega
    have hbound := h.curSize
    constructor
    · change (nextRow _ st.prev st.cur).size+3*(p+1)=3*N+1
      rw [hsz]; omega
    · change (nextRow _ st.prev st.cur).size ≤ st.cur.size
      rw [hsz]; omega
    · exact h.curRow
    · exact nextSound M p h.prevRow h.curRow h.prevSize
    · change (st.weights.push _).size=p+1+1
      simp [h.wSize]
    · intro a b ha hab
      change covers coefficientScale (entry zeroInterval (entry #[] (st.weights.push _) a) b) (wVal M s a b)
      rw [pushGet,h.wSize]
      by_cases he : a=p+1
      · subst a
        rw [if_pos rfl,tabGet _ (by omega)]
        exact weightSound hseed s hs p b (h.curRow b (by omega))
      · rw [if_neg he]
        exact h.wRow a b (by omega) hab

private noncomputable def rho : ℝ[X] := cqRhoPoly 0.34101124 0.05276111

private theorem rho_scale : C (rhoDen:ℝ)*rho =
    C (rho1:ℝ)*X^1-C (rho3:ℝ)*X^3+C (rho5:ℝ)*X^5 := by
  unfold rho cqRhoPoly
  rw [← mul_assoc,← Polynomial.C_mul]
  have h : (rhoDen:ℝ)*(1/(1+0.34101124^2+0.05276111^2)) = (rho1:ℝ) := by
    norm_num [rhoDen,rho1,rho3,rho5]
  have h3 : (rho1:ℝ)*0.34101124^2 = (rho3:ℝ) := by norm_num [rho1,rho3]
  have h5 : (rho1:ℝ)*0.05276111^2 = (rho5:ℝ) := by norm_num [rho1,rho5]
  rw [h,←h3,←h5,Polynomial.C_mul,Polynomial.C_mul]
  ring

private theorem rho_step (a j : ℕ) :
    let q (k : ℕ) := if k ≤ j then (rho^a).coeff (j-k) else 0
    (rho^(a+1)).coeff j = ((rho1:ℝ)*q 1-(rho3:ℝ)*q 3+(rho5:ℝ)*q 5)/(rhoDen:ℝ) := by
  dsimp only
  apply (eq_div_iff (by norm_num [rhoDen,rho1,rho3,rho5])).2
  rw [mul_comm, ←coeff_C_mul, pow_succ', ←mul_assoc, rho_scale, add_mul,sub_mul,
    mul_assoc (C (rho1:ℝ)),mul_assoc (C (rho3:ℝ)),mul_assoc (C (rho5:ℝ)),
    coeff_add,coeff_sub,coeff_C_mul,coeff_C_mul,coeff_C_mul,
    coeff_X_pow_mul',coeff_X_pow_mul',coeff_X_pow_mul']

private def RhoRow (xs : Array Interval) (a N : ℕ) : Prop :=
  ∀ j, j ≤ N → covers coefficientScale (entry zeroInterval xs j) ((rho^a).coeff j)

private theorem shiftedSound (a j k N : ℕ) (xs : Array Interval) (hx : RhoRow xs a N) (hj : j ≤ N) :
    covers coefficientScale (shifted xs k j) (if k ≤ j then (rho^a).coeff (j-k) else 0) := by
  by_cases h : k ≤ j
  · simpa [shifted,h] using hx (j-k) (by omega)
  · simpa [shifted,h] using cvZ coefficientScale

private theorem rhoNextSound (N a : ℕ) (xs : Array Interval) (hx : RhoRow xs a N) :
    RhoRow (rhoNext N xs) (a+1) N := by
  intro j hj
  rw [rhoNext,tabGet _ (by omega),rho_step]
  exact cvQuo (cvP (cvM (cvTimes (shiftedSound a j 1 N xs hx hj) rho1)
    (cvTimes (shiftedSound a j 3 N xs hx hj) rho3))
    (cvTimes (shiftedSound a j 5 N xs hx hj) rho5)) (by decide)

private theorem rhoSize (N a : ℕ) : (rhoPowers N a).size=a+1 := by
  induction a with
  | zero => rfl
  | succ a ih => simp [rhoPowers,ih]

private theorem entrySingleton {α : Type} (d v : α) : entry d #[v] 0 = v := rfl

private theorem rhoTableSound (N a : ℕ) : ∀ i, i ≤ a → RhoRow (entry #[] (rhoPowers N a) i) i N := by
  induction a with
  | zero =>
    intro i hi
    obtain rfl : i=0 := by omega
    intro j hj
    rw [rhoPowers,entrySingleton,tabGet _ (by omega),pow_zero,coeff_one]
    by_cases h : j=0
    · simpa [h] using cvOne coefficientScale
    · simpa [h] using cvZ coefficientScale
  | succ a ih =>
    intro i hi
    rw [rhoPowers,pushGet,rhoSize]
    by_cases h : i=a+1
    · subst i
      rw [if_pos rfl]
      exact rhoNextSound N a _ (ih a le_rfl)
    · rw [if_neg h]
      exact ih i (by omega)

private theorem checked_coefficient {M : ℕ → ℝ} (s : ℝ) (N m : ℕ) (hm : m ≤ N)
    {ws rs : Array (Array Interval)}
    (wOK : ∀ a b, a ≤ N → a+b ≤ N → covers coefficientScale
      (entry zeroInterval (entry #[] ws a) b) (wVal M s a b))
    (rOK : ∀ a, a ≤ N → RhoRow (entry #[] rs a) a N) :
    covers coefficientScale (fullSum ws rs m)
      (∑ a ∈ Finset.range (m+1), ∑ b ∈ Finset.range (m+1-a),
        (-1:ℝ)^b*((mom M (cqSexticPoly s a b))^2/((a.factorial:ℝ)*(b.factorial:ℝ)))*
        (rho^a).coeff (m-b)) := by
  apply sumB
  intro a ha
  apply sumB
  intro b hb
  have h := cvTimes (cvProd (by unfold coefficientScale; positivity)
    (wOK a b (by omega) (by omega)) (rOK a (by omega) (m-b) (by omega))) ((-1:ℤ)^b)
  simpa only [wVal,Int.cast_pow,Int.cast_neg,Int.cast_one,mul_assoc] using h

private theorem verified_implies (hcheck : cqNonlinearHeadCheck = true)
    (M : ℕ → ℝ) (hseed : cqSexticSeedBounds M) (hodd : ∀ n, n ≤ 757 → Odd n → M n = 0)
    (hr : ∀ n : ℕ, n ≤ 751 → 3*c*M (n+6) =
      ((n:ℝ)+1)*M n-(1+9*c)*M (n+2)+12*c*M (n+4)) (s : ℝ) (hs : s^2=c)
    (j : ℕ) (hj : j < 125) :
    let m := 2*j+3
    |∑ a ∈ Finset.range (m+1), ∑ b ∈ Finset.range (m+1-a),
      (-1:ℝ)^b * ((cqSexticPoly s a b).sum (fun k v => v*M k))^2 /
        ((a.factorial:ℝ)*(b.factorial:ℝ)) * (rho^a).coeff (m-b)| ≤
      (2*3.14159265358979323846)*(((cqHeadUnits[j]?.getD 0 : ℕ):ℝ)/10^20) := by
  let N : ℕ := 251
  let m := 2*j+3
  have hm : m ≤ N := by dsimp [N,m]; omega
  let xs := startAt N
  have h0 : Row M xs (V M 0) := by
    intro b hb
    dsimp only [xs,startAt] at *
    rw [tabSize] at hb
    rw [tabGet _ hb,base_zero]
    exact hStartSound M (rawSound M hodd hr _ (by decide)) hodd b
      (by rw [rawSize]; dsimp [N] at *; omega) (by dsimp [N] at hb; omega)
  have hg := gridSound hseed s hs N xs h0 (by simp [xs,startAt]) N le_rfl
  let v := fullSum (grid N xs N).weights (rhoPowers N N) m
  have hv := checked_coefficient s N m hm hg.wRow (rhoTableSound N N)
  let x : ℝ := ∑ a ∈ Finset.range (m+1), ∑ b ∈ Finset.range (m+1-a),
        (-1:ℝ)^b*((mom M (cqSexticPoly s a b))^2/((a.factorial:ℝ)*(b.factorial:ℝ)))*(rho^a).coeff (m-b)
  change rawC v ((coefficientScale:ℝ)*x) at hv
  have hcheck' : max (-v.lo) v.hi*10^40 ≤ coefficientScale*2*314159265358979323846*(cqHeadUnits[j]?.getD 0) := by
    unfold cqNonlinearHeadCheck verifyList at hcheck
    simpa only [decide_eq_true_eq] using (List.all_eq_true.mp hcheck j (List.mem_range.mpr hj))
  have hcc : (0:ℝ) < (coefficientScale:ℝ) := by unfold coefficientScale; positivity
  have hmag : (coefficientScale:ℝ)*|x| ≤ max (-(v.lo:ℝ)) (v.hi:ℝ) := by
    rw [← abs_of_pos hcc,←abs_mul]
    exact abs_le.mpr ⟨by linarith only [hv.1,le_max_left (-(v.lo:ℝ)) (v.hi:ℝ)],
      hv.2.trans (le_max_right _ _)⟩
  have hcc' : (max (-(v.lo:ℝ)) (v.hi:ℝ))*10^40 ≤
      (coefficientScale:ℝ)*2*314159265358979323846*((cqHeadUnits[j]?.getD 0:ℕ):ℝ) := by exact_mod_cast hcheck'
  have hmag' := (mul_le_mul_of_nonneg_right hmag (by norm_num : (0:ℝ)≤10^40)).trans hcc'
  have hlead : |x| ≤ (2*3.14159265358979323846)*(((cqHeadUnits[j]?.getD 0:ℕ):ℝ)/10^20) := by
    apply le_of_mul_le_mul_left (a:=(coefficientScale:ℝ)) _ hcc
    linarith only [hmag']
  simpa only [x,m,mom_def,mul_div_assoc] using hlead

end NonlinearHermite

open NonlinearHermite in
theorem solution (M : ℕ → ℝ) (hseed : cqSexticSeedBounds M)
    (hodd : ∀ n, n ≤ 757 → Odd n → M n=0)
    (hrec : let c : ℝ := 0.136419125^2/(6*(1+(0.34101124:ℝ)^2+0.05276111^2))
      ∀ n : ℕ, n ≤ 751 → 3*c*M (n+6) =
        ((n:ℝ)+1)*M n-(1+9*c)*M (n+2)+12*c*M (n+4))
    (s : ℝ) (hs : s^2 = 0.136419125^2/(6*(1+(0.34101124:ℝ)^2+0.05276111^2))) :
    ∀ j : ℕ, j < 125 →
      let m := 2*j+3
      |∑ a ∈ Finset.range (m+1), ∑ b ∈ Finset.range (m+1-a),
        (-1:ℝ)^b * ((cqSexticPoly s a b).sum (fun k v => v*M k))^2 /
          ((a.factorial:ℝ)*(b.factorial:ℝ)) *
          ((cqRhoPoly 0.34101124 0.05276111)^a).coeff (m-b)| ≤
        (2*3.14159265358979323846)*(((cqHeadUnits[j]?.getD 0 : ℕ):ℝ)/10^20) := by
  have heq : 0.136419125^2/(6*(1+(0.34101124:ℝ)^2+0.05276111^2))=c := by
    norm_num [c,slopeNumerator,slopeDenominator]
  dsimp only at hrec
  rw [heq] at hrec hs
  exact verified_implies cq_nonlinear_head_check M hseed hodd hrec s hs
