-- Prove2me | solution 2 for GrothendieckLB.Supplement.cq_head_through_degree_17
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T19:06:26.90138+00:00
-- url     : https://prove2.me/submissions/d4adaee9-2a30-4b8f-ba9e-a4f61af064ec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckLB_Supplement_cq_head_integer_comparisons_17
import Definitions.Def_GrothendieckLB_Supplement_cqSexticHead
import Mathlib
import Mathlib.Analysis.Real.Pi.Bounds
import Theorems.Thm_GrothendieckLB_Supplement_theorem_5_1
import Theorems.Thm_GrothendieckLB_Supplement_cqA_sextic_reduction
import Theorems.Thm_GrothendieckLB_Supplement_cq_sextic_moment_recurrence
import Theorems.Thm_GrothendieckLB_Supplement_cq_sextic_initial_integrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Definitions.Def_GrothendieckLB_Supplement_cqNonlinearHeadCheck

/- The moment and interval soundness arguments adapt the public nonlinear rational bounds
   submission 6ced4b79-2df5-46cd-91cc-4b3d293f1114 and finite-head submissions for
   GrothendieckLB.Supplement.cq_sextic_finite_head_arithmetic and cq_head_coefficient_enclosures.
   The cutoff, verified comparisons, and direct theorem for the Gaussian correlation are specialized here. -/
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

private theorem verified_implies (hcheck : verifyList 17 (List.range 8) = true)
    (M : ℕ → ℝ) (hseed : cqSexticSeedBounds M) (hodd : ∀ n, n ≤ 757 → Odd n → M n = 0)
    (hr : ∀ n : ℕ, n ≤ 751 → 3*c*M (n+6) =
      ((n:ℝ)+1)*M n-(1+9*c)*M (n+2)+12*c*M (n+4)) (s : ℝ) (hs : s^2=c)
    (j : ℕ) (hj : j < 8) :
    let m := 2*j+3
    |∑ a ∈ Finset.range (m+1), ∑ b ∈ Finset.range (m+1-a),
      (-1:ℝ)^b * ((cqSexticPoly s a b).sum (fun k v => v*M k))^2 /
        ((a.factorial:ℝ)*(b.factorial:ℝ)) * (rho^a).coeff (m-b)| ≤
      (2*3.14159265358979323846)*(((cqHeadUnits[j]?.getD 0 : ℕ):ℝ)/10^20) := by
  let N : ℕ := 17
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
    unfold verifyList at hcheck
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
private theorem partial_numerators (M : ℕ → ℝ) (hseed : cqSexticSeedBounds M)
    (hodd : ∀ n, n ≤ 757 → Odd n → M n=0)
    (hrec : let c : ℝ := 0.136419125^2/(6*(1+(0.34101124:ℝ)^2+0.05276111^2))
      ∀ n : ℕ, n ≤ 751 → 3*c*M (n+6) =
        ((n:ℝ)+1)*M n-(1+9*c)*M (n+2)+12*c*M (n+4))
    (s : ℝ) (hs : s^2 = 0.136419125^2/(6*(1+(0.34101124:ℝ)^2+0.05276111^2))) :
    ∀ j : ℕ, j < 8 →
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
  exact verified_implies cq_head_integer_comparisons_17 M hseed hodd hrec s hs

open GrothendieckLB.Supplement Polynomial Real
namespace SexticFiniteCertificate

private noncomputable def slope := 0.136419125 / Real.sqrt (6*(1+(0.34101124:ℝ)^2+0.05276111^2))
private noncomputable def variance : ℝ := 1+0.34101124^2+0.05276111^2
private noncomputable def c : ℝ := (0.136419125:ℝ)^2/(6*variance)
private theorem slope_sq : slope^2 = c := by
  unfold slope c variance
  rw [div_pow,Real.sq_sqrt (by positivity)]

private noncomputable def L (M : ℕ → ℝ) (P : ℝ[X]) := P.sum fun k t => t*M k
private noncomputable def numerator (M : ℕ → ℝ) (s : ℝ) (m : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (m+1), ∑ b ∈ Finset.range (m+1-a),
    (-1:ℝ)^b * (L M (cqSexticPoly s a b))^2 / ((a.factorial:ℝ)*(b.factorial:ℝ)) *
      ((cqRhoPoly 0.34101124 0.05276111)^a).coeff (m-b)

private theorem normalize (M : ℕ → ℝ) (m : ℕ) :
    2*Real.pi*cqHeadFromMoments M m = numerator M slope m := by
  unfold cqHeadFromMoments numerator
  rw [← mul_assoc, show 2*Real.pi*(Real.pi/2)=Real.pi^2 by ring]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  unfold cqHermiteFromMoments L slope
  rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg _),Real.sq_sqrt (Nat.cast_nonneg _)]
  field_simp [Real.pi_ne_zero]

private theorem L_monomial (M : ℕ → ℝ) (a : ℝ) (k : ℕ) : L M (monomial k a) = a*M k := by
  exact sum_monomial_index _ _ (by simp)

private theorem L_add (M : ℕ → ℝ) (P Q : ℝ[X]) : L M (P+Q) = L M P+L M Q := by
  apply sum_add_index
  · intros; simp
  · intros; exact add_mul _ _ _

private theorem linear_numerator (M : ℕ → ℝ) :
    numerator M slope 1 = (M 0)^2/variance-9*c*(M 0-M 2)^2 := by
  have h10 : L M (cqSexticPoly slope 1 0) = M 0 := by
    have hp : cqSexticPoly slope 1 0 = monomial 0 1 := by simp [cqSexticPoly,hermite_zero]
    rw [hp,L_monomial,one_mul]
  have h01 : L M (cqSexticPoly slope 0 1) = 3*slope*(M 2-M 0) := by
    have hp : cqSexticPoly slope 0 1 = monomial 2 (3*slope)+monomial 0 (-(3*slope)) := by
      simp [cqSexticPoly,hermite_zero,← C_mul_X_pow_eq_monomial,sub_eq_add_neg,mul_add]
    rw [hp,L_add,L_monomial,L_monomial]
    ring
  have hrho : (cqRhoPoly 0.34101124 0.05276111).coeff 1 = 1/variance := by
    norm_num [cqRhoPoly,variance,Polynomial.coeff_C_mul,Polynomial.coeff_sub,Polynomial.coeff_add,
      Polynomial.coeff_X_pow,Polynomial.coeff_X]
  unfold numerator
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.reduceAdd,Nat.reduceSub,Nat.sub_zero,
    zero_add,pow_zero,pow_one,Polynomial.coeff_one,one_ne_zero,if_false,if_true,one_mul,
    mul_zero,h10,h01,hrho,Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,
    mul_one,div_one,add_zero]
  rw [← slope_sq]
  ring

private theorem pi_upper : Real.pi < 3.141592653589793238463 := by
  pi_upper_bound [
    2167275978168831745282800581884047809581357933085665141/1532495540865888858358347027150309183618739122183602176,
    2831682527741617894188699702696694829316038616151628637/1532495540865888858358347027150309183618739122183602176,
    3006098137529702223242191313425850454491077936538132017/1532495540865888858358347027150309183618739122183602176,
    1525116155962980137005952169117539650818562591202317987/766247770432944429179173513575154591809369561091801088,
    765324791435768937036758547847623025898458909175521305/383123885216472214589586756787577295904684780545900544,
    3064067963721659302159267125229786076991946295916643077/1532495540865888858358347027150309183618739122183602176,
    191547518346267808112197268466112755908258992411694147/95780971304118053647396689196894323976171195136475136,
    1532466692070417048966031207695226649854994115724338663/766247770432944429179173513575154591809369561091801088,
    95780520540628117215766582643950560860905638050046003/47890485652059026823698344598447161988085597568237568,
    1532493737810868421973998007865783456704500377799262253/766247770432944429179173513575154591809369561091801088,
    766247545051033728038323100075555234028704468374234199/383123885216472214589586756787577295904684780545900544,
    3064990856349858728927032591518222504628099325912021045/1532495540865888858358347027150309183618739122183602176,
    1532495512693148725926859238443783694595200700718099247/766247770432944429179173513575154591809369561091801088,
    3064991067645407618131227497947243376847519795253941345/1532495540865888858358347027150309183618739122183602176,
    1532495539105092595023609873256385584326172618118159899/766247770432944429179173513575154591809369561091801088,
    3064991080851379584922881248023617345074427083313307033/1532495540865888858358347027150309183618739122183602176,
    3064991081511678183760338088397673156276356387621822859/1532495540865888858358347027150309183618739122183602176,
    766247770419188208369277785013504315633305225273265283/383123885216472214589586756787577295904684780545900544,
    766247770429505373976691863891447225596970226967913687/383123885216472214589586756787577295904684780545900544,
    3064991081728338661514210475231087299568127090730944031/1532495540865888858358347027150309183618739122183602176,
    1532495540865458976458036519473310809472627546064843717/766247770432944429179173513575154591809369561091801088,
    3064991081731562775766538792925455806327963591769969791/1532495540865888858358347027150309183618739122183602176,
    1532495540865861990739577619242893133072656321956994743/766247770432944429179173513575154591809369561091801088,
    1532495540865882141453654675158735125330193765818466605/766247770432944429179173513575154591809369561091801088,
    23945242826029487173940217799242119784271113141639819/11972621413014756705924586149611790497021399392059392,
    3064991081731776877103607510301096608168127861022953437/1532495540865888858358347027150309183618739122183602176,
    3064991081731777506813422418300730739947849620856591639/1532495540865888858358347027150309183618739122183602176,
    766247770432944416060219036325161502798731974814971027/383123885216472214589586756787577295904684780545900544,
    3064991081731777703597739577050625250150581708763519979/1532495540865888858358347027150309183618739122183602176,
    1532495540865888856718477717494060043105493963066677431/766247770432944429179173513575154591809369561091801088,
    1532495540865888857948379699736246898435591389143966977/766247770432944429179173513575154591809369561091801088,
    1532495540865888858255855195296793612319524911219918125/766247770432944429179173513575154591809369561091801088,
    766247770432944429166362034593465145396860682293097605/383123885216472214589586756787577295904684780545900544,
    766247770432944429175970643829732230206235647490360031/383123885216472214589586756787577295904684780545900544,
    1532495540865888858356745592277598002817171328645160999/766247770432944429179173513575154591809369561091801088,
    1532495540865888858357946668432131388418347121502884341/766247770432944429179173513575154591809369561091801088,
    3064991081731777716716493874941529469637282237489831991/1532495540865888858358347027150309183618739122183602176,
    3064991081731777716716644009460846142837429242239297921/1532495540865888858358347027150309183618739122183602176,
    3064991081731777716716681543090675311137465993809692535/1532495540865888858358347027150309183618739122183602176,
    3064991081731777716716690926498132603212475181726230447/1532495540865888858358347027150309183618739122183602176]

set_option exponentiation.threshold 650 in
private theorem linear_lower (M : ℕ → ℝ) (hc : cqSexticSeedBounds M) :
    (88157382204959954858:ℝ)/10^20 ≤ cqHeadFromMoments M 1 := by
  obtain ⟨⟨h0l,h0u⟩,⟨h2l,h2u⟩,_⟩ := hc
  norm_num1 at h0l h0u h2l h2u
  let l0 : ℝ := 24897419982413584374398274139/10^28
  let u0 : ℝ := 24897419982413584374398274140/10^28
  let l2 : ℝ := 24115695951663088682731945145/10^28
  let u2 : ℝ := 24115695951663088682731945146/10^28
  have hl0 : l0 ≤ M 0 := by dsimp [l0]; linarith only [h0l]
  have hu0 : M 0 ≤ u0 := by dsimp [u0]; linarith only [h0u]
  have hl2 : l2 ≤ M 2 := by dsimp [l2]; linarith only [h2l]
  have hu2 : M 2 ≤ u2 := by dsimp [u2]; linarith only [h2u]
  have hd : 0 ≤ M 0-M 2 := by
    linarith only [hl0,hu2,show u2 ≤ l0 by norm_num [u2,l0]]
  have hcs : 0 ≤ 9*c := by norm_num [c,variance]
  have hnum : l0^2/variance - 9*c*(u0-l2)^2 ≤ numerator M slope 1 := by
    rw [linear_numerator]
    apply sub_le_sub
    · exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by norm_num [l0]) hl0 2)
        (by norm_num [variance])
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd (sub_le_sub hu0 hl2) 2) hcs
  have hdecimal : 2*3.141592653589793238463*((88157382204959954858:ℝ)/10^20) ≤
      l0^2/variance-9*c*(u0-l2)^2 := by norm_num [variance,c,l0,u0,l2]
  apply le_of_mul_le_mul_left (a:=2*Real.pi) _ (by positivity)
  rw [normalize]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left pi_upper.le (by norm_num)) (by positivity)).trans
    (hdecimal.trans hnum)

end SexticFiniteCertificate

open SexticFiniteCertificate in
private theorem partial_moments (M : ℕ → ℝ) (hseed : cqSexticSeedBounds M)
    (hodd : ∀ n, n ≤ 757 → Odd n → M n = 0)
    (hrec : let c : ℝ := 0.136419125^2 / (6*(1+(0.34101124:ℝ)^2+0.05276111^2))
      ∀ n : ℕ, n ≤ 751 → 3*c*M (n+6) =
        ((n:ℝ)+1)*M n - (1+9*c)*M (n+2) + 12*c*M (n+4)) :
    (88157382204959954858:ℝ)/10^20 ≤ cqHeadFromMoments M 1 ∧
      ∀ j : ℕ, j < 8 → |cqHeadFromMoments M (2*j+3)| ≤
        ((cqHeadUnits[j]?.getD 0 : ℕ) : ℝ)/10^20 := by
  refine ⟨linear_lower M hseed,?_⟩
  intro j hj
  let u : ℝ := ((cqHeadUnits[j]?.getD 0 : ℕ) : ℝ)/10^20
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hn : |numerator M slope (2*j+3)| ≤ (2*3.14159265358979323846)*u :=
    partial_numerators M hseed hodd hrec slope slope_sq j hj
  apply le_of_mul_le_mul_left (a:=2*Real.pi) _ (by positivity)
  calc
    _ = |2*Real.pi * cqHeadFromMoments M (2*j+3)| := by
      rw [abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    _ = _ := congrArg abs (normalize M (2*j+3))
    _ ≤ _ := hn
    _ ≤ (2*Real.pi)*u := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left Real.pi_gt_d20.le (by norm_num : 0 ≤ (2:ℝ))) hu

open MeasureTheory Polynomial Real
open GrothendieckLB GrothendieckLB.Supplement

private noncomputable def density (s x : ℝ) : ℝ :=
  exp (-(x^2+(s*(x^3-3*x))^2)/2)

private noncomputable def moment (s : ℝ) (n : ℕ) : ℝ :=
  ∫ x : ℝ, x^n * density s x

private theorem monomial_integrable (s : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => x^n * density s x) := by
  have hg : Integrable fun x : ℝ => x^n * exp (-(1/2 : ℝ) * x^2) := by
    simpa only [rpow_natCast] using integrable_rpow_mul_exp_neg_mul_sq (by norm_num : 0 < (1/2:ℝ))
      (lt_of_lt_of_le (by norm_num : (-1:ℝ) < 0) (Nat.cast_nonneg n))
  apply hg.mono (by unfold density; fun_prop)
  filter_upwards with x
  simp only [density, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply Real.exp_le_exp.mpr
  linarith only [sq_nonneg (s*(x^3-3*x))]

private theorem polynomial_moment (s : ℝ) (P : ℝ[X]) :
    ∫ x : ℝ, P.eval x * density s x = P.sum (fun n c => c*moment s n) := by
  simp_rw [eval_eq_sum, Polynomial.sum_def, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun n _ => (monomial_integrable s n).const_mul (P.coeff n))]
  simp only [integral_const_mul, moment]

private theorem odd_moment (s : ℝ) (n : ℕ) (hn : Odd n) : moment s n = 0 := by
  have hd (x : ℝ) : density s (-x) = density s x := by
    unfold density
    congr 1
    ring
  have h := integral_neg_eq_self (fun x : ℝ => x^n * density s x) volume
  simp only [hn.neg_pow, hd, neg_mul, integral_neg] at h
  unfold moment
  linarith only [h]

private theorem recovery (η s₃ s₅ : ℝ) :
    let s := η / Real.sqrt (6*(1+s₃^2+s₅^2))
    ∀ a b, a+b ≠ 0 → cqA η s₃ s₅ a b = cqHermiteFromMoments s (moment s) a b := by
  let s := η / Real.sqrt (6*(1+s₃^2+s₅^2))
  let H (n : ℕ) (x : ℝ) : ℝ := Polynomial.aeval x (Polynomial.hermite n)
  have hH (n : ℕ) (x : ℝ) : ((hermite n).map (Int.castRingHom ℝ)).eval x = H n x := by
    rw [eval_map]
    rfl
  have h := cqA_sextic_reduction η s₃ s₅
  change (∀ a b, Real.pi * √((a+1).factorial:ℝ) * √(b.factorial:ℝ) * cqA η s₃ s₅ (a+1) b =
      ∫ x : ℝ, H a (-s*(x^3-3*x))*H b x*density s x) ∧
    (∀ b, Real.pi * √((b+1).factorial:ℝ) * cqA η s₃ s₅ 0 (b+1) =
      3*s * ∫ x : ℝ, (x^2-1)*H b x*density s x) at h
  change ∀ a b : ℕ, a+b ≠ 0 → cqA η s₃ s₅ a b = cqHermiteFromMoments s (moment s) a b
  intro a b hab
  rw [cqHermiteFromMoments, eq_div_iff (by positivity), mul_comm, ← polynomial_moment]
  cases a with
  | succ a =>
    simpa only [cqSexticPoly, eval_mul, eval_comp, eval_C, eval_sub, eval_pow, eval_X,
      hH, Nat.succ_eq_add_one] using h.1 a b
  | zero =>
    cases b with
    | zero => simp at hab
    | succ b =>
      simp only [cqSexticPoly, eval_mul, eval_C, eval_sub, eval_pow, eval_X, eval_one,
        hH, Nat.factorial_zero, Nat.cast_one, Real.sqrt_one, mul_one]
      rw [show (fun x : ℝ => 3*s*(x^2-1)*H b x*density s x) =
        (fun x => (3*s)*((x^2-1)*H b x*density s x)) by funext x; ring,
        integral_const_mul]
      exact h.2 b

theorem solution :
    let H := cqCorr 0.136419125 0.34101124 0.05276111
    (88157382204959954858 : ℝ) / 10 ^ 20 ≤ taylorCoeff 1 H ∧
      ∀ j : ℕ, j < 8 → |taylorCoeff (2 * j + 3) H| ≤
          ((cqHeadUnits[j]?.getD 0 : ℕ) : ℝ) / 10 ^ 20 := by
  let s := 0.136419125 / Real.sqrt (6*(1+(0.34101124:ℝ)^2+0.05276111^2))
  let M := moment s
  have hcoef (m : ℕ) (hm : 1 ≤ m) : taylorCoeff m (cqCorr 0.136419125 0.34101124 0.05276111) =
      cqHeadFromMoments M m := by
    rw [(theorem_5_1 0.136419125 0.34101124 0.05276111).2.1 m hm]
    unfold cqHeadFromMoments
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a+b=0
    · obtain ⟨rfl,rfl⟩ := Nat.add_eq_zero_iff.mp hab
      simp [Polynomial.coeff_one, Nat.ne_of_gt hm]
    · rw [recovery 0.136419125 0.34101124 0.05276111 a b hab]
  have hsq : s^2 = 0.136419125^2 / (6*(1+(0.34101124:ℝ)^2+0.05276111^2)) := by
    rw [show s = _ by rfl, div_pow, Real.sq_sqrt (by positivity)]
  have hcert := partial_moments M cq_sextic_initial_integrals
      (fun n _ hn => odd_moment s n hn)
      (fun n _ => by rw [← hsq]; exact cq_sextic_moment_recurrence s n)
  exact ⟨(hcoef 1 (by decide)).symm ▸ hcert.1,
    fun j hj => (hcoef (2*j+3) (by omega)).symm ▸ hcert.2 j hj⟩
