-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_fifth_price_majorant_quarters
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:10:56.358141+00:00
-- url     : https://prove2.me/submissions/e94cc4af-f33c-4cfd-b167-a738140e95a0

import Definitions.Def_GrothendieckLB_Supplement_cqPriceMajorant
import Definitions.Def_GrothendieckLB_Supplement_cqNonlinearHeadCheck
import Mathlib.Tactic.Eval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false


open GrothendieckLB.Supplement.CQPrice GrothendieckLB.Supplement.CQHeadArithmetic
namespace CQPriceBox
set_option maxRecDepth 120000
set_option maxHeartbeats 200000000
set_option exponentiation.threshold 50000
def S : ℤ := 2^64
def SN : ℕ := 2^64
def D : ℤ := 512
structure Box where
  re : Interval
  im : Interval
  deriving Inhabited,DecidableEq

deriving instance Lean.ToExpr for Interval
deriving instance Lean.ToExpr for Box

def zero : Box := ⟨zeroInterval,zeroInterval⟩
def one : Box := ⟨fixed S,zeroInterval⟩
def plus (x y : Box) : Box := ⟨addInterval x.re y.re,addInterval x.im y.im⟩
def prod (x y : Box) : Box :=
  ⟨subInterval (mulInterval S x.re y.re) (mulInterval S x.im y.im),
   addInterval (mulInterval S x.re y.im) (mulInterval S x.im y.re)⟩
def scale (a : ℤ) (z : Box) : Box := ⟨scaleInterval a z.re,scaleInterval a z.im⟩
def divInt (z : Box) (a : ℕ) : Box := ⟨divideOut a z.re,divideOut a z.im⟩
def lookupB (xs : Array Box) (k : ℕ) := entry zero xs k

def input (l h : ℕ) : Box :=
  let x := (l:ℤ)
  let y := (h:ℤ)
  ⟨⟨S*99999*(D^4-y^4)/(100000*(D^4+y^4)), -(-(S*(D^4-x^4))/(D^4+x^4))⟩,
   ⟨S*99999*(2*x^2*D^2)/(100000*(D^4+x^4)), -(-(S*(2*y^2*D^2))/(D^4+y^4))⟩⟩

def powers (z : Box) : ℕ → Array Box
  | 0 => #[one]
  | k+1 => let xs := powers z k
           xs.push (if k=0 then z else prod (lookupB xs ((k+1)/2)) (lookupB xs (k+1-(k+1)/2)))

def linear (xs : Array Box) : List (ℕ × ℤ) → Box
  | [] => zero
  | (k,a)::ts => plus (scale a (lookupB xs k)) (linear xs ts)

def atPoly (xs : Array Box) (p : RationalPoly) := divInt (linear xs p.terms) p.denominator

def absBound (x : Interval) : ℕ := (max (-x.lo) x.hi).toNat
def normSquared (x : Box) : ℕ := absBound x.re ^ 2 + absBound x.im ^ 2
def ceilRoot (n : ℕ) := let a := Nat.sqrt n; if a*a=n then a else a+1

structure Panel where
  lo : ℕ
  hi : ℕ
  ps : Array Box
  sig : ℕ
  mags : List ℕ
  deriving Inhabited,Lean.ToExpr

def build (l h : ℕ) : Panel :=
  let xs := powers (input l h) 25
  let c := absBound (atPoly xs rho).re
  let den := Nat.sqrt (SN^2-c^2)
  let sig := (SN^2+den-1)/den
  let ms := terms.map (fun t => ceilRoot (normSquared (atPoly xs t.polynomial)))
  ⟨l,h,xs,sig,ms⟩

def rawMoment (ts : List (ℕ × ℕ)) (s : ℕ) :=
  (ts.map (fun e => e.2*s^e.1*SN^(9-e.1))).sum

def numerator (s : ℕ) : List Term → List ℕ → ℕ
  | t::ts,m::ms => m*rawMoment t.moments s + numerator s ts ms
  | _,_ => 0

def normChecks (xs : Array Box) : List Term → List ℕ → Bool
  | [],[] => true
  | t::ts,m::ms => decide (normSquared (atPoly xs t.polynomial) ≤ m^2) && normChecks xs ts ms
  | _,_ => false

def polyShape (p : RationalPoly) : Prop :=
  0<p.denominator ∧ p.terms.all (fun e => decide (e.1≤25))=true
instance (p : RationalPoly) : Decidable (polyShape p) := inferInstanceAs (Decidable (_ ∧ _))
def termShape (t : Term) : Prop :=
  polyShape t.polynomial ∧ t.moments.all (fun e => decide (e.1≤9))=true
instance (t : Term) : Decidable (termShape t) := inferInstanceAs (Decidable (_ ∧ _))

def shape : Prop := polyShape rho ∧ terms.all (fun t => decide (termShape t))=true
instance : Decidable shape := inferInstanceAs (Decidable (_ ∧ _))

def valid (p : Panel) (H : ℕ) : Prop :=
  p.lo ≤ p.hi ∧ p.hi ≤ 512 ∧
  lookupB p.ps 0=one ∧ lookupB p.ps 1=input p.lo p.hi ∧
  (∀ i : Fin 24, let k := i.val+2
    lookupB p.ps k = prod (lookupB p.ps (k/2)) (lookupB p.ps (k-k/2))) ∧
  (let c := absBound (atPoly p.ps rho).re
   c < SN ∧ 0 < p.sig ∧ SN^4 ≤ (SN^2-c^2)*p.sig^2) ∧
  normChecks p.ps terms p.mags = true ∧
  255*numerator p.sig terms p.mags ≤ 100*H*SN^13
instance (p : Panel) (H : ℕ) : Decidable (valid p H) := inferInstanceAs (Decidable (_ ∧ _))

def joined : List Panel → ℕ → ℕ → Bool
  | [],l,h => decide (l=h)
  | x::xs,l,h => decide (l=x.lo) && joined xs x.hi h

def ends0 : List (ℕ × ℕ) := [(0,32), (32,48), (48,56), (56,64), (64,68), (68,72), (72,76), (76,80), (80,84), (84,88), (88,90), (90,92), (92,94), (94,96), (96,98), (98,100), (100,102), (102,104), (104,106), (106,108), (108,109), (109,110), (110,111), (111,112), (112,113), (113,114), (114,115), (115,116), (116,117), (117,118), (118,119), (119,120), (120,121), (121,122), (122,123), (123,124), (124,125), (125,126), (126,127), (127,128)]
noncomputable def q0 : List Panel := eval% (ends0.map (fun e => build e.1 e.2))

def ends1 : List (ℕ × ℕ) := [(128,130), (130,132), (132,134), (134,136), (136,138), (138,140), (140,142), (142,143), (143,144), (144,145), (145,146), (146,147), (147,148), (148,149), (149,150), (150,151), (151,152), (152,153), (153,154), (154,155), (155,156), (156,157), (157,158), (158,159), (159,160), (160,161), (161,162), (162,163), (163,164), (164,165), (165,166), (166,167), (167,168), (168,169), (169,170), (170,171), (171,172), (172,173), (173,174), (174,175), (175,176), (176,177), (177,178), (178,179), (179,180), (180,181), (181,182), (182,183), (183,184), (184,185), (185,186), (186,187), (187,188), (188,189), (189,190), (190,191), (191,192), (192,193), (193,194), (194,195), (195,196), (196,197), (197,198), (198,199), (199,200), (200,201), (201,202), (202,203), (203,204), (204,205), (205,206), (206,207), (207,208), (208,209), (209,210), (210,211), (211,212), (212,213), (213,214), (214,215), (215,216), (216,217), (217,218), (218,219), (219,220), (220,221), (221,222), (222,223), (223,224), (224,225), (225,226), (226,227), (227,228), (228,229), (229,230), (230,231), (231,232), (232,233), (233,234), (234,235), (235,236), (236,237), (237,238), (238,240), (240,242), (242,244), (244,246), (246,248), (248,250), (250,252), (252,254), (254,256)]
noncomputable def q1 : List Panel := eval% (ends1.map (fun e => build e.1 e.2))

def ends2 : List (ℕ × ℕ) := [(256,257), (257,258), (258,259), (259,260), (260,261), (261,262), (262,263), (263,264), (264,265), (265,266), (266,268), (268,270), (270,272), (272,274), (274,276), (276,278), (278,280), (280,282), (282,284), (284,288), (288,292), (292,296), (296,300), (300,304), (304,312), (312,320), (320,328), (328,336), (336,352), (352,384)]
noncomputable def q2 : List Panel := eval% (ends2.map (fun e => build e.1 e.2))

def ends3 : List (ℕ × ℕ) := [(384,385), (385,386), (386,388), (388,390), (390,392), (392,396), (396,400), (400,408), (408,416), (416,432), (432,448), (448,512)]
noncomputable def q3 : List Panel := eval% (ends3.map (fun e => build e.1 e.2))

end CQPriceBox

namespace CQPriceBox
set_option maxRecDepth 200000
set_option maxHeartbeats 400000000
set_option exponentiation.threshold 50000
set_option Elab.async false
theorem shapes : shape := by decide +kernel
theorem numeric0 : q0.all (fun p => decide (valid p 531000))=true ∧ joined q0 0 128=true := by decide +kernel
theorem numeric1 : q1.all (fun p => decide (valid p 545000))=true ∧ joined q1 128 256=true := by decide +kernel
theorem numeric2 : q2.all (fun p => decide (valid p 486000))=true ∧ joined q2 256 384=true := by decide +kernel
theorem numeric3 : q3.all (fun p => decide (valid p 84000))=true ∧ joined q3 384 512=true := by decide +kernel
end CQPriceBox


open GrothendieckLB.Supplement GrothendieckLB.Supplement.CQPrice GrothendieckLB.Supplement.CQHeadArithmetic
namespace CQPriceBox
def rawC (b : Interval) (x : ℝ) : Prop := (b.lo:ℝ) ≤ x ∧ x ≤ (b.hi:ℝ)
def covers (s : ℤ) (b : Interval) (x : ℝ) : Prop := rawC b ((s:ℝ)*x)

theorem rawP {b c : Interval} {x y : ℝ} (hx : rawC b x) (hy : rawC c y) :
    rawC (addInterval b c) (x+y) := by
  simpa [rawC,addInterval] using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem rawM {b c : Interval} {x y : ℝ} (hx : rawC b x) (hy : rawC c y) :
    rawC (subInterval b c) (x-y) := by
  simpa [rawC,subInterval] using And.intro (sub_le_sub hx.1 hy.2) (sub_le_sub hx.2 hy.1)

theorem rawTimes {b : Interval} {x : ℝ} (hx : rawC b x) (k : ℤ) :
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

theorem rawQuo {b : Interval} {x : ℝ} (hx : rawC b x) {d : ℤ} (hd : 0 < d) :
    rawC (divideOut d b) (x/(d:ℝ)) := by
  have hp : 0 < (d:ℝ) := by exact_mod_cast hd
  have hl : (↑(b.lo/d):ℝ)*(d:ℝ) ≤ (b.lo:ℝ) := by exact_mod_cast Int.ediv_mul_le _ hd.ne'
  have hu : (↑((-b.hi)/d):ℝ)*(d:ℝ) ≤ -(b.hi:ℝ) := by exact_mod_cast Int.ediv_mul_le _ hd.ne'
  constructor
  · exact (le_div_iff₀ hp).2 (hl.trans hx.1)
  · apply (div_le_iff₀ hp).2
    simp only [divideOut,Int.cast_neg,neg_mul]
    linarith only [hu,hx.2]

theorem lineLow {a b x t l : ℝ} (hal : l ≤ a*t) (hbl : l ≤ b*t)
    (ha : a ≤ x) (hb : x ≤ b) : l ≤ x*t := by
  rcases le_total 0 t with ht|ht
  · exact hal.trans (mul_le_mul_of_nonneg_right ha ht)
  · exact hbl.trans (mul_le_mul_of_nonpos_right hb ht)

theorem lineHigh {a b x t l : ℝ} (hal : a*t ≤ l) (hbl : b*t ≤ l)
    (ha : a ≤ x) (hb : x ≤ b) : x*t ≤ l := by
  rcases le_total 0 t with ht|ht
  · exact (mul_le_mul_of_nonneg_right hb ht).trans hbl
  · exact (mul_le_mul_of_nonpos_right ha ht).trans hal

theorem rawProd {b e : Interval} {x y : ℝ} (hx : rawC b x) (hy : rawC e y)
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

theorem cvZ (s : ℤ) : covers s zeroInterval 0 := by simp [covers,rawC,zeroInterval]
theorem cvOne (s : ℤ) : covers s (fixed s) 1 := by simp [covers,rawC,fixed]
theorem cvP {s : ℤ} {a b : Interval} {x y : ℝ} (hx : covers s a x) (hy : covers s b y) :
    covers s (addInterval a b) (x+y) := by simpa only [covers,mul_add] using rawP hx hy
theorem cvM {s : ℤ} {a b : Interval} {x y : ℝ} (hx : covers s a x) (hy : covers s b y) :
    covers s (subInterval a b) (x-y) := by simpa only [covers,mul_sub] using rawM hx hy
theorem cvTimes {s : ℤ} {a : Interval} {x : ℝ} (hx : covers s a x) (k : ℤ) :
    covers s (scaleInterval k a) ((k:ℝ)*x) := by simpa only [covers,mul_left_comm] using rawTimes hx k
theorem cvQuo {s : ℤ} {a : Interval} {x : ℝ} (hx : covers s a x) {d : ℤ} (hd : 0 < d) :
    covers s (divideOut d a) (x/(d:ℝ)) := by simpa only [covers,mul_div_assoc] using rawQuo hx hd
theorem cvProd {s : ℤ} (hs : 0 < s) {a b : Interval} {x y : ℝ} (hx : covers s a x) (hy : covers s b y) :
    covers s (mulInterval s a b) (x*y) := by
  have hp : (s:ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold covers
  rw [show (s:ℝ)*(x*y)=((s:ℝ)*x)*((s:ℝ)*y)/(s:ℝ) by field_simp [hp]]
  exact rawProd hx hy hs


theorem sPos : 0<S := by decide
theorem sReal : 0<(S:ℝ) := by exact_mod_cast sPos
theorem snCast : (SN:ℝ)=(S:ℝ) := by norm_num [S,SN]

def encloses (b : Box) (z : ℂ) : Prop := covers S b.re z.re ∧ covers S b.im z.im

theorem enZero : encloses zero 0 := ⟨cvZ _,cvZ _⟩
theorem enOne : encloses one 1 := ⟨cvOne _,cvZ _⟩
theorem enAdd {p q : Box} {z w : ℂ} (h : encloses p z) (k : encloses q w) :
    encloses (plus p q) (z+w) := ⟨cvP h.1 k.1,cvP h.2 k.2⟩

theorem enMul {p q : Box} {z w : ℂ} (h : encloses p z) (k : encloses q w) :
    encloses (prod p q) (z*w) := by
  exact ⟨cvM (cvProd sPos h.1 k.1) (cvProd sPos h.2 k.2),
    cvP (cvProd sPos h.1 k.2) (cvProd sPos h.2 k.1)⟩

theorem enScale {p : Box} {z : ℂ} (hp : encloses p z) (a : ℤ) : encloses (scale a p) ((a:ℂ)*z) := by
  constructor
  · simpa only [scale, Complex.mul_re,Complex.intCast_re,Complex.intCast_im,zero_mul,sub_zero] using cvTimes hp.1 a
  · simpa only [scale, Complex.mul_im,Complex.intCast_re,Complex.intCast_im,zero_mul,add_zero] using cvTimes hp.2 a

theorem enDiv {p : Box} {z : ℂ} (hp : encloses p z) (a : ℕ) (ha : 0<a) :
    encloses (divInt p a) (z/a) := by
  have h : 0<(a:ℤ) := by exact_mod_cast ha
  constructor
  · simpa only [divInt, Complex.div_natCast_re,Int.cast_natCast] using cvQuo hp.1 h
  · simpa only [divInt, Complex.div_natCast_im,Int.cast_natCast] using cvQuo hp.2 h

theorem enPowers (p : Panel) (z : ℂ) (h0 : lookupB p.ps 0=one) (h1 : encloses (lookupB p.ps 1) z)
    (rec : ∀ i : Fin 24, let k := i.val+2
      lookupB p.ps k = prod (lookupB p.ps (k/2)) (lookupB p.ps (k-k/2))) :
    ∀ j, j≤25 → encloses (lookupB p.ps j) (z^j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    rcases j with _|j
    · rw [pow_zero,h0];exact enOne
    rcases j with _|i
    · simpa using h1
    have hrec := rec ⟨i,by omega⟩
    change lookupB p.ps (i+2) = prod (lookupB p.ps ((i+2)/2)) (lookupB p.ps (i+2-(i+2)/2)) at hrec
    rw [hrec]
    have hh := enMul (ih ((i+2)/2) (by omega) (by omega)) (ih (i+2-(i+2)/2) (by omega) (by omega))
    rw [← pow_add,show (i+2)/2+(i+2-(i+2)/2)=i+2 by omega] at hh
    exact hh

theorem enLinear (ps : Array Box) (z : ℂ)
    (hp : ∀ k, k≤25 → encloses (lookupB ps k) (z^k)) (xs : List (ℕ×ℤ))
    (hx : ∀ t∈xs,t.1≤25) :
    encloses (linear ps xs) ((xs.map (fun t => (t.2:ℂ)*z^t.1)).sum) := by
  induction xs with
  | nil => exact enZero
  | cons x xs ih =>
    rcases x with ⟨k,a⟩
    exact enAdd (enScale (hp k (hx (k,a) (by simp))) a) (ih (fun t ht => hx t (by simp [ht])))

theorem enPoly (ps : Array Box) (z : ℂ) (hp : ∀ k, k≤25 → encloses (lookupB ps k) (z^k))
    (p : RationalPoly) (h : polyShape p) : encloses (atPoly ps p) (CQPrice.eval p z) := by
  apply enDiv (enLinear ps z hp p.terms _ ) _ h.1
  intro t ht; exact of_decide_eq_true (List.all_eq_true.mp h.2 t ht)

theorem absCover {v : Interval} {x : ℝ} (hv : covers S v x) : |(S:ℝ)*x|≤(absBound v:ℝ) := by
  have h1 : (-v.lo : ℤ)≤((absBound v:ℕ):ℤ) :=
    (le_max_left _ _).trans (Int.self_le_toNat _)
  have h2 : v.hi≤((absBound v:ℕ):ℤ) :=
    (le_max_right _ _).trans (Int.self_le_toNat _)
  have h1' : -(v.lo:ℝ)≤(absBound v:ℝ) := by exact_mod_cast h1
  have h2' : (v.hi:ℝ)≤(absBound v:ℝ) := by exact_mod_cast h2
  exact abs_le.mpr ⟨by linarith only [hv.1,h1'],hv.2.trans h2'⟩

theorem normCap {b : Box} {z : ℂ} {m : ℕ} (h : encloses b z) (hm : normSquared b≤m^2) :
    ‖z‖≤(m:ℝ)/(SN:ℝ) := by
  rw [snCast,le_div_iff₀ sReal]
  have hr := absCover h.1
  have hi := absCover h.2
  have hr' := pow_le_pow_left₀ (abs_nonneg _) hr 2
  have hi' := pow_le_pow_left₀ (abs_nonneg _) hi 2
  have hm' : (absBound b.re:ℝ)^2+(absBound b.im:ℝ)^2≤(m:ℝ)^2 := by exact_mod_cast hm
  apply le_of_sq_le_sq _ (Nat.cast_nonneg _)
  rw [mul_pow,Complex.sq_norm,Complex.normSq_apply]
  rw [sq_abs,mul_pow] at hr' hi'
  nlinarith only [hr',hi',hm']

end CQPriceBox

open GrothendieckLB.Supplement GrothendieckLB.Supplement.CQPrice GrothendieckLB.Supplement.CQHeadArithmetic
namespace CQPriceBox
set_option maxRecDepth 10000
set_option exponentiation.threshold 50000
set_option maxHeartbeats 2000000

theorem sigmaCap (z : ℂ) (b : Box) (sig : ℕ) (he : encloses b (CQPrice.eval rho z))
    (hc : absBound b.re < SN) (hpos : 0<sig)
    (hv : SN^4 ≤ (SN^2 - absBound b.re^2)*sig^2) : sigma z ≤ (sig:ℝ)/(SN:ℝ) := by
  let x := (CQPrice.eval rho z).re
  let c := absBound b.re
  have hs : 0<(SN:ℝ) := by norm_num [SN]
  have hcr : (c:ℝ)<(SN:ℝ) := by exact_mod_cast hc
  have hsr : 0<(sig:ℝ) := Nat.cast_pos.mpr hpos
  have hsub : c^2≤SN^2 := Nat.pow_le_pow_left hc.le 2
  have hp : (SN:ℝ)^4≤((SN:ℝ)^2-(c:ℝ)^2)*(sig:ℝ)^2 := by
    exact_mod_cast (show SN^4 ≤ (SN^2-c^2)*sig^2 from hv)
  have h := absCover he.1
  rw [← snCast] at h
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs,mul_pow] at h2
  change (SN:ℝ)^2*x^2 ≤ (c:ℝ)^2 at h2
  have hc2 : (c:ℝ)^2<(SN:ℝ)^2 := by
    nlinarith only [mul_pos (sub_pos.mpr hcr) (show 0<(SN:ℝ)+(c:ℝ) by positivity)]
  have hgap : 0<1-x^2 := by
    by_contra! hh
    have hh' := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (SN:ℝ)) hh
    nlinarith only [h2,hc2,hh']
  have hden : (SN:ℝ)^2-(c:ℝ)^2 ≤ (SN:ℝ)^2*(1-x^2) := by nlinarith only [h2]
  have hg := hp.trans (mul_le_mul_of_nonneg_right hden (sq_nonneg (sig:ℝ)))
  have ht : (SN:ℝ)^2≤(1-x^2)*(sig:ℝ)^2 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hs)).mp
    nlinarith only [hg]
  have hsq : (SN:ℝ)≤Real.sqrt (1-x^2)*(sig:ℝ) := by
    apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) hsr.le)
    rw [mul_pow,Real.sq_sqrt hgap.le]; exact ht
  change (Real.sqrt (1-x^2))⁻¹ ≤ (sig:ℝ)/(SN:ℝ)
  rw [← one_div,div_le_div_iff₀ (Real.sqrt_pos.mpr hgap) hs,one_mul,mul_comm]
  exact hsq

private theorem momentSum (ts : List (ℕ×ℕ)) (v : ℝ) (sig : ℕ) (hv : 0≤v)
    (hsig : v≤(sig:ℝ)/(SN:ℝ)) (hts : ∀ e∈ts,e.1≤9) :
    (ts.map (fun e => (e.2:ℝ)*v^e.1)).sum ≤ (rawMoment ts sig:ℝ)/(SN:ℝ)^9 := by
  have hs : 0<(SN:ℝ) := by norm_num [SN]
  induction ts with
  | nil => simp [rawMoment]
  | cons e ts ih =>
    obtain ⟨k,d⟩ := e
    have hk : k≤9 := hts (k,d) (by simp)
    have h9 : (SN:ℝ)^9=(SN:ℝ)^k*(SN:ℝ)^(9-k) := by
      rw [← pow_add,show k+(9-k)=9 by omega]
    have hpow := pow_le_pow_left₀ hv hsig k
    have hfirst : (d:ℝ)*v^k ≤ ((d:ℝ)*(sig:ℝ)^k*(SN:ℝ)^(9-k))/(SN:ℝ)^9 := by
      calc
        _ ≤ (d:ℝ)*((sig:ℝ)/(SN:ℝ))^k := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
        _ = _ := by rw [div_pow,h9]; field_simp [hs.ne']
    have ht := ih (fun e he => hts e (by simp [he]))
    simp only [rawMoment,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
    rw [add_div]
    exact add_le_add hfirst ht

private theorem moment_le (t : Term) (v : ℝ) (sig : ℕ) (hv : 0≤v) (hsig : v≤(sig:ℝ)/(SN:ℝ))
    (ht : termShape t) : momentBound t v ≤ (rawMoment t.moments sig:ℝ)/(SN:ℝ)^12 := by
  have h := momentSum t.moments v sig hv hsig (fun e he => of_decide_eq_true (List.all_eq_true.mp ht.2 e he))
  have h9 : (SN:ℝ)^9*(2:ℝ)^192=(SN:ℝ)^12 := by norm_num [SN]
  unfold momentBound
  calc
    _ ≤ ((rawMoment t.moments sig:ℝ)/(SN:ℝ)^9)/(2:ℝ)^192 :=
      div_le_div_of_nonneg_right h (by positivity)
    _ = _ := by rw [div_div,h9]

private theorem moments_nonnegative (t : Term) {v : ℝ} (hv : 0≤v) : 0≤momentBound t v := by
  apply div_nonneg _ (by positivity)
  have g (xs : List (ℕ×ℕ)) : 0≤(xs.map (fun e => (e.2:ℝ)*v^e.1)).sum := by
    induction xs with
    | nil => simp
    | cons e xs ih =>
      exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hv _)) ih
  exact g _

theorem terms_le (z : ℂ) (ps : Array Box) (sig : ℕ)
    (hp : ∀ k, k≤25 → encloses (lookupB ps k) (z^k))
    (hs : sigma z≤(sig:ℝ)/(SN:ℝ)) (ts : List Term) (ms : List ℕ)
    (hn : normChecks ps ts ms=true) (hshape : ∀ t∈ts,termShape t) :
    (ts.map (fun t => ‖CQPrice.eval t.polynomial z‖ * momentBound t (sigma z))).sum ≤
      (numerator sig ts ms:ℝ)/(SN:ℝ)^13 := by
  have hv : 0≤sigma z := inv_nonneg.mpr (Real.sqrt_nonneg _)
  induction ts generalizing ms with
  | nil => cases ms <;> simp [numerator]
  | cons t ts ih =>
    cases ms with
    | nil => simp [normChecks] at hn
    | cons m ms =>
      simp only [normChecks,Bool.and_eq_true,decide_eq_true_eq] at hn
      have ht := hshape t (by simp)
      have hb := normCap (enPoly ps z hp t.polynomial ht.1) hn.1
      have hd := moment_le t (sigma z) sig hv hs ht
      have hpart : ‖CQPrice.eval t.polynomial z‖ * momentBound t (sigma z) ≤
          ((m:ℝ)*(rawMoment t.moments sig:ℝ))/(SN:ℝ)^13 := by
        calc
          _ ≤ ((m:ℝ)/(SN:ℝ))*((rawMoment t.moments sig:ℝ)/(SN:ℝ)^12) :=
            mul_le_mul hb hd (moments_nonnegative _ hv) (by positivity)
          _ = _ := by rw [div_mul_div_comm,show (SN:ℝ)*(SN:ℝ)^12=(SN:ℝ)^13 by ring]
      have hrest := ih ms hn.2 (fun x hx => hshape x (by simp [hx]))
      simp only [List.map_cons,List.sum_cons,numerator,Nat.cast_add,Nat.cast_mul,add_div]
      exact add_le_add hpart hrest

theorem majorant_cap (p : Panel) (H : ℕ) (h : valid p H) (hshape : shape) (z : ℂ)
    (hz : encloses (input p.lo p.hi) z) : (2.55:ℝ)*majorant z ≤ H := by
  obtain ⟨_,_,hz0,hz1,hp,hs,hn,hnum⟩ := h
  have hpow := enPowers p z hz0 (hz1.symm ▸ hz) hp
  have sig := sigmaCap z _ p.sig (enPoly p.ps z hpow rho hshape.1) hs.1 hs.2.1 hs.2.2
  have hM := terms_le z p.ps p.sig hpow sig terms p.mags hn
    (fun t ht => of_decide_eq_true (List.all_eq_true.mp hshape.2 t ht))
  have he : (255:ℝ)*(numerator p.sig terms p.mags:ℝ) ≤ 100*(H:ℝ)*(SN:ℝ)^13 := by exact_mod_cast hnum
  calc
    _ ≤ 2.55*((numerator p.sig terms p.mags:ℝ)/(SN:ℝ)^13) := mul_le_mul_of_nonneg_left hM (by norm_num)
    _ ≤ _ := by
      rw [← mul_div_assoc,div_le_iff₀ (by norm_num [SN] : 0<(SN:ℝ)^13)]
      linarith only [he]

end CQPriceBox

open GrothendieckLB.Supplement GrothendieckLB.Supplement.CQPrice GrothendieckLB.Supplement.CQHeadArithmetic
namespace CQPriceBox
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 50000

private noncomputable def xr (s : ℝ) := (1-s^4)/(1+s^4)
private noncomputable def yi (s : ℝ) := 2*s^2/(1+s^4)
private theorem x_nonneg {x : ℝ} (hx : 0≤x) (h1 : x≤1) : 0≤xr x :=
  div_nonneg (sub_nonneg.mpr (pow_le_one₀ hx h1)) (by positivity)
private theorem y_nonneg (x : ℝ) : 0≤yi x := by unfold yi; positivity
private theorem x_decreasing {a b : ℝ} (ha : 0≤a) (h : a≤b) : xr b≤xr a := by
  unfold xr
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith only [pow_le_pow_left₀ ha h 4]
private theorem y_increasing {a b : ℝ} (ha : 0≤a) (h : a≤b) (hb : b≤1) : yi a≤yi b := by
  have h1 := pow_le_pow_left₀ ha h 2
  have h2 := pow_le_one₀ (ha.trans h) hb (n:=2)
  have h3 := pow_le_one₀ ha (h.trans hb) (n:=2)
  have h4 : a^2*b^2 ≤ 1 := by
    calc
      _ ≤ (1:ℝ)*1 := mul_le_mul h3 h2 (sq_nonneg _) (by norm_num)
      _ = _ := by ring
  unfold yi
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith only [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h4)]

private theorem x_ratio (k : ℕ) :
    xr ((k:ℝ)/512) = (((D^4-(k:ℤ)^4:ℤ):ℝ))/((D^4+(k:ℤ)^4:ℤ):ℝ) := by
  unfold xr D
  push_cast
  field_simp <;> ring
private theorem y_ratio (k : ℕ) :
    yi ((k:ℝ)/512) = (((2*(k:ℤ)^2*D^2:ℤ):ℝ))/((D^4+(k:ℤ)^4:ℤ):ℝ) := by
  unfold yi D
  push_cast
  field_simp <;> ring

private theorem lower (u d : ℤ) (hd : 0<d) :
    ((S*99999*u/(100000*d):ℤ):ℝ) ≤ (S:ℝ)*((99999:ℝ)/100000*((u:ℝ)/d)) := by
  have hD : 0<100000*d := by positivity
  have hD' : 0<((100000*d:ℤ):ℝ) := by exact_mod_cast hD
  have hf : ((S*99999*u/(100000*d):ℤ):ℝ) * ((100000*d:ℤ):ℝ) ≤ ((S*99999*u:ℤ):ℝ) :=
    by exact_mod_cast Int.ediv_mul_le (S*99999*u) hD.ne'
  calc
    _ ≤ ((S*99999*u:ℤ):ℝ)/((100000*d:ℤ):ℝ) := (le_div_iff₀ hD').mpr hf
    _ = _ := by push_cast; ring

private theorem upper (u d : ℤ) (hd : 0<d) :
    (S:ℝ)*((u:ℝ)/d) ≤ ((-(-(S*u)/d):ℤ):ℝ) := by
  have hD : 0<(d:ℝ) := by exact_mod_cast hd
  have hf : ((-(S*u)/d:ℤ):ℝ)*(d:ℝ) ≤ -((S:ℝ)*u) :=
    by exact_mod_cast Int.ediv_mul_le (-(S*u)) hd.ne'
  rw [Int.cast_neg, ← mul_div_assoc, div_le_iff₀ hD,neg_mul]
  linarith only [hf]

theorem chart (l h : ℕ) (lh : l≤h) (hh : h≤512)
    (r s : ℝ) (hr : (99999:ℝ)/100000≤r) (hr1 : r<1)
    (hL : (l:ℝ)/512≤s) (hH : s≤(h:ℝ)/512) :
    encloses (input l h) (point r s) := by
  let a := (l:ℝ)/512
  let b := (h:ℝ)/512
  have ha : 0≤a := by dsimp [a]; positivity
  have hb : 0≤b := by dsimp [b]; positivity
  have hb1 : b≤1 := by dsimp [b]; apply (div_le_iff₀ (by norm_num)).mpr; norm_num; exact_mod_cast hh
  have haS : a≤s := hL
  have hsB : s≤b := hH
  have hs0 := ha.trans haS
  have hs1 := hsB.trans hb1
  have r0 : 0≤r := by linarith only [hr]
  have hdb (k : ℕ) : 0<D^4+(k:ℤ)^4 := by unfold D; positivity
  constructor
  · constructor
    · calc
        _ ≤ (S:ℝ)*((99999:ℝ)/100000*xr b) := by
          dsimp [b]; rw [x_ratio]; exact lower _ _ (hdb h)
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul hr (x_decreasing hs0 hsB) (x_nonneg hb hb1) r0) sReal.le
    · calc
        _ ≤ (S:ℝ)*(1*xr a) := mul_le_mul_of_nonneg_left
          (mul_le_mul hr1.le (x_decreasing ha haS) (x_nonneg hs0 hs1) (by norm_num)) sReal.le
        _ ≤ _ := by dsimp [a]; rw [one_mul,x_ratio];exact upper _ _ (hdb l)
  · constructor
    · calc
        _ ≤ (S:ℝ)*((99999:ℝ)/100000*yi a) := by
          dsimp [a]; rw [y_ratio];exact lower _ _ (hdb l)
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul hr (y_increasing ha haS hs1) (y_nonneg _) r0) sReal.le
    · calc
        _ ≤ (S:ℝ)*(1*yi b) := mul_le_mul_of_nonneg_left
          (mul_le_mul hr1.le (y_increasing hs0 hsB hb1) (y_nonneg _) (by norm_num)) sReal.le
        _ ≤ _ := by dsimp [b]; rw [one_mul,y_ratio];exact upper _ _ (hdb h)

theorem quarter (ps : List Panel) (H : ℕ) (hq : ps.all (fun p => decide (valid p H))=true)
    (r s : ℝ) (hr : (99999:ℝ)/100000≤r) (hr1 : r<1)
    (lo hi : ℕ) (hj : joined ps lo hi=true) (hlt : lo<hi)
    (hl : (lo:ℝ)/512≤s) (hh : s≤(hi:ℝ)/512) :
    2.55*majorant (point r s) ≤ H := by
  induction ps generalizing lo hi with
  | nil => simp [joined] at hj; omega
  | cons p ps ih =>
    simp only [joined,Bool.and_eq_true,decide_eq_true_eq] at hj
    simp only [List.all_cons,Bool.and_eq_true,decide_eq_true_eq] at hq
    rw [hj.1] at hl
    by_cases h : s≤(p.hi:ℝ)/512
    · exact majorant_cap p H hq.1 shapes _ (chart _ _ hq.1.1 hq.1.2.1 r s hr hr1 hl h)
    · have hrange : (p.hi:ℝ)<(hi:ℝ) := by linarith
      exact ih hq.2 p.hi hi hj.2 (by exact_mod_cast hrange) (le_of_lt (lt_of_not_ge h)) hh

end CQPriceBox
open CQPriceBox
theorem solution (r s : ℝ) (hr : (99999:ℝ)/100000≤r) (hr₁ : r<1) (hs : s∈Set.Icc 0 1) :
    let u := (2.55:ℝ)*majorant (point r s)
    (s≤1/4 → u≤531000) ∧ (1/4≤s → s≤1/2 → u≤545000) ∧
      (1/2≤s → s≤3/4 → u≤486000) ∧ (3/4≤s → u≤84000) := by
  refine ⟨fun hh => ?_,fun hl hh => ?_,fun hl hh => ?_,fun hl => ?_⟩
  · exact quarter q0 531000 numeric0.1 r s hr hr₁ 0 128 numeric0.2 (by decide)
      (by norm_num;exact hs.1) (by norm_num at *;linarith only [hh])
  · exact quarter q1 545000 numeric1.1 r s hr hr₁ 128 256 numeric1.2 (by decide)
      (by norm_num at *;linarith only [hl]) (by norm_num at *;linarith only [hh])
  · exact quarter q2 486000 numeric2.1 r s hr hr₁ 256 384 numeric2.2 (by decide)
      (by norm_num at *;linarith only [hl]) (by norm_num at *;linarith only [hh])
  · exact quarter q3 84000 numeric3.1 r s hr hr₁ 384 512 numeric3.2 (by decide)
      (by norm_num at *;linarith only [hl]) (by norm_num;exact hs.2)