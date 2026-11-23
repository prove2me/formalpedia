-- Prove2me | solution 1 for GrothendieckLB.Supplement.gauss_four_panel_upper_error
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:53:20.093421+00:00
-- url     : https://prove2.me/submissions/9d6cfede-ec06-4681-bf08-db72b24c7f1b

import Definitions.Def_GrothendieckLB_Supplement_cqGaussFourPanel
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib

open Set Polynomial MeasureTheory
open scoped BigOperators
noncomputable section
namespace GaussPanelProof
private abbrev I := Icc (0:ℝ) 1
private theorem betweenZeros {f : ℝ → ℝ} (hf : Continuous f) (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ I ∧ f x = 0) :
    ∃ u : Finset ℝ, Disjoint u s ∧ s.card ≤ u.card+1 ∧
      ∀ x ∈ u, x ∈ I ∧ deriv f x = 0 := by
  classical
  let g (p : ℝ × ℝ) : ℝ := if h : ∃ z ∈ Ioo p.1 p.2, deriv f z = 0 then h.choose else 0
  let pairs := (s ×ˢ s).filter fun p => p.1 < p.2
  let t := pairs.image g
  have root {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hlt : x < y) :
      g (x,y) ∈ Ioo x y ∧ deriv f (g (x,y)) = 0 := by
    have h := exists_deriv_eq_zero hlt hf.continuousOn ((hs x hx).2.trans (hs y hy).2.symm)
    simpa only [g, dif_pos h] using h.choose_spec
  refine ⟨t \ s, Finset.disjoint_sdiff.symm, Finset.card_le_sdiff_of_interleaved ?_, ?_⟩
  · intro x hx y hy hlt _
    exact ⟨g (x,y), Finset.mem_image.mpr ⟨(x,y), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hy⟩,hlt⟩,rfl⟩,
      (root hx hy hlt).1⟩
  · intro z hz
    obtain ⟨⟨x,y⟩,hp,rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hz).1
    obtain ⟨hxy,hlt⟩ := Finset.mem_filter.mp hp
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    obtain ⟨⟨h1,h2⟩,h3⟩ := root hx hy hlt
    exact ⟨⟨(hs x hx).1.1.trans h1.le,h2.le.trans (hs y hy).1.2⟩,h3⟩

private theorem manyZeros (n : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ n f)
    (s : Finset ℝ) (hs : ∀ x ∈ s, x ∈ I ∧ f x = 0) (hcard : n < s.card) :
    ∃ x ∈ I, iteratedDeriv n f x = 0 := by
  induction n generalizing f s with
  | zero =>
    obtain ⟨x,hx⟩ := Finset.card_pos.mp hcard
    exact ⟨x,(hs x hx).1,by simpa using (hs x hx).2⟩
  | succ n ih =>
    obtain ⟨u,_,h,hu⟩ := betweenZeros hf.continuous s hs
    simpa only [iteratedDeriv_succ'] using ih hf.deriv' u hu (by omega)

private def term (s : Finset ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ[X] :=
  let L := Lagrange.basis s id u
  (C (f u) + C (deriv f u - 2*f u*L.derivative.eval u)*(X-C u))*L^2

private theorem interpolant (s : Finset ℝ) (hc : s.card = 4) (f : ℝ → ℝ) :
    ∃ p : ℝ[X], p.natDegree ≤ 7 ∧ ∀ u ∈ s, p.eval u = f u ∧ p.derivative.eval u = deriv f u := by
  classical
  refine ⟨∑ u ∈ s, term s f u,?_,?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro u hu
    have hL := Lagrange.natDegree_basis (s:=s) (v:=id) (Set.injOn_id _) hu
    rw [hc] at hL
    unfold term
    calc
      _ ≤ _ := natDegree_mul_le
      _ ≤ 1+2*3 := by
        gcongr
        · apply natDegree_add_le_of_degree_le
          · simp
          · calc
              _ ≤ _ := natDegree_mul_le
              _ ≤ 0+1 := by rw [natDegree_C,natDegree_X_sub_C]
        · exact (natDegree_pow_le.trans (Nat.mul_le_mul_left _ (by omega)))
      _ = _ := by decide
  · intro x hx
    have diag : (Lagrange.basis s id x).eval x = 1 := Lagrange.eval_basis_self (Set.injOn_id _) hx
    have off (u : ℝ) (hu : u ≠ x) : (Lagrange.basis s id u).eval x = 0 := Lagrange.eval_basis_of_ne (v:=id) hu hx
    constructor
    · rw [eval_finsetSum,Finset.sum_eq_single_of_mem x hx (fun u _ hux => by simp [term,off u hux])]
      simp [term,diag]
    · rw [derivative_sum,eval_finsetSum,Finset.sum_eq_single_of_mem x hx (fun u _ hux => by
        simp [term,derivative_mul,derivative_pow,off u hux])]
      simp [term,derivative_mul,derivative_pow,diag]
      <;> ring

private theorem smoothEval (p : ℝ[X]) (n : ℕ) : ContDiff ℝ n p.eval := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [eval_add] using hp.add hq
  | monomial n a =>
    simp only [eval_monomial]
    fun_prop

private theorem evalJet (n : ℕ) (p : ℝ[X]) :
    iteratedDeriv n p.eval = (derivative^[n] p).eval := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih,Function.iterate_succ_apply']
    funext x
    exact Polynomial.deriv _

private theorem doubleZeros (s : Finset ℝ) (hs : s.card=4) (x : ℝ) (hx : x ∉ s)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 8 f) (hz : ∀ z ∈ insert x s, z ∈ I ∧ f z=0)
    (hd : ∀ z ∈ s, deriv f z=0) : ∃ y ∈ I, iteratedDeriv 8 f y=0 := by
  classical
  obtain ⟨u,hu,hc,hzu⟩ := betweenZeros hf.continuous (insert x s) hz
  have hdis : Disjoint u s := hu.mono_right (Finset.subset_insert _ _)
  have h8 : 7 < (u∪s).card := by
    rw [Finset.card_union_of_disjoint hdis,hs]
    rw [Finset.card_insert_of_notMem hx,hs] at hc
    omega
  have hh (v : ℝ) (hv : v ∈ u∪s) : v ∈ I ∧ deriv f v = 0 := by
    rcases Finset.mem_union.mp hv with h | h
    · exact hzu v h
    · exact ⟨(hz v (Finset.mem_insert_of_mem h)).1,hd v h⟩
  exact (iteratedDeriv_succ' (n:=7) (f:=f)) ▸ manyZeros 7 hf.deriv' _ hh h8

private theorem derivativeSum (n : ℕ) (p r : ℝ[X]) :
    derivative^[n] (p+r) = derivative^[n] p+derivative^[n] r := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply',ih,map_add]

private theorem evalTop {p : ℝ[X]} {n : ℕ} (hd : p.natDegree = n) (hm : p.Monic) :
    derivative^[n] p = C (n.factorial:ℝ) := by
  ext i
  rw [coeff_iterate_derivative]
  by_cases hi : i=0
  · subst i
    simp [←hd,hm.coeff_natDegree,Nat.descFactorial_self]
  · rw [coeff_eq_zero_of_natDegree_lt (show p.natDegree < i+n by omega)]
    simp [coeff_C,hi,Ne.symm hi]

private theorem majorant {s : Finset ℝ} (hc : s.card=4) (hs : ∀ u ∈ s, u ∈ I)
    {q : ℝ[X]} (hroot : ∀ u, q.eval u=0 ↔ u ∈ s)
    (hdq : (q^2).natDegree=8) (hm : (q^2).Monic)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 8 f) {B : ℝ} (hB : ∀ x ∈ I, iteratedDeriv 8 f x ≤ B) :
    ∃ p : ℝ[X], p.natDegree ≤ 7 ∧ (∀ u ∈ s, p.eval u=f u) ∧
      ∀ x ∈ I, f x ≤ p.eval x+(B/40320)*(q.eval x)^2 := by
  classical
  obtain ⟨p,hdeg,hp⟩ := interpolant s hc f
  refine ⟨p,hdeg,fun u hu => (hp u hu).1,?_⟩
  intro x hx
  by_cases hx' : x ∈ s
  · simp [(hp x hx').1,(hroot x).2 hx']
  have hq : q.eval x ≠ 0 := fun h => hx' ((hroot x).1 h)
  let c := (f x-p.eval x)/(q.eval x)^2
  let R := p+C c*q^2
  let g := f-R.eval
  have hg : ContDiff ℝ 8 g := hf.sub (smoothEval R 8)
  have gx : g x=0 := by
    change f x-(p+C c*q^2).eval x=0
    simp only [eval_add,eval_mul,eval_pow,eval_C,c]
    field_simp
    <;> ring
  have gu {u : ℝ} (hu : u ∈ s) : g u=0 := by simp [g,R,(hp u hu).1,(hroot u).2 hu]
  have gdu (u : ℝ) (hu : u ∈ s) : deriv g u=0 := by
    rw [show deriv g u = deriv f u-deriv R.eval u from deriv_sub
      (hf.differentiable (by norm_num) u) (R.differentiable u),R.deriv]
    simp [R,derivative_mul,derivative_pow,(hroot u).2 hu,(hp u hu).2]
  obtain ⟨v,hv,hv'⟩ := doubleZeros s hc x hx' g hg (by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl|hu
    · exact ⟨hx,gx⟩
    · exact ⟨hs u hu,gu hu⟩) gdu
  have hR : derivative^[8] R=C (c*40320) := by
    rw [show derivative^[8] R=derivative^[8] p+derivative^[8] (C c*q^2) from
      derivativeSum 8 p _,iterate_derivative_eq_zero (by omega : p.natDegree < 8),
      iterate_derivative_C_mul,evalTop hdq hm]
    norm_num
  rw [show iteratedDeriv 8 g v = iteratedDeriv 8 f v-iteratedDeriv 8 R.eval v from
    iteratedDeriv_sub hf.contDiffAt (smoothEval R 8).contDiffAt,evalJet,hR] at hv'
  simp only [eval_C] at hv'
  have hle := hB v hv
  have hc' : c ≤ B/40320 := by linarith
  have hxv : c*(q.eval x)^2 = f x-p.eval x := div_mul_cancel₀ _ (pow_ne_zero _ hq)
  linarith only [hxv,mul_le_mul_of_nonneg_right hc' (sq_nonneg (q.eval x))]

open GrothendieckLB.Supplement.CQBoundary GaussFour
private abbrev r : ℝ := Real.sqrt 30
private abbrev a : ℝ := (1-outer)/2
private abbrev b : ℝ := (1-GaussFour.inner)/2
private abbrev c : ℝ := (1+GaussFour.inner)/2
private abbrev d : ℝ := (1+outer)/2
private def nodes : Finset ℝ := {a,b,c,d}
private def Q : ℝ[X] := (X-C a)*(X-C d)*((X-C b)*(X-C c))

private theorem r_sq : r^2=30 := Real.sq_sqrt (by norm_num)
private theorem u_sq : outer^2=(15+2*r)/35 := Real.sq_sqrt (by positivity)
private theorem v_sq : GaussFour.inner^2=(15-2*r)/35 := Real.sq_sqrt (by nlinarith only [r_sq,sq_nonneg (r-6)])
private theorem order : 0 < a ∧ a < b ∧ b < c ∧ c < d ∧ d < 1 := by
  have h1 : 0 ≤ outer := Real.sqrt_nonneg _
  have h2 : 0 ≤ GaussFour.inner := Real.sqrt_nonneg _
  have h3 : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have h4 : r < 6 := by nlinarith only [r_sq,sq_nonneg (r-6)]
  have h5 : 0 < GaussFour.inner := Real.sqrt_pos.mpr (show 0 < (15-2*r)/35 by linarith)
  have h6 : GaussFour.inner < outer := Real.sqrt_lt_sqrt (show 0 ≤ (15-2*r)/35 by linarith) (show (15-2*r)/35 < (15+2*r)/35 by linarith)
  have h7 : outer < 1 := by nlinarith only [u_sq,h4,sq_nonneg (outer-1)]
  dsimp only [a,b,c,d]
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

private theorem nodesCard : nodes.card=4 := by
  obtain ⟨_,h1,h2,h3,_⟩ := order
  simp [nodes,h1.ne,h2.ne,h3.ne,(h1.trans h2).ne,(h2.trans h3).ne,(h1.trans (h2.trans h3)).ne]

private theorem nodesMem (x : ℝ) (hx : x ∈ nodes) : x ∈ I := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := order
  simp only [nodes,Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl|rfl|rfl|rfl <;> constructor <;> linarith

private theorem qRoot (x : ℝ) : Q.eval x=0 ↔ x ∈ nodes := by
  simp [Q,nodes,sub_eq_zero]
  tauto

private theorem qDeg : (Q^2).natDegree=8 := by
  have h (v : ℝ) : (X-C v : ℝ[X]) ≠ 0 := X_sub_C_ne_zero v
  simp [Q,natDegree_pow,natDegree_mul,h,mul_ne_zero]

private theorem qMonic : (Q^2).Monic :=
  (((monic_X_sub_C a).mul (monic_X_sub_C d)).mul ((monic_X_sub_C b).mul (monic_X_sub_C c))).pow 2

private theorem qValue (x : ℝ) : Q.eval x=x^4-2*x^3+(9/7)*x^2-(2/7)*x+1/70 := by
  simp only [Q,eval_mul,eval_sub,eval_X,eval_C,a,b,c,d]
  rw [show (x-(1-outer)/2)*(x-(1+outer)/2)=(x-1/2)^2-outer^2/4 by ring,
    show (x-(1-GaussFour.inner)/2)*(x-(1+GaussFour.inner)/2)=(x-1/2)^2-GaussFour.inner^2/4 by ring,u_sq,v_sq]
  linear_combination (-1/4900 : ℝ)*r_sq

private theorem meanCong {f g : ℝ → ℝ} (he : ∀ u ∈ nodes, f u=g u) : mean f=mean g := by
  have ha := he a (by simp [nodes])
  have hb := he b (by simp [nodes])
  have hc := he c (by simp [nodes])
  have hd := he d (by simp [nodes])
  unfold mean
  rw [ha,hb,hc,hd]

private theorem meanPow (n : ℕ) (hn : n < 8) : mean (fun x => x^n)=1/(n+1:ℝ) := by
  have pow4 (x : ℝ) : x^4=(x^2)^2 := by ring
  have pow6 (x : ℝ) : x^6=(x^2)^3 := by ring
  have pow3 (x : ℝ) : x^3=x*x^2 := by ring
  interval_cases n <;> unfold mean <;> change _ = _ <;>
    ring_nf <;> try rfl
  all_goals
    simp only [pow6 outer,pow6 GaussFour.inner,pow4 outer,pow4 GaussFour.inner,u_sq,v_sq]
    ring_nf
  all_goals
    change _ = _
    simp only [pow4 r,pow3 r,r_sq]
    ring_nf

private theorem exactPolynomial (p : ℝ[X]) (hp : p.natDegree ≤ 7) :
    (∫ x in (0:ℝ)..1, p.eval x)=mean p.eval := by
  have he := p.eval_eq_sum_range' (by omega : p.natDegree < 8)
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum (fun i _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  unfold mean
  simp only [←Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hm := meanPow i (Finset.mem_range.mp hi)
  unfold mean at hm
  rw [intervalIntegral.integral_const_mul,integral_pow]
  have hi' : i+1 ≠ 0 := by omega
  simp only [one_pow,zero_pow hi',sub_zero,Nat.cast_add,Nat.cast_one]
  change _=_
  linear_combination (p.coeff i)*hm.symm

private theorem squareMass : (∫ x in (0:ℝ)..1, (Q.eval x)^2)=1/44100 := by
  have h (x : ℝ) : (Q.eval x)^2=(1/4900:ℝ)*x^0 + (-2/245:ℝ)*x^1 + (29/245:ℝ)*x^2 + (-194/245:ℝ)*x^3 + (692/245:ℝ)*x^4 + (-40/7:ℝ)*x^5 + (46/7:ℝ)*x^6 + (-4:ℝ)*x^7 + (1:ℝ)*x^8 := by rw [qValue]; ring
  simp_rw [h]
  repeat' rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)]
  norm_num [intervalIntegral.integral_const_mul,integral_pow,integral_id]
  have h1 : (∫ x in (0:ℝ)..1, 2/245*x)=(1:ℝ)/245 := by
    rw [intervalIntegral.integral_const_mul (2/245) (fun x : ℝ => x),integral_id]
    norm_num
  rw [h1]
  norm_num

private theorem panelRule (f : ℝ → ℝ) (B : ℝ) (hf : ContDiff ℝ 8 f)
    (hB : ∀ x ∈ Set.Icc (0:ℝ) 1, iteratedDeriv 8 f x ≤ B) :
    (∫ x in (0:ℝ)..1, f x) ≤ mean f + B/1778112000 := by
  obtain ⟨p,hd,hn,hx⟩ := majorant nodesCard nodesMem qRoot qDeg qMonic hf hB
  have hp := (smoothEval p 8).continuous
  have hq := (smoothEval Q 8).continuous
  have hm := intervalIntegral.integral_mono_on (μ:=volume) (by norm_num : (0:ℝ) ≤ 1)
    (hf.continuous.intervalIntegrable _ _) ((hp.add (continuous_const.mul (hq.pow 2))).intervalIntegrable _ _) hx
  change (∫ x in (0:ℝ)..1, f x) ≤ (∫ x in (0:ℝ)..1, p.eval x+(B/40320)*(Q.eval x)^2) at hm
  have hc : IntervalIntegrable (fun x : ℝ => (B/40320)*(Q.eval x)^2) volume 0 1 :=
    (continuous_const.mul (hq.pow 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hp.intervalIntegrable _ _) hc,
    intervalIntegral.integral_const_mul,squareMass,exactPolynomial p hd,meanCong hn] at hm
  linarith
end GaussPanelProof

open GaussPanelProof GrothendieckLB.Supplement in
theorem solution :
    ∀ (f : ℝ → ℝ) (B : ℝ), ContDiff ℝ 8 f → (∀ x ∈ Set.Icc (0:ℝ) 1, iteratedDeriv 8 f x ≤ B) →
      (∫ x in (0:ℝ)..1, f x) ≤ CQBoundary.GaussFour.mean f + B/1778112000 := panelRule
