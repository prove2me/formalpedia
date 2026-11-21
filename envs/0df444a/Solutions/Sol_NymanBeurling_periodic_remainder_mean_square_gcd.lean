-- Prove2me | solution 1 for NymanBeurling.periodic_remainder_mean_square_gcd
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:53:12.426392+00:00
-- url     : https://prove2.me/submissions/8cc15540-3f19-45b8-9e2a-418fcfb9670e

import Mathlib

open Finset Function Filter Topology
noncomputable section

private def center (d m : ℕ) : ℝ := 2*((m%d:ℕ):ℝ) - d + 1
private def av (P : ℕ) (f : ℕ→ℝ) := (∑ m ∈ range P,f m)/(P:ℝ)

private theorem blocks (k d : ℕ) (f : ℕ→ℝ) : (∑ i ∈ range (k*d),f i)=
    ∑ j ∈ range k,∑ r ∈ range d, f (j*d+r) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.succ_mul,sum_range_add,ih,sum_range_succ]

private theorem block_period (k d : ℕ) (f : ℕ→ℝ) (hf : Periodic f d) :
    (∑ i ∈ range (k*d),f i)=(k:ℝ)*(∑ r ∈ range d,f r) := by
  rw [blocks]
  have he (j r : ℕ) : f (j*d+r)=f r := by
    rw [Nat.add_comm]; exact hf.nat_mul j r
  simp [he]

private theorem av_period {P Q : ℕ} (hp : 0<P) (hq : 0<Q) (f : ℕ→ℝ)
    (hP : Periodic f P) (hQ : Periodic f Q) : av P f=av Q f := by
  have ht := block_period Q P f hP
  rw [Nat.mul_comm,block_period P Q f hQ] at ht
  apply (div_eq_div_iff (by exact_mod_cast hp.ne' : (P:ℝ)≠0)
    (by exact_mod_cast hq.ne' : (Q:ℝ)≠0)).mpr
  linarith [ht]

private theorem sum_moms (d : ℕ) :
    2*(∑ r ∈ range d,(r:ℝ))=(d:ℝ)*(d-1) ∧
    6*(∑ r ∈ range d,(r:ℝ)^2)=(d:ℝ)*(d-1)*(2*d-1) := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    simp only [sum_range_succ,Nat.cast_succ]
    constructor <;> nlinarith [ih.1,ih.2]

private theorem cen_first (d : ℕ) : (∑ m ∈ range d,center d m)=0 := by
  have he (r : ℕ) (hr : r∈range d) : center d r=2*(r:ℝ)-(d-1:ℝ) := by
    rw [center,Nat.mod_eq_of_lt (mem_range.mp hr)];ring
  rw [sum_congr rfl he,sum_sub_distrib,←mul_sum,sum_const,card_range,nsmul_eq_mul]
  linarith [(sum_moms d).1]

private theorem cen_second (d : ℕ) :
    3*(∑ m ∈ range d,(center d m)^2)=(d:ℝ)*(d^2-1) := by
  have he (r : ℕ) (hr : r∈range d) : (center d r)^2=
      4*(r:ℝ)^2-(4*((d:ℝ)-1))*r+((d:ℝ)-1)^2 := by
    rw [center,Nat.mod_eq_of_lt (mem_range.mp hr)];ring
  rw [sum_congr rfl he,sum_add_distrib,sum_sub_distrib,←mul_sum,←mul_sum,sum_const,card_range,nsmul_eq_mul]
  nlinarith [(sum_moms d).2,congrArg (fun x : ℝ => ((d:ℝ)-1)*x) (sum_moms d).1]

private theorem center_per {d P : ℕ} (h : d∣P) : Periodic (center d) P := by
  intro x
  simp [center,Nat.add_mod,Nat.mod_eq_zero_of_dvd h]

private def cEquiv {d e : ℕ} (hd : 0<d) (he : 0<e) (h : d.Coprime e) :
    Fin (d*e) ≃ Fin d × Fin e where
  toFun x := (⟨x.val%d,Nat.mod_lt _ hd⟩,⟨x.val%e,Nat.mod_lt _ he⟩)
  invFun x := ⟨Nat.chineseRemainder h x.1.val x.2.val,Nat.chineseRemainder_lt_mul h _ _ hd.ne' he.ne'⟩
  left_inv x := by
    apply Fin.ext
    let y := Nat.chineseRemainder h (x.val%d) (x.val%e)
    have h1 : y.val ≡ x.val [MOD d] := by simpa [Nat.ModEq] using y.property.1
    have h2 : y.val ≡ x.val [MOD e] := by simpa [Nat.ModEq] using y.property.2
    have hc := (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨h1,h2⟩
    have hy : y.val < d*e := Nat.chineseRemainder_lt_mul h _ _ hd.ne' he.ne'
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt x.isLt,Nat.mod_eq_of_lt hy] using hc
  right_inv x := by
    apply Prod.ext <;> apply Fin.ext
    · exact Eq.trans (show _ % d = x.1.val % d from (Nat.chineseRemainder h x.1.val x.2.val).property.1) (Nat.mod_eq_of_lt x.1.isLt)
    · exact Eq.trans (show _ % e = x.2.val % e from (Nat.chineseRemainder h x.1.val x.2.val).property.2) (Nat.mod_eq_of_lt x.2.isLt)

private theorem coprime_cen {d e : ℕ} (hd : 0<d) (he : 0<e) (h : d.Coprime e) :
    (∑ m ∈ range (d*e), center d m*center e m)=0 := by
  let E := cEquiv hd he h
  let F (x : Fin d × Fin e) := center d x.1.val * center e x.2.val
  have heq (x : Fin (d*e)) : F (E x)=center d x.val*center e x.val := by simp [F,E,cEquiv,center]
  calc _ = ∑ x : Fin (d*e), F (E x) := by rw [←Fin.sum_univ_eq_sum_range];simp_rw [heq]
       _ = ∑ x : Fin d × Fin e, F x := E.sum_comp F
       _ = 0 := by
         rw [Fintype.sum_prod_type]
         simp only [F,←mul_sum,Fin.sum_univ_eq_sum_range,cen_first,mul_zero,sum_const_zero]

private theorem cen_decompose {g d r : ℕ} (hg : 0<g) (hr : r<g) (k : ℕ) :
    center (g*d) (k*g+r)=g*center d k+center g r := by
  have hmod : (k*g+r)%(g*d)=(k%d)*g+r := by
    have he : k*g+r = (k%d)*g+r+(g*d)*(k/d) := by
      have hh:=congrArg (fun n : ℕ => n*g) (Nat.mod_add_div k d)
      nlinarith only [hh]
    by_cases hd : d=0
    · subst d;simp
    · rw [he,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt]
      have hk := Nat.mod_lt k (Nat.pos_of_ne_zero hd)
      nlinarith only [Nat.mul_le_mul_right g (Nat.succ_le_of_lt hk),hr]
  rw [center,hmod,center,center,Nat.mod_eq_of_lt hr]
  push_cast;ring

private theorem gcd_scaled {g d e : ℕ} (hg : 0<g) (hd : 0<d) (he : 0<e) (h : d.Coprime e) :
    3*(∑ m ∈ range ((d*e)*g),center (g*d) m*center (g*e) m)=
      ((d*e:ℕ):ℝ)*g*((g:ℝ)^2-1) := by
  rw [blocks,mul_sum]
  have hinner (k : ℕ) : 3*(∑ r ∈ range g,center (g*d) (k*g+r)*center (g*e) (k*g+r))=
      (3*(g:ℝ)^3)*(center d k*center e k)+(g:ℝ)*(g^2-1) := by
    have heq (r : ℕ) (hr : r∈range g) :
        center (g*d) (k*g+r)*center (g*e) (k*g+r) =
        ((g:ℝ)^2*(center d k*center e k)) +
          ((g:ℝ)*(center d k+center e k))*center g r + (center g r)^2 := by
      simp only [cen_decompose hg (mem_range.mp hr)]; ring
    rw [sum_congr rfl heq,sum_add_distrib,sum_add_distrib,
      ←mul_sum (range g) (fun r => center g r),cen_first,
      sum_const,card_range,nsmul_eq_mul,mul_zero,add_zero]
    nlinarith [cen_second g]
  simp only [hinner,sum_add_distrib,←mul_sum,coprime_cen hd he h,mul_zero,zero_add,sum_const,card_range,nsmul_eq_mul]
  ring

private theorem av_center {P d : ℕ} (hp : 0<P) (hd : 0<d) (h : d∣P) :
    av P (center d)=0 := by
  rw [av_period hp hd _ (center_per h) (center_per (dvd_refl d)),av,cen_first,zero_div]

private theorem av_cov {P d e : ℕ} (hp : 0<P) (hd : 0<d) (he : 0<e) (hdP : d∣P) (heP : e∣P) :
    av P (fun m => center d m*center e m)=((d.gcd e:ℝ)^2-1)/3 := by
  let g := d.gcd e
  let a := d/g
  let b := e/g
  have hg : 0<g := Nat.gcd_pos_of_pos_left e hd
  have hda : g*a=d := Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)
  have heb : g*b=e := Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)
  have ha : 0<a := Nat.pos_of_ne_zero (fun hj => by simp [hj] at hda;omega)
  have hb : 0<b := Nat.pos_of_ne_zero (fun hj => by simp [hj] at heb;omega)
  have cop : a.Coprime b := Nat.coprime_div_gcd_div_gcd hg
  let Q := (a*b)*g
  have hq : 0<Q := Nat.mul_pos (Nat.mul_pos ha hb) hg
  have hdQ : d∣Q := ⟨b,by dsimp only [Q]; rw [←hda];ring⟩
  have heQ : e∣Q := ⟨a,by dsimp only [Q];rw [←heb];ring⟩
  rw [av_period hp hq (fun m => center d m*center e m) ((center_per hdP).mul (center_per heP)) ((center_per hdQ).mul (center_per heQ))]
  have h := gcd_scaled hg ha hb cop
  rw [hda,heb] at h
  unfold av; dsimp only [Q]
  apply (div_eq_div_iff (by exact_mod_cast hq.ne' : (((a*b)*g:ℕ):ℝ)≠0) (by norm_num)).mpr
  rw [Nat.cast_mul];dsimp only [g] at h ⊢;linarith [h]

private def Rval (S : Finset ℕ) (c : ℕ→ℝ) (m : ℕ) :=
  1-∑ d ∈ S,c d*((m%d:ℕ):ℝ)/(d:ℝ)
private def meanR (S : Finset ℕ) (c : ℕ→ℝ) :=
  1-∑ d ∈ S,c d*((d:ℝ)-1)/(2*d)
private def gcdMean (S : Finset ℕ) (c : ℕ→ℝ) := (meanR S c)^2+
  ∑ d ∈ S, ∑ e ∈ S,c d*c e*((d.gcd e:ℝ)^2-1)/(12*d*e)

private theorem av_add (P : ℕ) (f g : ℕ→ℝ) :
    av P (fun m => f m+g m)=av P f+av P g := by simp [av,sum_add_distrib,add_div]
private theorem av_sub (P : ℕ) (f g : ℕ→ℝ) :
    av P (fun m => f m-g m)=av P f-av P g := by simp [av,sum_sub_distrib,sub_div]
private theorem av_const {P : ℕ} (hp : 0<P) (r : ℝ) : av P (fun _ =>r)=r := by
  have hn : (P:ℝ)≠0 := by exact_mod_cast hp.ne'
  simp [av,nsmul_eq_mul,hn]
private theorem av_mul' (P : ℕ) (r : ℝ) (f : ℕ→ℝ) : av P (fun m => r*f m)=r*av P f := by
  simp [av,←mul_sum,mul_div_assoc]
private theorem av_sum {ι : Type*} (P : ℕ) (s : Finset ι) (f : ι→ℕ→ℝ) :
    av P (fun m => ∑ i ∈ s,f i m)=∑ i ∈ s,av P (f i) := by
  unfold av;rw [sum_comm,Finset.sum_div]

private theorem gcd_avg (P : ℕ) (hp : 0<P) (S : Finset ℕ) (c : ℕ→ℝ)
    (hpos : ∀ d∈S,0<d) (hper : ∀ d∈S,d∣P) :
    av P (fun m => (Rval S c m)^2)=gcdMean S c := by
  let D (d : ℕ) := c d/(2*d)
  let X (m : ℕ) := ∑ d ∈ S,D d*center d m
  have hx : av P X=0 := by
    unfold X;rw [av_sum]
    apply sum_eq_zero;intro d hd
    rw [av_mul',av_center hp (hpos d hd) (hper d hd),mul_zero]
  have hform (m : ℕ) : Rval S c m=meanR S c-X m := by
    unfold Rval meanR X
    rw [sub_sub,←sum_add_distrib]
    congr 1;apply sum_congr rfl
    intro d hd;dsimp [D,center]
    field_simp [show (d:ℝ)≠0 by exact_mod_cast (hpos d hd).ne'];ring
  have hsecond : av P (fun m => X m*X m)=
      ∑ d ∈ S,∑ e ∈ S, c d*c e*((d.gcd e:ℝ)^2-1)/(12*d*e) := by
    have he (m : ℕ) : X m*X m=∑ d ∈ S,∑ e ∈ S,
        (D d*D e)*(center d m*center e m) := by
      simp only [X,Finset.sum_mul,Finset.mul_sum];congr! 2 with d hd e he;ring
    simp_rw [he]
    rw [av_sum]
    apply sum_congr rfl; intro d hd
    rw [av_sum]
    apply sum_congr rfl;intro e he
    rw [av_mul',av_cov hp (hpos d hd) (hpos e he) (hper d hd) (hper e he)]
    dsimp [D];ring
  have hs (m : ℕ) : (Rval S c m)^2=(meanR S c)^2- (2*meanR S c)*X m + X m*X m := by
    rw [hform];ring
  simp_rw [hs]
  rw [av_add,av_sub,av_const hp,av_mul',hx,mul_zero,sub_zero,hsecond,gcdMean]

private def wgt (n : ℕ) := 1/((n+1:ℝ)*(n+2:ℝ))
private theorem wgt_pos (n : ℕ) : 0<wgt n := by dsimp [wgt];positivity
private theorem wgt_anti : Antitone wgt := by
  intro a b h
  apply one_div_le_one_div_of_le (by positivity)
  gcongr <;> exact_mod_cast h
private theorem wgt_telescope (H n : ℕ) :
    wgt (H+n)=1/((H+n:ℕ)+1:ℝ)-1/((H+n+1:ℕ)+1:ℝ) := by
  dsimp [wgt];push_cast;field_simp;ring
private theorem wgt_sum (H : ℕ) : HasSum (fun n=>wgt (H+n)) (1/(H+1:ℝ)) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => (wgt_pos _).le) _).mpr
  have hh (n : ℕ) : ∑ j ∈ range n,wgt (H+j)=1/(H+1:ℝ)-1/((H+n:ℕ)+1:ℝ) := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ,ih,wgt_telescope];ring
  simp_rw [hh]
  have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).comp (tendsto_add_atTop_nat H)
  simpa only [comp_def,add_zero,sub_zero,Nat.add_comm H] using
    (tendsto_const_nhds (x:=1/(H+1:ℝ))).sub ht

private theorem per_bd {P : ℕ} (hp : 0<P) {f : ℕ→ℝ} (hf : Periodic f P) :
    ∃ B : ℝ,0≤B ∧ ∀ n,|f n|≤B := by
  refine ⟨∑ r ∈ range P,|f r|,sum_nonneg fun _ _ => abs_nonneg _,fun n => ?_⟩
  have h : f n=f (n%P) := by
    have hx := hf.nat_mul (n/P) (n%P)
    change f (n%P+(n/P)*P)=f (n%P) at hx
    rw [Nat.mul_comm (n/P),Nat.mod_add_div] at hx
    exact hx
  rw [h]
  exact single_le_sum (f:=fun r => |f r|) (fun r _ => abs_nonneg _) (mem_range.mpr (Nat.mod_lt _ hp))

private theorem centered_prefixes {P : ℕ} (hp : 0<P) {f : ℕ→ℝ} (hf : Periodic f P) :
    ∃ B : ℝ, 0≤B ∧ ∀ (H n : ℕ), |∑ i ∈ range n,(f (H+i)-av P f)|≤B := by
  let g (m : ℕ) := f m-av P f
  let A (n : ℕ) := ∑ i ∈ range n,g i
  have h0 : A P=0 := by
    dsimp [A,g,av];rw [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul]
    field_simp [show (P:ℝ)≠0 by exact_mod_cast hp.ne'];ring
  have ha : Periodic A P := by
    intro x
    rw [Nat.add_comm];dsimp [A];change (∑ i ∈ range P,g i)=0 at h0
    rw [sum_range_add,h0,zero_add]
    apply sum_congr rfl;intro i _
    simpa only [g,Nat.add_comm P i] using congrArg (fun t => t-av P f) (hf i)
  obtain ⟨C,hC,hb⟩ := per_bd hp ha
  refine ⟨2*C,by positivity,fun H n => ?_⟩
  have he : ∑ i ∈ range n,g (H+i)=A (H+n)-A H := by dsimp [A];rw [sum_range_add];ring
  change |∑ i ∈ range n,g (H+i)|≤_
  rw [he]
  exact (abs_sub _ _).trans (by linarith [hb (H+n),hb H])

private theorem abel_bound (z v : ℕ→ℝ) (hv : Antitone v) (hpos : ∀ n,0≤v n)
    (B : ℝ) (hb : 0≤B) (hZ : ∀ n,|∑ i ∈ range n,z i|≤B) (N : ℕ) :
    |∑ i ∈ range N,v i*z i| ≤ B*v 0 := by
  cases N with
  | zero => simp [mul_nonneg hb (hpos _)]
  | succ n =>
    have h := sum_range_by_parts v z (n+1)
    simp only [smul_eq_mul,Nat.add_sub_cancel] at h
    rw [h]
    apply (abs_sub _ _).trans
    have hh (i : ℕ) : |v (i+1)-v i|=v i-v (i+1) := abs_of_nonpos (sub_nonpos.mpr (hv (Nat.le_succ _))) |>.trans (neg_sub _ _)
    have h1 : |v n*(∑ i ∈ range (n+1), z i)| ≤ v n*B := by
      rw [abs_mul,abs_of_nonneg (hpos _)];exact mul_le_mul_of_nonneg_left (hZ _) (hpos _)
    have h2 : |∑ i ∈ range n,(v (i+1)-v i)*(∑ j ∈ range (i+1),z j)| ≤
        B*(v 0-v n) := by
      calc _ ≤ ∑ i ∈ range n,|(v (i+1)-v i)*(∑ j ∈ range (i+1),z j)| := abs_sum_le_sum_abs _ _
           _ ≤ ∑ i ∈ range n,(v i-v (i+1))*B := by
             apply sum_le_sum;intro i hi
             rw [abs_mul,hh];exact mul_le_mul_of_nonneg_left (hZ _) (sub_nonneg.mpr (hv (Nat.le_succ _)))
           _ = _ := by rw [←sum_mul,sum_range_sub'];ring
    linarith

private theorem periodic_tail {P : ℕ} (hp : 0<P) {f : ℕ→ℝ} (hf : Periodic f P) :
    Tendsto (fun H : ℕ => (H+1:ℝ)*∑' j : ℕ,wgt (H+j)*f (H+j+1)) atTop (𝓝 (av P f)) := by
  obtain ⟨B,hB,hpre⟩ := centered_prefixes hp hf
  obtain ⟨C,hC,hb⟩ := per_bd hp hf
  have hsum (H : ℕ) : Summable (fun j => wgt (H+j)*f (H+j+1)) :=
    Summable.of_norm_bounded ((wgt_sum H).summable.mul_right C) (fun j => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (wgt_pos _)];exact mul_le_mul_of_nonneg_left (hb _) (wgt_pos _).le)
  have herr (H : ℕ) : |(∑' j : ℕ,wgt (H+j)*f (H+j+1)) - av P f/(H+1:ℝ)|≤B*wgt H := by
    have hs := (hsum H).hasSum.sub ((wgt_sum H).mul_right (av P f))
    have ht := hs.tendsto_sum_nat.abs
    rw [show (1/(H+1:ℝ))*(av P f) = av P f/(H+1:ℝ) by ring] at ht
    apply le_of_tendsto ht
    filter_upwards with n
    simp only [←mul_sub]
    have hz := abel_bound (fun j => f (H+j+1)-av P f) (fun j => wgt (H+j))
      (fun a b h => wgt_anti (Nat.add_le_add_left h _)) (fun _ => (wgt_pos _).le) B hB
      (fun j => by simpa only [Nat.add_right_comm H _ 1] using hpre (H+1) j) n
    simpa only [Nat.add_zero] using hz
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun H : ℕ => B/((H:ℝ)+2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  apply squeeze_zero (fun _ => norm_nonneg _) _ hlim
  intro H
  have hh : 0<(H+1:ℝ) := by positivity
  have he := mul_le_mul_of_nonneg_left (herr H) hh.le
  have hmul (x : ℝ) : (H+1:ℝ)*|x|=|(H+1:ℝ)*x| := by rw [abs_mul,abs_of_pos hh]
  rw [hmul] at he
  have h1 (x : ℝ) : (H+1:ℝ)*(x-av P f/(H+1:ℝ))=(H+1:ℝ)*x-av P f := by field_simp
  have h2 : (H+1:ℝ)*(B*wgt H)=B/((H:ℝ)+2) := by dsimp [wgt];field_simp
  rw [h1,h2] at he
  exact he

theorem solution (S : Finset ℕ) (c : ℕ→ℝ) (P : ℕ) (hP : 0<P)
    (hd : ∀ d∈S,0<d) (hper : ∀ d∈S,d∣P) :
    let R := fun m : ℕ => 1-∑ d ∈ S,c d*((m%d:ℕ):ℝ)/(d:ℝ)
    let M := (1-∑ d ∈ S,c d*((d:ℝ)-1)/(2*d))^2+
      ∑ d ∈ S,∑ e ∈ S,c d*c e*((d.gcd e:ℝ)^2-1)/(12*d*e)
    (∑ m ∈ Finset.range P,(R m)^2)/(P:ℝ)=M ∧
      Tendsto (fun H : ℕ => (H+1:ℝ)*∑' j : ℕ,
        (R (H+j+1))^2/(((H+j:ℕ)+1:ℝ)*((H+j:ℕ)+2:ℝ))) atTop (𝓝 M) := by
  dsimp only
  have fper : Periodic (fun n => (Rval S c n)^2) P := by
    intro n
    simp only [Rval]
    congr 2
    apply sum_congr rfl;intro d h
    simp [Nat.add_mod,Nat.mod_eq_zero_of_dvd (hper d h)]
  have hh := gcd_avg P hP S c hd hper
  refine ⟨hh,?_⟩
  have ht := periodic_tail hP fper
  rw [hh] at ht
  simpa only [wgt,one_div,div_eq_inv_mul,mul_one,Rval,gcdMean,meanR] using ht
