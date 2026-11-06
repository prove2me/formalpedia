-- Prove2me | solution 1 for OAI.SevenEighths.Parameters.exists_high_data
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:13:21.510355+00:00
-- url     : https://prove2.me/submissions/69ba1d4f-69ce-4259-9315-a88d593f6921

import Definitions.Def_OAI_NumberTheory_DirichletL_ParametersCentralBudget
import Definitions.Def_OAI_NumberTheory_DirichletL_ParametersHighData
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.Parameters

private theorem exists_distinct_slot_lengths_aux (L : ℝ) (hL : 0<L) :
    ∃N : ℕ,0<N ∧ ∃ell : Fin N→ℝ,Function.Injective ell ∧
      (∀j,0<ell j ∧ ell j<L) ∧ (∑j,ell j)=1/6 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (1/(3*L)))
  have hN1 : (1:ℝ)<N := (le_max_left _ _).trans_lt hN
  have hNp : 0<(N:ℝ) := by linarith
  have hNnat : 0<N := by exact_mod_cast hNp
  have hNL : 1/(3*L)<(N:ℝ) := (le_max_right _ _).trans_lt hN
  have hsmall : 1/(3*(N:ℝ))<L := by
    have hh := (div_lt_iff₀ (show 0<3*L by positivity)).mp hNL
    apply (div_lt_iff₀ (show 0<3*(N:ℝ) by positivity)).mpr
    nlinarith
  let w : Fin N→ℝ := fun j=>1+(j.val:ℝ)/(N:ℝ)
  let A : ℝ := ∑j,w j
  have hw (j : Fin N) : 1≤w j ∧ w j<2 := by
    have hj : (j.val:ℝ)<N := by exact_mod_cast j.isLt
    have hdiv : (j.val:ℝ)/(N:ℝ)<1 := (div_lt_one hNp).mpr hj
    dsimp only [w]
    constructor
    · linarith [div_nonneg (Nat.cast_nonneg j.val) hNp.le]
    · linarith
  have hA : (N:ℝ)≤A := by
    calc
      _ = ∑_j : Fin N,(1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _=>(hw j).1
  have hAp : 0<A := hNp.trans_le hA
  let ell : Fin N→ℝ := fun j=>w j/(6*A)
  refine ⟨N,hNnat,ell,?_,?_,?_⟩
  · intro j k he
    have hden : 6*A≠0 := by positivity
    have hwjk : w j=w k := (div_left_inj' hden).mp he
    have hjk : (j.val:ℝ)/(N:ℝ)=(k.val:ℝ)/(N:ℝ) := by dsimp [w] at hwjk;linarith
    have he' : (j.val:ℝ)=(k.val:ℝ) := (div_left_inj' hNp.ne').mp hjk
    apply Fin.ext
    exact_mod_cast he'
  · intro j
    constructor
    · exact div_pos (by linarith [(hw j).1]) (by positivity)
    · calc
        ell j < 2/(6*A) := (div_lt_div_iff_of_pos_right (by positivity)).mpr (hw j).2
        _ ≤ 2/(6*(N:ℝ)) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
        _ = 1/(3*(N:ℝ)) := by ring
        _ < L := hsmall
  · dsimp only [ell]
    rw [←Finset.sum_div]
    change A/(6*A)=1/6
    field_simp

private theorem exists_physical_slot_lengths_aux (dmin dmax mesh R : ℝ)
    (hdmin : 0<dmin) (hd : dmin≤dmax) (hm : 0<mesh) (hR : 0<R) :
    ∃N : ℕ,0<N ∧ ∃ell : Fin N→ℝ,
    ∃rmin : ℝ,0<rmin ∧
      Function.Injective ell ∧ (∑j,ell j)=1/6 ∧
      (∀j,0<ell j ∧ dmax*rmin≤ell j ∧ ell j≤dmin*mesh ∧ ell j≤dmin*R) ∧
      (∀d : ℝ,dmin≤d → d≤dmax → ∀j,rmin≤ell j/d ∧ ell j/d≤mesh ∧ ell j/d≤R) := by
  obtain ⟨N,hN,ell,hi,he,hS⟩ := exists_distinct_slot_lengths_aux (dmin*min mesh R)
    (mul_pos hdmin (lt_min hm hR))
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  obtain ⟨j,hj,hjmin⟩ := Finset.exists_min_image Finset.univ ell hne
  have hmax : 0<dmax := hdmin.trans_le hd
  let rmin := ell j/(2*dmax)
  have hr : 0<rmin := div_pos (he j).1 (by positivity)
  have hlo (k : Fin N) : dmax*rmin≤ell k := by
    have hk := hjmin k (Finset.mem_univ k)
    have hiden : dmax*rmin=ell j/2 := by dsimp [rmin]; field_simp
    rw [hiden]
    linarith [(he j).1]
  have hup (k : Fin N) : ell k≤dmin*mesh ∧ ell k≤dmin*R := by
    constructor
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hdmin.le)
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hdmin.le)
  refine ⟨N,hN,ell,rmin,hr,hi,hS,fun k=>⟨(he k).1,hlo k,(hup k).1,(hup k).2⟩,?_⟩
  intro d hd' hd'' k
  have hd0 : 0<d := hdmin.trans_le hd'
  refine ⟨(le_div_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_⟩
  · exact (by nlinarith : rmin*d≤dmax*rmin).trans (hlo k)
  · exact (hup k).1.trans (by nlinarith)
  · exact (hup k).2.trans (by nlinarith)

private theorem exists_detector_scales_aux (R rmin mesh dmin loss ellMin allowance J : ℝ)
    (hR : 0≤R) (hr : 0<rmin) (hm : 0<mesh) (hd : 0<dmin)
    (hl : 0<loss) (hell : 0<ellMin) (ha : 0<allowance) (hJ : 0≤J) :
    ∃ε e κ cost τ : ℝ,
      0<ε ∧ ε≤1/1000 ∧ ε<rmin*mesh ∧ ε≤allowance ∧
      0<e ∧ e<1/1000 ∧ e≤ellMin/4 ∧ e≤allowance ∧
      0<κ ∧ κ≤1 ∧ 0<cost ∧
      12*e*(22+2)+8*κ+2*cost≤ε/2 ∧
      8*e*R+κ≤ε ∧
      0<τ ∧ τ<dmin/2 ∧ 4*τ<dmin*cost ∧
      2*τ*(1+J)≤loss ∧ ∀eps : ℝ,0≤eps → eps≤1 → τ*(2+4*eps)<loss := by
  let ε := min (allowance/2) (min (rmin*mesh/2) (1/2000))
  have hε : 0<ε := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hεa : ε≤allowance/2 := min_le_left _ _
  have hεr : ε≤rmin*mesh/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε1 : ε≤1/2000 := (min_le_right _ _).trans (min_le_right _ _)
  let e := min (ε/(10000*(1+R))) (min (ellMin/4) (allowance/2))
  have he : 0<e := lt_min (div_pos hε (by positivity)) (lt_min (by positivity) (by positivity))
  have heb : e≤ε/(10000*(1+R)) := min_le_left _ _
  have hep : e*(10000*(1+R))≤ε := (le_div_iff₀ (by positivity)).mp heb
  have heR : 0≤e*R := mul_nonneg he.le hR
  have hel : e≤ellMin/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hea : e≤allowance/2 := (min_le_right _ _).trans (min_le_right _ _)
  let κ := ε/1000
  let cost := ε/1000
  have hk : 0<κ := by dsimp [κ]; positivity
  have hc : 0<cost := by dsimp [cost]; positivity
  let τ := min (dmin*cost/16) (min (dmin/4) (loss/(4*(1+J+6))))
  have ht : 0<τ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have htc : τ≤dmin*cost/16 := min_le_left _ _
  have htd : τ≤dmin/4 := (min_le_right _ _).trans (min_le_left _ _)
  have htl : τ≤loss/(4*(1+J+6)) := (min_le_right _ _).trans (min_le_right _ _)
  have htJ : τ*(4*(1+J+6))≤loss := (le_div_iff₀ (by positivity)).mp htl
  have hprod : 0≤τ*J := mul_nonneg ht.le hJ
  refine ⟨ε,e,κ,cost,τ,hε,by linarith,by nlinarith [mul_pos hr hm],by linarith,
    he,by nlinarith,hel,by linarith,hk,?_,hc,?_,?_,ht,by linarith,?_,?_,?_⟩
  · dsimp [κ];linarith
  · dsimp [κ,cost];nlinarith
  · dsimp [κ];nlinarith
  · have hp := mul_pos hd hc;linarith
  · nlinarith
  · intro eps heps heps1
    have hp := mul_le_mul_of_nonneg_left heps1 ht.le
    nlinarith

private theorem exists_central_budget_aux (Δ : ℝ) (hΔ : 0<Δ) :
    ∃ t : ℝ,0<t ∧ t<Δ/4 ∧ t≤1/100000000 ∧
      (0:ℝ)<1/200 ∧ (1/200:ℝ)<1/100 ∧
      (13/16:ℝ)+t+2*t≤7/8 ∧ (7/8:ℝ)≤37/42 ∧ t≤3/16 ∧
      0<Δ-t/4 ∧ Δ-t/4<Δ ∧
      (3/16+Δ-t+t/8+t/8 : ℝ)≤3/16+(Δ-t/4) ∧
      ∀N : ℕ,∃allowance : ℝ,0<allowance ∧
      ∀ε e eps : ℝ,0≤ε → ε≤allowance → 0≤e → e≤allowance →
        0≤eps → eps≤allowance →
        159*ε+t+t+7*t≤1/32 ∧
        (13/16)*(159*ε+t+t+7*t)+2*t+(3/2)*(2*t)+
          (26*e+(N+8)*eps+t+t/6)+(t+t+t)+t≤49/440640 := by
  let t := min (Δ/8) (1/100000000)
  have ht : 0<t := lt_min (by positivity) (by norm_num)
  have htΔ : t≤Δ/8 := min_le_left _ _
  have ht1 : t≤1/100000000 := min_le_right _ _
  refine ⟨t,ht,by linarith,ht1,by norm_num,by norm_num,by linarith,
    by norm_num,by linarith,by linarith,by linarith,by linarith,?_⟩
  intro N
  let allowance := t/((N:ℝ)+2000)
  have hden : 0<(N:ℝ)+2000 := by positivity
  have ha : 0<allowance := div_pos ht hden
  have ha0 : allowance≤t/2000 := div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N])
  have hap : allowance*((N:ℝ)+2000)=t := by dsimp [allowance];field_simp
  refine ⟨allowance,ha,?_⟩
  intro ε e eps hε hεa he hea heps hepsa
  have hεt : 2000*ε≤t := by linarith
  have het : 2000*e≤t := by linarith
  have hepsN : ((N:ℝ)+2000)*eps≤t := by
    have h := mul_le_mul_of_nonneg_left hepsa hden.le
    nlinarith
  have heps8 : ((N:ℝ)+8)*eps≤t := by nlinarith
  constructor <;> nlinarith

private theorem exists_high_data_aux (Δ : ℝ) (hΔ : 0<Δ) : Nonempty (HighData Δ) := by
  obtain ⟨t,ht,htΔ,ht1,_,_,hgeo,hdtop,ht3,hω,hωΔ,hhigh,hallow⟩ := exists_central_budget_aux Δ hΔ
  obtain ⟨N,hN,ell,rmin,hr,hell,hsum,hbounds,_⟩ :=
    exists_physical_slot_lengths_aux (1/200) (7/8) t t (by norm_num) (by norm_num) ht ht
  obtain ⟨allowance,ha,hbud⟩ := hallow N
  let small := min allowance (t/((N:ℝ)+2000))
  have hsmall : 0<small := lt_min ha (div_pos ht (by positivity))
  have hsa : small≤allowance := min_le_left _ _
  have hst : small≤t/((N:ℝ)+2000) := min_le_right _ _
  have hst0 : small≤t/2000 := hst.trans
    (div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N]))
  let ellMin := (7/8:ℝ)*rmin
  have hmin : 0<ellMin := mul_pos (by norm_num) hr
  obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
    hdet,hphase,_,_,_,_,_⟩ :=
    exists_detector_scales_aux t rmin t (1/200) t ellMin small 0
      ht.le hr ht (by norm_num) ht hmin hsmall (by norm_num)
  let eps := small/2
  have heps : 0<eps := by dsimp [eps];positivity
  have hepss : eps≤small := by dsimp [eps];linarith only [hsmall]
  have heps1 : eps≤1 := by linarith only [hepss, hst0, ht1]
  have hbud' := hbud ε e eps hε.le (hεa.trans hsa) he.le (hea.trans hsa)
    heps.le (hepss.trans hsa)
  have heN : ((N:ℝ)+2000)*eps≤t := by
    have h := (le_div_iff₀ (show 0<(N:ℝ)+2000 by positivity)).mp (hepss.trans hst)
    simpa only [mul_comm] using h
  have he8 : ((N:ℝ)+8)*eps≤t := by nlinarith only [heN, heps.le]
  have het : 2000*e≤t := by linarith only [hea, hst0]
  let sigma := min (t/2) (ellMin/4)
  have hs : 0<sigma := lt_min (by positivity) (by positivity)
  have hst2 : sigma≤t/2 := min_le_left _ _
  have hsell : sigma≤ellMin/4 := min_le_right _ _
  refine ⟨{
    t:=t,N:=N,ell:=ell,rmin:=rmin,ε:=ε,e:=e,κ:=κ,cost:=cost,eps:=eps,sigma:=sigma
    t_pos:=ht,t_delta:=htΔ,t_small:=ht1,slots_pos:=hN,slots_injective:=hell,slots_sum:=hsum
    slots_bounds:=fun j=>⟨(hbounds j).1,(hbounds j).2.1,(hbounds j).2.2.1⟩
    rmin_pos:=hr,epsilon_pos:=hε,epsilon_small:=hε1,epsilon_gap:=hεgap
    e_pos:=he,e_small:=he1,kappa_pos:=hκ,kappa_small:=hκ1,cost_pos:=hcost
    eps_pos:=heps,eps_small:=heps1,sigma_pos:=hs,detector_budget:=by linarith only [hdet]
    phase_budget:=hphase,count_budget:=hbud'.1,central_budget:=hbud'.2
    geometric_budget:=by linarith only [hst2, het, ht1]
    principal_budget:=by linarith only [hst2, ht1]
    window_budget:=by change sigma+e≤(7/8)*ellMin;linarith only [hsell, heell, hmin]
    floor_budget:=by linarith only [hst2, het, he8, ht1]
    high_saving:=by linarith only [hst2, ht]
    height_choice:=?_ }⟩
  intro J hJ
  let τ := min ((1/200:ℝ)*cost/16) (min (1/800) (t/(4*(J+7))))
  have htau : 0<τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have hτc : τ≤(1/200:ℝ)*cost/16 := min_le_left _ _
  have hτd : τ≤1/800 := (min_le_right _ _).trans (min_le_left _ _)
  have hτt : τ≤t/(4*(J+7)) := (min_le_right _ _).trans (min_le_right _ _)
  have hτJ : τ*(4*(J+7))≤t := (le_div_iff₀ (by positivity)).mp hτt
  have hprod : 0≤τ*J := mul_nonneg htau.le hJ
  have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
  refine ⟨τ,htau,by linarith only [hτd],by linarith only [hτc, hcost],
      by nlinarith only [hτJ, hprod, htau],by nlinarith only [hτJ, hprod, htau],
      by nlinarith only [hτJ, hprod, hprodeps, htau]⟩

theorem solution (Δ : ℝ) (hΔ : 0<Δ) : Nonempty (HighData Δ) := by
  exact exists_high_data_aux Δ hΔ
