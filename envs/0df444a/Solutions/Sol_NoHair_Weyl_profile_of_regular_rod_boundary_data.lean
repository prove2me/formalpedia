-- Prove2me | solution 1 for NoHair.Weyl.profile_of_regular_rod_boundary_data
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:41:13.462808+00:00
-- url     : https://prove2.me/submissions/8e1e8bf8-1581-429b-a0c9-5cc1c1082d73

import Definitions.Def_NoHair_regularRodBoundaryData
import Theorems.Thm_NoHair_Weyl_prolate_coordinate_differentials
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

open NoHair NoHair.Weyl Set Filter MeasureTheory
open scoped Topology

private def clip (a b t : ℝ) := max a (min b t)
private lemma clip_mem {a b : ℝ} (h : a ≤ b) (t : ℝ) : clip a b t ∈ Icc a b :=
  ⟨le_max_left _ _,max_le h (min_le_left _ _)⟩
private lemma clip_eq {a b t : ℝ} (h : t ∈ Icc a b) : clip a b t = t := by
  simp [clip,min_eq_right h.2,max_eq_right h.1]

private lemma line_mem {d c t : ℝ} (hd : d ∈ Icc (-1:ℝ) 1) (hc : c ∈ Icc (-1:ℝ) 1)
    (ht : t ∈ Icc (0:ℝ) 1) : d+(c-d)*t ∈ Icc (-1:ℝ) 1 := by
  constructor
  · nlinarith only [mul_nonneg (sub_nonneg.mpr hd.1) (sub_nonneg.mpr ht.2),
                     mul_nonneg (sub_nonneg.mpr hc.1) ht.1]
  · nlinarith only [mul_nonneg (sub_nonneg.mpr hd.2) (sub_nonneg.mpr ht.2),
                     mul_nonneg (sub_nonneg.mpr hc.2) ht.1]

private def path (L d : ℝ) (z : OrbitPoint) (t : ℝ) : OrbitPoint :=
  (clip 0 L z.1,d+(clip (-1) 1 z.2-d)*clip 0 1 t)

private def meanSlope (df : OrbitPoint → ℝ) (L d : ℝ) (z : OrbitPoint) :=
  ∫ t in (0:ℝ)..1, df (path L d z t)

private lemma path_cont {df : OrbitPoint → ℝ} {L d : ℝ} (hL : 0 ≤ L)
    (hd : d ∈ Icc (-1:ℝ) 1) (hdf : ContinuousOn df (Icc 0 L ×ˢ Icc (-1:ℝ) 1)) :
    Continuous (fun v : OrbitPoint × ℝ => df (path L d v.1 v.2)) := by
  apply hdf.comp_continuous
  · unfold path clip
    fun_prop
  · intro v
    exact ⟨clip_mem hL _,line_mem hd (clip_mem (by norm_num) _) (clip_mem zero_le_one _)⟩

private lemma mean_cont {df : OrbitPoint → ℝ} {L d : ℝ} (hL : 0 ≤ L)
    (hd : d ∈ Icc (-1:ℝ) 1) (hdf : ContinuousOn df (Icc 0 L ×ˢ Icc (-1:ℝ) 1)) :
    Continuous (meanSlope df L d) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f:=fun z t => df (path L d z t)) (path_cont hL hd hdf) 0 1

private lemma mean_ftc {f df : OrbitPoint → ℝ} {L d q c : ℝ} (hL : 0 ≤ L)
    (hd : d ∈ Icc (-1:ℝ) 1) (hq : q ∈ Icc 0 L) (hc : c ∈ Icc (-1:ℝ) 1)
    (hdf : ContinuousOn df (Icc 0 L ×ˢ Icc (-1:ℝ) 1))
    (hf : ∀ z ∈ Icc 0 L ×ˢ Icc (-1:ℝ) 1, HasDerivAt (fun s => f (z.1,s)) (df z) z.2) :
    meanSlope df L d (q,c)*(c-d) = f (q,c)-f (q,d) := by
  let g := fun t => f (q,d+(c-d)*t)
  let gp := fun t => df (path L d (q,c) t)*(c-d)
  have hg (t : ℝ) (ht : t ∈ uIcc (0:ℝ) 1) : HasDerivAt g (gp t) t := by
    rw [uIcc_of_le zero_le_one] at ht
    have e : path L d (q,c) t = (q,d+(c-d)*t) := by simp [path,clip_eq hq,clip_eq hc,clip_eq ht]
    have v : HasDerivAt (fun t : ℝ => d+(c-d)*t) (c-d) t := by
      simpa only [id_eq,mul_one] using (((hasDerivAt_id t).const_mul (c-d)).const_add d)
    dsimp only [gp]
    rw [e]
    exact (hf (q,d+(c-d)*t) ⟨hq,line_mem hd hc ht⟩).comp t v
  have hp : Continuous gp :=
    ((path_cont hL hd hdf).comp (continuous_const.prodMk continuous_id)).mul continuous_const
  have e := intervalIntegral.integral_eq_sub_of_hasDerivAt hg (hp.intervalIntegrable 0 1)
  simpa [g,gp,meanSlope,intervalIntegral.integral_mul_const] using e

private lemma mean_pole {df : OrbitPoint → ℝ} {L q d : ℝ} (hq : q ∈ Icc 0 L)
    (hd : d ∈ Icc (-1:ℝ) 1) : meanSlope df L d (q,d) = df (q,d) := by
  simp [meanSlope,path,clip_eq hq,clip_eq hd]

private lemma divide_poles {f df : OrbitPoint → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hdf : ContinuousOn df (Icc 0 L ×ˢ Icc (-1:ℝ) 1))
    (hf : ∀ z ∈ Icc 0 L ×ˢ Icc (-1:ℝ) 1, HasDerivAt (fun s => f (z.1,s)) (df z) z.2)
    (hz : ∀ q ∈ Icc 0 L, f (q,-1)=0 ∧ f (q,1)=0) :
    ∃ A : OrbitPoint → ℝ, Continuous A ∧ ∀ q ∈ Icc 0 L,
      (∀ c ∈ Icc (-1:ℝ) 1, (1-c^2)*A (q,c)=f (q,c)) ∧
      A (q,-1)=df (q,-1)/2 ∧ A (q,1)= -df (q,1)/2 := by
  have hl : (-1:ℝ) ∈ Icc (-1:ℝ) 1 := by constructor <;> norm_num
  have hr : (1:ℝ) ∈ Icc (-1:ℝ) 1 := by constructor <;> norm_num
  let Lm := meanSlope df L (-1)
  let Rm := meanSlope df L 1
  refine ⟨fun z => (Lm z-Rm z)/2,((mean_cont hL hl hdf).sub (mean_cont hL hr hdf)).div_const _,?_⟩
  intro q hq
  have leq {c : ℝ} (hc : c ∈ Icc (-1:ℝ) 1) : Lm (q,c)*(c-(-1))=f (q,c) := by
    simpa [Lm,(hz q hq).1] using mean_ftc hL hl hq hc hdf hf
  have req {c : ℝ} (hc : c ∈ Icc (-1:ℝ) 1) : Rm (q,c)*(c-1)=f (q,c) := by
    simpa [Rm,(hz q hq).2] using mean_ftc hL hr hq hc hdf hf
  refine ⟨?_,?_,?_⟩
  · intro c hc
    dsimp only
    linear_combination ((1-c)/2)*(leq hc) + ((1+c)/2)*(req hc)
  · have E := req hl
    rw [(hz q hq).1] at E
    change (meanSlope df L (-1) (q,-1)-Rm (q,-1))/2=_
    rw [mean_pole hq hl]
    linarith only [E]
  · have E := leq hr
    rw [(hz q hq).2] at E
    change (Lm (q,1)-meanSlope df L 1 (q,1))/2=_
    rw [mean_pole hq hr]
    linarith only [E]

theorem solution (u : ErnstPotentials) (m ℓ J : ℝ) (hm : 0 < m) (hl : 0 ≤ ℓ)
    (h : RegularRodBoundaryData u m ℓ J) : HasProfileEstimates u (rodBoundaryProfile m ℓ J) := by
  let L := 1/(m+ℓ)
  let K := Icc 0 L ×ˢ Icc (-1:ℝ) 1
  have hmℓ : 0 < m+ℓ := add_pos_of_pos_of_nonneg hm hl
  have hL : 0 ≤ L := (one_div_pos.mpr hmℓ).le
  obtain ⟨A,cA,hA⟩ := divide_poles hL h.normSlope_continuous h.norm_derivative
    (fun q hq => ⟨(h.poles q hq).1,(h.poles q hq).2.1⟩)
  obtain ⟨V,cV,hV⟩ := divide_poles hL h.twistSlope_continuous h.twist_derivative
    (fun q hq => ⟨(h.poles q hq).2.2.1,(h.poles q hq).2.2.2.1⟩)
  have hs {c : ℝ} (hc : c ∈ Ioo (-1:ℝ) 1) : 0 < 1-c^2 := by
    nlinarith only [mul_pos (sub_pos.mpr hc.2) (sub_pos.mpr hc.1)]
  have hpos (z : OrbitPoint) (hz : z ∈ K) : 0 < A z := by
    obtain ⟨q,c⟩ := z
    obtain ⟨hq,hc⟩ := hz
    change q ∈ Icc 0 L at hq
    change c ∈ Icc (-1:ℝ) 1 at hc
    rcases eq_or_lt_of_le hc.1 with e|lo
    · subst c; rw [(hA q hq).2.1]; exact half_pos (h.poles q hq).2.2.2.2.1
    rcases eq_or_lt_of_le hc.2 with e|hi
    · subst c; rw [(hA q hq).2.2]; exact half_pos (neg_pos.mpr (h.poles q hq).2.2.2.2.2)
    have e := (hA q hq).1 c hc
    exact pos_of_mul_pos_right (e.symm ▸ h.interior_pos q hq c ⟨lo,hi⟩) (hs ⟨lo,hi⟩).le
  have hz : (0:ℝ) ∈ Icc 0 L := ⟨le_rfl,hL⟩
  have cin {f : OrbitPoint → ℝ} {a : ℝ} (cf : Continuous f)
      (hi : ∀ c ∈ Ioo (-1:ℝ) 1, f (0,c)=a) : ∀ c ∈ Icc (-1:ℝ) 1, f (0,c)=a := by
    apply Set.EqOn.of_subset_closure (s:=Ioo (-1:ℝ) 1) (t:=Icc (-1:ℝ) 1)
      (f:=fun c => f (0,c)) (g:=fun _ => a) hi
      (cf.comp (continuous_const.prodMk continuous_id)).continuousOn continuousOn_const Ioo_subset_Icc_self
    rw [closure_Ioo (by norm_num : (-1:ℝ) ≠ 1)]
  have hA0 : ∀ c ∈ Icc (-1:ℝ) 1, A (0,c)=1 := by
    apply cin cA
    intro c hc
    have hcc:=Ioo_subset_Icc_self hc
    have e:=((hA 0 hz).1 c hcc).trans (h.infinity c hcc).1
    exact (mul_left_cancel₀ (hs hc).ne' (by simpa only [mul_one] using e : (1-c^2)*A (0,c)=(1-c^2)*1))
  have hV0 : ∀ c ∈ Icc (-1:ℝ) 1, V (0,c)=0 := by
    apply cin cV
    intro c hc
    have hcc:=Ioo_subset_Icc_self hc
    exact (mul_eq_zero.mp (((hV 0 hz).1 c hcc).trans (h.infinity c hcc).2)).resolve_left (hs hc).ne'
  let B := fun z : OrbitPoint => max |A z-1| |V z|
  have cB : Continuous B := ((cA.sub continuous_const).abs).max cV.abs
  have cK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have neK : K.Nonempty := ⟨(0,0),hz,by constructor <;> norm_num⟩
  obtain ⟨v,hv,hmin⟩ := cK.exists_isMinOn neK cA.continuousOn
  obtain ⟨w,hw,hmax⟩ := cK.exists_isMaxOn neK cB.continuousOn
  let R := prolateRadius ℓ
  let r := fun p => m+R p
  let z := fun p : OrbitPoint => (1/r p,p.2/R p)
  let b := rodBoundaryProfile m ℓ J
  have geom (p : OrbitPoint) : z p ∈ K ∧ 0 < r p ∧
      Real.exp (2*p.1)+p.2^2 ≤ (r p)^2 ∧
      u.normSq p/b.normSq p=A (z p) ∧ (u.twist p-b.twist p)/b.normSq p=V (z p) := by
    let c:=p.2/R p
    obtain ⟨hR,hS,_,he,_⟩ := (prolate_coordinate_differentials ℓ).2.2 p
    change 0 < R p at hR
    change 0 < 1-c^2 at hS
    change Real.exp (2*p.1)=(R p^2-ℓ^2)*(1-c^2) at he
    have hd : 0 < R p^2-ℓ^2 := pos_of_mul_pos_left (he ▸ Real.exp_pos (2*p.1)) hS.le
    have hℓ : ℓ ≤ R p := by nlinarith only [hd,hl,hR,sq_nonneg (R p-ℓ)]
    have hr : 0 < r p := add_pos hm hR
    have hq : 1/r p ∈ Icc 0 L := ⟨(one_div_pos.mpr hr).le,one_div_le_one_div_of_le hmℓ (by change m+ℓ ≤ m+R p; linarith)⟩
    have hc : c ∈ Icc (-1:ℝ) 1 :=
      ⟨by nlinarith only [hS,sq_nonneg (c+1)],by nlinarith only [hS,sq_nonneg (c-1)]⟩
    have hpz : p.2=R p*c := by dsimp [c]; field_simp [hR.ne']
    have rad : Real.exp (2*p.1)+p.2^2 ≤ (r p)^2 := by
      change _ ≤ (m+R p)^2
      rw [he,hpz]
      nlinarith only [mul_nonneg (sq_nonneg ℓ) hS.le,mul_pos hm hR,sq_nonneg m]
    refine ⟨⟨hq,hc⟩,hr,rad,?_,?_⟩
    · have eq:=((hA _ hq).1 c hc).trans (h.values p).1
      change (1-c^2)*A (z p)=u.normSq p/(r p)^2 at eq
      change u.normSq p/((1-c^2)*(r p)^2)=_
      apply (div_eq_iff (mul_ne_zero hS.ne' (pow_ne_zero _ hr.ne'))).2
      linear_combination -((eq_div_iff (pow_ne_zero _ hr.ne')).mp eq)
    · have eq:=((hV _ hq).1 c hc).trans (h.values p).2
      change (1-c^2)*V (z p)=(u.twist p-2*J*(3*c-c^3))/(r p)^2 at eq
      change (u.twist p-2*J*(3*c-c^3))/((1-c^2)*(r p)^2)=_
      apply (div_eq_iff (mul_ne_zero hS.ne' (pow_ne_zero _ hr.ne'))).2
      linear_combination -((eq_div_iff (pow_ne_zero _ hr.ne')).mp eq)
  constructor
  · refine ⟨A v,B w,hpos v hv,?_⟩
    intro p
    obtain ⟨hp,_,_,hn,ht⟩ := geom p
    change A v ≤ u.normSq p/b.normSq p ∧ |u.normSq p/b.normSq p-1| ≤ B w ∧ |(u.twist p-b.twist p)/b.normSq p| ≤ B w
    rw [hn,ht]
    exact ⟨hmin hp,(le_max_left _ _).trans (hmax hp),(le_max_right _ _).trans (hmax hp)⟩
  · intro ε hε
    have ev : ∀ᶠ t : ℝ in 𝓝 0, ∀ c ∈ Icc (-1:ℝ) 1, B (t,c)<ε := by
      apply isCompact_Icc.eventually_forall_of_forall_eventually
      intro c hc
      apply cB.continuousAt.eventually_lt continuousAt_const
      simpa [B,hA0 c hc,hV0 c hc] using hε
    obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp ev
    refine ⟨(1/δ+1)^2,?_⟩
    intro p hp
    obtain ⟨hpK,hr,hrad,hn,ht⟩ := geom p
    have hδ1 : 0 < 1/δ := one_div_pos.mpr hδ
    have hle : 1/δ+1 ≤ r p := (sq_le_sq₀ (by linarith) hr.le).mp (hp.trans hrad)
    have htδ : 1/r p < δ := (div_lt_iff₀ hr).2 (calc
      1 = (1/δ)*δ := (div_mul_cancel₀ 1 hδ.ne').symm
      _ < r p*δ := mul_lt_mul_of_pos_right (by linarith) hδ
      _ = δ*r p := mul_comm _ _)
    have hdist : dist (1/r p) 0 < δ := by rwa [Real.dist_eq,sub_zero,abs_of_pos (one_div_pos.mpr hr)]
    have hh := hball hdist (z p).2 hpK.2
    change B (z p)<ε at hh
    change |u.normSq p/b.normSq p-1| ≤ ε ∧ |(u.twist p-b.twist p)/b.normSq p| ≤ ε
    rw [hn,ht]
    exact ⟨(le_max_left _ _).trans hh.le,(le_max_right _ _).trans hh.le⟩
