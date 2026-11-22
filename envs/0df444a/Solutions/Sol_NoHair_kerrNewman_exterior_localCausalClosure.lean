-- Prove2me | solution 1 for NoHair.kerrNewman_exterior_localCausalClosure
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:18:57.521953+00:00
-- url     : https://prove2.me/submissions/9d1adb05-dffe-4969-a064-d9b960def90e

import Definitions.Def_NoHair_KerrNewmanExteriorGeodesics

open NoHair NoHair.ExteriorGeodesics Set Filter
open OAI.WeakMTWGlobalSupport OAI.WeakMTWGlobalSupport.CoordinateGeometry
open OAI.WeakMTWGlobalSupport.NormalNeighborhood NoHair.PseudoNormal
open scoped ContDiff Manifold BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 330000
noncomputable section

private theorem energy_barrier (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    {x₀ : E4} (N : NF m a e x₀) (base : E4) (c v : ℝ→E4) (o : ℝ)
    (hd : ∀ t, HasDerivAt c (v t) t) (hmemS : ∀ t∈J, c t∈S m a e)
    (htarget : ∀ t∈J, (base,c t)∈N.normal.target)
    (hcone : ∀ t∈J, F m a e (c t) (v t) (v t) ≤ 0)
    (hsign : ∀ t∈J, 0 < o*v t 0) (htime : ∀ t∈J, 0 < o*(c t 0-base 0))
    (hseed : initialEnergy N base (c 0) < 0) : initialEnergy N base (c 1) ≤ initialEnergy N base (c 0) := by
  have sG := field_smooth m a e hp
  have invG (z : E4) (hz : z∈S m a e) := field_inv m a e hp hz
  have symG (z : E4) (hz : z∈S m a e) := field_sym m a e hp hz
  let d (t : ℝ) := (2/N.time)*F m a e (c t) (terminalVelocity N base (c t)) (v t)
  have HE (t : ℝ) (ht : t∈J) : HasDerivAt (fun t => initialEnergy N base (c t)) (d t) t :=
    initialEnergy_deriv N (openS m a e) sG symG invG (htarget t ht) (hd t)
  have H := image_le_of_deriv_right_lt_deriv_boundary (f:=fun t => initialEnergy N base (c t))
    (f':=d) (B:=fun _ => initialEnergy N base (c 0)) (B':=fun _ => 0) (a:=(0:ℝ)) (b:=1)
    (fun t ht => (HE t ht).continuousAt.continuousWithinAt) (fun t ht => (HE t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    le_rfl (fun t => hasDerivAt_const t _) (by
      intro t hti ha
      have ht := Ico_subset_Icc_self hti
      let u := logVec N base (c t)
      have htar' := htarget t ht
      have hu : (base,u)∈N.normal.source := (N.normalAt base).map_target htar'
      obtain ⟨hR,hC,hfirst,_⟩ := radial_data N hu
      have hlast : Z N base u N.time=c t := by simpa only [N.normalAt_apply,Z,u,logVec] using (N.normalAt base).right_inv htar'
      have htim (r : ℝ) (hr : r∈span N) :
          F m a e (Z N base u r) (Velo N base u r) (Velo N base u r) < 0 :=
        (flow_energy N (openS m a e) sG symG invG hu hr).trans_lt (ha.trans_lt hseed)
      have hdt (r : ℝ) (hr : r∈span N) : Velo N base u r 0≠0 := by
        have hh := htim r hr
        exact nonzero_time m a e hp (hR r hr).1 (fun h => by simp [h] at hh) hh.le
      have hforward : 0 < o*(Z N base u N.time 0-Z N base u 0 0) := by
        rw [hlast,hfirst]
        exact htime t ht
      have hfin : N.time∈span N := right_mem_Icc.mpr N.time_pos.le
      have hsg := clock_positive N.time_pos (Z N base u) (Velo N base u) (fun r hr => (hR r hr).2) hC hdt hforward N.time hfin
      have hh := htim N.time hfin
      rw [hlast] at hh
      have hm := cone_pair_negative m a e hp (hmemS t ht) (hcone t ht) hh (common_sign (hsign t ht) hsg)
      dsimp only [d]
      apply mul_neg_of_pos_of_neg (div_pos (by norm_num) N.time_pos)
      rw [symG (c t) (hmemS t ht)]
      exact hm)
  exact H (right_mem_Icc.mpr zero_le_one)

private theorem past_shift_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (p w : E) :
    Tendsto (fun t : ℝ => p-t • w) (𝓝[>] (0:ℝ)) (𝓝 p) := by
  have h : Continuous (fun t : ℝ => p-t • w) := continuous_const.sub (continuous_id.smul continuous_const)
  have hh := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  simpa only [zero_smul,sub_zero] using hh

private theorem derivative_quotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ→E) (v : E) (hf : HasDerivAt f v 0) (h0 : f 0=0) :
    Tendsto (fun s : ℝ => s⁻¹ • f s) (𝓝[>] (0:ℝ)) (𝓝 v) := by
  have h := (hasDerivAt_iff_tendsto_slope_left_right.mp hf).2
  have he : slope f 0 = (fun s : ℝ => s⁻¹ • f s) := by
    funext s
    rw [slope_def_module,h0,sub_zero,sub_zero]
  rwa [he] at h

private theorem scaled_norm_negative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (g₀ : E →L[ℝ] E →L[ℝ] ℝ) (f : ℝ→E) (v : E)
    (hg : Tendsto g (𝓝[>] (0:ℝ)) (𝓝 g₀)) (hf : Tendsto (fun s : ℝ => s⁻¹ • f s) (𝓝[>] 0) (𝓝 v))
    (hneg : g₀ v v < 0) : ∀ᶠ s in 𝓝[>] (0:ℝ), g s (f s) (f s) < 0 := by
  have he : Continuous (fun k : (E →L[ℝ] E →L[ℝ] ℝ) × (E×E) => k.1 k.2.1 k.2.2) :=
    (continuous_fst.clm_apply (continuous_fst.comp continuous_snd)).clm_apply (continuous_snd.comp continuous_snd)
  have hlim : Tendsto (fun s : ℝ => g s (s⁻¹ • f s) (s⁻¹ • f s)) (𝓝[>] 0) (𝓝 (g₀ v v)) :=
    (he.tendsto (g₀,v,v)).comp (hg.prodMk_nhds (hf.prodMk_nhds hf))
  have hspos : ∀ᶠ s in 𝓝[>] (0:ℝ), 0<s := self_mem_nhdsWithin
  filter_upwards [hlim.eventually_lt_const hneg,hspos] with s hs hp
  change g s (s⁻¹ • f s) (s⁻¹ • f s) < 0 at hs
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul] at hs
  exact neg_of_mul_neg_right (neg_of_mul_neg_right hs (inv_pos.mpr hp).le) (inv_pos.mpr hp).le

private theorem scale_timelike {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E →L[ℝ] E →L[ℝ] ℝ) (v : E) (t : ℝ) (ht : 0 < t) (hv : G v v < 0) :
    G (t⁻¹ • v) (t⁻¹ • v) < 0 := by
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
  exact mul_neg_of_pos_of_neg (inv_pos.mpr ht) (mul_neg_of_pos_of_neg (inv_pos.mpr ht) hv)

private theorem past_seed (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) {x₀ : E4} (N : NF m a e x₀)
    {p : E4} (hpS : p∈S m a e) (hsrc : (p,(0:E4))∈N.normal.source)
    (hlog : logVec N p p = 0) (w : E4) (hw : F m a e p w w < 0) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), initialEnergy N (p-s • w) p < 0 := by
  let f (s : ℝ) := logVec N (p-s • w) p
  let g (s : ℝ) := F m a e (p-s • w)
  have sm := field_smooth m a e hp
  have hG : ContinuousAt (F m a e) p := (sm p hpS).continuousWithinAt.continuousAt ((openS m a e).mem_nhds hpS)
  have gL : Tendsto g (𝓝[>] (0:ℝ)) (𝓝 (F m a e p)) := hG.tendsto.comp (past_shift_limit p w)
  have hd : HasDerivAt f (N.time⁻¹ • w) 0 := logVec_base_deriv N (openS m a e) sm
    (fun z hz => field_inv m a e hp hz) hsrc w
  have f0 : f 0 = 0 := by simpa only [f,zero_smul,sub_zero] using hlog
  exact scaled_norm_negative g (F m a e p) f (N.time⁻¹ • w) gL
    (derivative_quotient f _ hd f0) (scale_timelike _ w N.time N.time_pos hw)

private theorem positive_shift {a p o s : ℝ} (h : 0 ≤ o*(a-p)) (ho : o≠0) (hs : 0<s) :
    0 < o*(a-(p-s*o)) := by
  nlinarith only [h,mul_pos hs (sq_pos_iff.mpr ho)]

private theorem past_energy_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : E×E→ℝ) (p q w : E) (hc : ContinuousAt k (p,q))
    (hh : ∀ᶠ s in 𝓝[>] (0:ℝ), k (p-s • w,q) ≤ 0) : k (p,q) ≤ 0 := by
  have hpair : Tendsto (fun s : ℝ => (p-s • w,q)) (𝓝[>] 0) (𝓝 (p,q)) :=
    (past_shift_limit p w).prodMk_nhds tendsto_const_nhds
  exact le_of_tendsto (hc.tendsto.comp hpair) hh

private theorem clock_along (c v : ℝ→E4) (o : ℝ) (hd : ∀ t, HasDerivAt c (v t) t)
    (hc : Continuous v) (hn : ∀ t∈J, v t 0≠0) (hstart : 0 < o*v 0 0) :
    (∀ t∈J, 0 < o*v t 0) ∧ ∀ t∈J, 0 ≤ o*(c t 0-c 0 0) := by
  have h₀ : (0:ℝ)∈J := left_mem_Icc.mpr zero_le_one
  have hone := (mul_ne_zero_iff.mp hstart.ne').1
  have hsign : ∀ t∈J, 0 < o*v t 0 := sign_prop
    (continuous_const.mul ((EuclideanSpace.proj (𝕜:=ℝ) 0).continuous.comp hc)).continuousOn
    (fun t ht => mul_ne_zero hone (hn t ht)) h₀ hstart
  have hclock (t : ℝ) : HasDerivAt (fun s => o*c s 0) (o*v t 0) t :=
    (time_deriv (hd t)).const_mul o
  have hdiff : Differentiable ℝ (fun s => o*c s 0) := fun t => (hclock t).differentiableAt
  have hmono : MonotoneOn (fun s => o*c s 0) J := monotoneOn_of_deriv_nonneg (convex_Icc (0:ℝ) 1)
    hdiff.continuous.continuousOn hdiff.differentiableOn (fun t ht => (hclock t).deriv.symm ▸ (hsign t (interior_subset ht)).le)
  refine ⟨hsign,?_⟩
  intro t ht
  rw [mul_sub]
  exact sub_nonneg.mpr (hmono h₀ ht ht.1)

private theorem energy_of_arc (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    {x₀ : E4} (N : NF m a e x₀) (V : Set E4) (hV : IsOpen V) (hVS : V⊆S m a e)
    (htar : ∀ p∈V, ∀ q∈V, (p,q)∈N.normal.target) (p q w : E4)
    (hpV : p∈V) (hqV : q∈V) (hsrc : (p,(0:E4))∈N.normal.source)
    (hlog : logVec N p p = 0) (hw : F m a e p w w < 0)
    (c v : ℝ→E4) (hd : ∀ t, HasDerivAt c (v t) t)
    (hmem : ∀ t∈J, c t∈V) (he0 : c 0=p) (he1 : c 1=q)
    (hcone : ∀ t∈J, F m a e (c t) (v t) (v t) ≤ 0)
    (hsign : ∀ t∈J, 0 < w 0*v t 0) (hdisp : ∀ t∈J, 0 ≤ w 0*(c t 0-p 0)) :
    initialEnergy N p q ≤ 0 := by
  let o := w 0
  have h₀ : (0:ℝ)∈J := left_mem_Icc.mpr zero_le_one
  have hone : o≠0 := (mul_ne_zero_iff.mp (hsign 0 h₀).ne').1
  let b (s : ℝ) := p-s • w
  have bL : Tendsto b (𝓝[>] (0:ℝ)) (𝓝 p) := past_shift_limit p w
  have bV : ∀ᶠ s in 𝓝[>] (0:ℝ), b s∈V := bL (hV.mem_nhds hpV)
  have spos : ∀ᶠ s in 𝓝[>] (0:ℝ), 0<s := self_mem_nhdsWithin
  have hbase : ∀ᶠ s in 𝓝[>] (0:ℝ), initialEnergy N (b s) p < 0 :=
    past_seed m a e hp N (hVS hpV) hsrc hlog w hw
  have hbound : ∀ᶠ s in 𝓝[>] (0:ℝ), initialEnergy N (b s) q ≤ 0 := by
    filter_upwards [hbase,bV,spos] with s hseed hsV hspos
    have htime (t : ℝ) (ht : t∈J) : 0 < o*(c t 0-b s 0) := by
      change 0 < o*(c t 0-(p 0-s*o))
      exact positive_shift (hdisp t ht) hone hspos
    have h := energy_barrier m a e hp N (b s) c v o hd (fun t ht => hVS (hmem t ht))
      (fun t ht => htar _ hsV _ (hmem t ht)) hcone hsign htime (by rwa [he0])
    rw [he0,he1] at h
    exact h.trans hseed.le
  exact past_energy_limit (fun k : E4×E4 => initialEnergy N k.1 k.2) p q w
    (energy_cont hp N (hVS hpV) (htar _ hpV _ hqV)) hbound


private theorem curve_necessary (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (U a)) (hT : IsTimeOrientation (G m a e) T) {x₀ : E4} (N : NF m a e x₀)
    (V : Set E4) (hV : IsOpen V) (hVS : V⊆S m a e) (hsrc : ∀ x∈V, (x,(0:E4))∈N.normal.source)
    (htar : ∀ p∈V, ∀ q∈V, (p,q)∈N.normal.target)
    (p q : U a) (hpV : p.val∈V) (hqV : q.val∈V)
    (hJ : q∈causalFuture (G m a e) T ((Subtype.val : U a → E4) ⁻¹' V) p) :
    initialEnergy N p.val q.val ≤ 0 ∧ 0 ≤ (q.val 0-p.val 0)*timeComponent (T p) := by
  have sG := field_smooth m a e hp
  have invG (z : E4) (hz : z∈S m a e) := field_inv m a e hp hz
  have hxsrc := hsrc p.val hpV
  have hlog0 : logVec N p.val p.val = 0 := by
    have he := normalAt_zero_of_invertible N (openS m a e) sG invG hxsrc
    simpa only [logVec,he] using (N.normalAt p.val).left_inv hxsrc
  rcases hJ with he|⟨γ,hγ,h0,h1⟩
  · have heq : q = p := mem_singleton_iff.mp he
    subst q
    constructor
    · change F m a e p.val (logVec N p.val p.val) (logVec N p.val p.val) ≤ 0
      simp only [hlog0,map_zero,ContinuousLinearMap.zero_apply,le_refl]
    · simp only [sub_self,zero_mul,le_refl]
  let c (t : ℝ) := (γ t).val
  let v := deriv c
  let w : E4 := T p
  let o := w 0
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a→E4) := contMDiff_subtype_val
  have hc : ContDiff ℝ 1 c := (hval.comp hγ.1).contDiff
  have hd (t : ℝ) : HasDerivAt c (v t) t := (hc.differentiable (by simp) t).hasDerivAt
  have hvel (t : ℝ) := ambient_velocity a γ hγ.1 t (v t) (hd t)
  have hmem (t : ℝ) (ht : t∈J) : c t∈V := (hγ.2 t ht).1
  have he0 : c 0=p.val := congrArg Subtype.val h0
  have he1 : c 1=q.val := congrArg Subtype.val h1
  have hcone (t : ℝ) (ht : t∈J) : v t≠0 ∧ F m a e (c t) (v t) (v t) ≤ 0 ∧ 0 < (v t 0)*timeComponent (T (γ t)) := by
    obtain ⟨hx,hn,hv,hf⟩ := hγ.2 t ht
    have hh := (cone_estimates m a e (γ t) (exterior_profile m a e hp _ (hVS hx)) _ _ hn hv hf (hT.2 _)).2
    change 0 < timeComponent (velocity γ t) * timeComponent (T (γ t)) at hh
    rw [hvel] at hh
    change (velocity γ t:E4)≠0 at hn
    change F m a e (c t) (velocity γ t:E4) (velocity γ t:E4) ≤ 0 at hv
    rw [hvel] at hn hv
    exact ⟨hn,hv,hh⟩
  have h₀ : (0:ℝ)∈J := left_mem_Icc.mpr zero_le_one
  have h₁ : (1:ℝ)∈J := right_mem_Icc.mpr zero_le_one
  have hstart : 0 < o*v 0 0 := by
    have h := (hcone 0 h₀).2.2
    rw [h0,mul_comm] at h
    exact h
  have hn (t : ℝ) (ht : t∈J) : v t 0≠0 :=
    nonzero_time m a e hp (hVS (hmem t ht)) (hcone t ht).1 (hcone t ht).2.1
  obtain ⟨hsign,hdisp₀⟩ := clock_along c v o hd (hc.continuous_deriv le_rfl) hn hstart
  have hdisp (t : ℝ) (ht : t∈J) : 0 ≤ o*(c t 0-p.val 0) := by
    simpa only [he0] using hdisp₀ t ht
  refine ⟨energy_of_arc m a e hp N V hV hVS htar p.val q.val w hpV hqV hxsrc hlog0
    (hT.2 p) c v hd hmem he0 he1 (fun t ht => (hcone t ht).2.1) hsign hdisp,?_⟩
  rw [← he1,mul_comm]
  exact hdisp 1 h₁

theorem solution (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    let U := kerrNewmanSpacetime a
    let D := (Subtype.val : U → E4) ⁻¹' kerrNewmanDOC m a e
    let g := kerrNewmanMetricField m a e
    ∀ x ∈ D, ∃ V : Set U, IsOpen V ∧ x ∈ V ∧ V ⊆ D ∧
      ∀ z : U × U, z.1 ∈ V → z.2 ∈ V →
        z ∈ closure {y : U × U | y.1 ∈ V ∧ y.2 ∈ V ∧ y.2 ∈ causalFuture g T V y.1} →
          z.2 ∈ causalFuture g T D z.1 := by
  classical
  dsimp only
  intro x hx
  obtain ⟨N⟩ := exists_normalFlow_of_invertible (openS m a e) (field_smooth m a e hp)
    (fun z hz => field_inv m a e hp hz) (x₀:=x.val) hx
  have hdiag := normal_center N (openS m a e) (field_smooth m a e hp) (fun z hz => field_inv m a e hp hz) N.center_mem
  have htar : (x.val,x.val)∈N.normal.target := hdiag ▸ N.normal.map_source N.center_mem
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (N.normal.open_target.mem_nhds htar)
  let V := Metric.ball x.val r ∩ (S m a e ∩ {p | (p,(0:E4))∈N.normal.source})
  have hV : IsOpen V := Metric.isOpen_ball.inter ((openS m a e).inter
    (N.normal.open_source.preimage (continuous_id.prodMk continuous_const)))
  have hVS {z : E4} (hz : z∈V) := hz.2.1
  have htr (p : E4) (hp : p∈V) (q : E4) (hq : q∈V) : (p,q)∈N.normal.target := by
    apply hball
    rw [Metric.mem_ball,Prod.dist_eq]
    exact max_lt (Metric.mem_ball.mp hp.1) (Metric.mem_ball.mp hq.1)
  refine ⟨(Subtype.val : U a→E4) ⁻¹' V,hV.preimage continuous_subtype_val,
    ⟨Metric.mem_ball_self hr,hx,N.center_mem⟩,fun _ hz => hVS hz,?_⟩
  intro z hpV hqV hcl
  obtain ⟨seq,hseq,hlim⟩ := mem_closure_iff_seq_limit.mp hcl
  have hnec (n : ℕ) := curve_necessary m a e hp T hT N V hV (fun _ hz => hVS hz)
    (fun _ hz => hz.2.2) htr (seq n).1 (seq n).2 (hseq n).1 (hseq n).2.1 (hseq n).2.2
  have hP : Tendsto (fun n => (seq n).1.val) atTop (𝓝 z.1.val) :=
    (continuous_subtype_val.tendsto z.1).comp ((continuous_fst.tendsto z).comp hlim)
  have hQ : Tendsto (fun n => (seq n).2.val) atTop (𝓝 z.2.val) :=
    (continuous_subtype_val.tendsto z.2).comp ((continuous_snd.tendsto z).comp hlim)
  apply radial_future m a e hp T hT N z.1 z.2 (htr _ hpV _ hqV)
  · exact le_of_tendsto ((energy_cont hp N (hVS hpV) (htr _ hpV _ hqV)).tendsto.comp
      (hP.prodMk_nhds hQ)) (Eventually.of_forall fun n => (hnec n).1)
  · have hTlim : Tendsto (fun n => W a T (seq n).1.val) atTop (𝓝 (W a T z.1.val)) :=
      (W_cont m a e T hT z.1).tendsto.comp hP
    have hproj : Continuous timeComponent := (EuclideanSpace.proj (𝕜:=ℝ) (0 : Fin 4)).continuous
    have hQ0 : Tendsto (fun n => timeComponent (seq n).2.val) atTop (𝓝 (timeComponent z.2.val)) :=
      (hproj.tendsto _).comp hQ
    have hP0 : Tendsto (fun n => timeComponent (seq n).1.val) atTop (𝓝 (timeComponent z.1.val)) :=
      (hproj.tendsto _).comp hP
    have ht0 : Tendsto (fun n => timeComponent (W a T (seq n).1.val)) atTop (𝓝 (timeComponent (W a T z.1.val))) :=
      (hproj.tendsto _).comp hTlim
    have hT0 : Tendsto (fun n => timeComponent (T (seq n).1)) atTop (𝓝 (timeComponent (T z.1))) := by
      simpa only [W_on] using ht0
    exact ge_of_tendsto ((hQ0.sub hP0).mul hT0) (Eventually.of_forall fun n => (hnec n).2)
