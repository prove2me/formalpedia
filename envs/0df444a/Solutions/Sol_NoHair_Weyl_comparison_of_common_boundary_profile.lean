-- Prove2me | solution 1 for NoHair.Weyl.comparison_of_common_boundary_profile
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:48:03.804812+00:00
-- url     : https://prove2.me/submissions/a01ca145-96f5-4698-8e16-4f963d8cb176

import Definitions.Def_NoHair_weylBoundaryProfile

noncomputable section

open NoHair.Weyl Filter Topology

private theorem abs_difference {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x-y| ≤ A+B := by
  obtain ⟨hl,hr⟩:=abs_le.mp hx
  obtain ⟨gl,gr⟩:=abs_le.mp hy
  exact abs_le.mpr ⟨by linarith,by linarith⟩

private theorem deviations (u v b : ErnstPotentials) (hb : ∀ p, 0 < b.normSq p)
    (p : OrbitPoint) (d e U V : ℝ) (hd : 0 < d) (he : 0 < e)
    (hu : d ≤ u.normSq p/b.normSq p ∧ |u.normSq p/b.normSq p-1| ≤ U ∧
      |(u.twist p-b.twist p)/b.normSq p| ≤ U)
    (hv : e ≤ v.normSq p/b.normSq p ∧ |v.normSq p/b.normSq p-1| ≤ V ∧
      |(v.twist p-b.twist p)/b.normSq p| ≤ V) :
    deviation u v p ≤ 2*(U+V)^2/(d*e) := by
  let x:=u.normSq p/b.normSq p
  let y:=v.normSq p/b.normSq p
  let s:=(u.twist p-b.twist p)/b.normSq p
  let t:=(v.twist p-b.twist p)/b.normSq p
  have hxy : d*e ≤ x*y := mul_le_mul hu.1 hv.1 he.le (hd.trans_le hu.1).le
  have same : deviation u v p=((x-y)^2+(s-t)^2)/(x*y) := by
    have ux : 0 < u.normSq p := (div_pos_iff_of_pos_right (hb p)).mp (hd.trans_le hu.1)
    have vx : 0 < v.normSq p := (div_pos_iff_of_pos_right (hb p)).mp (he.trans_le hv.1)
    unfold deviation x y s t
    field_simp [(hb p).ne',ux.ne',vx.ne'] <;> ring
  have hx : |x-y| ≤ U+V := by
    rw [show x-y=(x-1)-(y-1) by ring]
    exact abs_difference hu.2.1 hv.2.1
  have ht : |s-t| ≤ U+V := abs_difference hu.2.2 hv.2.2
  have sqr {z : ℝ} (hz : |z| ≤ U+V) : z^2 ≤ (U+V)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg z) hz 2
  rw [same]
  calc
    _ ≤ (2*(U+V)^2)/(x*y) := by
      apply (div_le_div_iff_of_pos_right ((mul_pos hd he).trans_le hxy)).mpr
      linarith only [sqr hx,sqr ht]
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (mul_pos hd he) hxy

private theorem scaled_bounds (u b : ErnstPotentials) (p : OrbitPoint) (hp : 0 < b.normSq p)
    (d B : ℝ) (h : d ≤ u.normSq p/b.normSq p ∧ |u.normSq p/b.normSq p-1| ≤ B ∧
      |(u.twist p-b.twist p)/b.normSq p| ≤ B) :
    d*b.normSq p ≤ u.normSq p ∧ u.normSq p ≤ (B+1)*b.normSq p ∧
    |u.twist p-b.twist p| ≤ B*b.normSq p := by
  have hx := (abs_le.mp h.2.1).2
  have ht := h.2.2
  rw [abs_div,abs_of_pos hp] at ht
  exact ⟨(le_div_iff₀ hp).mp h.1,(div_le_iff₀ hp).mp (by linarith),(div_le_iff₀ hp).mp ht⟩

theorem solution (u v b : ErnstPotentials)
    (hb : ∀ p, 0 < b.normSq p) (hu : HasProfileEstimates u b) (hv : HasProfileEstimates v b) :
    HasComparisonBounds u v ∧ ∀ ℓ J : ℝ, HasAxisData v ℓ J →
      (∀ z : ℝ, |z| < ℓ → ∃ L : ℝ, Tendsto (fun s : ℝ => u.normSq (s,z)) atBot (𝓝 L)) →
      HasAxisData u ℓ J := by
  obtain ⟨⟨d,B,hd,gu⟩,fu⟩:=hu
  obtain ⟨⟨e,C,he,gv⟩,fv⟩:=hv
  constructor
  · constructor
    · exact ⟨_,fun p => deviations u v b hb p d e B C hd he (gu p) (gv p)⟩
    · intro ε hε
      let δ:=Real.sqrt (ε*(d*e)/8)
      have hδ : 0 < δ := Real.sqrt_pos.mpr (by positivity)
      have hδ2 : δ^2=ε*(d*e)/8 := Real.sq_sqrt (by positivity)
      obtain ⟨R,hR⟩:=fu δ hδ
      obtain ⟨T,hT⟩:=fv δ hδ
      refine ⟨max R T,fun p hp => ?_⟩
      apply (deviations u v b hb p d e δ δ hd he ⟨(gu p).1,hR p ((le_max_left R T).trans hp)⟩
        ⟨(gv p).1,hT p ((le_max_right R T).trans hp)⟩).trans
      exact (div_le_iff₀ (mul_pos hd he)).mpr (by nlinarith only [hδ2])
  · have ub (p : OrbitPoint) := scaled_bounds u b p (hb p) d B (gu p)
    have vb (p : OrbitPoint) := scaled_bounds v b p (hb p) e C (gv p)
    have axis (z K : ℝ)
        (hn : Tendsto (fun s : ℝ => v.normSq (s,z)) atBot (𝓝 0))
        (ht : Tendsto (fun s : ℝ => v.twist (s,z)) atBot (𝓝 K)) :
        Tendsto (fun s : ℝ => u.normSq (s,z)) atBot (𝓝 0) ∧
        Tendsto (fun s : ℝ => u.twist (s,z)) atBot (𝓝 K) := by
      have hbase : Tendsto (fun s : ℝ => b.normSq (s,z)) atBot (𝓝 0) := by
        apply squeeze_zero (fun s => (hb (s,z)).le)
          (fun s => (le_div_iff₀ he).mpr (by simpa only [mul_comm] using (vb (s,z)).1))
        simpa only [zero_div] using hn.div_const e
      have unorm := squeeze_zero (fun s : ℝ => ((mul_pos hd (hb (s,z))).le.trans (ub (s,z)).1))
        (fun s => (ub (s,z)).2.1)
        (show Tendsto (fun s : ℝ => (B+1)*b.normSq (s,z)) atBot (𝓝 0) by
          simpa only [mul_zero] using hbase.const_mul (B+1))
      have htw : Tendsto (fun s : ℝ => u.twist (s,z)-v.twist (s,z)) atBot (𝓝 0) := by
        apply (tendsto_zero_iff_abs_tendsto_zero _).2
        apply squeeze_zero (fun _ => abs_nonneg _)
          (fun s => show |u.twist (s,z)-v.twist (s,z)| ≤ (B+C)*b.normSq (s,z) by
            rw [show u.twist (s,z)-v.twist (s,z)=(u.twist (s,z)-b.twist (s,z))-(v.twist (s,z)-b.twist (s,z)) by ring,
              add_mul]
            exact abs_difference (ub (s,z)).2.2 (vb (s,z)).2.2)
        simpa only [mul_zero] using hbase.const_mul (B+C)
      refine ⟨unorm,?_⟩
      simpa only [sub_add_cancel,zero_add] using htw.add ht
    intro ℓ J hvax hLim
    refine ⟨fun z hz => axis z (4*J) (hvax.1 z hz).1 (hvax.1 z hz).2,
      fun z hz => axis z (-(4*J)) (hvax.2.1 z hz).1 (hvax.2.1 z hz).2,?_⟩
    intro z hz
    obtain ⟨L,hL⟩:=hLim z hz
    obtain ⟨K,hK,ht⟩:=hvax.2.2 z hz
    have hC : 0 ≤ C := (abs_nonneg _).trans (gv (0,z)).2.1
    have bound (s : ℝ) : d*v.normSq (s,z) ≤ (C+1)*u.normSq (s,z) := calc
      _ ≤ d*((C+1)*b.normSq (s,z)) := mul_le_mul_of_nonneg_left (vb (s,z)).2.1 hd.le
      _ = (C+1)*(d*b.normSq (s,z)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (ub (s,z)).1 (by linarith)
    have hh := le_of_tendsto_of_tendsto' (ht.const_mul d) (hL.const_mul (C+1)) bound
    exact ⟨L,pos_of_mul_pos_right ((mul_pos hd hK).trans_le hh) (by linarith),hL⟩
