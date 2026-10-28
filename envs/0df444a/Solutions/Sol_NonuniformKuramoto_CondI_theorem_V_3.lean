-- Prove2me | solution 1 for NonuniformKuramoto.CondI.theorem_V_3
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-27T16:08:25.134523+00:00
-- url     : https://prove2.me/submissions/494b7847-0e93-4371-9130-b059a4d12fcf

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model
import Definitions.Def_NonuniformKuramoto_CondI_Constants

open Filter Topology

namespace NonuniformKuramoto.CondI.KUFresh
open Filter Set Topology
variable {I : Type*} [Fintype I] [Nonempty I]
noncomputable def peak (v : I → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty v
lemma le_peak (v : I → ℝ) (i : I) : v i ≤ peak v := Finset.le_sup' _ (Finset.mem_univ i)
lemma peak_le {v : I → ℝ} {c : ℝ} (h : ∀ i, v i ≤ c) : peak v ≤ c :=
  Finset.sup'_le _ _ (fun i _ => h i)
lemma peak_attained (v : I → ℝ) : ∃ i, v i = peak v := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty v
  exact ⟨i,hi.symm⟩
lemma peak_lt {v : I → ℝ} {c : ℝ} (h : ∀ i, v i < c) : peak v < c := by
  obtain ⟨i,hi⟩ := peak_attained v
  rw [←hi]
  exact h i
lemma peak_lipschitz (v w : I → ℝ) : |peak v-peak w| ≤ ‖v-w‖ := by
  apply abs_le.mpr
  constructor
  · have h : peak w ≤ peak v+‖v-w‖ := by
      apply peak_le
      intro i
      have hi := norm_le_pi_norm (v-w) i
      change |v i-w i| ≤ ‖v-w‖ at hi
      have := le_peak v i
      linarith [(abs_le.mp hi).1]
    linarith
  · have h : peak v ≤ peak w+‖v-w‖ := by
      apply peak_le
      intro i
      have hi := norm_le_pi_norm (v-w) i
      change |v i-w i| ≤ ‖v-w‖ at hi
      have := le_peak w i
      linarith [(abs_le.mp hi).2]
    linarith
lemma continuous_peak : Continuous (peak : (I → ℝ) → ℝ) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simpa only [NNReal.coe_one,one_mul,Real.dist_eq,dist_eq_norm,Real.norm_eq_abs] using peak_lipschitz v w
lemma peak_const (c : ℝ) : peak (fun _ : I => c)=c := by
  apply le_antisymm (peak_le fun _ => le_rfl)
  exact le_peak (fun _ : I => c) (Classical.choice (inferInstance : Nonempty I))
lemma peak_add_const (v : I → ℝ) (c : ℝ) : peak (fun i => v i+c)=peak v+c := by
  apply le_antisymm (peak_le fun i => add_le_add (le_peak v i) le_rfl)
  obtain ⟨i,hi⟩ := peak_attained v
  simpa only [hi] using le_peak (fun i => v i+c) i
end NonuniformKuramoto.CondI.KUFresh

namespace NonuniformKuramoto.CondI.KUFresh
open Filter Set Topology
variable {I : Type*} [Fintype I] [Nonempty I]
noncomputable def diam (v : I → ℝ) : ℝ := peak (fun p : I×I => v p.1-v p.2)
lemma sub_le_diam (v : I → ℝ) (i j : I) : v i-v j ≤ diam v := le_peak (fun p : I×I => v p.1-v p.2) (i,j)
lemma diam_nonneg (v : I → ℝ) : 0 ≤ diam v := by
  obtain ⟨i⟩ := ‹Nonempty I›
  simpa using sub_le_diam v i i
lemma diam_le {v : I → ℝ} {c : ℝ} (h : ∀ i j,v i-v j ≤ c) : diam v ≤ c :=
  peak_le fun p => h p.1 p.2
lemma diam_attained (v : I → ℝ) : ∃ i j,v i-v j=diam v := by
  obtain ⟨⟨i,j⟩,h⟩ := peak_attained (fun p : I×I => v p.1-v p.2)
  exact ⟨i,j,h⟩
lemma diam_extrema {v : I → ℝ} {i j : I} (h : v i-v j=diam v) :
    (∀ k,v k ≤ v i) ∧ (∀ k,v j ≤ v k) := by
  constructor
  · intro k
    have := sub_le_diam v k j
    linarith
  · intro k
    have := sub_le_diam v i k
    linarith
lemma continuous_diam : Continuous (diam : (I→ℝ)→ℝ) := by
  apply continuous_peak.comp
  exact continuous_pi fun p => (continuous_apply p.1).sub (continuous_apply p.2)
omit [Fintype I] [Nonempty I] in
lemma clamp_extrema (v : I → ℝ) (m l : I) (hm : ∀i,v i ≤ v m)
    (hl : ∀i,v l ≤ v i) {γ : ℝ} (hg : 0 ≤ γ) (hv : γ < v m-v l) :
    let w := fun i => min (v i) (v l+γ)
    w m-w l=γ ∧ (∀i,w i ≤ w m) ∧ (∀i,w l ≤ w i) ∧
      ∀i,|v i-w i| ≤ (v m-v l)-γ := by
  dsimp only
  have hwm : min (v m) (v l+γ)=v l+γ := min_eq_right (by linarith)
  have hwl : min (v l) (v l+γ)=v l := min_eq_left (by linarith)
  refine ⟨?_,?_,?_,?_⟩
  · rw [hwm,hwl];ring
  · intro i
    rw [hwm]
    exact min_le_right _ _
  · intro i
    rw [hwl]
    exact le_min (hl i) (by linarith)
  · intro i
    rw [abs_of_nonneg (sub_nonneg.mpr (min_le_left _ _))]
    rcases le_total (v i) (v l+γ) with hi|hi
    · rw [min_eq_left hi]
      linarith
    · rw [min_eq_right hi]
      have := hm i
      linarith
end NonuniformKuramoto.CondI.KUFresh

namespace NonuniformKuramoto.CondI.KUFresh
open Finset
noncomputable def fieldLip {n : ℕ} (D : Fin n → ℝ) (P : Fin n → Fin n → ℝ) : ℝ :=
  1+4*∑ i,∑ j,|P i j|/|D i|
lemma fieldLip_pos {n : ℕ} (D : Fin n → ℝ) (P : Fin n → Fin n → ℝ) : 0 < fieldLip D P := by
  unfold fieldLip
  positivity
lemma field_difference_lipschitz {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (v w : Fin n → ℝ) {ε : ℝ} (_he : 0 ≤ ε) (hvw : ∀ i,|v i-w i| ≤ ε) (i : Fin n) :
    |field D ω P ϕ v i-field D ω P ϕ w i| ≤
      (2*∑ j,|P i j|/|D i|)*ε := by
  unfold field
  rw [←sub_div,sub_sub_sub_cancel_left,abs_div]
  have hs : |(∑ j,P i j*Real.sin (w i-w j+ϕ i j))-
      (∑ j,P i j*Real.sin (v i-v j+ϕ i j))| ≤ (∑ j,|P i j|)*(2*ε) := by
    rw [←sum_sub_distrib]
    calc
      _ ≤ ∑ j,|P i j*Real.sin (w i-w j+ϕ i j)-P i j*Real.sin (v i-v j+ϕ i j)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j,|P i j| *(2*ε) := by
        apply sum_le_sum
        intro j _
        rw [←mul_sub,abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have hsin := Real.abs_sin_sub_sin_le (w i-w j+ϕ i j) (v i-v j+ϕ i j)
        have hdiff : |(w i-w j+ϕ i j)-(v i-v j+ϕ i j)| ≤ 2*ε := by
          have hid : (w i-w j+ϕ i j)-(v i-v j+ϕ i j)=-(v i-w i)+(v j-w j) := by ring
          rw [hid]
          have ht := abs_add_le (-(v i-w i)) (v j-w j)
          rw [abs_neg] at ht
          linarith [hvw i,hvw j]
        exact hsin.trans hdiff
      _ = _ := by rw [sum_mul]
  have hd := div_le_div_of_nonneg_right hs (abs_nonneg (D i))
  calc
    _ ≤ ((∑ j,|P i j|)*(2*ε))/|D i| := hd
    _ = _ := by rw [←sum_div]; ring
end NonuniformKuramoto.CondI.KUFresh

namespace NonuniformKuramoto.CondI.KUFresh
open Finset
lemma compressed_field_bound {n : ℕ} [Nonempty (Fin n)]
    (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) {γ : ℝ} (hg : 0 ≤ γ)
    (hb : ∀ (w : Fin n → ℝ) (m l : Fin n),m ≠ l →
      (∀i,w i ≤ w m) → (∀i,w l ≤ w i) → w m-w l=γ →
      field D ω P ϕ w m-field D ω P ϕ w l ≤ 0)
    (v : Fin n → ℝ) (hv : γ < diam v) (m l : Fin n) (hml : v m-v l=diam v) :
    field D ω P ϕ v m-field D ω P ϕ v l ≤ fieldLip D P*(diam v-γ) := by
  have hmne : m ≠ l := by intro he; subst l; simp only [sub_self] at hml; linarith
  have hm := (diam_extrema hml).1
  have hl := (diam_extrema hml).2
  let w := fun i => min (v i) (v l+γ)
  have hc := clamp_extrema v m l hm hl hg (by linarith : γ < v m-v l)
  change w m-w l=γ ∧ (∀i,w i ≤ w m) ∧ (∀i,w l ≤ w i) ∧
    (∀i,|v i-w i| ≤ (v m-v l)-γ) at hc
  have hbase := hb w m l hmne hc.2.1 hc.2.2.1 hc.1
  have he : 0 ≤ diam v-γ := by linarith
  have hdist : ∀i,|v i-w i| ≤ diam v-γ := by simpa only [hml] using hc.2.2.2
  have hfm := field_difference_lipschitz D ω P ϕ v w he hdist m
  have hfl := field_difference_lipschitz D ω P ϕ v w he hdist l
  let S := ∑ i,∑ j,|P i j|/|D i|
  have hmS : (∑ j,|P m j|/|D m|) ≤ S :=
    single_le_sum (f := fun i => ∑ j,|P i j|/|D i|) (fun i _ => sum_nonneg fun j _ => div_nonneg (abs_nonneg _) (abs_nonneg _)) (mem_univ m)
  have hlS : (∑ j,|P l j|/|D l|) ≤ S :=
    single_le_sum (f := fun i => ∑ j,|P i j|/|D i|) (fun i _ => sum_nonneg fun j _ => div_nonneg (abs_nonneg _) (abs_nonneg _)) (mem_univ l)
  have hmm := mul_le_mul_of_nonneg_right hmS he
  have hll := mul_le_mul_of_nonneg_right hlS he
  change _ ≤ (1+4*S)*(diam v-γ)
  nlinarith only [hbase,(abs_le.mp hfm).2,(abs_le.mp hfl).1,hmm,hll,he]
end NonuniformKuramoto.CondI.KUFresh

namespace NonuniformKuramoto.CondI.KUFresh
open Filter Set Topology
variable {I : Type*} [Fintype I] [Nonempty I]
def UpperSlope (f : ℝ → ℝ) (t b : ℝ) : Prop :=
  ∀ r, b < r → ∀ᶠ y in 𝓝[>] t, slope f t y < r
lemma peak_upperSlope (f : I → ℝ → ℝ) (d : I → ℝ) (t b : ℝ)
    (hd : ∀ i, HasDerivWithinAt (f i) (d i) (Ici t) t)
    (hb : ∀ i, f i t=peak (fun j => f j t) → d i ≤ b) :
    UpperSlope (fun y => peak (fun i => f i y)) t b := by
  intro r hr
  have hi (i : I) : ∀ᶠ y in 𝓝[>] t,
      f i y < peak (fun j => f j t)+r*(y-t) := by
    by_cases he : f i t=peak (fun j => f j t)
    · have hs := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).mp (hd i).Ioi_of_Ici
      have hh := hs.eventually (Iio_mem_nhds ((hb i he).trans_lt hr))
      filter_upwards [hh,self_mem_nhdsWithin] with y hy hyt
      rw [slope_def_field] at hy
      have hy' := (div_lt_iff₀ (sub_pos.mpr hyt)).mp hy
      rw [he] at hy'
      linarith
    · have hlt : f i t < peak (fun j => f j t) := lt_of_le_of_ne (le_peak (fun j => f j t) i) he
      have hleft := (hd i).Ioi_of_Ici.continuousWithinAt
      have hright : Tendsto (fun y : ℝ => peak (fun j => f j t)+r*(y-t)) (𝓝[>] t)
          (𝓝 (peak (fun j => f j t))) := by
        have hc : ContinuousAt (fun y : ℝ => peak (fun j => f j t)+r*(y-t)) t := by fun_prop
        simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
      exact hleft.eventually_lt hright hlt
  have hall := Filter.eventually_all.mpr hi
  filter_upwards [hall,self_mem_nhdsWithin] with y hy hyt
  have hp := peak_lt hy
  rw [slope_def_field]
  apply (div_lt_iff₀ (sub_pos.mpr hyt)).mpr
  linarith
lemma UpperSlope.frequently {f : ℝ → ℝ} {t b r : ℝ} (h : UpperSlope f t b)
    (hr : b < r) : ∃ᶠ y in 𝓝[>] t, slope f t y < r := (h r hr).frequently
end NonuniformKuramoto.CondI.KUFresh

namespace NonuniformKuramoto.CondI.KUFresh
open Filter Set Topology
lemma solution_continuous {n : ℕ} {D ω : Fin n → ℝ} {P ϕ : Fin n → Fin n → ℝ}
    {θ : ℝ → Fin n → ℝ} (hθ : IsSolution D ω P ϕ θ) : ContinuousOn θ (Ici 0) :=
  fun t ht => (hθ t ht).continuousWithinAt
lemma solution_deriv_right {n : ℕ} {D ω : Fin n → ℝ} {P ϕ : Fin n → Fin n → ℝ}
    {θ : ℝ → Fin n → ℝ} (hθ : IsSolution D ω P ϕ θ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt θ (field D ω P ϕ (θ t)) (Ici t) t :=
  (hθ t ht).mono (fun _ hy => ht.trans hy)
lemma diam_upperSlope {I : Type*} [Fintype I] [Nonempty I] {θ : ℝ → I → ℝ}
    {v : I → ℝ} {t b : ℝ} (hd : HasDerivWithinAt θ v (Ici t) t)
    (hb : ∀i j,θ t i-θ t j=diam (θ t) → v i-v j ≤ b) :
    UpperSlope (fun s => diam (θ s)) t b := by
  apply peak_upperSlope (f := fun p : I×I => fun s => θ s p.1-θ s p.2)
    (d := fun p => v p.1-v p.2)
  · intro p
    exact ((hasDerivWithinAt_pi.mp hd) p.1).sub ((hasDerivWithinAt_pi.mp hd) p.2)
  · intro p hp
    exact hb p.1 p.2 hp
lemma solution_diam_finite {n : ℕ} [Nonempty (Fin n)] {D ω : Fin n → ℝ}
    {P ϕ : Fin n → Fin n → ℝ} {θ : ℝ → Fin n → ℝ} (hθ : IsSolution D ω P ϕ θ)
    {t : ℝ} (ht : 0 ≤ t) : ∃b,UpperSlope (fun s => diam (θ s)) t b := by
  refine ⟨diam (field D ω P ϕ (θ t)),diam_upperSlope (solution_deriv_right hθ ht) ?_⟩
  intro i j _
  exact sub_le_diam _ i j
lemma solution_shift {n : ℕ} {D ω : Fin n → ℝ} {P ϕ : Fin n → Fin n → ℝ}
    {θ : ℝ → Fin n → ℝ} (hθ : IsSolution D ω P ϕ θ) {T : ℝ} (hT : 0 ≤ T) :
    IsSolution D ω P ϕ (fun s => θ (T+s)) := by
  intro t ht
  apply hasDerivWithinAt_pi.mpr
  intro i
  have hd := ((hasDerivWithinAt_pi.mp (hθ (T+t) (add_nonneg hT ht))) i).comp t
    (((hasDerivAt_id t).const_add T).hasDerivWithinAt) (fun s hs => add_nonneg hT hs)
  simp only [mul_one,Function.comp_def] at hd
  convert hd using 1
  rfl
end NonuniformKuramoto.CondI.KUFresh

namespace NonuniformKuramoto.CondI.KUFresh
open Filter Set Topology
lemma upperSlope_barrier {f B B' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (ha : f a ≤ B a)
    (hB : ∀t,HasDerivAt B (B' t) t)
    (hs : ∀t∈Ico a b,∃d,UpperSlope f t d ∧ (f t=B t → d < B' t)) :
    ∀t∈Icc a b,f t ≤ B t := by
  classical
  let d (t : ℝ) : ℝ := if h : t∈Ico a b then Classical.choose (hs t h) else 0
  apply image_le_of_liminf_slope_right_lt_deriv_boundary hf (f' := d) _ ha hB _
  · intro t ht r hr
    have hp := Classical.choose_spec (hs t ht)
    have he : d t=Classical.choose (hs t ht) := dif_pos ht
    rw [he] at hr
    exact hp.1.frequently hr
  · intro t ht heq
    have hp := Classical.choose_spec (hs t ht)
    simpa only [d,dif_pos ht] using hp.2 heq
lemma upperSlope_linear {f : ℝ → ℝ} {a b c : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hs : ∀t∈Ico a b,UpperSlope f t c) :
    ∀t∈Icc a b,f t ≤ f a+c*(t-a) := by
  apply image_le_of_liminf_slope_right_le_deriv_boundary hf
    (B' := fun _ => c)
  · simp
  · fun_prop
  · intro t _
    exact (((((hasDerivAt_id t).sub_const a).const_mul c).const_add (f a)).congr_deriv (by simp)).hasDerivWithinAt
  · intro t ht r hr
    exact (hs t ht).frequently hr
lemma upperSlope_invariant {f : ℝ → ℝ} {γ L : ℝ}
    (hf : ContinuousOn f (Ici 0)) (h0 : f 0 ≤ γ)
    (hfinite : ∀t,0 ≤ t → ∃d,UpperSlope f t d)
    (hbound : ∀t,0 ≤ t → γ < f t → UpperSlope f t (L*(f t-γ))) :
    ∀t,0 ≤ t → f t ≤ γ := by
  intro t ht
  by_contra hn
  have hgap : 0 < f t-γ := sub_pos.mpr (lt_of_not_ge hn)
  let ε := (f t-γ)/(2*Real.exp ((L+1)*t))
  have he : 0 < ε := div_pos hgap (by positivity)
  have hbar := upperSlope_barrier (B := fun s => γ+ε*Real.exp ((L+1)*s))
    (B' := fun s => ε*Real.exp ((L+1)*s)*(L+1))
    (a := 0) (b := t) (hf.mono (fun _ hs => hs.1))
    (by simpa using (show f 0 ≤ γ+ε by linarith))
    (by
      intro s
      exact ((((hasDerivAt_id s).const_mul (L+1)).exp.const_mul ε).const_add γ).congr_deriv (by dsimp; ring))
    (by
      intro s hs
      by_cases hEq : f s=γ+ε*Real.exp ((L+1)*s)
      · have hpos : 0 < ε*Real.exp ((L+1)*s) := mul_pos he (Real.exp_pos _)
        refine ⟨L*(f s-γ),hbound s hs.1 (by linarith),?_⟩
        intro _
        rw [hEq]
        nlinarith
      · obtain ⟨d,hd⟩ := hfinite s hs.1
        exact ⟨d,hd,fun h => (hEq h).elim⟩)
  have hb := hbar t ⟨ht,le_rfl⟩
  have hc : ε*Real.exp ((L+1)*t)=(f t-γ)/2 := by
    dsimp [ε]
    field_simp
  rw [hc] at hb
  linarith
end NonuniformKuramoto.CondI.KUFresh

namespace NonuniformKuramoto.CondI.KUFresh
open Filter Set Topology
lemma arc_invariant_of_boundary {n : ℕ} [Nonempty (Fin n)]
    (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) {γ : ℝ} (hg : 0 ≤ γ)
    (hb : ∀ (w : Fin n → ℝ) (m l : Fin n),m ≠ l →
      (∀i,w i ≤ w m) → (∀i,w l ≤ w i) → w m-w l=γ →
      field D ω P ϕ w m-field D ω P ϕ w l ≤ 0) :
    IsPosInvariant D ω P ϕ (ArcClosed γ) := by
  intro θ hθ h0 t ht
  have hc : ContinuousOn (fun s => diam (θ s)) (Ici 0) := continuous_diam.comp_continuousOn (solution_continuous hθ)
  have hi := upperSlope_invariant (L := fieldLip D P) hc (diam_le h0)
    (fun s hs => solution_diam_finite hθ hs)
    (by
      intro s hs hgs
      apply diam_upperSlope (solution_deriv_right hθ hs)
      intro m l hml
      exact compressed_field_bound D ω P ϕ hg hb (θ s) hgs m l hml)
  intro i j
  exact (sub_le_diam _ i j).trans (hi t ht)
end NonuniformKuramoto.CondI.KUFresh

namespace NonuniformKuramoto.CondI.KUFresh
open Filter Set Topology
lemma finite_entry {f : ℝ → ℝ} {γ η : ℝ} (hη : 0 < η)
    (hf : ContinuousOn f (Ici 0)) (hpos : ∀t,0 ≤ t → 0 ≤ f t)
    (hs : ∀t,0 ≤ t → γ < f t → UpperSlope f t (-η)) :
    ∃T,0 ≤ T ∧ f T ≤ γ := by
  by_contra hn
  push Not at hn
  let T := (f 0+1)/η
  have hT : 0 ≤ T := div_nonneg (by linarith [hpos 0 le_rfl]) hη.le
  have hlin := upperSlope_linear (a := 0) (b := T) (c := -η)
    (hf.mono (fun _ hh => hh.1)) (fun t ht => hs t ht.1 (hn t ht.1)) T ⟨hT,le_rfl⟩
  have hmul : η*T=f 0+1 := by dsimp [T]; field_simp
  have hp := hpos T hT
  nlinarith
end NonuniformKuramoto.CondI.KUFresh

namespace NonuniformKuramoto.CondI.KUFresh
open Filter Set Topology
lemma arc_entry_of_drift {n : ℕ} [Nonempty (Fin n)]
    (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) {γ γ0 η : ℝ}
    (hγ : 0 ≤ γ) (hη : 0 < η)
    (hinv : IsPosInvariant D ω P ϕ (ArcClosed γ))
    (hb : ∀ (v : Fin n → ℝ) (m l : Fin n),m ≠ l →
      (∀i,v i ≤ v m) → (∀i,v l ≤ v i) →
      γ < v m-v l → v m-v l ≤ γ0 →
      field D ω P ϕ v m-field D ω P ϕ v l ≤ -η)
    (θ : ℝ → Fin n → ℝ) (hθ : IsSolution D ω P ϕ θ)
    (hupper : ∀t,0 ≤ t → ArcClosed γ0 (θ t)) :
    ∃T,0 ≤ T ∧ ∀t,T ≤ t → ArcClosed γ (θ t) := by
  have hfinite := finite_entry (γ := γ) hη
    (continuous_diam.comp_continuousOn (solution_continuous hθ))
    (fun t _ => diam_nonneg (θ t))
    (by
      intro t ht hgt
      change γ < diam (θ t) at hgt
      apply diam_upperSlope (solution_deriv_right hθ ht)
      intro m l hml
      have he := diam_extrema hml
      have hne : m ≠ l := by intro h; subst l; simp only [sub_self] at hml; linarith
      exact hb (θ t) m l hne he.1 he.2 (by linarith)
        (hml ▸ diam_le (hupper t ht)))
  obtain ⟨T,hT,htarget⟩ := hfinite
  refine ⟨T,hT,?_⟩
  intro t ht
  have hstart : ArcClosed γ (θ T) := fun i j => (sub_le_diam _ i j).trans htarget
  have hh := hinv (fun s => θ (T+s)) (solution_shift hθ hT)
    (by simpa only [add_zero] using hstart) (t-T) (sub_nonneg.mpr ht)
  simpa only [add_sub_cancel] using hh
end NonuniformKuramoto.CondI.KUFresh


namespace NonuniformKuramoto.CondI.KUFresh

open Classical

lemma offDiag_nonempty {n : ℕ} (hn : 2 ≤ n) :
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2)).Nonempty := by
  refine ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩
  simp

lemma minOffDiag_le {n : ℕ} (f : Fin n × Fin n → ℝ) (i j : Fin n)
    (hij : i ≠ j) : minOffDiag f ≤ f (i,j) := by
  have h : (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2)).Nonempty :=
    ⟨(i,j), by simp [hij]⟩
  simp only [minOffDiag, dif_pos h]
  exact Finset.inf'_le _ (by simp [hij])

lemma le_minOffDiag {n : ℕ} (hn : 2 ≤ n) (f : Fin n × Fin n → ℝ) (a : ℝ)
    (h : ∀ i j, i ≠ j → a ≤ f (i,j)) : a ≤ minOffDiag f := by
  simp only [minOffDiag, dif_pos (offDiag_nonempty hn)]
  apply Finset.le_inf'
  intro p hp
  exact h p.1 p.2 (Finset.mem_filter.mp hp).2

lemma minOffDiag_pos {n : ℕ} (hn : 2 ≤ n) (f : Fin n × Fin n → ℝ)
    (h : ∀ i j, i ≠ j → 0 < f (i,j)) : 0 < minOffDiag f := by
  rw [minOffDiag, dif_pos (offDiag_nonempty hn)]
  apply (Finset.lt_inf'_iff _).mpr
  intro p hp
  exact h p.1 p.2 (Finset.mem_filter.mp hp).2

lemma le_maxOffDiag {n : ℕ} (f : Fin n × Fin n → ℝ) (i j : Fin n)
    (hij : i ≠ j) : f (i,j) ≤ maxOffDiag f := by
  have h : (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2)).Nonempty :=
    ⟨(i,j), by simp [hij]⟩
  simp only [maxOffDiag, dif_pos h]
  exact Finset.le_sup' _ (by simp [hij])

lemma maxOffDiag_nonneg {n : ℕ} (hn : 2 ≤ n) (f : Fin n × Fin n → ℝ)
    (h : ∀ i j, 0 ≤ f (i,j)) : 0 ≤ maxOffDiag f := by
  obtain ⟨p, hp⟩ := offDiag_nonempty hn
  exact (h p.1 p.2).trans (le_maxOffDiag f p.1 p.2 (Finset.mem_filter.mp hp).2)

lemma le_maxIdx {n : ℕ} (f : Fin n → ℝ) (i : Fin n) : f i ≤ maxIdx f := by
  have h : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i, Finset.mem_univ i⟩
  simp only [maxIdx, dif_pos h]
  exact Finset.le_sup' _ (Finset.mem_univ i)

lemma maxIdx_le {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) (a : ℝ)
    (h : ∀ i, f i ≤ a) : maxIdx f ≤ a := by
  have hu : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn⟩, by simp⟩
  simp only [maxIdx, dif_pos hu]
  exact Finset.sup'_le _ _ (fun i _ => h i)

lemma maxIdx_lt {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) (a : ℝ)
    (h : ∀ i, f i < a) : maxIdx f < a := by
  have hu : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn⟩, by simp⟩
  rw [maxIdx, dif_pos hu]
  obtain ⟨i, _, he⟩ := Finset.exists_mem_eq_sup' hu f
  rw [he]
  exact h i

end NonuniformKuramoto.CondI.KUFresh


namespace NonuniformKuramoto.CondI.KUFresh

lemma sin_add_lower {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x + y ≤ Real.pi) : Real.sin (x+y) ≤ Real.sin x + Real.sin y := by
  have hsx := Real.sin_nonneg_of_nonneg_of_le_pi hx (by linarith : x ≤ Real.pi)
  have hsy := Real.sin_nonneg_of_nonneg_of_le_pi hy (by linarith : y ≤ Real.pi)
  have h1 := mul_nonneg hsx (sub_nonneg.mpr (Real.cos_le_one y))
  have h2 := mul_nonneg hsy (sub_nonneg.mpr (Real.cos_le_one x))
  rw [Real.sin_add]
  nlinarith

lemma arcsin_cohesive {c φ : ℝ} (hc : 0 ≤ c) (hφ : 0 ≤ φ)
    (hφp : φ < Real.pi/2) (hlt : c < Real.cos φ) :
    0 ≤ Real.arcsin c ∧ Real.arcsin c < Real.pi/2-φ ∧
    Real.pi/2 < Real.pi-Real.arcsin c ∧ Real.pi-Real.arcsin c ≤ Real.pi := by
  have hc1 : c < 1 := lt_of_lt_of_le hlt (Real.cos_le_one φ)
  have ha0 := Real.arcsin_nonneg.mpr hc
  have ha : Real.arcsin c < Real.pi/2-φ := (Real.arcsin_lt_iff_lt_sin (y := Real.pi/2-φ) ⟨by linarith, hc1.le⟩
    ⟨by linarith [Real.pi_pos], by linarith⟩).mpr (by simpa only [Real.sin_pi_div_two_sub] using hlt)
  exact ⟨ha0, ha, by linarith, by linarith⟩

lemma sin_between_arcsin {c v : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hlo : Real.arcsin c ≤ v) (hhi : v ≤ Real.pi-Real.arcsin c) : c ≤ Real.sin v := by
  have ha0 := Real.arcsin_nonneg.mpr hc
  by_cases hv : v ≤ Real.pi/2
  · exact (Real.arcsin_le_iff_le_sin ⟨by linarith, hc1.le⟩
      ⟨by linarith [Real.pi_pos], hv⟩).mp hlo
  · have hh : c ≤ Real.sin (Real.pi-v) :=
      (Real.arcsin_le_iff_le_sin ⟨by linarith, hc1.le⟩
        ⟨by linarith [Real.pi_pos], by linarith⟩).mp (by linarith)
    simpa using hh

lemma sin_between_arcsin_strict {c v : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (hlo : Real.arcsin c < v) (hhi : v < Real.pi-Real.arcsin c) : c < Real.sin v := by
  have ha0 := Real.arcsin_nonneg.mpr hc
  by_cases hv : v ≤ Real.pi/2
  · exact (Real.arcsin_lt_iff_lt_sin ⟨by linarith, hc1.le⟩
      ⟨by linarith [Real.pi_pos], hv⟩).mp hlo
  · have hh : c < Real.sin (Real.pi-v) :=
      (Real.arcsin_lt_iff_lt_sin ⟨by linarith, hc1.le⟩
        ⟨by linarith [Real.pi_pos], by linarith⟩).mp (by linarith)
    simpa using hh

end NonuniformKuramoto.CondI.KUFresh


namespace NonuniformKuramoto.CondI.KUFresh

lemma phi_bounds {n : ℕ} (hn : 2 ≤ n) (ϕ : Fin n → Fin n → ℝ)
    (hii : ∀ i, ϕ i i = 0)
    (hϕ : ∀ i j, i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi/2) :
    (∀ i j, 0 ≤ ϕ i j ∧ ϕ i j ≤ phiMax ϕ) ∧
    0 ≤ phiMax ϕ ∧ phiMax ϕ < Real.pi/2 := by
  have h0 : ∀ i j, 0 ≤ ϕ i j := by
    intro i j
    by_cases h : i=j
    · subst j; rw [hii]
    · exact (hϕ i j h).1
  have hp : ∀ i j, ϕ i j < Real.pi/2 := by
    intro i j
    by_cases h : i=j
    · subst j; rw [hii]; positivity
    · exact (hϕ i j h).2
  have hle : ∀ i j, ϕ i j ≤ phiMax ϕ := fun i j =>
    (le_maxIdx (ϕ i) j).trans (le_maxIdx (fun i => maxIdx (ϕ i)) i)
  refine ⟨fun i j => ⟨h0 i j, hle i j⟩, ?_, ?_⟩
  · let i : Fin n := ⟨0, by omega⟩
    exact (h0 i i).trans (hle i i)
  · exact maxIdx_lt (by omega) _ _ (fun i => maxIdx_lt (by omega) _ _ (hp i))

lemma native_coupling_guards {n : ℕ} (hn : 2 ≤ n) (D ω : Fin n → ℝ)
    (P ϕ : Fin n → Fin n → ℝ) (hD : ∀ i, 0 < D i)
    (hP : ∀ i j, i ≠ j → 0 < P i j) (hPii : ∀ i, P i i = 0)
    (hϕii : ∀ i, ϕ i i = 0)
    (hϕ : ∀ i j, i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi/2) :
    0 < GammaMin D P ϕ ∧ 0 ≤ omegaSpread D ω + 2*lossMax D P ϕ ∧
    Real.cos (phiMax ϕ)*GammaCrit D ω P ϕ = omegaSpread D ω+2*lossMax D P ϕ := by
  have hb := phi_bounds hn ϕ hϕii hϕ
  have hc : 0 < Real.cos (phiMax ϕ) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hb.2.2⟩
  have hmin : 0 < minOffDiag (fun p : Fin n × Fin n => P p.1 p.2 / D p.1 * Real.cos (ϕ p.1 p.2)) := by
    apply minOffDiag_pos hn
    intro i j hij
    exact mul_pos (div_pos (hP i j hij) (hD i))
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [(hϕ i j hij).1, Real.pi_pos], (hϕ i j hij).2⟩)
  have hw : 0 ≤ omegaSpread D ω := maxOffDiag_nonneg hn _ (fun _ _ => abs_nonneg _)
  have hl : 0 ≤ lossMax D P ϕ := by
    let i : Fin n := ⟨0, by omega⟩
    apply le_trans (b := ∑ j, P i j / D i * Real.sin (ϕ i j)) _ (le_maxIdx (fun i => ∑ j, P i j / D i * Real.sin (ϕ i j)) i)
    apply Finset.sum_nonneg
    intro j _
    by_cases hij : i=j
    · subst j; simp [hPii]
    · exact mul_nonneg (div_pos (hP i j hij) (hD i)).le
        (Real.sin_nonneg_of_nonneg_of_le_pi (hb.1 i j).1 (by linarith [(hb.1 i j).2, hb.2.2, Real.pi_pos]))
  refine ⟨by unfold GammaMin; positivity, by positivity, ?_⟩
  unfold GammaCrit
  field_simp [ne_of_gt hc]

lemma gamma_guards {n : ℕ} (hn : 2 ≤ n) (D ω : Fin n → ℝ)
    (P ϕ : Fin n → Fin n → ℝ) (hD : ∀ i, 0 < D i)
    (hP : ∀ i j, i ≠ j → 0 < P i j) (hPii : ∀ i, P i i = 0)
    (hϕii : ∀ i, ϕ i i = 0)
    (hϕ : ∀ i j, i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi/2)
    (h26 : GammaCrit D ω P ϕ < GammaMin D P ϕ) :
    0 ≤ gammaMin D ω P ϕ ∧ gammaMin D ω P ϕ < Real.pi/2-phiMax ϕ ∧
    Real.pi/2 < gammaMax D ω P ϕ ∧ gammaMax D ω P ϕ ≤ Real.pi := by
  have hb := phi_bounds hn ϕ hϕii hϕ
  have hg := native_coupling_guards hn D ω P ϕ hD hP hPii hϕii hϕ
  have hc : 0 < Real.cos (phiMax ϕ) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hb.2.2⟩
  exact arcsin_cohesive (by rw [hg.2.2]; exact div_nonneg hg.2.1 hg.1.le)
    hb.2.1 hb.2.2 ((div_lt_iff₀ hg.1).mpr (mul_lt_mul_of_pos_left h26 hc))

end NonuniformKuramoto.CondI.KUFresh


namespace NonuniformKuramoto.CondI.KUFresh

noncomputable def lossless {n : ℕ} (D : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (i j : Fin n) : ℝ := P i j / D i * Real.cos (ϕ i j)
noncomputable def lossy {n : ℕ} (D : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (i j : Fin n) : ℝ := P i j / D i * Real.sin (ϕ i j)

lemma field_expansion {n : ℕ} (D ω θ : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (i : Fin n) : field D ω P ϕ θ i = ω i / D i -
      ∑ j, (lossless D P ϕ i j * Real.sin (θ i-θ j) +
        lossy D P ϕ i j * Real.cos (θ i-θ j)) := by
  unfold field
  rw [sub_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.sin_add]
  unfold lossless lossy
  ring

lemma lossy_nonneg {n : ℕ} (hn : 2 ≤ n) (D : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (hD : ∀ i, 0 < D i) (hP : ∀ i j, i ≠ j → 0 < P i j)
    (hPii : ∀ i, P i i = 0) (hϕii : ∀ i, ϕ i i = 0)
    (hϕ : ∀ i j, i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi/2) (i j : Fin n) :
    0 ≤ lossy D P ϕ i j := by
  by_cases hij : i=j
  · subst j; simp [lossy, hPii]
  · have hb := phi_bounds hn ϕ hϕii hϕ
    exact mul_nonneg (div_pos (hP i j hij) (hD i)).le
      (Real.sin_nonneg_of_nonneg_of_le_pi (hb.1 i j).1
        (by linarith [(hb.1 i j).2, hb.2.2, Real.pi_pos]))

lemma extreme_field_bound {n : ℕ} (hn : 2 ≤ n) (D ω θ : Fin n → ℝ)
    (P ϕ : Fin n → Fin n → ℝ) (hD : ∀ i, 0 < D i)
    (hP : ∀ i j, i ≠ j → 0 < P i j) (hPii : ∀ i, P i i = 0)
    (hϕii : ∀ i, ϕ i i = 0)
    (hϕ : ∀ i j, i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi/2)
    (m l : Fin n) (hml : m ≠ l) (hm : ∀ j, θ j ≤ θ m) (hl : ∀ j, θ l ≤ θ j)
    (hv : θ m-θ l ≤ Real.pi) :
    field D ω P ϕ θ m-field D ω P ϕ θ l ≤
      omegaSpread D ω+2*lossMax D P ϕ-GammaMin D P ϕ*Real.sin (θ m-θ l) := by
  let a := minOffDiag (fun p : Fin n × Fin n => lossless D P ϕ p.1 p.2)
  have ha : 0 ≤ a := by
    apply le_minOffDiag hn
    intro i j hij
    exact (mul_pos (div_pos (hP i j hij) (hD i))
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [(hϕ i j hij).1, Real.pi_pos], (hϕ i j hij).2⟩)).le
  have hs (j : Fin n) : a*Real.sin (θ m-θ l) ≤
      lossless D P ϕ m j*Real.sin (θ m-θ j) +
      lossless D P ϕ l j*Real.sin (θ j-θ l) := by
    have hx := Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr (hm j)) (by linarith [hl j])
    have hy := Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr (hl j)) (by linarith [hm j])
    have hmj : a*Real.sin (θ m-θ j) ≤ lossless D P ϕ m j*Real.sin (θ m-θ j) := by
      by_cases h : m=j
      · subst j; simp
      · exact mul_le_mul_of_nonneg_right (minOffDiag_le _ m j h) hx
    have hlj : a*Real.sin (θ j-θ l) ≤ lossless D P ϕ l j*Real.sin (θ j-θ l) := by
      by_cases h : l=j
      · subst j; simp
      · exact mul_le_mul_of_nonneg_right (minOffDiag_le _ l j h) hy
    have hh := mul_le_mul_of_nonneg_left
      (sin_add_lower (sub_nonneg.mpr (hm j)) (sub_nonneg.mpr (hl j)) (by linarith)) ha
    have he : θ m-θ j+(θ j-θ l)=θ m-θ l := by ring
    rw [he] at hh
    nlinarith
  have hb (j : Fin n) :
      -(lossless D P ϕ m j*Real.sin (θ m-θ j)+lossy D P ϕ m j*Real.cos (θ m-θ j)) +
      (lossless D P ϕ l j*Real.sin (θ l-θ j)+lossy D P ϕ l j*Real.cos (θ l-θ j)) ≤
      -a*Real.sin (θ m-θ l)+lossy D P ϕ m j+lossy D P ϕ l j := by
    have h1 := lossy_nonneg hn D P ϕ hD hP hPii hϕii hϕ m j
    have h2 := lossy_nonneg hn D P ϕ hD hP hPii hϕii hϕ l j
    have h3 := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (θ m-θ j)) h1
    have h4 := mul_le_mul_of_nonneg_left (Real.cos_le_one (θ l-θ j)) h2
    have he : Real.sin (θ l-θ j) = -Real.sin (θ j-θ l) := by rw [← Real.sin_neg]; congr 1; ring
    rw [he]
    nlinarith [hs j]
  have ht := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hb j)
  have hw : ω m/D m-ω l/D l ≤ omegaSpread D ω :=
    (le_abs_self _).trans (le_maxOffDiag (fun p : Fin n×Fin n => |ω p.1/D p.1-ω p.2/D p.2|) m l hml)
  have hbm : (∑ j, lossy D P ϕ m j) ≤ lossMax D P ϕ := le_maxIdx (fun i => ∑ j, lossy D P ϕ i j) m
  have hbl : (∑ j, lossy D P ϕ l j) ≤ lossMax D P ϕ := le_maxIdx (fun i => ∑ j, lossy D P ϕ i j) l
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at ht
  rw [field_expansion, field_expansion]
  change _ ≤ _ - ((n:ℝ)*a)*_
  simp only [Finset.sum_add_distrib]
  nlinarith only [ht, hw, hbm, hbl]

end NonuniformKuramoto.CondI.KUFresh


namespace NonuniformKuramoto.CondI.KUFresh
open Set

lemma sine_boundary {A G v : ℝ} (hG : 0 < G) (hA : 0 ≤ A) (hc : A/G < 1)
    (hv : Real.arcsin (A/G) ≤ v ∧ v ≤ Real.pi-Real.arcsin (A/G)) :
    A-G*Real.sin v ≤ 0 := by
  have hh := sin_between_arcsin (div_nonneg hA hG.le) hc hv.1 hv.2
  have hh' := (div_le_iff₀ hG).mp hh
  nlinarith

lemma sine_interior {A G v : ℝ} (hG : 0 < G) (hA : 0 ≤ A) (hc : A/G < 1)
    (hv : Real.arcsin (A/G) < v ∧ v < Real.pi-Real.arcsin (A/G)) :
    A-G*Real.sin v < 0 := by
  have hh := sin_between_arcsin_strict (div_nonneg hA hG.le) hc hv.1 hv.2
  have hh' := (div_lt_iff₀ hG).mp hh
  nlinarith

lemma sine_uniform_gap {A G lo hi : ℝ} (hG : 0 < G) (hA : 0 ≤ A) (hc : A/G < 1)
    (hl : Real.arcsin (A/G) < lo) (hlh : lo ≤ hi)
    (hh : hi < Real.pi-Real.arcsin (A/G)) :
    ∃ η : ℝ, 0 < η ∧ ∀ v ∈ Icc lo hi, A-G*Real.sin v ≤ -η := by
  obtain ⟨v,hv,hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hlh)
    (show ContinuousOn (fun v : ℝ => A-G*Real.sin v) (Icc lo hi) by fun_prop)
  have hn := sine_interior hG hA hc ⟨hl.trans_le hv.1, hv.2.trans_lt hh⟩
  refine ⟨-(A-G*Real.sin v), by linarith, ?_⟩
  intro y hy
  simpa using hm hy

lemma native_sine_parameters {n : ℕ} (hn : 2 ≤ n) (D ω : Fin n → ℝ)
    (P ϕ : Fin n → Fin n → ℝ) (hD : ∀ i, 0 < D i)
    (hP : ∀ i j, i ≠ j → 0 < P i j) (hPii : ∀ i, P i i = 0)
    (hϕii : ∀ i, ϕ i i = 0)
    (hϕ : ∀ i j, i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi/2)
    (h26 : GammaCrit D ω P ϕ < GammaMin D P ϕ) :
    let A := omegaSpread D ω+2*lossMax D P ϕ
    let G := GammaMin D P ϕ
    0 < G ∧ 0 ≤ A ∧ A/G < 1 ∧
      gammaMin D ω P ϕ=Real.arcsin (A/G) ∧ gammaMax D ω P ϕ=Real.pi-Real.arcsin (A/G) := by
  dsimp only
  have hg := native_coupling_guards hn D ω P ϕ hD hP hPii hϕii hϕ
  have hb := phi_bounds hn ϕ hϕii hϕ
  have hc : 0 < Real.cos (phiMax ϕ) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hb.2.2⟩
  have ht : (omegaSpread D ω+2*lossMax D P ϕ)/GammaMin D P ϕ < Real.cos (phiMax ϕ) := by
    rw [← hg.2.2]
    exact (div_lt_iff₀ hg.1).mpr (mul_lt_mul_of_pos_left h26 hc)
  refine ⟨hg.1,hg.2.1,ht.trans_le (Real.cos_le_one _),?_,?_⟩
  · simp only [gammaMin, hg.2.2]
  · simp only [gammaMax, hg.2.2]

end NonuniformKuramoto.CondI.KUFresh

namespace NonuniformKuramoto.CondI.KUFresh
open Set
variable {n : ℕ} (hn : 2 ≤ n) (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (hD : ∀i,0 < D i) (hP : ∀i j,i ≠ j → 0 < P i j) (hPii : ∀i,P i i=0)
    (hϕii : ∀i,ϕ i i=0) (hϕ : ∀i j,i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi/2)
    (h26 : GammaCrit D ω P ϕ < GammaMin D P ϕ)
include hn hD hP hPii hϕii hϕ h26
lemma native_arc_invariant {γ : ℝ} (hγ : γ ∈ Icc (gammaMin D ω P ϕ) (gammaMax D ω P ϕ)) :
    IsPosInvariant D ω P ϕ (ArcClosed γ) := by
  let : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  have hg := gamma_guards hn D ω P ϕ hD hP hPii hϕii hϕ h26
  have hs := native_sine_parameters hn D ω P ϕ hD hP hPii hϕii hϕ h26
  apply arc_invariant_of_boundary D ω P ϕ (hg.1.trans hγ.1)
  intro v m l hml hm hl he
  have hb := extreme_field_bound hn D ω v P ϕ hD hP hPii hϕii hϕ m l hml hm hl
    (by rw [he]; exact hγ.2.trans hg.2.2.2)
  rw [he] at hb
  exact hb.trans (sine_boundary hs.1 hs.2.1 hs.2.2.1 ⟨hs.2.2.2.1 ▸ hγ.1,hs.2.2.2.2 ▸ hγ.2⟩)
lemma native_arc_entry (θ : ℝ → Fin n → ℝ) (hθ : IsSolution D ω P ϕ θ)
    (h0 : ArcOpen (gammaMax D ω P ϕ) (θ 0)) :
    ∀γ ∈ Ioc (gammaMin D ω P ϕ) (gammaMax D ω P ϕ),
      ∃T,0 ≤ T ∧ ∀t,T ≤ t → ArcClosed γ (θ t) := by
  let : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  have hg := gamma_guards hn D ω P ϕ hD hP hPii hϕii hϕ h26
  have hs := native_sine_parameters hn D ω P ϕ hD hP hPii hϕii hϕ h26
  have hv : diam (θ 0) < gammaMax D ω P ϕ := by
    obtain ⟨i,j,hij⟩ := diam_attained (θ 0)
    rw [← hij]
    exact h0 i j
  have hgm : gammaMin D ω P ϕ < gammaMax D ω P ϕ := by
    have hp := phi_bounds hn ϕ hϕii hϕ
    linarith [hg.2.1,hg.2.2.1,hp.2.1]
  obtain ⟨γ0,hlo,hhi⟩ := exists_between (max_lt hv hgm)
  have hinv0 := native_arc_invariant hn D ω P ϕ hD hP hPii hϕii hϕ h26
    (γ := γ0) ⟨(le_max_right _ _).trans hlo.le,hhi.le⟩
  have hu : ∀t,0 ≤ t → ArcClosed γ0 (θ t) :=
    hinv0 θ hθ (fun i j => (sub_le_diam _ i j).trans ((le_max_left _ _).trans hlo.le))
  intro γ hγ
  by_cases hh : γ0 ≤ γ
  · exact ⟨0,le_rfl,fun t ht i j => (hu t ht i j).trans hh⟩
  have hlt : γ < γ0 := lt_of_not_ge hh
  obtain ⟨η,hη,hgap⟩ := sine_uniform_gap hs.1 hs.2.1 hs.2.2.1
    (hs.2.2.2.1 ▸ hγ.1) hlt.le (hs.2.2.2.2 ▸ hhi)
  apply arc_entry_of_drift D ω P ϕ (hg.1.trans hγ.1.le) hη
    (native_arc_invariant hn D ω P ϕ hD hP hPii hϕii hϕ h26 ⟨hγ.1.le,hγ.2⟩) _ θ hθ hu
  intro v m l hml hm hl hlow hupp
  exact (extreme_field_bound hn D ω v P ϕ hD hP hPii hϕii hϕ m l hml hm hl
    (hupp.trans (hhi.le.trans hg.2.2.2))).trans (hgap _ ⟨hlow.le,hupp⟩)
end NonuniformKuramoto.CondI.KUFresh


namespace NonuniformKuramoto.CondI.KUFresh

noncomputable def frequencyCoeff {n : ℕ} (D θ : Fin n → ℝ)
    (P ϕ : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  P i j / D i * Real.cos (θ i-θ j+ϕ i j)

lemma frequency_derivative {n : ℕ} (D ω : Fin n → ℝ)
    (P ϕ : Fin n → Fin n → ℝ) (θ : ℝ → Fin n → ℝ)
    (hs : IsSolution D ω P ϕ θ) (t : ℝ) (ht : 0 ≤ t) (i : Fin n) :
    HasDerivWithinAt (fun s => field D ω P ϕ (θ s) i)
      (∑ j, frequencyCoeff D (θ t) P ϕ i j *
        (field D ω P ϕ (θ t) j-field D ω P ϕ (θ t) i)) (Set.Ici 0) t := by
  have hd (j : Fin n) := hasDerivWithinAt_pi.mp (hs t ht) j
  have hj (j : Fin n) := ((((hd i).sub (hd j)).add_const (ϕ i j)).sin.const_mul (P i j))
  have hh := ((HasDerivWithinAt.sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hj j)).const_sub (ω i)).div_const (D i)
  have he : (∑ j, frequencyCoeff D (θ t) P ϕ i j *
      (field D ω P ϕ (θ t) j-field D ω P ϕ (θ t) i)) =
      (-∑ j, P i j*(Real.cos (θ t i-θ t j+ϕ i j)*
        (field D ω P ϕ (θ t) i-field D ω P ϕ (θ t) j)))/D i := by
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    unfold frequencyCoeff
    ring
  rw [he]
  simpa only [field, Finset.sum_apply, Pi.sub_apply] using hh

lemma frequency_coeff_lower {n : ℕ} (D θ : Fin n → ℝ)
    (P ϕ : Fin n → Fin n → ℝ) (hD : ∀ i, 0 < D i)
    (hP : ∀ i j, i ≠ j → 0 < P i j)
    (φ γ : ℝ) (hφ : ∀ i j, 0 ≤ ϕ i j ∧ ϕ i j ≤ φ)
    (hγ : ArcClosed γ θ) (hc : γ+φ < Real.pi/2)
    (i j : Fin n) (hij : i ≠ j) :
    P i j / D i * Real.cos (γ+φ) ≤ frequencyCoeff D θ P ϕ i j := by
  have hi := hγ i j
  have hj := hγ j i
  have ha : |θ i-θ j+ϕ i j| ≤ γ+φ := by
    rw [abs_le]
    constructor <;> linarith [(hφ i j).1, (hφ i j).2]
  have hg0 : 0 ≤ γ+φ := (abs_nonneg _).trans ha
  have hcos := Real.strictAntiOn_cos.antitoneOn ⟨abs_nonneg _, ha.trans (by linarith [Real.pi_pos])⟩
    ⟨hg0, by linarith [Real.pi_pos]⟩ ha
  rw [Real.cos_abs] at hcos
  exact mul_le_mul_of_nonneg_left hcos (div_pos (hP i j hij) (hD i)).le

end NonuniformKuramoto.CondI.KUFresh


namespace NonuniformKuramoto.CondI.KUFresh

variable {I : Type*} [Fintype I]

noncomputable def consensusDrift (a : I → I → ℝ) (v : I → ℝ) (i : I) : ℝ :=
  ∑ j, a i j*(v j-v i)

lemma consensus_max_nonpos (a : I → I → ℝ) (v : I → ℝ)
    (ha : ∀ i j, i ≠ j → 0 ≤ a i j) (i : I) (hi : ∀ j, v j ≤ v i) :
    consensusDrift a v i ≤ 0 := by
  apply Finset.sum_nonpos
  intro j _
  by_cases h : i=j
  · subst j; simp
  · exact mul_nonpos_of_nonneg_of_nonpos (ha i j h) (sub_nonpos.mpr (hi j))

lemma consensus_min_nonneg (a : I → I → ℝ) (v : I → ℝ)
    (ha : ∀ i j, i ≠ j → 0 ≤ a i j) (i : I) (hi : ∀ j, v i ≤ v j) :
    0 ≤ consensusDrift a v i := by
  apply Finset.sum_nonneg
  intro j _
  by_cases h : i=j
  · subst j; simp
  · exact mul_nonneg (ha i j h) (sub_nonneg.mpr (hi j))

lemma consensus_pair_bound (a : I → I → ℝ) (v : I → ℝ) (c : ℝ)
    (ha : ∀ i j, i ≠ j → c ≤ a i j) (i l : I)
    (hi : ∀ j, v j ≤ v i) (hl : ∀ j, v l ≤ v j) :
    consensusDrift a v i-consensusDrift a v l ≤
      -((Fintype.card I:ℝ)*c)*(v i-v l) := by
  have hh (j : I) : a i j*(v j-v i)-a l j*(v j-v l) ≤ -c*(v i-v l) := by
    have h1 : a i j*(v j-v i) ≤ c*(v j-v i) := by
      by_cases h : i=j
      · subst j; simp
      · exact mul_le_mul_of_nonpos_right (ha i j h) (sub_nonpos.mpr (hi j))
    have h2 : c*(v j-v l) ≤ a l j*(v j-v l) := by
      by_cases h : l=j
      · subst j; simp
      · exact mul_le_mul_of_nonneg_right (ha l j h) (sub_nonneg.mpr (hl j))
    linarith
  have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) => hh j)
  simpa only [consensusDrift, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_neg, neg_mul, mul_assoc] using h

end NonuniformKuramoto.CondI.KUFresh


namespace NonuniformKuramoto.CondI.KUFresh
open Set
variable {I : Type*} [Fintype I] [Nonempty I]

lemma peak_antitone_of_active_deriv (v d : ℝ → I → ℝ)
    (hd : ∀ t, 0 ≤ t → ∀ i, HasDerivWithinAt (fun s => v s i) (d t i) (Ici 0) t)
    (hb : ∀ t, 0 ≤ t → ∀ i, v t i=peak (v t) → d t i ≤ 0) :
    AntitoneOn (fun t => peak (v t)) (Ici 0) := by
  have hv : ContinuousOn v (Ici 0) := fun t ht =>
    (hasDerivWithinAt_pi.mpr (hd t ht)).continuousWithinAt
  intro a ha b hb' hab
  have h := upperSlope_linear (a := a) (b := b) (c := 0)
    ((continuous_peak.comp_continuousOn hv).mono (fun t ht => le_trans ha ht.1))
    (by
      intro t ht
      apply peak_upperSlope (fun i s => v s i) (d t) t 0
      · intro i
        exact (hd t (le_trans ha ht.1) i).mono (fun s hs => le_trans (le_trans ha ht.1) hs)
      · exact hb t (le_trans ha ht.1)) b ⟨hab, le_rfl⟩
  simpa using h

lemma consensus_extrema_monotone (v : ℝ → I → ℝ) (a : ℝ → I → I → ℝ)
    (hd : ∀ t, 0 ≤ t → ∀ i, HasDerivWithinAt (fun s => v s i)
      (consensusDrift (a t) (v t) i) (Ici 0) t)
    (ha : ∀ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ a t i j) :
    AntitoneOn (fun t => peak (v t)) (Ici 0) ∧
    MonotoneOn (fun t => -peak (fun i => -v t i)) (Ici 0) := by
  constructor
  · apply peak_antitone_of_active_deriv v (fun t => consensusDrift (a t) (v t)) hd
    intro t ht i hi
    apply consensus_max_nonpos _ _ (ha t ht) i
    intro j
    rw [hi]
    exact le_peak _ j
  · have h := peak_antitone_of_active_deriv (fun t i => -v t i)
      (fun t i => -consensusDrift (a t) (v t) i)
      (fun t ht i => (hd t ht i).neg) (by
        intro t ht i hi
        apply neg_nonpos.mpr
        apply consensus_min_nonneg _ _ (ha t ht) i
        intro j
        have hh := le_peak (fun i => -v t i) j
        rw [← hi] at hh
        linarith)
    intro x hx y hy hxy
    exact neg_le_neg (h hx hy hxy)

lemma consensus_diameter_decay (v : ℝ → I → ℝ) (a : ℝ → I → I → ℝ)
    (c : ℝ) (hd : ∀ t, 0 ≤ t → ∀ i, HasDerivWithinAt (fun s => v s i)
      (consensusDrift (a t) (v t) i) (Ici 0) t)
    (ha : ∀ t, 0 ≤ t → ∀ i j, i ≠ j → c ≤ a t i j) :
    ∀ t, 0 ≤ t → diam (v t) ≤ diam (v 0)*Real.exp (-((Fintype.card I:ℝ)*c)*t) := by
  let r : ℝ := (Fintype.card I:ℝ)*c
  let w (t : ℝ) (p : I×I) := Real.exp (r*t)*(v t p.1-v t p.2)
  let dw (t : ℝ) (p : I×I) := Real.exp (r*t)*
    (r*(v t p.1-v t p.2)+consensusDrift (a t) (v t) p.1-consensusDrift (a t) (v t) p.2)
  have hw : ∀ t, 0 ≤ t → ∀ p, HasDerivWithinAt (fun s => w s p) (dw t p) (Ici 0) t := by
    intro t ht p
    have hh : HasDerivWithinAt (fun s => Real.exp (r*s)*(v s p.1-v s p.2))
        ((Real.exp (r*t)*r)*(v t p.1-v t p.2)+Real.exp (r*t)*
          (consensusDrift (a t) (v t) p.1-consensusDrift (a t) (v t) p.2)) (Ici 0) t :=
      by
        have hh0 := ((((hasDerivAt_id t).const_mul r).exp.hasDerivWithinAt).mul
          ((hd t ht p.1).sub (hd t ht p.2)))
        simp only [id_eq, mul_one, Pi.sub_apply] at hh0
        convert hh0 using 1 <;> rfl
    convert hh using 1
    dsimp [dw]
    ring
  have hm := peak_antitone_of_active_deriv w dw hw (by
    intro t ht p hp
    have he := Real.exp_pos (r*t)
    have hmax (j : I) : v t j ≤ v t p.1 := by
      have hh := le_peak (w t) (j,p.2)
      rw [← hp] at hh
      dsimp [w] at hh
      nlinarith
    have hmin (j : I) : v t p.2 ≤ v t j := by
      have hh := le_peak (w t) (p.1,j)
      rw [← hp] at hh
      dsimp [w] at hh
      nlinarith
    have hh := consensus_pair_bound (a t) (v t) c (ha t ht) p.1 p.2 hmax hmin
    apply mul_nonpos_of_nonneg_of_nonpos he.le
    dsimp [r]
    linarith)
  intro t ht
  obtain ⟨i,j,hij⟩ := diam_attained (v t)
  have h := (le_peak (w t) (i,j)).trans (hm (by simp) ht ht)
  have h0 : peak (w 0)=diam (v 0) := by simp only [w, mul_zero, Real.exp_zero, one_mul]; rfl
  change w t (i,j) ≤ peak (w 0) at h
  rw [h0] at h
  change Real.exp (r*t)*(v t i-v t j) ≤ _ at h
  rw [hij] at h
  have hh := mul_le_mul_of_nonneg_left h (Real.exp_pos (-r*t)).le
  have he : Real.exp (-r*t)*Real.exp (r*t)=1 := by rw [← Real.exp_add]; simp
  rw [← mul_assoc, he, one_mul] at hh
  simpa only [mul_comm (Real.exp (-r*t)), r] using hh

end NonuniformKuramoto.CondI.KUFresh


namespace NonuniformKuramoto.CondI.KUFresh
open Set
variable {I : Type*} [Fintype I] [Nonempty I]

lemma trough_le (v : I → ℝ) (i : I) : -peak (fun j => -v j) ≤ v i := by
  have h := le_peak (fun j => -v j) i
  linarith

lemma trough_le_peak (v : I → ℝ) : -peak (fun j => -v j) ≤ peak v := by
  let i : I := Classical.choice (inferInstance : Nonempty I)
  exact (trough_le v i).trans (le_peak v i)

lemma abs_sub_le_diam_of_bracket (v : I → ℝ) (b : ℝ)
    (hl : -peak (fun j => -v j) ≤ b) (hu : b ≤ peak v) (i : I) :
    |v i-b| ≤ diam v := by
  obtain ⟨j,hj⟩ := peak_attained v
  obtain ⟨l,hl'⟩ := peak_attained (fun j => -v j)
  have h1 := sub_le_diam v i l
  have h2 := sub_le_diam v j i
  rw [← hj] at hu
  rw [← hl'] at hl
  rw [abs_le]
  constructor <;> linarith

lemma exists_consensus_limit (v : ℝ → I → ℝ) (a : ℝ → I → I → ℝ)
    (c : ℝ) (hc : 0 < c)
    (hd : ∀ t, 0 ≤ t → ∀ i, HasDerivWithinAt (fun s => v s i)
      (consensusDrift (a t) (v t) i) (Ici 0) t)
    (ha : ∀ t, 0 ≤ t → ∀ i j, i ≠ j → c ≤ a t i j) :
    ∃ b : ℝ, (∀ t, 0 ≤ t → -peak (fun i => -v t i) ≤ b ∧ b ≤ peak (v t)) ∧
      ∀ t, 0 ≤ t → ∀ i, |v t i-b| ≤ diam (v 0)*Real.exp (-((Fintype.card I:ℝ)*c)*t) := by
  have hm := consensus_extrema_monotone v a hd (fun t ht i j hij => hc.le.trans (ha t ht i j hij))
  let low (t : ℝ) := -peak (fun i => -v t i)
  let S : Set ℝ := {b | ∃ t : ℝ, 0 ≤ t ∧ b=low t}
  have hS : S.Nonempty := ⟨low 0, 0, le_rfl, rfl⟩
  have hB : BddAbove S := by
    refine ⟨peak (v 0), ?_⟩
    rintro b ⟨t,ht,rfl⟩
    exact (trough_le_peak (v t)).trans (hm.1 (by simp) ht ht)
  have hb (t : ℝ) (ht : 0 ≤ t) : low t ≤ sSup S ∧ sSup S ≤ peak (v t) := by
    refine ⟨le_csSup hB ⟨t,ht,rfl⟩, csSup_le hS ?_⟩
    rintro b ⟨s,hs,rfl⟩
    rcases le_total s t with hst|hts
    · exact (hm.2 hs ht hst).trans (trough_le_peak (v t))
    · exact (trough_le_peak (v s)).trans (hm.1 ht hs hts)
  refine ⟨sSup S, hb, ?_⟩
  intro t ht i
  exact (abs_sub_le_diam_of_bracket (v t) (sSup S) (hb t ht).1 (hb t ht).2 i).trans
    (consensus_diameter_decay v a c hd ha t ht)

end NonuniformKuramoto.CondI.KUFresh


namespace NonuniformKuramoto.CondI.KUFresh
open Set

lemma cohesive_solution_synchronizes {n : ℕ} (hn : 2 ≤ n) (D ω : Fin n → ℝ)
    (P ϕ : Fin n → Fin n → ℝ) (hD : ∀ i, 0 < D i)
    (hP : ∀ i j, i ≠ j → 0 < P i j) (hϕii : ∀ i, ϕ i i = 0)
    (hϕ : ∀ i j, i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi/2)
    (θ : ℝ → Fin n → ℝ) (hs : IsSolution D ω P ϕ θ)
    (γ : ℝ) (hc : γ+phiMax ϕ < Real.pi/2)
    (hγ : ∀ t, 0 ≤ t → ArcClosed γ (θ t)) :
    ∃ b C r : ℝ, 0 < r ∧
      (∀ t, 0 ≤ t → ∀ i, |field D ω P ϕ (θ t) i-b| ≤ C*Real.exp (-r*t)) ∧
      (∀ t, 0 ≤ t → (∃ i, field D ω P ϕ (θ t) i ≤ b) ∧
        (∃ i, b ≤ field D ω P ϕ (θ t) i)) := by
  let : NeZero n := ⟨by omega⟩
  let v (t : ℝ) := field D ω P ϕ (θ t)
  let a (t : ℝ) := frequencyCoeff D (θ t) P ϕ
  let c : ℝ := minOffDiag (fun p : Fin n×Fin n => P p.1 p.2/D p.1)*Real.cos (γ+phiMax ϕ)
  have hp := phi_bounds hn ϕ hϕii hϕ
  have hg0 : 0 ≤ γ := by
    let i : Fin n := ⟨0,by omega⟩
    simpa using hγ 0 le_rfl i i
  have hcos : 0 < Real.cos (γ+phiMax ϕ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hp.2.1, Real.pi_pos], hc⟩
  have hc0 : 0 < c := mul_pos
    (minOffDiag_pos hn _ (fun i j hij => div_pos (hP i j hij) (hD i))) hcos
  have ha : ∀ t, 0 ≤ t → ∀ i j, i ≠ j → c ≤ a t i j := by
    intro t ht i j hij
    exact (mul_le_mul_of_nonneg_right (minOffDiag_le _ i j hij) hcos.le).trans
      (frequency_coeff_lower D (θ t) P ϕ hD hP (phiMax ϕ) γ hp.1 (hγ t ht) hc i j hij)
  have hd : ∀ t, 0 ≤ t → ∀ i, HasDerivWithinAt (fun s => v s i)
      (consensusDrift (a t) (v t) i) (Ici 0) t := fun t ht i => frequency_derivative D ω P ϕ θ hs t ht i
  obtain ⟨b,hb,he⟩ := exists_consensus_limit v a c hc0 hd ha
  refine ⟨b,diam (v 0),(n:ℝ)*c,by positivity,?_,?_⟩
  · simpa only [Fintype.card_fin] using he
  · intro t ht
    obtain ⟨i,hi⟩ := peak_attained (fun i => -v t i)
    obtain ⟨j,hj⟩ := peak_attained (v t)
    refine ⟨⟨i,?_⟩,⟨j,?_⟩⟩
    · have hh := (hb t ht).1
      rw [← hi] at hh
      simpa [v] using hh
    · have hh := (hb t ht).2
      rw [← hj] at hh
      exact hh

lemma field_uniform_bound {n : ℕ} (hn : 0 < n) (D ω : Fin n → ℝ)
    (P ϕ : Fin n → Fin n → ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ θ : Fin n → ℝ, ∀ i, |field D ω P ϕ θ i| ≤ M := by
  let B (i : Fin n) : ℝ := (|ω i|+∑ j, |P i j|)/|D i|
  refine ⟨maxIdx B,?_,?_⟩
  · let i : Fin n := ⟨0,hn⟩
    exact (by dsimp [B]; positivity : 0 ≤ B i).trans (le_maxIdx B i)
  · intro θ i
    apply le_trans _ (le_maxIdx B i)
    unfold field
    rw [abs_div]
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    calc
      |ω i-∑ j,P i j*Real.sin (θ i-θ j+ϕ i j)| ≤ |ω i|+|∑ j,P i j*Real.sin (θ i-θ j+ϕ i j)| := abs_sub _ _
      _ ≤ |ω i|+∑ j,|P i j*Real.sin (θ i-θ j+ϕ i j)| := add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ |ω i|+∑ j,|P i j| := by
        apply add_le_add le_rfl
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

end NonuniformKuramoto.CondI.KUFresh


namespace NonuniformKuramoto.CondI.KUFresh
open Filter Topology

lemma exponential_converges {f : ℝ → ℝ} {b C r : ℝ} (hr : 0 < r)
    (h : ∀ t, 0 ≤ t → |f t-b| ≤ C*Real.exp (-r*t)) : Tendsto f atTop (𝓝 b) := by
  have he : Tendsto (fun t : ℝ => C*Real.exp (-r*t)) atTop (𝓝 0) := by
    have ht : Tendsto (fun t : ℝ => r*t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hr tendsto_id
    simpa only [Function.comp_def, neg_mul, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul C
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun t => (dist_nonneg : 0 ≤ dist (f t) b))) _ he
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  simpa only [Real.dist_eq] using h t ht

lemma exponential_limit_unique {f : ℝ → ℝ} {b b' C C' r r' : ℝ}
    (hr : 0 < r) (hr' : 0 < r')
    (h : ∀ t, 0 ≤ t → |f t-b| ≤ C*Real.exp (-r*t))
    (h' : ∀ t, 0 ≤ t → |f t-b'| ≤ C'*Real.exp (-r'*t)) : b=b' :=
  tendsto_nhds_unique (exponential_converges hr h) (exponential_converges hr' h')

end NonuniformKuramoto.CondI.KUFresh


namespace NonuniformKuramoto.CondI.KUFresh

lemma exponential_tail_extension {I : Type*} (f : ℝ → I → ℝ)
    (b M C r T : ℝ) (hM : 0 ≤ M) (hr : 0 < r) (hT : 0 ≤ T)
    (hf : ∀ t, 0 ≤ t → ∀ i, |f t i| ≤ M)
    (hb : (∃ i, f T i ≤ b) ∧ (∃ i, b ≤ f T i))
    (htail : ∀ s, 0 ≤ s → ∀ i, |f (T+s) i-b| ≤ C*Real.exp (-r*s)) :
    ∃ C' : ℝ, ∀ t, 0 ≤ t → ∀ i, |f t i-b| ≤ C'*Real.exp (-r*t) := by
  have hbn : |b| ≤ M := by
    obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := hb
    rw [abs_le]
    have h1 := (abs_le.mp (hf T hT i)).1
    have h2 := (abs_le.mp (hf T hT j)).2
    constructor <;> linarith
  let K : ℝ := max (2*M) C
  have hK : 0 ≤ K := le_trans (by positivity) (le_max_left _ _)
  refine ⟨K*Real.exp (r*T), ?_⟩
  intro t ht i
  have he : (K*Real.exp (r*T))*Real.exp (-r*t) = K*Real.exp (-r*(t-T)) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he]
  by_cases hlate : T ≤ t
  · have hh := htail (t-T) (sub_nonneg.mpr hlate) i
    have heq : T+(t-T)=t := by ring
    rw [heq] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
  · have hh : |f t i-b| ≤ 2*M := by
      exact (abs_sub _ _).trans (by linarith [hf t ht i])
    have hex : 1 ≤ Real.exp (-r*(t-T)) := Real.one_le_exp_iff.mpr (by nlinarith)
    exact hh.trans ((le_max_left _ _).trans (by nlinarith))

end NonuniformKuramoto.CondI.KUFresh

namespace NonuniformKuramoto.CondI.KUFresh
open Set
lemma native_synchronization {n : ℕ} (hn : 2 ≤ n) (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (hD : ∀i,0 < D i) (hP : ∀i j,i ≠ j → 0 < P i j) (hPii : ∀i,P i i=0)
    (hϕii : ∀i,ϕ i i=0) (hϕ : ∀i j,i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi/2)
    (h26 : GammaCrit D ω P ϕ < GammaMin D P ϕ)
    (θ : ℝ → Fin n → ℝ) (hθ : IsSolution D ω P ϕ θ)
    (h0 : ArcOpen (gammaMax D ω P ϕ) (θ 0)) :
    ∃ b C r : ℝ,0 < r ∧
      (∀t,0 ≤ t → ∀i,|field D ω P ϕ (θ t) i-b| ≤ C*Real.exp (-r*t)) ∧
      (ArcOpen (Real.pi/2-phiMax ϕ) (θ 0) →
        (∃i,field D ω P ϕ (θ 0) i ≤ b) ∧ (∃i,b ≤ field D ω P ϕ (θ 0) i)) := by
  let : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  have hg := gamma_guards hn D ω P ϕ hD hP hPii hϕii hϕ h26
  have hp := phi_bounds hn ϕ hϕii hϕ
  obtain ⟨γ,hγlo,hγhi⟩ := exists_between hg.2.1
  have hγmax : γ ≤ gammaMax D ω P ϕ := by linarith [hp.2.1,hg.2.2.1]
  obtain ⟨T,hT,hentry⟩ := native_arc_entry hn D ω P ϕ hD hP hPii hϕii hϕ h26 θ hθ h0 γ ⟨hγlo,hγmax⟩
  obtain ⟨b,C,r,hr,htail,hbracket⟩ := cohesive_solution_synchronizes hn D ω P ϕ hD hP hϕii hϕ
    (fun s => θ (T+s)) (solution_shift hθ hT) γ (by linarith)
    (fun s hs => hentry (T+s) (by linarith))
  obtain ⟨M,hM,hMbound⟩ := field_uniform_bound (by omega : 0 < n) D ω P ϕ
  obtain ⟨C',hglobal⟩ := exponential_tail_extension (fun t => field D ω P ϕ (θ t)) b M C r T hM hr hT
    (fun t _ i => hMbound (θ t) i) (by simpa only [add_zero] using hbracket 0 le_rfl) htail
  refine ⟨b,C',r,hr,hglobal,?_⟩
  intro hinit
  have hv : diam (θ 0) < Real.pi/2-phiMax ϕ := by
    obtain ⟨i,j,hij⟩ := diam_attained (θ 0)
    rw [← hij]
    exact hinit i j
  obtain ⟨γ',hlo,hhi⟩ := exists_between (max_lt hv hg.2.1)
  have hh : γ' ∈ Icc (gammaMin D ω P ϕ) (gammaMax D ω P ϕ) :=
    ⟨(le_max_right _ _).trans hlo.le,by linarith [hp.2.1,hg.2.2.1]⟩
  have hinv := native_arc_invariant hn D ω P ϕ hD hP hPii hϕii hϕ h26 hh
  have hstart : ArcClosed γ' (θ 0) := fun i j =>
    (sub_le_diam _ i j).trans ((le_max_left _ _).trans hlo.le)
  obtain ⟨b',C'',r',hr',he',hb'⟩ := cohesive_solution_synchronizes hn D ω P ϕ hD hP hϕii hϕ
    θ hθ γ' (by linarith) (hinv θ hθ hstart)
  let i : Fin n := ⟨0,by omega⟩
  have heq : b=b' := exponential_limit_unique hr hr' (fun t ht => hglobal t ht i) (fun t ht => he' t ht i)
  rw [heq]
  exact hb' 0 le_rfl
end NonuniformKuramoto.CondI.KUFresh

namespace NonuniformKuramoto.CondI.KUFresh
theorem native_theorem_V_3 {n : ℕ} (hn : 2 ≤ n) (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (hD : ∀ i, 0 < D i) (hPsymm : ∀ i j, P i j = P j i)
    (hP : ∀ i j, i ≠ j → 0 < P i j) (hPii : ∀ i, P i i = 0) (hϕii : ∀ i, ϕ i i = 0)
    (hϕ : ∀ i j, i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi / 2)
    (h26 : GammaCrit D ω P ϕ < GammaMin D P ϕ) :
    (∀ γ ∈ Set.Icc (gammaMin D ω P ϕ) (gammaMax D ω P ϕ),
      IsPosInvariant D ω P ϕ (ArcClosed γ)) ∧
    ∀ θ : ℝ → Fin n → ℝ, IsSolution D ω P ϕ θ → ArcOpen (gammaMax D ω P ϕ) (θ 0) →
      (∀ γ ∈ Set.Ioc (gammaMin D ω P ϕ) (gammaMax D ω P ϕ),
        ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ArcClosed γ (θ t)) ∧
      ∃ ωinf C r : ℝ, 0 < r ∧
        (∀ t : ℝ, 0 ≤ t → ∀ i, |field D ω P ϕ (θ t) i - ωinf| ≤ C * Real.exp (-r * t)) ∧
        (ArcOpen (Real.pi / 2 - phiMax ϕ) (θ 0) →
          (∃ i, field D ω P ϕ (θ 0) i ≤ ωinf) ∧ (∃ i, ωinf ≤ field D ω P ϕ (θ 0) i)) := by
  have _hPsymm := hPsymm
  refine ⟨?_,?_⟩
  · intro γ hγ
    exact native_arc_invariant hn D ω P ϕ hD hP hPii hϕii hϕ h26 hγ
  · intro θ hθ h0
    exact ⟨native_arc_entry hn D ω P ϕ hD hP hPii hϕii hϕ h26 θ hθ h0,
      native_synchronization hn D ω P ϕ hD hP hPii hϕii hϕ h26 θ hθ h0⟩
end NonuniformKuramoto.CondI.KUFresh

namespace NonuniformKuramoto.CondI

/-- Theorem V.3 (Synchronization condition I), pp. 19–20, with the two printed clauses that are false
as stated replaced by their corrected forms (see the item's Formalization Note):
1) `∆̄(γ)` is positively invariant for every `γ ∈ [γ_min, γ_max]`, and every solution with
   `θ(0) ∈ ∆(γ_max)` enters and stays in `∆̄(γ)` for every `γ ∈ ]γ_min, γ_max]` (asymptotic reading of
   "reaches `∆̄(γ_min)`");
2) every solution with `θ(0) ∈ ∆(γ_max)` achieves exponential frequency synchronization to some
   `θ̇_∞`, and `θ̇_∞ ∈ [θ̇_min(0), θ̇_max(0)]` whenever moreover `θ(0) ∈ ∆(π/2 − ϕ_max)`. -/
theorem theorem_V_3 {n : ℕ} (hn : 2 ≤ n) (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (hD : ∀ i, 0 < D i) (hPsymm : ∀ i j, P i j = P j i)
    (hP : ∀ i j, i ≠ j → 0 < P i j) (hPii : ∀ i, P i i = 0) (hϕii : ∀ i, ϕ i i = 0)
    (hϕ : ∀ i j, i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi / 2)
    (h26 : GammaCrit D ω P ϕ < GammaMin D P ϕ) :
    (∀ γ ∈ Set.Icc (gammaMin D ω P ϕ) (gammaMax D ω P ϕ),
      IsPosInvariant D ω P ϕ (ArcClosed γ)) ∧
    ∀ θ : ℝ → Fin n → ℝ, IsSolution D ω P ϕ θ → ArcOpen (gammaMax D ω P ϕ) (θ 0) →
      (∀ γ ∈ Set.Ioc (gammaMin D ω P ϕ) (gammaMax D ω P ϕ),
        ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ArcClosed γ (θ t)) ∧
      ∃ ωinf C r : ℝ, 0 < r ∧
        (∀ t : ℝ, 0 ≤ t → ∀ i, |field D ω P ϕ (θ t) i - ωinf| ≤ C * Real.exp (-r * t)) ∧
        (ArcOpen (Real.pi / 2 - phiMax ϕ) (θ 0) →
          (∃ i, field D ω P ϕ (θ 0) i ≤ ωinf) ∧ (∃ i, ωinf ≤ field D ω P ϕ (θ 0) i)) := by
  exact KUFresh.native_theorem_V_3 hn D ω P ϕ hD hPsymm hP hPii hϕii hϕ h26

end NonuniformKuramoto.CondI

open NonuniformKuramoto.CondI
theorem solution {n : ℕ} (hn : 2 ≤ n) (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (hD : ∀ i, 0 < D i) (hPsymm : ∀ i j, P i j = P j i)
    (hP : ∀ i j, i ≠ j → 0 < P i j) (hPii : ∀ i, P i i = 0) (hϕii : ∀ i, ϕ i i = 0)
    (hϕ : ∀ i j, i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi / 2)
    (h26 : GammaCrit D ω P ϕ < GammaMin D P ϕ) :
    (∀ γ ∈ Set.Icc (gammaMin D ω P ϕ) (gammaMax D ω P ϕ),
      IsPosInvariant D ω P ϕ (ArcClosed γ)) ∧
    ∀ θ : ℝ → Fin n → ℝ, IsSolution D ω P ϕ θ → ArcOpen (gammaMax D ω P ϕ) (θ 0) →
      (∀ γ ∈ Set.Ioc (gammaMin D ω P ϕ) (gammaMax D ω P ϕ),
        ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ArcClosed γ (θ t)) ∧
      ∃ ωinf C r : ℝ, 0 < r ∧
        (∀ t : ℝ, 0 ≤ t → ∀ i, |field D ω P ϕ (θ t) i - ωinf| ≤ C * Real.exp (-r * t)) ∧
        (ArcOpen (Real.pi / 2 - phiMax ϕ) (θ 0) →
          (∃ i, field D ω P ϕ (θ 0) i ≤ ωinf) ∧ (∃ i, ωinf ≤ field D ω P ϕ (θ 0) i)) := by
  exact NonuniformKuramoto.CondI.theorem_V_3 hn D ω P ϕ hD hPsymm hP hPii hϕii hϕ h26
