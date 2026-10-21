-- Prove2me | solution 1 for MatchCongestion.Welfare.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:38:31.62971+00:00
-- url     : https://prove2.me/submissions/0239a8d1-d5e7-4f87-984c-7ae9e170cf20

import Mathlib
import Definitions.Def_MatchCongestion_Welfare_Setting

set_option autoImplicit false
open MatchCongestion.Welfare

theorem mcE_exp_lt_one {x : ℝ} (h : x < 0) : Real.exp x < 1 := by
  simpa using Real.exp_lt_exp.mpr h

theorem mcE_one_sub_pos {x : ℝ} (h : 0 < x) : 0 < 1 - Real.exp (-x) := by
  have := mcE_exp_lt_one (show -x < 0 by linarith); linarith

theorem mcE_pos (x : ℝ) : 0 < E x := by
  unfold E
  split_ifs with h
  · exact one_pos
  · rcases lt_or_gt_of_ne h with hx | hx
    · have h1 : 1 < Real.exp (-x) := by
        simpa using Real.exp_lt_exp.mpr (show 0 < -x by linarith)
      exact div_pos_of_neg_of_neg (by linarith) hx
    · exact div_pos (mcE_one_sub_pos hx) hx

theorem mcE_of_pos {x : ℝ} (h : 0 < x) : E x = (1 - Real.exp (-x)) / x := by
  unfold E; rw [if_neg h.ne']

theorem mcE_zero : E 0 = 1 := by simp [E]

theorem mcE_mul (x : ℝ) : E x * x = 1 - Real.exp (-x) := by
  unfold E
  split_ifs with h
  · subst h; simp
  · field_simp

theorem mcE_anti {x z : ℝ} (hx : 0 < x) (hxz : x < z) : E z < E x := by
  have hz : 0 < z := hx.trans hxz
  rw [mcE_of_pos hx, mcE_of_pos hz, div_lt_div_iff₀ hz hx]
  have hc := strictConvexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-z))
    (by intro h; linarith) (show 0 < 1 - x / z by
      rw [sub_pos, div_lt_one hz]; exact hxz) (show 0 < x / z from div_pos hx hz)
    (by ring)
  simp only [smul_eq_mul, Real.exp_zero, mul_one, mul_zero, zero_add] at hc
  have e : x / z * -z = -x := by field_simp
  rw [e] at hc
  have := mul_lt_mul_of_pos_left hc hz
  have e2 : z * ((1 - x / z) + x / z * Real.exp (-z)) = z - x + x * Real.exp (-z) := by
    field_simp
  rw [e2] at this
  nlinarith
noncomputable def mcf (A r s : ℝ) : ℝ := 1 - Real.exp (-(A * s * (1 - s))) - r * s

theorem mcf_concave (A r : ℝ) (hA : 0 ≤ A) : ConcaveOn ℝ Set.univ (mcf A r) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hb' : b = 1 - a := by linarith
  subst hb'
  simp only [smul_eq_mul, mcf]
  have hq : A * (a * x + (1 - a) * y) ^ 2 - A * (a * x + (1 - a) * y) ≤
      a * (A * x ^ 2 - A * x) + (1 - a) * (A * y ^ 2 - A * y) := by
    have : a * (A * x ^ 2 - A * x) + (1 - a) * (A * y ^ 2 - A * y)
        - (A * (a * x + (1 - a) * y) ^ 2 - A * (a * x + (1 - a) * y))
        = A * (a * (1 - a) * (x - y) ^ 2) := by ring
    have h2 : 0 ≤ A * (a * (1 - a) * (x - y) ^ 2) := by
      apply mul_nonneg hA; apply mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
    linarith
  have h1 := Real.exp_le_exp.mpr hq
  have h2 := convexOn_exp.2 (Set.mem_univ (A * x ^ 2 - A * x)) (Set.mem_univ (A * y ^ 2 - A * y))
    ha hb (by ring : a + (1 - a) = 1)
  simp only [smul_eq_mul] at h2
  have e : ∀ s : ℝ, -(A * s * (1 - s)) = A * s ^ 2 - A * s := fun s => by ring
  simp only [e]
  nlinarith

theorem mcf_pos_small (A r : ℝ) (hr : 0 < r) (hrA : r < A) (s : ℝ) (hs : 0 < s)
    (hσ : s < (A - r) / (A * (1 + r))) : 0 < mcf A r s := by
  have hA : 0 < A := hr.trans hrA
  have hAr : 0 < A * (1 + r) := by positivity
  have hs1 : s * (A * (1 + r)) < A - r := by rwa [lt_div_iff₀ hAr] at hσ
  have hs2 : s < 1 := by nlinarith
  set u := A * s * (1 - s) with hu
  have hu0 : 0 < u := by rw [hu]; apply mul_pos (mul_pos hA hs); linarith
  have key : r * s * (1 + u) < u := by
    have : r * (1 + u) < A * (1 - s) := by
      have : u ≤ A * s := by rw [hu]; nlinarith
      nlinarith
    have h3 : r * s * (1 + u) < s * (A * (1 - s)) := by nlinarith
    rw [hu]; nlinarith
  have e1 : Real.exp (-u) * (1 + u) ≤ 1 := by
    have h := Real.add_one_le_exp u
    have h4 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    have h5 := Real.exp_pos (-u)
    nlinarith
  unfold mcf
  rw [← hu]
  by_contra hcon
  push_neg at hcon
  have h6 : 1 - r * s ≤ Real.exp (-u) := by linarith
  nlinarith

theorem mcf_chord (A r : ℝ) (hA : 0 ≤ A) (s' s s'' : ℝ) (h1 : s' < s) (h2 : s < s'') :
    ((s'' - s) / (s'' - s')) * mcf A r s' + ((s - s') / (s'' - s')) * mcf A r s'' ≤ mcf A r s := by
  have hd : 0 < s'' - s' := by linarith
  have ha : 0 ≤ (s'' - s) / (s'' - s') := div_nonneg (by linarith) hd.le
  have hb : 0 ≤ (s - s') / (s'' - s') := div_nonneg (by linarith) hd.le
  have hab : (s'' - s) / (s'' - s') + (s - s') / (s'' - s') = 1 := by
    field_simp; ring
  have := (mcf_concave A r hA).2 (Set.mem_univ s') (Set.mem_univ s'') ha hb hab
  simp only [smul_eq_mul] at this
  have e : (s'' - s) / (s'' - s') * s' + (s - s') / (s'' - s') * s'' = s := by
    field_simp; ring
  rwa [e] at this

/-- sign pattern around a positive root -/
theorem mcf_sign (A r : ℝ) (hr : 0 < r) (hrA : r < A) (st : ℝ) (hst : 0 < st)
    (hroot : mcf A r st = 0) :
    (∀ s, 0 < s → s < st → 0 < mcf A r s) ∧ (∀ s, st < s → mcf A r s < 0) := by
  have hA : 0 < A := hr.trans hrA
  have hσpos : 0 < (A - r) / (A * (1 + r)) := by
    apply div_pos (by linarith); positivity
  set σ := (A - r) / (A * (1 + r)) with hσ
  constructor
  · intro s hs hsst
    set s' := min s σ / 2 with hs'
    have hm : 0 < min s σ := lt_min hs hσpos
    have hs'0 : 0 < s' := by rw [hs']; linarith
    have hs's : s' < s := by rw [hs']; have := min_le_left s σ; linarith
    have hs'σ : s' < σ := by rw [hs']; have := min_le_right s σ; linarith
    have hp := mcf_pos_small A r hr hrA s' hs'0 hs'σ
    have hc := mcf_chord A r hA.le s' s st hs's hsst
    rw [hroot] at hc
    have : 0 < (st - s) / (st - s') := div_pos (by linarith) (by linarith)
    nlinarith [mul_pos this hp]
  · intro s hs
    set s' := min st σ / 2 with hs'
    have hm : 0 < min st σ := lt_min hst hσpos
    have hs'0 : 0 < s' := by rw [hs']; linarith
    have hs's : s' < st := by rw [hs']; have := min_le_left st σ; linarith
    have hs'σ : s' < σ := by rw [hs']; have := min_le_right st σ; linarith
    have hp := mcf_pos_small A r hr hrA s' hs'0 hs'σ
    have hc := mcf_chord A r hA.le s' st s hs's hs
    rw [hroot] at hc
    have h1 : 0 < (s - st) / (s - s') := div_pos (by linarith) (by linarith)
    have h2 : 0 < (st - s') / (s - s') := div_pos (by linarith) (by linarith)
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_pos h1 hp, mul_nonneg h2.le hcon]

theorem mcf_exists (A r : ℝ) (hr : 0 < r) (hrA : r < A) :
    ∃ s, 0 < s ∧ s < 1 ∧ mcf A r s = 0 := by
  have hA : 0 < A := hr.trans hrA
  have hσpos : 0 < (A - r) / (A * (1 + r)) := by
    apply div_pos (by linarith); positivity
  set σ := (A - r) / (A * (1 + r)) with hσ
  have hσ1 : σ < 1 := by
    rw [hσ, div_lt_one (by positivity)]; nlinarith
  have hp := mcf_pos_small A r hr hrA (σ / 2) (by linarith) (by linarith)
  have h1 : mcf A r 1 = -r := by simp [mcf]
  have hcont : ContinuousOn (mcf A r) (Set.Icc (σ / 2) 1) := by
    unfold mcf; fun_prop
  obtain ⟨s, hs, hz⟩ := intermediate_value_Icc' (by linarith : σ / 2 ≤ 1) hcont
    (show (0 : ℝ) ∈ Set.Icc (mcf A r 1) (mcf A r (σ / 2)) from ⟨by rw [h1]; linarith, hp.le⟩)
  refine ⟨s, by linarith [hs.1], ?_, hz⟩
  rcases hs.2.lt_or_eq with h | h
  · exact h
  · exfalso; rw [h, h1] at hz; linarith


theorem mc_eq15 (P : Params) (hca : 0 < P.ca) (p : ℝ) (hp : P.ca < p) :
    Wa P (Mbr P p) p = 1 - P.ca / p + P.ca / p * Real.log (P.ca / p) := by
  have hp0 : 0 < p := hca.trans hp
  have hM : Mbr P p = (1 / p) * Real.log (p / P.ca) := by
    unfold Mbr; rw [if_neg (not_le.mpr hp)]
  have hmp : Mbr P p * p = Real.log (p / P.ca) := by
    rw [hM]; field_simp
  have hpc : 0 < p / P.ca := div_pos hp0 hca
  have hexp : Real.exp (-(Mbr P p * p)) = P.ca / p := by
    rw [hmp, Real.exp_neg, Real.exp_log hpc, inv_div]
  have hlog : Real.log (P.ca / p) = - Real.log (p / P.ca) := by
    rw [← inv_div, Real.log_inv]
  unfold Wa
  rw [hexp, hM, hlog]
  field_simp
  ring


theorem mc_eq16 (P : Params) (hP : P.Standing) (m α p q : ℝ)
    (hss : IsMFSS P m α p q) (hm : m = Mbr P p) (hp : P.ca < p) :
    We P α m q = P.r * (1 - P.ca / p + P.cs / P.β * Real.log (P.ca / p)) := by
  obtain ⟨_, hr, hβ, _, hca, _⟩ := hP
  obtain ⟨hq, hpe⟩ := hss
  have hp0 : 0 < p := hca.trans hp
  have hpc : 1 < p / P.ca := by rw [lt_div_iff₀ hca]; linarith
  set L := Real.log (p / P.ca) with hL
  have hLpos : 0 < L := Real.log_pos hpc
  have hM : m = (1 / p) * L := by
    rw [hm]; unfold Mbr; rw [if_neg (not_le.mpr hp)]
  have hmp : m * p = L := by rw [hM]; field_simp
  have hmpos : 0 < m := by rw [hM]; positivity
  have hexp : Real.exp (-(m * p)) = P.ca / p := by
    rw [hmp, hL, Real.exp_neg, Real.exp_log (by linarith), inv_div]
  have hlog : Real.log (P.ca / p) = - L := by
    rw [hL, ← inv_div, Real.log_inv]
  have h1 : 0 < 1 - P.ca / p := by
    rw [sub_pos, div_lt_one hp0]; exact hp
  have hq' : q = (1 - P.ca / p) / L := by
    rw [hq]; unfold E
    rw [if_neg (by rw [hmp]; exact hLpos.ne'), hexp, hmp]
  have hqpos : 0 < q := by rw [hq']; positivity
  have hLq : L * q = 1 - P.ca / p := by rw [hq']; field_simp
  set x := P.r * m * P.β * q with hx
  have hxpos : 0 < x := by positivity
  have hpe' : p = α * P.β * ((1 - Real.exp (-x)) / x) := by
    rw [hpe]; unfold E; rw [if_neg hxpos.ne']
  have hA : α * (1 - Real.exp (-x)) = P.r * L * q := by
    have : α * (1 - Real.exp (-x)) * P.β = p * x := by
      rw [hpe']; field_simp
    have h2 : p * x = P.β * (P.r * L * q) := by
      rw [hx, ← hmp]; ring
    have : α * (1 - Real.exp (-x)) * P.β = (P.r * L * q) * P.β := by
      rw [this, h2]; ring
    exact mul_right_cancel₀ hβ.ne' this
  unfold We csp
  rw [hA, hlog]
  have : P.r * L * q * (1 - P.cs / P.β / q) = P.r * (L * q) - P.r * (P.cs / P.β) * L := by
    field_simp
  rw [this, hLq]
  ring
theorem mc_h14 (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    ∃! t : ℝ, 0 < t ∧ t < 1 ∧ 1 - t + k * Real.log t = 0 := by
  have hconc := strictConcaveOn_log_Ioi
  have hex : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ 1 - t + k * Real.log t = 0 := by
    have hlk : Real.log k < 0 := Real.log_neg hk0 hk1
    set t0 := k * Real.exp (-2 / k) with ht0
    have ht0pos : 0 < t0 := by positivity
    have hexp1 : Real.exp (-2 / k) < 1 := by
      have : 0 < 2 / k := by positivity
      have e : -2 / k = -(2 / k) := by ring
      have h5 := Real.exp_lt_exp.mpr (show -2 / k < 0 by linarith)
      simpa using h5
    have ht0k : t0 < k := by
      rw [ht0]; nlinarith
    have hlog0 : Real.log t0 = Real.log k + (-2 / k) := by
      rw [ht0, Real.log_mul hk0.ne' (Real.exp_pos _).ne', Real.log_exp]
    have hh0 : 1 - t0 + k * Real.log t0 < 0 := by
      rw [hlog0]
      have : k * (-2 / k) = -2 := by field_simp
      have h3 : k * Real.log k ≤ 0 := by nlinarith
      nlinarith
    have hhk : 0 < 1 - k + k * Real.log k := by
      have h1 : Real.log (1 / k) < 1 / k - 1 := by
        apply Real.log_lt_sub_one_of_pos (by positivity)
        intro h; field_simp at h; linarith
      rw [one_div, Real.log_inv] at h1
      have h2 := mul_lt_mul_of_pos_left h1 hk0
      have : k * (k⁻¹ - 1) = 1 - k := by field_simp
      nlinarith
    have hcont : ContinuousOn (fun t : ℝ => 1 - t + k * Real.log t) (Set.Icc t0 k) := by
      apply ContinuousOn.add
      · fun_prop
      · apply ContinuousOn.mul continuousOn_const
        apply Real.continuousOn_log.mono
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact (lt_of_lt_of_le ht0pos hx.1).ne'
    obtain ⟨t, ht, htz⟩ := intermediate_value_Icc ht0k.le hcont
      (show (0 : ℝ) ∈ Set.Icc (1 - t0 + k * Real.log t0) (1 - k + k * Real.log k) from
        ⟨hh0.le, hhk.le⟩)
    refine ⟨t, lt_of_lt_of_le ht0pos ht.1, ?_, htz⟩
    rcases ht.2.lt_or_eq with h | h
    · linarith
    · exfalso; rw [h] at htz; linarith
  have key : ∀ t1 t2 : ℝ, 0 < t1 → t1 < t2 → t2 < 1 →
      1 - t1 + k * Real.log t1 = 0 → 1 - t2 + k * Real.log t2 = 0 → False := by
    intro t1 t2 h1 h12 h2 e1 e2
    set a := (1 - t2) / (1 - t1) with ha
    have h1m : 0 < 1 - t1 := by linarith
    have hapos : 0 < a := div_pos (by linarith) h1m
    have hb : 0 < 1 - a := by
      rw [sub_pos, ha, div_lt_one h1m]; linarith
    have hc := hconc.2 (Set.mem_Ioi.mpr h1) (Set.mem_Ioi.mpr one_pos)
      (by intro h; linarith) hapos hb (by ring)
    simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hc
    have hlin : a * t1 + (1 - a) * 1 = t2 := by
      rw [ha]; field_simp; ring
    rw [hlin] at hc
    have hat : a * (1 - t1) = 1 - t2 := by rw [ha]; field_simp
    have h3 := mul_lt_mul_of_pos_left hc hk0
    have e1' : k * Real.log t1 = t1 - 1 := by linarith
    have e2' : k * Real.log t2 = t2 - 1 := by linarith
    have h4 : k * (a * Real.log t1) = a * (t1 - 1) := by rw [← e1']; ring
    rw [h4, e2'] at h3
    nlinarith [hat]
  obtain ⟨t, ht0, ht1, hte⟩ := hex
  refine ⟨t, ⟨ht0, ht1, hte⟩, ?_⟩
  rintro t' ⟨ht0', ht1', hte'⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact key t' t ht0' h ht1 hte' hte
  · exact key t t' ht0 h ht1' hte hte'

theorem mc_root14 (P : Params) (hP : P.Standing) :
    ∃! p : ℝ, P.ca < p ∧ Eq14 P p := by
  obtain ⟨hmax, hr, hβ, _, hca, hcs⟩ := hP
  have hcsβ : P.cs < P.β := lt_of_le_of_lt (le_max_right _ _) hmax
  have hk0 : 0 < P.cs / P.β := div_pos hcs hβ
  have hk1 : P.cs / P.β < 1 := by rw [div_lt_one hβ]; exact hcsβ
  obtain ⟨t, ⟨ht0, ht1, hte⟩, hu⟩ := mc_h14 _ hk0 hk1
  have hpt : P.ca < P.ca / t := by
    rw [lt_div_iff₀ ht0]; nlinarith
  refine ⟨P.ca / t, ⟨hpt, ?_⟩, ?_⟩
  · unfold Eq14
    have : P.ca / (P.ca / t) = t := by field_simp
    rw [this]; exact hte
  · rintro p ⟨hp, hpe⟩
    have hp0 : 0 < p := hca.trans hp
    have h1 : P.ca / p = t := by
      apply hu
      refine ⟨div_pos hca hp0, ?_, hpe⟩
      rw [div_lt_one hp0]; exact hp
    rw [← h1]
    field_simp

theorem mc_eq13_iff (P : Params) (hca : 0 < P.ca) (p : ℝ) (hp : 0 < p) :
    Eq13 P p ↔ mcf (P.r * P.β / P.ca) P.r (1 - P.ca / p) = 0 := by
  unfold Eq13 mcf
  have : -(P.r * P.β / p) * (1 - P.ca / p) =
      -(P.r * P.β / P.ca * (1 - P.ca / p) * (1 - (1 - P.ca / p))) := by
    field_simp; ring
  rw [this]
  constructor <;> intro h <;> linarith

theorem mc_root13 (P : Params) (hP : P.Standing) :
    ∃! p : ℝ, P.ca < p ∧ Eq13 P p := by
  obtain ⟨hmax, hr, hβ, _, hca, hcs⟩ := hP
  have hcaβ : P.ca < P.β := lt_of_le_of_lt (le_max_left _ _) hmax
  have hrA : P.r < P.r * P.β / P.ca := by
    rw [lt_div_iff₀ hca]; nlinarith
  obtain ⟨s, hs0, hs1, hsz⟩ := mcf_exists _ _ hr hrA
  have h1s : 0 < 1 - s := by linarith
  have hp : P.ca < P.ca / (1 - s) := by
    rw [lt_div_iff₀ h1s]; nlinarith
  have hcs' : 1 - P.ca / (P.ca / (1 - s)) = s := by field_simp; ring
  refine ⟨P.ca / (1 - s), ⟨hp, ?_⟩, ?_⟩
  · rw [mc_eq13_iff P hca _ (hca.trans hp), hcs']; exact hsz
  · rintro p ⟨hpc, hpe⟩
    have hp0 : 0 < p := hca.trans hpc
    have hz := (mc_eq13_iff P hca p hp0).mp hpe
    set s' := 1 - P.ca / p with hs'
    have hs'0 : 0 < s' := by
      rw [hs', sub_pos, div_lt_one hp0]; exact hpc
    have hs'1 : s' < 1 := by
      rw [hs']; have : 0 < P.ca / p := div_pos hca hp0
      linarith
    have : s' = s := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := (mcf_sign _ _ hr hrA s' hs'0 hz).2 s h
        linarith
      · have := (mcf_sign _ _ hr hrA s hs0 hsz).2 s' h
        linarith
    have e : P.ca / p = 1 - s := by rw [← this, hs']; ring
    rw [← e]; field_simp

theorem mch_sign (k : ℝ) (hk0 : 0 < k) (ts : ℝ) (hts0 : 0 < ts) (hts1 : ts < 1)
    (hz : 1 - ts + k * Real.log ts = 0) :
    (∀ t, ts < t → t < 1 → 0 < 1 - t + k * Real.log t) ∧
    (∀ t, 0 < t → t < ts → 1 - t + k * Real.log t < 0) := by
  have hconc := strictConcaveOn_log_Ioi
  have hlts : k * Real.log ts = ts - 1 := by linarith
  constructor
  · intro t h1 h2
    have hd : 0 < 1 - ts := by linarith
    set a := (1 - t) / (1 - ts) with ha
    have hapos : 0 < a := div_pos (by linarith) hd
    have hb : 0 < 1 - a := by rw [sub_pos, ha, div_lt_one hd]; linarith
    have hc := hconc.2 (Set.mem_Ioi.mpr hts0) (Set.mem_Ioi.mpr one_pos)
      (by intro h; linarith) hapos hb (by ring)
    simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hc
    have hlin : a * ts + (1 - a) * 1 = t := by rw [ha]; field_simp; ring
    rw [hlin] at hc
    have hat : a * (1 - ts) = 1 - t := by rw [ha]; field_simp
    have h3 := mul_lt_mul_of_pos_left hc hk0
    have h4 : k * (a * Real.log ts) = a * (ts - 1) := by rw [← hlts]; ring
    rw [h4] at h3
    nlinarith [hat]
  · intro t h0 h1
    by_contra hcon
    push_neg at hcon
    have hd : 0 < 1 - t := by linarith
    set a := (1 - ts) / (1 - t) with ha
    have hapos : 0 < a := div_pos (by linarith) hd
    have hb : 0 < 1 - a := by rw [sub_pos, ha, div_lt_one hd]; linarith
    have hc := hconc.2 (Set.mem_Ioi.mpr h0) (Set.mem_Ioi.mpr one_pos)
      (by intro h; linarith) hapos hb (by ring)
    simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at hc
    have hlin : a * t + (1 - a) * 1 = ts := by rw [ha]; field_simp; ring
    rw [hlin] at hc
    have hat : a * (1 - t) = 1 - ts := by rw [ha]; field_simp
    have h3 := mul_lt_mul_of_pos_left hc hk0
    have h5 : t - 1 ≤ k * Real.log t := by linarith
    have h6 := mul_le_mul_of_nonneg_left h5 hapos.le
    have h4 : k * (a * Real.log t) = a * (k * Real.log t) := by ring
    rw [h4, hlts] at h3
    nlinarith [hat]

theorem mc_Mbr_facts (P : Params) (hca : 0 < P.ca) (p : ℝ) (hp : P.ca < p) :
    Mbr P p = (1 / p) * Real.log (p / P.ca) ∧ Mbr P p * p = Real.log (p / P.ca) ∧
      0 < Real.log (p / P.ca) ∧ 0 < Mbr P p := by
  have hp0 : 0 < p := hca.trans hp
  have hpc : 1 < p / P.ca := by rw [lt_div_iff₀ hca]; linarith
  have hL := Real.log_pos hpc
  have hM : Mbr P p = (1 / p) * Real.log (p / P.ca) := by
    unfold Mbr; rw [if_neg (not_le.mpr hp)]
  exact ⟨hM, by rw [hM]; field_simp, hL, by rw [hM]; positivity⟩

theorem mc_q0 (P : Params) (hca : 0 < P.ca) (p : ℝ) (hp : P.ca < p) :
    E (Mbr P p * p) = (1 - P.ca / p) / Real.log (p / P.ca) := by
  obtain ⟨_, h1, hL, _⟩ := mc_Mbr_facts P hca p hp
  have hexp : Real.exp (-(Mbr P p * p)) = P.ca / p := by
    rw [h1, Real.exp_neg, Real.exp_log (div_pos (hca.trans hp) hca), inv_div]
  rw [mcE_of_pos (by rw [h1]; exact hL), hexp, h1]

theorem mc_y (P : Params) (hca : 0 < P.ca) (p : ℝ) (hp : P.ca < p) :
    P.r * Mbr P p * P.β * E (Mbr P p * p) = P.r * P.β / p * (1 - P.ca / p) := by
  obtain ⟨hM, _, hL, _⟩ := mc_Mbr_facts P hca p hp
  have hp0 : 0 < p := hca.trans hp
  rw [mc_q0 P hca p hp, hM]
  field_simp

theorem mc_alpha (P : Params) (hr : 0 < P.r) (hβ : 0 < P.β) (hca : 0 < P.ca) (p : ℝ)
    (hp : P.ca < p) (α : ℝ) :
    p = α * P.β * E (P.r * P.β / p * (1 - P.ca / p)) ↔
    α * (1 - Real.exp (-(P.r * P.β / p * (1 - P.ca / p)))) = P.r * (1 - P.ca / p) := by
  have hp0 : 0 < p := hca.trans hp
  have h1 : 0 < 1 - P.ca / p := by rw [sub_pos, div_lt_one hp0]; exact hp
  set y := P.r * P.β / p * (1 - P.ca / p) with hyd
  have hy : 0 < y := by positivity
  have hpy : p * y = P.β * (P.r * (1 - P.ca / p)) := by rw [hyd]; field_simp
  rw [mcE_of_pos hy]
  constructor
  · intro h
    have h' : p * y = α * P.β * ((1 - Real.exp (-y)) / y) * y := by rw [← h]
    have h2 : p * y = P.β * (α * (1 - Real.exp (-y))) := by rw [h']; field_simp
    rw [hpy] at h2
    have := mul_left_cancel₀ hβ.ne' h2
    linarith
  · intro h
    rw [mul_div_assoc', eq_div_iff hy.ne', hpy, ← h]; ring

theorem mc_w (P : Params) (hca : 0 < P.ca) (p : ℝ) (hp : P.ca < p) :
    1 - Real.exp (-(P.r * P.β / p * (1 - P.ca / p))) - P.r * (1 - P.ca / p) =
      mcf (P.r * P.β / P.ca) P.r (1 - P.ca / p) := by
  have hp0 : 0 < p := hca.trans hp
  unfold mcf
  have : P.r * P.β / p * (1 - P.ca / p) =
      P.r * P.β / P.ca * (1 - P.ca / p) * (1 - (1 - P.ca / p)) := by
    field_simp; ring
  rw [this]

theorem mc_D (P : Params) (hca : 0 < P.ca) (p : ℝ) (hp : P.ca < p) :
    (E (Mbr P p * p) < csp P ↔ 1 - P.ca / p + P.cs / P.β * Real.log (P.ca / p) < 0) ∧
    (csp P < E (Mbr P p * p) ↔ 0 < 1 - P.ca / p + P.cs / P.β * Real.log (P.ca / p)) := by
  obtain ⟨_, _, hL, _⟩ := mc_Mbr_facts P hca p hp
  have hlog : Real.log (P.ca / p) = - Real.log (p / P.ca) := by
    rw [← inv_div, Real.log_inv]
  rw [mc_q0 P hca p hp, hlog]
  unfold csp
  constructor
  · rw [div_lt_iff₀ hL]
    constructor <;> intro h <;> linarith
  · rw [lt_div_iff₀ hL]
    constructor <;> intro h <;> linarith

theorem mc_signD (P : Params) (hca : 0 < P.ca) (hk0 : 0 < P.cs / P.β) (pb : ℝ)
    (hpb : P.ca < pb) (h14 : Eq14 P pb) (p : ℝ) (hp : P.ca < p) :
    (p < pb → 0 < 1 - P.ca / p + P.cs / P.β * Real.log (P.ca / p)) ∧
    (pb < p → 1 - P.ca / p + P.cs / P.β * Real.log (P.ca / p) < 0) := by
  have hp0 : 0 < p := hca.trans hp
  have hpb0 : 0 < pb := hca.trans hpb
  have ht1 : P.ca / pb < 1 := by rw [div_lt_one hpb0]; exact hpb
  have ht0 : 0 < P.ca / pb := div_pos hca hpb0
  obtain ⟨hs1, hs2⟩ := mch_sign _ hk0 _ ht0 ht1 h14
  constructor
  · intro h
    apply hs1 _ _ (by rw [div_lt_one hp0]; exact hp)
    rw [div_lt_div_iff₀ hpb0 hp0]; nlinarith
  · intro h
    apply hs2 _ (div_pos hca hp0)
    rw [div_lt_div_iff₀ hp0 hpb0]; nlinarith

theorem mc_signF (P : Params) (hr : 0 < P.r) (hca : 0 < P.ca)
    (hrA : P.r < P.r * P.β / P.ca) (ph : ℝ)
    (hph : P.ca < ph) (h13 : Eq13 P ph) (p : ℝ) (hp : P.ca < p) :
    (p < ph → 0 < mcf (P.r * P.β / P.ca) P.r (1 - P.ca / p)) ∧
    (ph < p → mcf (P.r * P.β / P.ca) P.r (1 - P.ca / p) < 0) := by
  have hp0 : 0 < p := hca.trans hp
  have hph0 : 0 < ph := hca.trans hph
  have hz := (mc_eq13_iff P hca ph hph0).mp h13
  have hst : 0 < 1 - P.ca / ph := by rw [sub_pos, div_lt_one hph0]; exact hph
  obtain ⟨hs1, hs2⟩ := mcf_sign _ _ hr hrA _ hst hz
  constructor
  · intro h
    apply hs1 _ (by rw [sub_pos, div_lt_one hp0]; exact hp)
    have : P.ca / ph < P.ca / p := by rw [div_lt_div_iff₀ hph0 hp0]; nlinarith
    linarith
  · intro h
    apply hs2
    have : P.ca / p < P.ca / ph := by rw [div_lt_div_iff₀ hp0 hph0]; nlinarith
    linarith

theorem mc_claimM (P : Params) (hP : P.Standing) (ph pb : ℝ) (hph : P.ca < ph)
    (h13 : Eq13 P ph) (hpb : P.ca < pb) (h14 : Eq14 P pb) (m α p q : ℝ)
    (hss : IsMFSS P m α p q) (hm : m = Mbr P p) (hα : α ∈ Acorr P q) :
    P.ca < p ∧ ((p = ph ∧ ph < pb ∧ α = 1) ∨
      (p = pb ∧ pb ≤ ph ∧
        α * (1 - Real.exp (-(P.r * P.β / p * (1 - P.ca / p)))) = P.r * (1 - P.ca / p))) := by
  obtain ⟨hmax, hr, hβ, hβ1, hca, hcs⟩ := hP
  have hcaβ : P.ca < P.β := lt_of_le_of_lt (le_max_left _ _) hmax
  have hcsβ : P.cs < P.β := lt_of_le_of_lt (le_max_right _ _) hmax
  have hk0 : 0 < P.cs / P.β := div_pos hcs hβ
  have hk1 : P.cs / P.β < 1 := by rw [div_lt_one hβ]; exact hcsβ
  have hrA : P.r < P.r * P.β / P.ca := by
    rw [lt_div_iff₀ hca]; nlinarith
  have hp : P.ca < p := by
    by_contra hnp
    push_neg at hnp
    have hm0 : m = 0 := by rw [hm]; unfold Mbr; rw [if_pos hnp]
    obtain ⟨h1, h2⟩ := hss
    rw [hm0] at h1 h2
    simp only [zero_mul, mul_zero, mcE_zero] at h1 h2
    unfold Acorr at hα
    rw [h1] at hα
    have c1 : ¬ (1 < csp P) := by unfold csp; rw [not_lt]; exact hk1.le
    have c2 : ¬ ((1 : ℝ) = csp P) := by unfold csp; intro h; linarith
    rw [if_neg (by unfold csp; rw [not_lt]; exact hk1.le), if_neg c2] at hα
    have hα1 : α = 1 := hα
    subst hα1
    nlinarith
  refine ⟨hp, ?_⟩
  have hp0 : 0 < p := hca.trans hp
  subst hm
  have hqE : q = E (Mbr P p * p) := hss.1
  have hy : P.r * Mbr P p * P.β * q = P.r * P.β / p * (1 - P.ca / p) := by
    rw [hqE]; exact mc_y P hca p hp
  have hαw : α * (1 - Real.exp (-(P.r * P.β / p * (1 - P.ca / p)))) = P.r * (1 - P.ca / p) := by
    apply (mc_alpha P hr hβ hca p hp α).mp
    have := hss.2
    rw [hy] at this
    exact this
  have hs : 0 < 1 - P.ca / p := by rw [sub_pos, div_lt_one hp0]; exact hp
  have hw : 0 < 1 - Real.exp (-(P.r * P.β / p * (1 - P.ca / p))) :=
    mcE_one_sub_pos (by positivity)
  have hFw := mc_w P hca p hp
  obtain ⟨hD1, hD2⟩ := mc_D P hca p hp
  rcases lt_trichotomy (1 - P.ca / p + P.cs / P.β * Real.log (P.ca / p)) 0 with hD | hD | hD
  · -- q < csp : alpha = 0
    exfalso
    have hlt : q < csp P := by rw [hqE]; exact hD1.mpr hD
    unfold Acorr at hα
    rw [if_pos hlt] at hα
    have : α = 0 := hα
    rw [this] at hαw
    have : 0 < P.r * (1 - P.ca / p) := by positivity
    linarith
  · -- indifference
    have h14p : Eq14 P p := hD
    have hpp : p = pb := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := (mc_signD P hca hk0 pb hpb h14 p hp).1 h; linarith
      · have := (mc_signD P hca hk0 pb hpb h14 p hp).2 h; linarith
    have hq1 : ¬ (q < csp P) := by
      rw [hqE]; intro h; have := hD1.mp h; linarith
    have hq2 : q = csp P := by
      by_contra hne
      have : csp P < q := lt_of_le_of_ne (not_lt.mp hq1) (Ne.symm hne)
      rw [hqE] at this
      have := hD2.mp this; linarith
    unfold Acorr at hα
    rw [if_neg hq1, if_pos hq2] at hα
    obtain ⟨hα0, hα1⟩ := hα
    right
    refine ⟨hpp, ?_, hαw⟩
    by_contra hnle
    push_neg at hnle
    have hnle' : ph < p := by rw [hpp]; exact hnle
    have hF := (mc_signF P hr hca hrA ph hph h13 p hp).2 hnle'
    rw [← hFw] at hF
    nlinarith
  · -- q > csp : alpha = 1
    have hgt : csp P < q := by rw [hqE]; exact hD2.mpr hD
    unfold Acorr at hα
    rw [if_neg (not_lt.mpr hgt.le), if_neg hgt.ne'] at hα
    have hα1 : α = 1 := hα
    subst hα1
    left
    have hpp : p = ph := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := (mc_signF P hr hca hrA ph hph h13 p hp).1 h
        rw [← hFw] at this; linarith
      · have := (mc_signF P hr hca hrA ph hph h13 p hp).2 h
        rw [← hFw] at this; linarith
    have hppb : p < pb := by
      by_contra hn
      push_neg at hn
      rcases hn.lt_or_eq with h | h
      · have := (mc_signD P hca hk0 pb hpb h14 p hp).2 h; linarith
      · rw [h] at h14
        unfold Eq14 at h14; linarith
    exact ⟨hpp, by rw [← hpp]; exact hppb, rfl⟩

theorem mc_exists (P : Params) (hP : P.Standing) (ph pb : ℝ) (hph : P.ca < ph)
    (h13 : Eq13 P ph) (hpb : P.ca < pb) (h14 : Eq14 P pb) :
    ∃ m α : ℝ, IsMFE P m α := by
  obtain ⟨hmax, hr, hβ, hβ1, hca, hcs⟩ := hP
  have hcaβ : P.ca < P.β := lt_of_le_of_lt (le_max_left _ _) hmax
  have hcsβ : P.cs < P.β := lt_of_le_of_lt (le_max_right _ _) hmax
  have hk0 : 0 < P.cs / P.β := div_pos hcs hβ
  have hrA : P.r < P.r * P.β / P.ca := by
    rw [lt_div_iff₀ hca]; nlinarith
  rcases lt_or_ge ph pb with hlt | hge
  · -- p = ph, alpha = 1
    refine ⟨Mbr P ph, 1, ph, E (Mbr P ph * ph), ⟨rfl, ?_⟩, rfl, ?_⟩
    · have hph0 : 0 < ph := hca.trans hph
      rw [mc_y P hca ph hph]
      apply (mc_alpha P hr hβ hca ph hph 1).mpr
      have hz := (mc_eq13_iff P hca ph hph0).mp h13
      have := mc_w P hca ph hph
      linarith
    · have hD := (mc_signD P hca hk0 pb hpb h14 ph hph).1 hlt
      have hgt : csp P < E (Mbr P ph * ph) := (mc_D P hca ph hph).2.mpr hD
      unfold Acorr
      rw [if_neg (not_lt.mpr hgt.le), if_neg hgt.ne']
      rfl
  · -- p = pb
    have hpb0 : 0 < pb := hca.trans hpb
    have hs : 0 < 1 - P.ca / pb := by rw [sub_pos, div_lt_one hpb0]; exact hpb
    have hw : 0 < 1 - Real.exp (-(P.r * P.β / pb * (1 - P.ca / pb))) :=
      mcE_one_sub_pos (by positivity)
    have hFw := mc_w P hca pb hpb
    have hF : 0 ≤ mcf (P.r * P.β / P.ca) P.r (1 - P.ca / pb) := by
      rcases hge.lt_or_eq with h | h
      · exact ((mc_signF P hr hca hrA ph hph h13 pb hpb).1 h).le
      · have hz := (mc_eq13_iff P hca ph (hca.trans hph)).mp h13
        rw [h]; exact hz.ge
    set w := 1 - Real.exp (-(P.r * P.β / pb * (1 - P.ca / pb))) with hwd
    set α := P.r * (1 - P.ca / pb) / w with hαd
    have hαw : α * w = P.r * (1 - P.ca / pb) := by rw [hαd]; field_simp
    have hα0 : 0 ≤ α := by rw [hαd]; positivity
    have hα1 : α ≤ 1 := by
      rw [hαd, div_le_one hw]; linarith
    refine ⟨Mbr P pb, α, pb, E (Mbr P pb * pb), ⟨rfl, ?_⟩, rfl, ?_⟩
    · rw [mc_y P hca pb hpb]
      exact (mc_alpha P hr hβ hca pb hpb α).mpr hαw
    · obtain ⟨hD1, hD2⟩ := mc_D P hca pb hpb
      have h14' : 1 - P.ca / pb + P.cs / P.β * Real.log (P.ca / pb) = 0 := h14
      have hq1 : ¬ (E (Mbr P pb * pb) < csp P) := by
        intro h; have := hD1.mp h; linarith
      have hq2 : E (Mbr P pb * pb) = csp P := by
        by_contra hne
        have : csp P < E (Mbr P pb * pb) := lt_of_le_of_ne (not_lt.mp hq1) (Ne.symm hne)
        have := hD2.mp this; linarith
      unfold Acorr
      rw [if_neg hq1, if_pos hq2]
      exact ⟨hα0, hα1⟩

theorem mc_theorem1 (P : Params) (hP : P.Standing) (ph pb : ℝ) (hph : P.ca < ph)
    (h13 : Eq13 P ph) (hpb : P.ca < pb) (h14 : Eq14 P pb) :
    ∃! mα : ℝ × ℝ, IsMFE P mα.1 mα.2 := by
  obtain ⟨m, α, hmα⟩ := mc_exists P hP ph pb hph h13 hpb h14
  refine ⟨(m, α), hmα, ?_⟩
  rintro ⟨m', α'⟩ h'
  obtain ⟨p, q, hss, hm, hα⟩ := hmα
  obtain ⟨p', q', hss', hm', hα'⟩ := h'
  dsimp only at hm' hα' hss'
  obtain ⟨hp1, hc⟩ := mc_claimM P hP ph pb hph h13 hpb h14 m α p q hss hm hα
  obtain ⟨_, hc'⟩ := mc_claimM P hP ph pb hph h13 hpb h14 m' α' p' q' hss' hm' hα'
  have key : p = p' ∧ α = α' := by
    rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> rcases hc' with ⟨h1', h2', h3'⟩ | ⟨h1', h2', h3'⟩
    · exact ⟨by rw [h1, h1'], by rw [h3, h3']⟩
    · exfalso; linarith
    · exfalso; linarith
    · have hpp : p = p' := by rw [h1, h1']
      refine ⟨hpp, ?_⟩
      subst hpp
      have hca : 0 < P.ca := hP.2.2.2.2.1
      have hr : 0 < P.r := hP.2.1
      have hβ : 0 < P.β := hP.2.2.1
      have hp := hp1
      have hp0 : 0 < p := hca.trans hp
      have hw : 0 < 1 - Real.exp (-(P.r * P.β / p * (1 - P.ca / p))) :=
        mcE_one_sub_pos (by
          have : 0 < 1 - P.ca / p := by rw [sub_pos, div_lt_one hp0]; exact hp
          positivity)
      have : α * (1 - Real.exp (-(P.r * P.β / p * (1 - P.ca / p)))) =
          α' * (1 - Real.exp (-(P.r * P.β / p * (1 - P.ca / p)))) := by rw [h3, h3']
      exact mul_right_cancel₀ hw.ne' this
  obtain ⟨hpp, hαα⟩ := key
  subst hpp
  subst hαα
  rw [hm, hm']

theorem solution (P : Params) (hP : P.Standing) :
    ∃! mα : ℝ × ℝ, IsMFE P mα.1 mα.2 := by
  obtain ⟨ph, ⟨hph, h13⟩, _⟩ := mc_root13 P hP
  obtain ⟨pb, ⟨hpb, h14⟩, _⟩ := mc_root14 P hP
  exact mc_theorem1 P hP ph pb hph h13 hpb h14
