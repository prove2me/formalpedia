-- Prove2me | solution 1 for MIBF.Balanced.full_lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T10:14:15.568803+00:00
-- url     : https://prove2.me/submissions/3687beb0-c055-4033-8d5b-376ff16c8ca2

import Mathlib
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_MIBF_Balanced_PureGap

set_option linter.all false

namespace GeneralCK
open scoped BigOperators
theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

@[simp] theorem H_zero : H 0 = 0 := by simp [H]
@[simp] theorem H_one : H 1 = 0 := by simp [H]
@[simp] theorem H_half : H (1 / 2) = 1 := by
  have h : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
  simpa [H, one_div] using div_self h

theorem H_complement (p : ℝ) : H (1 - p) = H p := by simp [H]

theorem H_nonneg {p : ℝ} (h₀ : 0 ≤ p) (h₁ : p ≤ 1) : 0 ≤ H p :=
  div_nonneg (Real.binEntropy_nonneg h₀ h₁) log_two_pos.le

theorem H_le_one (p : ℝ) : H p ≤ 1 := by
  rw [H, div_le_one log_two_pos]
  exact Real.binEntropy_le_log_two

theorem H_continuous : Continuous H :=
  Real.binEntropy_continuous.div_const _

end GeneralCK


namespace GeneralCK

theorem H_strictMonoOn : StrictMonoOn H (Set.Icc 0 (1 / 2)) := by
  intro a ha b hb hab
  exact div_lt_div_of_pos_right
    (Real.binEntropy_strictMonoOn (by simpa using ha) (by simpa using hb) hab)
    log_two_pos

theorem H_pos {p : ℝ} (hp : 0 < p) (hp' : p < 1) : 0 < H p :=
  div_pos (Real.binEntropy_pos hp hp') log_two_pos

theorem entropyInverse_H_lower {v : ℝ} (hv : 0 ≤ v) (hv' : v ≤ 1 / 2) :
    entropyInverse (H v) = v := by
  apply le_antisymm
  · apply csInf_le
    · exact ⟨0, fun _ hx => hx.1⟩
    · exact ⟨hv, hv', le_rfl⟩
  · apply le_csInf
    · exact ⟨v, hv, hv', le_rfl⟩
    · intro b hb
      by_contra hn
      have := H_strictMonoOn ⟨hb.1, hb.2.1⟩ ⟨hv, hv'⟩ (lt_of_not_ge hn)
      exact (not_lt_of_ge hb.2.2) this

theorem entropyInverse_H {m : ℝ} (hm : 0 ≤ m) (hm' : m ≤ 1) :
    entropyInverse (H m) = min m (1 - m) := by
  by_cases hl : m ≤ 1 / 2
  · rw [entropyInverse_H_lower hm hl, min_eq_left (by linarith)]
  · rw [← H_complement m, entropyInverse_H_lower (by linarith) (by linarith),
      min_eq_right (by linarith)]

@[simp] theorem eta_one : eta 1 = 0 := by simp [eta]

theorem radialContact_H_lower {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) :
    radialContact (1 - 2 * v) (H v) = v := by
  have hHv : 0 < H v := H_pos hv (by linarith)
  have hset : {u : ℝ | 0 < u ∧ u < 1 / 2 ∧
      (1 - 2 * v) * H u = H v * (1 - 2 * u)} = {v} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hu, hu', heq⟩
      rcases lt_trichotomy u v with h | h | h
      · have hH := H_strictMonoOn ⟨hu.le, hu'.le⟩ ⟨hv.le, hv'.le⟩ h
        have hmul : (1 - 2 * v) * H u < (1 - 2 * v) * H v :=
          mul_lt_mul_of_pos_left hH (by linarith)
        have hmul' : H v * (1 - 2 * v) < H v * (1 - 2 * u) :=
          mul_lt_mul_of_pos_left (by linarith) hHv
        nlinarith
      · exact h
      · have hH := H_strictMonoOn ⟨hv.le, hv'.le⟩ ⟨hu.le, hu'.le⟩ h
        have hmul : (1 - 2 * v) * H v < (1 - 2 * v) * H u :=
          mul_lt_mul_of_pos_left hH (by linarith)
        have hmul' : H v * (1 - 2 * u) < H v * (1 - 2 * v) :=
          mul_lt_mul_of_pos_left (by linarith) hHv
        nlinarith
    · rintro rfl
      exact ⟨hv, hv', mul_comm _ _⟩
  unfold radialContact
  rw [hset, csInf_singleton]

theorem B_H_lower {m : ℝ} (hm : 0 < m) (hm' : m ≤ 1 / 2) : B m (H m) = 0 := by
  by_cases heq : m = 1 / 2
  · subst m
    norm_num [B, phi, psi, F, eta_one]
  · have hlt : m < 1 / 2 := lt_of_le_of_ne hm' heq
    have hH : H m < 1 := by
      calc H m < H (1 / 2) := H_strictMonoOn ⟨hm.le, hm'⟩ ⟨by norm_num, le_rfl⟩ hlt
           _ = 1 := H_half
    have hz : |1 - 2 * m| = 1 - 2 * m := abs_of_pos (by linarith)
    have hz' : 1 - 2 * m ≠ 0 := by linarith
    simp [B, phi, psi, eta, ne_of_lt hH, entropyInverse_H_lower hm.le hm',
      hz, F, hz', radialContact_H_lower hm hlt]

theorem B_complement (m h : ℝ) : B (1 - m) h = B m h := by
  have hz : |1 - 2 * (1 - m)| = |1 - 2 * m| := by
    rw [show 1 - 2 * (1 - m) = -(1 - 2 * m) by ring, abs_neg]
  simp only [B, phi, psi, H_complement, hz]

theorem B_H {m : ℝ} (hm : 0 < m) (hm' : m < 1) : B m (H m) = 0 := by
  by_cases hl : m ≤ 1 / 2
  · exact B_H_lower hm hl
  · rw [← B_complement m (H m), ← H_complement m]
    exact B_H_lower (by linarith) (by linarith)

end GeneralCK


namespace GeneralCK

/-- The contact equation has exactly one solution in the open lower half. -/
theorem existsUnique_radialContact {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    ∃! v : ℝ, 0 < v ∧ v < 1 / 2 ∧ z * H v = h * (1 - 2 * v) := by
  let g : ℝ → ℝ := fun v => z * H v - h * (1 - 2 * v)
  have hg : Continuous g :=
    (H_continuous.const_mul z).sub
      ((continuous_const.sub (continuous_const.mul continuous_id)).const_mul h)
  have hzero : g 0 = -h := by simp [g]
  have hhalf : g (1 / 2) = z := by simp only [g, H_half]; ring
  have himage := intermediate_value_Icc (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    hg.continuousOn
  obtain ⟨v, hv, heq⟩ := himage (show (0 : ℝ) ∈ Set.Icc (g 0) (g (1 / 2)) by
    rw [hzero, hhalf]; exact ⟨by linarith, hz.le⟩)
  have hv0 : 0 < v := by
    apply lt_of_le_of_ne hv.1
    intro he
    rw [← he, hzero] at heq
    linarith
  have hv1 : v < 1 / 2 := by
    apply lt_of_le_of_ne hv.2
    intro he
    rw [he, hhalf] at heq
    linarith
  have hveq : z * H v = h * (1 - 2 * v) := sub_eq_zero.mp heq
  refine ⟨v, ⟨hv0, hv1, hveq⟩, ?_⟩
  rintro u ⟨hu0, hu1, hueq⟩
  rcases lt_trichotomy u v with huv | huv | huv
  · have hH := H_strictMonoOn ⟨hu0.le, hu1.le⟩ ⟨hv0.le, hv1.le⟩ huv
    have hm := mul_lt_mul_of_pos_left hH hz
    nlinarith
  · exact huv
  · have hH := H_strictMonoOn ⟨hv0.le, hv1.le⟩ ⟨hu0.le, hu1.le⟩ huv
    have hm := mul_lt_mul_of_pos_left hH hz
    nlinarith

theorem radialContact_spec {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 < radialContact z h ∧ radialContact z h < 1 / 2 ∧
      z * H (radialContact z h) = h * (1 - 2 * radialContact z h) := by
  obtain ⟨v, hv, huniq⟩ := existsUnique_radialContact hz hh
  have hset : {u : ℝ | 0 < u ∧ u < 1 / 2 ∧ z * H u = h * (1 - 2 * u)} = {v} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun hu => huniq u hu, fun he => he ▸ hv⟩
  simpa only [radialContact, hset, csInf_singleton] using hv

theorem radialContact_pos {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 < radialContact z h := (radialContact_spec hz hh).1

theorem radialContact_lt_half {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    radialContact z h < 1 / 2 := (radialContact_spec hz hh).2.1

theorem radialContact_equation {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    z * H (radialContact z h) = h * (1 - 2 * radialContact z h) :=
  (radialContact_spec hz hh).2.2

theorem radialContact_eq_of_equation {z h v : ℝ} (hz : 0 < z) (hh : 0 < h)
    (hv : 0 < v) (hv' : v < 1 / 2) (heq : z * H v = h * (1 - 2 * v)) :
    radialContact z h = v := by
  obtain ⟨u, _, huniq⟩ := existsUnique_radialContact hz hh
  exact (huniq _ (radialContact_spec hz hh)).trans (huniq v ⟨hv, hv', heq⟩).symm

/-- Simultaneous nonzero scaling leaves the defining root set unchanged. -/
theorem radialContact_scale (z h : ℝ) {c : ℝ} (hc : c ≠ 0) :
    radialContact (c * z) (c * h) = radialContact z h := by
  unfold radialContact
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, mul_assoc, mul_right_inj' hc]

/-- Homogeneity includes the explicitly defined zero-radius branch. -/
theorem F_scale (z h c : ℝ) : F (c * z) (c * h) = c * F z h := by
  by_cases hc : c = 0
  · subst c; simp [F]
  by_cases hz : z = 0
  · subst z; simp [F]
  simp only [F, mul_ne_zero hc hz, hz, ↓reduceIte, radialContact_scale z h hc]
  ring

theorem radialContact_strictMono_entropy {z a b : ℝ}
    (hz : 0 < z) (ha : 0 < a) (hab : a < b) :
    radialContact z a < radialContact z b := by
  obtain ⟨hu, hu', hequ⟩ := radialContact_spec hz ha
  obtain ⟨hv, hv', heqv⟩ := radialContact_spec hz (ha.trans hab)
  by_contra hn
  have hvu : radialContact z b ≤ radialContact z a := le_of_not_gt hn
  have hH := H_strictMonoOn.monotoneOn ⟨hv.le, hv'.le⟩ ⟨hu.le, hu'.le⟩ hvu
  have hm := mul_le_mul_of_nonneg_left hH hz.le
  have hg : a * (1 - 2 * radialContact z a) < b * (1 - 2 * radialContact z b) := by
    calc
      a * (1 - 2 * radialContact z a) ≤ a * (1 - 2 * radialContact z b) :=
        mul_le_mul_of_nonneg_left (by linarith) ha.le
      _ < b * (1 - 2 * radialContact z b) :=
        mul_lt_mul_of_pos_right hab (by linarith)
  linarith

theorem radialContact_mono_entropy {z a b : ℝ}
    (hz : 0 < z) (ha : 0 < a) (hab : a ≤ b) :
    radialContact z a ≤ radialContact z b := by
  rcases hab.eq_or_lt with rfl | hab
  · exact le_rfl
  · exact (radialContact_strictMono_entropy hz ha hab).le

theorem radialContact_strictAnti_radius {a b h : ℝ}
    (ha : 0 < a) (hab : a < b) (hh : 0 < h) :
    radialContact b h < radialContact a h := by
  obtain ⟨hu, hu', hequ⟩ := radialContact_spec ha hh
  obtain ⟨hv, hv', heqv⟩ := radialContact_spec (ha.trans hab) hh
  by_contra hn
  have huv : radialContact a h ≤ radialContact b h := le_of_not_gt hn
  have hH := H_strictMonoOn.monotoneOn ⟨hu.le, hu'.le⟩ ⟨hv.le, hv'.le⟩ huv
  have hm := mul_le_mul_of_nonneg_left (show 1 - 2 * radialContact b h ≤
      1 - 2 * radialContact a h by linarith) hh.le
  have hg : a * H (radialContact a h) < b * H (radialContact b h) := by
    calc
      a * H (radialContact a h) ≤ a * H (radialContact b h) :=
        mul_le_mul_of_nonneg_left hH ha.le
      _ < b * H (radialContact b h) :=
        mul_lt_mul_of_pos_right hab (H_pos hv (by linarith))
  linarith

theorem radialContact_anti_radius {a b h : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hh : 0 < h) :
    radialContact b h ≤ radialContact a h := by
  rcases hab.eq_or_lt with rfl | hab
  · exact le_rfl
  · exact (radialContact_strictAnti_radius ha hab hh).le

theorem radialContact_normalize_radius {z : ℝ} (hz : z ≠ 0) (h : ℝ) :
    radialContact z h = radialContact 1 (h / z) := by
  have hs := radialContact_scale z h (c := z⁻¹) (inv_ne_zero hz)
  simpa only [inv_mul_cancel₀ hz, ← div_eq_inv_mul] using hs.symm

theorem radialContact_normalize_entropy (z : ℝ) {h : ℝ} (hh : h ≠ 0) :
    radialContact z h = radialContact (z / h) 1 := by
  have hs := radialContact_scale z h (c := h⁻¹) (inv_ne_zero hh)
  simpa only [inv_mul_cancel₀ hh, ← div_eq_inv_mul] using hs.symm

theorem F_perspective {h : ℝ} (hh : h ≠ 0) (z : ℝ) :
    F z h = h * F (z / h) 1 := by
  simpa only [mul_div_cancel₀ z hh, mul_one] using (F_scale (z / h) 1 h)

theorem radialContact_le_iff_ratio {z₁ z₂ h₁ h₂ : ℝ}
    (hz₁ : 0 < z₁) (hz₂ : 0 < z₂) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) :
    radialContact z₁ h₁ ≤ radialContact z₂ h₂ ↔ h₁ / z₁ ≤ h₂ / z₂ := by
  rw [radialContact_normalize_radius hz₁.ne', radialContact_normalize_radius hz₂.ne']
  constructor
  · intro hc
    by_contra hn
    have := radialContact_strictMono_entropy (z := 1) (by norm_num)
      (div_pos hh₂ hz₂) (lt_of_not_ge hn)
    exact (not_lt_of_ge hc) this
  · exact radialContact_mono_entropy (by norm_num) (div_pos hh₁ hz₁)

/-- A nonnegative residual certifies an upper contact bracket. -/
theorem radialContact_le_iff {z h v : ℝ} (hz : 0 < z) (hh : 0 < h)
    (hv : 0 ≤ v) (hv' : v ≤ 1 / 2) :
    radialContact z h ≤ v ↔ h * (1 - 2 * v) ≤ z * H v := by
  obtain ⟨hu, hu', heq⟩ := radialContact_spec hz hh
  constructor
  · intro huv
    have hH := H_strictMonoOn.monotoneOn ⟨hu.le, hu'.le⟩ ⟨hv, hv'⟩ huv
    have hm := mul_le_mul_of_nonneg_left hH hz.le
    have ht := mul_le_mul_of_nonneg_left
      (show 1 - 2 * v ≤ 1 - 2 * radialContact z h by linarith) hh.le
    linarith
  · intro hr
    by_contra hn
    have hvu := lt_of_not_ge hn
    have hH := H_strictMonoOn ⟨hv, hv'⟩ ⟨hu.le, hu'.le⟩ hvu
    have hm := mul_lt_mul_of_pos_left hH hz
    have ht := mul_lt_mul_of_pos_left
      (show 1 - 2 * radialContact z h < 1 - 2 * v by linarith) hh
    linarith

/-- A nonpositive residual certifies a lower contact bracket. -/
theorem le_radialContact_iff {z h v : ℝ} (hz : 0 < z) (hh : 0 < h)
    (hv : 0 ≤ v) (hv' : v ≤ 1 / 2) :
    v ≤ radialContact z h ↔ z * H v ≤ h * (1 - 2 * v) := by
  obtain ⟨hu, hu', heq⟩ := radialContact_spec hz hh
  constructor
  · intro hvu
    have hH := H_strictMonoOn.monotoneOn ⟨hv, hv'⟩ ⟨hu.le, hu'.le⟩ hvu
    have hm := mul_le_mul_of_nonneg_left hH hz.le
    have ht := mul_le_mul_of_nonneg_left
      (show 1 - 2 * radialContact z h ≤ 1 - 2 * v by linarith) hh.le
    linarith
  · intro hr
    by_contra hn
    have huv := lt_of_not_ge hn
    have hH := H_strictMonoOn ⟨hu.le, hu'.le⟩ ⟨hv, hv'⟩ huv
    have hm := mul_lt_mul_of_pos_left hH hz
    have ht := mul_lt_mul_of_pos_left
      (show 1 - 2 * v < 1 - 2 * radialContact z h by linarith) hh
    linarith

end GeneralCK


namespace GeneralCK

theorem entropyInverse_spec {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    0 ≤ entropyInverse h ∧ entropyInverse h ≤ 1 / 2 ∧ H (entropyInverse h) = h := by
  have himage := intermediate_value_Icc (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    H_continuous.continuousOn
  obtain ⟨v, hv, heq⟩ := himage (show h ∈ Set.Icc (H 0) (H (1 / 2)) by
    simpa only [H_zero, H_half, Set.mem_Icc] using And.intro h0 h1)
  rw [← heq, entropyInverse_H_lower hv.1 hv.2]
  exact ⟨hv.1, hv.2, rfl⟩

theorem entropyInverse_pos {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) :
    0 < entropyInverse h := by
  obtain ⟨hv, _, heq⟩ := entropyInverse_spec h0.le h1
  apply lt_of_le_of_ne hv
  intro he
  rw [← he, H_zero] at heq
  linarith

theorem entropyInverse_mono {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    entropyInverse a ≤ entropyInverse b := by
  obtain ⟨ha0, ha1, hea⟩ := entropyInverse_spec ha (hab.trans hb)
  obtain ⟨hb0, hb1, heb⟩ := entropyInverse_spec (ha.trans hab) hb
  by_contra hn
  have := H_strictMonoOn ⟨hb0, hb1⟩ ⟨ha0, ha1⟩ (lt_of_not_ge hn)
  rw [hea, heb] at this
  linarith

theorem J_nonneg {v : ℝ} (hv : 0 < v) (hv' : v ≤ 1 / 2) : 0 ≤ J v := by
  apply div_nonneg _ log_two_pos.le
  apply Real.log_nonneg
  apply (le_div_iff₀ hv).2
  linarith

theorem J_antitone {u v : ℝ} (hu : 0 < u) (hv : v ≤ 1 / 2) (huv : u ≤ v) :
    J v ≤ J u := by
  have hv0 : 0 < v := hu.trans_le huv
  apply (div_le_div_iff_of_pos_right log_two_pos).2
  apply Real.log_le_log (div_pos (by linarith) hv0)
  apply (div_le_div_iff₀ hv0 hu).2
  nlinarith

theorem eta_eq_profile {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    eta h = (1 - 2 * entropyInverse h) * J (entropyInverse h) := by
  by_cases heq : h = 1
  · subst h
    have hv : entropyInverse 1 = 1 / 2 := by
      simpa only [H_half] using entropyInverse_H_lower (v := (1 / 2 : ℝ))
        (by norm_num) le_rfl
    simp [eta, hv]
  · simp [eta, heq]

theorem eta_antitoneOn : AntitoneOn eta (Set.Ioc 0 1) := by
  intro a ha b hb hab
  rw [eta_eq_profile ha.1.le ha.2, eta_eq_profile hb.1.le hb.2]
  have huv := entropyInverse_mono ha.1.le hb.2 hab
  have hu := entropyInverse_pos ha.1 ha.2
  have hv := entropyInverse_pos hb.1 hb.2
  have hu' := (entropyInverse_spec ha.1.le ha.2).2.1
  have hv' := (entropyInverse_spec hb.1.le hb.2).2.1
  exact mul_le_mul (by linarith) (J_antitone hu hv' huv)
    (J_nonneg hv hv') (by linarith)

end GeneralCK


namespace GeneralCK.Comparison
open Set

/-- A continuous scalar curve cannot become positive if its right derivative is
nonpositive wherever the curve is positive. -/
theorem nonpos_of_deriv_nonpos_when_pos {g g' : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hc : ContinuousOn g (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt g (g' t) (Ici t) t)
    (h0 : g 0 ≤ 0)
    (hbound : ∀ t ∈ Ico 0 T, 0 < g t → g' t ≤ 0) : g T ≤ 0 := by
  by_contra hn
  have hp : 0 < g T := lt_of_not_ge hn
  let e := g T / (2 * (T + 1))
  have he : 0 < e := div_pos hp (by positivity)
  have hB : ∀ t : ℝ, HasDerivAt (fun s => e * (s + 1)) e t := by
    intro t
    simpa using ((hasDerivAt_id t).add_const 1).const_mul e
  have hb := image_le_of_deriv_right_lt_deriv_boundary hc hd
    (B := fun t => e * (t + 1)) (B' := fun _ => e)
    (by simpa using h0.trans he.le) hB (by
      intro t ht htB
      have hg : 0 < g t := by rw [htB]; exact mul_pos he (by linarith [ht.1])
      exact (hbound t ht hg).trans_lt he)
    (show T ∈ Icc 0 T from ⟨hT, le_rfl⟩)
  have heq : e * (T + 1) = g T / 2 := by
    dsimp [e]
    field_simp
  rw [heq] at hb
  linarith

/-- Comparison with an antitone scalar field. No differentiability of the field
itself, nor differentiation of an inverse function, is required. -/
theorem antitone_ode_comparison {field u v u' v' : ℝ → ℝ} {s : Set ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hf : AntitoneOn field s)
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hdu : ∀ t ∈ Ico 0 T, HasDerivWithinAt u (u' t) (Ici t) t)
    (hdv : ∀ t ∈ Ico 0 T, HasDerivWithinAt v (v' t) (Ici t) t)
    (hus : ∀ t ∈ Ico 0 T, u t ∈ s) (hvs : ∀ t ∈ Ico 0 T, v t ∈ s)
    (hu' : ∀ t ∈ Ico 0 T, u' t ≤ field (u t))
    (hv' : ∀ t ∈ Ico 0 T, field (v t) ≤ v' t)
    (h0 : u 0 ≤ v 0) : u T ≤ v T := by
  have h := nonpos_of_deriv_nonpos_when_pos hT (hu.sub hv)
    (fun t ht => (hdu t ht).sub (hdv t ht)) (sub_nonpos.mpr h0) (by
      intro t ht hpos
      change 0 < u t - v t at hpos
      have hf' := hf (hvs t ht) (hus t ht) (by linarith)
      have h₁ := hu' t ht
      have h₂ := hv' t ht
      linarith)
  exact sub_nonpos.mp h

/-- The Bernoulli parameter under the continuous-time binary noise flow. -/
noncomputable def noiseParameter (eps t : ℝ) : ℝ :=
  (1 - Real.exp (-2 * t) * (1 - 2 * eps)) / 2

theorem noiseParameter_mem {eps t : ℝ} (he : 0 < eps) (he' : eps < 1 / 2)
    (ht : 0 ≤ t) : noiseParameter eps t ∈ Ioo 0 (1 / 2) := by
  have hp := Real.exp_pos (-2 * t)
  have hle : Real.exp (-2 * t) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hm : 0 < 1 - 2 * eps := by linarith
  have hmul : Real.exp (-2 * t) * (1 - 2 * eps) ≤ 1 - 2 * eps :=
    mul_le_of_le_one_left hm.le hle
  have hmulpos := mul_pos hp hm
  dsimp [noiseParameter]
  constructor <;> linarith

@[simp] theorem noiseParameter_zero (eps : ℝ) : noiseParameter eps 0 = eps := by
  simp [noiseParameter]

theorem hasDerivAt_noiseParameter (eps t : ℝ) :
    HasDerivAt (noiseParameter eps) (1 - 2 * noiseParameter eps t) t := by
  have hd := (((hasDerivAt_id t).const_mul (-2)).exp.mul_const (1 - 2 * eps)).const_sub 1
  convert! hd.div_const 2 using 1
  simp only [noiseParameter, id_eq]
  ring

theorem hasDerivAt_H {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    HasDerivAt H (J p) p := by
  have hl : Real.log ((1 - p) / p) = Real.log (1 - p) - Real.log p :=
    Real.log_div (by linarith) (ne_of_gt hp)
  simpa [H, J, hl] using!
    (Real.hasDerivAt_binEntropy (ne_of_gt hp) (by linarith)).div_const (Real.log 2)

theorem eta_H {p : ℝ} (hp : 0 < p) (hp' : p < 1 / 2) :
    eta (H p) = (1 - 2 * p) * J p := by
  have hlt : H p < 1 := by
    rw [← H_half]
    exact H_strictMonoOn ⟨hp.le, hp'.le⟩ ⟨by norm_num, le_rfl⟩ hp'
  simp [eta, ne_of_lt hlt, entropyInverse_H_lower hp.le hp'.le]

theorem hasDerivAt_entropy_trajectory {eps t : ℝ}
    (he : 0 < eps) (he' : eps < 1 / 2) (ht : 0 ≤ t) :
    HasDerivAt (fun s => H (noiseParameter eps s))
      (eta (H (noiseParameter eps t))) t := by
  have hp := noiseParameter_mem he he' ht
  rw [eta_H hp.1 hp.2]
  convert! (hasDerivAt_H hp.1 (by linarith [hp.2])).comp t
    (hasDerivAt_noiseParameter eps t) using 1
  ring

/-- The explicit entropy trajectory is a lower bound for every supersolution
of the scalar entropy-production inequality. -/
theorem entropy_lower_bound {eps T : ℝ} {delta delta' : ℝ → ℝ}
    (he : 0 < eps) (he' : eps < 1 / 2) (hT : 0 ≤ T)
    (hc : ContinuousOn delta (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt delta (delta' t) (Ici t) t)
    (hrange : ∀ t ∈ Ico 0 T, delta t ∈ Ioc 0 1)
    (hprod : ∀ t ∈ Ico 0 T, eta (delta t) ≤ delta' t)
    (h0 : H eps ≤ delta 0) : H (noiseParameter eps T) ≤ delta T := by
  apply antitone_ode_comparison hT eta_antitoneOn
    (u := fun t => H (noiseParameter eps t))
    (u' := fun t => eta (H (noiseParameter eps t)))
    (v' := delta')
  · exact H_continuous.comp_continuousOn (fun t _ =>
      (hasDerivAt_noiseParameter eps t).continuousAt.continuousWithinAt)
  · exact hc
  · intro t ht
    exact (hasDerivAt_entropy_trajectory he he' ht.1).hasDerivWithinAt
  · exact hd
  · intro t ht
    have hp := noiseParameter_mem he he' ht.1
    exact ⟨H_pos hp.1 (by linarith [hp.2]), H_le_one _⟩
  · exact hrange
  · intro _ _
    exact le_rfl
  · exact hprod
  · simpa using h0

end GeneralCK.Comparison


namespace GeneralCK
open Set Filter
open scoped Topology

theorem entropyInverse_lt_half {h : ℝ} (h0 : 0 ≤ h) (h1 : h < 1) :
    entropyInverse h < 1 / 2 := by
  obtain ⟨_, hv, heq⟩ := entropyInverse_spec h0 h1.le
  apply lt_of_le_of_ne hv
  intro hh
  rw [hh, H_half] at heq
  linarith

theorem entropyInverse_strictMonoOn : StrictMonoOn entropyInverse (Icc 0 1) := by
  intro a ha b hb hab
  apply lt_of_le_of_ne (entropyInverse_mono ha.1 hb.2 hab.le)
  intro he
  have h := congrArg H he
  rw [(entropyInverse_spec ha.1 ha.2).2.2, (entropyInverse_spec hb.1 hb.2).2.2] at h
  exact ne_of_lt hab h

theorem entropyInverse_image : entropyInverse '' Icc 0 1 = Icc 0 (1 / 2) := by
  ext v
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨(entropyInverse_spec hh.1 hh.2).1, (entropyInverse_spec hh.1 hh.2).2.1⟩
  · intro hv
    exact ⟨H v, ⟨H_nonneg hv.1 (by linarith [hv.2]), H_le_one v⟩,
      entropyInverse_H_lower hv.1 hv.2⟩

theorem continuousAt_entropyInverse {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    ContinuousAt entropyInverse h := by
  apply entropyInverse_strictMonoOn.continuousAt_of_image_mem_nhds
    (Icc_mem_nhds h0 h1)
  rw [entropyInverse_image]
  exact Icc_mem_nhds (entropyInverse_pos h0 h1.le) (entropyInverse_lt_half h0.le h1)

theorem J_pos {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) : 0 < J v := by
  apply div_pos _ log_two_pos
  apply Real.log_pos
  apply (lt_div_iff₀ hv).2
  linarith

theorem hasDerivAt_entropyInverse {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    HasDerivAt entropyInverse (1 / J (entropyInverse h)) h := by
  have hv := entropyInverse_pos h0 h1.le
  have hv' := entropyInverse_lt_half h0.le h1
  have hd := (Comparison.hasDerivAt_H hv (by linarith)).of_local_left_inverse
    (continuousAt_entropyInverse h0 h1) (ne_of_gt (J_pos hv hv')) (by
      filter_upwards [Ioo_mem_nhds h0 h1] with y hy
      exact (entropyInverse_spec hy.1.le hy.2.le).2.2)
  simpa only [one_div] using hd

theorem hasDerivAt_J {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    HasDerivAt J (-1 / (Real.log 2 * v * (1 - v))) v := by
  have hv1 : 1 - v ≠ 0 := by linarith
  have hlog : J =ᶠ[𝓝 v] (fun p => (Real.log (1 - p) - Real.log p) / Real.log 2) := by
    filter_upwards [Ioo_mem_nhds hv hv'] with p hp
    simp only [J, Real.log_div (by linarith [hp.2] : 1 - p ≠ 0) (ne_of_gt hp.1)]
  have hd := (((hasDerivAt_id v).const_sub 1).log (by simpa using hv1)).sub
    ((hasDerivAt_id v).log (ne_of_gt hv))
  have hd' := (hd.div_const (Real.log 2)).congr_of_eventuallyEq hlog
  convert! hd' using 1
  simp only [id_eq]
  field_simp [hv1]
  ring

/-- First entropy-coordinate derivative of the scalar production profile. -/
theorem hasDerivAt_eta {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    HasDerivAt eta
      (-2 - (1 - 2 * entropyInverse h) /
        (Real.log 2 * entropyInverse h * (1 - entropyInverse h) * J (entropyInverse h))) h := by
  have hv := entropyInverse_pos h0 h1.le
  have hv' := entropyInverse_lt_half h0.le h1
  have hJ : J (entropyInverse h) ≠ 0 := ne_of_gt (J_pos hv hv')
  have hi := hasDerivAt_entropyInverse h0 h1
  have hd := (hi.const_mul 2).const_sub 1 |>.mul
    ((hasDerivAt_J hv (by linarith)).comp h hi)
  have heq : eta =ᶠ[𝓝 h] (fun y => (1 - 2 * entropyInverse y) * J (entropyInverse y)) := by
    filter_upwards [Ioo_mem_nhds h0 h1] with y hy
    exact eta_eq_profile hy.1.le hy.2.le
  have hd' := hd.congr_of_eventuallyEq heq
  convert! hd' using 1
  simp only [Function.comp_apply]
  field_simp [hJ]
  ring

theorem deriv_entropyInverse {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    deriv entropyInverse h = 1 / J (entropyInverse h) :=
  (hasDerivAt_entropyInverse h0 h1).deriv

theorem deriv_J {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    deriv J v = -1 / (Real.log 2 * v * (1 - v)) :=
  (hasDerivAt_J hv hv').deriv

theorem deriv_eta {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    deriv eta h = -2 - (1 - 2 * entropyInverse h) /
      (Real.log 2 * entropyInverse h * (1 - entropyInverse h) * J (entropyInverse h)) :=
  (hasDerivAt_eta h0 h1).deriv

end GeneralCK


namespace GeneralCK.Certificates
open scoped BigOperators

/-- Rational partial sum for log((1+w)/(1-w)). -/
def logLower (w : ℚ) (n : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range n, w ^ (2 * i + 1) / (2 * i + 1)

/-- A conservative, proved Taylor remainder. -/
def logUpper (w : ℚ) (n : ℕ) : ℚ :=
  logLower w n + 2 * w ^ (2 * n + 1) / (1 - w ^ 2)

/-- Acceptance uses exact rational arithmetic only. -/
def checkLog (w : ℚ) (n : ℕ) (lo hi : ℚ) : Bool :=
  decide (0 ≤ w ∧ w < 1 ∧ lo ≤ logLower w n ∧ logUpper w n ≤ hi)

/-- Soundness connects the executable rational checker to the real logarithm. -/
theorem checkLog_sound {w lo hi : ℚ} {n : ℕ}
    (hc : checkLog w n lo hi = true) :
    (lo : ℝ) ≤ Real.log ((1 + (w : ℝ)) / (1 - (w : ℝ))) ∧
    Real.log ((1 + (w : ℝ)) / (1 - (w : ℝ))) ≤ (hi : ℝ) := by
  have hh : 0 ≤ w ∧ w < 1 ∧ lo ≤ logLower w n ∧ logUpper w n ≤ hi :=
    of_decide_eq_true hc
  obtain ⟨hw₀, hw₁, hl, hu⟩ := hh
  have hw₀' : (0 : ℝ) ≤ w := by exact_mod_cast hw₀
  have hw₁' : (w : ℝ) < 1 := by exact_mod_cast hw₁
  have lower := Real.sum_range_le_log_div hw₀' hw₁' n
  have upper := Real.log_div_le_sum_range_add hw₀' hw₁' n
  dsimp [logLower, logUpper] at hl hu
  have hl' : (lo : ℝ) ≤
      2 * ∑ i ∈ Finset.range n, (w : ℝ) ^ (2 * i + 1) / (2 * i + 1) := by
    exact_mod_cast hl
  have hu' :
      2 * ∑ i ∈ Finset.range n, (w : ℝ) ^ (2 * i + 1) / (2 * i + 1) +
      2 * (w : ℝ) ^ (2 * n + 1) / (1 - (w : ℝ) ^ 2) ≤ (hi : ℝ) := by
    exact_mod_cast hu
  rw [mul_div_assoc] at hu'
  constructor <;> linarith

end GeneralCK.Certificates


/-! Generated rational witnesses for the retained diagonal contact pilot. -/
namespace GeneralCK.Certificates.PilotData

theorem log_two :
    (34657359 / 50000000) ≤ Real.log (2 / 1) ∧
    Real.log (2 / 1) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000)) (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem log_scaled_left :
    (262151201 / 500000000) ≤ Real.log (5279 / 3125) ∧
    Real.log (5279 / 3125) ≤ (524302403 / 1000000000) := by
  have h := checkLog_sound (w := (1077 / 4202)) (n := 12)
    (lo := (262151201 / 500000000)) (hi := (524302403 / 1000000000)) (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem log_scaled_right :
    (262245907 / 500000000) ≤ Real.log (1056 / 625) ∧
    Real.log (1056 / 625) ≤ (104898363 / 200000000) := by
  have h := checkLog_sound (w := (431 / 1681)) (n := 12)
    (lo := (262245907 / 500000000)) (hi := (104898363 / 200000000)) (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem log_inv_complement_left :
    (54234457 / 1000000000) ≤ Real.log (100000 / 94721) ∧
    Real.log (100000 / 94721) ≤ (27117229 / 500000000) := by
  have h := checkLog_sound (w := (5279 / 194721)) (n := 12)
    (lo := (54234457 / 1000000000)) (hi := (27117229 / 500000000)) (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem log_inv_complement_right :
    (27122507 / 500000000) ≤ Real.log (625 / 592) ∧
    Real.log (625 / 592) ≤ (10849003 / 200000000) := by
  have h := checkLog_sound (w := (33 / 1217)) (n := 12)
    (lo := (27122507 / 500000000)) (hi := (10849003 / 200000000)) (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.PilotData


namespace GeneralCK.Certificates.Mixed

noncomputable def hn (v : ℝ) : ℝ := -v * Real.log v - (1-v) * Real.log (1-v)
noncomputable def kap (v : ℝ) : ℝ := -Real.log (v*(1-v))/2
noncomputable def profile (v : ℝ) : ℝ :=
  2*(1-2*v)*(hn v)^2*(2*kap v-(1-2*v)^2) /
    (Real.log 2*(4*v*(1-v))^2*(kap v)^3)


end GeneralCK.Certificates.Mixed


namespace GeneralCK
open Set Filter
open scoped Topology

theorem radialContact_image_radius {h : ℝ} (hh : 0 < h) :
    (fun z => radialContact z h) '' Ioi 0 = Ioo 0 (1 / 2) := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨radialContact_pos hz hh, radialContact_lt_half hz hh⟩
  · intro hv
    have hH : 0 < H v := H_pos hv.1 (by linarith [hv.2])
    have hz : 0 < h * (1 - 2 * v) / H v :=
      div_pos (mul_pos hh (by linarith [hv.2])) hH
    refine ⟨h * (1 - 2 * v) / H v, hz, ?_⟩
    apply radialContact_eq_of_equation hz hh hv.1 hv.2
    exact div_mul_cancel₀ _ hH.ne'

theorem continuousAt_radialContact_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    ContinuousAt (fun r => radialContact r h) z := by
  have hanti : StrictAntiOn (fun r => radialContact r h) (Ioi 0) :=
    fun a ha b _ hab => radialContact_strictAnti_radius ha hab hh
  apply hanti.dual_right.continuousAt_of_image_mem_nhds (Ioi_mem_nhds hz)
  change (fun r => radialContact r h) '' Ioi 0 ∈ 𝓝 (radialContact z h)
  rw [radialContact_image_radius hh]
  exact Ioo_mem_nhds (radialContact_pos hz hh) (radialContact_lt_half hz hh)

theorem radialContact_denominator_pos {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 < z * J (radialContact z h) + 2 * h := by
  have hJ := J_pos (radialContact_pos hz hh) (radialContact_lt_half hz hh)
  positivity

theorem hasDerivAt_radialContact_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (fun r => radialContact r h)
      (-H (radialContact z h) / (z * J (radialContact z h) + 2 * h)) z := by
  let v := radialContact z h
  have hv : 0 < v := radialContact_pos hz hh
  have hv' : v < 1 / 2 := radialContact_lt_half hz hh
  have hH : H v ≠ 0 := (H_pos hv (by linarith)).ne'
  have heq : h * (1 - 2 * v) = z * H v := (radialContact_equation hz hh).symm
  have hd : HasDerivAt (fun u => h * (1 - 2 * u) / H u)
      (-(z * J v + 2 * h) / H v) v := by
    have hd := ((((hasDerivAt_id v).const_mul 2).const_sub 1).const_mul h).div
      (Comparison.hasDerivAt_H hv (by linarith)) hH
    convert! hd using 1
    simp only [id_eq, mul_one, heq]
    field_simp
    ring
  have hD : z * J v + 2 * h ≠ 0 := (radialContact_denominator_pos hz hh).ne'
  have hinv := hd.of_local_left_inverse (continuousAt_radialContact_radius hz hh)
    (div_ne_zero (neg_ne_zero.mpr hD) hH) (by
      filter_upwards [Ioi_mem_nhds hz] with r hr
      have hp := H_pos (radialContact_pos hr hh)
        (show radialContact r h < 1 by linarith [radialContact_lt_half hr hh])
      rw [← radialContact_equation hr hh]
      exact mul_div_cancel_right₀ r hp.ne')
  convert! hinv using 1
  change -H v / (z * J v + 2 * h) = (-(z * J v + 2 * h) / H v)⁻¹
  rw [inv_div, div_neg, neg_div]

theorem deriv_radialContact_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    deriv (fun r => radialContact r h) z =
      -H (radialContact z h) / (z * J (radialContact z h) + 2 * h) :=
  (hasDerivAt_radialContact_radius hz hh).deriv

theorem hasDerivAt_F_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (fun r => F r h)
      (J (radialContact z h) + z * H (radialContact z h) /
        (Real.log 2 * radialContact z h * (1 - radialContact z h) *
          (z * J (radialContact z h) + 2 * h))) z := by
  have hv := radialContact_pos hz hh
  have hv' : radialContact z h < 1 := by linarith [radialContact_lt_half hz hh]
  have hd := (hasDerivAt_id z).mul
    ((hasDerivAt_J hv hv').comp z (hasDerivAt_radialContact_radius hz hh))
  have heq : (fun r => F r h) =ᶠ[𝓝 z] (fun r => r * J (radialContact r h)) := by
    filter_upwards [Ioi_mem_nhds hz] with r hr
    simp only [F, ne_of_gt (show 0 < r from hr), ↓reduceIte]
  have hd' := hd.congr_of_eventuallyEq heq
  convert! hd' using 1
  simp only [id_eq, one_mul, Function.comp_apply, div_eq_mul_inv, mul_inv_rev]
  ring

theorem deriv_F_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    deriv (fun r => F r h) z =
      J (radialContact z h) + z * H (radialContact z h) /
        (Real.log 2 * radialContact z h * (1 - radialContact z h) *
          (z * J (radialContact z h) + 2 * h)) :=
  (hasDerivAt_F_radius hz hh).deriv

namespace Certificates.Mixed

theorem hn_eq_H_mul_log (v : ℝ) : hn v = H v * Real.log 2 := by
  unfold hn H Real.binEntropy
  simp only [Real.log_inv]
  rw [div_mul_cancel₀ _ log_two_pos.ne']
  ring

theorem kap_identity {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    2 * kap v = 2 * hn v + (1 - 2 * v) * (Real.log 2 * J v) := by
  unfold kap hn J
  rw [Real.log_mul hv.ne' (by linarith), Real.log_div (by linarith) hv.ne']
  field_simp
  ring

theorem kap_pos {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) : 0 < kap v := by
  have hi := kap_identity hv (show v < 1 by linarith)
  have hhn : 0 < hn v := by
    rw [hn_eq_H_mul_log]
    exact mul_pos (H_pos hv (by linarith)) log_two_pos
  have hj := J_pos hv hv'
  have hr : 0 < (1 - 2 * v) * (Real.log 2 * J v) :=
    mul_pos (by linarith) (mul_pos log_two_pos hj)
  linarith

theorem hasDerivAt_hn {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    HasDerivAt hn (J v * Real.log 2) v := by
  simpa only [← hn_eq_H_mul_log] using
    (Comparison.hasDerivAt_H hv hv').mul_const (Real.log 2)

theorem hasDerivAt_kap {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    HasDerivAt kap (-(1 - 2 * v) / (2 * v * (1 - v))) v := by
  have hd := (((hasDerivAt_id v).mul ((hasDerivAt_id v).const_sub 1)).log
    (mul_ne_zero hv.ne' (by simpa using (show 1 - v ≠ 0 by linarith)))).neg.div_const 2
  convert! hd using 1
  simp only [id_eq, one_mul, Pi.mul_apply]
  field_simp
  ring

end Certificates.Mixed

open Certificates.Mixed

noncomputable def radialSlope (v : ℝ) : ℝ :=
  J v + (1 - 2 * v) * hn v / (2 * Real.log 2 * v * (1 - v) * kap v)

theorem hasDerivAt_radialSlope {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) :
    HasDerivAt radialSlope
      (-hn v * (2 * kap v - (1 - 2 * v)^2) /
        (4 * Real.log 2 * v^2 * (1 - v)^2 * (kap v)^2)) v := by
  have hv1 : v < 1 := by linarith
  have hL : Real.log 2 ≠ 0 := log_two_pos.ne'
  have hvc : 1 - v ≠ 0 := by linarith
  have hr : 1 - 2 * v ≠ 0 := by linarith
  have hk : kap v ≠ 0 := (kap_pos hv hv').ne'
  have hJ : J v = (2 * kap v - 2 * hn v) / ((1 - 2 * v) * Real.log 2) := by
    apply (eq_div_iff (mul_ne_zero hr hL)).2
    nlinarith [kap_identity hv hv1]
  have hdN := (((hasDerivAt_id v).const_mul 2).const_sub 1).mul (hasDerivAt_hn hv hv1)
  have hdD := (((hasDerivAt_id v).const_mul (2 * Real.log 2)).mul
    ((hasDerivAt_id v).const_sub 1)).mul (hasDerivAt_kap hv hv1)
  have hd := (hasDerivAt_J hv hv1).add (hdN.div hdD (by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hL) hv.ne') hvc) hk))
  convert! hd using 1
  simp only [id_eq, mul_one, Pi.mul_apply]
  rw [hJ]
  field_simp
  ring

theorem radialContact_denominator_identity {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    (z * J (radialContact z h) + 2 * h) * (1 - 2 * radialContact z h) * Real.log 2 =
      2 * z * kap (radialContact z h) := by
  have hv := radialContact_pos hz hh
  have hv' : radialContact z h < 1 := by linarith [radialContact_lt_half hz hh]
  have hk := kap_identity hv hv'
  rw [hn_eq_H_mul_log] at hk
  have heq := radialContact_equation hz hh
  linear_combination -z * hk - (2 * Real.log 2) * heq

theorem hasDerivAt_F_radius_slope {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (fun r => F r h) (radialSlope (radialContact z h)) z := by
  have hv := radialContact_pos hz hh
  have hv' := radialContact_lt_half hz hh
  have hD := (radialContact_denominator_pos hz hh).ne'
  have hK := (kap_pos hv hv').ne'
  have hvc : 1 - radialContact z h ≠ 0 := by linarith
  have hL := log_two_pos.ne'
  have hi := radialContact_denominator_identity hz hh
  convert! hasDerivAt_F_radius hz hh using 1
  unfold radialSlope
  rw [hn_eq_H_mul_log]
  field_simp [hD, hK, hvc, hL, hv.ne']
  field_simp [show J (radialContact z h) * z + 2 * h ≠ 0 by
    simpa only [mul_comm] using hD]
  linear_combination H (radialContact z h) * hi

theorem deriv_F_radius_slope {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    deriv (fun r => F r h) z = radialSlope (radialContact z h) :=
  (hasDerivAt_F_radius_slope hz hh).deriv

theorem hasDerivAt_deriv_F_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (deriv (fun r => F r h))
      (hn (radialContact z h) * (2 * kap (radialContact z h) -
          (1 - 2 * radialContact z h)^2) * H (radialContact z h) /
        (4 * Real.log 2 * (radialContact z h)^2 * (1 - radialContact z h)^2 *
          (kap (radialContact z h))^2 * (z * J (radialContact z h) + 2 * h))) z := by
  have hd := (hasDerivAt_radialSlope (radialContact_pos hz hh)
    (radialContact_lt_half hz hh)).comp z (hasDerivAt_radialContact_radius hz hh)
  have heq : deriv (fun r => F r h) =ᶠ[𝓝 z] (fun r => radialSlope (radialContact r h)) := by
    filter_upwards [Ioi_mem_nhds hz] with r hr
    exact deriv_F_radius_slope hr hh
  have hd' := hd.congr_of_eventuallyEq heq
  convert! hd' using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem radius_mul_deriv2_F_eq_profile {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    z * deriv (deriv (fun r => F r h)) z = profile (radialContact z h) := by
  rw [(hasDerivAt_deriv_F_radius hz hh).deriv]
  have hv := radialContact_pos hz hh
  have hv' := radialContact_lt_half hz hh
  have hD := (radialContact_denominator_pos hz hh).ne'
  have hK := (kap_pos hv hv').ne'
  have hvc : 1 - radialContact z h ≠ 0 := by linarith
  have hL := log_two_pos.ne'
  have hi := radialContact_denominator_identity hz hh
  unfold profile
  rw [hn_eq_H_mul_log]
  field_simp [hD, hK, hvc, hL, hv.ne']
  linear_combination -2 * (H (radialContact z h))^2 *
    (2 * kap (radialContact z h) - (1 - 2 * radialContact z h)^2) * hi

end GeneralCK


namespace GeneralCK
open Set Filter
open scoped Topology BigOperators

theorem F_nonneg {z h : ℝ} (hz : 0 ≤ z) (hh : 0 < h) : 0 ≤ F z h := by
  rcases hz.eq_or_lt with rfl | hz
  · simp [F]
  · simp only [F, hz.ne', ↓reduceIte]
    exact mul_nonneg hz.le (J_nonneg (radialContact_pos hz hh)
      (radialContact_lt_half hz hh).le)

theorem F_mono_radius {a b h : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hh : 0 < h) :
    F a h ≤ F b h := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa [F] using F_nonneg hab hh
  have hb : 0 < b := ha.trans_le hab
  have hj := J_antitone (radialContact_pos hb hh) (radialContact_lt_half ha hh).le
    (radialContact_anti_radius ha hab hh)
  simp only [F, ha.ne', hb.ne', ↓reduceIte]
  exact mul_le_mul hab hj (J_nonneg (radialContact_pos ha hh)
    (radialContact_lt_half ha hh).le) hb.le

theorem F_le_linear_near_zero {z h : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1) (hh : 0 < h) :
    F z h ≤ z * J (radialContact 1 h) := by
  rcases hz.eq_or_lt with rfl | hz
  · simp [F]
  simp only [F, hz.ne', ↓reduceIte]
  exact mul_le_mul_of_nonneg_left
    (J_antitone (radialContact_pos (by norm_num : (0 : ℝ) < 1) hh)
      (radialContact_lt_half hz hh).le (radialContact_anti_radius hz hz' hh)) hz.le

theorem continuousWithinAt_F_zero {h : ℝ} (hh : 0 < h) :
    ContinuousWithinAt (fun z => F z h) (Ici 0) 0 := by
  change Tendsto (fun z => F z h) (𝓝[Ici 0] 0) (𝓝 (F 0 h))
  simp only [F, ↓reduceIte]
  apply squeeze_zero'
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact F_nonneg hz hh
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with z hz hz'
    exact F_le_linear_near_zero hz hz'.le hh
  · have ht := (tendsto_id.mul_const (J (radialContact 1 h))).mono_left
      (show 𝓝[Ici (0 : ℝ)] 0 ≤ 𝓝 0 from nhdsWithin_le_nhds)
    simpa using ht

theorem continuousOn_F_radius {h : ℝ} (hh : 0 < h) :
    ContinuousOn (fun z => F z h) (Ici 0) := by
  intro z hz
  change 0 ≤ z at hz
  rcases hz.eq_or_lt with rfl | hz
  · exact continuousWithinAt_F_zero hh
  · exact (hasDerivAt_F_radius hz hh).continuousAt.continuousWithinAt

theorem kap_sq_gap_nonneg {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    0 ≤ 2 * Certificates.Mixed.kap v - (1 - 2*v)^2 := by
  have hp : 0 < v*(1-v) := mul_pos hv (by linarith)
  have hl := Real.log_le_sub_one_of_pos hp
  unfold Certificates.Mixed.kap
  nlinarith only [hl, hp]

theorem deriv2_F_radius_nonneg {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 ≤ deriv (deriv (fun r => F r h)) z := by
  rw [(hasDerivAt_deriv_F_radius hz hh).deriv]
  have hv := radialContact_pos hz hh
  have hv' : radialContact z h < 1 := by linarith [radialContact_lt_half hz hh]
  have hH := (H_pos hv hv').le
  have hn : 0 ≤ Certificates.Mixed.hn (radialContact z h) := by
    rw [Certificates.Mixed.hn_eq_H_mul_log]
    exact mul_nonneg hH log_two_pos.le
  have hg := kap_sq_gap_nonneg hv hv'
  have hd := (radialContact_denominator_pos hz hh).le
  exact div_nonneg (mul_nonneg (mul_nonneg hn hg) hH) (by positivity)

theorem convexOn_F_radius {h : ℝ} (hh : 0 < h) :
    ConvexOn ℝ (Ici 0) (fun z => F z h) := by
  apply convexOn_of_deriv2_nonneg (convex_Ici 0) (continuousOn_F_radius hh)
  · intro z hz
    exact (hasDerivAt_F_radius (by simpa using hz) hh).differentiableAt.differentiableWithinAt
  · intro z hz
    exact (hasDerivAt_deriv_F_radius (by simpa using hz) hh).differentiableAt.differentiableWithinAt
  · intro z hz
    exact deriv2_F_radius_nonneg (by simpa using hz) hh


end GeneralCK

namespace GeneralCK
open Set

lemma radialContact_hom {z h : ℝ} (hh : 0 < h) : radialContact z h = radialContact (z / h) 1 := by
  unfold radialContact
  congr 1
  ext v
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    field_simp
    linarith
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    field_simp at h3
    linarith

lemma F_hom {z h : ℝ} (hh : 0 < h) : F z h = h * F (z / h) 1 := by
  by_cases hz : z = 0
  · simp [F, hz]
  · have hz' : z / h ≠ 0 := div_ne_zero hz hh.ne'
    unfold F
    rw [if_neg hz, if_neg hz', radialContact_hom hh]
    field_simp

lemma F_mixed {za zc e f : ℝ} (hf : 0 < f) (hfe : f < e) (hzc : 0 ≤ zc) (hzz : zc ≤ za) :
    F za e - F za f ≤ F zc e - F zc f := by
  have he : 0 < e := hf.trans hfe
  rcases hzc.eq_or_lt with rfl | hzc
  · have h0 : F 0 e = 0 := by simp [F]
    have h0' : F 0 f = 0 := by simp [F]
    rw [h0, h0']
    rcases hzz.eq_or_lt with rfl | hza
    · simp [F]
    · have hlt := radialContact_strictMono_entropy hza hf hfe
      have hj := J_antitone (radialContact_pos hza hf) (radialContact_lt_half hza he).le hlt.le
      have : F za e ≤ F za f := by
        simp only [F, hza.ne', ↓reduceIte]
        exact mul_le_mul_of_nonneg_left hj hza.le
      linarith
  · rcases hzz.eq_or_lt with rfl | hza
    · simp
    · have hc := convexOn_F_radius (h := 1) one_pos
      set Γ : ℝ → ℝ := fun s => F s 1 with hΓ
      have hx1 : 0 < zc / e := div_pos hzc he
      have hx12 : zc / e < za / e := div_lt_div_of_pos_right hza he
      have hy1 : zc / f < za / f := div_lt_div_of_pos_right hza hf
      have hxy1 : zc / e < zc / f := div_lt_div_of_pos_left hzc hf hfe
      have hxy2 : za / e < za / f := div_lt_div_of_pos_left (hzc.trans hza) hf hfe
      have m1 := hc.secant_mono_aux2 (x := zc / e) (y := za / e) (z := za / f)
        (le_of_lt hx1) (le_of_lt (hx1.trans (hx12.trans hxy2))) hx12 hxy2
      have m2 := hc.secant_mono_aux3 (x := zc / e) (y := zc / f) (z := za / f)
        (le_of_lt hx1) (le_of_lt (hx1.trans (hxy1.trans hy1))) hxy1 hy1
      have hS := m1.trans m2
      have hd : 0 < za - zc := by linarith
      have e1 : za / e - zc / e = (za - zc) / e := by ring
      have e2 : za / f - zc / f = (za - zc) / f := by ring
      simp only [hΓ] at hS
      rw [e1, e2] at hS
      rw [div_le_div_iff₀ (div_pos hd he) (div_pos hd hf)] at hS
      rw [F_hom (z := za) he, F_hom (z := zc) he, F_hom (z := za) hf, F_hom (z := zc) hf]
      set A := F (za / e) 1 - F (zc / e) 1
      set B := F (za / f) 1 - F (zc / f) 1
      have key : A * e ≤ B * f := by
        have h1 : A * ((za - zc) / f) * (e * f / (za - zc)) = A * e := by field_simp
        have h2 : B * ((za - zc) / e) * (e * f / (za - zc)) = B * f := by field_simp
        have hp : 0 ≤ e * f / (za - zc) := by positivity
        rw [← h1, ← h2]
        exact mul_le_mul_of_nonneg_right hS hp
      simp only [A, B] at key
      nlinarith [key]

end GeneralCK

namespace MIBF.Balanced

lemma kappaEnt_symm (e f : ℝ) : kappaEnt e f = kappaEnt f e := by
  unfold kappaEnt kappa GeneralCK.interiorCost
  generalize GeneralCK.entropyInverse e = u
  generalize GeneralCK.entropyInverse f = w
  rw [abs_sub_comm, add_comm (GeneralCK.H u)]
  ring

lemma part1 : ∀ a c e f : ℝ, InRS a c e f → f < e → pureGap a c f e ≤ pureGap a c e f := by
  rintro a c e f ⟨ha, hac, hc, -, he, -, hf, -⟩ hfe
  unfold pureGap Rphi
  rw [kappaEnt_symm f e, add_comm f e]
  unfold GeneralCK.phi
  have hz : |1 - 2 * a| = 1 - 2 * a := abs_of_nonneg (by linarith)
  have hz' : |1 - 2 * c| = 1 - 2 * c := abs_of_nonneg (by linarith)
  rw [hz, hz']
  have := GeneralCK.F_mixed (za := 1 - 2 * a) (zc := 1 - 2 * c) hf hfe (by linarith) (by linarith)
  linarith

end MIBF.Balanced

open MIBF.Balanced in
theorem solution : (∀ a c e f : ℝ, InRS a c e f → f < e → pureGap a c f e ≤ pureGap a c e f) ∧
      (∀ a c e f : ℝ, InRS a c e f → pureGap a c e f < 0 →
        ∃ a' c' e' f' : ℝ, InRS a' c' e' f' ∧ e' ≤ f' ∧ pureGap a' c' e' f' < 0) := by
  refine ⟨MIBF.Balanced.part1, ?_⟩
  intro a c e f hmem hneg
  rcases le_or_gt e f with hef | hfe
  · exact ⟨a, c, e, f, hmem, hef, hneg⟩
  · obtain ⟨ha, hac, hc, hS, he, heH, hf, hfH⟩ := hmem
    have hHac : GeneralCK.H a ≤ GeneralCK.H c := by
      unfold GeneralCK.H
      have := Real.binEntropy_strictMonoOn.monotoneOn (Set.mem_Icc.2 ⟨ha, by linarith⟩)
        (Set.mem_Icc.2 ⟨by linarith, by linarith⟩) hac
      exact div_le_div_of_nonneg_right this (Real.log_pos (by norm_num)).le
    refine ⟨a, c, f, e, ⟨ha, hac, hc, hS, hf, by linarith, he, by linarith⟩, hfe.le, ?_⟩
    exact lt_of_le_of_lt (MIBF.Balanced.part1 a c e f ⟨ha, hac, hc, hS, he, heH, hf, hfH⟩ hfe) hneg


