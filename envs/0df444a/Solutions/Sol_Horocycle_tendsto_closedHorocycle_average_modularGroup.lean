-- Prove2me | solution 1 for Horocycle.tendsto_closedHorocycle_average_modularGroup
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T20:13:21.684306+00:00
-- url     : https://prove2.me/submissions/8045ff22-10f4-4192-9d35-5863fd82fa06
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AutomorphicForm_FundamentalDomainExactVolume
import Theorems.Thm_Horocycle_tendsto_closedHorocycle_average_of_vanishing_near_cusp

open UpperHalfPlane MeasureTheory Filter Topology
open scoped MatrixGroups

set_option autoImplicit false

namespace Sol_Horocycle_tendsto_closedHorocycle_average_modularGroup

/-- The invariant height `sup_γ Im(γ z)`. -/
noncomputable def hgt (z : ℍ) : ℝ := ⨆ g : SL(2, ℤ), (g • z).im

lemma bdd_hgt (z : ℍ) : BddAbove (Set.range fun g : SL(2, ℤ) => (g • z).im) := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_max_im z
  exact ⟨(g • z).im, by rintro _ ⟨g', rfl⟩; exact hg g'⟩

lemma le_hgt (z : ℍ) (g : SL(2, ℤ)) : (g • z).im ≤ hgt z := le_ciSup (bdd_hgt z) g

lemma im_le_hgt (z : ℍ) : z.im ≤ hgt z := by simpa using le_hgt z 1

lemma hgt_smul (g : SL(2, ℤ)) (z : ℍ) : hgt (g • z) = hgt z := by
  unfold hgt
  simp_rw [← mul_smul]
  exact (Equiv.mulRight g).iSup_comp (g := fun g' => (g' • z).im)

/-- `Im (g • z)` in terms of the bottom row. -/
lemma im_smul_eq (g : SL(2, ℤ)) (z : ℍ) :
    (g • z).im = z.im / Complex.normSq (((↑g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * z +
      ((↑g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ)) := by
  rw [ModularGroup.im_smul_eq_div_normSq]
  simp [ModularGroup.denom_apply]

lemma int_ineq (c d : ℤ) (h : c ≠ 0 ∨ d ≠ 0) : 1 ≤ c ^ 2 - |c * d| + d ^ 2 := by
  rcases h with h | h
  · rcases eq_or_ne d 0 with hd | hd
    · subst hd; simp; exact Int.one_le_abs h
    · have h1 := Int.one_le_abs h
      have h2 := Int.one_le_abs hd
      rw [abs_mul]
      nlinarith [sq_abs c, sq_abs d, sq_nonneg (|c| - |d|)]
  · rcases eq_or_ne c 0 with hc | hc
    · subst hc; simp; exact Int.one_le_abs h
    · have h1 := Int.one_le_abs h
      have h2 := Int.one_le_abs hc
      rw [abs_mul]
      nlinarith [sq_abs c, sq_abs d, sq_nonneg (|c| - |d|)]


lemma ne_zero_or_ne_zero_of_isCoprime {c d : ℤ} (h : IsCoprime c d) : c ≠ 0 ∨ d ≠ 0 := by
  by_contra hcd
  push Not at hcd
  obtain ⟨rfl, rfl⟩ := hcd
  exact not_isCoprime_zero_zero h

lemma normSq_eq (c d : ℤ) (z : ℍ) :
    Complex.normSq ((c : ℂ) * z + d) = (c * z.re + d) ^ 2 + (c * z.im) ^ 2 := by
  rw [Complex.normSq_apply]
  simp
  ring

lemma one_le_normSq_of_mem_fd {z : ℍ} (hz : z ∈ ModularGroup.fd) (c d : ℤ) (h : c ≠ 0 ∨ d ≠ 0) :
    1 ≤ Complex.normSq ((c : ℂ) * z + d) := by
  have hint : (1 : ℝ) ≤ (c : ℝ) ^ 2 - |(c : ℝ) * d| + (d : ℝ) ^ 2 := by
    have := int_ineq c d h
    exact_mod_cast this
  obtain ⟨h1, h2⟩ := hz
  rw [Complex.normSq_apply] at h1
  rw [normSq_eq]
  have hx : 2 * |z.re| ≤ 1 := by linarith
  have h3 : |(c : ℝ) * d| * (2 * |z.re|) ≤ |(c : ℝ) * d| := by
    nlinarith [abs_nonneg ((c : ℝ) * d)]
  have h4 : -(2 * c * d * z.re) ≤ |(c : ℝ) * d| * (2 * |z.re|) := by
    have := neg_abs_le (2 * (c : ℝ) * d * z.re)
    have e : |2 * (c : ℝ) * d * z.re| = |(c : ℝ) * d| * (2 * |z.re|) := by
      rw [show 2 * (c : ℝ) * d * z.re = ((c : ℝ) * d) * (2 * z.re) by ring, abs_mul, abs_mul]
      simp
    linarith
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h1
  nlinarith [sq_nonneg (c : ℝ)]

lemma im_smul_le_of_mem_fd {z : ℍ} (hz : z ∈ ModularGroup.fd) (g : SL(2, ℤ)) :
    (g • z).im ≤ z.im := by
  rw [im_smul_eq]
  exact div_le_self z.im_pos.le (one_le_normSq_of_mem_fd hz _ _
    (ne_zero_or_ne_zero_of_isCoprime (ModularGroup.bottom_row_coprime g)))

lemma hgt_eq_im_of_mem_fd {z : ℍ} (hz : z ∈ ModularGroup.fd) : hgt z = z.im :=
  le_antisymm (ciSup_le fun g => im_smul_le_of_mem_fd hz g) (im_le_hgt z)

lemma continuous_phi (p : Fin 2 → ℤ) (hp : p 0 ≠ 0 ∨ p 1 ≠ 0) :
    Continuous fun z : ℍ => z.im / Complex.normSq ((p 0 : ℂ) * z + p 1) := by
  refine UpperHalfPlane.continuous_im.div ?_ ?_
  · exact Complex.continuous_normSq.comp
      ((continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const)
  · intro z hz
    rw [normSq_eq] at hz
    have hzi := z.im_pos
    have hs : ((p 0 : ℝ) * z.im) ^ 2 = 0 := by
      nlinarith [sq_nonneg ((p 0 : ℝ) * z.re + p 1), sq_nonneg ((p 0 : ℝ) * z.im)]
    have h0 : (p 0 : ℝ) = 0 := by
      rcases mul_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hs) with h | h
      · exact h
      · exact absurd h hzi.ne'
    have h0' : p 0 = 0 := by exact_mod_cast h0
    rw [h0] at hz
    have h1 : (p 1 : ℝ) = 0 := by nlinarith
    have h1' : p 1 = 0 := by exact_mod_cast h1
    rcases hp with hp | hp
    · exact hp h0'
    · exact hp h1'

lemma sumsq_le (c d x y a R : ℝ) (ha : 0 < a) (hy : a < y) (hx : |x| < R) :
    c ^ 2 + d ^ 2 ≤ (2 + (1 + 2 * R ^ 2) / a ^ 2) * ((c * x + d) ^ 2 + (c * y) ^ 2) := by
  have hx2 : x ^ 2 ≤ R ^ 2 := by
    have := sq_abs x
    nlinarith [abs_nonneg x]
  have h1 : d ^ 2 ≤ 2 * (c * x + d) ^ 2 + 2 * c ^ 2 * R ^ 2 := by
    nlinarith [sq_nonneg (c * x + d + c * x), sq_nonneg c, mul_le_mul_of_nonneg_left hx2 (sq_nonneg c)]
  have h2 : c ^ 2 * a ^ 2 ≤ c ^ 2 * y ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg c)
    nlinarith
  set A := (1 + 2 * R ^ 2) / a ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have hA1 : A * a ^ 2 = 1 + 2 * R ^ 2 := by
    rw [hA]; field_simp
  have h3 : (1 + 2 * R ^ 2) * c ^ 2 ≤ A * (c * y) ^ 2 := by
    rw [← hA1]
    nlinarith [mul_le_mul_of_nonneg_left h2 hA0]
  nlinarith [sq_nonneg (c * x + d), sq_nonneg (c * y), mul_nonneg hA0 (sq_nonneg (c * x + d))]

lemma continuous_hgt : Continuous hgt := by
  rw [continuous_iff_continuousAt]
  intro z0
  set a : ℝ := z0.im / 2 with ha_def
  have ha : 0 < a := by have := z0.im_pos; positivity
  set R : ℝ := |z0.re| + 1 with hR
  set K : ℝ := 2 + (1 + 2 * R ^ 2) / a ^ 2 with hK_def
  have hK : 2 ≤ K := by
    have : 0 ≤ (1 + 2 * R ^ 2) / a ^ 2 := by positivity
    linarith
  set N : ℕ := ⌈K⌉₊ with hN_def
  have hN : K ≤ N := Nat.le_ceil K
  set box : Finset (Fin 2 → ℤ) := Fintype.piFinset (fun _ => Finset.Icc (-(N : ℤ)) N) with hbox
  set P : Finset (Fin 2 → ℤ) := box.filter (fun p => IsCoprime (p 0) (p 1)) with hP_def
  have hN1 : (1 : ℤ) ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have h01 : (![0, 1] : Fin 2 → ℤ) ∈ P := by
    rw [hP_def, Finset.mem_filter, hbox, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> simp <;> omega
    · simpa using (isCoprime_one_right : IsCoprime (0 : ℤ) 1)
  have hP : P.Nonempty := ⟨_, h01⟩
  let φ : (Fin 2 → ℤ) → ℍ → ℝ := fun p z => z.im / Complex.normSq ((p 0 : ℂ) * z + p 1)
  have hφcont : ∀ p ∈ P, Continuous (φ p) := fun p hp =>
    continuous_phi p (ne_zero_or_ne_zero_of_isCoprime (Finset.mem_filter.mp hp).2)
  have hG : Continuous (fun z => P.sup' hP (fun p => φ p z)) :=
    Continuous.finset_sup'_apply hP hφcont
  have hU : ∀ᶠ z in 𝓝 z0, a < z.im ∧ |z.re| < R := by
    have h1 : ∀ᶠ z in 𝓝 z0, a < z.im :=
      UpperHalfPlane.continuous_im.continuousAt.eventually
        (lt_mem_nhds (by linarith [z0.im_pos] : a < z0.im))
    have h2 : ∀ᶠ z in 𝓝 z0, |z.re| < R :=
      (continuous_abs.comp UpperHalfPlane.continuous_re).continuousAt.eventually
        (gt_mem_nhds (by simp [hR] : |z0.re| < R))
    exact h1.and h2
  refine hG.continuousAt.congr ?_
  filter_upwards [hU] with z hz
  apply le_antisymm
  · refine Finset.sup'_le hP _ fun p hp => ?_
    obtain ⟨g, -, hg⟩ := ModularGroup.bottom_row_surj (R := ℤ) (Finset.mem_filter.mp hp).2
    have := le_hgt z g
    rw [im_smul_eq] at this
    have e0 : (↑g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = p 0 := by rw [← hg]
    have e1 : (↑g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = p 1 := by rw [← hg]
    rw [e0, e1] at this
    exact this
  · refine ciSup_le fun g => ?_
    rw [im_smul_eq]
    by_cases hb : (↑g : Matrix (Fin 2) (Fin 2) ℤ) 1 ∈ box
    · have hmem : (↑g : Matrix (Fin 2) (Fin 2) ℤ) 1 ∈ P :=
        Finset.mem_filter.mpr ⟨hb, ModularGroup.bottom_row_coprime g⟩
      exact Finset.le_sup' (fun p => φ p z) hmem
    · set c : ℤ := (↑g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc
      set d : ℤ := (↑g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd
      have hcd : (N : ℤ) < |c| ∨ (N : ℤ) < |d| := by
        rw [hbox, Fintype.mem_piFinset, Fin.forall_fin_two] at hb
        simp only [Finset.mem_Icc] at hb
        rw [← hc, ← hd] at hb
        by_contra hcon
        push Not at hcon
        exact hb ⟨abs_le.mp hcon.1, abs_le.mp hcon.2⟩
      have hsq : K ≤ (c : ℝ) ^ 2 + (d : ℝ) ^ 2 := by
        have hN' : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        rcases hcd with h | h
        · have h' : (N : ℝ) + 1 ≤ |(c : ℝ)| := by
            have : (N : ℤ) + 1 ≤ |c| := h
            exact_mod_cast this
          nlinarith [sq_abs (c : ℝ), sq_nonneg (d : ℝ)]
        · have h' : (N : ℝ) + 1 ≤ |(d : ℝ)| := by
            have : (N : ℤ) + 1 ≤ |d| := h
            exact_mod_cast this
          nlinarith [sq_abs (d : ℝ), sq_nonneg (c : ℝ)]
      have hQ : 1 ≤ Complex.normSq ((c : ℂ) * z + d) := by
        rw [normSq_eq]
        have := sumsq_le c d z.re z.im a R ha hz.1 hz.2
        rw [← hK_def] at this
        by_contra hlt
        push Not at hlt
        nlinarith [sq_nonneg ((c : ℝ) * z.re + d), sq_nonneg ((c : ℝ) * z.im)]
      calc z.im / Complex.normSq ((c : ℂ) * z + d) ≤ z.im := div_le_self z.im_pos.le hQ
        _ = φ ![0, 1] z := by simp [φ]
        _ ≤ P.sup' hP (fun p => φ p z) := Finset.le_sup' (fun p => φ p z) h01


/-- Invariant continuous cut-off: `1` where `hgt ≤ T`, `0` where `hgt ≥ T + 1`. -/
noncomputable def cut (T : ℝ) (z : ℍ) : ℝ := max 0 (min 1 (T + 1 - hgt z))

lemma cut_nonneg (T : ℝ) (z : ℍ) : 0 ≤ cut T z := le_max_left _ _

lemma cut_le_one (T : ℝ) (z : ℍ) : cut T z ≤ 1 := max_le zero_le_one (min_le_left _ _)

lemma continuous_cut (T : ℝ) : Continuous (cut T) :=
  continuous_const.max (continuous_const.min (continuous_const.sub continuous_hgt))

lemma cut_smul (T : ℝ) (g : SL(2, ℤ)) (z : ℍ) : cut T (g • z) = cut T z := by
  simp only [cut, hgt_smul]

lemma cut_eq_one {T : ℝ} {z : ℍ} (h : hgt z ≤ T) : cut T z = 1 := by
  unfold cut
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

lemma cut_eq_zero {T : ℝ} {z : ℍ} (h : T + 1 ≤ z.im) : cut T z = 0 := by
  have := im_le_hgt z
  unfold cut
  exact max_eq_left (le_trans (min_le_right _ _) (by linarith))

lemma measurableSet_fd : MeasurableSet ModularGroup.fd := by
  show MeasurableSet ({z : ℍ | 1 ≤ Complex.normSq (z : ℂ)} ∩ {z : ℍ | |z.re| ≤ 1 / 2})
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_le measurable_const
      (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe).measurable
  · exact measurableSet_le (continuous_abs.comp UpperHalfPlane.continuous_re).measurable
      measurable_const

lemma volume_fd_lt_top : volume ModularGroup.fd < ⊤ :=
  FLT.FundamentalDomainExactVolume.gate_volume_lt_top

lemma tail_small {η : ℝ} (hη : 0 < η) :
    ∃ T : ℝ, (volume ({z : ℍ | T < z.im} ∩ ModularGroup.fd)).toReal < η := by
  let s : ℕ → Set ℍ := fun n => {z : ℍ | (n : ℝ) < z.im} ∩ ModularGroup.fd
  have hanti : Antitone s := fun m n hmn z hz =>
    ⟨show (m : ℝ) < z.im from lt_of_le_of_lt (Nat.cast_le.mpr hmn) hz.1, hz.2⟩
  have hmeas : ∀ n, NullMeasurableSet (s n) volume := fun n =>
    ((measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable).inter
      measurableSet_fd).nullMeasurableSet
  have hfin : ∃ n, volume (s n) ≠ ⊤ :=
    ⟨0, ne_top_of_le_ne_top volume_fd_lt_top.ne (measure_mono Set.inter_subset_right)⟩
  have hinter : (⋂ n, s n) = ∅ := by
    ext z
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
    intro h
    obtain ⟨n, hn⟩ := exists_nat_gt z.im
    exact absurd (h n).1 (not_lt.mpr hn.le)
  have hlim := tendsto_measure_iInter_atTop hmeas hanti hfin
  rw [hinter, measure_empty] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hη))).exists
  exact ⟨n, ENNReal.toReal_lt_of_lt_ofReal hn⟩

lemma integrableOn_fd {E : Type*} [NormedAddCommGroup E] {g : ℍ → E} (hg : Continuous g)
    {B : ℝ} (hB : ∀ z, ‖g z‖ ≤ B) : IntegrableOn g ModularGroup.fd :=
  IntegrableOn.of_bound volume_fd_lt_top hg.aestronglyMeasurable B (Eventually.of_forall hB)

lemma continuous_horo {E : Type*} [TopologicalSpace E] (g : ℍ → E) (hg : Continuous g) {y : ℝ}
    (hy : 0 < y) :
    Continuous fun x : ℝ => g (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) := by
  have hsrc : ∀ x : ℝ, (x : ℂ) + (y : ℂ) * Complex.I ∈ UpperHalfPlane.ofComplex.source := by
    intro x
    simpa [UpperHalfPlane.ofComplex] using hy
  refine hg.comp ?_
  exact UpperHalfPlane.ofComplex.continuousOn.comp_continuous (by fun_prop) hsrc

end Sol_Horocycle_tendsto_closedHorocycle_average_modularGroup

open Sol_Horocycle_tendsto_closedHorocycle_average_modularGroup in
theorem solution (f : ℍ → ℂ) (hf : Continuous f)
    (hfb : ∃ C : ℝ, ∀ z : ℍ, ‖f z‖ ≤ C)
    (hΓ : ∀ (γ : SL(2, ℤ)) (z : ℍ), f (γ • z) = f z) :
    Tendsto
      (fun y : ℝ => ∫ x in (0 : ℝ)..1,
        f (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)))
      (𝓝[>] 0) (𝓝 ((3 / Real.pi : ℂ) * ∫ z in ModularGroup.fd, f z)) := by
  obtain ⟨C, hC⟩ := hfb
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC UpperHalfPlane.I)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hvol : (volume ModularGroup.fd).toReal = Real.pi / 3 :=
    FLT.FundamentalDomainExactVolume.volume_fd_toReal
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η : ℝ := ε * Real.pi / (12 * (C + 1)) with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨T, hT⟩ := tail_small hη
  set S : Set ℍ := {z : ℍ | T < z.im} with hS_def
  have hSmeas : MeasurableSet S :=
    measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable
  set m : ℝ := (volume (S ∩ ModularGroup.fd)).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  set χ : ℍ → ℝ := cut T with hχ
  have hχcont : Continuous χ := continuous_cut T
  have hχ0 : ∀ z, 0 ≤ χ z := cut_nonneg T
  have hχ1 : ∀ z, χ z ≤ 1 := cut_le_one T
  -- the child, applied to `f χ` and to `χ`
  have hfχ := Horocycle.tendsto_closedHorocycle_average_of_vanishing_near_cusp
    (fun z => f z * (χ z : ℂ)) (hf.mul (Complex.continuous_ofReal.comp hχcont))
    (fun γ z => by simp only [χ, cut_smul, hΓ])
    ⟨T + 1, fun z hz => by simp [χ, cut_eq_zero hz]⟩
  have hχc := Horocycle.tendsto_closedHorocycle_average_of_vanishing_near_cusp
    (fun z => (χ z : ℂ)) (Complex.continuous_ofReal.comp hχcont)
    (fun γ z => by simp only [χ, cut_smul])
    ⟨T + 1, fun z hz => by simp [χ, cut_eq_zero hz]⟩
  set j : ℝ := 3 / Real.pi * ∫ z in ModularGroup.fd, χ z with hj
  have hχr : Tendsto (fun y : ℝ => ∫ x in (0 : ℝ)..1, χ (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) (𝓝[>] 0) (𝓝 j) := by
    have e1 : ∀ y : ℝ, (∫ x in (0 : ℝ)..1, ((χ (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) : ℝ) : ℂ)) =
        ((∫ x in (0 : ℝ)..1, χ (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) : ℝ) : ℂ) := fun y => intervalIntegral.integral_ofReal
    have e2 : (3 / Real.pi : ℂ) * ∫ z in ModularGroup.fd, (χ z : ℂ) = ((j : ℝ) : ℂ) := by
      rw [integral_complex_ofReal, hj]
      push_cast
      ring
    have h' : Tendsto (fun y : ℝ => ((∫ x in (0 : ℝ)..1, χ (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) : ℝ) : ℂ)) (𝓝[>] 0)
        (𝓝 ((j : ℝ) : ℂ)) := by
      rw [← e2]
      refine hχc.congr fun y => ?_
      rw [← e1]
    have := (Complex.continuous_re.tendsto _).comp h'
    simpa [Function.comp_def] using this
  -- integrals over the fundamental domain
  have hint1 : IntegrableOn (fun _ : ℍ => (1 : ℝ)) ModularGroup.fd :=
    integrableOn_fd continuous_const (B := 1) (fun _ => by simp)
  have hintχ : IntegrableOn χ ModularGroup.fd :=
    integrableOn_fd hχcont (B := 1) (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hχ0 z)]; exact hχ1 z)
  have hint1χ : IntegrableOn (fun z => 1 - χ z) ModularGroup.fd := hint1.sub hintχ
  have hintS : IntegrableOn (S.indicator (1 : ℍ → ℝ)) ModularGroup.fd :=
    IntegrableOn.indicator (f := (1 : ℍ → ℝ)) hint1 hSmeas
  set D : ℝ := ∫ z in ModularGroup.fd, (1 - χ z) with hD_def
  have hD_eq : D = Real.pi / 3 - ∫ z in ModularGroup.fd, χ z := by
    rw [hD_def, integral_sub hint1 hintχ, setIntegral_const, smul_eq_mul, mul_one,
      Measure.real, hvol]
  have hD_le : D ≤ m := by
    have h1 : D ≤ ∫ z in ModularGroup.fd, S.indicator (1 : ℍ → ℝ) z := by
      refine setIntegral_mono_on hint1χ hintS measurableSet_fd fun z hz => ?_
      by_cases hzS : z ∈ S
      · rw [Set.indicator_of_mem hzS, Pi.one_apply]
        linarith [hχ0 z]
      · rw [Set.indicator_of_notMem hzS]
        have hle : hgt z ≤ T := by
          rw [hgt_eq_im_of_mem_fd hz]
          simpa [hS_def] using hzS
        simp [χ, cut_eq_one hle]
    have h2 : ∫ z in ModularGroup.fd, S.indicator (1 : ℍ → ℝ) z = m := by
      rw [integral_indicator_one hSmeas, Measure.real, Measure.restrict_apply hSmeas]
    linarith
  have hD0 : 0 ≤ D := setIntegral_nonneg measurableSet_fd fun z _ => by linarith [hχ1 z]
  have hj1 : 1 - j ≤ 3 / Real.pi * m := by
    have : 1 - j = 3 / Real.pi * D := by
      rw [hD_eq, hj]
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hD_le (by positivity)
  have hL : ‖(3 / Real.pi : ℂ) * (∫ z in ModularGroup.fd, f z * (χ z : ℂ)) -
      (3 / Real.pi : ℂ) * ∫ z in ModularGroup.fd, f z‖ ≤ 3 / Real.pi * (C * m) := by
    have hintf : IntegrableOn f ModularGroup.fd := integrableOn_fd hf hC
    have hintfχ : IntegrableOn (fun z => f z * (χ z : ℂ)) ModularGroup.fd :=
      integrableOn_fd (hf.mul (Complex.continuous_ofReal.comp hχcont)) (B := C) (fun z => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ0 z)]
        nlinarith [hC z, hχ0 z, hχ1 z, norm_nonneg (f z)])
    rw [← mul_sub, norm_mul, ← integral_sub hintfχ hintf]
    have hn : ‖(3 / Real.pi : ℂ)‖ = 3 / Real.pi := by
      rw [show (3 / Real.pi : ℂ) = ((3 / Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hn]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hb : ‖∫ z in ModularGroup.fd, (f z * (χ z : ℂ) - f z)‖ ≤
        ∫ z in ModularGroup.fd, C * (1 - χ z) := by
      refine norm_integral_le_of_norm_le (hint1χ.const_mul C) (Eventually.of_forall fun z => ?_)
      rw [show f z * (χ z : ℂ) - f z = -(f z * ((1 - χ z : ℝ) : ℂ)) by push_cast; ring, norm_neg,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hχ1 z])]
      exact mul_le_mul_of_nonneg_right (hC z) (by linarith [hχ1 z])
    calc _ ≤ ∫ z in ModularGroup.fd, C * (1 - χ z) := hb
      _ = C * D := by rw [integral_const_mul]
      _ ≤ C * m := mul_le_mul_of_nonneg_left hD_le hC0
  -- choice of constants
  have hkey : 3 / Real.pi * (C * m) ≤ ε / 4 := by
    have h1 : 3 / Real.pi * (C * m) ≤ 3 / Real.pi * ((C + 1) * η) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul (by linarith) hT.le hm0 (by linarith)
    have h2 : 3 / Real.pi * ((C + 1) * η) = ε / 4 := by
      rw [hη_def]
      field_simp
      ring
    linarith
  have hev1 := Metric.tendsto_nhds.mp hfχ (ε / 4) (by positivity)
  have hev2 := Metric.tendsto_nhds.mp hχr (ε / (4 * (C + 1))) (by positivity)
  have hev3 : ∀ᶠ y in 𝓝[>] (0 : ℝ), 0 < y := self_mem_nhdsWithin
  filter_upwards [hev1, hev2, hev3] with y h1 h2 hy
  have hcf : Continuous fun x : ℝ => f (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) :=
    continuous_horo f hf hy
  have hcχ : Continuous fun x : ℝ => χ (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) :=
    continuous_horo χ hχcont hy
  have hcfχ : Continuous fun x : ℝ => f (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) *
      ((χ (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) : ℝ) : ℂ) :=
    hcf.mul (Complex.continuous_ofReal.comp hcχ)
  have hH : ‖(∫ x in (0 : ℝ)..1, f (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) -
      ∫ x in (0 : ℝ)..1, f (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) *
        ((χ (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) : ℝ) : ℂ)‖ ≤
      C * (1 - ∫ x in (0 : ℝ)..1, χ (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) := by
    rw [← intervalIntegral.integral_sub (hcf.intervalIntegrable _ _) (hcfχ.intervalIntegrable _ _)]
    have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) zero_le_one
      (f := fun x : ℝ => f (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) -
        f (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) *
          ((χ (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) : ℝ) : ℂ))
      (g := fun x : ℝ => C * (1 - χ (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))))
      (Eventually.of_forall fun x _ => by
        set w := UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)
        rw [show f w - f w * ((χ w : ℝ) : ℂ) = f w * ((1 - χ w : ℝ) : ℂ) by push_cast; ring,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hχ1 w])]
        exact mul_le_mul_of_nonneg_right (hC w) (by linarith [hχ1 w]))
      ((continuous_const.mul (continuous_const.sub hcχ)).intervalIntegrable _ _)
    refine hb.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub intervalIntegrable_const (hcχ.intervalIntegrable _ _),
      intervalIntegral.integral_const]
    simp
  have hJ : 1 - (∫ x in (0 : ℝ)..1, χ (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) ≤
      3 / Real.pi * m + ε / (4 * (C + 1)) := by
    rw [Real.dist_eq] at h2
    have := abs_lt.mp h2
    linarith [hj1]
  have h3 : C * (ε / (4 * (C + 1))) ≤ ε / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hCJ : C * (1 - ∫ x in (0 : ℝ)..1,
      χ (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) ≤
      3 / Real.pi * (C * m) + ε / 4 := by
    calc _ ≤ C * (3 / Real.pi * m + ε / (4 * (C + 1))) := mul_le_mul_of_nonneg_left hJ hC0
      _ = 3 / Real.pi * (C * m) + C * (ε / (4 * (C + 1))) := by ring
      _ ≤ _ := by linarith
  calc _ ≤ _ := dist_triangle4 _
        (∫ x in (0 : ℝ)..1, f (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) *
          ((χ (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) : ℝ) : ℂ))
        ((3 / Real.pi : ℂ) * ∫ z in ModularGroup.fd, f z * (χ z : ℂ)) _
    _ < ε := by
      rw [dist_eq_norm, dist_eq_norm ((3 / Real.pi : ℂ) * ∫ z in ModularGroup.fd, f z * (χ z : ℂ))]
      linarith [hH, hCJ, hkey, h1, hL]
