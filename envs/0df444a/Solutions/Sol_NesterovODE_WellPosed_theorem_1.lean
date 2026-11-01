-- Prove2me | solution 1 for NesterovODE.WellPosed.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T13:45:17.871837+00:00
-- url     : https://prove2.me/submissions/b1970098-99a9-45f8-ac62-738598324e96

import Mathlib
import Definitions.Def_NesterovODE_WellPosed_Setting

set_option autoImplicit false

namespace NesterovODE.WellPosed.NAux

open MeasureTheory intervalIntegral Set Filter Topology BoundedContinuousFunction

variable {n : ℕ}

/-- The velocity operator `Q F u = -(u³)⁻¹ ∫₀ᵘ s³ F(s) ds`. -/
noncomputable def Q (F : ℝ → E n) (u : ℝ) : E n :=
  -(u ^ 3)⁻¹ • ∫ s in (0:ℝ)..u, s ^ 3 • F s

/-- The weight `exp (L t²)`. -/
noncomputable def wt (L : ℝ) (t : ℝ) : ℝ := Real.exp (L * t ^ 2)

lemma wt_pos (L t : ℝ) : 0 < wt L t := Real.exp_pos _

lemma one_le_wt {L : ℝ} (hL : 0 ≤ L) (t : ℝ) : 1 ≤ wt L t :=
  Real.one_le_exp (by positivity)

lemma wt_zero (L : ℝ) : wt L 0 = 1 := by simp [wt]

lemma wt_mono {L : ℝ} (hL : 0 ≤ L) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    wt L s ≤ wt L t := by
  unfold wt
  apply Real.exp_le_exp.2
  have : s ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hs hst 2
  exact mul_le_mul_of_nonneg_left this hL

lemma continuous_wt (L : ℝ) : Continuous (wt L) := by
  unfold wt; fun_prop

lemma hasDerivAt_wt (L t : ℝ) : HasDerivAt (wt L) (2 * L * t * wt L t) t := by
  unfold wt
  have h := ((hasDerivAt_pow 2 t).const_mul L).exp
  refine h.congr_deriv ?_
  simp only [Nat.cast_ofNat]
  ring_nf

lemma Q_zero (F : ℝ → E n) : Q F 0 = 0 := by simp [Q]

lemma continuous_I {F : ℝ → E n} (hF : Continuous F) :
    Continuous (fun u => ∫ s in (0:ℝ)..u, s ^ 3 • F s) := by
  have : Continuous (fun s : ℝ => s ^ 3 • F s) := (continuous_pow 3).smul hF
  exact continuous_primitive (fun a b => this.intervalIntegrable a b) 0

lemma continuous_Q {F : ℝ → E n} (hF : Continuous F) : Continuous (Q F) := by
  rw [continuous_iff_continuousAt]
  intro u
  rcases eq_or_ne u 0 with rfl | hu
  · obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (-1:ℝ) 1)).exists_bound_of_continuousOn
      hF.continuousOn
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by norm_num))
    have hbd : ∀ u : ℝ, |u| ≤ 1 → ‖Q F u‖ ≤ M * |u| := by
      intro u hu1
      rcases eq_or_ne u 0 with rfl | hu0
      · simp [Q_zero]
      have hI : ‖∫ s in (0:ℝ)..u, s ^ 3 • F s‖ ≤ (|u| ^ 3 * M) * |u - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro x hx
        have hx' : |x| ≤ |u| := by
          have := Set.uIoc_subset_uIcc hx
          rw [Set.mem_uIcc] at this
          rcases this with h | h
          · rw [abs_le]; constructor <;> [skip; skip] <;>
              cases abs_cases u <;> cases abs_cases x <;> linarith [h.1, h.2]
          · rw [abs_le]; constructor <;> [skip; skip] <;>
              cases abs_cases u <;> cases abs_cases x <;> linarith [h.1, h.2]
        have hxm : x ∈ Icc (-1:ℝ) 1 := by
          rw [Set.mem_Icc, ← abs_le]; exact hx'.trans hu1
        rw [norm_smul, Real.norm_eq_abs, abs_pow]
        exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hx' 3) (hM x hxm)
          (norm_nonneg _) (by positivity)
      rw [sub_zero] at hI
      rw [Q, norm_smul, norm_neg, norm_inv, Real.norm_eq_abs, abs_pow]
      have hpos : 0 < |u| := abs_pos.2 hu0
      calc (|u| ^ 3)⁻¹ * ‖∫ s in (0:ℝ)..u, s ^ 3 • F s‖
          ≤ (|u| ^ 3)⁻¹ * (|u| ^ 3 * M * |u|) := mul_le_mul_of_nonneg_left hI (by positivity)
        _ = M * |u| := by field_simp
    show Tendsto (Q F) (𝓝 0) (𝓝 (Q F 0))
    rw [Q_zero]
    apply squeeze_zero_norm' (a := fun u => M * |u|)
    · have : Ioo (-1:ℝ) 1 ∈ 𝓝 (0:ℝ) := isOpen_Ioo.mem_nhds (by norm_num)
      filter_upwards [this] with u hu
      exact hbd u (by rw [abs_le]; exact ⟨hu.1.le, hu.2.le⟩)
    · have : Continuous (fun u : ℝ => M * |u|) := by fun_prop
      simpa using this.tendsto 0
  · have h1 : ContinuousAt (fun u : ℝ => -(u ^ 3)⁻¹) u :=
      ((continuous_pow 3).continuousAt.inv₀ (pow_ne_zero 3 hu)).neg
    exact h1.smul (continuous_I hF).continuousAt

lemma norm_Q_le {F : ℝ → E n} {L C u : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C) (hu : 0 ≤ u)
    (hF : ∀ s ∈ Icc 0 u, ‖F s‖ ≤ C * wt L s) : ‖Q F u‖ ≤ C * u * wt L u := by
  rcases hu.eq_or_lt with rfl | hu
  · simp [Q_zero]
  have hI : ‖∫ s in (0:ℝ)..u, s ^ 3 • F s‖ ≤ (u ^ 3 * (C * wt L u)) * |u - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le hu.le] at hx
    rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos hx.1]
    have h1 := hF x ⟨hx.1.le, hx.2⟩
    have h2 := wt_mono hL hx.1.le hx.2
    have h3 : x ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ hx.1.le hx.2 3
    calc x ^ 3 * ‖F x‖ ≤ x ^ 3 * (C * wt L x) :=
          mul_le_mul_of_nonneg_left h1 (pow_pos hx.1 3).le
      _ ≤ u ^ 3 * (C * wt L u) :=
          mul_le_mul h3 (mul_le_mul_of_nonneg_left h2 hC)
            (mul_nonneg hC (wt_pos L x).le) (pow_pos hu 3).le
  rw [sub_zero, abs_of_pos hu] at hI
  rw [Q, norm_smul, norm_neg, norm_inv, Real.norm_eq_abs, abs_pow, abs_of_pos hu]
  calc (u ^ 3)⁻¹ * ‖∫ s in (0:ℝ)..u, s ^ 3 • F s‖
      ≤ (u ^ 3)⁻¹ * (u ^ 3 * (C * wt L u) * u) :=
        mul_le_mul_of_nonneg_left hI (inv_nonneg.2 (pow_pos hu 3).le)
    _ = C * u * wt L u := by field_simp

lemma Q_sub {F₁ F₂ : ℝ → E n} {u : ℝ}
    (h₁ : IntervalIntegrable (fun s : ℝ => s ^ 3 • F₁ s) volume 0 u)
    (h₂ : IntervalIntegrable (fun s : ℝ => s ^ 3 • F₂ s) volume 0 u) :
    Q F₁ u - Q F₂ u = Q (fun s => F₁ s - F₂ s) u := by
  unfold Q
  rw [← smul_sub, ← intervalIntegral.integral_sub h₁ h₂]
  simp_rw [smul_sub]

lemma cmp {L : ℝ} (hL : 0 < L) {D U : ℝ → E n} {c T : ℝ} (hc : 0 ≤ c)
    (hD : ContinuousOn D (Icc 0 T)) (hD0 : D 0 = 0)
    (hDd : ∀ x ∈ Ico 0 T, HasDerivWithinAt D (U x) (Ici x) x)
    (hU : ∀ x ∈ Ico 0 T, ‖U x‖ ≤ c * x * wt L x) :
    ∀ t ∈ Icc 0 T, ‖D t‖ ≤ c / (2 * L) * wt L t := by
  have hB : ∀ x, HasDerivAt (fun t => c / (2 * L) * wt L t) (c * x * wt L x) x := by
    intro x
    have := (hasDerivAt_wt L x).const_mul (c / (2 * L))
    refine this.congr_deriv ?_
    field_simp
  intro t ht
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary hD hDd ?_ hB hU ht
  rw [hD0, norm_zero]
  exact mul_nonneg (div_nonneg hc (by positivity)) (wt_pos L 0).le

section Exist

/-- the trajectory attached to a weighted profile `Z`. -/
noncomputable def Xof (L : ℝ) (Z : ℝ →ᵇ E n) : ℝ → E n := fun t => wt L t • Z t

/-- primitive of the velocity. -/
noncomputable def Prim (G : E n → E n) (L : ℝ) (Z : ℝ →ᵇ E n) (t : ℝ) : E n :=
  ∫ u in (0:ℝ)..t, Q (fun s => G (Xof L Z s)) u

/-- the weighted Picard map, pointwise. -/
noncomputable def psiF (G : E n → E n) (L : ℝ) (x₀ : E n) (Z : ℝ →ᵇ E n) (t : ℝ) : E n :=
  (wt L t)⁻¹ • (x₀ + Prim G L Z (max t 0))

variable {G : E n → E n} {K : NNReal} {L : ℝ} {x₀ : E n}

lemma continuous_Xof (L : ℝ) (Z : ℝ →ᵇ E n) : Continuous (Xof L Z) :=
  (continuous_wt L).smul Z.continuous

lemma continuous_QF (hG : Continuous G) (Z : ℝ →ᵇ E n) :
    Continuous (Q (fun s => G (Xof L Z s))) :=
  continuous_Q (hG.comp (continuous_Xof L Z))

lemma hasDerivAt_Prim (hG : Continuous G) (Z : ℝ →ᵇ E n) (x : ℝ) :
    HasDerivAt (Prim G L Z) (Q (fun s => G (Xof L Z s)) x) x :=
  ((continuous_QF hG Z).integral_hasStrictDerivAt 0 x).hasDerivAt

lemma continuous_Prim (hG : Continuous G) (Z : ℝ →ᵇ E n) : Continuous (Prim G L Z) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_Prim hG Z x).continuousAt

lemma continuous_psiF (hG : Continuous G) (Z : ℝ →ᵇ E n) : Continuous (psiF G L x₀ Z) := by
  unfold psiF
  have h1 : Continuous (fun t => (wt L t)⁻¹) :=
    (continuous_wt L).inv₀ (fun t => (wt_pos L t).ne')
  exact h1.smul (continuous_const.add
    ((continuous_Prim hG Z).comp (continuous_id.max continuous_const)))

lemma norm_G_le (hG : LipschitzWith K G) (x : E n) : ‖G x‖ ≤ ‖G 0‖ + K * ‖x‖ := by
  have h := hG.dist_le_mul x 0
  rw [dist_eq_norm, dist_eq_norm, sub_zero] at h
  have h2 := norm_sub_norm_le (G x) (G 0)
  linarith

lemma wt_max_le (hL : 0 ≤ L) (t : ℝ) : wt L (max t 0) ≤ wt L t := by
  rcases le_total 0 t with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, wt_zero]; exact one_le_wt hL t

lemma norm_Prim_le (hL : 0 < L) (hG : Continuous G) (Z : ℝ →ᵇ E n) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s, 0 ≤ s → ‖G (Xof L Z s)‖ ≤ C * wt L s) {t : ℝ} (ht : 0 ≤ t) :
    ‖Prim G L Z t‖ ≤ C / (2 * L) * wt L t :=
  cmp hL hC (continuous_Prim hG Z).continuousOn (by simp [Prim])
    (fun x _ => (hasDerivAt_Prim hG Z x).hasDerivWithinAt)
    (fun x hx => norm_Q_le hL.le hC hx.1 (fun s hs => hF s hs.1)) t ⟨ht, le_rfl⟩

lemma norm_psiF_le (hL : 0 < L) (hK : (K : ℝ) = L) (hG : LipschitzWith K G)
    (Z : ℝ →ᵇ E n) (t : ℝ) :
    ‖psiF G L x₀ Z t‖ ≤ ‖x₀‖ + (‖G 0‖ + L * ‖Z‖) / (2 * L) := by
  have hC : 0 ≤ ‖G 0‖ + L * ‖Z‖ := by positivity
  have hF : ∀ s, 0 ≤ s → ‖G (Xof L Z s)‖ ≤ (‖G 0‖ + L * ‖Z‖) * wt L s := by
    intro s _
    have h1 := norm_G_le hG (Xof L Z s)
    have h2 : ‖Xof L Z s‖ ≤ wt L s * ‖Z‖ := by
      rw [Xof, norm_smul, Real.norm_eq_abs, abs_of_pos (wt_pos L s)]
      exact mul_le_mul_of_nonneg_left (Z.norm_coe_le_norm s) (wt_pos L s).le
    have h3 := one_le_wt hL.le s
    rw [hK] at h1
    have h4 := mul_le_mul_of_nonneg_left h2 hL.le
    have h5 := mul_le_mul_of_nonneg_left h3 (norm_nonneg (G 0))
    nlinarith
  have hP := norm_Prim_le hL hG.continuous Z hC hF (le_max_right t 0)
  have hw := wt_max_le hL.le t
  have hwpos := wt_pos L t
  have hwne := hwpos.ne'
  rw [psiF, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hwpos]
  have hc2 : 0 ≤ (‖G 0‖ + L * ‖Z‖) / (2 * L) := div_nonneg hC (by positivity)
  have hn : ‖x₀ + Prim G L Z (max t 0)‖ ≤ ‖x₀‖ + (‖G 0‖ + L * ‖Z‖) / (2 * L) * wt L t :=
    (norm_add_le _ _).trans (add_le_add le_rfl (hP.trans (mul_le_mul_of_nonneg_left hw hc2)))
  have hinv : (wt L t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_wt hL.le t)
  calc (wt L t)⁻¹ * ‖x₀ + Prim G L Z (max t 0)‖
      ≤ (wt L t)⁻¹ * (‖x₀‖ + (‖G 0‖ + L * ‖Z‖) / (2 * L) * wt L t) :=
        mul_le_mul_of_nonneg_left hn (inv_nonneg.2 hwpos.le)
    _ = (wt L t)⁻¹ * ‖x₀‖ + (‖G 0‖ + L * ‖Z‖) / (2 * L) := by
        rw [mul_add]; congr 1; field_simp
    _ ≤ ‖x₀‖ + (‖G 0‖ + L * ‖Z‖) / (2 * L) := by
        have := mul_le_mul_of_nonneg_right hinv (norm_nonneg x₀)
        linarith

/-- the weighted Picard map. -/
noncomputable def psi (hL : 0 < L) (hK : (K : ℝ) = L) (hG : LipschitzWith K G) (x₀ : E n)
    (Z : ℝ →ᵇ E n) : ℝ →ᵇ E n :=
  BoundedContinuousFunction.ofNormedAddCommGroup (psiF G L x₀ Z) (continuous_psiF hG.continuous Z)
    _ (norm_psiF_le hL hK hG Z)

lemma psi_contracting (hL : 0 < L) (hK : (K : ℝ) = L) (hG : LipschitzWith K G) (x₀ : E n) :
    ContractingWith (1 / 2) (psi hL hK hG x₀) := by
  refine ⟨by rw [← NNReal.coe_lt_coe]; norm_num, LipschitzWith.of_dist_le_mul fun Z₁ Z₂ => ?_⟩
  have hhalf : (((1 / 2 : NNReal)) : ℝ) = 1 / 2 := by norm_num
  rw [hhalf]
  set d := dist Z₁ Z₂
  have hd : 0 ≤ d := dist_nonneg
  rw [BoundedContinuousFunction.dist_le (by positivity)]
  intro t
  show dist (psiF G L x₀ Z₁ t) (psiF G L x₀ Z₂ t) ≤ 1 / 2 * d
  have hGc := hG.continuous
  have key := cmp hL (D := fun t => Prim G L Z₁ t - Prim G L Z₂ t)
    (U := fun x => Q (fun s => G (Xof L Z₁ s)) x - Q (fun s => G (Xof L Z₂ s)) x)
    (c := L * d) (T := max t 0) (by positivity)
    ((continuous_Prim hGc Z₁).sub (continuous_Prim hGc Z₂)).continuousOn (by simp [Prim])
    (fun x _ => ((hasDerivAt_Prim hGc Z₁ x).sub (hasDerivAt_Prim hGc Z₂ x)).hasDerivWithinAt)
    ?_ (max t 0) ⟨le_max_right t 0, le_rfl⟩
  · have hwpos := wt_pos L t
    have hw := wt_max_le hL.le t
    rw [dist_eq_norm, psiF, psiF, ← smul_sub, add_sub_add_left_eq_sub, norm_smul,
      Real.norm_eq_abs, abs_inv, abs_of_pos hwpos]
    have e : L * d / (2 * L) = 1 / 2 * d := by field_simp
    rw [e] at key
    calc (wt L t)⁻¹ * ‖Prim G L Z₁ (max t 0) - Prim G L Z₂ (max t 0)‖
        ≤ (wt L t)⁻¹ * (1 / 2 * d * wt L t) :=
          mul_le_mul_of_nonneg_left (key.trans (mul_le_mul_of_nonneg_left hw (by positivity)))
            (inv_nonneg.2 hwpos.le)
      _ = 1 / 2 * d := by field_simp
  · intro x hx
    have h1 : IntervalIntegrable (fun s : ℝ => s ^ 3 • G (Xof L Z₁ s)) volume 0 x :=
      ((continuous_pow 3).smul (hGc.comp (continuous_Xof L Z₁))).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun s : ℝ => s ^ 3 • G (Xof L Z₂ s)) volume 0 x :=
      ((continuous_pow 3).smul (hGc.comp (continuous_Xof L Z₂))).intervalIntegrable _ _
    rw [Q_sub (F₁ := fun s => G (Xof L Z₁ s)) (F₂ := fun s => G (Xof L Z₂ s)) h1 h2]
    refine norm_Q_le hL.le (by positivity) hx.1 (fun s _ => ?_)
    have h3 := hG.dist_le_mul (Xof L Z₁ s) (Xof L Z₂ s)
    rw [dist_eq_norm, dist_eq_norm, hK] at h3
    have h4 : ‖Xof L Z₁ s - Xof L Z₂ s‖ ≤ wt L s * d := by
      rw [Xof, Xof, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (wt_pos L s),
        ← dist_eq_norm]
      exact mul_le_mul_of_nonneg_left (BoundedContinuousFunction.dist_coe_le_dist s)
        (wt_pos L s).le
    calc ‖G (Xof L Z₁ s) - G (Xof L Z₂ s)‖ ≤ L * ‖Xof L Z₁ s - Xof L Z₂ s‖ := h3
      _ ≤ L * (wt L s * d) := mul_le_mul_of_nonneg_left h4 hL.le
      _ = L * d * wt L s := by ring

theorem exists_sol (f : E n → ℝ) (x₀ : E n) (K : NNReal) (hK0 : 0 < K)
    (hG : LipschitzWith K (gradient f)) : ∃ X V : ℝ → E n, IsSolution f 3 x₀ X V := by
  have hL : (0 : ℝ) < K := NNReal.coe_pos.2 hK0
  have hc := psi_contracting (G := gradient f) hL rfl hG x₀
  have hZ : psi hL rfl hG x₀ (ContractingWith.fixedPoint _ hc) = ContractingWith.fixedPoint _ hc :=
    ContractingWith.fixedPoint_isFixedPt hc
  set Z := ContractingWith.fixedPoint _ hc
  have hGc := hG.continuous
  have hX : ∀ t, Xof K Z t = x₀ + Prim (gradient f) K Z (max t 0) := by
    intro t
    have h := congrArg (fun φ : ℝ →ᵇ E n => φ t) hZ
    change psiF (gradient f) K x₀ Z t = Z t at h
    rw [Xof, ← h, psiF, smul_inv_smul₀ (wt_pos _ t).ne']
  have hPrim := hasDerivAt_Prim (L := (K : ℝ)) hGc Z
  refine ⟨Xof K Z, Q (fun s => gradient f (Xof K Z s)), ?_, Q_zero _, ?_,
    (continuous_QF hGc Z).continuousWithinAt, fun t ht => ⟨?_, ?_⟩⟩
  · rw [hX]; simp [Prim]
  · have h0 := ((hPrim 0).const_add x₀).hasDerivWithinAt (s := Ici 0)
    refine h0.congr (fun t ht => ?_) ?_
    · rw [hX, max_eq_left (show (0:ℝ) ≤ t from ht)]
    · rw [hX, max_eq_left le_rfl]
  · refine ((hPrim t).const_add x₀).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds ht] with s hs
    rw [hX, max_eq_left hs.le]
  · have hFc : Continuous (fun s => gradient f (Xof K Z s)) := hGc.comp (continuous_Xof _ Z)
    have hI : HasDerivAt (fun u => ∫ s in (0:ℝ)..u, s ^ 3 • gradient f (Xof K Z s))
        (t ^ 3 • gradient f (Xof K Z t)) t :=
      (((continuous_pow 3).smul hFc).integral_hasStrictDerivAt 0 t).hasDerivAt
    have ht3 : t ^ 3 ≠ 0 := pow_ne_zero 3 ht.ne'
    have hinv : HasDerivAt (fun u : ℝ => -(u ^ 3)⁻¹)
        (-(-((((3 : ℕ) : ℝ)) * t ^ (3 - 1)) / (t ^ 3) ^ 2)) t :=
      ((hasDerivAt_pow 3 t).inv ht3).neg
    have h := hinv.smul hI
    refine h.congr_deriv ?_
    have hb : -(t ^ 3)⁻¹ * t ^ 3 = -1 := by field_simp
    have hc' : -(-((((3 : ℕ) : ℝ)) * t ^ (3 - 1)) / (t ^ 3) ^ 2) = -(3 / t) * -(t ^ 3)⁻¹ := by
      norm_num; field_simp
    simp only [Q, smul_smul]
    rw [hb, hc', neg_one_smul]
    abel

end Exist

section Uniq

variable {f : E n → ℝ} {x₀ : E n}

lemma sol_contX {X V : ℝ → E n} (h : IsSolution f 3 x₀ X V) : ContinuousOn X (Ici 0) := by
  intro t ht
  rcases (show (0:ℝ) ≤ t from ht).eq_or_lt with rfl | ht'
  · exact h.2.2.1.continuousWithinAt
  · exact ((h.2.2.2.2 t ht').1.continuousAt).continuousWithinAt

lemma sol_contV {X V : ℝ → E n} (h : IsSolution f 3 x₀ X V) : ContinuousOn V (Ici 0) := by
  intro t ht
  rcases (show (0:ℝ) ≤ t from ht).eq_or_lt with rfl | ht'
  · exact h.2.2.2.1
  · exact ((h.2.2.2.2 t ht').2.continuousAt).continuousWithinAt

lemma sol_V_eq (hG : Continuous (gradient f)) {X V : ℝ → E n} (h : IsSolution f 3 x₀ X V)
    {t : ℝ} (ht : 0 ≤ t) : V t = Q (fun s => gradient f (X s)) t := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [h.2.1, Q_zero]
  have hXc := sol_contX h
  have hVc := sol_contV h
  have hFc : ContinuousOn (fun s => s ^ 3 • gradient f (X s)) (Ici 0) :=
    (continuous_pow 3).continuousOn.smul (hG.comp_continuousOn hXc)
  have hint : IntegrableOn (fun s => s ^ 3 • gradient f (X s)) (uIcc 0 t) :=
    (hFc.mono (by rw [uIcc_of_le ht.le]; exact Icc_subset_Ici_self)).integrableOn_compact
      isCompact_uIcc
  have hIc := intervalIntegral.continuousOn_primitive_interval hint
  rw [uIcc_of_le ht.le] at hIc
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun s => s ^ 3 • V s + ∫ r in (0:ℝ)..s, r ^ 3 • gradient f (X r))
    (f' := fun _ => (0 : E n)) ht.le
    (((continuous_pow 3).continuousOn.smul (hVc.mono Icc_subset_Ici_self)).add hIc) ?_
    intervalIntegrable_const
  · simp only [intervalIntegral.integral_zero, intervalIntegral.integral_same] at key
    norm_num at key
    have e : t ^ 3 • V t = -∫ r in (0:ℝ)..t, r ^ 3 • gradient f (X r) :=
      eq_neg_of_add_eq_zero_left key.symm
    rw [Q, neg_smul, ← smul_neg, ← e, smul_smul, inv_mul_cancel₀ (pow_ne_zero 3 ht.ne'),
      one_smul]
  · intro s hs
    have hV' := (h.2.2.2.2 s hs.1).2
    have h1 := (hasDerivAt_pow 3 s).smul hV'
    have hint' : IntervalIntegrable (fun r => r ^ 3 • gradient f (X r)) volume 0 s :=
      (hFc.mono (by rw [uIcc_of_le hs.1.le]; exact Icc_subset_Ici_self)).intervalIntegrable
    have h2 := intervalIntegral.integral_hasDerivAt_right hint'
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi (hFc.mono Ioi_subset_Ici_self) s hs.1)
      (hFc.continuousAt (Ici_mem_nhds hs.1))
    refine (h1.add h2).congr_deriv ?_
    have e1 : s ^ 3 * -(3 / s) = -(((3 : ℕ) : ℝ) * s ^ (3 - 1)) := by
      norm_num; field_simp
    rw [smul_sub, smul_smul, e1, neg_smul]
    abel

lemma uniq {K : NNReal} (hK0 : 0 < K) (hG : LipschitzWith K (gradient f)) {X V Y W : ℝ → E n}
    (hX : IsSolution f 3 x₀ X V) (hY : IsSolution f 3 x₀ Y W) : Set.EqOn X Y (Ici 0) := by
  have hL : (0:ℝ) < K := NNReal.coe_pos.2 hK0
  intro t ht
  have ht : (0:ℝ) ≤ t := ht
  have hXc := sol_contX hX
  have hYc := sol_contX hY
  have hGc := hG.continuous
  have hDc : ContinuousOn (fun s => X s - Y s) (Icc 0 t) :=
    (hXc.sub hYc).mono Icc_subset_Ici_self
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) t)).exists_bound_of_continuousOn hDc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, ht⟩)
  have claim : ∀ k : ℕ, ∀ s ∈ Icc 0 t, ‖X s - Y s‖ ≤ M * (1 / 2) ^ k * wt K s := by
    intro k
    induction k with
    | zero =>
      intro s hs
      simpa using (hM s hs).trans (le_mul_of_one_le_right hM0 (one_le_wt hL.le s))
    | succ k ih =>
      have hck : 0 ≤ M * (1 / 2 : ℝ) ^ k := by positivity
      have key := cmp hL (D := fun s => X s - Y s) (U := fun s => V s - W s)
        (c := K * (M * (1 / 2) ^ k)) (T := t) (by positivity) hDc (by simp [hX.1, hY.1]) ?_ ?_
      · intro s hs
        refine (key s hs).trans (le_of_eq ?_)
        field_simp
        ring
      · intro x hx
        rcases hx.1.eq_or_lt with rfl | hx0
        · exact hX.2.2.1.sub hY.2.2.1
        · exact ((hX.2.2.2.2 x hx0).1.sub (hY.2.2.2.2 x hx0).1).hasDerivWithinAt
      · intro x hx
        have hsub : uIcc 0 x ⊆ Ici 0 := by rw [uIcc_of_le hx.1]; exact Icc_subset_Ici_self
        have i1 : IntervalIntegrable (fun s : ℝ => s ^ 3 • gradient f (X s)) volume 0 x :=
          (((continuous_pow 3).continuousOn.smul (hGc.comp_continuousOn hXc)).mono
            hsub).intervalIntegrable
        have i2 : IntervalIntegrable (fun s : ℝ => s ^ 3 • gradient f (Y s)) volume 0 x :=
          (((continuous_pow 3).continuousOn.smul (hGc.comp_continuousOn hYc)).mono
            hsub).intervalIntegrable
        show ‖V x - W x‖ ≤ _
        rw [sol_V_eq hGc hX hx.1, sol_V_eq hGc hY hx.1,
          Q_sub (F₁ := fun s => gradient f (X s)) (F₂ := fun s => gradient f (Y s)) i1 i2]
        refine norm_Q_le hL.le (by positivity) hx.1 (fun s hs => ?_)
        have h1 := hG.dist_le_mul (X s) (Y s)
        rw [dist_eq_norm, dist_eq_norm] at h1
        have h2 := ih s ⟨hs.1, hs.2.trans hx.2.le⟩
        calc ‖gradient f (X s) - gradient f (Y s)‖ ≤ K * ‖X s - Y s‖ := h1
          _ ≤ K * (M * (1 / 2) ^ k * wt K s) := mul_le_mul_of_nonneg_left h2 hL.le
          _ = K * (M * (1 / 2) ^ k) * wt K s := by ring
  have hlim : Tendsto (fun k : ℕ => M * (1 / 2 : ℝ) ^ k * wt K t) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul M).mul_const (wt K t)
    simpa using this
  have h0 : ‖X t - Y t‖ ≤ 0 := ge_of_tendsto' hlim (fun k => claim k t ⟨ht, le_rfl⟩)
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

end Uniq

end NesterovODE.WellPosed.NAux

open NesterovODE.WellPosed in
theorem solution {n : ℕ} (f : E n → ℝ) (x₀ : E n)
    (hf : ∃ L : NNReal, IsFL f L) :
    (∃ X V : ℝ → E n, IsSolution f 3 x₀ X V) ∧
    (∀ X V Y W : ℝ → E n,
      IsSolution f 3 x₀ X V → IsSolution f 3 x₀ Y W →
      Set.EqOn X Y (Set.Ici 0)) := by
  obtain ⟨K, hK0, -, -, hG⟩ := hf
  exact ⟨NAux.exists_sol f x₀ K hK0 hG, fun X V Y W hX hY => NAux.uniq hK0 hG hX hY⟩
