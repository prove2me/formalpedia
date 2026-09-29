-- Prove2me | solution 1 for MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_integral_insertNth_mul_cexp_le_mul_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/da135bab-32c9-5104-9fd7-e622538ccd5a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_integral_insertNth_mul_cexp_le_mul_prod

set_option autoImplicit false

open MeasureTheory

namespace PMDK6B

variable {n : ℕ}

abbrev Q := ℝ × ℝ
abbrev X (n : ℕ) := Fin n → ℝ

def box (n : ℕ) (R : ℝ) : Set (X n) := Set.Icc (fun _ => -R) (fun _ => R)

lemma isCompact_box (R : ℝ) : IsCompact (box n R) := isCompact_Icc
lemma measurableSet_box (R : ℝ) : MeasurableSet (box n R) := measurableSet_Icc
lemma volume_box_lt_top (R : ℝ) : volume (box n R) < ⊤ := (isCompact_box R).measure_lt_top

lemma not_mem_box {R : ℝ} {x : X n} (hx : x ∉ box n R) : ∃ i, R < |x i| := by
  by_contra h
  push_neg at h
  exact hx ⟨fun i => (abs_le.mp (h i)).1, fun i => (abs_le.mp (h i)).2⟩

noncomputable def ex (ξ : X n) (x : X n) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ξ i * x i : ℝ) : ℂ)))

lemma norm_ex (ξ x : X n) : ‖ex ξ x‖ = 1 := by
  rw [ex, Complex.norm_exp]
  have : (-(2 * Real.pi * Complex.I * ((∑ i, ξ i * x i : ℝ) : ℂ))).re = 0 := by simp [Complex.mul_re]
  rw [this, Real.exp_zero]

lemma continuous_ex (ξ : X n) : Continuous (ex ξ) := by
  unfold ex
  refine Complex.continuous_exp.comp (Continuous.neg (continuous_const.mul
    (Complex.continuous_ofReal.comp ?_)))
  exact continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i)

structure IsWin (R : ℝ) (V : Q × X n → ℂ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) V
  suppx : ∀ q : Q × X n, (∃ i, R < |q.2 i|) → V q = 0
  supps : ∀ q : Q × X n, R < |q.1.1| → V q = 0

private noncomputable def _root_.PMDK6B.dir (u : Q × X n) (V : Q × X n → ℂ) : Q × X n → ℂ := fun q => fderiv ℝ V q u

p2m_export "PMDK6B" "dir"
lemma isOpen_outx (R : ℝ) : IsOpen {q : Q × X n | ∃ i, R < |q.2 i|} := by
  have : {q : Q × X n | ∃ i, R < |q.2 i|} = ⋃ i, {q | R < |q.2 i|} := by ext q; simp
  rw [this]
  exact isOpen_iUnion fun i => isOpen_lt continuous_const
    (continuous_abs.comp ((continuous_apply i).comp continuous_snd))

lemma isOpen_outs (R : ℝ) : IsOpen {q : Q × X n | R < |q.1.1|} :=
  isOpen_lt continuous_const (continuous_abs.comp (continuous_fst.comp continuous_fst))

lemma fderiv_eq_zero_of_open {V : Q × X n → ℂ} {O : Set (Q × X n)} (hO : IsOpen O)
    (hV : ∀ q ∈ O, V q = 0) (q : Q × X n) (hq : q ∈ O) (u : Q × X n) : fderiv ℝ V q u = 0 := by
  have hev : V =ᶠ[nhds q] (fun _ => (0 : ℂ)) := by
    filter_upwards [hO.mem_nhds hq] with q' hq'
    exact hV q' hq'
  rw [hev.fderiv_eq]; simp

lemma IsWin.dir {R : ℝ} {V : Q × X n → ℂ} (hV : IsWin R V) (u : Q × X n) : IsWin R (dir u V) where
  smooth := ((contDiff_infty_iff_fderiv.1 hV.smooth).2).clm_apply contDiff_const
  suppx := fun q hq => fderiv_eq_zero_of_open (isOpen_outx R) (fun q' hq' => hV.suppx q' hq') q hq u
  supps := fun q hq => fderiv_eq_zero_of_open (isOpen_outs R) (fun q' hq' => hV.supps q' hq') q hq u

noncomputable def Ψ (ξ : X n) (V : Q × X n → ℂ) (p : Q) : ℂ := ∫ x, V (p, x) * ex ξ x

noncomputable def dV (V : Q × X n → ℂ) (q : Q × X n) : Q →L[ℝ] ℂ :=
  (fderiv ℝ V q).comp (ContinuousLinearMap.inl ℝ Q (X n))

lemma continuous_dV {V : Q × X n → ℂ} (hV : ContDiff ℝ (⊤ : ℕ∞) V) : Continuous (dV V) :=
  (((contDiff_infty_iff_fderiv.1 hV).2).continuous).clm_comp continuous_const

lemma hasFDerivAt_slice {V : Q × X n → ℂ} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (p : Q) (x : X n) :
    HasFDerivAt (fun p' : Q => V (p', x)) (dV V (p, x)) p := by
  have hd : HasFDerivAt V (fderiv ℝ V (p, x)) (p, x) :=
    (hV.differentiable (by simp)).differentiableAt.hasFDerivAt
  exact hd.comp p (hasFDerivAt_prodMk_left p x)

lemma dV_eq_zero {R : ℝ} {V : Q × X n → ℂ} (hV : IsWin R V) (p : Q) (x : X n) (hx : x ∉ box n R) :
    dV V (p, x) = 0 := by
  have hev : V =ᶠ[nhds (p, x)] (fun _ => (0 : ℂ)) := by
    filter_upwards [(isOpen_outx R).mem_nhds (not_mem_box hx)] with q' hq'
    exact hV.suppx q' hq'
  simp only [dV, hev.fderiv_eq, fderiv_const]
  simp

lemma exists_local_bound {Y : Type*} [NormedAddCommGroup Y] {F : Q × X n → Y} (hF : Continuous F)
    (p₀ : Q) (R : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Metric.closedBall p₀ 1, ∀ x ∈ box n R, ‖F (p, x)‖ ≤ C := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p₀ (1 : ℝ)).prod (isCompact_box (n := n) R)).exists_bound_of_continuousOn
    hF.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun p hp x hx => (hC (p, x) (Set.mem_prod.mpr ⟨hp, hx⟩)).trans (le_max_left _ _)⟩

lemma integrable_of_supp {Y : Type*} [NormedAddCommGroup Y] {f : X n → Y} (hf : Continuous f) {R : ℝ}
    (hsupp : ∀ x, x ∉ box n R → f x = 0) : Integrable f := by
  refine hf.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_box R) hsupp)

lemma hasFDerivAt_Ψ {R : ℝ} {V : Q × X n → ℂ} (hV : IsWin R V) (ξ : X n) (p₀ : Q) :
    HasFDerivAt (Ψ ξ V) (∫ x, ex ξ x • dV V (p₀, x)) p₀ := by
  have hVc : Continuous V := hV.smooth.continuous
  have hdVc : Continuous (dV V) := continuous_dV hV.smooth
  obtain ⟨C, hC0, hC⟩ := exists_local_bound hdVc p₀ R
  have hslice : ∀ p, Continuous fun x : X n => ex ξ x • V (p, x) := fun p =>
    (continuous_ex ξ).smul (hVc.comp (continuous_const.prodMk continuous_id))
  have hslice' : ∀ p, Continuous fun x : X n => ex ξ x • dV V (p, x) := fun p =>
    (continuous_ex ξ).smul (hdVc.comp (continuous_const.prodMk continuous_id))
  have e : Ψ ξ V = fun p => ∫ x, ex ξ x • V (p, x) := by
    funext p; simp only [Ψ, smul_eq_mul, mul_comm]
  rw [e]
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun p x => ex ξ x • V (p, x)) (F' := fun p x => ex ξ x • dV V (p, x)) (x₀ := p₀)
    (s := Metric.ball p₀ 1) (bound := (box n R).indicator fun _ => C) (Metric.ball_mem_nhds p₀ one_pos)
    (Filter.Eventually.of_forall fun p => (hslice p).aestronglyMeasurable)
    (integrable_of_supp (hslice p₀) (fun x hx => by
      show ex ξ x • V (p₀, x) = 0
      rw [hV.suppx (p₀, x) (not_mem_box hx), smul_zero]))
    (hslice' p₀).aestronglyMeasurable
    (ae_of_all _ fun x p hp => by
      rw [norm_smul, norm_ex, one_mul]
      by_cases hx : x ∈ box n R
      · rw [Set.indicator_of_mem hx]; exact hC p (Metric.ball_subset_closedBall hp) x hx
      · rw [Set.indicator_of_notMem hx, dV_eq_zero hV p x hx, norm_zero])
    ((integrableOn_const (volume_box_lt_top R).ne).integrable_indicator (measurableSet_box R))
    (ae_of_all _ fun x p _ => (hasFDerivAt_slice hV.smooth p x).const_smul (ex ξ x))

lemma fderiv_Ψ_apply {R : ℝ} {V : Q × X n → ℂ} (hV : IsWin R V) (ξ : X n) (p : Q) (v : Q) :
    fderiv ℝ (Ψ ξ V) p v = Ψ ξ (dir (v, (0 : X n)) V) p := by
  rw [(hasFDerivAt_Ψ hV ξ p).fderiv]
  have hcs : HasCompactSupport (fun x : X n => dV V (p, x)) :=
    HasCompactSupport.intro (isCompact_box R) (fun x hx => dV_eq_zero hV p x hx)
  have hdVint : Integrable (fun x : X n => dV V (p, x)) :=
    ((continuous_dV hV.smooth).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport hcs
  have hint : Integrable (fun x => ex ξ x • dV V (p, x)) :=
    hdVint.norm.mono'
      ((continuous_ex ξ).smul ((continuous_dV hV.smooth).comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [norm_smul, norm_ex, one_mul])
  rw [ContinuousLinearMap.integral_apply hint v]
  simp only [Ψ, dir, dV, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearMap.inl_apply, smul_eq_mul, mul_comm]

lemma differentiable_Ψ {R : ℝ} {V : Q × X n → ℂ} (hV : IsWin R V) (ξ : X n) :
    Differentiable ℝ (Ψ ξ V) := fun p => (hasFDerivAt_Ψ hV ξ p).differentiableAt

lemma contDiff_Ψ_nat (R : ℝ) (ξ : X n) : ∀ (i : ℕ) (V : Q × X n → ℂ), IsWin R V → ContDiff ℝ i (Ψ ξ V) := by
  intro i
  induction i with
  | zero =>
    intro V hV
    exact contDiff_zero.mpr (differentiable_Ψ hV ξ).continuous
  | succ i ih =>
    intro V hV
    rw [show ((i + 1 : ℕ) : WithTop ℕ∞) = (i : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_fderiv_apply]
    refine ⟨differentiable_Ψ hV ξ, fun h => absurd h (by simp), fun v => ?_⟩
    have : (fun p => fderiv ℝ (Ψ ξ V) p v) = Ψ ξ (dir (v, (0 : X n)) V) :=
      funext fun p => fderiv_Ψ_apply hV ξ p v
    rw [this]
    exact ih _ (hV.dir _)

lemma contDiff_Ψ {R : ℝ} {V : Q × X n → ℂ} (hV : IsWin R V) (ξ : X n) : ContDiff ℝ (⊤ : ℕ∞) (Ψ ξ V) :=
  contDiff_infty.2 fun i => contDiff_Ψ_nat R ξ i V hV

private noncomputable def _root_.PMDK6B.DDX : (ℓ : ℕ) → (Fin ℓ → Q) → (Q × X n → ℂ) → (Q × X n → ℂ)
  | 0, _, V => V
  | ℓ + 1, u, V => DDX ℓ (Fin.init u) (dir (u (Fin.last ℓ), (0 : X n)) V)

p2m_export "PMDK6B" "DDX"
lemma IsWin.DDX {R : ℝ} : ∀ (ℓ : ℕ) (u : Fin ℓ → Q) {V : Q × X n → ℂ}, IsWin R V → IsWin R (DDX ℓ u V)
  | 0, _, _, hV => hV
  | ℓ + 1, u, _, hV => IsWin.DDX ℓ (Fin.init u) (hV.dir _)

lemma iteratedFDeriv_Ψ_apply {R : ℝ} (ξ : X n) : ∀ (ℓ : ℕ) (V : Q × X n → ℂ),
    IsWin R V → ∀ (p : Q) (u : Fin ℓ → Q), (iteratedFDeriv ℝ ℓ (Ψ ξ V) p) u = Ψ ξ (DDX ℓ u V) p := by
  intro ℓ
  induction ℓ with
  | zero => intro V hV p u; simp [DDX]
  | succ ℓ ih =>
    intro V hV p u
    rw [iteratedFDeriv_succ_apply_right]
    set L : (Q →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ (u (Fin.last ℓ)) with hL
    have hfd : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ (Ψ ξ V) y) :=
      (contDiff_infty_iff_fderiv.1 (contDiff_Ψ hV ξ)).2
    have h1 : iteratedFDeriv ℝ ℓ (fun y => fderiv ℝ (Ψ ξ V) y (u (Fin.last ℓ))) p =
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ ℓ (fun y => fderiv ℝ (Ψ ξ V) y) p) := by
      have : (fun y => fderiv ℝ (Ψ ξ V) y (u (Fin.last ℓ))) = L ∘ (fun y => fderiv ℝ (Ψ ξ V) y) := by
        funext y; simp [hL]
      rw [this, ContinuousLinearMap.iteratedFDeriv_comp_left L hfd.contDiffAt (by exact_mod_cast le_top)]
    have h2 : ((iteratedFDeriv ℝ ℓ (fun y => fderiv ℝ (Ψ ξ V) y) p) (Fin.init u)) (u (Fin.last ℓ)) =
        (iteratedFDeriv ℝ ℓ (fun y => fderiv ℝ (Ψ ξ V) y (u (Fin.last ℓ))) p) (Fin.init u) := by
      rw [h1]; simp [hL]
    rw [h2]
    have h3 : (fun y => fderiv ℝ (Ψ ξ V) y (u (Fin.last ℓ))) = Ψ ξ (dir (u (Fin.last ℓ), (0 : X n)) V) :=
      funext fun y => fderiv_Ψ_apply hV ξ y _
    rw [h3, ih _ (hV.dir _) p (Fin.init u)]
    rfl

lemma norm_iteratedFDeriv_dir_le {V : Q × X n → ℂ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (w : Q × X n) (j : ℕ) (q : Q × X n) :
    ‖iteratedFDeriv ℝ j (dir w V) q‖ ≤ ‖w‖ * ‖iteratedFDeriv ℝ (j + 1) V q‖ := by
  set L : ((Q × X n) →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ w with hL
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ V y) := (contDiff_infty_iff_fderiv.1 hV).2
  have : dir w V = L ∘ (fun y => fderiv ℝ V y) := by funext y; simp [hL, dir]
  rw [this, ContinuousLinearMap.iteratedFDeriv_comp_left L hfd.contDiffAt (by exact_mod_cast le_top),
    ← norm_iteratedFDeriv_fderiv]
  calc ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ j (fderiv ℝ V) q)‖
      ≤ ‖L‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ V) q‖ := ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ ‖w‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ V) q‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg w) (fun f => ?_)
        rw [hL, ContinuousLinearMap.apply_apply, mul_comm]
        exact f.le_opNorm w

lemma norm_iteratedFDeriv_DDX_le {R : ℝ} : ∀ (ℓ : ℕ) (u : Fin ℓ → Q) {V : Q × X n → ℂ}, IsWin R V →
    ∀ (j : ℕ) (q : Q × X n), ‖iteratedFDeriv ℝ j (DDX ℓ u V) q‖ ≤ (∏ i, ‖u i‖) * ‖iteratedFDeriv ℝ (j + ℓ) V q‖
  | 0, u, V, hV, j, q => by simp [DDX]
  | ℓ + 1, u, V, hV, j, q => by
    have ih := norm_iteratedFDeriv_DDX_le ℓ (Fin.init u) (hV.dir (u (Fin.last ℓ), (0 : X n))) j q
    have h2 := norm_iteratedFDeriv_dir_le hV.smooth (u (Fin.last ℓ), (0 : X n)) (j + ℓ) q
    have hnorm : ‖(u (Fin.last ℓ), (0 : X n))‖ = ‖u (Fin.last ℓ)‖ := by simp [Prod.norm_def]
    rw [hnorm] at h2
    calc ‖iteratedFDeriv ℝ j (DDX (ℓ + 1) u V) q‖
        = ‖iteratedFDeriv ℝ j (DDX ℓ (Fin.init u) (dir (u (Fin.last ℓ), (0 : X n)) V)) q‖ := rfl
      _ ≤ (∏ i, ‖Fin.init u i‖) * ‖iteratedFDeriv ℝ (j + ℓ) (dir (u (Fin.last ℓ), (0 : X n)) V) q‖ := ih
      _ ≤ (∏ i, ‖Fin.init u i‖) * (‖u (Fin.last ℓ)‖ * ‖iteratedFDeriv ℝ (j + ℓ + 1) V q‖) :=
          mul_le_mul_of_nonneg_left h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      _ = (∏ i, ‖u i‖) * ‖iteratedFDeriv ℝ (j + (ℓ + 1)) V q‖ := by
          have e : iteratedFDeriv ℝ (j + (ℓ + 1)) V q = iteratedFDeriv ℝ (j + ℓ + 1) V q := rfl
          rw [e, Fin.prod_univ_castSucc (fun i => ‖u i‖)]
          simp only [Fin.init]
          ring

def vX (i : Fin n) : Q × X n := ((0 : Q), (Pi.single i (1 : ℝ) : X n))

lemma norm_single (i : Fin n) : ‖(Pi.single i (1 : ℝ) : X n)‖ = 1 := by
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i' => ?_
    by_cases h : i' = i
    · subst h; simp
    · simp [h]
  · have := norm_le_pi_norm (Pi.single i (1 : ℝ) : X n) i
    simpa using this

lemma norm_vX (i : Fin n) : ‖(vX i : Q × X n)‖ = 1 := by
  simp only [vX, Prod.norm_def, norm_zero]
  rw [max_eq_right (norm_nonneg _), norm_single]

lemma norm_iteratedFDeriv_dX2_le {V : Q × X n → ℂ} (hV : ContDiff ℝ (⊤ : ℕ∞) V) (a : Fin n) (j : ℕ)
    (q : Q × X n) : ‖iteratedFDeriv ℝ j (dir (vX a) (dir (vX a) V)) q‖ ≤ ‖iteratedFDeriv ℝ (j + 2) V q‖ := by
  have hV' : ContDiff ℝ (⊤ : ℕ∞) (dir (vX a) V) := ((contDiff_infty_iff_fderiv.1 hV).2).clm_apply contDiff_const
  calc _ ≤ ‖(vX a : Q × X n)‖ * ‖iteratedFDeriv ℝ (j + 1) (dir (vX a) V) q‖ := norm_iteratedFDeriv_dir_le hV' _ j q
    _ ≤ ‖(vX a : Q × X n)‖ * (‖(vX a : Q × X n)‖ * ‖iteratedFDeriv ℝ (j + 1 + 1) V q‖) :=
        mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_dir_le hV _ (j + 1) q) (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ (j + 2) V q‖ := by rw [norm_vX]; ring_nf

lemma ex_sub_smul (ξ : X n) (x : X n) (i : Fin n) (τ : ℝ) :
    ex ξ (x - τ • Pi.single i 1) = ex ξ x * Complex.exp (2 * Real.pi * Complex.I * (ξ i) * τ) := by
  unfold ex
  have : (∑ i', ξ i' * (x - τ • (Pi.single i 1 : X n)) i') = (∑ i', ξ i' * x i') - ξ i * τ := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp
    · intro i' _ hi; simp [hi]
    · simp
  rw [this, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma integral_fderiv_mul_ex (g : X n → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (ξ : X n) (i : Fin n) :
    ∫ x, fderiv ℝ g x (Pi.single i 1) * ex ξ x = (2 * Real.pi * Complex.I * (ξ i)) * ∫ x, g x * ex ξ x := by
  set v : X n := Pi.single i 1 with hv
  set φ : ℝ → ℂ := fun τ => ∫ x, g (x + τ • v) * ex ξ x with hφ

  have hφ1 : ∀ τ : ℝ, φ τ = Complex.exp (2 * Real.pi * Complex.I * (ξ i) * τ) * ∫ x, g x * ex ξ x := by
    intro τ
    have := integral_add_right_eq_self (μ := (volume : Measure (X n))) (fun x => g x * ex ξ (x - τ • v)) (τ • v)
    simp only [add_sub_cancel_right] at this
    rw [hφ]
    simp only
    rw [this]
    simp_rw [hv, ex_sub_smul]
    rw [← integral_const_mul]
    congr 1; funext x; ring

  have hgc' : Continuous g := hg.continuous
  have hg' : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ g x) := (contDiff_infty_iff_fderiv.1 hg).2
  have hg's : HasCompactSupport (fun x => fderiv ℝ g x) := hgc.fderiv ℝ
  obtain ⟨C, hC⟩ := hg'.continuous.bounded_above_of_compact_support hg's
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℝ, ∀ x, x ∉ Metric.closedBall (0 : X n) R₀ → fderiv ℝ g x = 0 := by
    obtain ⟨R₀, hR₀⟩ := hg's.isCompact.isBounded.subset_closedBall 0
    exact ⟨R₀, fun x hx => by
      by_contra h
      exact hx (hR₀ (subset_tsupport _ h))⟩
  have hderiv : ∀ (x : X n) (τ : ℝ),
      HasDerivAt (fun σ : ℝ => g (x + σ • v) * ex ξ x) (fderiv ℝ g (x + τ • v) v * ex ξ x) τ := by
    intro x τ
    have hl : HasDerivAt (fun σ : ℝ => x + σ • v) v τ := by
      have := ((hasDerivAt_id τ).smul_const v).const_add x
      simpa using this
    have hG : HasFDerivAt g (fderiv ℝ g (x + τ • v)) (x + τ • v) :=
      (hg.differentiable (by simp)).differentiableAt.hasFDerivAt
    exact (hG.comp_hasDerivAt τ hl).mul_const _
  have hv1 : ‖v‖ = 1 := by rw [hv]; exact norm_single i
  have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (X n)))
    (F := fun (τ : ℝ) (x : X n) => g (x + τ • v) * ex ξ x)
    (F' := fun (τ : ℝ) (x : X n) => fderiv ℝ g (x + τ • v) v * ex ξ x) (x₀ := 0)
    (s := Metric.ball 0 1) (bound := (Metric.closedBall (0 : X n) (R₀ + 1)).indicator fun _ => C * ‖v‖)
    (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall fun τ => ((hgc'.comp (continuous_id.add continuous_const)).mul
      (continuous_ex ξ)).aestronglyMeasurable)
    (by
      have : (fun x : X n => g (x + (0 : ℝ) • v) * ex ξ x) = fun x => g x * ex ξ x := by
        funext x; simp
      show Integrable (fun x : X n => g (x + (0 : ℝ) • v) * ex ξ x) volume
      rw [this]
      exact (hgc'.mul (continuous_ex ξ)).integrable_of_hasCompactSupport hgc.mul_right)
    (((hg'.continuous.comp (continuous_id.add continuous_const)).clm_apply continuous_const).mul
      (continuous_ex ξ)).aestronglyMeasurable
    (ae_of_all _ fun x τ hτ => by
      rw [norm_mul, norm_ex, mul_one]
      by_cases hx : x ∈ Metric.closedBall (0 : X n) (R₀ + 1)
      · rw [Set.indicator_of_mem hx]
        exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
      · rw [Set.indicator_of_notMem hx]
        have hτ' : |τ| < 1 := by simpa using hτ
        have : x + τ • v ∉ Metric.closedBall (0 : X n) R₀ := by
          intro h
          apply hx
          rw [Metric.mem_closedBall, dist_zero_right] at h ⊢
          have : ‖x‖ ≤ ‖x + τ • v‖ + ‖τ • v‖ := by
            calc ‖x‖ = ‖(x + τ • v) - τ • v‖ := by rw [add_sub_cancel_right]
              _ ≤ ‖x + τ • v‖ + ‖τ • v‖ := norm_sub_le _ _
          rw [norm_smul, hv1, mul_one, Real.norm_eq_abs] at this
          linarith
        rw [hR₀ _ this, ContinuousLinearMap.zero_apply, norm_zero])
    ((integrableOn_const (measure_closedBall_lt_top).ne).integrable_indicator measurableSet_closedBall)
    (ae_of_all _ fun x τ _ => hderiv x τ)
  have hD2 : HasDerivAt φ (∫ x, fderiv ℝ g (x + (0 : ℝ) • v) v * ex ξ x) 0 := hD.2
  simp only [zero_smul, add_zero] at hD2
  have hD3 : HasDerivAt φ (Complex.exp (2 * Real.pi * Complex.I * (ξ i) * (0 : ℝ)) *
      (2 * Real.pi * Complex.I * (ξ i)) * ∫ x, g x * ex ξ x) 0 := by
    have e : φ = fun τ : ℝ => Complex.exp (2 * Real.pi * Complex.I * (ξ i) * τ) * ∫ x, g x * ex ξ x :=
      funext hφ1
    rw [e]
    apply HasDerivAt.mul_const
    have h1 : HasDerivAt (fun τ : ℝ => 2 * Real.pi * Complex.I * (ξ i) * (τ : ℂ))
        (2 * Real.pi * Complex.I * (ξ i) * 1) 0 := by
      have : HasDerivAt (fun τ : ℝ => ((id τ : ℝ) : ℂ)) ((1 : ℝ) : ℂ) 0 := (hasDerivAt_id (0 : ℝ)).ofReal_comp
      simpa using this.const_mul (2 * Real.pi * Complex.I * (ξ i))
    have := h1.cexp
    simpa using this
  have := hD2.unique hD3
  rw [hv] at this
  rw [this]
  simp

lemma hasCompactSupport_slice {R : ℝ} {U : Q × X n → ℂ} (hU : IsWin R U) (p : Q) :
    HasCompactSupport (fun x : X n => U (p, x)) :=
  HasCompactSupport.intro (isCompact_box R) (fun x hx => hU.suppx (p, x) (not_mem_box hx))

lemma Ψ_dX {R : ℝ} {U : Q × X n → ℂ} (hU : IsWin R U) (ξ : X n) (i : Fin n) (p : Q) :
    Ψ ξ (dir (vX i) U) p = (2 * Real.pi * Complex.I * (ξ i)) * Ψ ξ U p := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x : X n => U (p, x)) := hU.smooth.comp (contDiff_const.prodMk contDiff_id)
  have key := integral_fderiv_mul_ex (fun x => U (p, x)) hg (hasCompactSupport_slice hU p) ξ i
  have hderiv : ∀ x : X n, fderiv ℝ (fun x : X n => U (p, x)) x (Pi.single i 1) = dir (vX i) U (p, x) := by
    intro x
    have hd : HasFDerivAt U (fderiv ℝ U (p, x)) (p, x) :=
      (hU.smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
    have h2 : HasFDerivAt (fun x' : X n => U (p, x')) ((fderiv ℝ U (p, x)).comp (ContinuousLinearMap.inr ℝ Q (X n))) x :=
      hd.comp x (hasFDerivAt_prodMk_right p x)
    rw [h2.fderiv]
    simp [dir, vX]
  simp_rw [hderiv] at key
  exact key

lemma norm_Ψ_eq {R : ℝ} {U : Q × X n → ℂ} (hU : IsWin R U) (ξ : X n) (i : Fin n) (hi : ξ i ≠ 0) (p : Q) :
    ‖Ψ ξ U p‖ = ‖Ψ ξ (dir (vX i) (dir (vX i) U)) p‖ * ((2 * Real.pi * |ξ i|) ^ 2)⁻¹ := by
  rw [Ψ_dX (hU.dir _) ξ i p, Ψ_dX hU ξ i p]
  set C : ℂ := 2 * Real.pi * Complex.I * (ξ i) with hCdef
  clear_value C
  have hn : ‖C‖ = 2 * Real.pi * |ξ i| := by
    rw [hCdef, norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_ofNat]
  rw [norm_mul, norm_mul, hn]
  have hpos : 0 < 2 * Real.pi * |ξ i| := by
    have : (0 : ℝ) < |ξ i| := abs_pos.mpr hi
    positivity
  field_simp

lemma norm_Ψ_le_of_bound {R : ℝ} {U : Q × X n → ℂ} (hU : IsWin R U) (ξ : X n) (p : Q) {C : ℝ}
    (hC : ∀ x, ‖U (p, x)‖ ≤ C) : ‖Ψ ξ U p‖ ≤ C * (volume (box n R)).toReal := by
  unfold Ψ
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := box n R)
    (fun x hx => by rw [hU.suppx (p, x) (not_mem_box hx), zero_mul])]
  have := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure (X n))) (s := box n R)
    (f := fun x => U (p, x) * ex ξ x) (C := C) (volume_box_lt_top R)
    (fun x _ => by rw [norm_mul, norm_ex, mul_one]; exact hC x)
  simpa [Measure.real] using this

lemma decay {R : ℝ} (ξ : X n) (p : Q) :
    ∀ (S : Finset (Fin n)), (∀ j ∈ S, ξ j ≠ 0) →
      ∀ (k : ℕ) (C : ℝ) (U : Q × X n → ℂ), IsWin R U → 2 * S.card ≤ k →
        (∀ i : ℕ, i ≤ k → ∀ q, ‖iteratedFDeriv ℝ i U q‖ ≤ C) →
        ‖Ψ ξ U p‖ ≤ C * (volume (box n R)).toReal * ∏ j ∈ S, ((2 * Real.pi * |ξ j|) ^ 2)⁻¹ := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ k C U hU _ hb
    rw [Finset.prod_empty, mul_one]
    exact norm_Ψ_le_of_bound hU ξ p fun x => by
      have := hb 0 (Nat.zero_le k) (p, x)
      rwa [norm_iteratedFDeriv_zero] at this
  | insert a S ha ih =>
    intro hm k C U hU hk hb
    have hma : ξ a ≠ 0 := hm a (Finset.mem_insert_self a S)
    have hmS : ∀ j ∈ S, ξ j ≠ 0 := fun j hj => hm j (Finset.mem_insert_of_mem hj)
    rw [Finset.card_insert_of_notMem ha] at hk
    set U' := dir (vX a) (dir (vX a) U) with hU'
    have hU'w : IsWin R U' := (hU.dir _).dir _
    have hb' : ∀ i : ℕ, i ≤ k - 2 → ∀ q, ‖iteratedFDeriv ℝ i U' q‖ ≤ C := fun i hi q =>
      (norm_iteratedFDeriv_dX2_le hU.smooth a i q).trans (hb (i + 2) (by omega) q)
    have := ih hmS (k - 2) C U' hU'w (by omega) hb'
    rw [norm_Ψ_eq hU ξ a hma p, Finset.prod_insert ha]
    have hpos : 0 ≤ ((2 * Real.pi * |ξ a|) ^ 2)⁻¹ := by positivity
    calc ‖Ψ ξ U' p‖ * ((2 * Real.pi * |ξ a|) ^ 2)⁻¹
        ≤ (C * (volume (box n R)).toReal * ∏ j ∈ S, ((2 * Real.pi * |ξ j|) ^ 2)⁻¹) * ((2 * Real.pi * |ξ a|) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right this hpos
      _ = C * (volume (box n R)).toReal * (((2 * Real.pi * |ξ a|) ^ 2)⁻¹ * ∏ j ∈ S, ((2 * Real.pi * |ξ j|) ^ 2)⁻¹) := by
          ring

lemma prod_filter_le (ξ : X n) :
    ∏ j ∈ Finset.univ.filter (fun j => 1 ≤ |ξ j|), ((2 * Real.pi * |ξ j|) ^ 2)⁻¹ ≤
      4 ^ n * ∏ j, (1 + |ξ j|)⁻¹ ^ 2 := by
  classical
  rw [Finset.prod_filter]
  have h4 : (4 : ℝ) ^ n * ∏ j, (1 + |ξ j|)⁻¹ ^ 2 = ∏ j : Fin n, (4 * (1 + |ξ j|)⁻¹ ^ 2) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h4]
  apply Finset.prod_le_prod
  · intro j _; split_ifs <;> positivity
  · intro j _
    have hπ := Real.pi_gt_three
    split_ifs with h
    · have h0 : 0 ≤ ((1 + |ξ j|) ^ 2)⁻¹ := by positivity
      calc ((2 * Real.pi * |ξ j|) ^ 2)⁻¹ ≤ ((1 + |ξ j|) ^ 2)⁻¹ :=
            inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by nlinarith) 2)
        _ ≤ 4 * (1 + |ξ j|)⁻¹ ^ 2 := by rw [inv_pow]; linarith
    · push_neg at h
      have hx : (1 + |ξ j|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg (ξ j)]
      have : (4 : ℝ)⁻¹ ≤ ((1 + |ξ j|) ^ 2)⁻¹ := inv_anti₀ (by positivity) hx
      rw [inv_pow]; linarith

section Insert
variable (k : Fin (n + 1))

noncomputable def A : Q × X n →L[ℝ] (Fin (n + 1) → ℝ) × ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => ((Fin.insertNth (α := fun _ => ℝ) k q.1.1 q.2 : Fin (n + 1) → ℝ), q.1.2)
      map_add' := fun a b => by
        ext ℓ
        · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
          rcases Fin.eq_self_or_eq_succAbove k ℓ with rfl | ⟨i', rfl⟩
          · simp [Fin.insertNth_apply_same]
          · simp [Fin.insertNth_apply_succAbove]
        · simp
      map_smul' := fun c a => by
        ext ℓ
        · simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply]
          rcases Fin.eq_self_or_eq_succAbove k ℓ with rfl | ⟨i', rfl⟩
          · simp [Fin.insertNth_apply_same]
          · simp [Fin.insertNth_apply_succAbove]
        · simp }

lemma A_apply (q : Q × X n) :
    A k q = ((Fin.insertNth (α := fun _ => ℝ) k q.1.1 q.2 : Fin (n + 1) → ℝ), q.1.2) := rfl

lemma norm_A_le : ‖(A k : Q × X n →L[ℝ] (Fin (n + 1) → ℝ) × ℝ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => ?_
  rw [one_mul, A_apply, Prod.norm_def]
  have h1 : ‖q.1‖ ≤ ‖q‖ := norm_fst_le q
  have h2 : ‖q.2‖ ≤ ‖q‖ := norm_snd_le q
  have h11 : ‖q.1.1‖ ≤ ‖q.1‖ := norm_fst_le q.1
  have h12 : ‖q.1.2‖ ≤ ‖q.1‖ := norm_snd_le q.1
  refine max_le ?_ (by simpa using h12.trans h1)
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun ℓ => ?_
  rcases Fin.eq_self_or_eq_succAbove k ℓ with rfl | ⟨i', rfl⟩
  · simp only [Fin.insertNth_apply_same]; exact h11.trans h1
  · simp only [Fin.insertNth_apply_succAbove]; exact (norm_le_pi_norm q.2 i').trans h2

lemma norm_iteratedFDeriv_comp_A_le {g : (Fin (n + 1) → ℝ) × ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {M : ℝ} (ℓ : ℕ) (hM : ∀ p, ‖iteratedFDeriv ℝ ℓ g p‖ ≤ M) (q : Q × X n) :
    ‖iteratedFDeriv ℝ ℓ (g ∘ (A k)) q‖ ≤ M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (A k q))
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (A k) hg q (by exact_mod_cast le_top)]
  calc _ ≤ ‖iteratedFDeriv ℝ ℓ g (A k q)‖ * ∏ _i : Fin ℓ, ‖(A k : Q × X n →L[ℝ] (Fin (n + 1) → ℝ) × ℝ)‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ M * 1 := mul_le_mul (hM _) (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => norm_A_le k)
        (Finset.prod_nonneg fun _ _ => norm_nonneg _) hM0
    _ = M := mul_one M

end Insert

end PMDK6B

theorem solution
    (n N : ℕ) (k : Fin (n + 1)) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : (Fin (n + 1) → ℝ) × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) g →
      (∀ p : (Fin (n + 1) → ℝ) × ℝ, (∃ i, R < |p.1 i|) → g p = 0) →
      ∀ M : ℝ, (∀ i : ℕ, i ≤ N + 2 * n → ∀ p : (Fin (n + 1) → ℝ) × ℝ, ‖iteratedFDeriv ℝ i g p‖ ≤ M) →
      ∀ ξ' : Fin n → ℝ,
        let h : ℝ × ℝ → ℂ := fun q =>
          ∫ x' : Fin n → ℝ, g (Fin.insertNth k q.1 x', q.2) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ξ' i * x' i : ℝ) : ℂ)))
        ContDiff ℝ (⊤ : ℕ∞) h ∧ (∀ q : ℝ × ℝ, R < |q.1| → h q = 0) ∧
          ∀ i : ℕ, i ≤ N → ∀ q : ℝ × ℝ,
            ‖iteratedFDeriv ℝ i h q‖ ≤ K * M * ∏ i', (1 + |ξ' i'|)⁻¹ ^ 2 := by
  classical
  refine ⟨4 ^ n * (volume (PMDK6B.box n R)).toReal, by positivity, ?_⟩
  intro g hg hgsupp M hM ξ'
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le _) 0)
  set V : PMDK6B.Q × PMDK6B.X n → ℂ := g ∘ (PMDK6B.A k) with hV
  have hVw : PMDK6B.IsWin R V :=
    { smooth := by rw [hV]; exact hg.comp (PMDK6B.A k).contDiff
      suppx := fun q ⟨i, hi⟩ => by
        simp only [hV, Function.comp_apply, PMDK6B.A_apply]
        exact hgsupp _ ⟨k.succAbove i, by simpa [Fin.insertNth_apply_succAbove] using hi⟩
      supps := fun q hq => by
        simp only [hV, Function.comp_apply, PMDK6B.A_apply]
        exact hgsupp _ ⟨k, by simpa [Fin.insertNth_apply_same] using hq⟩ }
  have hVb : ∀ i : ℕ, i ≤ N + 2 * n → ∀ q, ‖iteratedFDeriv ℝ i V q‖ ≤ M := fun i hi q =>
    PMDK6B.norm_iteratedFDeriv_comp_A_le k hg i (hM i hi) q
  have hΨ : (fun q : ℝ × ℝ => ∫ x' : Fin n → ℝ, g (Fin.insertNth k q.1 x', q.2) *
      Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ξ' i * x' i : ℝ) : ℂ)))) = PMDK6B.Ψ ξ' V := rfl
  simp only []
  rw [hΨ]
  refine ⟨PMDK6B.contDiff_Ψ hVw ξ', ?_, ?_⟩
  · intro q hq
    show (∫ x, V (q, x) * PMDK6B.ex ξ' x) = 0
    have : ∀ x, V (q, x) * PMDK6B.ex ξ' x = 0 := fun x => by rw [hVw.supps (q, x) hq, zero_mul]
    simp_rw [this]
    exact integral_zero _ _
  · intro i hi q
    obtain ⟨S, hS⟩ : ∃ S : Finset (Fin n), S = Finset.univ.filter (fun j => 1 ≤ |ξ' j|) := ⟨_, rfl⟩
    have hSm : ∀ j ∈ S, ξ' j ≠ 0 := fun j hj => by
      rw [hS] at hj
      have := (Finset.mem_filter.mp hj).2
      intro h; rw [h, abs_zero] at this; exact absurd this (by norm_num)
    have hScard : 2 * S.card ≤ 2 * n := by
      have h1 := Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun j => 1 ≤ |ξ' j|)
      rw [Finset.card_univ, Fintype.card_fin, ← hS] at h1
      omega
    have hprod : ∏ j ∈ S, ((2 * Real.pi * |ξ' j|) ^ 2)⁻¹ ≤ 4 ^ n * ∏ j, (1 + |ξ' j|)⁻¹ ^ 2 := by
      rw [hS]; exact PMDK6B.prod_filter_le ξ'
    have hT0 : 0 ≤ ∏ j, (1 + |ξ' j|)⁻¹ ^ 2 := Finset.prod_nonneg fun j _ => by positivity
    apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
    intro u
    rw [PMDK6B.iteratedFDeriv_Ψ_apply ξ' i V hVw q u]
    have hU : PMDK6B.IsWin R (PMDK6B.DDX i u V) := hVw.DDX i u
    have hUb : ∀ i' : ℕ, i' ≤ 2 * n → ∀ q', ‖iteratedFDeriv ℝ i' (PMDK6B.DDX i u V) q'‖ ≤ (∏ i, ‖u i‖) * M := by
      intro i' hi' q'
      refine (PMDK6B.norm_iteratedFDeriv_DDX_le i u hVw i' q').trans ?_
      exact mul_le_mul_of_nonneg_left (hVb (i' + i) (by omega) q') (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    have hdec := PMDK6B.decay ξ' q S hSm (2 * n) ((∏ i, ‖u i‖) * M) (PMDK6B.DDX i u V) hU hScard hUb
    have hvb : 0 ≤ (volume (PMDK6B.box n R)).toReal := ENNReal.toReal_nonneg
    calc ‖PMDK6B.Ψ ξ' (PMDK6B.DDX i u V) q‖
        ≤ (∏ i, ‖u i‖) * M * (volume (PMDK6B.box n R)).toReal * ∏ j ∈ S, ((2 * Real.pi * |ξ' j|) ^ 2)⁻¹ := hdec
      _ ≤ (∏ i, ‖u i‖) * M * (volume (PMDK6B.box n R)).toReal * (4 ^ n * ∏ j, (1 + |ξ' j|)⁻¹ ^ 2) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = 4 ^ n * (volume (PMDK6B.box n R)).toReal * M * (∏ j, (1 + |ξ' j|)⁻¹ ^ 2) * ∏ i, ‖u i‖ := by ring

end S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_integral_insertNth_mul_cexp_le_mul_prod
end P2MW
export P2MW.S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_integral_insertNth_mul_cexp_le_mul_prod (solution)
