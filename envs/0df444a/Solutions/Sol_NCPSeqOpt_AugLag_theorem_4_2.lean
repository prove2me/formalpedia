-- Prove2me | solution 1 for NCPSeqOpt.AugLag.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T13:03:10.573678+00:00
-- url     : https://prove2.me/submissions/1ba9e2dc-89dc-484c-91b3-57e8201680e3

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_NCPSeqOpt_AugLag_Setting

open MoreauProx.Decomposition
open scoped InnerProductSpace
open Filter Topology

namespace AuxAugLag42

open NCPSeqOpt.AugLag

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- closed convex nonempty -/
def CCN (C : Set E) : Prop := C.Nonempty ∧ IsClosed C ∧ Convex ℝ C

lemma CCN_of_cone {K : Set E} (hK : IsClosedConvexCone K) : CCN K :=
  ⟨hK.1, hK.2.1, hK.2.2.1⟩

lemma proj_spec {C : Set E} (hC : CCN C) (w : E) : IsProj C w (proj C w) := by
  have hex : ∃ v, IsProj C w v := by
    obtain ⟨v, hv, heq⟩ := exists_norm_eq_iInf_of_complete_convex hC.1
      hC.2.1.isComplete hC.2.2 w
    refine ⟨v, hv, fun u hu => ?_⟩
    rw [heq]
    exact ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩ (⟨u, hu⟩ : C)
  unfold proj
  rw [dif_pos hex]
  exact hex.choose_spec

lemma proj_mem {C : Set E} (hC : CCN C) (w : E) : proj C w ∈ C := (proj_spec hC w).1

lemma var_ineq {C : Set E} (hC : CCN C) (w : E) :
    ∀ u ∈ C, ⟪w - proj C w, u - proj C w⟫_ℝ ≤ 0 := by
  have h := proj_spec hC w
  have hne : Nonempty C := ⟨⟨_, h.1⟩⟩
  have heq : ‖w - proj C w‖ = ⨅ u : C, ‖w - u‖ := by
    apply le_antisymm
    · exact le_ciInf (fun u => h.2 u u.2)
    · exact ciInf_le ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩ (⟨_, h.1⟩ : C)
  exact (norm_eq_iInf_iff_real_inner_le_zero hC.2.2 h.1).1 heq

lemma proj_eq_of_var {C : Set E} (hC : CCN C) (w q : E) (hq : q ∈ C)
    (hv : ∀ u ∈ C, ⟪w - q, u - q⟫_ℝ ≤ 0) : proj C w = q := by
  set p := proj C w
  have h1 : ⟪w - p, q - p⟫_ℝ ≤ 0 := var_ineq hC w q hq
  have h2 : ⟪w - q, p - q⟫_ℝ ≤ 0 := hv p (proj_mem hC w)
  have hsum : ⟪q - p, q - p⟫_ℝ ≤ 0 := by
    have : q - p = (w - p) - (w - q) := by abel
    have hpq : p - q = -(q - p) := by abel
    rw [hpq, inner_neg_right] at h2
    calc ⟪q - p, q - p⟫_ℝ = ⟪w - p, q - p⟫_ℝ - ⟪w - q, q - p⟫_ℝ := by
          rw [this, inner_sub_left]
      _ ≤ 0 := by linarith
  rw [real_inner_self_eq_norm_sq] at hsum
  have : ‖q - p‖ = 0 := by nlinarith [norm_nonneg (q - p)]
  rw [norm_eq_zero, sub_eq_zero] at this
  exact this.symm

lemma proj_nonexp {C : Set E} (hC : CCN C) (v w : E) :
    ‖proj C w - proj C v‖ ≤ ‖w - v‖ := by
  set P := proj C w with hP
  set Q := proj C v with hQ
  have h1 : ⟪w - P, Q - P⟫_ℝ ≤ 0 := var_ineq hC w Q (proj_mem hC v)
  have h2 : ⟪v - Q, P - Q⟫_ℝ ≤ 0 := var_ineq hC v P (proj_mem hC w)
  have hQP : Q - P = -(P - Q) := by abel
  rw [hQP, inner_neg_right] at h1
  have hwv : w - v = (w - P) - (v - Q) + (P - Q) := by abel
  have key : ‖P - Q‖ ^ 2 ≤ ⟪w - v, P - Q⟫_ℝ := by
    rw [hwv, inner_add_left, inner_sub_left, real_inner_self_eq_norm_sq]
    linarith
  have hcs : ⟪w - v, P - Q⟫_ℝ ≤ ‖w - v‖ * ‖P - Q‖ := real_inner_le_norm _ _
  have hn := norm_nonneg (P - Q)
  have hn2 := norm_nonneg (w - v)
  nlinarith

lemma proj_lipschitz {C : Set E} (hC : CCN C) : LipschitzWith 1 (proj C) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  exact proj_nonexp hC b a

lemma proj_continuous {C : Set E} (hC : CCN C) : Continuous (proj C) :=
  (proj_lipschitz hC).continuous

/-! ### polar cone -/

lemma polar_CCN (K : Set E) : CCN (polarCone K) := by
  refine ⟨⟨0, fun x _ => by simp⟩, ?_, ?_⟩
  · have : polarCone K = ⋂ x ∈ K, {y : E | ⟪x, y⟫_ℝ ≤ 0} := by
      ext y; simp [polarCone]
    rw [this]
    refine isClosed_biInter fun x _ => ?_
    exact isClosed_le (continuous_const.inner continuous_id) continuous_const
  · intro a ha b hb s t hs ht hst x hx
    have h1 := ha x hx
    have h2 := hb x hx
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    nlinarith

lemma polar_smul {K : Set E} {y : E} (hy : y ∈ polarCone K) {t : ℝ} (ht : 0 ≤ t) :
    t • y ∈ polarCone K := by
  intro x hx
  rw [real_inner_smul_right]
  have := hy x hx
  nlinarith

lemma cone_add {K : Set E} (hK : IsClosedConvexCone K) {a b : E} (ha : a ∈ K) (hb : b ∈ K) :
    a + b ∈ K := by
  have h2a := hK.2.2.2 a ha 2 (by norm_num)
  have h2b := hK.2.2.2 b hb 2 (by norm_num)
  have := hK.2.2.1 h2a h2b (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num)
  convert this using 1
  rw [smul_smul, smul_smul]; norm_num

lemma cone_zero {K : Set E} (hK : IsClosedConvexCone K) : (0 : E) ∈ K := by
  obtain ⟨a, ha⟩ := hK.1
  have := hK.2.2.2 a ha 0 le_rfl
  simpa using this

/-- Moreau decomposition, part 1: orthogonality and polar membership. -/
lemma moreau_orth {K : Set E} (hK : IsClosedConvexCone K) (w : E) :
    ⟪w - proj K w, proj K w⟫_ℝ = 0 := by
  set p := proj K w
  have hp : p ∈ K := proj_mem (CCN_of_cone hK) w
  have h0 := var_ineq (CCN_of_cone hK) w 0 (cone_zero hK)
  have h2 := var_ineq (CCN_of_cone hK) w (2 • p) (hK.2.2.2 p hp 2 (by norm_num))
  rw [zero_sub, inner_neg_right] at h0
  have : (2:ℝ) • p - p = p := by rw [two_smul]; abel
  rw [two_smul] at h2
  have h2' : ⟪w - p, p⟫_ℝ ≤ 0 := by
    have hh : p + p - p = p := by abel
    rw [hh] at h2; exact h2
  linarith

lemma moreau_polar_mem {K : Set E} (hK : IsClosedConvexCone K) (w : E) :
    w - proj K w ∈ polarCone K := by
  set p := proj K w
  have hp : p ∈ K := proj_mem (CCN_of_cone hK) w
  intro x hx
  have h := var_ineq (CCN_of_cone hK) w (p + x) (cone_add hK hp hx)
  rw [add_sub_cancel_left] at h
  rw [real_inner_comm]; exact h

lemma moreau {K : Set E} (hK : IsClosedConvexCone K) (w : E) :
    proj (polarCone K) w = w - proj K w := by
  apply proj_eq_of_var (polar_CCN K) w _ (moreau_polar_mem hK w)
  intro v hv
  have hp : proj K w ∈ K := proj_mem (CCN_of_cone hK) w
  have e : w - (w - proj K w) = proj K w := by abel
  rw [e, inner_sub_right]
  have h1 := hv _ hp
  have h2 := moreau_orth hK w
  rw [real_inner_comm] at h2
  linarith

lemma proj_polar_of_mem {K : Set E} (hK : IsClosedConvexCone K) {g : E} (hg : g ∈ K) :
    proj (polarCone K) g = 0 := by
  apply proj_eq_of_var (polar_CCN K) g 0 (fun x _ => by simp)
  intro u hu
  simpa using hu g hg

/-! ### derivative of the squared distance -/

lemma dsq_upper {C : Set E} (hC : CCN C) (w h : E) :
    ‖(w + h) - proj C (w + h)‖ ^ 2 - ‖w - proj C w‖ ^ 2
      - 2 * ⟪w - proj C w, h⟫_ℝ ≤ ‖h‖ ^ 2 := by
  have h1 := (proj_spec hC (w + h)).2 (proj C w) (proj_mem hC w)
  have e : w + h - proj C w = (w - proj C w) + h := by abel
  rw [e] at h1
  have h1' := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [norm_add_sq_real] at h1'
  linarith

lemma dsq_lower {C : Set E} (hC : CCN C) (w h : E) :
    -‖h‖ ^ 2 ≤ ‖(w + h) - proj C (w + h)‖ ^ 2 - ‖w - proj C w‖ ^ 2
      - 2 * ⟪w - proj C w, h⟫_ℝ := by
  set a := w - proj C w
  set b := (w + h) - proj C (w + h)
  have h1 := (proj_spec hC w).2 (proj C (w + h)) (proj_mem hC (w + h))
  have e : w - proj C (w + h) = b - h := by simp only [b]; abel
  rw [e] at h1
  have h1' : ‖a‖ ^ 2 ≤ ‖b - h‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [norm_sub_sq_real b h] at h1'
  -- ⟪b - a, h⟫ ≥ 0
  have hba : b - a = h - (proj C (w + h) - proj C w) := by simp only [a, b]; abel
  have hne := proj_nonexp hC w (w + h)
  have e2 : w + h - w = h := by abel
  rw [e2] at hne
  have hcs : ⟪proj C (w + h) - proj C w, h⟫_ℝ ≤ ‖h‖ * ‖h‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hne (norm_nonneg _))
  have hge : 0 ≤ ⟪b - a, h⟫_ℝ := by
    rw [hba, inner_sub_left, real_inner_self_eq_norm_sq]; nlinarith
  rw [inner_sub_left] at hge
  nlinarith

lemma hasFDerivAt_dsq {C : Set E} (hC : CCN C) (w : E) :
    HasFDerivAt (fun v => ‖v - proj C v‖ ^ 2) ((2:ℝ) • innerSL ℝ (w - proj C w)) w := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_norm_pow_id (n := 2)
    (by norm_num))
  refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun h => ?_)
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, innerSL_apply_apply, smul_eq_mul, one_mul,
    Real.norm_eq_abs, norm_pow, abs_norm]
  rw [abs_le]
  exact ⟨dsq_lower hC w h, dsq_upper hC w h⟩

lemma hasFDerivAt_polar_sq {K : Set E} (hK : IsClosedConvexCone K) (w : E) :
    HasFDerivAt (fun v => ‖proj (polarCone K) v‖ ^ 2)
      ((2:ℝ) • innerSL ℝ (proj (polarCone K) w)) w := by
  have e : (fun v => ‖proj (polarCone K) v‖ ^ 2) = fun v => ‖v - proj K v‖ ^ 2 := by
    funext v; rw [moreau hK]
  rw [e, moreau hK]
  exact hasFDerivAt_dsq (CCN_of_cone hK) w


/-! ### chain rule and gradients -/

variable {n : ℕ}


lemma innerSL_comp_eq_toDual (A : (EuclideanSpace ℝ (Fin n)) →L[ℝ] E) (v : E) :
    (innerSL ℝ v).comp A = InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (ContinuousLinearMap.adjoint A v) := by
  ext z
  simp [ContinuousLinearMap.adjoint_inner_left]

lemma hasFDerivAt_polar_sq_comp {K : Set E} (hK : IsClosedConvexCone K) (F : (EuclideanSpace ℝ (Fin n)) → E) (x : (EuclideanSpace ℝ (Fin n)))
    (hF : DifferentiableAt ℝ F x) :
    HasFDerivAt (fun y => ‖proj (polarCone K) (F y)‖ ^ 2)
      (((2:ℝ) • innerSL ℝ (proj (polarCone K) (F x))).comp (fderiv ℝ F x)) x :=
  (hasFDerivAt_polar_sq hK (F x)).comp x hF.hasFDerivAt

lemma augLag_grad {f : (EuclideanSpace ℝ (Fin n)) → ℝ} (hf : ContDiff ℝ 1 f) {G : (EuclideanSpace ℝ (Fin n)) → E} (hG : ContDiff ℝ 1 G)
    {K : Set E} (hK : IsClosedConvexCone K) (ρ : ℝ) (Λ : E) (x : (EuclideanSpace ℝ (Fin n))) :
    HasGradientAt (fun y => augLag f G K ρ y Λ)
      (gradient f x + adjD G x (ρ • proj (polarCone K) (G x + ρ⁻¹ • Λ))) x := by
  have hfd : HasGradientAt f (gradient f x) x :=
    ((hf.differentiable one_ne_zero) x).hasGradientAt
  have hGd : DifferentiableAt ℝ (fun y => G y + ρ⁻¹ • Λ) x :=
    ((hG.differentiable one_ne_zero) x).add_const _
  have hh := hasFDerivAt_polar_sq_comp hK (fun y => G y + ρ⁻¹ • Λ) x hGd
  have hsum := hfd.hasFDerivAt.add ((hh.sub_const (‖ρ⁻¹ • Λ‖ ^ 2)).const_mul (ρ / 2))
  rw [hasGradientAt_iff_hasFDerivAt]
  unfold augLag
  refine hsum.congr_fderiv ?_
  have hfG : fderiv ℝ (fun y => G y + ρ⁻¹ • Λ) x = fderiv ℝ G x := by
    rw [fderiv_add_const]
  rw [hfG]
  ext z
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, innerSL_apply_apply, smul_eq_mul,
    InnerProductSpace.toDual_apply_apply, inner_add_left, adjD,
    ContinuousLinearMap.adjoint_inner_left, real_inner_smul_left]
  ring

lemma psi_hasFDerivAt {G : (EuclideanSpace ℝ (Fin n)) → E} (hG : ContDiff ℝ 1 G) {K : Set E} (hK : IsClosedConvexCone K)
    (y : (EuclideanSpace ℝ (Fin n))) :
    HasFDerivAt (Psi K G) ((1/2 : ℝ) • (((2:ℝ) • innerSL ℝ (proj (polarCone K) (G y))).comp
      (fderiv ℝ G y))) y := by
  have hh := hasFDerivAt_polar_sq_comp hK G y ((hG.differentiable one_ne_zero) y)
  have := hh.const_mul (1/2 : ℝ)
  exact this

lemma psi_fderiv_norm_le {G : (EuclideanSpace ℝ (Fin n)) → E} (hG : ContDiff ℝ 1 G) {K : Set E}
    (hK : IsClosedConvexCone K) (y : (EuclideanSpace ℝ (Fin n))) :
    ‖fderiv ℝ (Psi K G) y‖ ≤ ‖adjD G y (proj (polarCone K) (G y))‖ := by
  rw [(psi_hasFDerivAt hG hK y).fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, innerSL_apply_apply, smul_eq_mul]
  have e : 1 / 2 * (2 * ⟪proj (polarCone K) (G y), (fderiv ℝ G y) z⟫_ℝ)
      = ⟪adjD G y (proj (polarCone K) (G y)), z⟫_ℝ := by
    simp only [adjD, ContinuousLinearMap.adjoint_inner_left]; ring
  rw [e, Real.norm_eq_abs]
  exact abs_real_inner_le_norm _ _

lemma norm_adjD_le (G : (EuclideanSpace ℝ (Fin n)) → E) (y : (EuclideanSpace ℝ (Fin n))) (v : E) :
    ‖adjD G y v‖ ≤ ‖fderiv ℝ G y‖ * ‖v‖ := by
  unfold adjD
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  rw [LinearIsometryEquiv.norm_map]

lemma psi_at_feas {G : (EuclideanSpace ℝ (Fin n)) → E} {K : Set E} (hK : IsClosedConvexCone K) {xbar : (EuclideanSpace ℝ (Fin n))}
    (hfeas : G xbar ∈ K) : Psi K G xbar = 0 := by
  simp [Psi, proj_polar_of_mem hK hfeas]

/-! ### the run -/

section run

variable {f : (EuclideanSpace ℝ (Fin n)) → ℝ} {G : (EuclideanSpace ℝ (Fin n)) → E} {K : Set E} {ε : ℕ → ℝ} {B : Set E} {τ σ ρ₀ : ℝ}
  {x : ℕ → (EuclideanSpace ℝ (Fin n))} {Λhat : ℕ → E} {ρ : ℕ → ℝ}

lemma rho_pos (hrun : IsALRun f G K ε B τ σ ρ₀ x Λhat ρ) : ∀ k, 0 < ρ k := by
  intro k
  induction k with
  | zero => rw [hrun.rho_zero]; exact hrun.rho0_pos
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [hrun.step4_zero]; exact ih
    · by_cases ht : ‖Vk K G ρ x Λhat k‖ ≤ σ * ‖Vk K G ρ x Λhat (k - 1)‖
      · rw [hrun.step4_keep k hk ht]; exact ih
      · have := hrun.step4_increase k hk ht
        have h1 := hrun.one_lt_tau
        nlinarith

lemma rho_succ_ge (hrun : IsALRun f G K ε B τ σ ρ₀ x Λhat ρ) : ∀ k, ρ k ≤ ρ (k + 1) := by
  intro k
  have ih := rho_pos hrun k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [hrun.step4_zero]
  · by_cases ht : ‖Vk K G ρ x Λhat k‖ ≤ σ * ‖Vk K G ρ x Λhat (k - 1)‖
    · rw [hrun.step4_keep k hk ht]
    · have := hrun.step4_increase k hk ht
      have h1 := hrun.one_lt_tau
      nlinarith

lemma rho_mono (hrun : IsALRun f G K ε B τ σ ρ₀ x Λhat ρ) : Monotone ρ :=
  monotone_nat_of_le_succ (rho_succ_ge hrun)

lemma Λhat_bdd (hrun : IsALRun f G K ε B τ σ ρ₀ x Λhat ρ) : ∃ R, 0 ≤ R ∧ ∀ k, ‖Λhat k‖ ≤ R := by
  obtain ⟨R, hR⟩ := hrun.B_compact.isBounded.exists_norm_le
  exact ⟨max R 0, le_max_right _ _, fun k => (hR _ (hrun.Λhat_mem k)).trans (le_max_left _ _)⟩

lemma mult_mem (hrun : IsALRun f G K ε B τ σ ρ₀ x Λhat ρ) (k : ℕ) :
    mult K G ρ x Λhat k ∈ polarCone K :=
  polar_smul (proj_mem (polar_CCN K) _) (rho_pos hrun k).le

lemma step1' (hf : ContDiff ℝ 1 f) (hG : ContDiff ℝ 1 G) (hK : IsClosedConvexCone K)
    (hrun : IsALRun f G K ε B τ σ ρ₀ x Λhat ρ) (k : ℕ) :
    ‖gradient f (x k) + adjD G (x k) (mult K G ρ x Λhat k)‖ ≤ ε k := by
  have := hrun.step1 k
  rw [(augLag_grad hf hG hK (ρ k) (Λhat k) (x k)).gradient] at this
  exact this

lemma dichotomy (hrun : IsALRun f G K ε B τ σ ρ₀ x Λhat ρ) :
    Tendsto ρ atTop atTop ∨
      ∃ k₀ : ℕ, (∀ k > k₀, ρ k = ρ k₀) ∧
        Tendsto (fun k => ‖Vk K G ρ x Λhat k‖) atTop (𝓝 0) := by
  have hmono := rho_mono hrun
  have hpos := rho_pos hrun
  have hτ := hrun.one_lt_tau
  by_cases hT : Tendsto ρ atTop atTop
  · exact Or.inl hT
  right
  rw [tendsto_atTop_atTop_iff_of_monotone hmono] at hT
  push Not at hT
  obtain ⟨C, hC⟩ := hT
  -- eventually no increase
  have hev : ∃ k₀, 1 ≤ k₀ ∧ ∀ k ≥ k₀, ρ (k + 1) = ρ k := by
    by_contra hcon
    push Not at hcon
    have hgrow : ∀ m : ℕ, ∃ k, τ ^ m * ρ 0 ≤ ρ k := by
      intro m
      induction m with
      | zero => exact ⟨0, by simp⟩
      | succ m ih =>
        obtain ⟨k, hk⟩ := ih
        obtain ⟨k', hk'1, hk'2⟩ := hcon (max k 1) (le_max_right _ _)
        have hk1 : 1 ≤ k' := le_trans (le_max_right _ _) hk'1
        have hkk : k ≤ k' := le_trans (le_max_left _ _) hk'1
        have ht : ¬ (‖Vk K G ρ x Λhat k'‖ ≤ σ * ‖Vk K G ρ x Λhat (k' - 1)‖) :=
          fun h => hk'2 (hrun.step4_keep k' hk1 h)
        have hinc := hrun.step4_increase k' hk1 ht
        refine ⟨k' + 1, ?_⟩
        have := hmono hkk
        rw [pow_succ]
        nlinarith
    have htend : Tendsto (fun m : ℕ => τ ^ m * ρ 0) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt hτ).atTop_mul_const (hpos 0)
    obtain ⟨m, hm⟩ := (htend.eventually_gt_atTop C).exists
    obtain ⟨k, hk⟩ := hgrow m
    exact absurd (hC k) (not_lt.mpr (le_of_lt (lt_of_lt_of_le hm hk)))
  obtain ⟨k₀, hk₀1, hk₀⟩ := hev
  refine ⟨k₀, ?_, ?_⟩
  · intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
      · rw [hk₀ k (le_of_lt h), ih h]
      · subst h; exact hk₀ _ le_rfl
  · have htest : ∀ k ≥ k₀, ‖Vk K G ρ x Λhat k‖ ≤ σ * ‖Vk K G ρ x Λhat (k - 1)‖ := by
      intro k hk
      by_contra ht
      have := hrun.step4_increase k (le_trans hk₀1 hk) ht
      rw [hk₀ k hk] at this
      have := hpos k
      nlinarith
    have hgeo : ∀ m, ‖Vk K G ρ x Λhat (k₀ + m)‖ ≤ σ ^ m * ‖Vk K G ρ x Λhat k₀‖ := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have := htest (k₀ + (m + 1)) (by omega)
        have e : k₀ + (m + 1) - 1 = k₀ + m := by omega
        rw [e] at this
        rw [pow_succ]
        have hs := hrun.sigma_pos
        calc ‖Vk K G ρ x Λhat (k₀ + (m + 1))‖ ≤ σ * ‖Vk K G ρ x Λhat (k₀ + m)‖ := this
          _ ≤ σ * (σ ^ m * ‖Vk K G ρ x Λhat k₀‖) := by gcongr
          _ = σ ^ m * σ * ‖Vk K G ρ x Λhat k₀‖ := by ring
    rw [← tendsto_add_atTop_iff_nat k₀]
    have hlim : Tendsto (fun m : ℕ => σ ^ m * ‖Vk K G ρ x Λhat k₀‖) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hrun.sigma_pos.le hrun.sigma_lt_one).mul_const
        ‖Vk K G ρ x Λhat k₀‖
      simpa using this
    refine squeeze_zero (fun m => norm_nonneg _) (fun m => ?_) hlim
    simpa [add_comm] using hgeo m

end run


/-! ### pointwise estimates -/

section pointwise

variable {K : Set E}

lemma est_I1 (r : ℝ) (hr : 0 < r) (g lam : E) :
    ‖proj (polarCone K) (g + r⁻¹ • lam) - proj (polarCone K) g‖ ≤ r⁻¹ * ‖lam‖ := by
  refine (proj_nonexp (polar_CCN K) g (g + r⁻¹ • lam)).trans (le_of_eq ?_)
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]

lemma est_I2 (hK : IsClosedConvexCone K) (r : ℝ) (g lam : E) :
    ⟪r • proj (polarCone K) (g + r⁻¹ • lam), proj K g⟫_ℝ
      = r * ⟪proj (polarCone K) (g + r⁻¹ • lam), proj K g - proj K (g + r⁻¹ • lam)⟫_ℝ := by
  set w := g + r⁻¹ • lam
  have h0 : ⟪proj (polarCone K) w, proj K w⟫_ℝ = 0 := by
    rw [moreau hK]; exact moreau_orth hK w
  rw [inner_sub_right, h0, sub_zero, real_inner_smul_left]

lemma est_I3 (hK : IsClosedConvexCone K) (r : ℝ) (hr : 0 < r) (g lam : E) :
    |⟪r • proj (polarCone K) (g + r⁻¹ • lam), proj K g⟫_ℝ|
      ≤ (‖proj (polarCone K) g‖ + r⁻¹ * ‖lam‖) * ‖lam‖ := by
  rw [est_I2 hK, abs_mul, abs_of_pos hr]
  set w := g + r⁻¹ • lam
  have h1 := abs_real_inner_le_norm (proj (polarCone K) w) (proj K g - proj K w)
  have h2 : ‖proj K g - proj K w‖ ≤ r⁻¹ * ‖lam‖ := by
    refine (proj_nonexp (CCN_of_cone hK) w g).trans (le_of_eq ?_)
    rw [show g - w = -(r⁻¹ • lam) by simp [w], norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  have h3 : ‖proj (polarCone K) w‖ ≤ ‖proj (polarCone K) g‖ + r⁻¹ * ‖lam‖ := by
    have := est_I1 (K := K) r hr g lam
    calc ‖proj (polarCone K) w‖
        = ‖(proj (polarCone K) w - proj (polarCone K) g) + proj (polarCone K) g‖ := by
          rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ r⁻¹ * ‖lam‖ + ‖proj (polarCone K) g‖ := by gcongr
      _ = _ := by ring
  have hn := norm_nonneg (proj (polarCone K) w)
  have hl := norm_nonneg lam
  have hri : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  calc r * |⟪proj (polarCone K) w, proj K g - proj K w⟫_ℝ|
      ≤ r * (‖proj (polarCone K) w‖ * (r⁻¹ * ‖lam‖)) := by
        gcongr; exact h1.trans (mul_le_mul_of_nonneg_left h2 hn)
    _ = ‖proj (polarCone K) w‖ * ‖lam‖ * (r * r⁻¹) := by ring
    _ = ‖proj (polarCone K) w‖ * ‖lam‖ := by rw [hri, mul_one]
    _ ≤ _ := by gcongr

lemma est_I4 (hK : IsClosedConvexCone K) (r : ℝ) (hr : 0 < r) (g lam : E) :
    |⟪r • proj (polarCone K) (g + r⁻¹ • lam), proj K g⟫_ℝ|
      ≤ (‖lam‖ + r * ‖r⁻¹ • lam - proj (polarCone K) (g + r⁻¹ • lam)‖) *
        (‖proj (polarCone K) g‖ + ‖r⁻¹ • lam - proj (polarCone K) (g + r⁻¹ • lam)‖) := by
  rw [est_I2 hK, ← real_inner_smul_left]
  set w := g + r⁻¹ • lam
  set V := r⁻¹ • lam - proj (polarCone K) w
  set p := proj (polarCone K) g
  have hdiff : proj K g - proj K w = -(p + V) := by
    have e1 : proj K g = g - p := by simp only [p]; rw [moreau hK]; abel
    have e2 : proj K w = w - proj (polarCone K) w := by rw [moreau hK]; abel
    rw [e1, e2]; simp only [V, w]; abel
  have hrw : r • proj (polarCone K) w = lam - r • V := by
    simp only [V, smul_sub, smul_smul]
    rw [mul_inv_cancel₀ hr.ne', one_smul]; abel
  rw [hrw, hdiff]
  have h1 := abs_real_inner_le_norm (lam - r • V) (-(p + V))
  refine h1.trans ?_
  rw [norm_neg]
  gcongr
  · refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  · exact norm_add_le _ _

lemma est_I5 (r : ℝ) (hr : 0 < r) (g lam : E) :
    |⟪r • proj (polarCone K) (g + r⁻¹ • lam), proj (polarCone K) g⟫_ℝ|
      ≤ r * ‖proj (polarCone K) g‖ ^ 2 + ‖lam‖ * ‖proj (polarCone K) g‖ := by
  set Pw := proj (polarCone K) (g + r⁻¹ • lam)
  set p := proj (polarCone K) g
  have e : ⟪r • Pw, p⟫_ℝ = r * ‖p‖ ^ 2 + r * ⟪Pw - p, p⟫_ℝ := by
    rw [real_inner_smul_left, inner_sub_left, real_inner_self_eq_norm_sq]; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have h1 := est_I1 (K := K) r hr g lam
  have h2 := abs_real_inner_le_norm (Pw - p) p
  have hri : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  rw [abs_mul, abs_mul, abs_of_pos hr, abs_of_nonneg (sq_nonneg _)]
  refine add_le_add (le_refl _) ?_
  calc r * |⟪Pw - p, p⟫_ℝ| ≤ r * ((r⁻¹ * ‖lam‖) * ‖p‖) := by
        gcongr; exact h2.trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
    _ = ‖lam‖ * ‖p‖ * (r * r⁻¹) := by ring
    _ = _ := by rw [hri, mul_one]

end pointwise


/-! ### sequence-level limits -/

section limits

variable {f : (EuclideanSpace ℝ (Fin n)) → ℝ} {G : (EuclideanSpace ℝ (Fin n)) → E} {K : Set E}
  {ε : ℕ → ℝ} {B : Set E} {τ σ ρ₀ : ℝ}
  {x : ℕ → (EuclideanSpace ℝ (Fin n))} {Λhat : ℕ → E} {ρ : ℕ → ℝ}

lemma grad_tendsto (hf : ContDiff ℝ 1 f) (hG : ContDiff ℝ 1 G) (hK : IsClosedConvexCone K)
    (hrun : IsALRun f G K ε B τ σ ρ₀ x Λhat ρ) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Tendsto (fun j => gradient f (x (φ j)) + adjD G (x (φ j)) (mult K G ρ x Λhat (φ j)))
      atTop (𝓝 0) :=
  squeeze_zero_norm (fun j => step1' hf hG hK hrun (φ j))
    (hrun.eps_tendsto.comp hφ.tendsto_atTop)

lemma p_tendsto (hG : ContDiff ℝ 1 G) (hK : IsClosedConvexCone K)
    {xbar : EuclideanSpace ℝ (Fin n)} (hfeas : G xbar ∈ K) {φ : ℕ → ℕ}
    (hx : Tendsto (x ∘ φ) atTop (𝓝 xbar)) :
    Tendsto (fun j => proj (polarCone K) (G (x (φ j)))) atTop (𝓝 0) := by
  have := ((proj_continuous (polar_CCN K)).tendsto (G xbar)).comp
    ((hG.continuous.tendsto xbar).comp hx)
  rw [proj_polar_of_mem hK hfeas] at this
  exact this

lemma PiK_tendsto (hf : ContDiff ℝ 1 f) (hG : ContDiff ℝ 1 G) (hK : IsClosedConvexCone K)
    (hrun : IsALRun f G K ε B τ σ ρ₀ x Λhat ρ)
    {xbar : EuclideanSpace ℝ (Fin n)} (hfeas : G xbar ∈ K) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hx : Tendsto (x ∘ φ) atTop (𝓝 xbar)) :
    Tendsto (fun j => ⟪mult K G ρ x Λhat (φ j), proj K (G (x (φ j)))⟫_ℝ) atTop (𝓝 0) := by
  obtain ⟨R, hR0, hR⟩ := Λhat_bdd hrun
  have hp := p_tendsto hG hK hfeas hx
  have hpn : Tendsto (fun j => ‖proj (polarCone K) (G (x (φ j)))‖) atTop (𝓝 0) := by
    simpa using hp.norm
  rcases dichotomy hrun with hT | ⟨k₀, hconst, hV⟩
  · have hinv : Tendsto (fun j => (ρ (φ j))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (hT.comp hφ.tendsto_atTop)
    have hb : Tendsto (fun j => (‖proj (polarCone K) (G (x (φ j)))‖ + (ρ (φ j))⁻¹ * R) * R)
        atTop (𝓝 0) := by
      have := ((hpn.add (hinv.mul_const R)).mul_const R)
      simpa using this
    refine squeeze_zero_norm (fun j => ?_) hb
    rw [Real.norm_eq_abs]
    have hr := rho_pos hrun (φ j)
    refine (est_I3 hK (ρ (φ j)) hr (G (x (φ j))) (Λhat (φ j))).trans ?_
    have := hR (φ j)
    have hi := inv_pos.mpr hr
    gcongr
  · have hVφ : Tendsto (fun j => ‖Vk K G ρ x Λhat (φ j)‖) atTop (𝓝 0) :=
      hV.comp hφ.tendsto_atTop
    have hb : Tendsto (fun j => (R + ρ k₀ * ‖Vk K G ρ x Λhat (φ j)‖) *
        (‖proj (polarCone K) (G (x (φ j)))‖ + ‖Vk K G ρ x Λhat (φ j)‖)) atTop (𝓝 0) := by
      have := ((tendsto_const_nhds (x := R)).add (hVφ.const_mul (ρ k₀))).mul (hpn.add hVφ)
      simpa using this
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hφ.tendsto_atTop.eventually_gt_atTop k₀] with j hj
    rw [Real.norm_eq_abs]
    have hr := rho_pos hrun (φ j)
    have h4 := est_I4 hK (ρ (φ j)) hr (G (x (φ j))) (Λhat (φ j))
    have hm : mult K G ρ x Λhat (φ j) = ρ (φ j) • proj (polarCone K)
        (G (x (φ j)) + (ρ (φ j))⁻¹ • Λhat (φ j)) := rfl
    have hv : Vk K G ρ x Λhat (φ j) = (ρ (φ j))⁻¹ • Λhat (φ j) - proj (polarCone K)
        (G (x (φ j)) + (ρ (φ j))⁻¹ • Λhat (φ j)) := rfl
    rw [hm, hv]
    refine h4.trans ?_
    have := hR (φ j)
    rw [hconst _ hj]
    gcongr

lemma gradient_continuous (hf : ContDiff ℝ 1 f) : Continuous (gradient f) := by
  have : gradient f = fun y => (InnerProductSpace.toDual ℝ _).symm (fderiv ℝ f y) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ _).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)

lemma rho_infeas_gen (hf : ContDiff ℝ 1 f) (hG : ContDiff ℝ 1 G) (hK : IsClosedConvexCone K)
    (hrun : IsALRun f G K ε B τ σ ρ₀ x Λhat ρ)
    {xbar : EuclideanSpace ℝ (Fin n)} (hfeas : G xbar ∈ K) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hx : Tendsto (x ∘ φ) atTop (𝓝 xbar)) (hL : GenLojasiewicz (Psi K G) xbar) :
    Tendsto (fun j => ρ (φ j) * ‖proj (polarCone K) (G (x (φ j)))‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨R, hR0, hR⟩ := Λhat_bdd hrun
  obtain ⟨δ, hδ, ψ, -, hψ, hineq⟩ := hL
  have hψx : Tendsto (fun j => |ψ (x (φ j))|) atTop (𝓝 0) := by
    have := (hψ.comp hx).abs
    simpa using this
  have hgf : Tendsto (fun j => ‖gradient f (x (φ j))‖) atTop (𝓝 ‖gradient f xbar‖) :=
    (((gradient_continuous hf).tendsto xbar).comp hx).norm
  have hdG : Tendsto (fun j => ‖fderiv ℝ G (x (φ j))‖) atTop (𝓝 ‖fderiv ℝ G xbar‖) :=
    (((hG.continuous_fderiv one_ne_zero).tendsto xbar).comp hx).norm
  have hεφ : Tendsto (fun j => ε (φ j)) atTop (𝓝 0) := hrun.eps_tendsto.comp hφ.tendsto_atTop
  have hb : Tendsto (fun j => 2 * |ψ (x (φ j))| *
      (ε (φ j) + ‖gradient f (x (φ j))‖ + ‖fderiv ℝ G (x (φ j))‖ * R)) atTop (𝓝 0) := by
    have := (hψx.const_mul 2).mul ((hεφ.add hgf).add (hdG.mul_const R))
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun j => ?_) ?_ hb
  · exact mul_nonneg (rho_pos hrun _).le (sq_nonneg _)
  filter_upwards [hx.eventually (Metric.ball_mem_nhds xbar hδ)] with j hj
  simp only [Function.comp_apply] at hj
  set X := x (φ j)
  set r := ρ (φ j)
  set lam := Λhat (φ j)
  set p := proj (polarCone K) (G X)
  set A := fderiv ℝ G X
  have hr : 0 < r := rho_pos hrun _
  have h1 := hineq X hj
  rw [psi_at_feas hK hfeas, sub_zero] at h1
  have hPsi : Psi K G X = 1 / 2 * ‖p‖ ^ 2 := rfl
  rw [hPsi, abs_of_nonneg (by positivity)] at h1
  have h2 := psi_fderiv_norm_le hG hK X
  have h3 : 1 / 2 * ‖p‖ ^ 2 ≤ |ψ X| * ‖adjD G X p‖ :=
    h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)))
  -- bound r * ‖A† p‖
  have hstep := step1' hf hG hK hrun (φ j)
  set L := mult K G ρ x Λhat (φ j)
  have hL : L = r • proj (polarCone K) (G X + r⁻¹ • lam) := rfl
  have hdiff : ‖r • p - L‖ ≤ R := by
    rw [hL, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have := est_I1 (K := K) r hr (G X) lam
    rw [norm_sub_rev] at this
    calc r * ‖p - proj (polarCone K) (G X + r⁻¹ • lam)‖ ≤ r * (r⁻¹ * ‖lam‖) := by gcongr
      _ = ‖lam‖ := by field_simp
      _ ≤ R := hR _
  have hA : r * ‖adjD G X p‖ ≤ ε (φ j) + ‖gradient f X‖ + ‖A‖ * R := by
    have e : r * ‖adjD G X p‖ = ‖adjD G X (r • p)‖ := by
      rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have e2 : adjD G X (r • p) = (gradient f X + adjD G X L) - gradient f X
        + adjD G X (r • p - L) := by
      rw [map_sub]; abel
    rw [e, e2]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans (add_le_add hstep le_rfl)) ?_
    refine (norm_adjD_le G X _).trans ?_
    exact mul_le_mul_of_nonneg_left hdiff (norm_nonneg _)
  have hψ0 := abs_nonneg (ψ X)
  calc r * ‖p‖ ^ 2 ≤ r * (2 * (|ψ X| * ‖adjD G X p‖)) := by gcongr; linarith
    _ = 2 * |ψ X| * (r * ‖adjD G X p‖) := by ring
    _ ≤ _ := by gcongr

lemma PiKpolar_tendsto (hf : ContDiff ℝ 1 f) (hG : ContDiff ℝ 1 G) (hK : IsClosedConvexCone K)
    (hrun : IsALRun f G K ε B τ σ ρ₀ x Λhat ρ)
    {xbar : EuclideanSpace ℝ (Fin n)} (hfeas : G xbar ∈ K) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hx : Tendsto (x ∘ φ) atTop (𝓝 xbar)) (hL : GenLojasiewicz (Psi K G) xbar) :
    Tendsto (fun j => ⟪mult K G ρ x Λhat (φ j), proj (polarCone K) (G (x (φ j)))⟫_ℝ)
      atTop (𝓝 0) := by
  obtain ⟨R, hR0, hR⟩ := Λhat_bdd hrun
  have hpn : Tendsto (fun j => ‖proj (polarCone K) (G (x (φ j)))‖) atTop (𝓝 0) := by
    simpa using (p_tendsto hG hK hfeas hx).norm
  have hb := (rho_infeas_gen hf hG hK hrun hfeas hφ hx hL).add (hpn.const_mul R)
  rw [mul_zero, add_zero] at hb
  refine squeeze_zero_norm (fun j => ?_) hb
  rw [Real.norm_eq_abs]
  refine (est_I5 (K := K) (ρ (φ j)) (rho_pos hrun _) (G (x (φ j))) (Λhat (φ j))).trans ?_
  have := hR (φ j)
  gcongr

theorem thm41 (hf : ContDiff ℝ 1 f) (hG : ContDiff ℝ 1 G) (hK : IsClosedConvexCone K)
    (hrun : IsALRun f G K ε B τ σ ρ₀ x Λhat ρ)
    (xbar : EuclideanSpace ℝ (Fin n)) (hfeas : G xbar ∈ K) (hlim : MapClusterPt xbar atTop x) :
    IsAGP f G K xbar := by
  obtain ⟨φ, hφ, hx⟩ := hlim.tendsto_subseq
  exact ⟨hfeas, x ∘ φ, fun j => mult K G ρ x Λhat (φ j), fun j => mult_mem hrun _, hx,
    grad_tendsto hf hG hK hrun hφ, PiK_tendsto hf hG hK hrun hfeas hφ hx⟩

theorem thm42 (hf : ContDiff ℝ 1 f) (hG : ContDiff ℝ 1 G) (hK : IsClosedConvexCone K)
    (hrun : IsALRun f G K ε B τ σ ρ₀ x Λhat ρ)
    (xbar : EuclideanSpace ℝ (Fin n)) (hfeas : G xbar ∈ K) (hlim : MapClusterPt xbar atTop x)
    (hL : GenLojasiewicz (Psi K G) xbar) :
    IsCAKKT f G K xbar := by
  obtain ⟨φ, hφ, hx⟩ := hlim.tendsto_subseq
  exact ⟨hfeas, x ∘ φ, fun j => mult K G ρ x Λhat (φ j), fun j => mult_mem hrun _, hx,
    grad_tendsto hf hG hK hrun hφ, PiK_tendsto hf hG hK hrun hfeas hφ hx,
    PiKpolar_tendsto hf hG hK hrun hfeas hφ hx hL⟩

end limits


/-! ### extra milestones -/

lemma infDist_eq {K : Set E} (hK : IsClosedConvexCone K) (v : E) :
    Metric.infDist v K = ‖v - proj K v‖ := by
  apply le_antisymm
  · rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem (proj_mem (CCN_of_cone hK) v)
  · rw [Metric.le_infDist hK.1]
    intro y hy
    rw [dist_eq_norm]
    exact (proj_spec (CCN_of_cone hK) v).2 y hy

theorem eq1 {K : Set E} (hK : IsClosedConvexCone K) :
    ContDiff ℝ 1 (fun v => Metric.infDist v K ^ 2) ∧
      ∀ w : E, HasGradientAt (fun v => Metric.infDist v K ^ 2) ((2 : ℝ) • (w - proj K w)) w := by
  have e : (fun v => Metric.infDist v K ^ 2) = fun v => ‖v - proj K v‖ ^ 2 := by
    funext v; rw [infDist_eq hK]
  have hgrad : ∀ w : E, HasGradientAt (fun v => ‖v - proj K v‖ ^ 2) ((2 : ℝ) • (w - proj K w)) w := by
    intro w
    rw [hasGradientAt_iff_hasFDerivAt]
    refine (hasFDerivAt_dsq (CCN_of_cone hK) w).congr_fderiv ?_
    ext z
    simp
  rw [e]
  refine ⟨?_, hgrad⟩
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨fun w => (2 : ℝ) • innerSL ℝ (w - proj K w), ?_, fun w => hasFDerivAt_dsq (CCN_of_cone hK) w⟩
  have hc : Continuous fun w : E => innerSL ℝ (w - proj K w) :=
    (innerSL ℝ (E := E)).continuous.comp (continuous_id.sub (proj_continuous (CCN_of_cone hK)))
  exact hc.const_smul (2 : ℝ)

theorem bounded_mult {f : (EuclideanSpace ℝ (Fin n)) → ℝ} {G : (EuclideanSpace ℝ (Fin n)) → E}
    {K : Set E} {ε : ℕ → ℝ} {B : Set E} {τ σ ρ₀ : ℝ}
    {x : ℕ → (EuclideanSpace ℝ (Fin n))} {Λhat : ℕ → E} {ρ : ℕ → ℝ}
    (hrun : IsALRun f G K ε B τ σ ρ₀ x Λhat ρ) (hρ : BddAbove (Set.range ρ)) :
    Tendsto (fun k => mult K G ρ x Λhat k - Λhat k) atTop (𝓝 0) ∧
      Bornology.IsBounded (Set.range (mult K G ρ x Λhat)) := by
  obtain ⟨C, hC⟩ := hρ
  have hCk : ∀ k, ρ k ≤ C := fun k => hC ⟨k, rfl⟩
  have hpos := rho_pos hrun
  have key : ∀ k, mult K G ρ x Λhat k - Λhat k = -(ρ k • Vk K G ρ x Λhat k) := by
    intro k
    simp only [mult, Vk, smul_sub, smul_smul]
    rw [mul_inv_cancel₀ (hpos k).ne', one_smul]; abel
  have hlim : Tendsto (fun k => mult K G ρ x Λhat k - Λhat k) atTop (𝓝 0) := by
    rcases dichotomy hrun with hT | ⟨k₀, -, hV⟩
    · exfalso
      obtain ⟨k, hk⟩ := (hT.eventually_gt_atTop C).exists
      exact absurd (hCk k) (not_le.mpr hk)
    · refine squeeze_zero_norm (a := fun k => C * ‖Vk K G ρ x Λhat k‖) (fun k => ?_) ?_
      · rw [key, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (hpos k)]
        exact mul_le_mul_of_nonneg_right (hCk k) (norm_nonneg _)
      · simpa using hV.const_mul C
  refine ⟨hlim, ?_⟩
  have hb1 : Bornology.IsBounded (Set.range Λhat) :=
    hrun.B_compact.isBounded.subset (Set.range_subset_iff.mpr hrun.Λhat_mem)
  have hb2 : Bornology.IsBounded (Set.range (fun k => mult K G ρ x Λhat k - Λhat k)) :=
    Metric.isBounded_range_of_tendsto _ hlim
  obtain ⟨R1, hR1⟩ := hb1.exists_norm_le
  obtain ⟨R2, hR2⟩ := hb2.exists_norm_le
  rw [isBounded_iff_forall_norm_le]
  refine ⟨R2 + R1, ?_⟩
  rintro _ ⟨k, rfl⟩
  have e : mult K G ρ x Λhat k = (mult K G ρ x Λhat k - Λhat k) + Λhat k := by abel
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (hR2 _ ⟨k, rfl⟩) (hR1 _ ⟨k, rfl⟩))

end AuxAugLag42

open AuxAugLag42 NCPSeqOpt.AugLag

set_option linter.unusedVariables false in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (G : EuclideanSpace ℝ (Fin n) → E) (hG : ContDiff ℝ 1 G)
    (K : Set E) (hK : IsClosedConvexCone K)
    (ε : ℕ → ℝ) (B : Set E) (τ σ ρ₀ : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (Λhat : ℕ → E) (ρ : ℕ → ℝ) (hrun : IsALRun f G K ε B τ σ ρ₀ x Λhat ρ)
    (xbar : EuclideanSpace ℝ (Fin n)) (hfeas : G xbar ∈ K) (hlim : MapClusterPt xbar atTop x)
    (hL : GenLojasiewicz (Psi K G) xbar) :
    IsCAKKT f G K xbar :=
  thm42 hf hG hK hrun xbar hfeas hlim hL

