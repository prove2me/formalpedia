-- Prove2me | solution 1 for MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c9151ecc-33c8-53f4-81dc-71ff4f1368ad

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic

set_option autoImplicit false

open MeasureTheory

namespace PMDND

variable {r c : ℕ}

def cube (c : ℕ) : Set (Fin c → ℝ) := Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1)

lemma measurableSet_cube : MeasurableSet (cube c) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

lemma cube_subset_Icc : cube c ⊆ Set.Icc (0 : Fin c → ℝ) 1 := by
  intro θ hθ
  simp only [cube, Set.mem_pi, Set.mem_univ, Set.mem_Ico, forall_true_left] at hθ
  exact ⟨fun i => (hθ i).1, fun i => (hθ i).2.le⟩

lemma volume_cube : volume (cube c) = 1 := by
  rw [cube, Real.volume_pi_Ico]
  simp

lemma volume_cube_lt_top : volume (cube c) < ⊤ := by
  rw [volume_cube]; exact ENNReal.one_lt_top

noncomputable def em (m : Fin c → ℤ) (θ : Fin c → ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))

lemma norm_em (m : Fin c → ℤ) (θ : Fin c → ℝ) : ‖em m θ‖ = 1 := by
  rw [em, Complex.norm_exp]
  have : (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))).re = 0 := by
    simp [Complex.mul_re]
  rw [this, Real.exp_zero]

lemma continuous_em (m : Fin c → ℤ) : Continuous (em m) := by
  unfold em
  refine Complex.continuous_exp.comp (Continuous.neg (continuous_const.mul
    (Complex.continuous_ofReal.comp ?_)))
  exact continuous_finset_sum _ fun j _ => continuous_const.mul (continuous_apply j)

structure IsWin (R : ℝ) (V : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) V
  supp : ∀ p : (Fin r → ℝ) × (Fin c → ℝ), (∃ k, R < |p.1 k|) → V p = 0
  per : ∀ (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c), V (p.1, p.2 + Pi.single j 1) = V p

private noncomputable def _root_.PMDND.dir (u : (Fin r → ℝ) × (Fin c → ℝ)) (V : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) :
    (Fin r → ℝ) × (Fin c → ℝ) → ℂ := fun p => fderiv ℝ V p u

p2m_export "PMDND" "dir"
lemma isOpen_outside (R : ℝ) : IsOpen {p : (Fin r → ℝ) × (Fin c → ℝ) | ∃ k, R < |p.1 k|} := by
  have : {p : (Fin r → ℝ) × (Fin c → ℝ) | ∃ k, R < |p.1 k|} = ⋃ k, {p | R < |p.1 k|} := by
    ext p; simp
  rw [this]
  exact isOpen_iUnion fun k => isOpen_lt continuous_const
    (continuous_abs.comp ((continuous_apply k).comp continuous_fst))

lemma IsWin.dir {R : ℝ} {V : (Fin r → ℝ) × (Fin c → ℝ) → ℂ} (hV : IsWin R V)
    (u : (Fin r → ℝ) × (Fin c → ℝ)) : IsWin R (dir u V) where
  smooth := ((contDiff_infty_iff_fderiv.1 hV.smooth).2).clm_apply contDiff_const
  supp := by
    intro p hp
    have hev : V =ᶠ[nhds p] (fun _ => (0 : ℂ)) := by
      filter_upwards [(isOpen_outside R).mem_nhds hp] with q hq
      exact hV.supp q hq
    show fderiv ℝ V p u = 0
    rw [hev.fderiv_eq]
    simp
  per := by
    intro p j
    show fderiv ℝ V (p.1, p.2 + Pi.single j 1) u = fderiv ℝ V p u
    set w : (Fin r → ℝ) × (Fin c → ℝ) := ((0 : Fin r → ℝ), Pi.single j (1 : ℝ)) with hw
    have hp : (p.1, p.2 + Pi.single j 1) = p + w := by ext <;> simp [hw]
    have hfun : (fun q => V (q + w)) = V := by
      funext q
      have : q + w = (q.1, q.2 + Pi.single j 1) := by ext <;> simp [hw]
      rw [this, hV.per]
    rw [hp, ← fderiv_comp_add_right w, hfun]

noncomputable def Ψ (m : Fin c → ℤ) (V : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (x : Fin r → ℝ) : ℂ :=
  ∫ θ in cube c, V (x, θ) * em m θ

noncomputable def dV (V : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (p : (Fin r → ℝ) × (Fin c → ℝ)) :
    (Fin r → ℝ) →L[ℝ] ℂ :=
  (fderiv ℝ V p).comp (ContinuousLinearMap.inl ℝ (Fin r → ℝ) (Fin c → ℝ))

lemma continuous_dV {V : (Fin r → ℝ) × (Fin c → ℝ) → ℂ} (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    Continuous (dV V) :=
  (((contDiff_infty_iff_fderiv.1 hV).2).continuous).clm_comp continuous_const

lemma hasFDerivAt_slice {V : (Fin r → ℝ) × (Fin c → ℝ) → ℂ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (x : Fin r → ℝ) (θ : Fin c → ℝ) :
    HasFDerivAt (fun x' : Fin r → ℝ => V (x', θ)) (dV V (x, θ)) x := by
  have hd : HasFDerivAt V (fderiv ℝ V (x, θ)) (x, θ) :=
    (hV.differentiable (by simp)).differentiableAt.hasFDerivAt
  exact hd.comp x (hasFDerivAt_prodMk_left x θ)

lemma exists_local_bound {Y : Type*} [NormedAddCommGroup Y]
    {F : (Fin r → ℝ) × (Fin c → ℝ) → Y} (hF : Continuous F) (x₀ : Fin r → ℝ) :
    ∃ C : ℝ, ∀ x ∈ Metric.closedBall x₀ 1, ∀ θ ∈ cube c, ‖F (x, θ)‖ ≤ C := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x₀ (1 : ℝ)).prod
    (isCompact_Icc (a := (0 : Fin c → ℝ)) (b := 1))).exists_bound_of_continuousOn hF.continuousOn
  exact ⟨C, fun x hx θ hθ => hC (x, θ) (Set.mem_prod.mpr ⟨hx, cube_subset_Icc hθ⟩)⟩

lemma integrableOn_cube_of_continuous {Y : Type*} [NormedAddCommGroup Y] {f : (Fin c → ℝ) → Y}
    (hf : Continuous f) : IntegrableOn f (cube c) volume :=
  (hf.continuousOn.integrableOn_compact (isCompact_Icc (a := (0 : Fin c → ℝ)) (b := 1))).mono_set
    cube_subset_Icc

lemma hasFDerivAt_Ψ {R : ℝ} {V : (Fin r → ℝ) × (Fin c → ℝ) → ℂ} (hV : IsWin R V)
    (m : Fin c → ℤ) (x₀ : Fin r → ℝ) :
    HasFDerivAt (Ψ m V) (∫ θ in cube c, em m θ • dV V (x₀, θ)) x₀ := by
  have hVc : Continuous V := hV.smooth.continuous
  have hdVc : Continuous (dV V) := continuous_dV hV.smooth
  obtain ⟨C, hC⟩ := exists_local_bound hdVc x₀
  have hslice : ∀ x, Continuous fun θ : Fin c → ℝ => em m θ • V (x, θ) := fun x =>
    (continuous_em m).smul (hVc.comp (continuous_const.prodMk continuous_id))
  have hslice' : ∀ x, Continuous fun θ : Fin c → ℝ => em m θ • dV V (x, θ) := fun x =>
    (continuous_em m).smul (hdVc.comp (continuous_const.prodMk continuous_id))
  have e : Ψ m V = fun x => ∫ θ in cube c, em m θ • V (x, θ) := by
    funext x; simp only [Ψ, smul_eq_mul, mul_comm]
  rw [e]
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict (cube c))
    (F := fun x θ => em m θ • V (x, θ)) (F' := fun x θ => em m θ • dV V (x, θ)) (x₀ := x₀)
    (s := Metric.ball x₀ 1) (bound := fun _ => C) (Metric.ball_mem_nhds x₀ one_pos)
    (Filter.Eventually.of_forall fun x => (hslice x).aestronglyMeasurable)
    (integrableOn_cube_of_continuous (hslice x₀))
    (hslice' x₀).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_cube).mpr (ae_of_all _ fun θ hθ x hx => by
      rw [norm_smul, norm_em, one_mul]
      exact hC x (Metric.ball_subset_closedBall hx) θ hθ))
    (integrableOn_const volume_cube_lt_top.ne)
    (ae_of_all _ fun θ x _ => (hasFDerivAt_slice hV.smooth x θ).const_smul (em m θ))

lemma fderiv_Ψ_apply {R : ℝ} {V : (Fin r → ℝ) × (Fin c → ℝ) → ℂ} (hV : IsWin R V)
    (m : Fin c → ℤ) (x : Fin r → ℝ) (v : Fin r → ℝ) :
    fderiv ℝ (Ψ m V) x v = Ψ m (dir (v, (0 : Fin c → ℝ)) V) x := by
  rw [(hasFDerivAt_Ψ hV m x).fderiv]
  have hint : Integrable (fun θ => em m θ • dV V (x, θ)) (volume.restrict (cube c)) :=
    integrableOn_cube_of_continuous
      ((continuous_em m).smul ((continuous_dV hV.smooth).comp (continuous_const.prodMk continuous_id)))
  rw [ContinuousLinearMap.integral_apply hint v]
  simp only [Ψ, dir, dV, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearMap.inl_apply, smul_eq_mul, mul_comm]

lemma differentiable_Ψ {R : ℝ} {V : (Fin r → ℝ) × (Fin c → ℝ) → ℂ} (hV : IsWin R V)
    (m : Fin c → ℤ) : Differentiable ℝ (Ψ m V) := fun x => (hasFDerivAt_Ψ hV m x).differentiableAt

lemma contDiff_Ψ_nat (R : ℝ) (m : Fin c → ℤ) : ∀ (n : ℕ) (V : (Fin r → ℝ) × (Fin c → ℝ) → ℂ),
    IsWin R V → ContDiff ℝ n (Ψ m V) := by
  intro n
  induction n with
  | zero =>
    intro V hV
    exact contDiff_zero.mpr (differentiable_Ψ hV m).continuous
  | succ n ih =>
    intro V hV
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_fderiv_apply]
    refine ⟨differentiable_Ψ hV m, fun hn => absurd hn (by simp), fun v => ?_⟩
    have : (fun x => fderiv ℝ (Ψ m V) x v) = Ψ m (dir (v, (0 : Fin c → ℝ)) V) :=
      funext fun x => fderiv_Ψ_apply hV m x v
    rw [this]
    exact ih _ (hV.dir _)

lemma contDiff_Ψ {R : ℝ} {V : (Fin r → ℝ) × (Fin c → ℝ) → ℂ} (hV : IsWin R V) (m : Fin c → ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (Ψ m V) :=
  contDiff_infty.2 fun n => contDiff_Ψ_nat R m n V hV

private noncomputable def _root_.PMDND.DDX : (n : ℕ) → (Fin n → (Fin r → ℝ)) → ((Fin r → ℝ) × (Fin c → ℝ) → ℂ) →
    ((Fin r → ℝ) × (Fin c → ℝ) → ℂ)
  | 0, _, V => V
  | n + 1, u, V => DDX n (Fin.init u) (dir (u (Fin.last n), (0 : Fin c → ℝ)) V)

p2m_export "PMDND" "DDX"
lemma IsWin.DDX {R : ℝ} : ∀ (n : ℕ) (u : Fin n → (Fin r → ℝ)) {V : (Fin r → ℝ) × (Fin c → ℝ) → ℂ},
    IsWin R V → IsWin R (DDX n u V)
  | 0, _, _, hV => hV
  | n + 1, u, _, hV => IsWin.DDX n (Fin.init u) (hV.dir _)

lemma iteratedFDeriv_Ψ_apply {R : ℝ} (m : Fin c → ℤ) : ∀ (n : ℕ) (V : (Fin r → ℝ) × (Fin c → ℝ) → ℂ),
    IsWin R V → ∀ (x : Fin r → ℝ) (u : Fin n → (Fin r → ℝ)),
      (iteratedFDeriv ℝ n (Ψ m V) x) u = Ψ m (DDX n u V) x := by
  intro n
  induction n with
  | zero => intro V hV x u; simp [DDX]
  | succ n ih =>
    intro V hV x u
    rw [iteratedFDeriv_succ_apply_right]

    set L : ((Fin r → ℝ) →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ (u (Fin.last n)) with hL
    have hfd : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ (Ψ m V) y) :=
      (contDiff_infty_iff_fderiv.1 (contDiff_Ψ hV m)).2
    have h1 : iteratedFDeriv ℝ n (fun y => fderiv ℝ (Ψ m V) y (u (Fin.last n))) x =
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ n (fun y => fderiv ℝ (Ψ m V) y) x) := by
      have : (fun y => fderiv ℝ (Ψ m V) y (u (Fin.last n))) = L ∘ (fun y => fderiv ℝ (Ψ m V) y) := by
        funext y; simp [hL]
      rw [this, ContinuousLinearMap.iteratedFDeriv_comp_left L hfd.contDiffAt (by exact_mod_cast le_top)]
    have h2 : ((iteratedFDeriv ℝ n (fun y => fderiv ℝ (Ψ m V) y) x) (Fin.init u)) (u (Fin.last n)) =
        (iteratedFDeriv ℝ n (fun y => fderiv ℝ (Ψ m V) y (u (Fin.last n))) x) (Fin.init u) := by
      rw [h1]; simp [hL]
    rw [h2]
    have h3 : (fun y => fderiv ℝ (Ψ m V) y (u (Fin.last n))) = Ψ m (dir (u (Fin.last n), (0 : Fin c → ℝ)) V) :=
      funext fun y => fderiv_Ψ_apply hV m y _
    rw [h3, ih _ (hV.dir _) x (Fin.init u)]
    rfl

lemma norm_iteratedFDeriv_dir_le {V : (Fin r → ℝ) × (Fin c → ℝ) → ℂ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (w : (Fin r → ℝ) × (Fin c → ℝ)) (j : ℕ) (p : (Fin r → ℝ) × (Fin c → ℝ)) :
    ‖iteratedFDeriv ℝ j (dir w V) p‖ ≤ ‖w‖ * ‖iteratedFDeriv ℝ (j + 1) V p‖ := by
  set L : (((Fin r → ℝ) × (Fin c → ℝ)) →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ w with hL
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ V y) := (contDiff_infty_iff_fderiv.1 hV).2
  have : dir w V = L ∘ (fun y => fderiv ℝ V y) := by funext y; simp [hL, dir]
  rw [this, ContinuousLinearMap.iteratedFDeriv_comp_left L hfd.contDiffAt (by exact_mod_cast le_top),
    ← norm_iteratedFDeriv_fderiv]
  calc ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ j (fderiv ℝ V) p)‖
      ≤ ‖L‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ V) p‖ := ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ ‖w‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ V) p‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg w) (fun f => ?_)
        rw [hL, ContinuousLinearMap.apply_apply, mul_comm]
        exact f.le_opNorm w

lemma norm_iteratedFDeriv_DDX_le {R : ℝ} : ∀ (n : ℕ) (u : Fin n → (Fin r → ℝ))
    {V : (Fin r → ℝ) × (Fin c → ℝ) → ℂ}, IsWin R V → ∀ (j : ℕ) (p : (Fin r → ℝ) × (Fin c → ℝ)),
    ‖iteratedFDeriv ℝ j (DDX n u V) p‖ ≤ (∏ i, ‖u i‖) * ‖iteratedFDeriv ℝ (j + n) V p‖
  | 0, u, V, hV, j, p => by simp [DDX]
  | n + 1, u, V, hV, j, p => by
    have ih := norm_iteratedFDeriv_DDX_le n (Fin.init u) (hV.dir (u (Fin.last n), (0 : Fin c → ℝ))) j p
    have h2 := norm_iteratedFDeriv_dir_le hV.smooth (u (Fin.last n), (0 : Fin c → ℝ)) (j + n) p
    have hnorm : ‖(u (Fin.last n), (0 : Fin c → ℝ))‖ = ‖u (Fin.last n)‖ := by
      simp [Prod.norm_def]
    rw [hnorm] at h2
    calc ‖iteratedFDeriv ℝ j (DDX (n + 1) u V) p‖
        = ‖iteratedFDeriv ℝ j (DDX n (Fin.init u) (dir (u (Fin.last n), (0 : Fin c → ℝ)) V)) p‖ := rfl
      _ ≤ (∏ i, ‖Fin.init u i‖) * ‖iteratedFDeriv ℝ (j + n) (dir (u (Fin.last n), (0 : Fin c → ℝ)) V) p‖ := ih
      _ ≤ (∏ i, ‖Fin.init u i‖) * (‖u (Fin.last n)‖ * ‖iteratedFDeriv ℝ (j + n + 1) V p‖) :=
          mul_le_mul_of_nonneg_left h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      _ = (∏ i, ‖u i‖) * ‖iteratedFDeriv ℝ (j + (n + 1)) V p‖ := by
          have e : iteratedFDeriv ℝ (j + (n + 1)) V p = iteratedFDeriv ℝ (j + n + 1) V p := rfl
          rw [e, Fin.prod_univ_castSucc (fun i => ‖u i‖)]
          simp only [Fin.init]
          ring

def eT (j : Fin c) : (Fin r → ℝ) × (Fin c → ℝ) := ((0 : Fin r → ℝ), (Pi.single j (1 : ℝ) : Fin c → ℝ))

lemma norm_eT (j : Fin c) : ‖(eT j : (Fin r → ℝ) × (Fin c → ℝ))‖ = 1 := by
  simp only [eT, Prod.norm_def, norm_zero]
  rw [max_eq_right (norm_nonneg _)]
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  · have := norm_le_pi_norm (Pi.single j (1 : ℝ) : Fin c → ℝ) j
    simpa using this

lemma norm_iteratedFDeriv_dT2_le {V : (Fin r → ℝ) × (Fin c → ℝ) → ℂ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (a : Fin c) (j : ℕ) (p : (Fin r → ℝ) × (Fin c → ℝ)) :
    ‖iteratedFDeriv ℝ j (dir (eT a) (dir (eT a) V)) p‖ ≤ ‖iteratedFDeriv ℝ (j + 2) V p‖ := by
  have hV' : ContDiff ℝ (⊤ : ℕ∞) (dir (eT a) V) :=
    ((contDiff_infty_iff_fderiv.1 hV).2).clm_apply contDiff_const
  calc _ ≤ ‖(eT a : (Fin r → ℝ) × (Fin c → ℝ))‖ * ‖iteratedFDeriv ℝ (j + 1) (dir (eT a) V) p‖ :=
        norm_iteratedFDeriv_dir_le hV' _ j p
    _ ≤ ‖(eT a : (Fin r → ℝ) × (Fin c → ℝ))‖ * (‖(eT a : (Fin r → ℝ) × (Fin c → ℝ))‖ *
          ‖iteratedFDeriv ℝ (j + 1 + 1) V p‖) :=
        mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_dir_le hV _ (j + 1) p) (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ (j + 2) V p‖ := by rw [norm_eT]; ring_nf

section Torus

attribute [local instance] instMeasureSpaceUnitAddCircle

theorem volume_unitAddCircle_eq : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := rfl

scoped instance instIsAddRightInvariant_unitAddCircle : (volume : Measure UnitAddCircle).IsAddRightInvariant := by
  rw [volume_unitAddCircle_eq]; infer_instance

scoped instance instSigmaFinite_unitAddCircle : SigmaFinite (volume : Measure UnitAddCircle) := by
  rw [volume_unitAddCircle_eq]; infer_instance

theorem periodic_intCast (g : (Fin c → ℝ) → ℂ)
    (hper : ∀ (θ : Fin c → ℝ) (j : Fin c), g (θ + Pi.single j 1) = g θ)
    (θ : Fin c → ℝ) (k : Fin c → ℤ) : g (θ + fun i => (k i : ℝ)) = g θ := by
  classical
  let P : AddSubgroup (Fin c → ℝ) :=
    { carrier := {v | ∀ θ, g (θ + v) = g θ}
      add_mem' := fun {a b} ha hb θ => by
        show g (θ + (a + b)) = g θ
        rw [← add_assoc, hb, ha]
      zero_mem' := fun θ => by show g (θ + 0) = g θ; rw [add_zero]
      neg_mem' := fun {a} ha θ => by
        show g (θ + -a) = g θ
        have h := ha (θ + -a)
        rw [neg_add_cancel_right] at h
        exact h.symm }
  have hsingle : ∀ (j : Fin c) (n : ℤ), (Pi.single j ((n : ℝ)) : Fin c → ℝ) ∈ P := by
    intro j n
    have h1 : (Pi.single j (1 : ℝ) : Fin c → ℝ) ∈ P := fun θ => hper θ j
    have : (Pi.single j ((n : ℝ)) : Fin c → ℝ) = n • (Pi.single j (1 : ℝ) : Fin c → ℝ) := by
      ext i
      by_cases h : i = j
      · subst h; simp
      · simp [h]
    rw [this]
    exact P.zsmul_mem h1 n
  have hk : (fun i => (k i : ℝ)) ∈ P := by
    have : (fun i => (k i : ℝ)) = ∑ j : Fin c, (Pi.single j ((k j : ℝ)) : Fin c → ℝ) :=
      (Finset.univ_sum_single (fun i => (k i : ℝ))).symm
    rw [this]
    exact P.sum_mem fun j _ => hsingle j (k j)
  exact hk θ

def qT (θ : Fin c → ℝ) : UnitAddTorus (Fin c) := fun i => (θ i : UnitAddCircle)

noncomputable def secT (x : UnitAddTorus (Fin c)) : Fin c → ℝ := fun i => ((AddCircle.equivIco (1 : ℝ) 0 (x i) : ℝ))

lemma qT_secT (x : UnitAddTorus (Fin c)) : qT (secT x) = x := by
  funext i
  exact AddCircle.coe_equivIco

lemma qT_add (θ w : Fin c → ℝ) : qT (θ + w) = qT θ + qT w := by
  funext i; simp [qT]

lemma secT_qT (θ : Fin c → ℝ) : ∃ k : Fin c → ℤ, secT (qT θ) = θ + fun i => (k i : ℝ) := by
  refine ⟨fun i => -⌊θ i⌋, funext fun i => ?_⟩
  show ((AddCircle.equivIco (1 : ℝ) 0 ((θ i : ℝ) : UnitAddCircle) : ℝ)) = θ i + ((-⌊θ i⌋ : ℤ) : ℝ)
  rw [AddCircle.coe_equivIco_mk_apply, div_one, mul_one, Int.fract, Int.cast_neg, sub_eq_add_neg]

lemma comp_secT_qT (g : (Fin c → ℝ) → ℂ)
    (hper : ∀ (θ : Fin c → ℝ) (j : Fin c), g (θ + Pi.single j 1) = g θ) (θ : Fin c → ℝ) :
    g (secT (qT θ)) = g θ := by
  obtain ⟨k, hk⟩ := secT_qT θ
  rw [hk]
  exact periodic_intCast g hper θ k

lemma integral_cube_eq_torus (g : (Fin c → ℝ) → ℂ)
    (hper : ∀ (θ : Fin c → ℝ) (j : Fin c), g (θ + Pi.single j 1) = g θ) :
    ∫ θ in cube c, g θ = ∫ x : UnitAddTorus (Fin c), g (secT x) := by
  refine Eq.trans ?_ (UnitAddTorus.integral_preimage (fun x => g (secT x)) (0 : Fin c → ℝ)).symm
  have hset : {x : Fin c → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin c → ℝ) i) ((0 : Fin c → ℝ) i + 1)}
      =ᵐ[volume] cube c := by
    have h1 : {x : Fin c → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin c → ℝ) i) ((0 : Fin c → ℝ) i + 1)}
        = Set.pi Set.univ (fun i => Set.Ioc ((0 : Fin c → ℝ) i) ((1 : Fin c → ℝ) i)) := by
      ext x; simp
    have h2 : cube c = Set.pi Set.univ (fun i => Set.Ico ((0 : Fin c → ℝ) i) ((1 : Fin c → ℝ) i)) := by
      ext x; simp [cube]
    rw [h1, h2, volume_pi]
    exact Measure.univ_pi_Ioc_ae_eq_Icc.trans Measure.univ_pi_Ico_ae_eq_Icc.symm
  rw [setIntegral_congr_set hset]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show g x = g (secT (qT x))
  exact (comp_secT_qT g hper x).symm

lemma integral_cube_translate (g : (Fin c → ℝ) → ℂ)
    (hper : ∀ (θ : Fin c → ℝ) (j : Fin c), g (θ + Pi.single j 1) = g θ) (w : Fin c → ℝ) :
    ∫ θ in cube c, g (θ + w) = ∫ θ in cube c, g θ := by
  have hper' : ∀ (θ : Fin c → ℝ) (j : Fin c), g (θ + Pi.single j 1 + w) = g (θ + w) := by
    intro θ j; rw [add_right_comm, hper]
  rw [integral_cube_eq_torus (fun θ => g (θ + w)) hper', integral_cube_eq_torus g hper]
  have key : ∀ x : UnitAddTorus (Fin c), g (secT x + w) = g (secT (x + qT w)) := by
    intro x
    have : x + qT w = qT (secT x + w) := by rw [qT_add, qT_secT]
    rw [this, comp_secT_qT g hper]
  simp_rw [key]
  exact integral_add_right_eq_self (fun x => g (secT x)) (qT w)

end Torus

lemma em_periodic (m : Fin c → ℤ) (θ : Fin c → ℝ) (j : Fin c) :
    em m (θ + Pi.single j 1) = em m θ := by
  unfold em
  have : (∑ i, (m i : ℝ) * (θ + (Pi.single j 1 : Fin c → ℝ)) i) = (∑ i, (m i : ℝ) * θ i) + (m j : ℝ) := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi; simp [hi]
    · simp
  rw [this]
  push_cast
  have h1 : -(2 * (Real.pi : ℂ) * Complex.I * ((m j : ℤ) : ℂ)) = ((-(m j) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [mul_add, neg_add, Complex.exp_add, h1, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma em_sub_smul (m : Fin c → ℤ) (θ : Fin c → ℝ) (j : Fin c) (t : ℝ) :
    em m (θ - t • Pi.single j 1) = em m θ * Complex.exp (2 * Real.pi * Complex.I * (m j : ℝ) * t) := by
  unfold em
  have : (∑ i, (m i : ℝ) * (θ - t • (Pi.single j 1 : Fin c → ℝ)) i) = (∑ i, (m i : ℝ) * θ i) - (m j : ℝ) * t := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi; simp [hi]
    · simp
  rw [this, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma integral_cube_fderiv_mul_em (g : (Fin c → ℝ) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hper : ∀ (θ : Fin c → ℝ) (j : Fin c), g (θ + Pi.single j 1) = g θ)
    (m : Fin c → ℤ) (j : Fin c) :
    ∫ θ in cube c, fderiv ℝ g θ (Pi.single j 1) * em m θ =
      (2 * Real.pi * Complex.I * (m j : ℝ)) * ∫ θ in cube c, g θ * em m θ := by
  set v : Fin c → ℝ := Pi.single j 1 with hv

  set φ : ℝ → ℂ := fun t => ∫ θ in cube c, g (θ + t • v) * em m θ with hφ

  have hφ1 : ∀ t : ℝ, φ t = Complex.exp (2 * Real.pi * Complex.I * (m j : ℝ) * t) *
      ∫ θ in cube c, g θ * em m θ := by
    intro t
    have hperF : ∀ (θ : Fin c → ℝ) (i : Fin c),
        (fun θ => g θ * em m (θ - t • v)) (θ + Pi.single i 1) = (fun θ => g θ * em m (θ - t • v)) θ := by
      intro θ i
      simp only
      rw [hper, show θ + Pi.single i 1 - t • v = (θ - t • v) + Pi.single i 1 by abel, em_periodic]
    have := integral_cube_translate (fun θ => g θ * em m (θ - t • v)) hperF (t • v)
    simp only [add_sub_cancel_right] at this
    rw [hφ]
    simp only
    rw [this]
    simp_rw [hv, em_sub_smul]
    rw [← integral_const_mul]
    congr 1; funext θ; ring

  have hgc : Continuous g := hg.continuous
  have hg'c : Continuous (fun θ => fderiv ℝ g θ) := (contDiff_infty_iff_fderiv.1 hg).2.continuous
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := (-1 : Fin c → ℝ) - 1) (b := (1 : Fin c → ℝ) + 1))).exists_bound_of_continuousOn
    hg'c.continuousOn
  have hmem : ∀ t ∈ Metric.ball (0 : ℝ) 1, ∀ θ ∈ cube c,
      θ + t • v ∈ Set.Icc ((-1 : Fin c → ℝ) - 1) ((1 : Fin c → ℝ) + 1) := by
    intro t ht θ hθ
    have ht' : |t| < 1 := by simpa using ht
    have hθ' := cube_subset_Icc hθ
    constructor
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, Pi.one_apply, smul_eq_mul, hv]
      have h1 : (0 : ℝ) ≤ θ i := hθ'.1 i
      by_cases hij : i = j
      · subst hij; simp; nlinarith [abs_lt.mp ht']
      · simp [hij]; linarith
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, hv]
      have h1 : θ i ≤ 1 := hθ'.2 i
      by_cases hij : i = j
      · subst hij; simp; nlinarith [abs_lt.mp ht']
      · simp [hij]; linarith
  have hderiv : ∀ (θ : Fin c → ℝ) (t : ℝ),
      HasDerivAt (fun s : ℝ => g (θ + s • v) * em m θ) (fderiv ℝ g (θ + t • v) v * em m θ) t := by
    intro θ t
    have hl : HasDerivAt (fun s : ℝ => θ + s • v) v t := by
      have := ((hasDerivAt_id t).smul_const v).const_add θ
      simpa using this
    have hG : HasFDerivAt g (fderiv ℝ g (θ + t • v)) (θ + t • v) :=
      (hg.differentiable (by simp)).differentiableAt.hasFDerivAt
    exact (hG.comp_hasDerivAt t hl).mul_const _
  have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (cube c))
    (F := fun (t : ℝ) (θ : Fin c → ℝ) => g (θ + t • v) * em m θ)
    (F' := fun (t : ℝ) (θ : Fin c → ℝ) => fderiv ℝ g (θ + t • v) v * em m θ) (x₀ := 0)
    (s := Metric.ball 0 1) (bound := fun _ => C * ‖v‖) (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall fun t => ((hgc.comp (continuous_id.add continuous_const)).mul
      (continuous_em m)).aestronglyMeasurable)
    (integrableOn_cube_of_continuous ((hgc.comp (continuous_id.add continuous_const)).mul (continuous_em m)))
    (((hg'c.comp (continuous_id.add continuous_const)).clm_apply continuous_const).mul
      (continuous_em m)).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_cube).mpr (ae_of_all _ fun θ hθ t ht => by
      rw [norm_mul, norm_em, mul_one]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hC _ (hmem t ht θ hθ)) (norm_nonneg _))))
    (integrableOn_const volume_cube_lt_top.ne)
    (ae_of_all _ fun θ t _ => hderiv θ t)
  have hD2 : HasDerivAt φ (∫ θ in cube c, fderiv ℝ g (θ + (0 : ℝ) • v) v * em m θ) 0 := hD.2
  simp only [zero_smul, add_zero] at hD2

  have hD3 : HasDerivAt φ (Complex.exp (2 * Real.pi * Complex.I * (m j : ℝ) * (0 : ℝ)) *
      (2 * Real.pi * Complex.I * (m j : ℝ)) * ∫ θ in cube c, g θ * em m θ) 0 := by
    have e : φ = fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (m j : ℝ) * t) *
        ∫ θ in cube c, g θ * em m θ := funext hφ1
    rw [e]
    apply HasDerivAt.mul_const
    have h1 : HasDerivAt (fun t : ℝ => 2 * Real.pi * Complex.I * (m j : ℝ) * (t : ℂ))
        (2 * Real.pi * Complex.I * (m j : ℝ) * 1) 0 := by
      have : HasDerivAt (fun t : ℝ => ((id t : ℝ) : ℂ)) ((1 : ℝ) : ℂ) 0 := (hasDerivAt_id (0 : ℝ)).ofReal_comp
      simpa using this.const_mul (2 * Real.pi * Complex.I * (m j : ℝ))
    have := h1.cexp
    simpa using this
  have := hD2.unique hD3
  rw [this]
  simp

lemma Ψ_dT {R : ℝ} {U : (Fin r → ℝ) × (Fin c → ℝ) → ℂ} (hU : IsWin R U) (m : Fin c → ℤ)
    (j : Fin c) (x : Fin r → ℝ) :
    Ψ m (dir (eT j) U) x = (2 * Real.pi * Complex.I * (m j : ℝ)) * Ψ m U x := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun θ : Fin c → ℝ => U (x, θ)) :=
    hU.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hgper : ∀ (θ : Fin c → ℝ) (i : Fin c), U (x, θ + Pi.single i 1) = U (x, θ) :=
    fun θ i => hU.per (x, θ) i
  have key := integral_cube_fderiv_mul_em (fun θ => U (x, θ)) hg hgper m j
  have hderiv : ∀ θ : Fin c → ℝ, fderiv ℝ (fun θ : Fin c → ℝ => U (x, θ)) θ (Pi.single j 1) =
      dir (eT j) U (x, θ) := by
    intro θ
    have hd : HasFDerivAt U (fderiv ℝ U (x, θ)) (x, θ) :=
      (hU.smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
    have h2 : HasFDerivAt (fun θ' : Fin c → ℝ => U (x, θ'))
        ((fderiv ℝ U (x, θ)).comp (ContinuousLinearMap.inr ℝ (Fin r → ℝ) (Fin c → ℝ))) θ :=
      hd.comp θ (hasFDerivAt_prodMk_right x θ)
    rw [h2.fderiv]
    simp [dir, eT]
  simp_rw [hderiv] at key
  exact key

lemma norm_Ψ_eq {R : ℝ} {U : (Fin r → ℝ) × (Fin c → ℝ) → ℂ} (hU : IsWin R U) (m : Fin c → ℤ)
    (j : Fin c) (hj : m j ≠ 0) (x : Fin r → ℝ) :
    ‖Ψ m U x‖ = ‖Ψ m (dir (eT j) (dir (eT j) U)) x‖ * ((2 * Real.pi * |(m j : ℝ)|) ^ 2)⁻¹ := by
  rw [Ψ_dT (hU.dir _) m j x, Ψ_dT hU m j x]
  set C : ℂ := 2 * Real.pi * Complex.I * (m j : ℝ) with hCdef
  clear_value C
  have hn : ‖C‖ = 2 * Real.pi * |(m j : ℝ)| := by
    rw [hCdef, norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_ofNat]
  rw [norm_mul, norm_mul, hn]
  have hpos : 0 < 2 * Real.pi * |(m j : ℝ)| := by
    have : (0 : ℝ) < |(m j : ℝ)| := abs_pos.mpr (by exact_mod_cast hj)
    positivity
  field_simp

lemma norm_Ψ_le_of_bound {U : (Fin r → ℝ) × (Fin c → ℝ) → ℂ} (m : Fin c → ℤ) (x : Fin r → ℝ)
    {C : ℝ} (hC : ∀ θ ∈ cube c, ‖U (x, θ)‖ ≤ C) : ‖Ψ m U x‖ ≤ C := by
  have := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure (Fin c → ℝ))) (s := cube c)
    (f := fun θ => U (x, θ) * em m θ) (C := C) volume_cube_lt_top
    (fun θ hθ => by rw [norm_mul, norm_em, mul_one]; exact hC θ hθ)
  rwa [Measure.real, volume_cube, ENNReal.toReal_one, mul_one] at this

lemma decay {R : ℝ} (m : Fin c → ℤ) (x : Fin r → ℝ) :
    ∀ (S : Finset (Fin c)), (∀ j ∈ S, m j ≠ 0) →
      ∀ (k : ℕ) (C : ℝ) (U : (Fin r → ℝ) × (Fin c → ℝ) → ℂ), IsWin R U → 2 * S.card ≤ k →
        (∀ i : ℕ, i ≤ k → ∀ p, ‖iteratedFDeriv ℝ i U p‖ ≤ C) →
        ‖Ψ m U x‖ ≤ C * ∏ j ∈ S, ((2 * Real.pi * |(m j : ℝ)|) ^ 2)⁻¹ := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ k C U hU _ hb
    rw [Finset.prod_empty, mul_one]
    exact norm_Ψ_le_of_bound m x fun θ _ => by
      have := hb 0 (Nat.zero_le k) (x, θ)
      rwa [norm_iteratedFDeriv_zero] at this
  | insert a S ha ih =>
    intro hm k C U hU hk hb
    have hma : m a ≠ 0 := hm a (Finset.mem_insert_self a S)
    have hmS : ∀ j ∈ S, m j ≠ 0 := fun j hj => hm j (Finset.mem_insert_of_mem hj)
    rw [Finset.card_insert_of_notMem ha] at hk
    set U' := dir (eT a) (dir (eT a) U) with hU'
    have hU'w : IsWin R U' := (hU.dir _).dir _
    have hb' : ∀ i : ℕ, i ≤ k - 2 → ∀ p, ‖iteratedFDeriv ℝ i U' p‖ ≤ C := fun i hi p =>
      (norm_iteratedFDeriv_dT2_le hU.smooth a i p).trans (hb (i + 2) (by omega) p)
    have := ih hmS (k - 2) C U' hU'w (by omega) hb'
    rw [norm_Ψ_eq hU m a hma x, Finset.prod_insert ha]
    have hpos : 0 ≤ ((2 * Real.pi * |(m a : ℝ)|) ^ 2)⁻¹ := by positivity
    calc ‖Ψ m U' x‖ * ((2 * Real.pi * |(m a : ℝ)|) ^ 2)⁻¹
        ≤ (C * ∏ j ∈ S, ((2 * Real.pi * |(m j : ℝ)|) ^ 2)⁻¹) * ((2 * Real.pi * |(m a : ℝ)|) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right this hpos
      _ = C * (((2 * Real.pi * |(m a : ℝ)|) ^ 2)⁻¹ * ∏ j ∈ S, ((2 * Real.pi * |(m j : ℝ)|) ^ 2)⁻¹) := by ring

lemma iteratedFDeriv_eq_zero_outside {R : ℝ} {W : (Fin r → ℝ) × (Fin c → ℝ) → ℂ} (hW : IsWin R W)
    (i : ℕ) (p : (Fin r → ℝ) × (Fin c → ℝ)) (hp : ∃ k, R < |p.1 k|) : iteratedFDeriv ℝ i W p = 0 := by
  have hev : W =ᶠ[nhds p] (fun _ => (0 : ℂ)) := by
    filter_upwards [(isOpen_outside R).mem_nhds hp] with q hq
    exact hW.supp q hq
  have := (hev.iteratedFDeriv ℝ i).eq_of_nhds
  rw [this, iteratedFDeriv_zero_fun]
  rfl

lemma iteratedFDeriv_periodic {R : ℝ} {W : (Fin r → ℝ) × (Fin c → ℝ) → ℂ} (hW : IsWin R W)
    (i : ℕ) (p : (Fin r → ℝ) × (Fin c → ℝ)) (k : Fin c → ℤ) :
    iteratedFDeriv ℝ i W (p + ((0 : Fin r → ℝ), fun j => (k j : ℝ))) = iteratedFDeriv ℝ i W p := by
  have hfun : (fun q => W (q + ((0 : Fin r → ℝ), fun j => (k j : ℝ)))) = W := by
    funext q
    have : q + ((0 : Fin r → ℝ), fun j => (k j : ℝ)) = (q.1, q.2 + fun j => (k j : ℝ)) := by
      ext <;> simp
    rw [this]
    exact periodic_intCast (fun θ => W (q.1, θ)) (fun θ j => hW.per (q.1, θ) j) q.2 k
  rw [← iteratedFDeriv_comp_add_right i, hfun]

lemma exists_bound_iteratedFDeriv {R : ℝ} {W : (Fin r → ℝ) × (Fin c → ℝ) → ℂ} (hW : IsWin R W)
    (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p, ‖iteratedFDeriv ℝ i W p‖ ≤ C := by
  have hcont : Continuous (iteratedFDeriv ℝ i W) :=
    hW.smooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := fun _ : Fin r => -R) (b := fun _ : Fin r => R)).prod
    (isCompact_Icc (a := (0 : Fin c → ℝ)) (b := 1))).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun p => ?_⟩
  by_cases hp : ∃ k, R < |p.1 k|
  · rw [iteratedFDeriv_eq_zero_outside hW i p hp, norm_zero]; exact le_max_right _ _
  · push_neg at hp

    set k : Fin c → ℤ := fun j => ⌊p.2 j⌋ with hk
    set p' : (Fin r → ℝ) × (Fin c → ℝ) := (p.1, fun j => Int.fract (p.2 j)) with hp'
    have hpp : p = p' + ((0 : Fin r → ℝ), fun j => (k j : ℝ)) := by
      ext j
      · simp [hp']
      · simp only [hp', hk, Prod.snd_add, Pi.add_apply]
        rw [← Int.self_sub_floor (p.2 j)]
        ring
    rw [hpp, iteratedFDeriv_periodic hW i p' k]
    refine (hC p' (Set.mem_prod.mpr ⟨?_, ?_⟩)).trans (le_max_left _ _)
    · simp only [hp', Set.mem_Icc]
      exact ⟨fun j => (abs_le.mp (hp j)).1, fun j => (abs_le.mp (hp j)).2⟩
    · simp only [hp', Set.mem_Icc]
      exact ⟨fun j => Int.fract_nonneg _, fun j => (Int.fract_lt_one _).le⟩

lemma exists_uniform_bound {R : ℝ} {W : (Fin r → ℝ) × (Fin c → ℝ) → ℂ} (hW : IsWin R W) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i : ℕ, i ≤ N → ∀ p, ‖iteratedFDeriv ℝ i W p‖ ≤ M := by
  choose C hC0 hC using fun i => exists_bound_iteratedFDeriv hW i
  refine ⟨∑ i ∈ Finset.range (N + 1), C i, Finset.sum_nonneg fun i _ => hC0 i, fun i hi p => ?_⟩
  exact (hC i p).trans (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_range.mpr (by omega)))

end PMDND
p2m_reactivate "P2MW.S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic.PMDND"

theorem solution
    {r c : ℕ} (W : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (R : ℝ) (hR : 0 ≤ R) (hsupp : ∀ p : (Fin r → ℝ) × (Fin c → ℝ), (∃ k, R < |p.1 k|) → W p = 0)
    (hper : ∀ (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c), W (p.1, p.2 + Pi.single j 1) = W p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ m : Fin c → ℤ,
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin r → ℝ =>
        ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
          W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) ∧
      (∀ x : Fin r → ℝ, (∃ k, R < |x k|) →
        (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
          W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) = 0) ∧
      ∀ n : ℕ, n ≤ 2 * r → ∀ x : Fin r → ℝ,
        ‖iteratedFDeriv ℝ n (fun x : Fin r → ℝ =>
            ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
              W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) x‖ ≤
          M * ∏ j, (1 + |(m j : ℝ)|)⁻¹ ^ 2 := by
  classical
  have hWin : PMDND.IsWin R W := ⟨hW, hsupp, hper⟩
  obtain ⟨M₀, hM₀, hbd⟩ := PMDND.exists_uniform_bound hWin (2 * r + 2 * c)
  refine ⟨M₀, hM₀, fun m => ?_⟩
  have hΨ : (fun x : Fin r → ℝ =>
      ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
        W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) =
      PMDND.Ψ m W := rfl
  rw [hΨ]
  refine ⟨PMDND.contDiff_Ψ hWin m, ?_, ?_⟩
  · intro x hx
    show (∫ θ in PMDND.cube c, W (x, θ) * PMDND.em m θ) = 0
    have : ∀ θ, W (x, θ) * PMDND.em m θ = 0 := fun θ => by rw [hsupp (x, θ) hx, zero_mul]
    simp_rw [this]
    exact integral_zero _ _
  · intro n hn x

    obtain ⟨S, hS⟩ : ∃ S : Finset (Fin c), S = Finset.univ.filter (fun j => m j ≠ 0) := ⟨_, rfl⟩
    have hSm : ∀ j ∈ S, m j ≠ 0 := fun j hj => by
      rw [hS] at hj; exact (Finset.mem_filter.mp hj).2
    have hScard : 2 * S.card ≤ 2 * c := by
      have h1 := Finset.card_filter_le (Finset.univ : Finset (Fin c)) (fun j => m j ≠ 0)
      rw [Finset.card_univ, Fintype.card_fin, ← hS] at h1
      omega
    have hprod : ∏ j ∈ S, ((2 * Real.pi * |(m j : ℝ)|) ^ 2)⁻¹ ≤ ∏ j, (1 + |(m j : ℝ)|)⁻¹ ^ 2 := by
      rw [← Finset.prod_subset (Finset.subset_univ S) (f := fun j => (1 + |(m j : ℝ)|)⁻¹ ^ 2)]
      · apply Finset.prod_le_prod (fun j _ => by positivity)
        intro j hj
        have hmj : (1 : ℝ) ≤ |(m j : ℝ)| := by
          have := hSm j hj
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs this
        rw [inv_pow]
        apply inv_anti₀ (by positivity)
        have hπ := Real.pi_gt_three
        exact pow_le_pow_left₀ (by positivity) (by nlinarith) 2
      · intro j _ hj
        have : m j = 0 := by
          by_contra h; exact hj (hS ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)
        simp [this]
    have hT0 : 0 ≤ ∏ j, (1 + |(m j : ℝ)|)⁻¹ ^ 2 := Finset.prod_nonneg fun j _ => by positivity
    apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
    intro u
    rw [PMDND.iteratedFDeriv_Ψ_apply m n W hWin x u]
    have hU : PMDND.IsWin R (PMDND.DDX n u W) := hWin.DDX n u
    have hUb : ∀ i : ℕ, i ≤ 2 * c → ∀ p, ‖iteratedFDeriv ℝ i (PMDND.DDX n u W) p‖ ≤ (∏ i, ‖u i‖) * M₀ := by
      intro i hi p
      refine (PMDND.norm_iteratedFDeriv_DDX_le n u hWin i p).trans ?_
      exact mul_le_mul_of_nonneg_left (hbd (i + n) (by omega) p) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    have hdec := PMDND.decay m x S hSm (2 * c) ((∏ i, ‖u i‖) * M₀) (PMDND.DDX n u W) hU hScard hUb
    calc ‖PMDND.Ψ m (PMDND.DDX n u W) x‖ ≤ (∏ i, ‖u i‖) * M₀ * ∏ j ∈ S, ((2 * Real.pi * |(m j : ℝ)|) ^ 2)⁻¹ := hdec
      _ ≤ (∏ i, ‖u i‖) * M₀ * ∏ j, (1 + |(m j : ℝ)|)⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = M₀ * (∏ j, (1 + |(m j : ℝ)|)⁻¹ ^ 2) * ∏ i, ‖u i‖ := by ring

end S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic
end P2MW
export P2MW.S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic (solution)
