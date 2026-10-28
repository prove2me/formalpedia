-- Prove2me | solution 1 for MaxwellWiki.charge_conservation_box
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T11:46:10.746946+00:00
-- url     : https://prove2.me/submissions/20811549-e3f2-4a8c-9229-57a0380c52ca

import Mathlib
import Definitions.Def_MaxwellWiki_Defs

open MaxwellWiki

namespace LU2Mx

open MeasureTheory

theorem timeDeriv_eq {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (Φ : ℝ × Vec3 → W) (t : ℝ) (x : Vec3)
    (h : DifferentiableAt ℝ Φ (t, x)) :
    deriv (fun s => Φ (s, x)) t = fderiv ℝ Φ (t, x) ((1 : ℝ), (0 : Vec3)) := by
  have h1 : HasDerivAt (Φ ∘ fun s => (s, x)) (fderiv ℝ Φ (t, x) ((1 : ℝ), (0 : Vec3))) t :=
    h.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  exact h1.deriv

theorem spaceDeriv_eq (Φ : ℝ × Vec3 → ℝ) (t : ℝ) (x : Vec3)
    (h : DifferentiableAt ℝ Φ (t, x)) (w : Vec3) :
    fderiv ℝ (fun y => Φ (t, y)) x w = fderiv ℝ Φ (t, x) ((0 : ℝ), w) := by
  have h3 : HasFDerivAt (fun y : Vec3 => ((t, y) : ℝ × Vec3))
      ((0 : Vec3 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Vec3)) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have h4 := h.hasFDerivAt.comp x h3
  rw [show (fun y => Φ (t, y)) = Φ ∘ (fun y : Vec3 => ((t, y) : ℝ × Vec3)) from rfl, h4.fderiv]
  simp

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem diff_fderiv (f : V → ℝ) (hf : ContDiff ℝ 2 f) : Differentiable ℝ (fderiv ℝ f) :=
  (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero

theorem diff_dir (f : V → ℝ) (hf : ContDiff ℝ 2 f) (b : V) :
    Differentiable ℝ (fun y => fderiv ℝ f y b) := fun y =>
  (diff_fderiv f hf y).clm_apply (differentiableAt_const b)

theorem cd_dir {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : V → W) (hf : ContDiff ℝ 2 f) (b : V) :
    ContDiff ℝ 1 (fun y => fderiv ℝ f y b) :=
  (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem pd2 (f : V → ℝ) (hf : ContDiff ℝ 2 f) (x a b : V) :
    fderiv ℝ (fun y => fderiv ℝ f y b) x a = fderiv ℝ (fderiv ℝ f) x a b := by
  rw [fderiv_clm_apply (diff_fderiv f hf x) (differentiableAt_const b)]
  simp

theorem sym (f : V → ℝ) (hf : ContDiff ℝ 2 f) (x a b : V) :
    fderiv ℝ (fderiv ℝ f) x a b = fderiv ℝ (fderiv ℝ f) x b a :=
  (hf.contDiffAt.isSymmSndFDerivAt (by simp)) a b

theorem mixed (f : Vec3 → ℝ) (hf : ContDiff ℝ 2 f) (x : Vec3) (a b : Fin 3) :
    partialDeriv a (fun y => partialDeriv b f y) x =
      partialDeriv b (fun y => partialDeriv a f y) x := by
  unfold partialDeriv
  rw [pd2 f hf, pd2 f hf, sym f hf]

theorem pd_sub (f g : Vec3 → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (a : Fin 3) (x : Vec3) :
    partialDeriv a (fun y => f y - g y) x = partialDeriv a f x - partialDeriv a g x := by
  unfold partialDeriv
  rw [fderiv_fun_sub (hf x) (hg x)]
  rfl

theorem pd_lin (f g : Vec3 → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (c d : ℝ) (a : Fin 3) (x : Vec3) :
    partialDeriv a (fun y => c * f y - d * g y) x = c * partialDeriv a f x - d * partialDeriv a g x := by
  unfold partialDeriv
  rw [fderiv_fun_sub ((hf x).const_mul c) ((hg x).const_mul d), fderiv_const_mul (hf x),
    fderiv_const_mul (hg x)]
  rfl

theorem diff_pd (f : Vec3 → ℝ) (hf : ContDiff ℝ 2 f) (b : Fin 3) :
    Differentiable ℝ (fun y => partialDeriv b f y) :=
  diff_dir f hf _

theorem div_eq (F : Vec3 → Vec3) (hF : ContDiff ℝ 1 F) (x : Vec3) :
    div F x = ∑ i, fderiv ℝ F x (Pi.single i 1) i := by
  unfold div
  apply Finset.sum_congr rfl
  intro i _
  unfold partialDeriv
  have h := (hF.differentiable one_ne_zero x).hasFDerivAt
  have h2 : HasFDerivAt ((fun v : Vec3 => v i) ∘ F)
      ((ContinuousLinearMap.proj i).comp (fderiv ℝ F x)) x :=
    (hasFDerivAt_apply i (F x)).comp x h
  rw [show (fun y => F y i) = (fun v : Vec3 => v i) ∘ F from rfl, h2.fderiv]
  rfl

theorem flux_eq (F : Vec3 → Vec3) (hF : ContDiff ℝ 1 F) (a b : Vec3) (hab : a ≤ b) :
    boxFlux F a b = ∫ x in Set.Icc a b, div F x := by
  rw [funext (div_eq F hF)]
  unfold boxFlux
  have hcont : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
  refine (MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable a b hab F (fderiv ℝ F) ∅
    Set.countable_empty hF.continuous.continuousOn ?_ ?_).symm
  · intro x _
    exact (hF.differentiable one_ne_zero x).hasFDerivAt
  · apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply Continuous.continuousOn
    apply continuous_finset_sum
    intro i _
    exact (continuous_apply i).comp (hcont.clm_apply continuous_const)

theorem amount_hasDeriv (ρ : ℝ → Vec3 → ℝ) (hρ : ContDiff ℝ 1 (Function.uncurry ρ))
    (a b : Vec3) (t : ℝ) :
    HasDerivAt (fun s => ∫ x in Set.Icc a b, ρ s x) (∫ x in Set.Icc a b, timeDeriv ρ t x) t := by
  have hd : Differentiable ℝ (Function.uncurry ρ) := hρ.differentiable one_ne_zero
  set G : ℝ × Vec3 → ℝ := fun q => fderiv ℝ (Function.uncurry ρ) q ((1 : ℝ), (0 : Vec3))
  have hG : Continuous G := (hρ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hTD : ∀ s y, timeDeriv ρ s y = G (s, y) := fun s y =>
    timeDeriv_eq (Function.uncurry ρ) s y (hd _)
  have hK : IsCompact (Set.Icc (t - 1) (t + 1) ×ˢ Set.Icc a b) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hG.continuousOn
  have hρs : ∀ s, Continuous (ρ s) := fun s =>
    hρ.continuous.comp (continuous_const.prodMk continuous_id)
  have hGs : ∀ s, Continuous (fun y => G (s, y)) := fun s =>
    hG.comp (continuous_const.prodMk continuous_id)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Icc a b)) (F := fun s y => ρ s y)
    (F' := fun s y => timeDeriv ρ s y) (x₀ := t) (bound := fun _ => M)
    (s := Metric.ball t 1) (Metric.ball_mem_nhds t one_pos)
    (Filter.Eventually.of_forall fun s => (hρs s).aestronglyMeasurable)
    ((hρs t).continuousOn.integrableOn_compact isCompact_Icc)
    (by simp_rw [hTD]; exact (hGs t).aestronglyMeasurable)
    (by
      refine (ae_restrict_of_forall_mem measurableSet_Icc ?_)
      intro y hy s hs
      rw [hTD]
      apply hM
      refine ⟨?_, hy⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
      constructor <;> linarith)
    (continuous_const.continuousOn.integrableOn_compact isCompact_Icc)
    (Filter.Eventually.of_forall fun y s _ =>
      (((hd _).comp s ((differentiableAt_id).prodMk (differentiableAt_const y))) :
        DifferentiableAt ℝ (fun r => ρ r y) s).hasDerivAt)
  exact key.2

end LU2Mx

open LU2Mx MeasureTheory in
theorem solution (ε₀ μ₀ : ℝ) (hε₀ : 0 < ε₀) (hμ₀ : 0 < μ₀)
    (E B J : ℝ → Vec3 → Vec3) (ρ : ℝ → Vec3 → ℝ)
    (hE : ContDiff ℝ 2 (Function.uncurry E)) (hB : ContDiff ℝ 2 (Function.uncurry B))
    (hM : IsMaxwellSolution ε₀ μ₀ E B J ρ) (a b : Vec3) (hab : a ≤ b) (t : ℝ) :
    HasDerivAt (fun s => ∫ x in Set.Icc a b, ρ s x) (-boxFlux (J t) a b) t := by
  have hε : ε₀ ≠ 0 := hε₀.ne'
  have hμ : μ₀ ≠ 0 := hμ₀.ne'
  set Φ : Fin 3 → ℝ × Vec3 → ℝ := fun i q => Function.uncurry E q i with hΦ
  have hΦc : ∀ i, ContDiff ℝ 2 (Φ i) := fun i => contDiff_pi.1 hE i
  have hΦd : ∀ i, Differentiable ℝ (Φ i) := fun i => (hΦc i).differentiable (by norm_num)
  have hEd : Differentiable ℝ (Function.uncurry E) := hE.differentiable (by norm_num)
  have hρE : ∀ s y, ρ s y = ε₀ * div (E s) y := by
    intro s y
    rw [hM.gauss]; field_simp
  have hTD : ∀ s y i, timeDeriv E s y i = fderiv ℝ (Φ i) (s, y) ((1 : ℝ), (0 : Vec3)) := by
    intro s y i
    have h1 : HasDerivAt (Function.uncurry E ∘ fun r => (r, y))
        (fderiv ℝ (Function.uncurry E) (s, y) ((1 : ℝ), (0 : Vec3))) s :=
      (hEd _).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s y))
    have h2 : HasFDerivAt ((fun v : Vec3 => v i) ∘ Function.uncurry E)
        ((ContinuousLinearMap.proj i).comp (fderiv ℝ (Function.uncurry E) (s, y))) (s, y) :=
      (hasFDerivAt_apply i _).comp (s, y) (hEd _).hasFDerivAt
    unfold timeDeriv
    rw [show (fun r => E r y) = Function.uncurry E ∘ fun r => (r, y) from rfl, h1.deriv,
      show Φ i = (fun v : Vec3 => v i) ∘ Function.uncurry E from rfl, h2.fderiv]
    rfl
  have hSD : ∀ s y i, partialDeriv i (fun z => E s z i) y =
      fderiv ℝ (Φ i) (s, y) ((0 : ℝ), (Pi.single i 1 : Vec3)) := by
    intro s y i
    unfold partialDeriv
    exact spaceDeriv_eq (Φ i) s y (hΦd i _) _
  -- ρ is C¹
  have hρc : ContDiff ℝ 1 (Function.uncurry ρ) := by
    have : Function.uncurry ρ = fun q => ε₀ * ∑ i, fderiv ℝ (Φ i) q ((0 : ℝ), (Pi.single i 1 : Vec3)) := by
      funext q
      obtain ⟨s, y⟩ := q
      simp only [Function.uncurry_apply_pair]
      rw [hρE]
      unfold div
      simp_rw [hSD]
    rw [this]
    exact contDiff_const.mul (ContDiff.sum fun i _ => cd_dir _ (hΦc i) _)
  -- pointwise continuity equation
  have hpt : ∀ x, timeDeriv ρ t x = -div (J t) x := by
    intro x
    have hcomm : ∀ i, partialDeriv i (fun y => timeDeriv E t y i) x =
        deriv (fun s => partialDeriv i (fun y => E s y i) x) t := by
      intro i
      simp_rw [hTD, hSD]
      unfold partialDeriv
      rw [spaceDeriv_eq (fun q => fderiv ℝ (Φ i) q ((1 : ℝ), (0 : Vec3))) t x
        (diff_dir _ (hΦc i) _ _), pd2 _ (hΦc i), sym _ (hΦc i), ← pd2 _ (hΦc i),
        ← timeDeriv_eq (fun q => fderiv ℝ (Φ i) q ((0 : ℝ), (Pi.single i 1 : Vec3))) t x
        (diff_dir _ (hΦc i) _ _)]
    have hρ : timeDeriv ρ t x =
        ε₀ * ∑ i, deriv (fun s => partialDeriv i (fun y => E s y i) x) t := by
      unfold timeDeriv
      have : (fun s => ρ s x) = fun s => ε₀ * ∑ i, partialDeriv i (fun y => E s y i) x := by
        funext s; rw [hρE]; rfl
      rw [this, deriv_const_mul]
      · rw [deriv_fun_sum]
        intro i _
        simp_rw [hSD]
        have hd := diff_dir _ (hΦc i) ((0 : ℝ), (Pi.single i 1 : Vec3))
        exact (hd _).comp t ((differentiableAt_id).prodMk (differentiableAt_const x))
      · apply DifferentiableAt.fun_sum
        intro i _
        simp_rw [hSD]
        have hd := diff_dir _ (hΦc i) ((0 : ℝ), (Pi.single i 1 : Vec3))
        exact (hd _).comp t ((differentiableAt_id).prodMk (differentiableAt_const x))
    have hTDd : ∀ i, Differentiable ℝ (fun y => timeDeriv E t y i) := by
      intro i
      simp_rw [hTD]
      intro y
      exact (diff_dir _ (hΦc i) _ _).comp y ((differentiableAt_const t).prodMk differentiableAt_id)
    have hBt : ContDiff ℝ 2 (B t) :=
      hB.comp (contDiff_const.prodMk contDiff_id)
    have hHc : ∀ k, ContDiff ℝ 2 (fun y => B t y k) := fun k => contDiff_pi.1 hBt k
    have hcurld : ∀ i, Differentiable ℝ (fun y => curl (B t) y i) := by
      intro i
      fin_cases i
      · exact (diff_pd _ (hHc 2) 1).sub (diff_pd _ (hHc 1) 2)
      · exact (diff_pd _ (hHc 0) 2).sub (diff_pd _ (hHc 2) 0)
      · exact (diff_pd _ (hHc 1) 0).sub (diff_pd _ (hHc 0) 1)
    have hJ : ∀ i, (fun y => J t y i) =
        fun y => μ₀⁻¹ * curl (B t) y i - ε₀ * timeDeriv E t y i := by
      intro i; funext y
      have := congrFun (hM.ampere_maxwell t y) i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this
      rw [this]; field_simp; ring
    have hdivJ : div (J t) x = ∑ i, (μ₀⁻¹ * partialDeriv i (fun y => curl (B t) y i) x -
        ε₀ * partialDeriv i (fun y => timeDeriv E t y i) x) := by
      unfold div
      apply Finset.sum_congr rfl
      intro i _
      rw [hJ i, pd_lin _ _ (hcurld i) (hTDd i)]
    have hdivcurl : ∑ i, partialDeriv i (fun y => curl (B t) y i) x = 0 := by
      rw [Fin.sum_univ_three]
      have e0 : (fun y => curl (B t) y 0) = fun y =>
          partialDeriv 1 (fun z => B t z 2) y - partialDeriv 2 (fun z => B t z 1) y := rfl
      have e1 : (fun y => curl (B t) y 1) = fun y =>
          partialDeriv 2 (fun z => B t z 0) y - partialDeriv 0 (fun z => B t z 2) y := rfl
      have e2 : (fun y => curl (B t) y 2) = fun y =>
          partialDeriv 0 (fun z => B t z 1) y - partialDeriv 1 (fun z => B t z 0) y := rfl
      rw [e0, e1, e2, pd_sub _ _ (diff_pd _ (hHc 2) 1) (diff_pd _ (hHc 1) 2),
        pd_sub _ _ (diff_pd _ (hHc 0) 2) (diff_pd _ (hHc 2) 0),
        pd_sub _ _ (diff_pd _ (hHc 1) 0) (diff_pd _ (hHc 0) 1),
        mixed _ (hHc 2) x 0 1, mixed _ (hHc 1) x 0 2, mixed _ (hHc 0) x 1 2]
      ring
    rw [hdivJ, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hdivcurl, hρ]
    simp_rw [hcomm]
    ring
  -- J t is C¹
  have hJc : ContDiff ℝ 1 (J t) := by
    have hBt : ContDiff ℝ 2 (B t) :=
      hB.comp (contDiff_const.prodMk contDiff_id)
    have hHc : ∀ k, ContDiff ℝ 2 (fun y => B t y k) := fun k => contDiff_pi.1 hBt k
    have hpd : ∀ k j : Fin 3, ContDiff ℝ 1 (fun y => partialDeriv j (fun z => B t z k) y) :=
      fun k j => cd_dir _ (hHc k) _
    rw [contDiff_pi]
    intro i
    have hJ : (fun y => J t y i) =
        fun y => μ₀⁻¹ * curl (B t) y i - ε₀ * fderiv ℝ (Φ i) (t, y) ((1 : ℝ), (0 : Vec3)) := by
      funext y
      have := congrFun (hM.ampere_maxwell t y) i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this
      rw [← hTD, this]; field_simp; ring
    rw [hJ]
    refine (contDiff_const.mul ?_).sub (contDiff_const.mul ?_)
    · fin_cases i
      · exact (hpd 2 1).sub (hpd 1 2)
      · exact (hpd 0 2).sub (hpd 2 0)
      · exact (hpd 1 0).sub (hpd 0 1)
    · exact (cd_dir _ (hΦc i) _).comp (contDiff_const.prodMk contDiff_id)
  have key := amount_hasDeriv ρ hρc a b t
  convert key using 1
  rw [flux_eq (J t) hJc a b hab, ← integral_neg]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hpt x).symm)
