-- Prove2me | solution 1 for MaxwellWiki.continuity_equation
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:39:42.947165+00:00
-- url     : https://prove2.me/submissions/b49eaf65-e498-4994-85c5-ae4e11bd50ea

import Mathlib
import Definitions.Def_MaxwellWiki_Defs
set_option autoImplicit false
open MaxwellWiki

private theorem partial_diff (f : Vec3 → ℝ) (hf : ContDiff ℝ 2 f) (i : Fin 3) :
    Differentiable ℝ (partialDeriv i f) := by
  exact ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero).clm_apply (differentiable_const _)

private theorem partial_sub (f g : Vec3 → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : Fin 3) (x : Vec3) :
    partialDeriv i (fun y => f y - g y) x = partialDeriv i f x - partialDeriv i g x := by
  unfold partialDeriv
  rw [fderiv_fun_sub (hf x) (hg x)]
  rfl

private theorem partial_comm (f : Vec3 → ℝ) (hf : ContDiff ℝ 2 f)
    (i j : Fin 3) (x : Vec3) : partialDeriv i (partialDeriv j f) x = partialDeriv j (partialDeriv i f) x := by
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  unfold partialDeriv
  rw [fderiv_clm_apply (hd x) (differentiableAt_const _), fderiv_clm_apply (hd x) (differentiableAt_const _)]
  simpa using hf.contDiffAt.isSymmSndFDerivAt (by simp) (Pi.single i 1) (Pi.single j 1)

private theorem divcurl (F : Vec3 → Vec3) (hF : ContDiff ℝ 2 F) (x : Vec3) :
    div (curl F) x = 0 := by
  have hc (i : Fin 3) : ContDiff ℝ 2 (fun y => F y i) := (contDiff_apply ℝ ℝ i).comp hF
  change partialDeriv 0 (fun y => partialDeriv 1 (fun z => F z 2) y - partialDeriv 2 (fun z => F z 1) y) x +
    (partialDeriv 1 (fun y => partialDeriv 2 (fun z => F z 0) y - partialDeriv 0 (fun z => F z 2) y) x +
    (partialDeriv 2 (fun y => partialDeriv 0 (fun z => F z 1) y - partialDeriv 1 (fun z => F z 0) y) x + 0)) = 0
  rw [partial_sub _ _ (partial_diff _ (hc 2) 1) (partial_diff _ (hc 1) 2),
    partial_sub _ _ (partial_diff _ (hc 0) 2) (partial_diff _ (hc 2) 0),
    partial_sub _ _ (partial_diff _ (hc 1) 0) (partial_diff _ (hc 0) 1)]
  rw [partial_comm _ (hc 2) 0 1, partial_comm _ (hc 1) 0 2, partial_comm _ (hc 0) 1 2]
  ring


private theorem space_slice (f : (ℝ × Vec3) → ℝ) (hf : Differentiable ℝ f)
    (t : ℝ) (x : Vec3) (i : Fin 3) :
    partialDeriv i (fun y => f (t,y)) x = fderiv ℝ f (t,x) (0, Pi.single i 1) := by
  have hh := (hf (t,x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  unfold partialDeriv
  change HasFDerivAt (fun y => f (t,y)) _ x at hh
  rw [hh.fderiv]
  rfl

private theorem time_slice {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : (ℝ × Vec3) → V) (hf : Differentiable ℝ f) (t : ℝ) (x : Vec3) :
    deriv (fun s => f (s,x)) t = fderiv ℝ f (t,x) (1,0) := by
  have hh := (hf (t,x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  exact hh.deriv

private theorem dir_diff (f : (ℝ × Vec3) → ℝ) (hf : ContDiff ℝ 2 f) (v : ℝ × Vec3) :
    Differentiable ℝ (fun p => fderiv ℝ f p v) :=
  ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero).clm_apply (differentiable_const _)

private theorem mixed (f : (ℝ × Vec3) → ℝ) (hf : ContDiff ℝ 2 f)
    (t : ℝ) (x : Vec3) (i : Fin 3) :
    deriv (fun s => partialDeriv i (fun y => f (s,y)) x) t =
      partialDeriv i (fun y => deriv (fun s => f (s,y)) t) x := by
  have hd := hf.differentiable (by norm_num)
  have hs : (fun s => partialDeriv i (fun y => f (s,y)) x) =
      fun s => fderiv ℝ f (s,x) (0, Pi.single i 1) := funext fun s => space_slice f hd s x i
  have ht : (fun y => deriv (fun s => f (s,y)) t) =
      fun y => fderiv ℝ f (t,y) (1,0) := funext fun y => time_slice f hd t y
  rw [hs, ht, time_slice _ (dir_diff f hf _), space_slice _ (dir_diff f hf _)]
  have hd' := (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  rw [fderiv_clm_apply (hd' (t,x)) (differentiableAt_const _),
    fderiv_clm_apply (hd' (t,x)) (differentiableAt_const _)]
  simpa using hf.contDiffAt.isSymmSndFDerivAt (by simp) (1,0) (0,Pi.single i 1)

private theorem timecomm (F : ℝ → Vec3 → Vec3) (hF : ContDiff ℝ 2 (Function.uncurry F))
    (t : ℝ) (x : Vec3) :
    timeDeriv (fun s y => div (F s) y) t x = div (fun y => timeDeriv F t y) x := by
  have hc (i : Fin 3) : ContDiff ℝ 2 (fun p : ℝ × Vec3 => F p.1 p.2 i) :=
    (contDiff_apply ℝ ℝ i).comp hF
  have hd (i : Fin 3) : DifferentiableAt ℝ (fun s => partialDeriv i (fun y => F s y i) x) t := by
    have he : (fun s => partialDeriv i (fun y => F s y i) x) =
        fun s => fderiv ℝ (fun p : ℝ × Vec3 => F p.1 p.2 i) (s,x) (0,Pi.single i 1) :=
      funext fun s => space_slice _ ((hc i).differentiable (by norm_num)) s x i
    rw [he]
    exact ((dir_diff _ (hc i) _).comp ((differentiable_id).prodMk (differentiable_const x))).differentiableAt
  have htime (y : Vec3) : timeDeriv F t y = fun i => deriv (fun s => F s y i) t := by
    unfold timeDeriv
    apply deriv_pi
    intro i
    exact (((hc i).differentiable (by norm_num)).comp
      (differentiable_id.prodMk (differentiable_const y))).differentiableAt
  change deriv (fun s => ∑ i, partialDeriv i (fun y => F s y i) x) t = _
  rw [deriv_fun_sum (fun i _ => hd i)]
  unfold div
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [htime]
  exact mixed _ (hc i) t x i

private theorem div_linear (F G : Vec3 → Vec3) (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (a b : ℝ) (x : Vec3) :
    div (fun y => a • F y - b • G y) x = a * div F x - b * div G x := by
  unfold div
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold partialDeriv
  have hf := differentiable_pi.mp hF i
  have hg := differentiable_pi.mp hG i
  change fderiv ℝ (fun y => a • F y i - b • G y i) x (Pi.single i 1) = _
  have hfa : DifferentiableAt ℝ (fun y => a • F y i) x := (hf x).const_smul a
  have hgb : DifferentiableAt ℝ (fun y => b • G y i) x := (hg x).const_smul b
  rw [fderiv_fun_sub hfa hgb,
    fderiv_fun_const_smul (hf x) a, fderiv_fun_const_smul (hg x) b]
  rfl

private theorem curl_diff (F : Vec3 → Vec3) (hF : ContDiff ℝ 2 F) : Differentiable ℝ (curl F) := by
  have hc (i : Fin 3) : ContDiff ℝ 2 (fun y => F y i) := (contDiff_apply ℝ ℝ i).comp hF
  apply differentiable_pi.mpr
  intro i
  fin_cases i
  · exact (partial_diff _ (hc 2) 1).sub (partial_diff _ (hc 1) 2)
  · exact (partial_diff _ (hc 0) 2).sub (partial_diff _ (hc 2) 0)
  · exact (partial_diff _ (hc 1) 0).sub (partial_diff _ (hc 0) 1)

private theorem time_diff (F : ℝ → Vec3 → Vec3) (hF : ContDiff ℝ 2 (Function.uncurry F)) (t : ℝ) :
    Differentiable ℝ (fun y => timeDeriv F t y) := by
  have he : (fun y => timeDeriv F t y) =
      fun y => fderiv ℝ (Function.uncurry F) (t,y) (1,0) :=
    funext fun y => time_slice _ (hF.differentiable (by norm_num)) t y
  rw [he]
  exact (((hF.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero).clm_apply
    (differentiable_const _)).comp ((differentiable_const t).prodMk differentiable_id)

theorem solution (ε₀ μ₀ : ℝ) (hε₀ : 0 < ε₀) (hμ₀ : 0 < μ₀)
    (E B J : ℝ → Vec3 → Vec3) (ρ : ℝ → Vec3 → ℝ)
    (hE : ContDiff ℝ 2 (Function.uncurry E)) (hB : ContDiff ℝ 2 (Function.uncurry B))
    (hM : IsMaxwellSolution ε₀ μ₀ E B J ρ) (t : ℝ) (x : Vec3) :
    timeDeriv ρ t x + div (J t) x = 0 := by
  have hBt : ContDiff ℝ 2 (B t) := hB.comp ((contDiff_const).prodMk contDiff_id)
  have hJ : J t = fun y => μ₀⁻¹ • curl (B t) y - ε₀ • timeDeriv E t y := by
    funext y
    have hh := congrArg (fun z : Vec3 => μ₀⁻¹ • z) (hM.ampere_maxwell t y)
    simp only [smul_smul, inv_mul_cancel₀ hμ₀.ne', one_smul] at hh
    exact eq_sub_iff_add_eq.mpr hh.symm
  have hρ : (fun s => ρ s x) = fun s => ε₀ * div (E s) x := by
    funext s
    have hh := (div_eq_iff hε₀.ne').mp (hM.gauss s x).symm
    nlinarith
  change deriv (fun s => ρ s x) t + div (J t) x = 0
  rw [hρ, deriv_const_mul_field, hJ,
    div_linear _ _ (curl_diff _ hBt) (time_diff E hE t), divcurl _ hBt x]
  change ε₀ * timeDeriv (fun s y => div (E s) y) t x +
    (μ₀⁻¹ * 0 - ε₀ * div (fun y => timeDeriv E t y) x) = 0
  rw [timecomm E hE t x]
  ring
