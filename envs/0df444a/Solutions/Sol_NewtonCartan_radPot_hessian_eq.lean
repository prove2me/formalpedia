-- Prove2me | solution 1 for NewtonCartan.radPot_hessian_eq
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T07:20:56.91828+00:00
-- url     : https://prove2.me/submissions/de0b982c-0bff-4558-a845-8c6577f2ccaa

import Definitions.Def_NewtonCartan_defs
import Theorems.Thm_NewtonCartan_exists_potential_of_closed_hessian_Sp
import Theorems.Thm_NewtonCartan_contDiff_integral_I01
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open scoped ContDiff BigOperators Topology Interval
open Classical MeasureTheory Set Filter ContinuousLinearMap
open NewtonCartan

lemma fderiv_apply_const {φ : Sp → ℝ} {z : Sp} (h : DifferentiableAt ℝ (fderiv ℝ φ) z)
    (v u : Sp) :
    fderiv ℝ (fun w => fderiv ℝ φ w v) z u = fderiv ℝ (fderiv ℝ φ) z u v := by
  have hA := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp z h.hasFDerivAt
  exact congrArg (fun L : Sp →L[ℝ] ℝ => L u) hA.fderiv

lemma iteratedFDeriv_two_eq_hess_sum (φ : Sp → ℝ) (hφ : ContDiff ℝ 2 φ)
    (z y : Sp) :
    iteratedFDeriv ℝ 2 φ z (fun _ => y) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        fderiv ℝ (fun w => fderiv ℝ φ w (Pi.single i 1)) z (Pi.single j 1) * y i * y j := by
  rw [iteratedFDeriv_two_apply]
  have hle : (1 : ℕ∞ω) + 1 ≤ 2 := by decide
  have hdiff : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    ((hφ.fderiv_right (m := 1) hle).differentiable (by decide)).differentiableAt
  have hfderiv : ∀ y, HasFDerivAt φ (fderiv ℝ φ y) y := fun y =>
    ((hφ.differentiable (by decide)).differentiableAt).hasFDerivAt
  have hf'' : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) z) z := hdiff.hasFDerivAt
  let cy i : ℝ := y i
  have hy : y = ∑ i : Fin 3, cy i • Pi.single i (1 : ℝ) := by
    ext m; simp [cy, Finset.sum_apply, Pi.single_apply]
  have hL : fderiv ℝ (fderiv ℝ φ) z y =
      ∑ i : Fin 3, cy i • fderiv ℝ (fderiv ℝ φ) z (Pi.single i 1) := by
    calc fderiv ℝ (fderiv ℝ φ) z y
        = fderiv ℝ (fderiv ℝ φ) z (∑ i : Fin 3, cy i • Pi.single i (1 : ℝ)) := by rw [hy]
      _ = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ φ) z (cy i • Pi.single i (1 : ℝ)) := by rw [map_sum]
      _ = ∑ i : Fin 3, cy i • fderiv ℝ (fderiv ℝ φ) z (Pi.single i 1) := by
            refine Finset.sum_congr rfl fun i _ => by rw [map_smul]
  have hsum :
      (fderiv ℝ (fderiv ℝ φ) z y) y =
        ∑ i : Fin 3, ∑ j : Fin 3,
          fderiv ℝ (fderiv ℝ φ) z (Pi.single i 1) (Pi.single j 1) * cy i * cy j := by
    calc (fderiv ℝ (fderiv ℝ φ) z y) y
        = (∑ i : Fin 3, cy i • fderiv ℝ (fderiv ℝ φ) z (Pi.single i 1)) y := by rw [hL]
      _ = ∑ i : Fin 3, cy i * fderiv ℝ (fderiv ℝ φ) z (Pi.single i 1) y := by
            simp [smul_eq_mul]
      _ = ∑ i : Fin 3, cy i * ∑ j : Fin 3, cy j *
            fderiv ℝ (fderiv ℝ φ) z (Pi.single i 1) (Pi.single j 1) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            congr 1
            calc fderiv ℝ (fderiv ℝ φ) z (Pi.single i 1) y
                = fderiv ℝ (fderiv ℝ φ) z (Pi.single i 1)
                    (∑ j : Fin 3, cy j • Pi.single j (1 : ℝ)) := by rw [hy]
              _ = ∑ j : Fin 3, cy j *
                    fderiv ℝ (fderiv ℝ φ) z (Pi.single i 1) (Pi.single j 1) := by
                    rw [map_sum]
                    refine Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
            fderiv ℝ (fderiv ℝ φ) z (Pi.single i 1) (Pi.single j 1) * cy i * cy j := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
  calc (fderiv ℝ (fderiv ℝ φ) z y) y
      = ∑ i : Fin 3, ∑ j : Fin 3,
          fderiv ℝ (fderiv ℝ φ) z (Pi.single i 1) (Pi.single j 1) * cy i * cy j := hsum
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
          fderiv ℝ (fderiv ℝ φ) z (Pi.single j 1) (Pi.single i 1) * y i * y j := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [second_derivative_symmetric hfderiv hf'' (Pi.single i 1) (Pi.single j 1)]
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
          fderiv ℝ (fun w => fderiv ℝ φ w (Pi.single i 1)) z (Pi.single j 1) * y i * y j := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [fderiv_apply_const hdiff]

lemma contDiff_radIntegrand_H (H : Sp → Fin 3 → Fin 3 → ℝ) (hH : ContDiff ℝ ∞ H)
    (i j : Fin 3) :
    ContDiff ℝ ∞ (fun p : Sp × ℝ =>
      (1 - p.2) * H (p.2 • p.1) i j * p.1 i * p.1 j) := by
  have hHij : ContDiff ℝ ∞ (fun z : Sp => H z i j) :=
    (contDiff_apply (𝕜 := ℝ) (E := ℝ) (ι := Fin 3) j).comp
      ((contDiff_apply (𝕜 := ℝ) (E := Fin 3 → ℝ) (ι := Fin 3) i).comp hH)
  have hsmul : ContDiff ℝ ∞ (fun p : Sp × ℝ => p.2 • p.1) := by fun_prop
  have hHs : ContDiff ℝ ∞ (fun p : Sp × ℝ => H (p.2 • p.1) i j) := hHij.comp hsmul
  have h1s : ContDiff ℝ ∞ (fun p : Sp × ℝ => (1 - p.2 : ℝ)) := by fun_prop
  have hyi : ContDiff ℝ ∞ (fun p : Sp × ℝ => p.1 i) := by fun_prop
  have hyj : ContDiff ℝ ∞ (fun p : Sp × ℝ => p.1 j) := by fun_prop
  exact (((h1s.mul hHs).mul hyi).mul hyj)

lemma contDiff_radPot (H : Sp → Fin 3 → Fin 3 → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun y : Sp =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ s in (0 : ℝ)..1, (1 - s) * H (s • y) i j * y i * y j) := by
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  have hg := contDiff_radIntegrand_H H hH i j
  simpa using contDiff_integral_I01 (E := Sp) (⊤ : ℕ∞)
    (fun y s => (1 - s) * H (s • y) i j * y i * y j) hg

noncomputable def potAdj (ψ : Sp → ℝ) : Sp → ℝ :=
  fun y => ψ y - ψ 0 - fderiv ℝ ψ 0 y

lemma hasFDerivAt_potAdj (ψ : Sp → ℝ) {z : Sp} (h : DifferentiableAt ℝ ψ z) :
    HasFDerivAt (potAdj ψ) (fderiv ℝ ψ z - fderiv ℝ ψ 0) z := by
  have hψ := h.hasFDerivAt
  have hc : HasFDerivAt (fun _ : Sp => ψ 0) (0 : Sp →L[ℝ] ℝ) z := hasFDerivAt_const _ _
  have hL : HasFDerivAt (fun y : Sp => fderiv ℝ ψ 0 y) (fderiv ℝ ψ 0) z :=
    (fderiv ℝ ψ 0).hasFDerivAt
  have h1 : HasFDerivAt (fun y => ψ y - ψ 0) (fderiv ℝ ψ z - 0) z := hψ.sub hc
  have h2 : HasFDerivAt (fun y => ψ y - ψ 0 - fderiv ℝ ψ 0 y)
      ((fderiv ℝ ψ z - 0) - fderiv ℝ ψ 0) z := h1.sub hL
  change HasFDerivAt (fun y => ψ y - ψ 0 - fderiv ℝ ψ 0 y) _ z
  convert h2
  ext v
  simp only [sub_zero]

lemma potAdj_fderiv (ψ : Sp → ℝ) {z : Sp} (h : DifferentiableAt ℝ ψ z) :
    fderiv ℝ (potAdj ψ) z = fderiv ℝ ψ z - fderiv ℝ ψ 0 :=
  (hasFDerivAt_potAdj ψ h).fderiv

lemma potAdj_fderiv_zero (ψ : Sp → ℝ) (h : DifferentiableAt ℝ ψ 0) :
    fderiv ℝ (potAdj ψ) 0 = 0 := by
  rw [potAdj_fderiv ψ h, sub_self]

lemma potAdj_zero (ψ : Sp → ℝ) : potAdj ψ 0 = 0 := by
  simp [potAdj]

lemma potAdj_hessian (ψ : Sp → ℝ) (hψ : ContDiff ℝ ∞ ψ) (y : Sp) (i j : Fin 3) :
    fderiv ℝ (fun z => fderiv ℝ (potAdj ψ) z (Pi.single i 1)) y (Pi.single j 1) =
      fderiv ℝ (fun z => fderiv ℝ ψ z (Pi.single i 1)) y (Pi.single j 1) := by
  have hdiff : Differentiable ℝ ψ := hψ.differentiable (by decide)
  have hfun :
      (fun z => fderiv ℝ (potAdj ψ) z (Pi.single i 1)) =
        fun z => fderiv ℝ ψ z (Pi.single i 1) - fderiv ℝ ψ 0 (Pi.single i 1) := by
    funext z
    rw [potAdj_fderiv ψ (hdiff.differentiableAt), sub_apply]
  rw [hfun]
  have hle : (1 : ℕ∞ω) + 1 ≤ ∞ := by decide
  have hD : DifferentiableAt ℝ (fun z => fderiv ℝ ψ z (Pi.single i 1)) y :=
    ((hψ.fderiv_right (m := 1) hle).differentiable (by decide)).differentiableAt.clm_apply
      (differentiableAt_const _)
  let c : ℝ := fderiv ℝ ψ 0 (Pi.single i 1)
  have hsub : HasFDerivAt (fun z => fderiv ℝ ψ z (Pi.single i 1) - c)
      (fderiv ℝ (fun z => fderiv ℝ ψ z (Pi.single i 1)) y - 0) y :=
    hD.hasFDerivAt.sub (hasFDerivAt_const c y)
  have hgoal :
      fderiv ℝ (fun z => fderiv ℝ ψ z (Pi.single i 1) - c) y =
        fderiv ℝ (fun z => fderiv ℝ ψ z (Pi.single i 1)) y := by
    convert hsub.fderiv
    ext; simp only [sub_zero]
  rw [hgoal]

lemma taylor_order2_of_zero_jet (f : Sp → ℝ) (hf : ContDiff ℝ ∞ f)
    (hz : f 0 = 0) (hd0 : fderiv ℝ f 0 = 0) (y : Sp) :
    f y = ∫ t in (0 : ℝ)..1, (1 - t) • iteratedFDeriv ℝ 2 f (t • y) (fun _ => y) := by
  have hAt : ∀ (t : ℝ) (_ : t ∈ Icc (0 : ℝ) 1), ContDiffAt ℝ 2 f (0 + t • y) :=
    fun t _ => hf.contDiffAt.of_le (by decide)
  have hT := map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := (0 : Sp)) (y := y) (n := 1) hAt
  have hsum :
      ∑ k ∈ Finset.range (1 + 1), ((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k f 0 (fun _ => y) = 0 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
      iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply, hd0, zero_apply, hz, add_zero]
  simp only [zero_add] at hT
  rw [hsum, zero_add, Nat.factorial_one, Nat.cast_one, inv_one, one_smul] at hT
  convert hT using 1
  congr 1
  ext t
  simp only [pow_one, Nat.reduceAdd]

theorem solution
    (H : Sp → Fin 3 → Fin 3 → ℝ) (hH : ContDiff ℝ ∞ H)
    (hsym : ∀ y i j, H y i j = H y j i)
    (hclosed : ∀ y i j k,
      fderiv ℝ (fun z => H z i j) y (Pi.single k 1) =
        fderiv ℝ (fun z => H z i k) y (Pi.single j 1)) :
    let φ : Sp → ℝ := fun y =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ s in (0 : ℝ)..1, (1 - s) * H (s • y) i j * y i * y j
    ContDiff ℝ ∞ φ ∧
      ∀ y i j, fderiv ℝ (fun z => fderiv ℝ φ z (Pi.single i 1)) y (Pi.single j 1) =
        H y i j := by
  refine ⟨contDiff_radPot H hH, fun y₀ i j => ?_⟩
  obtain ⟨ψ, hψ, hhess⟩ := exists_potential_of_closed_hessian_Sp H hH hsym hclosed
  have hAdjHess : ∀ y a b,
      fderiv ℝ (fun z => fderiv ℝ (potAdj ψ) z (Pi.single a 1)) y (Pi.single b 1) =
        H y a b := fun y a b => (potAdj_hessian ψ hψ y a b).trans (hhess y a b)
  have hAdjCont : ContDiff ℝ ∞ (potAdj ψ) :=
    (hψ.sub contDiff_const).sub (ContinuousLinearMap.contDiff (fderiv ℝ ψ 0))
  set φ : Sp → ℝ := fun y =>
    ∑ i : Fin 3, ∑ j : Fin 3,
      ∫ s in (0 : ℝ)..1, (1 - s) * H (s • y) i j * y i * y j
  have hEq : φ = potAdj ψ := by
    funext y
    have hT := taylor_order2_of_zero_jet (potAdj ψ) hAdjCont (potAdj_zero ψ)
      (potAdj_fderiv_zero ψ (hψ.differentiable (by decide)).differentiableAt) y
    have hExp (t : ℝ) :
        iteratedFDeriv ℝ 2 (potAdj ψ) (t • y) (fun _ => y) =
          ∑ a : Fin 3, ∑ b : Fin 3, H (t • y) a b * y a * y b := by
      rw [iteratedFDeriv_two_eq_hess_sum (potAdj ψ) (hAdjCont.of_le (by decide))]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hAdjHess]
    have hCont (a b : Fin 3) : Continuous fun t : ℝ =>
        (1 - t) * H (t • y) a b * y a * y b := by
      have hHij : Continuous fun z : Sp => H z a b :=
        ((contDiff_apply (𝕜 := ℝ) (E := ℝ) (ι := Fin 3) b).comp
          ((contDiff_apply (𝕜 := ℝ) (E := Fin 3 → ℝ) (ι := Fin 3) a).comp hH)).continuous
      exact (((continuous_const.sub continuous_id).mul (hHij.comp (by fun_prop))).mul
        continuous_const).mul continuous_const
    have hswap :
        ∫ t in (0 : ℝ)..1, ∑ a : Fin 3, ∑ b : Fin 3, (1 - t) * H (t • y) a b * y a * y b =
          ∑ a : Fin 3, ∑ b : Fin 3,
            ∫ t in (0 : ℝ)..1, (1 - t) * H (t • y) a b * y a * y b := by
      have h1 := @intervalIntegral.integral_finsetSum ℝ _ _ (0:ℝ) 1 volume (Fin 3)
        Finset.univ (fun a t => ∑ b : Fin 3, (1 - t) * H (t • y) a b * y a * y b)
        (fun a _ => Continuous.intervalIntegrable
          (continuous_finsetSum _ fun b _ => hCont a b) _ _)
      rw [h1]
      refine Finset.sum_congr rfl fun a _ =>
        @intervalIntegral.integral_finsetSum ℝ _ _ (0:ℝ) 1 volume (Fin 3)
          Finset.univ (fun b t => (1 - t) * H (t • y) a b * y a * y b)
          (fun b _ => (hCont a b).intervalIntegrable _ _)
    calc φ y
        = ∑ a : Fin 3, ∑ b : Fin 3,
            ∫ t in (0 : ℝ)..1, (1 - t) * H (t • y) a b * y a * y b := rfl
      _ = ∫ t in (0 : ℝ)..1, ∑ a : Fin 3, ∑ b : Fin 3, (1 - t) * H (t • y) a b * y a * y b :=
            hswap.symm
      _ = ∫ t in (0 : ℝ)..1, (1 - t) • iteratedFDeriv ℝ 2 (potAdj ψ) (t • y) (fun _ => y) := by
            congr 1; ext t
            symm
            rw [hExp t, Finset.smul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl fun b _ => by simp only [smul_eq_mul]; ring
      _ = potAdj ψ y := hT.symm
  -- Goal is Hessian of φ; rewrite to potAdj
  have hfd1 : fderiv ℝ φ = fderiv ℝ (potAdj ψ) := by rw [hEq]
  have hfd2 : (fun z => fderiv ℝ φ z (Pi.single i 1)) =
      fun z => fderiv ℝ (potAdj ψ) z (Pi.single i 1) := by
    funext z; rw [hfd1]
  rw [hfd2]
  exact hAdjHess y₀ i j
