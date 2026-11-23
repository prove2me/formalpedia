-- Prove2me | solution 1 for ManipPotential.proposition_6_11_rank
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:47:40.433958+00:00
-- url     : https://prove2.me/submissions/6791c86a-deb8-4872-8755-2a069b8cc673

import Mathlib
import Definitions.Def_ManipPotential_ExtRanking
import Definitions.Def_ManipPotential_cycTotal

open ManipPotential Filter
open scoped Topology

/-- Proposition 6.11, rank of the Jacobian, p.35. -/
theorem solution {m : ℕ} [NeZero m]
    (U : Set ((ExtRanking m → ℝ) × ℝ)) (hU : IsOpen U)
    (G : ((ExtRanking m → ℝ) × ℝ) → (Ranking m → ℝ))
    (hG : ∀ z ∈ U, (∀ s : ExtRanking m, G z s.1 = z.1 s) ∧ cycTotal (G z) = z.2) :
    ∀ z ∈ U, DifferentiableAt ℝ G z →
      Module.finrank ℝ (LinearMap.range (fderiv ℝ G z).toLinearMap) = m.factorial - m + 1 := by
  classical
  intro z hz hdiff
  let E := ExtRanking m → ℝ
  let X := Ranking m → ℝ
  let D : (E × ℝ) →L[ℝ] X := fderiv ℝ G z
  let ev : ExtRanking m → (X →L[ℝ] ℝ) := fun s => ContinuousLinearMap.proj s.1
  let ine : ExtRanking m → ((E × ℝ) →L[ℝ] ℝ) := fun s =>
    (ContinuousLinearMap.proj s).comp (ContinuousLinearMap.fst ℝ E ℝ)
  let cyc : X →L[ℝ] ℝ := ∑ j : Fin m, ContinuousLinearMap.proj (ell j)
  let inr : (E × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ E ℝ
  have hD : HasFDerivAt G D z := hdiff.hasFDerivAt
  have hext (s : ExtRanking m) : (ev s).comp D = ine s := by
    have hcomp : HasFDerivAt ((fun P : X => P s.1) ∘ G) ((ev s).comp D) z :=
      (ev s).hasFDerivAt.comp z hD
    have hEq : (fun w : E × ℝ => w.1 s) =ᶠ[𝓝 z] ((fun P : X => P s.1) ∘ G) := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact ((hG w hw).1 s).symm
    have hlocal := hcomp.congr_of_eventuallyEq hEq
    exact hlocal.unique (ine s).hasFDerivAt
  have hcyc : cyc.comp D = inr := by
    have hfun : (fun P : X => cyc P) = cycTotal := by
      funext P
      simp only [cyc, cycTotal, ContinuousLinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro j hj
      rfl
    have hcomp : HasFDerivAt (cyc ∘ G) (cyc.comp D) z :=
      cyc.hasFDerivAt.comp z hD
    have hEq : (fun w : E × ℝ => w.2) =ᶠ[𝓝 z] (cyc ∘ G) := by
      filter_upwards [hU.mem_nhds hz] with w hw
      simp only [Function.comp_apply, hfun]
      exact ((hG w hw).2).symm
    have hlocal := hcomp.congr_of_eventuallyEq hEq
    exact hlocal.unique inr.hasFDerivAt
  have h_inj : Function.Injective D.toLinearMap := by
    intro v w hvw
    change D v = D w at hvw
    have hzero : D (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have he : v.1 = w.1 := by
      funext s
      have h := congrArg (fun A : (E × ℝ) →L[ℝ] ℝ => A (v - w)) (hext s)
      simp only [ContinuousLinearMap.comp_apply, hzero, map_zero, ev, ine,
        ContinuousLinearMap.proj_apply, ContinuousLinearMap.coe_fst'] at h
      exact sub_eq_zero.mp h.symm
    have hr : v.2 = w.2 := by
      have h := congrArg (fun A : (E × ℝ) →L[ℝ] ℝ => A (v - w)) hcyc
      simp only [ContinuousLinearMap.comp_apply, hzero, map_zero, inr,
        ContinuousLinearMap.coe_snd'] at h
      exact sub_eq_zero.mp h.symm
    exact Prod.ext he hr
  rw [LinearMap.finrank_range_of_inj h_inj]
  rw [Module.finrank_prod, Module.finrank_pi, Module.finrank_self]
  congr 1
  let e : ExtRanking m ≃ {s : Ranking m // ¬ ∃ j, ell j = s} :=
    Equiv.subtypeEquivRight (by intro s; simp only [not_exists])
  rw [Fintype.card_congr e]
  rw [Fintype.card_subtype_compl (fun s : Ranking m => ∃ j, ell j = s)]
  have hell : Function.Injective (ell : Fin m → Ranking m) := by
    intro i j h
    simpa [ell] using congrArg (fun q : Ranking m => q 0) h
  have hrange : Fintype.card {s : Ranking m // ∃ j, ell j = s} = m := by
    let er : {s : Ranking m // ∃ j, ell j = s} ≃
        {s : Ranking m // s ∈ Finset.univ.image ell} :=
      Equiv.subtypeEquivRight (by intro s; simp)
    rw [Fintype.card_congr er, Fintype.card_subtype]
    simpa using Finset.card_image_of_injective Finset.univ hell
  rw [hrange]
  change Fintype.card (Equiv.Perm (Fin m)) - m = m.factorial - m
  rw [Fintype.card_perm, Fintype.card_fin]
