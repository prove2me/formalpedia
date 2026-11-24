-- Prove2me | solution 1 for GlobalTheory.AnalyticLineDerivative.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:13:25.434876+00:00
-- url     : https://prove2.me/submissions/5fb7e1b1-84c8-4770-b7ab-1ab440dc7bf7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_Imports
import Theorems.Thm_GlobalTheory_AnalyticLineDerivative_hasDerivAt_line
import Theorems.Thm_GlobalTheory_AnalyticLineDerivative_analyticAt_eval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AnalyticLineDerivative
open MvPolynomial
universe u_1 u_2 u_3 u_4
namespace GlobalTheory.AnalyticLineDerivative
theorem _root_.solution {E : Type u_1} {S : Type u_2} {J : Type u_3} {σ : Type u_4}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [CommRing S] [Fintype J]
    [Fintype σ] [DecidableEq σ] (χ : E → S →+* ℂ) (rel : σ → MvPolynomial J S) (c : σ → J)
    (hc : Function.Bijective c) (z₀ : E) (u₀ : J → ℂ)
    (han : ∀ a : S, AnalyticAt ℂ (fun z : E => χ z a) z₀)
    (hdet : Matrix.det (Matrix.of fun s r : σ =>
      eval₂Hom (χ z₀) u₀ (pderiv (c s) (rel r))) ≠ 0) :
    ∃ Φ : OpenPartialHomeomorph (E × (J → ℂ)) (E × (σ → ℂ)),
      (∀ w : E × (J → ℂ), Φ w = (w.1, fun r : σ => eval₂Hom (χ w.1) w.2 (rel r))) ∧
        (z₀, u₀) ∈ Φ.source ∧ AnalyticOnNhd ℂ Φ.symm Φ.target := by
  classical
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  set G : E × (J → ℂ) → (σ → ℂ) := fun w r => eval₂Hom (χ w.1) w.2 (rel r)
  set F : E × (J → ℂ) → E × (σ → ℂ) := fun w => (w.1, G w)
  set a₀ : E × (J → ℂ) := (z₀, u₀)
  have hGan : AnalyticAt ℂ G a₀ := AnalyticAt.pi fun r => analyticAt_eval χ z₀ u₀ han (rel r)
  have hFan : AnalyticAt ℂ F a₀ := analyticAt_fst.prod hGan
  have hGd : HasFDerivAt G (fderiv ℂ G a₀) a₀ := hGan.differentiableAt.hasFDerivAt

  have hdirG : ∀ v : J → ℂ, fderiv ℂ G a₀ (0, v) =
      fun r => ∑ j, v j * eval₂Hom (χ z₀) u₀ (pderiv j (rel r)) := by
    intro v
    have hℓ : HasDerivAt (fun t : ℂ => ((z₀, u₀ + t • v) : E × (J → ℂ))) ((0 : E), (1 : ℂ) • v) 0 :=
      (hasDerivAt_const (0 : ℂ) z₀).prodMk (((hasDerivAt_id (0 : ℂ)).smul_const v).const_add u₀)
    have hcomp := hGd.comp_hasDerivAt_of_eq 0 hℓ (by simp [a₀])
    rw [one_smul] at hcomp
    funext r
    exact ((hasDerivAt_pi.mp hcomp) r).unique (hasDerivAt_line (χ z₀) u₀ v (rel r))
  set L : E × (J → ℂ) →L[ℂ] E × (σ → ℂ) :=
    (ContinuousLinearMap.fst ℂ E (J → ℂ)).prod (fderiv ℂ G a₀)
  have hFd : HasFDerivAt F L a₀ := hasFDerivAt_fst.prodMk hGd

  have hLinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).mpr ?_
    rintro ⟨h, v⟩ hw
    have hh : h = 0 := by simpa [L] using congrArg Prod.fst hw
    subst hh
    have hv : fderiv ℂ G a₀ (0, v) = 0 := by simpa [L] using congrArg Prod.snd hw
    rw [hdirG] at hv
    have hzero : Matrix.vecMul (fun s => v (c s))
        (Matrix.of fun s r : σ => eval₂Hom (χ z₀) u₀ (pderiv (c s) (rel r))) = 0 := by
      funext r
      have hr := congrFun hv r
      simp only [Pi.zero_apply] at hr ⊢
      rw [← hr]
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply]
      exact (Equiv.ofBijective c hc).sum_comp
        (fun j => v j * eval₂Hom (χ z₀) u₀ (pderiv j (rel r)))
    have hvc : (fun s => v (c s)) = 0 := by
      by_contra hne
      exact hdet (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hne, hzero⟩)
    have hv0 : v = 0 := by
      funext j
      obtain ⟨s, rfl⟩ := hc.2 j
      exact congrFun hvc s
    subst hv0
    rfl
  have hrank : Module.finrank ℂ (E × (J → ℂ)) = Module.finrank ℂ (E × (σ → ℂ)) := by
    simp [Module.finrank_prod, Fintype.card_of_bijective hc]
  have hLsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank
      (f := (L : E × (J → ℂ) →ₗ[ℂ] E × (σ → ℂ)))).mp hLinj
  let i : (E × (J → ℂ)) ≃L[ℂ] (E × (σ → ℂ)) :=
    (LinearEquiv.ofBijective (L : E × (J → ℂ) →ₗ[ℂ] E × (σ → ℂ))
      ⟨hLinj, hLsurj⟩).toContinuousLinearEquiv
  have hi : (i : E × (J → ℂ) →L[ℂ] E × (σ → ℂ)) = L := ContinuousLinearMap.ext fun _ => rfl
  have hstrict : HasStrictFDerivAt F (i : E × (J → ℂ) →L[ℂ] E × (σ → ℂ)) a₀ := by
    rw [hi, ← hFd.fderiv]
    exact hFan.hasStrictFDerivAt

  have hev : ∀ᶠ w in nhds a₀, AnalyticAt ℂ F w ∧
      ∃ j : (E × (J → ℂ)) ≃L[ℂ] (E × (σ → ℂ)), fderiv ℂ F w = j := by
    refine hFan.eventually_analyticAt.and ?_
    have hmem : fderiv ℂ F a₀ ∈
        Set.range ((↑) : ((E × (J → ℂ)) ≃L[ℂ] (E × (σ → ℂ))) → E × (J → ℂ) →L[ℂ] E × (σ → ℂ)) :=
      ⟨i, by rw [hi, hFd.fderiv]⟩
    refine (hFan.fderiv.continuousAt.eventually_mem
      (ContinuousLinearEquiv.isOpen.mem_nhds hmem)).mono fun w hw => ?_
    obtain ⟨j, hj⟩ := hw
    exact ⟨j, hj.symm⟩
  obtain ⟨U, hUsub, hUopen, ha₀U⟩ := mem_nhds_iff.mp hev
  refine ⟨(hstrict.toOpenPartialHomeomorph F).restrOpen U hUopen, fun w => rfl, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hstrict.mem_toOpenPartialHomeomorph_source, ha₀U⟩
  · intro b hb
    have hsrc := ((hstrict.toOpenPartialHomeomorph F).restrOpen U hUopen).map_target hb
    rw [OpenPartialHomeomorph.restrOpen_source] at hsrc
    obtain ⟨hA, j, hj⟩ := hUsub hsrc.2
    exact ((hstrict.toOpenPartialHomeomorph F).restrOpen U hUopen).analyticAt_symm hb hA hj
end GlobalTheory.AnalyticLineDerivative
