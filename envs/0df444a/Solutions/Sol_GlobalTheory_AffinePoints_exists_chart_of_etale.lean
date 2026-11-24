-- Prove2me | solution 1 for GlobalTheory.AffinePoints.exists_chart_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:10:40.585452+00:00
-- url     : https://prove2.me/submissions/4fec19c7-b297-4a35-8c47-6a918ada2041

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ContinuousAevalMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
import Theorems.Thm_GlobalTheory_AffinePoints_analyticAt_aevalTower
import Theorems.Thm_GlobalTheory_AffinePoints_hasDerivAt_aevalTower_line
import Theorems.Thm_GlobalTheory_AffinePoints_exists_openPartialHomeomorph_analytic
import Theorems.Thm_GlobalTheory_AffinePoints_continuousOn_iff
import Theorems.Thm_GlobalTheory_AffinePoints_continuous_coords


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable [CompleteSpace 𝕜] {A : Type*} [CommRing A] [Algebra 𝕜 A] {d : ℕ}
namespace GlobalTheory.AffinePoints
theorem _root_.solution (g : MvPolynomial (Fin d) 𝕜 →ₐ[𝕜] A) (hg : g.Etale)
    (p : A →ₐ[𝕜] 𝕜) :
    ∃ e : OpenPartialHomeomorph (A →ₐ[𝕜] 𝕜) (Fin d → 𝕜), p ∈ e.source ∧
      (e : (A →ₐ[𝕜] 𝕜) → Fin d → 𝕜) = coords g ∧
      ∀ a, AnalyticOnNhd 𝕜 (fun z => e.symm z a) e.target := by
  classical
  letI : Algebra (MvPolynomial (Fin d) 𝕜) A := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) 𝕜) A := hg
  haveI : IsScalarTower 𝕜 (MvPolynomial (Fin d) 𝕜) A :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  obtain ⟨ι, σ, _, _, P, hP⟩ := (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.1
    ‹Algebra.Etale (MvPolynomial (Fin d) 𝕜) A›).out
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite σ
  have hcard : Fintype.card σ = Fintype.card ι := by
    have := P.card_relations_le_card_vars_of_isFinite
    simp only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card] at this hP
    omega
  have hbij : Function.Bijective P.map :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨P.map_inj, hcard⟩
  let π : MvPolynomial ι (MvPolynomial (Fin d) 𝕜) →ₐ[𝕜] A := (aeval P.val).restrictScalars 𝕜
  have hπ : Function.Surjective π := P.aeval_val_surjective
  let ev : (Fin d → 𝕜) × (ι → 𝕜) → (MvPolynomial ι (MvPolynomial (Fin d) 𝕜) →ₐ[𝕜] 𝕜) :=
    fun w => aevalTower (aeval w.1) w.2
  let j : (A →ₐ[𝕜] 𝕜) → (Fin d → 𝕜) × (ι → 𝕜) := fun q => (coords g q, fun i => q (P.val i))
  have hjc : Continuous j :=
    (continuous_coords g).prodMk (continuous_pi fun _ => continuous_eval _)
  have hevj : ∀ q, ev (j q) = comap π q := by
    intro q
    refine MvPolynomial.algHom_ext' ?_ ?_
    · ext i
      simp [ev, j, π, RingHom.algebraMap_toAlgebra]
    · intro i; simp [ev, j, π]
  have hker : ∀ a, π a = 0 ↔ a ∈ Ideal.span (range P.relation) := by
    intro a
    rw [P.span_range_relation_eq_ker]
    rw [P.ker_eq_ker_aeval_val]
    rfl
  have hex : ∀ w, (∀ r, ev w (P.relation r) = 0) → ∃ q, j q = w ∧ comap π q = ev w := by
    intro w hw
    obtain ⟨q, hq⟩ := exists_comap_eq_of_surjective π hπ (ev w) fun a ha => by
      have : Ideal.span (range P.relation) ≤ RingHom.ker (ev w) := by
        rw [Ideal.span_le]; rintro _ ⟨r, rfl⟩; exact hw r
      exact this ((hker a).1 ha)
    refine ⟨q, ?_, hq⟩
    ext i
    · simpa [ev, π, j, RingHom.algebraMap_toAlgebra] using DFunLike.congr_fun hq (C (X i))
    · simpa [ev, π, j] using DFunLike.congr_fun hq (X i)
  have hjinj : Function.Injective j := by
    intro q q' h
    ext a
    obtain ⟨b, rfl⟩ := hπ a
    have := hevj q
    rw [h, hevj] at this
    exact (DFunLike.congr_fun this b).symm
  let Ψ : (Fin d → 𝕜) × (ι → 𝕜) → (Fin d → 𝕜) × (σ → 𝕜) :=
    fun w => (w.1, fun r => ev w (P.relation r))
  have hΨj : ∀ q, Ψ (j q) = (coords g q, 0) := by
    intro q
    ext r
    · rfl
    · change ev (j q) (P.relation r) = 0
      rw [hevj, comap_apply, (hker _).2 (Ideal.subset_span ⟨r, rfl⟩), map_zero]
  have hΨan : AnalyticAt 𝕜 Ψ (j p) :=
    analyticAt_fst.prod (analyticAt_pi_iff.2 fun r => analyticAt_aevalTower _ _)
  have hinj : Function.Injective (fderiv 𝕜 Ψ (j p)) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨u, v⟩ huv
    have hline : HasDerivAt (fun t : 𝕜 => Ψ (j p + t • (u, v))) 0 0 := by
      have h1 : HasDerivAt (fun t : 𝕜 => j p + t • (u, v)) (u, v) 0 := by
        simpa using ((hasDerivAt_id (0 : 𝕜)).smul_const (u, v)).const_add (j p)
      have h2 : HasFDerivAt Ψ (fderiv 𝕜 Ψ (j p)) (j p + (0 : 𝕜) • (u, v)) := by
        simpa using hΨan.differentiableAt.hasFDerivAt
      have := h2.comp_hasDerivAt (0 : 𝕜) h1
      rwa [huv] at this
    have hu : u = 0 := by
      have h1 : HasDerivAt (fun t : 𝕜 => (j p).1 + t • u) u 0 := by
        simpa using ((hasDerivAt_id (0 : 𝕜)).smul_const u).const_add (j p).1
      have h2 := (ContinuousLinearMap.fst 𝕜 (Fin d → 𝕜) (σ → 𝕜)).hasFDerivAt.comp_hasDerivAt
        (0 : 𝕜) hline
      exact h1.unique h2
    subst hu
    have hv : ∀ r, ∑ i, ev (j p) (pderiv i (P.relation r)) * v i = 0 := by
      intro r
      have h1 := hasDerivAt_aevalTower_line (aeval (j p).1) (P.relation r) (j p).2 v
      have h2 := (((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : σ => 𝕜) r).comp
        (ContinuousLinearMap.snd 𝕜 (Fin d → 𝕜) (σ → 𝕜))).hasFDerivAt.comp_hasDerivAt (0 : 𝕜) hline)
      refine h1.unique ?_
      simpa [Function.comp_def, Ψ, ev] using h2
    have hdet : ((ev (j p)).toRingHom.mapMatrix P.jacobiMatrix).det ≠ 0 := by
      rw [← RingHom.map_det, hevj]
      have := (P.jacobian_isUnit.map p).ne_zero
      rw [P.jacobian_eq_jacobiMatrix_det, P.algebraMap_apply] at this
      exact this
    have hw : (fun s => v (P.map s)) = 0 := by
      refine Matrix.eq_zero_of_vecMul_eq_zero hdet ?_
      ext r
      rw [Pi.zero_apply, ← hv r, ← hbij.sum_comp]
      simp [Matrix.vecMul, dotProduct, P.jacobiMatrix_apply, mul_comm]
    have : v = 0 := by
      ext i
      obtain ⟨s, rfl⟩ := hbij.2 i
      exact congrFun hw s
    rw [this]; rfl
  obtain ⟨Φ, hΦ, hpS, hsymm⟩ := exists_openPartialHomeomorph_analytic
    (by simp [Module.finrank_prod, hcard]) hΨan hinj
  have hex' : ∀ z : Fin d → 𝕜, ∃ q : A →ₐ[𝕜] 𝕜, (z, 0) ∈ Φ.target →
      j q = Φ.symm (z, 0) ∧ comap π q = ev (Φ.symm (z, 0)) := by
    intro z
    by_cases hz : (z, 0) ∈ Φ.target
    · obtain ⟨q, hq⟩ := hex (Φ.symm (z, 0)) fun r => by
        have := congrFun (congrArg Prod.snd (Φ.right_inv hz)) r
        rwa [hΦ] at this
      exact ⟨q, fun _ => hq⟩
    · exact ⟨p, fun h => absurd h hz⟩
  choose s hs using hex'
  have han : ∀ a, AnalyticOnNhd 𝕜 (fun z => s z a) {z | (z, 0) ∈ Φ.target} := by
    intro a
    obtain ⟨b, rfl⟩ := hπ a
    have hop : IsOpen {z : Fin d → 𝕜 | (z, 0) ∈ Φ.target} :=
      Φ.open_target.preimage (continuous_id.prodMk continuous_const)
    refine AnalyticOnNhd.congr hop (f := fun z => ev (Φ.symm (z, 0)) b) ?_ ?_
    · intro z hz
      have h1 : AnalyticAt 𝕜 (fun z : Fin d → 𝕜 => Φ.symm (z, 0)) z :=
        AnalyticAt.comp (f := fun z : Fin d → 𝕜 => (z, (0 : σ → 𝕜))) (hsymm _ hz)
          (analyticAt_id.prod analyticAt_const)
      exact AnalyticAt.comp (f := fun z : Fin d → 𝕜 => Φ.symm (z, 0))
        (analyticAt_aevalTower b _) h1
    · intro z hz
      exact (DFunLike.congr_fun (hs z hz).2 b).symm
  have hmap : ∀ q, j q ∈ Φ.source → (coords g q, 0) ∈ Φ.target := by
    intro q hq
    have := Φ.map_source hq
    rwa [hΦ, hΨj] at this
  refine ⟨{ toFun := coords g
            invFun := s
            source := j ⁻¹' Φ.source
            target := {z | (z, 0) ∈ Φ.target}
            map_source' := hmap
            map_target' := fun z hz => ?_
            left_inv' := fun q hq => ?_
            right_inv' := fun z hz => ?_
            open_source := Φ.open_source.preimage hjc
            open_target := Φ.open_target.preimage (continuous_id.prodMk continuous_const)
            continuousOn_toFun := (continuous_coords g).continuousOn
            continuousOn_invFun := continuousOn_iff.2 fun a => (han a).continuousOn },
    hpS, rfl, han⟩
  · rw [mem_preimage, (hs z hz).1]; exact Φ.map_target hz
  · apply hjinj
    rw [(hs _ (hmap q hq)).1, ← hΨj, ← hΦ, Φ.left_inv hq]
  · have := Φ.right_inv hz
    rw [← (hs z hz).1, hΦ, hΨj] at this
    exact congrArg Prod.fst this
end GlobalTheory.AffinePoints
