-- Prove2me | solution 1 for GlobalTheory.Ker.CreOp.foldr_creation_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:58:53.53036+00:00
-- url     : https://prove2.me/submissions/1306015d-d062-459a-b99e-8cc355ec8890

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FoldrHolDEqIteratedFDeriv
import Theorems.Thm_GlobalTheory_Ker_CreOp_contDiff_holD
import Theorems.Thm_GlobalTheory_Ker_CreOp_holD_add
import Theorems.Thm_GlobalTheory_Ker_CreOp_exists_clm_of_antilinear
import Theorems.Thm_GlobalTheory_Ker_CreOp_holD_mul
import Theorems.Thm_GlobalTheory_Ker_CreOp_contDiff_foldr_holD
import Theorems.Thm_GlobalTheory_Ker_CreOp_foldr_holD_eq_iteratedFDeriv
import Theorems.Thm_GlobalTheory_SCV_contDiff_of_differentiable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex
open scoped ComplexConjugate
namespace GlobalTheory.Ker.CreOp
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
variable {σ : Type} (u : σ → W)
private theorem contDiff_list_sum_mul (R : List ((W →L[ℝ] ℂ) × (W → ℂ)))
    (hR : ∀ p ∈ R, ContDiff ℝ (⊤ : ℕ∞) p.2) :
    ContDiff ℝ (⊤ : ℕ∞) fun z => (R.map fun p => p.1 z * p.2 z).sum := by
  induction R with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact contDiff_const
  | cons p R ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (p.1.contDiff.mul (hR p (by simp))).add (ih fun q hq => hR q (by simp [hq]))
private theorem holD_list_sum_mul (R : List ((W →L[ℝ] ℂ) × (W → ℂ)))
    (hR : ∀ p ∈ R, (∀ a, p.1 (I • a) = -I * p.1 a) ∧ ContDiff ℝ (⊤ : ℕ∞) p.2) (v : W) :
    holD v (fun z => (R.map fun p => p.1 z * p.2 z).sum) =
      fun z => (R.map fun p => p.1 z * holD v p.2 z).sum := by
  induction R with
  | nil => funext z; simp [holD]
  | cons p R ih =>
    have hp := hR p (by simp)
    have hR' : ∀ q ∈ R, (∀ a, q.1 (I • a) = -I * q.1 a) ∧ ContDiff ℝ (⊤ : ℕ∞) q.2 :=
      fun q hq => hR q (by simp [hq])
    have hS := contDiff_list_sum_mul R fun q hq => (hR' q hq).2
    have hd : Differentiable ℝ p.2 := (contDiff_infty_iff_fderiv.1 hp.2).1
    simp only [List.map_cons, List.sum_cons]
    rw [holD_add (show Differentiable ℝ fun z => p.1 z * p.2 z from p.1.differentiable.mul hd)
      (contDiff_infty_iff_fderiv.1 hS).1,
      holD_mul p.1 hp.1 hd, ih hR']
end GlobalTheory.Ker.CreOp
end

set_option autoImplicit false
open Complex
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.Ker GlobalTheory.Ker.CreOp
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
variable {σ : Type} (u : σ → W)
namespace GlobalTheory.Ker.CreOp
theorem _root_.solution : ∀ (σ W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (u : σ → W) (lam : σ → W → ℂ) (θ : W → ℂ),
    (∀ l, (∀ a b, lam l (a + b) = lam l a + lam l b) ∧
      ∀ (t : ℂ) a, lam l (t • a) = conj t * lam l a) → Differentiable ℂ θ →
    ∀ Dl : σ → (W → ℂ) → W → ℂ,
      (∀ l Φ z, Dl l Φ z = lam l z * Φ z +
        (1 / 2 : ℂ) * (fderiv ℝ Φ z (u l) - I * fderiv ℝ Φ z (I • u l))) →
      ∀ L : List σ, ContDiff ℝ (⊤ : ℕ∞) (L.foldr Dl θ) ∧
        L.foldr Dl θ 0 = iteratedFDeriv ℂ L.length θ 0 fun k => u (L.get k) := by
  intro σ W _ _ _ u lam θ hlam hθ Dl hDl L
  choose T hT using fun l => exists_clm_of_antilinear (hlam l).1 (hlam l).2
  have hTI : ∀ l a, T l (I • a) = -I * T l a := by
    intro l a
    rw [← hT l, (hlam l).2, Complex.conj_I]
  have hθs : ContDiff ℝ (⊤ : ℕ∞) θ :=
    (GlobalTheory.SCV.contDiff_of_differentiable hθ _).restrict_scalars ℝ
  have step : ∀ l Φ, Dl l Φ = fun z => T l z * Φ z + holD (u l) Φ z := by
    intro l Φ
    funext z
    rw [hDl, ← hT l]
    rfl
  have hsm : ∀ L : List σ, ContDiff ℝ (⊤ : ℕ∞) (L.foldr Dl θ) := by
    intro L
    induction L with
    | nil => exact hθs
    | cons l L ih =>
      simp only [List.foldr_cons]
      rw [step]
      exact ((T l).contDiff.mul ih).add (contDiff_holD ih (u l))
  have key : ∀ L : List σ, ∃ R : List ((W →L[ℝ] ℂ) × (W → ℂ)),
      (∀ p ∈ R, (∀ a, p.1 (I • a) = -I * p.1 a) ∧ ContDiff ℝ (⊤ : ℕ∞) p.2) ∧
      L.foldr Dl θ = fun z =>
        L.foldr (fun l => holD (u l)) θ z + (R.map fun p => p.1 z * p.2 z).sum := by
    intro L
    induction L with
    | nil => exact ⟨[], by simp, by funext z; simp⟩
    | cons l L ih =>
      obtain ⟨R, hR, hE⟩ := ih
      refine ⟨(T l, L.foldr Dl θ) :: R.map (fun p => (p.1, holD (u l) p.2)), ?_, ?_⟩
      · intro p hp
        simp only [List.mem_cons, List.mem_map] at hp
        rcases hp with rfl | ⟨q, hq, rfl⟩
        · exact ⟨hTI l, hsm L⟩
        · exact ⟨(hR q hq).1, contDiff_holD (hR q hq).2 (u l)⟩
      · have hD := contDiff_foldr_holD u hθs L
        have hS := contDiff_list_sum_mul R fun p hp => (hR p hp).2
        have e : holD (u l) (L.foldr Dl θ) = fun z =>
            holD (u l) (L.foldr (fun l => holD (u l)) θ) z +
              (R.map fun p => p.1 z * holD (u l) p.2 z).sum := by
          rw [hE, holD_add (contDiff_infty_iff_fderiv.1 hD).1 (contDiff_infty_iff_fderiv.1 hS).1,
            holD_list_sum_mul R hR (u l)]
        funext z
        simp only [List.foldr_cons, step, e, List.map_cons, List.map_map, List.sum_cons,
          Function.comp_def]
        ring
  refine ⟨hsm L, ?_⟩
  obtain ⟨R, -, hE⟩ := key L
  have h0 : (R.map fun p => p.1 0 * p.2 0).sum = 0 :=
    List.sum_eq_zero fun x hx => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
      simp
  rw [hE]
  simp only [h0, add_zero]
  rw [foldr_holD_eq_iteratedFDeriv u hθ L]
end GlobalTheory.Ker.CreOp
