-- Prove2me | solution 1 for GlobalTheory.finrank_totalDegree_image_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:57:35.306227+00:00
-- url     : https://prove2.me/submissions/d5f5c344-3a5d-40dd-bdf6-6b7c98c6f851

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankTotalDegreeImageGrowth
import Theorems.Thm_GlobalTheory_DegreeGrowth_mem_boxSpan
import Theorems.Thm_GlobalTheory_DegreeGrowth_boxSpan_mono
import Theorems.Thm_GlobalTheory_DegreeGrowth_exists_aeval_mul_mem
import Theorems.Thm_GlobalTheory_DegreeGrowth_upper
import Theorems.Thm_GlobalTheory_DegreeGrowth_lower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (K B : Type) [Field K] [CommRing B] [IsDomain B] [Algebra K B] (m g : ℕ) (r : Fin m → B), Function.Surjective (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B) → Algebra.trdeg K B = g → ∃ c C : ℕ, 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t → t ^ g ≤ c * Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin m) K t).map (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap) ∧ Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin m) K t).map (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap) ≤ C * t ^ g := by
  intro K B _ _ _ _ m g r hr hg
  haveI : Algebra.FiniteType K B := Algebra.FiniteType.of_surjective _ hr
  obtain ⟨s, φ, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K B
  letI : Algebra (MvPolynomial (Fin s) K) B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin s) K) B :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  haveI : Module.Finite (MvPolynomial (Fin s) K) B := hfin
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have hs : s = g := by
    have h := trdeg_add_eq K (MvPolynomial (Fin s) K) (A := B)
    rw [MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero, hg] at h
    simpa using h
  subst hs
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := MvPolynomial (Fin s) K) (M := B)
  have hall : ∀ x : B, ∃ D, x ∈ DegreeGrowth.boxSpan K (fun i => φ (MvPolynomial.X i)) b D := by
    intro x
    have hx : x ∈ Submodule.span (MvPolynomial (Fin s) K) (Set.range b) := hb ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      exact ⟨0, by simpa using DegreeGrowth.mem_boxSpan (K := K) (fun i => φ (MvPolynomial.X i)) b 0 (fun _ => 0) (fun _ => le_rfl) l⟩
    | zero => exact ⟨0, zero_mem _⟩
    | add x z _ _ h1 h2 =>
      obtain ⟨D1, h1⟩ := h1
      obtain ⟨D2, h2⟩ := h2
      exact ⟨max D1 D2, add_mem (DegreeGrowth.boxSpan_mono _ b (le_max_left _ _) h1)
        (DegreeGrowth.boxSpan_mono _ b (le_max_right _ _) h2)⟩
    | smul p x _ hx =>
      have h := DegreeGrowth.exists_aeval_mul_mem _ b p hx
      have e : MvPolynomial.aeval (fun i => φ (MvPolynomial.X i)) = φ :=
        (MvPolynomial.aeval_unique φ).symm
      rw [e] at h
      exact h
  obtain ⟨C, hC⟩ := DegreeGrowth.upper _ b hall r
  obtain ⟨c, hc1, hc⟩ := DegreeGrowth.lower φ hinj r hr
  exact ⟨c, C, hc1, fun t ht => ⟨hc t, hC t ht⟩⟩
end GlobalTheory
