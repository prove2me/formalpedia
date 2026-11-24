-- Prove2me | solution 1 for GlobalTheory.CuspGL.PrimOrth.ipGL_psi_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:09:42.112957+00:00
-- url     : https://prove2.me/submissions/90a61dff-b224-4479-ae87-8a1b839077b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndomorphismInnerProductPrimitiveMobiu
import Theorems.Thm_GlobalTheory_CuspGL_PrimOrth_add_preserves
import Theorems.Thm_GlobalTheory_CuspGL_PrimOrth_add_preserves_iff
import Theorems.Thm_GlobalTheory_CuspGL_PrimOrth_isUnit_add_iff
import Theorems.Thm_GlobalTheory_CuspGL_PrimOrth_sum_mul_eq_zero
import Theorems.Thm_GlobalTheory_CuspGL_PrimOrth_psi_bot
import Theorems.Thm_GlobalTheory_CuspGL_psi_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.PrimOrth
variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
open Classical
namespace GlobalTheory.CuspGL.PrimOrth
theorem _root_.solution (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : F[X] → ℂ) (hs : IsAdditive s) (φ : Module.End F V → ℂ)
    (hφ : IsPrimitive φ) : ipGL φ (psi s V) = ipGL φ (fun g => s (LinearMap.charpoly g)) := by
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) := Finite.of_injective _ (DFunLike.coe_injective (F := V →ₗ[F] V))
  haveI : Finite (Submodule F V) := Finite.of_injective _ (SetLike.coe_injective (A := Submodule F V))
  letI := Fintype.ofFinite (Module.End F V)
  letI := Fintype.ofFinite (Submodule F V)
  let R : Submodule F V → Module.End F V → ℂ := fun W g =>
    if h : W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W then psi s W (g.restrict h.2) else 0
  have hR : ∀ g, psi s V g = s (LinearMap.charpoly g) - ∑ W, R W g := by
    intro g
    rw [psi_eq, finsum_eq_sum_of_fintype]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun W : Submodule F V => W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W)]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter fun W : Submodule F V => ¬ (W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W)), add_zero,
      Finset.sum_subtype (p := fun W : Submodule F V => W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W) _ (by simp)]
    · refine Finset.sum_congr rfl fun W _ => ?_
      simp only [R, dif_pos W.2]
    · intro W hW
      simp only [R, dif_neg (Finset.mem_filter.mp hW).2]
  have hW : ∀ W, ∑ g, φ g * (if IsUnit g then star (R W g) else 0) = 0 := by
    intro W
    by_cases h1 : W = ⊤
    · refine Finset.sum_eq_zero fun g _ => ?_
      have : R W g = 0 := dif_neg (fun h => h.1 h1)
      simp [this]
    by_cases h0 : W = ⊥
    · refine Finset.sum_eq_zero fun g _ => ?_
      have : R W g = 0 := by
        subst h0
        simp only [R]
        split_ifs
        · exact psi_bot hs _ _
        · rfl
      simp [this]
    refine sum_mul_eq_zero hφ h0 h1 _ ?_ ?_
    · intro g h hh
      by_cases hg : ∀ x ∈ W, g x ∈ W
      · have e : R W (g + h) = R W g := by
          simp only [R]
          rw [dif_pos ⟨h1, add_preserves hh hg⟩, dif_pos ⟨h1, hg⟩]
          congr 1
          ext x
          simp [LinearMap.restrict_apply, hh.2 x x.2]
        simp only [e, isUnit_add_iff hh hg]
      · have e1 : R W g = 0 := dif_neg (fun H => hg H.2)
        have e2 : R W (g + h) = 0 := dif_neg (fun H => hg ((add_preserves_iff hh).mp H.2))
        simp [e1, e2]
    · intro g hg
      have e1 : R W g = 0 := dif_neg (fun H => hg H.2)
      simp [e1]
  have hsum : ∀ ψ : Module.End F V → ℂ,
      ipGL φ ψ = ∑ g, φ g * (if IsUnit g then star (ψ g) else 0) := by
    intro ψ
    rw [ipGL, finsum_mem_def, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : IsUnit g
    · simp [Set.indicator, hg]
    · simp [Set.indicator, hg]
  rw [hsum, hsum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  have h2 : ∑ W, ∑ g, φ g * (if IsUnit g then star (R W g) else 0) = 0 :=
    Finset.sum_eq_zero fun W _ => hW W
  rw [Finset.sum_comm, ← neg_eq_zero, ← Finset.sum_neg_distrib] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases hg : IsUnit g
  · simp only [if_pos hg, hR g, star_sub, star_sum, ← Finset.mul_sum]
    ring
  · simp [hg]
end GlobalTheory.CuspGL.PrimOrth
