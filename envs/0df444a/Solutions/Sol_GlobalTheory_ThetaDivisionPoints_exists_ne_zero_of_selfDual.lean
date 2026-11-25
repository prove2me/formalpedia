-- Prove2me | solution 1 for GlobalTheory.ThetaDivisionPoints.exists_ne_zero_of_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:19:51.146834+00:00
-- url     : https://prove2.me/submissions/7e4d9fed-41bf-4444-a877-347a9975806b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsThetaDivisionPointNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ThetaFunctionNeZeroAtDivisionPointSelfDual
import Theorems.Thm_GlobalTheory_ThetaDivisionPoints_eq_zero_of_im_eq_zero
import Theorems.Thm_GlobalTheory_ThetaDivisionPoints_exists_ne_zero_of_principal
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open Complex Matrix
open GlobalTheory GlobalTheory.ThetaDivisionPoints
namespace GlobalTheory.ThetaDivisionPoints
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (g : ℕ) (B : LinearMap.BilinForm ℚ V) (p : V →ₗ[ℤ] (Fin g → ℂ)), Function.Injective p → ∀ L : Submodule ℤ V, L.FG → (∀ x, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, B x y = k) → Submodule.span ℝ (p '' (L : Set V)) = ⊤ → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ u v, (p u ⬝ᵥ Hm.mulVec (star (p v))).im = (B u v : ℝ)) → ∀ c : V → ℂ, (∀ v, ‖c v‖ = 1) → ∀ N : ℕ, 2 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, Differentiable ℂ f → f ≠ 0 → (∀ v ∈ L, ∀ z, f (z + p v) = c v * cexp (N * (Real.pi * (z ⬝ᵥ Hm.mulVec (star (p v))) + Real.pi / 2 * (p v ⬝ᵥ Hm.mulVec (star (p v))))) * f z) → ∃ v ∈ L, f ((N : ℂ)⁻¹ • p v) ≠ 0 := by
  intro V _ _ _ g B p hp L hfg hL hsp Hm hH hpos hB c hc N hN f hdf h0 hf
  set Λ : Submodule ℤ (Fin g → ℂ) := L.map p with hΛ
  have hsp' : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ := hsp
  choose q hq hpq using fun l : Λ => l.2
  have hint : ∀ l m : Λ, ∃ k : ℤ,
      (k : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im := fun l m => by
    obtain ⟨k, hk⟩ := (hL _).1 (hq l) _ (hq m)
    exact ⟨k, by rw [← hpq l, ← hpq m, hB, hk, Rat.cast_intCast]⟩
  choose k hk using hint
  let Ef : LinearMap.BilinForm ℤ Λ := LinearMap.mk₂ ℤ k
    (fun a b m => Int.cast_injective (α := ℝ) (by
      rw [Int.cast_add, hk, hk, hk, Submodule.coe_add, add_dotProduct, add_im]))
    (fun t a m => Int.cast_injective (α := ℝ) (by
      rw [smul_eq_mul, Int.cast_mul, hk, hk, Submodule.coe_smul, smul_dotProduct]; simp))
    (fun m a b => Int.cast_injective (α := ℝ) (by
      rw [Int.cast_add, hk, hk, hk, Submodule.coe_add, star_add, mulVec_add, dotProduct_add,
        add_im]))
    (fun t m a => Int.cast_injective (α := ℝ) (by
      rw [smul_eq_mul, Int.cast_mul, hk, hk, Submodule.coe_smul, star_smul, mulVec_smul,
        dotProduct_smul]; simp))
  have hE : ∀ l m : Λ, (Ef l m : ℝ) =
      ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im := hk
  have hker : ∀ l : Λ, Ef l = 0 → l = 0 := fun l hl =>
    Subtype.ext (eq_zero_of_im_eq_zero hpos hsp' fun m hm => by
      rw [← hE l ⟨m, hm⟩, hl]; simp)
  have hdisc : DiscreteTopology Λ := by
    haveI : Module.Finite ℤ Λ := Module.Finite.iff_fg.2 (hfg.map p)
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := Λ)
    refine discreteTopology_of_isOpen_singleton_zero ?_
    have e : ({0} : Set Λ) = ⋂ m ∈ s, {l : Λ |
        |((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im| < 1} := by
      ext l
      simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
      refine ⟨fun h m _ => by simp [h], fun h => hker l (LinearMap.ext_on hs fun m hm => ?_)⟩
      have h1 := h m hm
      rw [← hE, ← Int.cast_abs, ← Int.cast_one, Int.cast_lt] at h1
      exact Int.abs_lt_one_iff.1 h1
    rw [e]
    refine isOpen_biInter_finset fun m _ => isOpen_lt ?_ continuous_const
    refine (Complex.continuous_im.comp ?_).abs
    exact continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp continuous_subtype_val).mul continuous_const
  have hBinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).2 fun u hu => hp ?_
    rw [map_zero]
    refine eq_zero_of_im_eq_zero hpos hsp ?_
    rintro _ ⟨v, -, rfl⟩
    rw [hB, hu]; simp
  have hBsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℚ) (V := V)).symm).1 hBinj
  have hbij : Function.Bijective Ef := by
    refine ⟨(injective_iff_map_eq_zero Ef).2 hker, fun φ => ?_⟩
    obtain ⟨ψ, hψ⟩ := (Module.Baer.of_divisible ℚ).extension_property L.subtype
      L.subtype_injective ((Algebra.linearMap ℤ ℚ) ∘ₗ φ ∘ₗ p.submoduleMap L)
    obtain ⟨x, hx⟩ := hBsurj ψ.toAddMonoidHom.toRatLinearMap
    have h1 : ∀ (y) (hy : y ∈ L), B x y = (φ ⟨p y, Submodule.mem_map_of_mem hy⟩ : ℤ) :=
      fun y hy => by
        rw [hx]
        exact LinearMap.congr_fun hψ ⟨y, hy⟩
    refine ⟨⟨p x, Submodule.mem_map_of_mem ((hL x).2 fun y hy => ⟨_, h1 y hy⟩)⟩,
      LinearMap.ext ?_⟩
    rintro ⟨_, y, hy, rfl⟩
    refine Int.cast_injective (α := ℝ) ?_
    rw [hE, hB, h1 y hy, Rat.cast_intCast]
  have hN0 : N ≠ 0 := by omega
  choose χ hχ using fun l : Λ => IsAlgClosed.exists_pow_nat_eq (c (q l)) (Nat.pos_of_ne_zero hN0)
  have hχ1 : ∀ l, ‖χ l‖ = 1 := fun l =>
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN0).1 (by rw [← norm_pow, hχ, hc])
  obtain ⟨_, ⟨v, hv, rfl⟩, h⟩ := exists_ne_zero_of_principal Λ hdisc hsp' Hm χ Ef hH hpos hχ1 hE
    hbij N hN f hdf h0 (fun l z => by
      rw [mul_pow, hχ, ← Complex.exp_nat_mul, ← hpq l]
      exact hf _ (hq l) z)
  exact ⟨v, hv, h⟩
end GlobalTheory.ThetaDivisionPoints
