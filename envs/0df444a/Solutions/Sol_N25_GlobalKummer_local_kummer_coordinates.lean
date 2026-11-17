-- Prove2me | solution 1 for N25.GlobalKummer.local_kummer_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:07.270475+00:00
-- url     : https://prove2.me/submissions/be7e7241-cd48-4bb7-8c0b-f9509dc29b18

import Definitions.Def_N25_GlobalKummerSequence
import Definitions.Def_GroupCohomology_Kummer
import Definitions.Def_N25_LocalFiniteFlatClasses

set_option autoImplicit false

noncomputable section

namespace N25.GlobalKummer

local instance localCoordinatesPrimeSeventyOne_sc39b60 : Fact (Nat.Prime 71) := ⟨by decide⟩

local instance localCoordinatesScalarTower_sc39b60 : IsScalarTower ℚ ℚ_[71] (PadicAlgCl 71) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

/-- Global cyclotomic Kummer data gives the exact multiplicative coordinates
at 71 through the prescribed algebraic-closure embedding. -/
theorem _root_.solution
    (c : groupCohomology.cocycles₁ cyclotomicRep)
    (e : ZMod 71 ≃+ Additive (rootsOfUnity 71 (AlgebraicClosure ℚ)))
    (he : ∀ (σ : Gal) (a : ZMod 71),
      e ((ExtCitation.cycloChar 71 σ : ZMod 71) * a) =
        Additive.ofMul (σ • Additive.toMul (e a)))
    (a : ℚˣ) (α : (AlgebraicClosure ℚ)ˣ)
    (hα : algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ) = (α : AlgebraicClosure ℚ) ^ 71)
    (hc : ∀ σ : Gal, (Additive.toMul (e (c σ))).val =
      groupCohomology.Kummer.kummerCocycle α σ) :
    ∃ μ : ZMod 71 → PadicAlgCl 71,
      Function.Injective μ ∧ μ 0 = 1 ∧
      (∀ b d, μ (b + d) = μ b * μ d) ∧
      (∀ b, μ b ^ 71 = 1) ∧
      (∀ (σ : PadicAlgCl 71 ≃ₐ[ℚ_[71]] PadicAlgCl 71) (b : ZMod 71),
        μ (localCyclotomicRep.ρ σ b) = σ (μ b)) ∧
      (padicEmbedding 71 (α : AlgebraicClosure ℚ)) ^ 71 =
        algebraMap ℚ_[71] (PadicAlgCl 71) (algebraMap ℚ ℚ_[71] (a : ℚ)) ∧
      ∀ σ : PadicAlgCl 71 ≃ₐ[ℚ_[71]] PadicAlgCl 71,
        μ (c (localGaloisToGlobal 71 σ)) * padicEmbedding 71 (α : AlgebraicClosure ℚ) =
          σ (padicEmbedding 71 (α : AlgebraicClosure ℚ)) := by
  let μ : ZMod 71 → PadicAlgCl 71 := fun b =>
    padicEmbedding 71 ((Additive.toMul (e b)).val : AlgebraicClosure ℚ)
  refine ⟨μ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b d hbd
    have hroots : Additive.toMul (e b) = Additive.toMul (e d) := by
      apply Subtype.ext
      apply Units.ext
      exact (padicEmbedding 71).injective hbd
    exact e.injective (congrArg Additive.ofMul hroots)
  · change padicEmbedding 71 ((Additive.toMul (e 0)).val : AlgebraicClosure ℚ) = 1
    rw [map_zero]
    change padicEmbedding 71 1 = 1
    exact map_one _
  · intro b d
    change padicEmbedding 71 ((Additive.toMul (e (b + d))).val : AlgebraicClosure ℚ) = _
    rw [map_add]
    change padicEmbedding 71
      (((Additive.toMul (e b)).val : AlgebraicClosure ℚ) *
        ((Additive.toMul (e d)).val : AlgebraicClosure ℚ)) = _
    exact map_mul _ _ _
  · intro b
    have hunit : ((Additive.toMul (e b)).val) ^ 71 = 1 := by
      simpa only [mem_rootsOfUnity] using (Additive.toMul (e b)).property
    have hfield : (((Additive.toMul (e b)).val : AlgebraicClosure ℚ)) ^ 71 = 1 := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
        congrArg (fun z : (AlgebraicClosure ℚ)ˣ => (z : AlgebraicClosure ℚ)) hunit
    change μ b ^ 71 = 1
    change (padicEmbedding 71 ((Additive.toMul (e b)).val : AlgebraicClosure ℚ)) ^ 71 = 1
    rw [← map_pow, hfield, map_one]
  · intro σ b
    change padicEmbedding 71
      ((Additive.toMul (e ((ExtCitation.cycloChar 71 (localGaloisToGlobal 71 σ) : ZMod 71) * b))).val :
        AlgebraicClosure ℚ) = _
    rw [he]
    change padicEmbedding 71 (localGaloisToGlobal 71 σ
      ((Additive.toMul (e b)).val : AlgebraicClosure ℚ)) = _
    exact padicEmbedding_localGaloisToGlobal 71 σ _
  · change (padicEmbedding 71 (α : AlgebraicClosure ℚ)) ^ 71 = _
    rw [← map_pow, ← hα, (padicEmbedding 71).commutes]
    exact (IsScalarTower.algebraMap_apply ℚ ℚ_[71] (PadicAlgCl 71) (a : ℚ)).symm
  · intro σ
    have hprod : (Additive.toMul (e (c (localGaloisToGlobal 71 σ)))).val * α =
        localGaloisToGlobal 71 σ • α := by
      rw [hc]
      simp [groupCohomology.Kummer.kummerCocycle, div_eq_mul_inv, mul_assoc]
    have h := congrArg (fun z : (AlgebraicClosure ℚ)ˣ =>
      padicEmbedding 71 (z : AlgebraicClosure ℚ)) hprod
    change padicEmbedding 71
      (((Additive.toMul (e (c (localGaloisToGlobal 71 σ)))).val : AlgebraicClosure ℚ) *
        (α : AlgebraicClosure ℚ)) =
      padicEmbedding 71 (localGaloisToGlobal 71 σ (α : AlgebraicClosure ℚ)) at h
    rw [map_mul, padicEmbedding_localGaloisToGlobal] at h
    exact h

end N25.GlobalKummer
