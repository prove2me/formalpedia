-- Prove2me | solution 1 for ModularCurve.JOne.degeneracyPullbackPair_galois_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/47aa5e38-8532-5873-bd57-27e259ffda9a

import Mathlib
import Definitions.Def_ModularCurve_X1DegeneracyPullback
import Theorems.Thm_AlgebraicCurve_SemilinearAut_pullbackAlong_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JOne_degeneracyPullbackPair_galois_smul

set_option autoImplicit false

noncomputable section

namespace X1DegPort

open ModularCurve AlgebraicCurve AlgebraicCurve.SemilinearAut HahnSeries

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [HasPrincipalDivisors K F']

theorem pullbackAlongHom_smul (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ) {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (hgg' : IntertwinesAlong φ.toRingHom g g') (x : Pic0 K F) :
    Pic0.pullbackAlongHom φ hφ hFI (g • x) = g' • Pic0.pullbackAlongHom φ hφ hFI x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [pic0_smul_mk, Pic0.pullbackAlongHom_mk, Pic0.pullbackAlongHom_mk, pic0_smul_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  show Divisor.pullbackAlong φ hφ (g • (D : Divisor K F)) =
    g' • Divisor.pullbackAlong φ hφ (D : Divisor K F)
  exact SemilinearAut.pullbackAlong_smul φ hφ hgg' D

end Generic

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

section Intertwine

variable (L : Type*) [Field L] [Algebra ℚ L] {N N' : ℕ} (σ : L ≃ₐ[ℚ] L)

theorem intertwines_incl (h : N ∣ N') :
    IntertwinesAlong (x1LevelInclBar L h).toRingHom
      (arithmeticGalois (x1FunctionField N) σ) (arithmeticGalois (x1FunctionField N') σ) := by
  intro x
  apply Subtype.ext
  show coeffMap (σ : L →+* L) ((x1LevelInclBar L h x : laurentBaseChange L _) : LaurentSeries L)
    = (x1LevelInclBar L h (arithmeticGalois (x1FunctionField N) σ • x) : LaurentSeries L)
  rw [coe_x1LevelInclBar, coe_x1LevelInclBar, coe_arithmeticGalois_smul]

theorem intertwines_subst (t : ℕ) [NeZero t] (h : N * t ∣ N') :
    IntertwinesAlong (x1LevelSubstBar L t h).toRingHom
      (arithmeticGalois (x1FunctionField N) σ) (arithmeticGalois (x1FunctionField N') σ) := by
  intro x
  apply Subtype.ext
  show coeffMap (σ : L →+* L) ((x1LevelSubstBar L t h x : laurentBaseChange L _) : LaurentSeries L)
    = (x1LevelSubstBar L t h (arithmeticGalois (x1FunctionField N) σ • x) : LaurentSeries L)
  by_cases hβ : HeckeBetaOneDefined N t
  · rw [coe_x1LevelSubstBar_of L t h hβ, coe_x1LevelSubstBar_of L t h hβ,
      coe_arithmeticGalois_smul, coeffMap_qExpand]
  · rw [coe_x1LevelSubstBar, coe_x1LevelSubstBar, heckeBetaOneBar_of_not N t hβ,
      coe_heckeAlphaOneBar, coe_heckeAlphaOneBar, coe_arithmeticGalois_smul]

end Intertwine

section Pair

variable (N N' t : ℕ) [NeZero t] (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JOne N)

theorem degeneracyPullbackPair_galois_smul (i : Fin 2) :
    JOne.degeneracyPullbackPair N N' t i (σ • x) = σ • JOne.degeneracyPullbackPair N N' t i x := by
  by_cases hin : JOne.DegeneracyPullbackInputs N N' t
  · obtain ⟨hdvd, hβ, h₁, h₂, hP, hFI₁, hFI₂⟩ := hin
    haveI := hP
    rw [JOne.degeneracyPullbackPair_eq hdvd hβ h₁ h₂ hFI₁ hFI₂, galois_smul_pic0_def,
      galois_smul_pic0_def]
    revert i
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · simp only [Matrix.cons_val_zero]
      exact pullbackAlongHom_smul _ h₁ hFI₁ (intertwines_incl (AlgebraicClosure ℚ) σ _) x
    · simp only [Matrix.cons_val_one]
      exact pullbackAlongHom_smul _ h₂ hFI₂ (intertwines_subst (AlgebraicClosure ℚ) σ t hdvd) x
  · rw [JOne.degeneracyPullbackPair_apply_of_not hin, JOne.degeneracyPullbackPair_apply_of_not hin]
    exact (smul_zero (A := JOne N') σ).symm

end Pair

end X1DegPort

end

theorem solution (N N' t : ℕ) [NeZero t] (i : Fin 2)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ModularCurve.JOne N) :
    ModularCurve.JOne.degeneracyPullbackPair N N' t i (σ • x) =
      σ • ModularCurve.JOne.degeneracyPullbackPair N N' t i x :=
  X1DegPort.degeneracyPullbackPair_galois_smul N N' t σ x i

end S_ModularCurve_JOne_degeneracyPullbackPair_galois_smul
end P2MW
export P2MW.S_ModularCurve_JOne_degeneracyPullbackPair_galois_smul (solution)
