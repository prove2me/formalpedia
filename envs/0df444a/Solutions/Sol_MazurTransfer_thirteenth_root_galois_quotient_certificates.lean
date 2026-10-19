-- Prove2me | solution 1 for MazurTransfer.thirteenth_root_galois_quotient_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T23:32:53.185663+00:00
-- url     : https://prove2.me/submissions/d8adfa6f-9223-4a4a-acfb-aea71dfde6bd

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal primitive-thirteenth-root Galois power map is
surjective over Q in a normal characteristic-zero extension, with its actual
root-fixing kernel and normalized generator lift. Named downstream consumer:
the actual arithmetic13 Picard kernel characters.
-/
import Mathlib
import Definitions.Def_MazurTransfer_ThirteenToNineteenOriginalCharacterDataAndConstructorCertificates20261018
noncomputable section
universe u
open Polynomial MazurTransfer.ThirteenToNineteenCharacters
attribute [local instance] characterOriginalPrime13Provider20261018 characterOriginalPrime19Provider20261018
namespace MazurTransfer.ThirteenthRootGaloisQuotientProofHelpers20261018
variable {K : Type u} [Field K] [CharZero K] [Normal ℚ K]
theorem exists_galois_square (z : K) (hz : IsPrimitiveRoot z 13) :
    ∃ σ : K ≃ₐ[ℚ] K, σ z = z ^ 2 := by
  have : NeZero (13 : ℚ) := ⟨by norm_num⟩
  have he : aeval (z ^ 2) (minpoly ℚ z) = 0 := by
    rw [← hz.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat (by decide : 0 < 13))]
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact (hz.pow_of_coprime 2 (by decide)).isRoot_cyclotomic (by decide : 0 < 13)
  exact minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic z) he

theorem autToPow_eq_of_apply (z : K) (hz : IsPrimitiveRoot z 13)
    (σ : K ≃ₐ[ℚ] K) (u : (ZMod 13)ˣ) (hσ : σ z = z ^ (u : ZMod 13).val) :
    hz.autToPow ℚ σ = u := by
  apply Units.ext
  apply ZMod.val_injective 13
  exact hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) ((hz.autToPow_spec ℚ σ).trans hσ)

theorem exists_galois_pow (z : K) (hz : IsPrimitiveRoot z 13) (u : (ZMod 13)ˣ) :
    ∃ σ : K ≃ₐ[ℚ] K, σ z = z ^ (u : ZMod 13).val := by
  have : NeZero (13 : ℚ) := ⟨by norm_num⟩
  have he : aeval (z ^ (u : ZMod 13).val) (minpoly ℚ z) = 0 := by
    rw [← hz.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat (by decide : 0 < 13))]
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact (hz.pow_of_coprime _ (ZMod.val_coe_unit_coprime u)).isRoot_cyclotomic (by decide : 0 < 13)
  exact minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic z) he

theorem autToPow_surjective (z : K) (hz : IsPrimitiveRoot z 13) : Function.Surjective (hz.autToPow ℚ) := by
  intro u
  obtain ⟨σ, hσ⟩ := exists_galois_pow z hz u
  exact ⟨σ, autToPow_eq_of_apply z hz σ u hσ⟩

theorem fixes_root_of_autToPow_eq_one (z : K) (hz : IsPrimitiveRoot z 13)
    (σ : K ≃ₐ[ℚ] K) (hσ : hz.autToPow ℚ σ = 1) : σ z = z := by
  have h := hz.autToPow_spec ℚ σ
  rw [hσ] at h
  change z ^ (1 : ZMod 13).val = σ z at h
  rw [show (1 : ZMod 13).val = 1 by decide, pow_one] at h
  exact h.symm

theorem exists_generator_lift (z : K) (hz : IsPrimitiveRoot z 13) :
    ∃ σ : K ≃ₐ[ℚ] K, σ z = z ^ 2 ∧ hz.autToPow ℚ σ = generator := by
  obtain ⟨σ, hσ⟩ := exists_galois_square z hz
  exact ⟨σ, hσ, autToPow_eq_of_apply z hz σ generator hσ⟩

end MazurTransfer.ThirteenthRootGaloisQuotientProofHelpers20261018
theorem solution :
    (∀ (K : Type u) [Field K] [CharZero K] [Normal ℚ K] (z : K) (hz : IsPrimitiveRoot z 13)
    (σ : K ≃ₐ[ℚ] K) (u : (ZMod 13)ˣ) (hσ : σ z = z ^ (u : ZMod 13).val),
    hz.autToPow ℚ σ = u) ∧
    (∀ (K : Type u) [Field K] [CharZero K] [Normal ℚ K] (z : K) (hz : IsPrimitiveRoot z 13) (u : (ZMod 13)ˣ),
    ∃ σ : K ≃ₐ[ℚ] K, σ z = z ^ (u : ZMod 13).val) ∧
    (∀ (K : Type u) [Field K] [CharZero K] [Normal ℚ K] (z : K) (hz : IsPrimitiveRoot z 13), Function.Surjective (hz.autToPow ℚ)) ∧
    (∀ (K : Type u) [Field K] [CharZero K] [Normal ℚ K] (z : K) (hz : IsPrimitiveRoot z 13)
    (σ : K ≃ₐ[ℚ] K) (hσ : hz.autToPow ℚ σ = 1), σ z = z) ∧
    (∀ (K : Type u) [Field K] [CharZero K] [Normal ℚ K] (z : K) (hz : IsPrimitiveRoot z 13),
    ∃ σ : K ≃ₐ[ℚ] K, σ z = z ^ 2 ∧ hz.autToPow ℚ σ = generator) := by
  exact ⟨fun K _ _ _ => @MazurTransfer.ThirteenthRootGaloisQuotientProofHelpers20261018.autToPow_eq_of_apply K _ _ _, fun K _ _ _ => @MazurTransfer.ThirteenthRootGaloisQuotientProofHelpers20261018.exists_galois_pow K _ _ _, fun K _ _ _ => @MazurTransfer.ThirteenthRootGaloisQuotientProofHelpers20261018.autToPow_surjective K _ _ _, fun K _ _ _ => @MazurTransfer.ThirteenthRootGaloisQuotientProofHelpers20261018.fixes_root_of_autToPow_eq_one K _ _ _, fun K _ _ _ => @MazurTransfer.ThirteenthRootGaloisQuotientProofHelpers20261018.exists_generator_lift K _ _ _⟩
#print axioms solution
