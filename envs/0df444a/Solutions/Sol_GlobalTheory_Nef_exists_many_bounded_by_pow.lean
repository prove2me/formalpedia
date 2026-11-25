-- Prove2me | solution 1 for GlobalTheory.Nef.exists_many_bounded_by_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:37:43.707801+00:00
-- url     : https://prove2.me/submissions/d8aebacd-4788-45be-b538-f8250e2368e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsManyBoundedByPow
import Theorems.Thm_GlobalTheory_Nef_PolesOfT_one_le_Mx
import Theorems.Thm_GlobalTheory_Nef_PolesOfT_exists_mul_bdd
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Nef
open Polynomial PolesOfT
namespace GlobalTheory.Nef
theorem _root_.solution : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ t : F, Transcendental k t → ∃ c : ℕ, ∀ N : ℕ, ∃ (n : ℕ) (f : Fin n → F), LinearIndependent k f ∧ ((N : ℤ) - c) * Module.finrank k⟮t⟯ F ≤ n ∧ ∀ (i : Fin n) (v : Place k F), v.1 (f i) ≤ max 1 (v.1 t) ^ N := by
  intro k F _ _ _ _ _ _ t ht
  by_cases hfin : FiniteDimensional k⟮t⟯ F
  swap
  · refine ⟨0, fun N => ⟨0, Fin.elim0, linearIndependent_empty_type, ?_, fun i => i.elim0⟩⟩
    rw [Module.finrank_of_infinite_dimensional hfin]; simp
  set d := Module.finrank k⟮t⟯ F with hd
  let b := Module.finBasis k⟮t⟯ F
  have halg : ∀ j, IsAlgebraic k⟮t⟯ (b j) := fun j => Algebra.IsAlgebraic.isAlgebraic _
  choose q hq0 cj hcj using fun j => exists_mul_bdd t (b j) (halg j)
  refine ⟨Finset.univ.sup cj, fun N => ?_⟩
  set c := Finset.univ.sup cj with hc
  set L := N - c with hL
  let w : Fin d → k⟮t⟯ := fun j => aeval (IntermediateField.AdjoinSimple.gen k t) (q j)
  have hw : ∀ j, algebraMap k⟮t⟯ F (w j) = aeval t (q j) := fun j => by
    simp only [w]; rw [← aeval_algebraMap_apply, IntermediateField.AdjoinSimple.algebraMap_gen]
  have hw0 : ∀ j, w j ≠ 0 := fun j h => hq0 j (by rw [← hw j, h, map_zero])
  let y : Fin d → F := fun j => aeval t (q j) * b j
  have hyli : LinearIndependent k⟮t⟯ y := by
    have := b.linearIndependent.units_smul (fun j => Units.mk0 (w j) (hw0 j))
    convert this using 1
    funext j
    simp [y, Algebra.smul_def, hw]
  have hpowF : LinearIndependent k (fun n : ℕ => t ^ n) := by
    have h1 := (Polynomial.basisMonomials k).linearIndependent.map' (aeval t).toLinearMap
      (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp ht))
    have heq : (fun n : ℕ => t ^ n) = (aeval t).toLinearMap ∘ Polynomial.basisMonomials k := by
      funext n
      simp [Polynomial.coe_basisMonomials]
    rw [heq]
    exact h1
  have hpow : LinearIndependent k (fun i : Fin L => (IntermediateField.AdjoinSimple.gen k t) ^ (i : ℕ)) := by
    have heq : (IsScalarTower.toAlgHom k k⟮t⟯ F).toLinearMap ∘
        (fun i : Fin L => (IntermediateField.AdjoinSimple.gen k t) ^ (i : ℕ)) =
        (fun n : ℕ => t ^ n) ∘ (fun i : Fin L => (i : ℕ)) := by
      funext i
      simp
    apply LinearIndependent.of_comp (IsScalarTower.toAlgHom k k⟮t⟯ F).toLinearMap
    rw [heq]
    exact hpowF.comp _ Fin.val_injective
  have hprod := linearIndependent_smul hpow hyli
  refine ⟨L * d, fun i => (fun p : Fin L × Fin d => (IntermediateField.AdjoinSimple.gen k t) ^ (p.1 : ℕ) • y p.2)
    (finProdFinEquiv.symm i), hprod.comp _ finProdFinEquiv.symm.injective, ?_, ?_⟩
  · push_cast
    have h1 : ((N : ℤ) - c) ≤ (L : ℤ) := by omega
    exact mul_le_mul_of_nonneg_right h1 (Int.natCast_nonneg _)
  · intro i v
    dsimp only
    generalize finProdFinEquiv.symm i = p
    obtain ⟨a, j⟩ := p
    have hsm : (IntermediateField.AdjoinSimple.gen k t) ^ (a : ℕ) • y j = t ^ (a : ℕ) * (aeval t (q j) * b j) := by
      rw [Algebra.smul_def, map_pow, IntermediateField.AdjoinSimple.algebraMap_gen]
    dsimp only
    rw [hsm, map_mul, map_pow]
    have ha : (a : ℕ) + c ≤ N := by have := a.2; omega
    calc v.1 t ^ (a : ℕ) * v.1 (aeval t (q j) * b j) ≤ Mx t v ^ (a : ℕ) * Mx t v ^ c :=
          mul_le_mul' (pow_le_pow_left₀ zero_le' (le_max_right _ _) _)
            ((hcj j v).trans (pow_le_pow_right₀ (one_le_Mx t v) (Finset.le_sup (Finset.mem_univ j))))
      _ = Mx t v ^ ((a : ℕ) + c) := (pow_add _ _ _).symm
      _ ≤ max 1 (v.1 t) ^ N := pow_le_pow_right₀ (one_le_Mx t v) ha
end GlobalTheory.Nef
