-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.sqfreeDimAll
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:27:44.443722+00:00
-- url     : https://prove2.me/submissions/4b5c17e2-6905-46c4-998d-b22be0a04e07

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardParabolicSubgroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraDimensionStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquarefreeDimensionFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_prod_Icc_one_eq
import Theorems.Thm_GlobalTheory_T_card_parabolic_subgroup
import Theorems.Thm_GlobalTheory_T_harish_chandra_dimension


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin
namespace GlobalTheory.CompanionTheory.TyFin
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.SqfreeDimAll := by
  intro K _ _ _ n s b lam hb hd
  have hq1 : (1 : ℤ) < (Fintype.card K : ℤ) := by
    have := Fintype.one_lt_card (α := K)
    exact_mod_cast this
  have hne : ∀ i : ℕ, 1 ≤ i → (Fintype.card K : ℤ) ^ i - 1 ≠ 0 := by
    intro i hi h
    have : (1 : ℤ) < (Fintype.card K : ℤ) ^ i := one_lt_pow₀ hq1 (by omega)
    linarith
  have hdim := GlobalTheory.T.harish_chandra_dimension K (Fin n) s b lam
  obtain ⟨hGL, hP⟩ := GlobalTheory.T.card_parabolic_subgroup K (Fin n)
  obtain ⟨hPc, hch⟩ := hP s b
  rw [Fintype.card_fin] at hGL hch
  have hblk : ∀ c, (Nat.card (GL {i // b i = c} K) : ℤ) =
      (Fintype.card K : ℤ) ^ (Fintype.card {i // b i = c}).choose 2 *
        ((∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}), ((Fintype.card K : ℤ) ^ i - 1)) *
          ((Fintype.card K : ℤ) ^ Fintype.card {i // b i = c} - 1)) := by
    intro c
    have hpos : 1 ≤ Fintype.card {i // b i = c} := by
      obtain ⟨i, hi⟩ := hb c
      exact Fintype.card_pos_iff.2 ⟨⟨i, hi⟩⟩
    rw [(GlobalTheory.T.card_parabolic_subgroup K {i // b i = c}).1,
      prod_Icc_one_eq (fun i => (Fintype.card K : ℤ) ^ i - 1) _ hpos]
  have hZ : (Module.finrank ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace K b lam) : ℤ) *
      (Nat.card (Formalism.IrreducibleCountingLemmas.TYPES.parab K b) : ℤ) =
      (Nat.card (GL (Fin n) K) : ℤ) * ∏ c, (Module.finrank ℂ (lam c) : ℤ) := by
    exact_mod_cast hdim
  have hPz : (Nat.card (Formalism.IrreducibleCountingLemmas.TYPES.parab K b) : ℤ) =
      (Fintype.card K : ℤ) ^ Fintype.card {p : Fin n × Fin n // b p.1 < b p.2} *
        ((Fintype.card K : ℤ) ^ (∑ c, (Fintype.card {i // b i = c}).choose 2) *
          ((∏ c, ∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}), ((Fintype.card K : ℤ) ^ i - 1)) *
            ∏ c, ((Fintype.card K : ℤ) ^ Fintype.card {i // b i = c} - 1))) := by
    rw [hPc]
    push_cast
    rw [Finset.prod_congr rfl (fun c _ => hblk c), Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hPz, hGL, hch, Finset.prod_congr rfl (fun c _ => hd c), pow_add] at hZ
  have hA : (∏ c, ∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}),
      ((Fintype.card K : ℤ) ^ i - 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun c _ => Finset.prod_ne_zero_iff.2 fun i hi =>
      hne i (Finset.mem_Ico.1 hi).1
  have hq0 : (Fintype.card K : ℤ) ≠ 0 := by linarith
  have hc : (Fintype.card K : ℤ) ^ Fintype.card {p : Fin n × Fin n // b p.1 < b p.2} *
      (Fintype.card K : ℤ) ^ (∑ c, (Fintype.card {i // b i = c}).choose 2) *
      (∏ c, ∏ i ∈ Finset.Ico 1 (Fintype.card {i // b i = c}), ((Fintype.card K : ℤ) ^ i - 1)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hq0) (pow_ne_zero _ hq0)) hA
  apply mul_left_cancel₀ hc
  linear_combination hZ
end GlobalTheory.CompanionTheory.TyFin
