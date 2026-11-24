-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadricCount.card_quadric_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:24:56.828601+00:00
-- url     : https://prove2.me/submissions/8c16616b-f149-434a-935a-13c81378ab3f

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteFieldQuadraticFormPointCount
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadricCount_norm_gauss
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadricCount_count_mul_card

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadricCount
open ComplexConjugate
variable {k : Type} [Field k] [Fintype k] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.SW.QuadricCount
theorem _root_.solution (k : Type) [Field k] [Fintype k] (hchar : ringChar k ≠ 2)
    (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (hM : Fintype.card ι = 2 * M) (hM1 : 1 ≤ M)
    (B : Matrix ι ι k) (hB : B.IsSymm) (hdet : B.det ≠ 0) (s : k) :
    |(Nat.card {x : ι → k // (2 : k)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) = s} : ℝ) -
      (Fintype.card k : ℝ) ^ (2 * M - 1)| ≤ (Fintype.card k : ℝ) ^ M := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hchar
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AddChar k ℂ, ψ 1 ≠ 1 :=
    AddChar.exists_apply_ne_zero.mpr one_ne_zero
  have hψ1 : ψ ≠ 1 := fun h => hψ (by simp [h])
  have hq : (0 : ℝ) < (Fintype.card k : ℝ) := by exact_mod_cast Fintype.card_pos
  set N : ℕ := Nat.card {x : ι → k // quadForm B x = s} with hNdef
  have hcount := count_mul_card ψ hψ1 B s
  rw [← hNdef, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : k))] at hcount
  have hzero : ψ (-((0 : k) * s)) * ∑ x, ψ ((0 : k) * quadForm B x) =
      (Fintype.card k : ℂ) ^ (2 * M) := by
    simp [hM]
  rw [hzero] at hcount
  have hbound : ‖∑ t ∈ Finset.univ.erase (0 : k), ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x)‖ ≤
      ((Fintype.card k : ℝ) - 1) * (Fintype.card k : ℝ) ^ M := by
    have hterm : ∀ t ∈ Finset.univ.erase (0 : k),
        ‖ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x)‖ ≤ (Fintype.card k : ℝ) ^ M := by
      intro t ht
      rw [norm_mul, AddChar.norm_apply, one_mul,
        norm_gauss ψ hψ1 h2 hB hdet hM (Finset.ne_of_mem_erase ht)]
    have := norm_sum_le_of_le _ hterm
    refine this.trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      nsmul_eq_mul, Nat.cast_sub Fintype.card_pos]
    simp
  have hreal : ((((N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M) : ℝ)) : ℂ) =
      ∑ t ∈ Finset.univ.erase (0 : k), ψ (-(t * s)) * ∑ x, ψ (t * quadForm B x) := by
    push_cast
    rw [hcount]
    ring
  have habs : |(N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M)| ≤
      ((Fintype.card k : ℝ) - 1) * (Fintype.card k : ℝ) ^ M := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hreal]
    exact hbound
  have hpow : (Fintype.card k : ℝ) ^ (2 * M) =
      (Fintype.card k : ℝ) ^ (2 * M - 1) * (Fintype.card k : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  have hfac : (N : ℝ) * (Fintype.card k : ℝ) - (Fintype.card k : ℝ) ^ (2 * M) =
      ((N : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)) * (Fintype.card k : ℝ) := by
    rw [hpow]
    ring
  rw [hfac, abs_mul, abs_of_pos hq] at habs
  have hqM : (0 : ℝ) ≤ (Fintype.card k : ℝ) ^ M := by positivity
  have hfin : |(N : ℝ) - (Fintype.card k : ℝ) ^ (2 * M - 1)| * (Fintype.card k : ℝ) ≤
      (Fintype.card k : ℝ) ^ M * (Fintype.card k : ℝ) := by
    nlinarith
  exact le_of_mul_le_mul_right hfin hq
end GlobalTheory.CompanionTheory.SW.QuadricCount
