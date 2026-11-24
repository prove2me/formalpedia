-- Prove2me | solution 1 for GlobalTheory.SepIdem.exists_separability_element
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:10:47.726347+00:00
-- url     : https://prove2.me/submissions/5cd97928-8e23-467a-9775-6989ce1ef1fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormallyUnramifiedOfIsReduced
import Theorems.Thm_GlobalTheory_SepIdem_exists_smul_kaehler_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct nonZeroDivisors
open GlobalTheory GlobalTheory.SepIdem
namespace GlobalTheory.SepIdem
theorem _root_.solution (O : Type) [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O]
    [IsReduced O] :
    ∃ (N : ℕ) (e : TensorProduct ℤ O O), 0 < N ∧ Algebra.TensorProduct.lmul' ℤ e = (N : O) ∧
      ∀ c : O, (TensorProduct.tmul ℤ c (1 : O) - TensorProduct.tmul ℤ (1 : O) c) * e = 0 := by
  obtain ⟨N, hN, hΩ⟩ := exists_smul_kaehler_eq_zero O
  set I := KaehlerDifferential.ideal ℤ O with hI
  have hfg : I.FG := KaehlerDifferential.ideal_fg ℤ O
  have : Module.Finite (O ⊗[ℤ] O) I := Module.Finite.iff_fg.2 hfg
  have hsq : ∀ x ∈ I, (N : O ⊗[ℤ] O) * x ∈ I ^ 2 := by
    intro x hx
    have h := hΩ (I.toCotangent ⟨x, hx⟩)
    have h2 : I.toCotangent ((N : O ⊗[ℤ] O) • ⟨x, hx⟩) = 0 := by
      rw [Nat.cast_smul_eq_nsmul, map_nsmul]
      exact (Nat.cast_smul_eq_nsmul O N (show Ω[O⁄ℤ] from I.toCotangent ⟨x, hx⟩)).symm.trans h
    exact (Ideal.toCotangent_eq_zero I _).1 h2
  obtain ⟨p, hp, -, hc, h0⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero (O ⊗[ℤ] O)
      (algebraMap (O ⊗[ℤ] O) (Module.End (O ⊗[ℤ] O) I) (N : O ⊗[ℤ] O)) I (by
        rintro _ ⟨⟨x, hx⟩, rfl⟩
        rw [Submodule.mem_smul_top_iff, smul_eq_mul, ← pow_two]
        exact hsq x hx)
  rw [Polynomial.aeval_algebraMap_apply] at h0
  refine ⟨N ^ p.natDegree, Polynomial.aeval (N : O ⊗[ℤ] O) p, pow_pos hN _, ?_, fun c => ?_⟩
  · rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, map_add, hp.coeff_natDegree,
      one_smul, map_sum, Finset.sum_eq_zero, zero_add, map_pow, map_natCast, Nat.cast_pow]
    intro k hk
    have : p.coeff k ∈ I :=
      Ideal.pow_le_self (Nat.sub_ne_zero_of_lt (Finset.mem_range.1 hk)) (hc k)
    have h : Algebra.TensorProduct.lmul' ℤ (p.coeff k) = 0 := this
    rw [smul_eq_mul, map_mul, h, zero_mul]
  · have hm := KaehlerDifferential.one_smul_sub_smul_one_mem_ideal ℤ c
    have := congrArg Subtype.val (LinearMap.congr_fun h0 ⟨_, hm⟩)
    have h : Polynomial.aeval (N : O ⊗[ℤ] O) p * ((1 : O) ⊗ₜ[ℤ] c - c ⊗ₜ[ℤ] (1 : O)) = 0 := this
    rw [← neg_sub, neg_mul, mul_comm, h, neg_zero]
end GlobalTheory.SepIdem
