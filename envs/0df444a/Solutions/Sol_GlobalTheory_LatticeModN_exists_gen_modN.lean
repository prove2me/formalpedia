-- Prove2me | solution 1 for GlobalTheory.LatticeModN.exists_gen_modN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:37.660652+00:00
-- url     : https://prove2.me/submissions/dbc8c197-9bd6-4994-83be-d5730b5443a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIndependentBasisCoprimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankEqRankMulDegreeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRankTwoBasisModN
import Theorems.Thm_GlobalTheory_T_exists_independent_basis_coprime
import Theorems.Thm_GlobalTheory_T_finrank_eq_rank_mul_degree


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.LatticeModN
namespace GlobalTheory.LatticeModN
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] [Module.Finite ℤ M] [IsAddTorsionFree M], Module.finrank ℤ M = 2 * Module.finrank ℚ F → ∀ N : ℕ, 1 ≤ N → ∃ x : Fin 2 → M, (∀ m : M, ∃ (a b : 𝓞 F) (m' : M), m = a • x 0 + b • x 1 + N • m') ∧ ∀ a b : 𝓞 F, (∃ m' : M, a • x 0 + b • x 1 = N • m') → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b := by
  intro F _ _ M _ _ _ _ hrk N hN
  rcases Nat.lt_or_ge N 2 with h1 | h2
  · obtain rfl : N = 1 := by omega
    refine ⟨0, fun m => ⟨0, 0, m, by simp⟩, fun a b _ => ⟨by simp, by simp⟩⟩
  obtain ⟨r, x, hli, c, hc0, hcop, hspan⟩ := GlobalTheory.T.exists_independent_basis_coprime F M N h2
  have hr := GlobalTheory.T.finrank_eq_rank_mul_degree F M r x hli c hc0 hspan
  have hf : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hr2 : r = 2 := by
    rw [hrk] at hr
    exact (Nat.eq_of_mul_eq_mul_right hf hr).symm
  subst hr2
  obtain ⟨u, v, huv⟩ := hcop
  have hNs : ∀ y : M, (N : 𝓞 F) • y = N • y := fun y => Nat.cast_smul_eq_nsmul (𝓞 F) N y
  refine ⟨x, fun m => ?_, fun a b ⟨m', hm'⟩ => ?_⟩
  · obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 F)).1 (hspan m)
    rw [Fin.sum_univ_two] at hg
    refine ⟨u * g 0, u * g 1, v • m, ?_⟩
    calc m = (1 : 𝓞 F) • m := (one_smul _ _).symm
      _ = u • (c • m) + (N : 𝓞 F) • (v • m) := by rw [← huv, add_smul, mul_smul, mul_comm v, mul_smul]
      _ = _ := by rw [← hg, hNs, smul_add, mul_smul, mul_smul]
  · obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 F)).1 (hspan m')
    rw [Fin.sum_univ_two] at hg
    have key : (c * a - N * g 0) • x 0 + (c * b - N * g 1) • x 1 = 0 := by
      have e1 : c • (a • x 0 + b • x 1) = (N : 𝓞 F) • (c • m') := by
        rw [hm', ← hNs, smul_comm]
      rw [← hg, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul] at e1
      rw [sub_smul, sub_smul]
      linear_combination (norm := module) e1
    have hz := Fintype.linearIndependent_iff.1 hli ![c * a - N * g 0, c * b - N * g 1]
      (by simpa [Fin.sum_univ_two] using key)
    have ha : c * a = N * g 0 := sub_eq_zero.1 (hz 0)
    have hb : c * b = N * g 1 := sub_eq_zero.1 (hz 1)
    refine ⟨⟨u * g 0 + v * a, ?_⟩, ⟨u * g 1 + v * b, ?_⟩⟩
    · calc a = (u * c + v * N) * a := by rw [huv, one_mul]
        _ = u * (c * a) + N * (v * a) := by ring
        _ = _ := by rw [ha]; ring
    · calc b = (u * c + v * N) * b := by rw [huv, one_mul]
        _ = u * (c * b) + N * (v * b) := by ring
        _ = _ := by rw [hb]; ring
end GlobalTheory.LatticeModN
