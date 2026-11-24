-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.leviPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:48:14.593194+00:00
-- url     : https://prove2.me/submissions/50733717-abb2-4a91-abe3-b243b6d7695a

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryBlockTriangularLeviPartUnitary
import Theorems.Thm_GlobalTheory_SatakeWeyl_blockDiagPart_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_P_fSatake_cTJ
import Theorems.Thm_GlobalTheory_SatakeWeyl_antiJ_mul_apply
import Theorems.Thm_GlobalTheory_SatakeWeyl_exists_mat
import Theorems.Thm_GlobalTheory_SatakeWeyl_mat_inv_apply
import Theorems.Thm_GlobalTheory_UnitarySwap_antiJ_mul_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution : LeviPart := by
  intro L _ _ σ n β hβ g hg
  have hβ' : ∀ a b, β a = β b ↔ β a.rev = β b.rev := fun a b =>
    ⟨hβ a b, fun h => by simpa using hβ _ _ h⟩
  have h0 : (mat g⁻¹).BlockTriangular β := by
    letI : Invertible (mat g) := (g : GL (Fin n) L).invertible
    have e : mat g⁻¹ = (mat g)⁻¹ := by simp [mat]
    rw [e]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg
  have h1 := blockDiagPart_mul β _ _ h0 hg (mat_inv_mul g)
  set M : Matrix (Fin n) (Fin n) L := Matrix.of fun a b => if β a = β b then mat g a b else 0 with hM
  have h2 : antiJ L n * (cT σ M * antiJ L n) =
      Matrix.of fun a b => if β a = β b then mat g⁻¹ a b else 0 := by
    ext a b
    rw [antiJ_mul_apply, P.fSatake_cTJ, Matrix.of_apply, mat_inv_apply, hM, Matrix.of_apply]
    by_cases h : β a = β b
    · rw [if_pos h, if_pos ((hβ' _ _).1 h.symm)]
    · rw [if_neg h, if_neg (fun e => h ((hβ' _ _).2 e).symm), map_zero]
  have h3 : cT σ M * antiJ L n * M = antiJ L n := by
    rw [← h2] at h1
    calc cT σ M * antiJ L n * M
        = antiJ L n * (antiJ L n * (cT σ M * antiJ L n) * M) := by
          rw [← Matrix.mul_assoc (antiJ L n), ← Matrix.mul_assoc (antiJ L n),
            GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.one_mul]
      _ = antiJ L n := by rw [h1, Matrix.mul_one]
  obtain ⟨m, hm⟩ := exists_mat M h3
  have hmL : m ∈ leviU σ β := fun i j h => by rw [hm, hM, Matrix.of_apply, if_neg h]
  refine ⟨m, hmL, fun a b h => by rw [hm, hM, Matrix.of_apply, if_pos h], fun i j h => ?_⟩
  rw [← mat_inv_mul m, mat_mul, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : β i = β l
  · rw [hm, hM, Matrix.of_apply]
    split_ifs with h4
    · rfl
    · rw [hg (lt_of_le_of_ne (hl ▸ h) (Ne.symm h4) : β j < β l)]
  · rw [(leviU σ β).inv_mem hmL i l hl, zero_mul, zero_mul]
end GlobalTheory.SatakeWeyl
