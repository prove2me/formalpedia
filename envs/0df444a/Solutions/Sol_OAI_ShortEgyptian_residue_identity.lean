-- Prove2me | solution 1 for OAI.ShortEgyptian.residue_identity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:57:11.458985+00:00
-- url     : https://prove2.me/submissions/9b7265d3-060a-4f7f-8824-399efdf64b4a

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/Basic.lean:L48-L69
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.residue_identity. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Theorems.Thm_OAI_ShortEgyptian_quotient_spec

-- ---- from OAI.NumberTheory.ShortEgyptian.Basic ----
namespace OAI

namespace ShortEgyptian

theorem residue_spec {v u : ℕ} (hv : 0 < v) (hu : 0 < u) :
    residue v u (quotient v u) < u ∧
      v + residue v u (quotient v u) = u * quotient v u := by
  obtain ⟨_, hlo, hhi⟩ := quotient_spec hv hu
  unfold residue
  omega

theorem residue_identity {M Q u t : ℕ} (hM : 0 < M) (hQ : 0 < Q)
    (hu : 0 < u) (ht : 0 < t) (htM : t ∣ M) :
    let z := quotient (Q * t) u
    let h := residue (Q * t) u z
    (u : ℚ) / (M * Q) =
      1 / ((M / t : ℕ) * (z : ℚ)) + (h : ℚ) / (M * Q * z) := by
  dsimp
  let z := quotient (Q * t) u
  let h := residue (Q * t) u z
  change (u : ℚ) / (M * Q) = 1 / ((M / t : ℕ) * (z : ℚ)) + h / (M * Q * z)
  have hMQ : (M : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  have hQQ : (Q : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hQ
  have hz : 0 < z := (quotient_spec (Nat.mul_pos hQ ht) hu).1
  have hzQ : (z : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hz
  have hdNat : M / t * t = M := Nat.div_mul_cancel htM
  have hdpos : 0 < M / t := by nlinarith
  have hdQ : ((M / t : ℕ) : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hdpos
  have hd : ((M / t : ℕ) : ℚ) * t = M := by exact_mod_cast hdNat
  have hh : (Q : ℚ) * t + h = u * z := by
    exact_mod_cast (residue_spec (Nat.mul_pos hQ ht) hu).2
  field_simp
  nlinarith [congrArg (fun x : ℚ => x * (((M / t : ℕ) : ℚ) * Q)) hh]

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian


theorem solution : type_of% @_root_.OAI.ShortEgyptian.residue_identity := @_root_.OAI.ShortEgyptian.residue_identity
