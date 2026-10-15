-- Prove2me | solution 1 for OAI.Paper320.initialFamily_joint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:21:30.736874+00:00
-- url     : https://prove2.me/submissions/9ef815f8-993c-4e62-90db-3107c2f2c0ff

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/InitialPredicates.lean:L113-L136
-- (upload_full_project.md Phase 4): solution for node OAI.Paper320.initialFamily_joint. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates

-- ---- from OAI.Combinatorics.Sensitivity.HammingBase ----
namespace OAI

/-! Hamming balls used by the initial nested predicates. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I C : Type} [Fintype I]

theorem hammingDist_flip_self (x : I → Bool) (i : I) :
    hammingDist x (flip x {i}) = 1 := by
  have h : (Finset.univ.filter fun j => x j ≠ flip x {i} j) = {i} := by
    ext j
    by_cases hj : j = i
    · subst j
      cases x i <;> simp [flip]
    · simp [flip, hj]
  rw [hammingDist, h]
  simp

theorem hammingDist_le_flip_add_one (x z : I → Bool) (i : I) :
    hammingDist x z ≤ hammingDist (flip x {i}) z + 1 := by
  have h := hammingDist_triangle x (flip x {i}) z
  rw [hammingDist_flip_self] at h
  omega

theorem hammingDist_flip_le_add_one (x z : I → Bool) (i : I) :
    hammingDist (flip x {i}) z ≤ hammingDist x z + 1 := by
  have h := hammingDist_triangle (flip x {i}) x z
  rw [hammingDist_comm (flip x {i}) x, hammingDist_flip_self] at h
  omega

theorem ballPredicate_eq_true [Fintype C] (centers : C → I → Bool) (R : ℕ)
    (x : I → Bool) :
    ballPredicate centers R x = true ↔ ∃ c, hammingDist x (centers c) ≤ R := by
  simp [ballPredicate]

theorem ballPredicate_no_joint_zero [Fintype C] (centers : C → I → Bool)
    {R S : ℕ} (hRS : R < S) (x : I → Bool) (i : I)
    (hS : ballPredicate centers S x = false)
    (hR : ballPredicate centers R (flip x {i}) = true) : False := by
  obtain ⟨c, hc⟩ := (ballPredicate_eq_true centers R (flip x {i})).1 hR
  have hd := hammingDist_le_flip_add_one x (centers c) i
  have ht := (ballPredicate_eq_true centers S x).2 ⟨c, by omega⟩
  simp_all

theorem ballPredicate_no_joint_one [Fintype C] (centers : C → I → Bool)
    {R S : ℕ} (hRS : R < S) (x : I → Bool) (i : I)
    (hR : ballPredicate centers R x = true)
    (hS : ballPredicate centers S (flip x {i}) = false) : False := by
  obtain ⟨c, hc⟩ := (ballPredicate_eq_true centers R x).1 hR
  have hd := hammingDist_flip_le_add_one x (centers c) i
  have ht := (ballPredicate_eq_true centers S (flip x {i})).2 ⟨c, by omega⟩
  simp_all

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveProfiles ----
namespace OAI

/-! The side and joint profiles count literal flips of the same raw input. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem jointSensitivity_le {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) (B : ℕ)
    (hB : ∀ q q' x, q < q' → F q x = b → F q' x = b →
      jointSensitivityAt (F q) (F q') x ≤ B) : jointSensitivity F b ≤ B := by
  apply Finset.sup_le
  intro q _
  apply Finset.sup_le
  intro q' _
  apply Finset.sup_le
  intro x _
  split_ifs with hx
  · exact hB q q' x hx.1 hx.2.1 hx.2.2
  · exact Nat.zero_le _

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.InitialPredicates ----
namespace OAI

/-! The separated Hamming-ball predicates and their explicit sensitive blocks. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem initialFamily_joint (d M : ℕ) (b : Bool) :
    jointSensitivity (initialFamily d M) b = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply jointSensitivity_le
  intro q q' x hqq hx hx'
  have hrad : d - q'.val < d - q.val := by omega
  unfold jointSensitivityAt
  have he : (Finset.univ.filter fun i =>
      initialFamily d M q (flip x {i}) ≠ initialFamily d M q x ∧
      initialFamily d M q' (flip x {i}) ≠ initialFamily d M q' x) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i _ hi
    obtain ⟨hi, hi'⟩ := hi
    cases b with
    | false =>
        have hflip : initialFamily d M q' (flip x {i}) = true := by
          simpa [hx'] using hi'
        exact ballPredicate_no_joint_zero blockCenter hrad x i hx hflip
    | true =>
        have hflip : initialFamily d M q (flip x {i}) = false := by
          simpa [hx] using hi
        exact ballPredicate_no_joint_one blockCenter hrad x i hx' hflip
  rw [he]
  simp

end Paper320

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper320
open scoped Classical

theorem solution (d M : ℕ) (b : Bool) :
    jointSensitivity (initialFamily d M) b = 0 := by
  first
    | exact OAI.Paper320.initialFamily_joint d M b
    | exact OAI.Paper320.initialFamily_joint
    | (apply OAI.Paper320.initialFamily_joint <;> assumption)
    | (intros; apply OAI.Paper320.initialFamily_joint <;> assumption)
