-- Prove2me | solution 1 for OAI.Lech.finiteLength_primary_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:56:32.479887+00:00
-- url     : https://prove2.me/submissions/2bd4ed5a-b74f-4878-b83f-141809a134d7

import Mathlib

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteLengthPrimary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Lech
variable {D M : Type*} [CommRing D] [IsLocalRing D]
  [AddCommGroup M] [Module D M]

lemma finiteLength_primary_annihilator_oai (hM : IsFiniteLength D M) :
    ∃ H : Ideal D, H.radical = IsLocalRing.maximalIdeal D ∧
      H ≤ Module.annihilator D M := by
  obtain ⟨hno,hart⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hM
  let := hno
  let := hart
  let m := IsLocalRing.maximalIdeal D
  have ha : Antitone (fun n : ℕ => m^n • (⊤ : Submodule D M)) := by
    intro n k hnk
    exact Submodule.smul_mono (Ideal.pow_le_pow_right hnk) le_rfl
  obtain ⟨n,hn⟩ := IsArtinian.monotone_stabilizes ⟨_,ha⟩
  have he : m^n • (⊤ : Submodule D M) = m • (m^n • (⊤ : Submodule D M)) := by
    rw [← smul_assoc, Ideal.smul_eq_mul, ← pow_succ']
    exact hn (n+1) (Nat.le_succ n)
  have hz : m^n • (⊤ : Submodule D M) = ⊥ := by
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m _ (IsNoetherian.noetherian _) he.le
    exact IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal D)
  refine ⟨m^(n+1),?_,?_⟩
  · rw [Ideal.radical_pow m (Nat.succ_ne_zero n)]
    exact (IsLocalRing.maximalIdeal.isMaximal D).isPrime.radical
  · intro a ha
    apply Module.mem_annihilator.mpr
    intro x
    have hx : a • x ∈ m^n • (⊤ : Submodule D M) :=
      Submodule.smul_mem_smul (Ideal.pow_le_pow_right (Nat.le_succ n) ha) trivial
    simpa only [hz, Submodule.mem_bot] using hx
end Lech

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Lech.finiteLength_primary_annihilator_oai.{u_1, u_2} := @OAI.Lech.finiteLength_primary_annihilator_oai.{u_1, u_2}
