-- Prove2me | solution 1 for N25.psi_inertia_witness
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:41.109045+00:00
-- url     : https://prove2.me/submissions/73783723-46d8-40a8-b1c9-72323652207f

import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace

noncomputable section

namespace N25

local instance prime5_N25_psi_inertia_witness_se821f4 : Fact (Nat.Prime 5) := ⟨by decide⟩

local instance prime71_N25_psi_inertia_witness_se821f4 : Fact (Nat.Prime 71) := ⟨by decide⟩

/-- Inertia contains an element with quintic character value 57. -/
theorem _root_.solution :
    ∃ τ : G5, τ ∈ I5 ∧ psi (r5 τ) = ZMod.unitOfCoprime 57 (by decide) := by
  let u : ℤ_[5]ˣ := (IsUnit.unit (show IsUnit (2 : ℤ_[5]) from by
    exact PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr (by decide : Nat.Coprime 5 2))))
  have hu : (u : ℤ_[5]) = 2 := IsUnit.unit_spec _
  obtain ⟨σ,hσ,hs⟩ :=
    (ExtCitation.primeLocalPlace q5).exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq (p := 5)
      (ExtCitation.liesOverPrime_primeLocalPlace q5) u
  obtain ⟨τ,_,hτ⟩ := ValuationSubring.exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq 5 σ hσ
  refine ⟨τ, ?_, ?_⟩
  · change localGaloisToGlobal 5 τ ∈ (ExtCitation.primeLocalPlace q5).inertiaSubgroupIn ℚ
    rw [hτ]; exact hσ
  · change psi (localGaloisToGlobal 5 τ) = _
    rw [hτ]
    have hred := cyclotomicCharacter.toZModPow (L := AlgebraicClosure ℚ) 5 (n := 2) σ.toRingEquiv
    rw [hs, hu] at hred
    have hchi : chi25 σ = ZMod.unitOfCoprime 2 (by decide) := by
      apply Units.ext
      change (modularCyclotomicCharacter (AlgebraicClosure ℚ)
        (IsAlgClosed.card_rootsOfUnity_eq (AlgebraicClosure ℚ) 25) σ.toRingEquiv : ZMod 25) = 2
      simpa only [map_ofNat] using hred.symm
    change psiBar (chi25 σ) = _
    rw [hchi]
    rfl

end N25
