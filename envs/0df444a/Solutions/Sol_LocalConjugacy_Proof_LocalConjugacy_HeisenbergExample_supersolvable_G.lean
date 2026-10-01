-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.supersolvable_G
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:32:37.037439+00:00
-- url     : https://prove2.me/submissions/25ee1e68-c650-4a91-a6e1-7c6b7badb7c3

import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples
import Definitions.Def_LocalConjugacy_Proof_Definitions
import Definitions.Def_LocalConjugacy_Proof_Bridges
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Heisenberg
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergStructure
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergSupersolvable
import Definitions.Def_LocalConjugacy_Proof_ConcreteGroups
import Definitions.Def_LocalConjugacy_Targets
import Definitions.Def_LocalConjugacy_Proof_Compactness
import Definitions.Def_LocalConjugacy_Proof_ProfiniteSylow
import Definitions.Def_LocalConjugacy_Proof_StructuralImages
import Definitions.Def_LocalConjugacy_Proof_FiniteAbelianCohomology
import Definitions.Def_LocalConjugacy_Proof_AbelianComplement
import Definitions.Def_LocalConjugacy_Proof_QuotientReduction
import Definitions.Def_LocalConjugacy_Proof_Cohomology
import Definitions.Def_LocalConjugacy_Proof_InvariantRestriction
import Definitions.Def_LocalConjugacy_Proof_CocycleActions
import Definitions.Def_LocalConjugacy_Proof_CoprimeCohomology
import Definitions.Def_LocalConjugacy_Proof_CocycleDescent
import Definitions.Def_LocalConjugacy_Proof_CocycleZorn
import Definitions.Def_LocalConjugacy_Proof_CocycleProducts
import Definitions.Def_LocalConjugacy_Proof_FiniteCoefficientSubgroup
import Definitions.Def_LocalConjugacy_Proof_CocycleInvarianceSubgroup
import Definitions.Def_LocalConjugacy_Proof_CocycleInjectivity
import Definitions.Def_LocalConjugacy_Proof_CocycleRebase
import Definitions.Def_LocalConjugacy_Proof_FiniteHall
import Definitions.Def_LocalConjugacy_Proof_SupersolvableStructure
import Definitions.Def_LocalConjugacy_Proof_ProfiniteHall
import Definitions.Def_LocalConjugacy_Proof_ActionProductTopology
import Definitions.Def_LocalConjugacy_Proof_HallCohomology
import Definitions.Def_LocalConjugacy_Proof_SupersolvableRestriction
import Definitions.Def_LocalConjugacy_Proof_NilpotentCoefficients
import Definitions.Def_LocalConjugacy_Proof_NonabelianComplement
import Definitions.Def_LocalConjugacy_Proof_ComplementSupersolvable
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Quaternion
import Definitions.Def_LocalConjugacy_Proof_QuaternionCohomology
import Definitions.Def_LocalConjugacy_Proof_QuaternionMatrices
import Definitions.Def_LocalConjugacy_Proof_QuaternionAction
import Definitions.Def_LocalConjugacy_Proof_QuaternionComplements

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy.HeisenbergExample

set_option maxRecDepth 10000
set_option maxHeartbeats 0






















private theorem step (L U : Subgroup G) (x : G) (n : ℕ)
    (hLU : L ≤ U) (hx : x ∈ U)
    (h : ∀ u ∈ U, ∃ k : Fin n, u * (x ^ k.val)⁻¹ ∈ L) :
    U = L ⊔ Subgroup.zpowers x := by
  apply le_antisymm _ (sup_le hLU (Subgroup.zpowers_le.mpr hx))
  intro u hu
  obtain ⟨k, hk⟩ := h u hu
  have ha : u * (x ^ k.val)⁻¹ ∈ L ⊔ Subgroup.zpowers x :=
    (show L ≤ L ⊔ Subgroup.zpowers x from le_sup_left) hk
  have hb : x ^ k.val ∈ L ⊔ Subgroup.zpowers x :=
    (show Subgroup.zpowers x ≤ L ⊔ Subgroup.zpowers x from le_sup_right)
      (Subgroup.npow_mem_zpowers x k.val)
  simpa using (L ⊔ Subgroup.zpowers x).mul_mem ha hb

private theorem step_Z : Z = ⊥ ⊔ Subgroup.zpowers (diagonal (Multiplicative.ofAdd 1)) := by
  apply step ⊥ Z (diagonal (Multiplicative.ofAdd 1)) 3 bot_le
  · exact ⟨_, rfl⟩
  · exact (by decide : ∀ z ∈ Z, ∃ k : Fin 3,
      z * (diagonal (Multiplicative.ofAdd 1) ^ k.val)⁻¹ = 1)

private theorem step_V : V = Z ⊔ Subgroup.zpowers v := by
  apply step _ _ _ 3
  · exact (by decide : ∀ x : G, x ∈ Z → x ∈ V)
  · decide
  · decide

private theorem step_N : N = V ⊔ Subgroup.zpowers shift := by
  apply step _ _ _ 3
  · exact inf_le_left
  · decide
  · decide

private theorem step_M : M = N ⊔ Subgroup.zpowers c := by
  apply step _ _ _ 3
  · exact (by decide : ∀ x : G, x ∈ N → x ∈ M)
  · decide
  · decide

private theorem step_G : (⊤ : Subgroup G) = M ⊔ Subgroup.zpowers t := by
  apply step _ _ _ 2 le_top (Subgroup.mem_top _)
  intro u _
  exact (by decide : ∀ x : G, ∃ k : Fin 2, x * (t ^ k.val)⁻¹ ∈ M) u

/-- The invariant cyclic series has orders `1,3,9,27,81,162`. -/
private theorem supersolvable_G_preparedProof : Supersolvable G := by
  let s : ℕ → Subgroup G := fun i =>
    if i = 0 then ⊥ else if i = 1 then Z else if i = 2 then V
    else if i = 3 then N else if i = 4 then M else ⊤
  have hs : ∀ i, s i ≤ s (i + 1) := by
    intro i
    by_cases hi : i < 5
    · interval_cases i
      · exact bot_le
      · change Z ≤ V; rw [step_V]; exact le_sup_left
      · change V ≤ N; rw [step_N]; exact le_sup_left
      · change N ≤ M; rw [step_M]; exact le_sup_left
      · exact le_top
    · have hi0 : i ≠ 0 := by omega
      have hi1 : i ≠ 1 := by omega
      have hi2 : i ≠ 2 := by omega
      have hi3 : i ≠ 3 := by omega
      have hi4 : i ≠ 4 := by omega
      have hj2 : i + 1 ≠ 2 := by omega
      have hj3 : i + 1 ≠ 3 := by omega
      have hj4 : i + 1 ≠ 4 := by omega
      simp [s, hi0, hi1, hi2, hi3, hi4, hj2, hj3, hj4]
  refine ⟨5, s, rfl, rfl, monotone_nat_of_le_succ hs, ?_, ?_⟩
  · intro i
    dsimp [s]
    split_ifs <;> infer_instance
  · intro i hi
    interval_cases i
    · exact ⟨diagonal (Multiplicative.ofAdd 1), step_Z⟩
    · exact ⟨v, step_V⟩
    · exact ⟨shift, step_N⟩
    · exact ⟨c, step_M⟩
    · exact ⟨t, step_G⟩

end LocalConjugacy.HeisenbergExample

end LocalConjugacy.Proof

end

theorem solution :
@LocalConjugacy.Proof.LocalConjugacy.Supersolvable.{0} LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.G
  (@SemidirectProduct.instGroup.{0, 0} LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.B
    LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.S
    (@Pi.group.{0, 0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (fun (a : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) =>
        LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.C3)
      fun (i : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) =>
      @Multiplicative.group.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@AddGroupWithOne.toAddGroup.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@DivisionRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@Field.toDivisionRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  Nat.fact_prime_three))))))
    (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.action) :=
  @LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.supersolvable_G_preparedProof
