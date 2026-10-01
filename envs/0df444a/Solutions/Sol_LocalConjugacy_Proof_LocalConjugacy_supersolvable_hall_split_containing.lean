-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.supersolvable_hall_split_containing
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:32:31.038445+00:00
-- url     : https://prove2.me/submissions/6eafc19e-7d24-41fd-8a52-8fb5b67c145a

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

namespace LocalConjugacy

variable {G F : Type*} [Group G] [Group F]

private theorem conjugate_comp (g h : G) (H : Subgroup G) :
    conjugate g (conjugate h H) = conjugate (g * h) H := by
  unfold conjugate
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

@[simp] private theorem conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
  unfold conjugate
  have he : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  change H.map (MulAut.conj (1 : G)).toMonoidHom = H
  rw [he, Subgroup.map_id]

@[simp] private theorem conjugate_inv_cancel (g : G) (H : Subgroup G) :
    conjugate g⁻¹ (conjugate g H) = H := by
  rw [conjugate_comp, inv_mul_cancel, conjugate_one]

private theorem conjugate_mono (g : G) {H K : Subgroup G} (h : H ≤ K) :
    conjugate g H ≤ conjugate g K := Subgroup.map_mono h



private theorem conjugate_le_iff (g : G) (H K : Subgroup G) :
    conjugate g H ≤ K ↔ H ≤ conjugate g⁻¹ K := by
  constructor
  · intro h
    simpa using conjugate_mono g⁻¹ h
  · intro h
    simpa only [conjugate_comp, mul_inv_cancel, conjugate_one] using conjugate_mono g h

private theorem sylow_smul_toSubgroup (p : ℕ) (g : G) (P : Sylow p G) :
    (g • P).toSubgroup = conjugate g P.toSubgroup := by
  simp only [Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.pointwise_smul_def, conjugate]
  congr 1

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy















private theorem IsHall.coprime {G : Type*} [Group G] {π : Set ℕ}
    {H : Subgroup G} (hH : IsHall π H) : (Nat.card H).Coprime H.index :=
  coprime_of_disjoint_primes hH.1 hH.2







private theorem exists_conjugate_sylow_le_of_not_dvd_index {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (Q : Subgroup G) (hQ : ¬ p ∣ Q.index) :
    ∃ g : G, conjugate g P.toSubgroup ≤ Q := by
  classical
  let R : Sylow p Q := Classical.choice inferInstance
  have hR : ¬ p ∣ (R.toSubgroup.map Q.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul Fact.out R.not_dvd_index hQ
  let T : Sylow p G := (R.isPGroup'.map Q.subtype).toSylow hR
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P T
  refine ⟨g, ?_⟩
  rw [← sylow_smul_toSubgroup, hg]
  exact (Subgroup.map_le_range Q.subtype R.toSubgroup).trans (le_of_eq Q.range_subtype)





end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy









universe u



/-- The finite split Hall decomposition for a prime cutoff. -/
private theorem supersolvable_hall_split {G : Type*} [Group G] [Finite G]
    (hG : Supersolvable G) (n : ℕ) :
    ∃ M Q : Subgroup G, M.Normal ∧ IsHall {p | n < p} M ∧
      M.IsComplement' Q ∧ IsHall {p | p ≤ n} Q := by
  obtain ⟨M, hMn, hM⟩ := supersolvable_exists_normalHall hG n
  letI := hMn
  obtain ⟨Q, hQ⟩ := Subgroup.exists_right_complement'_of_coprime hM.coprime
  refine ⟨M, Q, hMn, hM, hQ, ?_, ?_⟩
  · intro p hp hd
    have hn := hM.2 p hp (hQ.card_right ▸ hd)
    exact Nat.le_of_not_gt hn
  · intro p hp hd hn
    have hh := hM.1 p hp (hQ.index_eq_card ▸ hd)
    exact Nat.not_lt_of_ge hn hh

/-- The Hall complement can be chosen to contain any prescribed Sylow
subgroup at a prime below the cutoff. -/
private theorem supersolvable_hall_split_containing_preparedProof {G : Type*} [Group G] [Finite G]
    (hG : Supersolvable G) {n p : ℕ} [Fact p.Prime] (hpn : p ≤ n)
    (P : Sylow p G) (M : Subgroup G) [M.Normal] (hM : IsHall {r | n < r} M) :
    ∃ Q : Subgroup G, M.IsComplement' Q ∧ IsHall {r | r ≤ n} Q ∧ P.toSubgroup ≤ Q := by
  obtain ⟨M', Q, hM'n, hM', hMQ, hQ⟩ := supersolvable_hall_split hG n
  letI := hM'n
  have he : M' = M := hM'.eq_of_normal hM
  subst M'
  obtain ⟨g, hg⟩ := exists_conjugate_sylow_le_of_not_dvd_index P Q
    (fun hd => hQ.2 p Fact.out hd hpn)
  let e := (MulAut.conj g⁻¹).toMonoidHom
  have hMe : M.map e = M := Subgroup.Normal.map_conj_eq M g⁻¹
  have hQe := hQ.map_surjective e (MulAut.conj g⁻¹).surjective
  have hce := complement_map_of_disjoint hMQ e (MulAut.conj g⁻¹).surjective
    (disjoint_of_cutoff_primes (hM.1.map e) hQe.1)
  rw [hMe] at hce
  exact ⟨Q.map e, hce, hQe, (conjugate_le_iff g P.toSubgroup Q).mp hg⟩

end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1

theorem solution :
∀ {G : Type u_1} [inst : Group.{u_1} G] [Finite.{u_1 + 1} G]
  (hG : @LocalConjugacy.Proof.LocalConjugacy.Supersolvable.{u_1} G inst) {n p : Nat} [Fact (Nat.Prime p)]
  (hpn : @LE.le.{0} Nat instLENat p n) (P : @Sylow.{u_1} p G inst) (M : @Subgroup.{u_1} G inst)
  [@Subgroup.Normal.{u_1} G inst M]
  (hM :
    @LocalConjugacy.Proof.LocalConjugacy.IsHall.{u_1} G inst
      (@Set.ofPred.{0} Nat fun (r : Nat) => @LT.lt.{0} Nat instLTNat n r) M),
  @Exists.{u_1 + 1} (@Subgroup.{u_1} G inst) fun (Q : @Subgroup.{u_1} G inst) =>
    And (@Subgroup.IsComplement'.{u_1} G inst M Q)
      (And
        (@LocalConjugacy.Proof.LocalConjugacy.IsHall.{u_1} G inst
          (@Set.ofPred.{0} Nat fun (r : Nat) => @LE.le.{0} Nat instLENat r n) Q)
        (@LE.le.{u_1} (@Subgroup.{u_1} G inst)
          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
          (@Sylow.toSubgroup.{u_1} p G inst P) Q)) :=
  @LocalConjugacy.Proof.LocalConjugacy.supersolvable_hall_split_containing_preparedProof
