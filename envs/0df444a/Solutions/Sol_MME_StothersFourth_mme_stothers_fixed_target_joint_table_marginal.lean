-- Prove2me | solution 1 for MME.StothersFourth.mme_stothers_fixed_target_joint_table_marginal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:07:38.47172+00:00
-- url     : https://prove2.me/submissions/fa6470b7-dcba-4912-9738-ecf661bfb911

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables
import Theorems.Thm_mme_stothers_fixed_outer_profile_arithmetic

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000

namespace MME.StothersFourth

private theorem fixedHashTargetMarginal_orbit_support :
    ∀ (q : Fin 10) (sigma : Fin 3 → Fin 9),
      fixedSameOrbitExplicit sigma (classRep q) →
        (∑ s, (sigma s).val) = 8 := by
  intro q sigma h
  have hrep : (∑ s, (classRep q s).val) = 8 := by
    fin_cases q <;>
      norm_num [classRep, cwFourthBlockType, Fin.sum_univ_three]
  rcases h with h | h | h | h | h | h <;>
    rcases h with ⟨h0, h1, h2⟩ <;>
    simp only [Fin.sum_univ_three, h0, h1, h2] at * <;>
    omega

private theorem fixedHashTargetMarginal_class_card
    (l : Fin 3) (r : Fin 9) (q : Fin 10) :
    Fintype.card
        {sigma : {sigma : FixedHashSupportTriple // sigma.1 l = r} //
          fixedSameOrbitExplicit sigma.1.1 (classRep q)} =
      fixedClassMarginalMultiplicity q r := by
  let e :
      {sigma : {sigma : FixedHashSupportTriple // sigma.1 l = r} //
          fixedSameOrbitExplicit sigma.1.1 (classRep q)} ≃
        {sigma // sigma ∈
          (fixedClassOrbit q).filter (fun sigma ↦ sigma l = r)} := {
    toFun sigma := ⟨sigma.1.1, by
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, sigma.2⟩
      · exact sigma.1.2⟩
    invFun sigma := by
      have hs := Finset.mem_filter.mp sigma.2
      have hsOrbit := Finset.mem_filter.mp hs.1
      exact ⟨⟨⟨sigma.1,
        fixedHashTargetMarginal_orbit_support q sigma.1 hsOrbit.2⟩,
          hs.2⟩, hsOrbit.2⟩
    left_inv sigma := by
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv sigma := by
      apply Subtype.ext
      rfl
  }
  calc
    Fintype.card
        {sigma : {sigma : FixedHashSupportTriple // sigma.1 l = r} //
          fixedSameOrbitExplicit sigma.1.1 (classRep q)} =
        Nat.card
          {sigma // sigma ∈
            (fixedClassOrbit q).filter (fun sigma ↦ sigma l = r)} := by
      calc
        Fintype.card
            {sigma : {sigma : FixedHashSupportTriple // sigma.1 l = r} //
              fixedSameOrbitExplicit sigma.1.1 (classRep q)} =
            Nat.card
              {sigma : {sigma : FixedHashSupportTriple // sigma.1 l = r} //
                fixedSameOrbitExplicit sigma.1.1 (classRep q)} :=
          Nat.card_eq_fintype_card.symm
        _ = Nat.card
              {sigma // sigma ∈
                (fixedClassOrbit q).filter (fun sigma ↦ sigma l = r)} :=
          Nat.card_congr e
    _ = ((fixedClassOrbit q).filter
        (fun sigma ↦ sigma l = r)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = fixedClassMarginalMultiplicity q r :=
      mme_stothers_fixed_outer_profile_arithmetic.2.2.1 q l r

private theorem fixedHashTargetMarginal_sum_ite_const_eq_card
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (p : alpha → Prop) [DecidablePred p] (c : ℕ) :
    (∑ x : alpha, if p x then c else 0) =
      Fintype.card {x : alpha // p x} * c := by
  rw [Fintype.card_subtype]
  calc
    (∑ x : alpha, if p x then c else 0) =
        ∑ x ∈ (Finset.univ.filter p), c := by
      rw [Finset.sum_filter]
    _ = (Finset.univ.filter p).card * c := by simp

end MME.StothersFourth

theorem solution
    (m : ℕ) (i : Fin 3) (j : Fin 9) :
    (∑ sigma : {sigma : MME.StothersFourth.FixedHashSupportTriple //
        sigma.1 i = j},
      MME.StothersFourth.fixedHashTargetJointTable m sigma.1) =
        MME.StothersFourth.fixedMarginalCount m j := by
  have hscaleTarget
      (sigma : MME.StothersFourth.FixedHashSupportTriple) :
      MME.StothersFourth.fixedHashTargetJointTable m sigma =
        m * MME.StothersFourth.fixedHashTargetJointTable 1 sigma := by
    simp only [MME.StothersFourth.fixedHashTargetJointTable,
      MME.StothersFourth.fixedJointMultiplicity,
      MME.StothersFourth.fixedProfileCount]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    split <;> simp
  have hscaleMarginal (r : Fin 9) :
      MME.StothersFourth.fixedMarginalCount m r =
        m * MME.StothersFourth.fixedMarginalCount 1 r := by
    simp [MME.StothersFourth.fixedMarginalCount]
  have hunit : ∀ l : Fin 3, ∀ r : Fin 9,
      (∑ sigma : {sigma : MME.StothersFourth.FixedHashSupportTriple //
          sigma.1 l = r},
        MME.StothersFourth.fixedHashTargetJointTable 1 sigma.1) =
          MME.StothersFourth.fixedMarginalCount 1 r := by
    intro l r
    change
      (∑ sigma : {sigma : MME.StothersFourth.FixedHashSupportTriple //
          sigma.1 l = r},
        ∑ q : Fin 10,
          if MME.StothersFourth.fixedSameOrbitExplicit sigma.1.1
              (MME.StothersFourth.classRep q) then
            1 * MME.StothersFourth.fixedProfileBaseCount q else 0) =
        1 * MME.StothersFourth.fixedMarginalBaseCount r
    rw [Finset.sum_comm]
    calc
      (∑ q : Fin 10,
          ∑ sigma : {sigma : MME.StothersFourth.FixedHashSupportTriple //
              sigma.1 l = r},
            if MME.StothersFourth.fixedSameOrbitExplicit sigma.1.1
                (MME.StothersFourth.classRep q) then
              1 * MME.StothersFourth.fixedProfileBaseCount q else 0) =
          ∑ q : Fin 10,
            MME.StothersFourth.fixedClassMarginalMultiplicity q r *
              MME.StothersFourth.fixedProfileBaseCount q := by
        apply Finset.sum_congr rfl
        intro q _
        rw [MME.StothersFourth.fixedHashTargetMarginal_sum_ite_const_eq_card,
          MME.StothersFourth.fixedHashTargetMarginal_class_card]
        simp
      _ = MME.StothersFourth.fixedMarginalBaseCount r :=
        (mme_stothers_fixed_outer_profile_arithmetic.2.2.2.1 r).symm
      _ = 1 * MME.StothersFourth.fixedMarginalBaseCount r := by simp
  calc
    (∑ sigma : {sigma : MME.StothersFourth.FixedHashSupportTriple //
        sigma.1 i = j},
      MME.StothersFourth.fixedHashTargetJointTable m sigma.1) =
        ∑ sigma : {sigma : MME.StothersFourth.FixedHashSupportTriple //
            sigma.1 i = j},
          m * MME.StothersFourth.fixedHashTargetJointTable 1 sigma.1 := by
      apply Finset.sum_congr rfl
      intro sigma _
      rw [hscaleTarget]
    _ = m *
        ∑ sigma : {sigma : MME.StothersFourth.FixedHashSupportTriple //
            sigma.1 i = j},
          MME.StothersFourth.fixedHashTargetJointTable 1 sigma.1 := by
      rw [Finset.mul_sum]
    _ = m * MME.StothersFourth.fixedMarginalCount 1 j := by
      rw [hunit i j]
    _ = MME.StothersFourth.fixedMarginalCount m j :=
      (hscaleMarginal j).symm
