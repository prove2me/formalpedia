-- Prove2me | solution 1 for NumberField.LevelArith.finiteDimensional_and_finrank_continuousH1Sr_res_inf_eq_finrank_invariants_selmerRep_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c97113ac-a5ed-58c0-ab72-fa6bb41a02d1

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_GroupCohomology_LevelConstantHom
import Theorems.Thm_groupCohomology_nonempty_continuousH1Sr_inf_linearEquiv_eqLevelConstantHom
import Theorems.Thm_NumberField_LevelArith_exists_selmerRep_linearEquiv_levelConstantHom
import Theorems.Thm_groupCohomology_nonempty_invariants_tensor_linearEquiv_eqLevelConstantHom
import Theorems.Thm_NumberField_LevelArith_finiteDimensional_unitsModP_sClass_selmerRep
import Theorems.Thm_ExtCitation_cycloChar_eq_one_of_mem_fixingSubgroup_of_isPrimitiveRoot_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_finiteDimensional_and_finrank_continuousH1Sr_res_inf_eq_finrank_invariants_selmerRep_tensor
p2m_attr_erase "instance" "groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity"
p2m_attr_erase "simp" "groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField.LevelArith

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S)
    [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L)
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
    (htriv : ∀ s : ↥K.fixingSubgroup, (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ L.fixingSubgroup → N.ρ s = 1)
    (V : Submodule (ZMod p) (H1 (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype
      (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)))))
    (hV : ∀ x, x ∈ V ↔ ∃ c : cocycles₁ (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype
        (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))), H1π _ c = x ∧
      ∀ g : ↥K.fixingSubgroup, ∃ a : N.twist ((cycloChar p).comp K.fixingSubgroup.subtype),
        ∀ s t : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup), (g⁻¹ * s * g : ↥K.fixingSubgroup) = t →
          (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)).ρ g (c t) - c s =
            (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)).ρ (s : ↥K.fixingSubgroup) a - a) :
    FiniteDimensional (ZMod p)
        ↥(continuousH1Sr (K.fixingSubgroup.subtype.comp (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype) S
            (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))) ⊓ V) ∧
      Module.finrank (ZMod p)
          ↥(continuousH1Sr (K.fixingSubgroup.subtype.comp (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype) S
              (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype))) ⊓ V) =
        Module.finrank (ZMod p) (selmerRep K L hKL S p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants := by

  have hM : ∀ s : ↥K.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ L.fixingSubgroup →
      (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)).ρ s = 1 := fun s hs => by
    apply LinearMap.ext
    intro v
    change (N.ρ.twist ((cycloChar p).comp K.fixingSubgroup.subtype)) s v = v
    have hc1 : cycloChar p (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = 1 :=
      ExtCitation.cycloChar_eq_one_of_mem_fixingSubgroup_of_isPrimitiveRoot_mem L ζ hζ hζL _ hs
    rw [Representation.twist_apply_apply, htriv s hs]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, hc1, Units.val_one, one_smul, Module.End.one_apply]

  obtain ⟨eA⟩ := groupCohomology.nonempty_continuousH1Sr_inf_linearEquiv_eqLevelConstantHom S K L
    (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)) hM V hV

  obtain ⟨e, he⟩ := NumberField.LevelArith.exists_selmerRep_linearEquiv_levelConstantHom S hpS K L hL hKL ζ hζ hζL

  obtain ⟨eC⟩ := groupCohomology.nonempty_invariants_tensor_linearEquiv_eqLevelConstantHom S
    (L.fixingSubgroup.subgroupOf K.fixingSubgroup) K.fixingSubgroup.subtype ((cycloChar p).comp K.fixingSubgroup.subtype)
    (selmerRep K L hKL S p) N e he

  haveI : FiniteDimensional (ZMod p) (selmerRep K L hKL S p) :=
    (NumberField.LevelArith.finiteDimensional_unitsModP_sClass_selmerRep (p := p) S K L hKL).2.2.2
  haveI : FiniteDimensional (ZMod p) (selmerRep K L hKL S p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) :=
    inferInstanceAs (Module.Finite (ZMod p) (TensorProduct (ZMod p) (selmerRep K L hKL S p) N))
  let E := eA.trans eC.symm
  exact ⟨Module.Finite.equiv E.symm, LinearEquiv.finrank_eq E⟩

end S_NumberField_LevelArith_finiteDimensional_and_finrank_continuousH1Sr_res_inf_eq_finrank_invariants_selmerRep_tensor
end P2MW
export P2MW.S_NumberField_LevelArith_finiteDimensional_and_finrank_continuousH1Sr_res_inf_eq_finrank_invariants_selmerRep_tensor (solution)
