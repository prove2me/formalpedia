-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.exists_compactOpen_psiN_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:13:33.900646+00:00
-- url     : https://prove2.me/submissions/1a8872b1-702f-4837-8d9b-598c27c3df5f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_ball_addChar_eq_one
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_exists_openSubgroup_isCompact_subset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
open ValuativeRel Topology
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {ψ₀ : AddChar F ℂ} (hψ : Continuous ψ₀) :
    ∃ K : Subgroup (Iwasawa.unipotent F n), IsCompact (K : Set (Iwasawa.unipotent F n)) ∧
      IsOpen (K : Set (Iwasawa.unipotent F n)) ∧ ∀ k ∈ K, psiN ψ₀ (k : GL (Fin n) F) = 1 := by
  obtain ⟨γ, hγ⟩ := exists_ball_addChar_eq_one F hψ
  set A := (valuation F).ltAddSubgroup γ
  have hAo : IsOpen (A : Set F) :=
    AddSubgroup.isOpen_of_mem_nhds A ((IsValuativeTopology.hasBasis_nhds_zero F).mem_of_mem trivial)
  let V : Set (Iwasawa.unipotent F n) :=
    ⋂ i : Fin n, ⋂ j : Fin n, {u | ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ A ∨
      j.val ≠ i.val + 1}
  have hVo : IsOpen V := by
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    by_cases hij : j.val = i.val + 1
    · have : {u : Iwasawa.unipotent F n | ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ A ∨
          j.val ≠ i.val + 1} = (fun u : Iwasawa.unipotent F n =>
            ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) ⁻¹' (A : Set F) := by
        ext u
        simp [hij]
      rw [this]
      exact hAo.preimage ((GLnLocal.continuous_entry F n i j).comp continuous_subtype_val)
    · have : {u : Iwasawa.unipotent F n | ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ A ∨
          j.val ≠ i.val + 1} = Set.univ := by
        ext u
        simp [hij]
      rw [this]
      exact isOpen_univ
  have h1V : (1 : Iwasawa.unipotent F n) ∈ V := by
    simp only [V, Set.mem_iInter, Set.mem_ofPred_eq]
    intro i j
    by_cases hij : j.val = i.val + 1
    · left
      have hne : i ≠ j := fun e => by rw [e] at hij; omega
      rw [OneMemClass.coe_one, Units.val_one, Matrix.one_apply_ne hne]
      exact A.zero_mem
    · exact Or.inr hij
  obtain ⟨K, hKc, hKV⟩ := exists_openSubgroup_isCompact_subset (hVo.mem_nhds h1V)
  refine ⟨K.toSubgroup, hKc, K.isOpen, fun k hk => ?_⟩
  have hkV : k ∈ V := hKV hk
  simp only [V, Set.mem_iInter, Set.mem_ofPred_eq] at hkV
  refine hγ _ ?_
  refine Valuation.mem_ltAddSubgroup_iff.1 (A.sum_mem fun i _ => A.sum_mem fun j _ => ?_)
  split_ifs with hij
  · exact (hkV i j).resolve_right (not_not.2 hij)
  · exact A.zero_mem
end GroundTheory.Automorphic.Whittaker
