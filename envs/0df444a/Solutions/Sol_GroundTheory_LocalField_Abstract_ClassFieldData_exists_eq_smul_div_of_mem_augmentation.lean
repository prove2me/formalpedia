-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.exists_eq_smul_div_of_mem_augmentation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:22:18.460797+00:00
-- url     : https://prove2.me/submissions/9596fe31-1e0e-4809-ae43-be821cc976fa

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Unramified
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
import Theorems.Thm_GroundTheory_LocalField_Abstract_smul_mem_fixedModule_of_normal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open GroundTheory.LocalField.Abstract.ClassFieldData
open ProfiniteInteger
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] (D : ClassFieldData G A)
variable {K L : OpenSubgroup G}
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (hLK : L ≤ K) (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1) {x : A}
    (hx : x ∈ augmentation A (K : Subgroup G) (L : Subgroup G)) :
    ∃ b ∈ fixedModule A (L : Subgroup G), x = (φ : G) • b / b := by
  have := normal_of_unramified (d := D.deg) hLK hu

  let S : Subgroup A :=
    { carrier := {y | ∃ b ∈ fixedModule A (L : Subgroup G), y = (φ : G) • b / b}
      one_mem' := ⟨1, Subgroup.one_mem _, by rw [smul_one, div_one]⟩
      mul_mem' := by
        rintro _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩
        exact ⟨b * c, Subgroup.mul_mem _ hb hc, by rw [smul_mul', mul_div_mul_comm]⟩
      inv_mem' := by
        rintro _ ⟨b, hb, rfl⟩
        exact ⟨b⁻¹, Subgroup.inv_mem _ hb, by rw [smul_inv', inv_div_inv, inv_div]⟩ }

  let T : Subgroup (K : Subgroup G) :=
    { carrier := {g | ∀ a ∈ fixedModule A (L : Subgroup G), (g : G) • a / a ∈ S}
      one_mem' := fun a _ => by
        rw [OneMemClass.coe_one, one_smul, div_self']
        exact S.one_mem
      mul_mem' := by
        intro g h hg hh a ha
        have hha : (h : G) • a ∈ fixedModule A (L : Subgroup G) :=
          smul_mem_fixedModule_of_normal (L := (L : Subgroup G)) hLK h.2 ha
        have e : ((g * h : (K : Subgroup G)) : G) • a / a =
            ((g : G) • ((h : G) • a) / ((h : G) • a)) * ((h : G) • a / a) := by
          rw [Subgroup.coe_mul, mul_smul]
          simp only [div_eq_mul_inv, mul_assoc, inv_mul_cancel_left]
        rw [e]
        exact S.mul_mem (hg _ hha) (hh a ha)
      inv_mem' := by
        intro g hg a ha
        have hga : ((g⁻¹ : (K : Subgroup G)) : G) • a ∈ fixedModule A (L : Subgroup G) :=
          smul_mem_fixedModule_of_normal (L := (L : Subgroup G)) hLK (g⁻¹).2 ha
        have e : ((g⁻¹ : (K : Subgroup G)) : G) • a / a =
            ((g : G) • (((g⁻¹ : (K : Subgroup G)) : G) • a) / (((g⁻¹ : (K : Subgroup G)) : G) • a))⁻¹ := by
          rw [smul_smul, InvMemClass.coe_inv, mul_inv_cancel, one_smul, inv_div]
        rw [e]
        exact S.inv_mem (hg _ hga) }
  have hφT : φ ∈ T := fun a ha => ⟨a, ha, rfl⟩
  have hLT : ∀ ρ : (K : Subgroup G), (ρ : G) ∈ (L : Subgroup G) → ρ ∈ T := fun ρ hρ a ha => by
    rw [ha ρ hρ, div_self']
    exact S.one_mem
  have hTop : ∀ g : (K : Subgroup G), g ∈ T := by
    intro g
    obtain ⟨m, hm⟩ := D.exists_pow_mul_mem_of_unramified hLK hu hφ g
    have hg : g = φ ^ m * ((φ ^ m)⁻¹ * g) := by group
    rw [hg]
    exact T.mul_mem (T.pow_mem hφT m) (hLT _ (by simpa using hm))
  have hle : augmentation A (K : Subgroup G) (L : Subgroup G) ≤ S := by
    rw [augmentation, Subgroup.closure_le]
    rintro _ ⟨g, hg, a, ha, rfl⟩
    exact hTop ⟨g, hg⟩ a ha
  exact hle hx
end GroundTheory.LocalField.Abstract.ClassFieldData
