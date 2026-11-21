-- Prove2me | solution 1 for JardenShami.mk_binTree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:26.453837+00:00
-- url     : https://prove2.me/submissions/8e94f9d8-1e86-4c05-ae55-6bcc0fe5d844

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_Kappa_mk_coe
attribute [local simp] JardenShami.Kappa.coe_mk
attribute [local simp] JardenShami.Kappa.mk_coe



set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {ν : Cardinal.{w}}
namespace JardenShami
theorem _root_.solution :
    #(binTree ν) ≤ Cardinal.sum fun β : Kappa ν => (2 : Cardinal.{w}) ^ #(Set.Iio β) := by
  classical
  have hU : binTree ν = ⋃ β : Kappa ν, Set.range fun f : Kappa ν → Fin 2 => binRestr f β := by
    ext g
    simp only [binTree, Set.mem_iUnion, Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨f, β, rfl⟩
      exact ⟨β, f, rfl⟩
    · rintro ⟨β, f, rfl⟩
      exact ⟨f, β, rfl⟩
  rw [hU]
  refine (Cardinal.mk_iUnion_le_sum_mk).trans (Cardinal.sum_le_sum _ _ fun β => ?_)
  -- `f ↾ β` depends only on `f` on `{α : α < β}`
  let R : (Set.Iio β → Fin 2) → Set (Kappa ν × Fin 2) := fun h =>
    {p | ∃ hp : p.1 < β, p.2 = h ⟨p.1, hp⟩}
  have hsub : (Set.range fun f : Kappa ν → Fin 2 => binRestr f β) ⊆ Set.range R := by
    rintro _ ⟨f, rfl⟩
    refine ⟨fun a => f a, ?_⟩
    ext ⟨α, d⟩
    simp only [R, binRestr, Set.mem_ofPred_eq]
    exact ⟨fun ⟨h, e⟩ => ⟨h, e⟩, fun ⟨h, e⟩ => ⟨h, e⟩⟩
  calc #(Set.range fun f : Kappa ν → Fin 2 => binRestr f β) ≤ #(Set.range R) :=
        Cardinal.mk_le_mk_of_subset hsub
    _ ≤ #(Set.Iio β → Fin 2) := Cardinal.mk_range_le
    _ = 2 ^ #(Set.Iio β) := by simp
end JardenShami
