-- Prove2me | solution 1 for MasulloGRH.isLF_of_isFrechet
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T11:55:55.826389+00:00
-- url     : https://prove2.me/submissions/2a21ebad-e98c-4456-9334-e36d5c0d4a82

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex

open Topology

set_option autoImplicit false

open MasulloGRH

namespace Sol_MasulloGRH_isLF_of_isFrechet

/-- The image under the inclusion `⊤ → E` of a Cauchy filter is a Cauchy filter. -/
private theorem isCauchyFilter_map_val {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] {f : Filter (⊤ : Submodule ℂ E)} (hf : IsCauchyFilter f) :
    IsCauchyFilter (f.map (Subtype.val : (⊤ : Submodule ℂ E) → E)) := by
  obtain ⟨hne, hc⟩ := hf
  refine ⟨Filter.map_neBot, fun U hU => ?_⟩
  have hU' : (Subtype.val : (⊤ : Submodule ℂ E) → E) ⁻¹' U ∈ 𝓝 (0 : (⊤ : Submodule ℂ E)) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨A, hA, hAU⟩ := hc _ hU'
  refine ⟨Subtype.val '' A, Filter.image_mem_map hA, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact hAU a ha b hb

/-- The whole space, viewed as the submodule `⊤` with the induced topology, is a Fréchet space
as soon as `E` is. -/
theorem isFrechet_top {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsFrechet E) : IsFrechet (⊤ : Submodule ℂ E) := by
  obtain ⟨⟨ι, hι, p, hp⟩, ⟨hT2, hcomplete⟩, hmet⟩ := hE
  have hind : IsInducing ((⊤ : Submodule ℂ E).subtype) := IsInducing.subtypeVal
  refine ⟨⟨ι, hι, p.comp (⊤ : Submodule ℂ E).subtype, hind.withSeminorms hp⟩,
    ⟨inferInstance, fun f hf => ?_⟩, IsEmbedding.subtypeVal.metrizableSpace⟩
  obtain ⟨x, hx⟩ := hcomplete _ (isCauchyFilter_map_val hf)
  refine ⟨⟨x, Submodule.mem_top⟩, ?_⟩
  rw [nhds_subtype]
  exact Filter.map_le_iff_le_comap.mp hx

/-- A topology `t` on `E` for which the inclusion of `⊤` (with the topology induced from `τE`)
is continuous is coarser than `τE`: the identity of `E` factors as `E → ⊤ → E`. -/
theorem le_of_continuous_val {E : Type*} [AddCommGroup E] [Module ℂ E]
    (τE t : TopologicalSpace E)
    (ht : @Continuous (⊤ : Submodule ℂ E) E (@instTopologicalSpaceSubtype E _ τE) t
      Subtype.val) : τE ≤ t := by
  have hmk : @Continuous E (⊤ : Submodule ℂ E) τE (@instTopologicalSpaceSubtype E _ τE)
      (fun x : E => (⟨x, Submodule.mem_top⟩ : (⊤ : Submodule ℂ E))) :=
    @Continuous.subtype_mk E E τE τE _ _ (@continuous_id E τE) _
  have hcomp : @Continuous E E τE t
      ((Subtype.val : (⊤ : Submodule ℂ E) → E) ∘
        fun x : E => (⟨x, Submodule.mem_top⟩ : (⊤ : Submodule ℂ E))) :=
    @Continuous.comp E (⊤ : Submodule ℂ E) E τE (@instTopologicalSpaceSubtype E _ τE) t
      _ _ ht hmk
  exact (@continuous_id_iff_le E τE t).mp hcomp

end Sol_MasulloGRH_isLF_of_isFrechet

open Sol_MasulloGRH_isLF_of_isFrechet in
theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsFrechet E) : IsLF E := by
  have hT2 : T2Space E := hE.2.1.1
  refine ⟨⟨hE.1, hT2⟩, fun _ => ⊤, fun _ => instTopologicalSpaceSubtype,
    fun x => ⟨0, Submodule.mem_top⟩, fun _ => isFrechet_top hE, fun _ => ⟨le_rfl, ?_⟩, ?_⟩
  · exact continuous_subtype_val.subtype_mk _
  · refine le_antisymm (le_sInf ?_) (sInf_le ⟨hE.1, fun _ => continuous_subtype_val⟩)
    intro t ht
    exact le_of_continuous_val _ t (ht.2 0)
