-- Prove2me | solution 1 for MasulloGRH.nuclear_permanence
-- status  : ACCEPTED   (prove)
-- author  : @ijawdoij123
-- created : 2026-11-20T22:40:47.984285+00:00
-- url     : https://prove2.me/submissions/07da515d-99a0-4594-8de3-9b8141d59dd3

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_nuclear_subspace
import Theorems.Thm_MasulloGRH_nuclear_quotient
import Theorems.Thm_MasulloGRH_nuclear_pi
import Theorems.Thm_MasulloGRH_nuclear_projTensor

set_option autoImplicit false

open MasulloGRH
open TensorProduct Topology

universe u

theorem solution :
    (∀ (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E], IsNuclear E →
      (∀ V : Submodule ℂ E, IsNuclear V) ∧
      (∀ V : Submodule ℂ E, IsClosed (V : Set E) → IsNuclear (E ⧸ V))) ∧
    (∀ (ι : Type u) (E : ι → Type u) [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
      [∀ i, TopologicalSpace (E i)], (∀ i, IsNuclear (E i)) → IsNuclear (∀ i, E i)) ∧
    (∀ (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
      [AddCommGroup F] [Module ℂ F] [TopologicalSpace F], IsNuclear E → IsNuclear F →
      @IsNuclear (E ⊗[ℂ] F) _ _ (projTensorTopology E F)) :=
  ⟨fun E _ _ _ hE => ⟨fun V => nuclear_subspace E hE V, fun V hV => nuclear_quotient E hE V hV⟩,
    fun ι E _ _ _ hE => nuclear_pi ι E hE,
    fun E F _ _ _ _ _ _ hE hF => nuclear_projTensor E F hE hF⟩
