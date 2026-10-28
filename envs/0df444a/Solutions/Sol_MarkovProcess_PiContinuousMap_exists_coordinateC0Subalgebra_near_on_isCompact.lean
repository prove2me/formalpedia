-- Prove2me | solution 1 for MarkovProcess.PiContinuousMap.exists_coordinateC0Subalgebra_near_on_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T18:25:18.931442+00:00
-- url     : https://prove2.me/submissions/768a8b5e-52a7-4726-a713-33dbc8b367cd

import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Definitions.Def_MarkovProcess_CoordinateProductAlgebras
import Theorems.Thm_MarkovProcess_PiContinuousMap_coordinateC0Subalgebra_separatesPoints
open Topology MarkovProcess.PiContinuousMap
open scoped ZeroAtInfty
variable {I α : Type*} [TopologicalSpace α]

theorem solution
    [T3Space α] [LocallyCompactSpace α]
    (f : C(I → α, ℝ)) {K : Set (I → α)} (hK : IsCompact K)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ g ∈ coordinateC0Subalgebra (I := I) (α := α),
      ∀ x ∈ K, ‖g x - f x‖ < epsilon := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let ι : C(K, I → α) := ⟨Subtype.val, continuous_subtype_val⟩
  let ρ := ContinuousMap.compRightAlgHom ℝ ℝ ι
  let B : Subalgebra ℝ C(K, ℝ) := (coordinateC0Subalgebra (I := I) (α := α)).map ρ
  have hsep : B.SeparatesPoints := by
    intro x y hxy
    obtain ⟨_, ⟨a, ha, rfl⟩, hne⟩ :=
      MarkovProcess.PiContinuousMap.coordinateC0Subalgebra_separatesPoints (I := I) (α := α)
        (fun h => hxy (Subtype.ext h))
    exact ⟨_, ⟨ρ a, ⟨a, ha, rfl⟩, rfl⟩, hne⟩
  obtain ⟨⟨g, hg⟩, hgf⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints B hsep
      (f.comp ι) epsilon hepsilon
  obtain ⟨a, ha, rfl⟩ := hg
  refine ⟨a, ha, fun x hx => ?_⟩
  have := ContinuousMap.norm_coe_le_norm (ρ a - f.comp ι) ⟨x, hx⟩
  exact lt_of_le_of_lt this hgf
