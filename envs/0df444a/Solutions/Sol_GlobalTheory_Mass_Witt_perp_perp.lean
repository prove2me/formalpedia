-- Prove2me | solution 1 for GlobalTheory.Mass.Witt.perp_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:01:47.502226+00:00
-- url     : https://prove2.me/submissions/befcc56d-605d-4a84-ae42-da155d51c75b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitian
import Theorems.Thm_GlobalTheory_Mass_Witt_mem_perp
import Theorems.Thm_GlobalTheory_Mass_Witt_isCompl_perp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Witt
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.Mass.Witt
theorem _root_.solution [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (ha : ∀ x, h x x = 0 → x = 0) (U : Submodule K V) : perp h (perp h U) = U := by
  have hle : U ≤ perp h (perp h U) := by
    intro u hu
    rw [mem_perp]
    intro w hw
    have h0 : h u w = 0 := (mem_perp h U w).1 hw u hu
    rw [← hs.eq u w, h0, map_zero]
  have c1 := Submodule.finrank_add_eq_of_isCompl (isCompl_perp h ha U)
  have c2 := Submodule.finrank_add_eq_of_isCompl (isCompl_perp h ha (perp h U))
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
end GlobalTheory.Mass.Witt
