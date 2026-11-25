-- Prove2me | solution 1 for GlobalTheory.Mass.Witt.isCompl_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:06:06.906535+00:00
-- url     : https://prove2.me/submissions/b8f19df7-a1aa-4c30-b237-e5cbd200d0e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitian
import Theorems.Thm_GlobalTheory_Mass_Witt_mem_perp

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
theorem _root_.solution [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (ha : ∀ x, h x x = 0 → x = 0) (U : Submodule K V) : IsCompl U (perp h U) := by
  have hdis : Disjoint U (perp h U) := by
    rw [Submodule.disjoint_def]
    intro x hxU hxP
    exact ha x (((mem_perp h U x).1 hxP) x hxU)
  let bU := Module.finBasis K U
  let T : V →ₗ[K] (Fin (Module.finrank K U) → K) := LinearMap.pi fun i => h (bU i : V)
  have hker : LinearMap.ker T ≤ perp h U := by
    intro v hv
    rw [mem_perp]
    intro x hx
    have hv' : ∀ i, h (bU i : V) v = 0 := fun i => by
      have := congrFun (LinearMap.mem_ker.mp hv) i
      simpa [T] using this
    have hx' : x = ∑ i, (bU.repr ⟨x, hx⟩ i) • (bU i : V) := by
      have e := congrArg Subtype.val (bU.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at e
      exact e.symm
    rw [hx', map_sum, LinearMap.sum_apply]
    simp [hv']
  have h1 := LinearMap.finrank_range_add_finrank_ker T
  have h2 : Module.finrank K (LinearMap.range T) ≤ Module.finrank K U := by
    simpa using Submodule.finrank_le (LinearMap.range T)
  have h3 := Submodule.finrank_mono hker
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq U (perp h U)
  rw [hdis.eq_bot, finrank_bot] at h4
  refine ⟨hdis, ?_⟩
  rw [codisjoint_iff]
  apply Submodule.eq_top_of_finrank_eq
  have h5 := Submodule.finrank_le (U ⊔ perp h U)
  omega
end GlobalTheory.Mass.Witt
