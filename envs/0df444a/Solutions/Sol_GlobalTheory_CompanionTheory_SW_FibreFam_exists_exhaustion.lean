-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreFam.exists_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:50.309602+00:00
-- url     : https://prove2.me/submissions/6c8bc353-035e-41ad-ba4d-4bc7f65adbec

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreFam
variable {V : Type} [TopologicalSpace V]
namespace GlobalTheory.CompanionTheory.SW.FibreFam
theorem _root_.solution [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    {U : Set V} (hU : IsOpen U) :
    ∃ K W : ℕ → Set V, (∀ n, IsCompact (K n)) ∧ (∀ n, IsOpen (W n)) ∧ (∀ n, W n ⊆ K n) ∧
      (∀ n, K n ⊆ U) ∧ Monotone K ∧ Monotone W ∧ (⋃ n, K n) = U ∧ (⋃ n, W n) = U := by
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  let E := CompactExhaustion.choice U
  have hint : ⋃ n, interior (E n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ n, E n := by
      rw [E.iUnion_eq]
      exact Set.mem_univ x
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨n + 1, E.subset_interior_succ n hn⟩
  refine ⟨fun n => (↑) '' E n, fun n => (↑) '' interior (E n),
    fun n => (E.isCompact n).image continuous_subtype_val,
    fun n => hU.isOpenMap_subtype_val _ isOpen_interior, fun n => Set.image_mono interior_subset,
    fun n => by
      rintro _ ⟨x, -, rfl⟩
      exact x.2,
    fun m n hmn => Set.image_mono (E.subset hmn),
    fun m n hmn => Set.image_mono (interior_mono (E.subset hmn)), ?_, ?_⟩
  · rw [← Set.image_iUnion, E.iUnion_eq, Set.image_univ, Subtype.range_coe]
  · rw [← Set.image_iUnion, hint, Set.image_univ, Subtype.range_coe]
end GlobalTheory.CompanionTheory.SW.FibreFam
