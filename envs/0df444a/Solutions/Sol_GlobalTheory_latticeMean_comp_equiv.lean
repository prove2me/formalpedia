-- Prove2me | solution 1 for GlobalTheory.latticeMean_comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:04:22.631136+00:00
-- url     : https://prove2.me/submissions/5e47b416-0717-4c85-9ca2-8ccb8b639934

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsAddFundamentalDomainLatticeDomain
import Theorems.Thm_GlobalTheory_existsUnique_add_mem_latticeDomain
import Theorems.Thm_GlobalTheory_measurableSet_latticeDomain
import Theorems.Thm_GlobalTheory_latticeMean_eq_latticeDomain
import Theorems.Thm_GlobalTheory_latticeMean_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Submodule Set
open GlobalTheory
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
namespace GlobalTheory
theorem _root_.solution {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] (L' : Submodule ℤ E') [DiscreteTopology L'] [IsZLattice ℝ L']
    (e : E ≃L[ℝ] E') (he : ∀ x, e x ∈ L' ↔ x ∈ L) {f : E' → G}
    (hf : ∀ a ∈ L', ∀ x, f (x + a) = f x) :
    latticeMean L (fun x => f (e x)) = latticeMean L' f := by
  borelize E E'
  set μ : Measure E := Measure.addHaar
  have hmp : MeasurePreserving e μ (μ.map e) := ⟨e.continuous.measurable, rfl⟩
  have hD : IsAddFundamentalDomain L (e ⁻¹' latticeDomain L') μ := by
    refine IsAddFundamentalDomain.mk'
      (e.continuous.measurable (measurableSet_latticeDomain L')).nullMeasurableSet fun x => ?_
    obtain ⟨a, ha, hu⟩ := existsUnique_add_mem_latticeDomain L' (e x)
    refine ⟨⟨e.symm a, (he _).1 (by simp)⟩, ?_, ?_⟩
    · simpa [Submodule.vadd_def, add_comm] using ha
    · rintro ⟨b, hb⟩ hb'
      have := hu ⟨e b, (he _).2 hb⟩ (by simpa [Submodule.vadd_def, add_comm] using hb')
      apply Subtype.ext
      simp [← this]
  rw [latticeMean_eq L μ hD (f := fun x => f (e x))
    (fun a ha x => by simpa using hf (e a) ((he _).2 ha) (e x)),
    latticeMean_eq_latticeDomain L' (μ.map e),
    ZLattice.covolume_eq_measure_fundamentalDomain L μ hD,
    ZLattice.covolume_eq_measure_fundamentalDomain L' (μ.map e)
      (isAddFundamentalDomain_latticeDomain L' _),
    ← hmp.measureReal_preimage (measurableSet_latticeDomain L').nullMeasurableSet]
  congr 1
  exact hmp.setIntegral_preimage_emb e.toHomeomorph.measurableEmbedding f _
end GlobalTheory
