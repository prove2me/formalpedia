-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HaarPK.exists_eq_smul_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:37:00.913563+00:00
-- url     : https://prove2.me/submissions/bb02a4f3-c7f7-4de5-92fe-fa4e11fe45c5

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds
import Theorems.Thm_GlobalTheory_CompanionTheory_HaarPK_exists_eq_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HaarPK
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
namespace GlobalTheory.CompanionTheory.HaarPK
theorem _root_.solution [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    (P : Subgroup G) (hP : IsClosed (P : Set G)) (μ ν : Measure G)
    (hμ1 : μ (P : Set G)ᶜ = 0) (hμ2 : ∀ p ∈ P, μ.map (fun x => p * x) = μ)
    (hμ3 : ∀ s : Set G, IsCompact s → μ s ≠ ⊤) (hμ4 : μ ≠ 0)
    (hν1 : ν (P : Set G)ᶜ = 0) (hν2 : ∀ p ∈ P, ν.map (fun x => p * x) = ν)
    (hν3 : ∀ s : Set G, IsCompact s → ν s ≠ ⊤) (hν4 : ν ≠ 0) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • ν := by
  have hemb : MeasurableEmbedding ((↑) : P → G) := MeasurableEmbedding.subtype_coe hP.measurableSet
  haveI : LocallyCompactSpace P := hP.locallyCompactSpace
  haveI : SecondCountableTopology P := inferInstanceAs (SecondCountableTopology (P : Set G))
  have key : ∀ μ : Measure G, μ (P : Set G)ᶜ = 0 → (∀ p ∈ P, μ.map (fun x => p * x) = μ) →
      (∀ s : Set G, IsCompact s → μ s ≠ ⊤) → μ ≠ 0 →
      ∃ μ' : Measure P, μ'.IsMulLeftInvariant ∧ IsFiniteMeasureOnCompacts μ' ∧ μ' ≠ 0 ∧
        μ = μ'.map (↑) := by
    intro μ h1 h2 h3 h4
    have hmap : μ = (μ.comap ((↑) : P → G)).map (↑) := by
      rw [hemb.map_comap, Subtype.range_coe_subtype]
      exact (Measure.restrict_eq_self_of_ae_mem h1).symm
    refine ⟨μ.comap (↑), ⟨fun p => ?_⟩, ⟨fun C hC => ?_⟩, fun h => h4 (by rw [hmap, h, Measure.map_zero]), hmap⟩
    · ext A hA
      rw [Measure.map_apply (measurable_const_mul p) hA, hemb.comap_apply, hemb.comap_apply]
      conv_rhs => rw [← h2 p p.2]
      rw [Measure.map_apply (measurable_const_mul _) (hemb.measurableSet_image.2 hA)]
      congr 1
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨p * y, hy, rfl⟩
      · rintro ⟨y, hy, hxy⟩
        refine ⟨p⁻¹ * y, by simpa using hy, ?_⟩
        simp only at hxy
        simp [hxy]
    · rw [hemb.comap_apply]
      exact (h3 _ (hC.image continuous_subtype_val)).lt_top
  obtain ⟨μ', a1, a2, a3, a4⟩ := key μ hμ1 hμ2 hμ3 hμ4
  obtain ⟨ν', b1, b2, b3, b4⟩ := key ν hν1 hν2 hν3 hν4
  obtain ⟨c, c0, ct, hc⟩ := exists_eq_smul μ' ν' a3 b3
  exact ⟨c, c0, ct, by rw [a4, b4, hc, Measure.map_smul]⟩
end GlobalTheory.CompanionTheory.HaarPK
