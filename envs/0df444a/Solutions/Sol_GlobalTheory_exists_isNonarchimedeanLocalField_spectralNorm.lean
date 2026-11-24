-- Prove2me | solution 1 for GlobalTheory.exists_isNonarchimedeanLocalField_spectralNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:42:34.635144+00:00
-- url     : https://prove2.me/submissions/0fe0224d-7a65-4395-a70f-ba76a2e6eb14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsNonarchimedeanLocalFieldSpectralNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
      [LocallyCompactSpace F] (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K],
      ∃ (_ : ValuativeRel K) (_ : TopologicalSpace K), IsNonarchimedeanLocalField K ∧
        ∀ x y : K, x ≤ᵥ y ↔ spectralNorm F K x ≤ spectralNorm F K y := by
  intro F _ _ _ _ K _ _ _
  letI nK : NontriviallyNormedField K := spectralNorm.nontriviallyNormedField F K
  haveI : IsUltrametricDist K := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := F) (L := K))
  letI rel : ValuativeRel K := ValuativeRel.ofValuation (NormedField.valuation (K := K))
  refine ⟨rel, inferInstance, ?_, fun x y => Iff.rfl⟩
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have hc : (NormedField.valuation (K := K)).Compatible := Valuation.Compatible.ofValuation _
  refine { toIsValuativeTopology := ?_, toLocallyCompactSpace := ?_, toIsNontrivial := ?_ }
  · exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := K))
      (fun {s} => (NormedField.toValued (K := K)).is_topological_valuation s)
  · letI : NormedSpace F K := spectralNorm.normedSpace F K
    haveI : ProperSpace K := FiniteDimensional.proper F K
    infer_instance
  · rw [isNontrivial_iff_isNontrivial (NormedField.valuation (K := K))]
    infer_instance
end GlobalTheory
