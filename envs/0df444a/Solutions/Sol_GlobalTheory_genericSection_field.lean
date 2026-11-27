-- Prove2me | solution 1 for GlobalTheory.genericSection_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:39:51.311791+00:00
-- url     : https://prove2.me/submissions/1e6f7117-3d4f-404b-8cc1-908e3747b98d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightIntegralEstimates
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GenericSectionInjectiveOfAxH
import Theorems.Thm_GlobalTheory_genericSection_reindex
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_fieldOfS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.AlgT
namespace GlobalTheory
theorem _root_.solution {k F : Type} [Field k] [CharZero k] [Field F] [Algebra k F] {D N : ℕ}
    (j₀ : Fin (N + 1)) (x : Fin N → F) (hfg : (⊤ : IntermediateField k F).FG)
    (htr : Algebra.trdeg k F = D)
    (hJ : ∃ J : Fin D → Fin N, LinearIndependent F fun a => KaehlerDifferential.D k F (x (J a))) :
    AlgebraicIndependent k (sImg (D := D) j₀ x) ∧
      FiniteDimensional (IntermediateField.adjoin k (Set.range (sImg (D := D) j₀ x))) (OmS F D N) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (Set.range (sImg (D := D) j₀ x)))
        (OmS F D N) := by
  obtain ⟨hind, hfin⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.fieldOfS k F D N x hfg htr hJ
  rw [genericSection_reindex j₀ x] at hind hfin
  rw [(Equiv.surjective _).range_comp] at hfin
  refine ⟨(algebraicIndependent_equiv _).1 hind, hfin, ?_⟩
  have : FiniteDimensional (IntermediateField.adjoin k (Set.range (sImg (D := D) j₀ x)))
    (OmS F D N) := hfin
  have : CharZero (IntermediateField.adjoin k (Set.range (sImg (D := D) j₀ x))) :=
    charZero_of_injective_algebraMap (algebraMap k _).injective
  infer_instance
end GlobalTheory
