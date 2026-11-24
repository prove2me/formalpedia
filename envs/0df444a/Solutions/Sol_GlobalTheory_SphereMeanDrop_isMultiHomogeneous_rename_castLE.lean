-- Prove2me | solution 1 for GlobalTheory.SphereMeanDrop.isMultiHomogeneous_rename_castLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:53:40.341529+00:00
-- url     : https://prove2.me/submissions/161b84ef-f390-480e-a44e-d82cb3bd0ae2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPolarGaussianProbabilityComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianRadialLawProbabilityLogIntegrableMeanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianFirstCoordsMeasurePreservingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BlockSphereProbZeroSetEqZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsMultiHomogeneousRenameCastLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SphereMeanDrop
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights
namespace GlobalTheory.SphereMeanDrop
theorem _root_.solution {B N n : ℕ} (h : N ≤ n) (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin N) ℂ) (hm : IsMultiHomogeneous a f) :
    IsMultiHomogeneous a (rename (fun p : Fin B × Fin N => (p.1, Fin.castLE h p.2)) f) := by
  have he : Function.Injective (fun p : Fin B × Fin N => (p.1, Fin.castLE h p.2)) := by
    intro p q hpq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext hpq.1 (Fin.castLE_injective h hpq.2)
  intro s hs b
  rw [support_rename_of_injective he, Finset.mem_image] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  rw [← hm t ht b]
  let emb : Fin N ↪ Fin n := ⟨Fin.castLE h, Fin.castLE_injective h⟩
  have hsub : (Finset.univ.map emb) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_subset hsub ?_]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Finsupp.mapDomain_apply he t (b, j)
  · intro j _ hj
    apply Finsupp.mapDomain_notin_range
    rintro ⟨q, hq⟩
    apply hj
    simp only [Prod.mk.injEq] at hq
    rw [Finset.mem_map]
    exact ⟨q.2, Finset.mem_univ _, hq.2⟩
end GlobalTheory.SphereMeanDrop
