-- Prove2me | solution 1 for GlobalTheory.LieEigenbasis.existsUnique_sum_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:40:54.774794+00:00
-- url     : https://prove2.me/submissions/e278e2cf-6a28-40f2-b81e-75a97d13663a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPushEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSumSingle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LieEigenbasis
namespace GlobalTheory.LieEigenbasis
theorem _root_.solution {k : Type} [Field k] {n N : ℕ} (s : Fin N → Fin n)
    (hs : Function.Injective s) (c : Fin n → k) (hc : ∀ i, i ∉ Set.range s → c i = 0) :
    ∃! d : Fin N → k, c = ∑ j, d j • (Pi.single (s j) 1 : Fin n → k) := by
  have h : ∀ (d : Fin N → k) (j : Fin N),
      (∑ j, d j • (Pi.single (s j) 1 : Fin n → k)) (s j) = d j := fun d j => by
    simp [Finset.sum_apply, Pi.single_apply, hs.eq_iff]
  refine ⟨fun j => c (s j), funext fun i => ?_, fun d hd => funext fun j => by rw [hd, h]⟩
  by_cases hi : i ∈ Set.range s
  · obtain ⟨j, rfl⟩ := hi
    rw [h]
  · rw [hc i hi, Finset.sum_apply]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    have : i ≠ s j := fun e => hi ⟨j, e.symm⟩
    simp [this]
end GlobalTheory.LieEigenbasis
