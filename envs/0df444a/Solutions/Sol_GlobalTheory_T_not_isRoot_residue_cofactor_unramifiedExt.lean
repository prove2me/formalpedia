-- Prove2me | solution 1 for GlobalTheory.T.not_isRoot_residue_cofactor_unramifiedExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:42:31.301965+00:00
-- url     : https://prove2.me/submissions/79580e27-e693-4d03-a415-837eb7d4f87e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotIsRootResidueCofactorUnramifiedExt
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotIsRootResidueCofactorUnramifiedExtStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_ResMult_not_isRoot_cofactor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ s : K'.O, (∀ y : K'.O, ∃ f : K.O[X], ∃ z ∈ IsLocalRing.maximalIdeal K'.O, algebraMap K'.O K'.E y = f.eval₂ (φ.comp (algebraMap K.O K.E)) (algebraMap K'.O K'.E s) + algebraMap K'.O K'.E z) → ∀ (p : K.O[X]) (r c : K'.O[X]), p.Monic → r.Monic → r.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ r.natDegree → p.natDegree = d * r.natDegree → p.map (φ.comp (algebraMap K.O K.E)) = (r * c).map (algebraMap K'.O K'.E) → ¬ (c.map (IsLocalRing.residue K'.O)).IsRoot (IsLocalRing.residue K'.O s) := by
  first | exact @GlobalTheory.UnitLemma.Unr.ResMult.not_isRoot_cofactor | exact GlobalTheory.UnitLemma.Unr.ResMult.not_isRoot_cofactor | (intros; apply GlobalTheory.UnitLemma.Unr.ResMult.not_isRoot_cofactor <;> assumption)
end _root_.GlobalTheory.T
