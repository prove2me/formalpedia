-- Prove2me | solution 1 for GlobalTheory.SectionsDescent.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:54:34.566801+00:00
-- url     : https://prove2.me/submissions/303170ee-6def-4f30-ae81-cf573a68a16b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsExtensionAffine
import Theorems.Thm_GlobalTheory_SectionsDescent_rs_rs
import Theorems.Thm_GlobalTheory_SectionsDescent_rs_self
import Theorems.Thm_GlobalTheory_SectionsDescent_rs_constHom
import Theorems.Thm_GlobalTheory_SectionsDescent_exists_sum_sec

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
noncomputable section
open GlobalTheory GlobalTheory.SectionsDescent
open GlobalTheory.FieldBaseChange
namespace GlobalTheory.SectionsDescent
theorem _root_.solution : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀) [QuasiCompact p₀] [QuasiSeparated p₀] (M : LB X₀), M.IsLB → IsPullback φ p p₀ (spMap i) → ∀ t : (M.pull φ).Sec, ∃ (n : ℕ) (c : Fin n → K) (s : Fin n → M.Sec), ∀ j : PUnit → M.ι, ∀ h : (M.pull φ).U j ≤ φ ⁻¹ᵁ M.U (j PUnit.unit), t.f j = ∑ a, constFn p _ (c a) * (φ.appLE _ _ h).hom ((s a).f (j PUnit.unit)) := by
  intro K₀ K _ _ i X₀ X p₀ p φ _ _ M hM H t
  let := i.toAlgebra
  have : CompactSpace X₀ := QuasiCompact.compactSpace_of_compactSpace p₀
  obtain ⟨J, S, c, s, e⟩ := exists_sum_sec (K := K₀) (F := K) H hM t
  refine ⟨S.card, fun a => c (S.equivFin.symm a), fun a => s (S.equivFin.symm a), fun j h => ?_⟩
  have e₁ : t.f j = rs h (loc t (j PUnit.unit)) := ((rs_rs _ _ _).trans (rs_self _ _)).symm
  rw [e₁, e, map_sum, ← Finset.sum_coe_sort, ← S.equivFin.symm.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, rs_constHom]
  rfl
end GlobalTheory.SectionsDescent
