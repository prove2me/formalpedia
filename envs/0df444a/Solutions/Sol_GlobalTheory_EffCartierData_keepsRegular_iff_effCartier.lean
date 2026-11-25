-- Prove2me | solution 1 for GlobalTheory.EffCartierData.keepsRegular_iff_effCartier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:54.173468+00:00
-- url     : https://prove2.me/submissions/cc14b36f-6f85-4282-b9c7-b41e7ecf43f1

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_EffCartierData_ideal_comap_idealSheaf
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_of_dvd
import Theorems.Thm_GlobalTheory_Cartier_isRegularFn_iff_of_isAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_isRegularFn_of_locally


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open Cartier
open GlobalTheory.EffCartierData
variable {X Y Z : Scheme.{0}}
variable (D D' : EffCartierData X)
namespace GlobalTheory.EffCartierData
theorem _root_.solution (φ : Y ⟶ X) :
    D.KeepsRegular φ ↔ FinalTheorems.EffCartier (D.idealSheaf.comap φ) := by
  constructor
  · intro h y
    obtain ⟨i, hi⟩ := D.exists_mem (φ y)
    obtain ⟨W, hyW, hW⟩ := exists_affine_le (V := φ ⁻¹ᵁ D.U i) (x := y) hi
    exact ⟨W, _, hyW, h i _ hW, D.ideal_comap_idealSheaf φ W i hW⟩
  · intro h i
    refine isRegularFn_of_locally fun y hy => ?_
    obtain ⟨W, g, hyW, hg, hI⟩ := h y
    obtain ⟨W', hyW', hW'⟩ := exists_affine_le (V := W.1 ⊓ φ ⁻¹ᵁ D.U i) (x := y) ⟨hyW, hy⟩
    have h₁ : W'.1 ≤ W.1 := hW'.trans inf_le_left
    refine ⟨W'.1, hW'.trans inf_le_right, hyW', ?_⟩
    refine (((isRegularFn_iff_of_isAffineOpen W.2).2 hg).resG h₁).of_dvd ?_
    rw [← Ideal.mem_span_singleton, ← D.ideal_comap_idealSheaf φ W' i]
    exact (D.idealSheaf.comap φ).ideal_le_comap_ideal (U := W') (V := W) h₁
      (by rw [hI]; exact Ideal.mem_span_singleton_self _)
end GlobalTheory.EffCartierData
