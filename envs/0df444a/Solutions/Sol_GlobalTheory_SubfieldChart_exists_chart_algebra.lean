-- Prove2me | solution 1 for GlobalTheory.SubfieldChart.exists_chart_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:23:59.400781+00:00
-- url     : https://prove2.me/submissions/df9fd312-c264-43d9-825a-5cb816560d0f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTestFunctionsSubsetOfMemNhds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolomorphicChart
import Theorems.Thm_GlobalTheory_SubfieldChart_exists_finite_test
import Theorems.Thm_GlobalTheory_SubfieldChart_resPt_extPt
import Theorems.Thm_GlobalTheory_SubfieldChart_extPt_resPt
import Theorems.Thm_GlobalTheory_SubfieldChart_exists_continuous_extPt
import Theorems.Thm_GlobalTheory_HolChart_exists_etale_coords_vanishing
import Theorems.Thm_GlobalTheory_exists_holomorphic_section_of_etale


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
open GlobalTheory GlobalTheory.SubfieldChart
variable {k A : Type} [Field k] [Algebra k ℂ] [CommRing A] [Algebra k A]
namespace GlobalTheory.SubfieldChart
theorem _root_.solution (d : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension d k A]
    (e : A →ₐ[k] ℂ) :
    ∃ (W : Set (Fin d → ℂ)) (p : (Fin d → ℂ) → (A →ₐ[k] ℂ)) (n : ℕ) (r : Fin n → A) (ε : ℝ),
      IsOpen W ∧ 0 ∈ W ∧ p 0 = e ∧ 0 < ε ∧ (∀ a, DifferentiableOn ℂ (fun w => p w a) W) ∧
      Set.InjOn p W ∧ ∀ x : A →ₐ[k] ℂ, (∀ i, ‖x (r i) - e (r i)‖ < ε) → ∃ w ∈ W, x = p w := by
  have hc : (algebraMap ℂ (ℂ ⊗[k] A)).IsStandardSmoothOfRelativeDimension d :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).2 inferInstance
  obtain ⟨φ, hφc, hφ, hφ0⟩ := HolChart.exists_etale_coords_vanishing _ hc (extPt e).toRingHom
    (fun a => (extPt e).commutes a)
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (ℂ ⊗[k] A) := φ.toAlgebra
  have _ : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) (ℂ ⊗[k] A) :=
    IsScalarTower.of_algebraMap_eq' hφc.symm
  have _ : Algebra.Etale (MvPolynomial (Fin d) ℂ) (ℂ ⊗[k] A) := hφ
  obtain ⟨W, σ, n, f, ε, hW, hW0, hσ0, hε, hσd, hσt, hσs⟩ :=
    exists_holomorphic_section_of_etale d (ℂ ⊗[k] A) (extPt e) hφ0
  choose F hF hF' using fun j => exists_continuous_extPt (f j)
  have hN : {u : A → ℂ | ∀ j, ‖F j u - extPt e (f j)‖ < ε} ∈ nhds (e : A → ℂ) := by
    refine IsOpen.mem_nhds ?_ fun j => ?_
    · rw [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun j =>
        isOpen_lt (((hF j).sub continuous_const).norm) continuous_const
    · rw [hF', sub_self, norm_zero]; exact hε
  obtain ⟨m, r, δ, hδ, hr⟩ := exists_finite_test hN
  refine ⟨W, fun w => resPt (σ w), m, r, δ, hW, hW0, ?_, hδ, fun a => hσd (1 ⊗ₜ a), ?_, ?_⟩
  · show resPt (σ 0) = e
    rw [hσ0, resPt_extPt]
  · intro w hw w' hw' h
    have h1 : σ w = σ w' := by
      rw [← extPt_resPt (σ w), ← extPt_resPt (σ w')]
      exact congrArg extPt h
    funext i
    rw [← hσt w hw i, h1, hσt w' hw' i]
  · intro x hx
    obtain ⟨w, hw, h⟩ := hσs (extPt x) fun j => by
      rw [← hF']; exact hr x hx j
    exact ⟨w, hw, (resPt_extPt x).symm.trans (congrArg resPt h)⟩
end GlobalTheory.SubfieldChart
