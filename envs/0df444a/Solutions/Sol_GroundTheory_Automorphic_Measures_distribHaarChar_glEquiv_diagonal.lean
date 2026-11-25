-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.distribHaarChar_glEquiv_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:55:27.206819+00:00
-- url     : https://prove2.me/submissions/f140c03f-73a1-4db1-a94e-d5c5ec5a8f98

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Theorems.Thm_GroundTheory_Automorphic_Measures_mem_box
import Theorems.Thm_GroundTheory_Automorphic_Measures_isOpen_box
import Theorems.Thm_GroundTheory_Automorphic_Measures_isCompact_box
import Theorems.Thm_GroundTheory_Automorphic_Measures_zero_mem_box
import Theorems.Thm_GroundTheory_Automorphic_Measures_glEquiv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {F} {ι : Type*} [Fintype ι]
variable [DecidableEq ι]
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution {D : ι → F} (h : (Matrix.diagonal D).det ≠ 0) :
    distribHaarChar (ι → F) (glEquiv (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h)) =
      distribHaarChar F (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h)) := by
  have hD : ∀ i, D i ≠ 0 := fun i => by
    rw [Matrix.det_diagonal] at h
    exact Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i)
  let u : ι → Fˣ := fun i => Units.mk0 (D i) (hD i)
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) =
      ∏ i, u i := by
    ext
    simp [u, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_diagonal]
  rw [hdet, map_prod]
  borelize F
  let ν : Measure F := Measure.addHaar
  let μ : Measure (ι → F) := Measure.pi fun _ => ν
  have himage : glEquiv (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) • box F ι =
      Set.univ.pi fun i => u i • (𝒪[F] : Set F) := by
    ext x
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      refine ⟨y i, mem_box.1 hy i, ?_⟩
      simp [LinearEquiv.smul_def, glEquiv_apply, u, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mulVec_diagonal]
    · intro hx
      choose y hy hyx using hx
      refine ⟨y, mem_box.2 hy, funext fun i => ?_⟩
      simpa [LinearEquiv.smul_def, glEquiv_apply, u, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mulVec_diagonal, Units.smul_def] using hyx i
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := box F ι)
    (isOpen_box.measure_ne_zero μ ⟨0, zero_mem_box⟩) isCompact_box.measure_lt_top.ne ?_
  rw [himage, box, Measure.pi_pi, Measure.pi_pi, ENNReal.ofNNReal_finsetProd,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (distribHaarChar_mul ν (u i) _).symm
end GroundTheory.Automorphic.Measures
