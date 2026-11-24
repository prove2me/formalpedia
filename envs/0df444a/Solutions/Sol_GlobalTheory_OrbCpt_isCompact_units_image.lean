-- Prove2me | solution 1 for GlobalTheory.OrbCpt.isCompact_units_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:17:27.328807+00:00
-- url     : https://prove2.me/submissions/68197b2a-8509-4cc4-b0f6-bdd8cf7492a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactPreimageNormCentralizerHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjugatesSeparableMatrixCompactModCentralizer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology Polynomial
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.OrbCpt
variable {k : Type} [NontriviallyNormedField k] {r : ℕ}
namespace GlobalTheory.OrbCpt
theorem _root_.solution {X : Type} [TopologicalSpace X] {P : Set X} (hP : IsCompact P)
    {f : X → Matrix (Fin r) (Fin r) k} (hf : Continuous f) (hdet : ∀ x ∈ P, (f x).det ≠ 0) :
    ∃ C : Set (GL (Fin r) k), IsCompact C ∧
      ∀ x ∈ P, ∃ c ∈ C, (c : Matrix (Fin r) (Fin r) k) = f x := by
  classical
  haveI : CompactSpace P := isCompact_iff_compactSpace.mp hP
  let φ : P → GL (Fin r) k := fun x =>
    ⟨f x, (f x)⁻¹, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdet x x.2)),
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet x x.2))⟩
  have hφ : Continuous φ := by
    rw [Units.continuous_iff]
    refine ⟨hf.comp continuous_subtype_val, ?_⟩
    show Continuous fun x : P => (f x)⁻¹
    have : (fun x : P => (f x)⁻¹) = fun x : P => ((f x).det)⁻¹ • (f x).adjugate := by
      funext x; rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [this]
    exact ((hf.comp continuous_subtype_val).matrix_det.inv₀ fun x => hdet x.1 x.2).smul
      (hf.comp continuous_subtype_val).matrix_adjugate
  exact ⟨Set.range φ, isCompact_range hφ, fun x hx => ⟨φ ⟨x, hx⟩, ⟨_, rfl⟩, rfl⟩⟩
end GlobalTheory.OrbCpt
