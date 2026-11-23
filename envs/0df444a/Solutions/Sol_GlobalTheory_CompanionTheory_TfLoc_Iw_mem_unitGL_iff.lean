-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TfLoc.Iw.mem_unitGL_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:13.93324+00:00
-- url     : https://prove2.me/submissions/2f1ceb60-8838-4613-ab1d-be43df416367

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel PositivityTheory.Rg.Tf.Loc Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TfLoc GlobalTheory.CompanionTheory.TfLoc.Iw
variable {F : Type*} [Field F] [ValuativeRel F] {m : ℕ}
namespace GlobalTheory.CompanionTheory.TfLoc.Iw
theorem _root_.solution (g : GL (Fin m) F) :
    g ∈ unitGL (n := Fin m) F ↔
      (∀ i j, valuation F ((g : Matrix (Fin m) (Fin m) F) i j) ≤ 1) ∧
      (∀ i j, valuation F (((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) i j) ≤ 1) := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => (h.val i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact ((h⁻¹).val i j).2
  · rintro ⟨h1, h2⟩
    let f := (Valuation.integer (valuation F)).subtype
    let A : Matrix (Fin m) (Fin m) (Valuation.integer (valuation F)) := fun i j => ⟨_, h1 i j⟩
    let B : Matrix (Fin m) (Fin m) (Valuation.integer (valuation F)) := fun i j => ⟨_, h2 i j⟩
    have hA : A.map f = (g : Matrix (Fin m) (Fin m) F) := by ext i j; rfl
    have hB : B.map f = ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := by ext i j; rfl
    have inj : Function.Injective (fun M : Matrix (Fin m) (Fin m) (Valuation.integer (valuation F)) => M.map f) :=
      Matrix.map_injective Subtype.val_injective
    have hAB : A * B = 1 := inj (by
      show (A * B).map f = (1 : Matrix (Fin m) (Fin m) _).map f
      rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero f) (map_one f)]
      exact Units.mul_inv g)
    have hBA : B * A = 1 := inj (by
      show (B * A).map f = (1 : Matrix (Fin m) (Fin m) _).map f
      rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero f) (map_one f)]
      exact Units.inv_mul g)
    exact ⟨⟨A, B, hAB, hBA⟩, Units.ext (by ext i j; rfl)⟩
end GlobalTheory.CompanionTheory.TfLoc.Iw
