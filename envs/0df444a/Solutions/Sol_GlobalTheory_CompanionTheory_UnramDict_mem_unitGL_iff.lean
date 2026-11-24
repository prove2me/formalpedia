-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnramDict.mem_unitGL_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:54:52.021496+00:00
-- url     : https://prove2.me/submissions/858ab6a1-8d2c-430d-98d6-be12b6b75e86

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Topology Filter
open PositivityTheory.Rg.Tf.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnramDict
namespace GlobalTheory.CompanionTheory.UnramDict
theorem _root_.solution {F : Type*} [Field F] [ValuativeRel F] {n : ℕ} (g : GL (Fin n) F) :
    g ∈ unitGL (n := Fin n) F ↔
      (∀ i j, (g : Matrix (Fin n) (Fin n) F) i j ∈ intO F) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ intO F := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => ((h : Matrix (Fin n) (Fin n) (intO F)) i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact (((h⁻¹ : GL (Fin n) (intO F)) : Matrix (Fin n) (Fin n) (intO F)) i j).2
  · rintro ⟨hA, hB⟩
    let f : intO F →+* F := (intO F).subtype
    let A : Matrix (Fin n) (Fin n) (intO F) := fun i j => ⟨_, hA i j⟩
    let B : Matrix (Fin n) (Fin n) (intO F) := fun i j => ⟨_, hB i j⟩
    have hinj : Function.Injective (f.mapMatrix (m := Fin n)) :=
      Matrix.map_injective Subtype.val_injective
    have hAf : f.mapMatrix A = (g : Matrix (Fin n) (Fin n) F) := by ext i j; rfl
    have hBf : f.mapMatrix B = ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      ext i j; rfl
    have hAB : A * B = 1 := hinj (by rw [map_mul, hAf, hBf, map_one]; exact Units.mul_inv g)
    have hBA : B * A = 1 := hinj (by rw [map_mul, hAf, hBf, map_one]; exact Units.inv_mul g)
    exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hAf⟩
end GlobalTheory.CompanionTheory.UnramDict
