-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TfLoc.Iw.iwahori_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:41:37.733296+00:00
-- url     : https://prove2.me/submissions/d9fc4db6-df4f-4d9d-ab5b-247a01f1299a

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
theorem _root_.solution {g : GL (Fin m) F} (hg : g ∈ iwahori (m := m) F) : g⁻¹ ∈ iwahori (m := m) F := by
  refine ⟨inv_mem hg.1, fun i j hij => ?_⟩
  obtain ⟨h, rfl⟩ := hg.1
  let φ := Ideal.Quotient.mk (ltIdeal F)
  let M : Matrix (Fin m) (Fin m) (Valuation.integer (valuation F) ⧸ ltIdeal F) :=
    (h : Matrix (Fin m) (Fin m) _).map φ
  let N : Matrix (Fin m) (Fin m) (Valuation.integer (valuation F) ⧸ ltIdeal F) :=
    ((h⁻¹ : GL (Fin m) _) : Matrix (Fin m) (Fin m) _).map φ
  have hMN : M * N = 1 := by
    show Matrix.map _ φ * Matrix.map _ φ = 1
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hNM : N * M = 1 := by
    show Matrix.map _ φ * Matrix.map _ φ = 1
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero φ) (map_one φ)]
  letI : Invertible M := ⟨N, hNM, hMN⟩
  have htri : M.BlockTriangular id := by
    intro a b hab
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hg.2 a b hab)
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular htri
  have hN : M⁻¹ = N := Matrix.inv_eq_right_inv hMN
  rw [hN] at hinv
  have h0 : N i j = 0 := hinv (show id j < id i from hij)
  rw [← map_inv]
  exact Ideal.Quotient.eq_zero_iff_mem.1 h0
end GlobalTheory.CompanionTheory.TfLoc.Iw
