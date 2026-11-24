-- Prove2me | solution 1 for GlobalTheory.GamFree.gram_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:08:50.040854+00:00
-- url     : https://prove2.me/submissions/ea9d7d75-a39c-4752-9ede-4f6db2f9e7e3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BoundedPowOfTriangularIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOfFinOrderOfBounded
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_gram_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_gram_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GamFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.GamFree
theorem _root_.solution (G γ : Matrix (Fin r) (Fin r) E)
    (hγ : ∀ x y, FD.herm G (γ *ᵥ x) (γ *ᵥ y) = FD.herm G x y) (τ : E →+* ℂ)
    (Y : Matrix (Fin r) (Fin r) ℂ) : FD.gram τ G (γ.map τ * Y) = FD.gram τ G Y := by
  have h : FD.gram τ G (γ.map τ) = G.map τ := by
    ext a b
    have := congrArg τ (hγ (Pi.single a 1) (Pi.single b 1))
    have h0 : FD.cc (0 : E) = 0 := by simp [FD.cc]
    have h1 : FD.cc (1 : E) = 1 := by simp [FD.cc]
    have e : FD.herm G (Pi.single a 1) (Pi.single b 1) = G a b := by
      simp [FD.herm, Pi.single_apply, apply_ite FD.cc, h0, h1]
    rw [e] at this
    rw [Matrix.map_apply, ← this]
    simp [FD.gram, FD.hermC, FD.herm, FD.col, FD.emb_cc]
  rw [FD.FrameDegreeData.gram_mul, h, FD.FrameDegreeData.gram_eq]
end GlobalTheory.GamFree
