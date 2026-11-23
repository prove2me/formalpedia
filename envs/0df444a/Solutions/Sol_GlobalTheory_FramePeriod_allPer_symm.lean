-- Prove2me | solution 1 for GlobalTheory.FramePeriod.allPer_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:25.763687+00:00
-- url     : https://prove2.me/submissions/aba56ebe-741c-42c3-b6fe-bbb147e23984

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Theorems.Thm_GlobalTheory_FramePeriod_allPer_apply

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
open GlobalTheory GlobalTheory.FramePeriod
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.FramePeriod
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ) (x : FD.Frame Ψ r)
    {g : ℕ} (idx : Fin g ≃ Ψ × Fin r) (y : Ψ → Fin r → ℂ) (τ : Ψ) :
    (fun a => allPer Gm q x idx y (idx.symm (τ, a))) = locPer τ.1 Gm q (FD.mat x τ) (y τ) := by
  funext a
  rw [allPer_apply, idx.apply_symm_apply]
end GlobalTheory.FramePeriod
