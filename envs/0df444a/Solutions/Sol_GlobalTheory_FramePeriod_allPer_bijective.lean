-- Prove2me | solution 1 for GlobalTheory.FramePeriod.allPer_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:53.481353+00:00
-- url     : https://prove2.me/submissions/78d73005-68b6-4258-b3e2-f72b8a4271b3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Theorems.Thm_GlobalTheory_FramePeriod_allPer_apply
import Theorems.Thm_GlobalTheory_FramePeriod_allPer_symm
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply



set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FramePeriod
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.FramePeriod
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ)
    (x : FD.Frame Ψ r) {g : ℕ} (idx : Fin g ≃ Ψ × Fin r)
    (h : ∀ τ : Ψ, Function.Bijective (locPer τ.1 Gm q (FD.mat x τ))) :
    Function.Bijective (allPer Gm q x idx) := by
  constructor
  · intro y y' hy
    funext τ
    apply (h τ).1
    rw [← allPer_symm Gm q x idx, ← allPer_symm Gm q x idx, hy]
  · intro z
    choose y hy using fun τ : Ψ => (h τ).2 (fun a => z (idx.symm (τ, a)))
    refine ⟨y, funext fun k => ?_⟩
    rw [allPer_apply, hy]; simp
end GlobalTheory.FramePeriod
