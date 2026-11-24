-- Prove2me | solution 1 for GlobalTheory.FramePeriod.card_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:28:17.920833+00:00
-- url     : https://prove2.me/submissions/7f6bfaac-4513-42f1-84a8-963738534842

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
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
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.FramePeriod
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} {g : ℕ} (idx : Fin g ≃ Ψ × Fin r) (σ : Ψ) (p : Fin g → Prop)
    (s : Fin r → Prop) (h : ∀ k, p k ↔ (idx k).1 = σ ∧ s (idx k).2) :
    Nat.card {k // p k} = Nat.card {a // s a} := by
  refine Nat.card_congr
    { toFun := fun k => ⟨(idx k.1).2, ((h k.1).1 k.2).2⟩
      invFun := fun a => ⟨idx.symm (σ, a.1), (h _).2 (by simpa using a.2)⟩
      left_inv := fun k => ?_
      right_inv := fun a => by simp }
  ext1
  simp only
  rw [← ((h k.1).1 k.2).1]; simp
end GlobalTheory.FramePeriod
