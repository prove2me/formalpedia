-- Prove2me | solution 1 for GlobalTheory.TateMatrices.padicExtension_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:52:53.61964+00:00
-- url     : https://prove2.me/submissions/38239753-56cd-4bdf-8ff7-0dad413d5ca2

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_CharR
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsTateMatricesLink

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2
noncomputable section
open GlobalTheory
open GlobalTheory.TateMatrices
variable {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {B : BX R₀} {O : LAlg R₀}
  {O₀ : Type} [CommRing O₀]
namespace GlobalTheory.TateMatrices
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ] (ρ : O₀ →+* Matrix κ κ ℤ_[p])
    (c : ℤ_[p]) (a : O₀) : padicExtension ρ (c ⊗ₜ[ℤ] a) = c • ρ a := by
  rw [Algebra.smul_def]
  exact Algebra.TensorProduct.lift_tmul _ _ _ c a
end GlobalTheory.TateMatrices
