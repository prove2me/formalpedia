-- Prove2me | solution 1 for GlobalTheory.FormalChartOf.tmul_eps_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:47:21.312936+00:00
-- url     : https://prove2.me/submissions/53af799d-3dba-4904-9838-c2adc52c007f

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFormalChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.FormalChartOf
variable {R₀ : Type} [CommRing R₀]
namespace GlobalTheory.FormalChartOf
theorem _root_.solution [IsLocalRing R₀] {M : Type} [AddCommGroup M] [Module R₀ M]
    (v : M ⊗[R₀] (dualProj R₀).ker) : ∃ w : M, v = w ⊗ₜ epsK R₀ := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨0, (TensorProduct.zero_tmul _ _).symm⟩
  | tmul w a =>
    refine ⟨TrivSqZeroExt.snd (a.1 : DualNumber R₀) • w, ?_⟩
    rw [TensorProduct.smul_tmul]
    congr 1
    apply Subtype.ext
    have h' : TrivSqZeroExt.fst (a.1 : DualNumber R₀) = 0 := a.2
    change (a.1 : DualNumber R₀) = TrivSqZeroExt.snd (a.1 : DualNumber R₀) • (DualNumber.eps : DualNumber R₀)
    ext <;> simp [h']
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, (TensorProduct.add_tmul _ _ _).symm⟩
end GlobalTheory.FormalChartOf
