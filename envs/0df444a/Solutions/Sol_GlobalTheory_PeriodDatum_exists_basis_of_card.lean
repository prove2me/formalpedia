-- Prove2me | solution 1 for GlobalTheory.PeriodDatum.exists_basis_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:18:37.453136+00:00
-- url     : https://prove2.me/submissions/087b270c-774d-4b21-a7d5-2a1db97ec2e5

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_DualLattices_SurjectiveAinfTowerZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TeichmullerQuot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ModPToValuationResidueFieldSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DualTowerMapExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsEndDifferentialRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PadicEndApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsTateMatricesLink
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsLiftOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NilpotentCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSeriesOfNaturalOnNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GroupLawPowerSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFormalChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FiniteAlgebraSplitLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinEtaleFormallyUnramified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinRepExistsIsPullbackSpec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinOfLocalAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvBasicNEvalSubCoeffMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsCompatibleBasis

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
open GlobalTheory GlobalTheory.PeriodDatum
namespace GlobalTheory.PeriodDatum
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (g : ℕ) (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (hcV : Nat.card V = p ^ (2 * g)) :
    ∃ f : Ix g → V, ∀ x : V, ∃! t : Ix g → ZMod p, x = ∑ j, (t j).val • f j := by
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hcV]; exact pow_ne_zero _ hp.out.ne_zero)
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hrk : Module.finrank (ZMod p) V = Fintype.card (Ix g) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [hcV, Nat.card_zmod] at h
    have h2 := Nat.pow_right_injective hp.out.two_le h
    rw [← h2, Fintype.card_sum, Fintype.card_fin, two_mul]
  let b : Module.Basis (Ix g) (ZMod p) V :=
    (Module.finBasisOfFinrankEq (ZMod p) V hrk).reindex (Fintype.equivFin (Ix g)).symm
  have hsm : ∀ (t : ZMod p) (y : V), t.val • y = t • y := fun t y => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  refine ⟨b, fun x => ⟨b.equivFun x, ?_, fun t ht => ?_⟩⟩
  · simp only [hsm]
    rw [← b.equivFun_symm_apply, LinearEquiv.symm_apply_apply]
  · simp only [hsm] at ht
    rw [← b.equivFun_symm_apply] at ht
    rw [ht, LinearEquiv.apply_symm_apply]
end GlobalTheory.PeriodDatum
