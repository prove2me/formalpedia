-- Prove2me | solution 1 for GlobalTheory.PeriodDatum.exists_compatible_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:26:45.07924+00:00
-- url     : https://prove2.me/submissions/9fbcf2d5-0b14-4fe0-8326-23e7dc44ea19

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
import Theorems.Thm_GlobalTheory_PeriodDatum_exists_basis_of_card
import Theorems.Thm_ReciprocityTheory_PGsh_FP_ext


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
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (g : ℕ) (Γ : Type) [AddCommGroup Γ]
    (hdiv : ∀ x : Γ, ∃ y, p • y = x) (hcard : Nat.card {x : Γ // p • x = 0} = p ^ (2 * g)) :
    ∃ τ : Ix g → ℕ → Γ, (∀ i n, (p ^ (n + 1)) • τ i n = 0) ∧ (∀ i n, τ i n = p • τ i (n + 1)) ∧
      ∀ x : Γ, p • x = 0 → ∃! t : Ix g → ZMod p, x = ∑ j, (t j).val • τ j 0 := by
  obtain ⟨V, hV⟩ : ∃ V : AddSubgroup Γ, ∀ x : Γ, x ∈ V ↔ p • x = 0 :=
    ⟨(nsmulAddMonoidHom p : Γ →+ Γ).ker, fun x => Iff.rfl⟩
  have hcV : Nat.card V = p ^ (2 * g) :=
    (Nat.card_congr (Equiv.subtypeEquivRight hV)).trans hcard
  obtain ⟨b, hb⟩ := @exists_basis_of_card p _ g V _
    (AddCommGroup.zmodModule (fun x => Subtype.ext ((hV _).1 x.2))) hcV
  choose d hd using hdiv
  let τ : Ix g → ℕ → Γ := fun i n => d^[n] (b i : Γ)
  have hτp : ∀ i n, τ i n = p • τ i (n + 1) := fun i n => by
    simp only [τ, Function.iterate_succ_apply', hd]
  have hsum : ∀ t : Ix g → ZMod p, ((∑ j, (t j).val • b j : V) : Γ) = ∑ j, (t j).val • τ j 0 :=
    fun t => by
      rw [AddSubmonoidClass.coe_finset_sum]
      rfl
  refine ⟨τ, fun i n => ?_, hτp, fun x hx => ?_⟩
  · induction n with
    | zero => rw [zero_add, pow_one]; exact (hV _).1 (b i).2
    | succ n ih => rw [pow_succ, mul_smul, ← hτp i n, ih]
  · obtain ⟨t, ht, hu⟩ := hb ⟨x, (hV x).2 hx⟩
    refine ⟨t, ?_, fun t' ht' => hu t' (Subtype.ext ?_)⟩
    · exact (congrArg Subtype.val ht).trans (hsum t)
    · exact ht'.trans (hsum t').symm
end GlobalTheory.PeriodDatum
