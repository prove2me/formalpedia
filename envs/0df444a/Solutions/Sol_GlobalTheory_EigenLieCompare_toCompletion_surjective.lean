-- Prove2me | solution 1 for GlobalTheory.EigenLieCompare.toCompletion_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:55:57.227265+00:00
-- url     : https://prove2.me/submissions/18ba4782-74ed-4738-9a42-616b90d60f1e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_ConjugatePlaceEigen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CotangentBidualToTangentFunctionInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NonemptyPadicIntRingHomOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsTorusAndQuotientHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MulEqZeroOfToCompletion
import Theorems.Thm_GlobalTheory_EigenLieCompare_tauExt_toPadic
import Theorems.Thm_GlobalTheory_EigenLieCompare_mem_iff_algebraMap
import Theorems.Thm_GlobalTheory_EigenLieCompare_integers_Ow
import Theorems.Thm_GlobalTheory_EigenLieCompare_valued_algebraMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_isPrecomplete_finite_module


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open GlobalTheory GlobalTheory.EigenLieCompare
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen GlobalTheory.HodgeTateCompare
variable {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E]
  {w : HeightOneSpectrum (𝓞 E)}
variable [Algebra ℤ_[p] (Ow w)]
namespace GlobalTheory.EigenLieCompare
theorem _root_.solution (hw : IsOver p w) :
    Function.Surjective (tauExt (p := p) (algebraMap (𝓞 E) (Ow w))) := by
  let I := IsLocalRing.maximalIdeal ℤ_[p]
  haveI : IsPrecomplete I (PadicOrder p E) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module I _
  have hI : I.map (algebraMap ℤ_[p] (Ow w)) = Ideal.span {(p : Ow w)} := by
    rw [show I = _ from PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton,
      map_natCast]
  haveI : IsHausdorff I (Ow w) := by
    rw [← IsHausdorff.map_algebraMap_iff (S := Ow w)]
    refine IsHausdorff.of_le_jacobson _ _ ?_
    rw [hI, IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top, Ideal.span_singleton_le_iff_mem,
      ← map_natCast (algebraMap (𝓞 E) (Ow w))]
    exact (mem_iff_algebraMap w _).1 hw
  refine surjective_of_mkQ_comp_surjective (I := I)
    (f := (tauExt (p := p) (algebraMap (𝓞 E) (Ow w))).toLinearMap) fun y => ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  have hp0 : w.intValuation (p : 𝓞 E) ≠ 0 :=
    w.intValuation_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  obtain ⟨r, hr⟩ := GlobalTheory.Idele.exists_valued_sub_le w (a := (y : w.adicCompletion E)) y.2
    (-(w.intValuation (p : 𝓞 E)).log).toNat
  have hd : (p : Ow w) ∣ y - algebraMap (𝓞 E) (Ow w) r := by
    refine (integers_Ow w).dvd_of_le ?_
    rw [← map_natCast (algebraMap (𝓞 E) (Ow w)), valued_algebraMap]
    refine le_trans hr ?_
    conv_rhs => rw [← WithZero.exp_log hp0]
    rw [WithZero.exp_le_exp]
    omega
  refine ⟨toPadic p E r, ?_⟩
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, tauExt_toPadic, eq_comm,
    Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Ideal.smul_top_eq_map, hI]
  exact Ideal.mem_span_singleton.2 hd
end GlobalTheory.EigenLieCompare
