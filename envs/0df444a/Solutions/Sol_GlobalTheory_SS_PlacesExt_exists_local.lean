-- Prove2me | solution 1 for GlobalTheory.SS.PlacesExt.exists_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:11:30.30901+00:00
-- url     : https://prove2.me/submissions/ac90ba4b-cc9f-41c5-b2b0-b5a7f01af022

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesFunctionField
import Theorems.Thm_GlobalTheory_SS_PlacesExt_v_zpow
import Theorems.Thm_GlobalTheory_SS_PlacesExt_v_unit
import Theorems.Thm_GlobalTheory_SS_PlacesExt_v_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_addv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_norm_eq_heightOne
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_dedekindRank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.PlacesExt
open IsDedekindDomain Polynomial ReciprocityTheory.ChartRestriction.G.T0
variable {k F L : Type} [Field k] [Field F] [Algebra k F] [Field L] [Algebra F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L] (Pl : Places k F)
variable (L)
namespace GlobalTheory.SS.PlacesExt
theorem _root_.solution (i : Pl.I) [IsDiscreteValuationRing (Pl.O i)] :
    ∃ (J : Type) (_ : Finite J) (O' : J → ValuationSubring L) (w : J → Lˣ → ℤ),
      (∀ j x y, w j (x * y) = w j x + w j y) ∧ (∀ j (x : Lˣ), (x : L) ∈ O' j ↔ 0 ≤ w j x) ∧
      (∀ y : L, (∀ j, y ∈ O' j) ↔ IsIntegral (Pl.O i) y) ∧
      ∀ y : Lˣ, ∑ᶠ j, w j y = Pl.v i (Units.map (Algebra.norm F) y) := by
  obtain ⟨hD, hFin, -, -, hmax, -⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.dedekindRank (Pl.O i) F L
  haveI := hD
  haveI := hFin
  haveI : IsFractionRing (integralClosure (Pl.O i) L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension (Pl.O i) F L _
  haveI : Finite {Q : Ideal (integralClosure (Pl.O i) L) // Q.IsMaximal} := hmax.to_subtype
  haveI : Finite (HeightOneSpectrum (integralClosure (Pl.O i) L)) :=
    Finite.of_equiv _ (ValPl.hoEquiv (Pl.O i) F L).symm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Pl.O i)
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have he : 0 < Pl.v i (Units.mk0 _ hϖ0) := v_pos Pl i hϖ.not_isUnit _ rfl
  refine ⟨HeightOneSpectrum (integralClosure (Pl.O i) L), inferInstance,
    fun P => (P.valuation L).valuationSubring,
    fun P y => ((P.asIdeal.inertiaDeg (Pl.O i) : ℤ) * -WithZero.log (P.valuation L y)) *
      Pl.v i (Units.mk0 _ hϖ0), fun P x y => ?_, fun P x => ?_, fun y => ⟨fun h => ?_, fun h P => ?_⟩,
    fun y => ?_⟩
  · beta_reduce
    rw [Units.val_mul, map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 x.ne_zero)
      ((Valuation.ne_zero_iff _).2 y.ne_zero)]
    ring
  · have hx : P.valuation L x ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
    haveI := P.isPrime
    have hf : (0 : ℤ) < P.asIdeal.inertiaDeg (Pl.O i) := by
      exact_mod_cast Ideal.inertiaDeg_pos P.asIdeal (Pl.O i)
    rw [Valuation.mem_valuationSubring_iff, ← WithZero.log_le_log hx one_ne_zero, WithZero.log_one,
      mul_nonneg_iff_of_pos_right he, mul_nonneg_iff_of_pos_left hf, neg_nonneg]
  · obtain ⟨b, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one
      (R := integralClosure (Pl.O i) L) L y h
    exact b.2
  · exact P.valuation_le_one (K := L) (⟨y, h⟩ : integralClosure (Pl.O i) L)
  · obtain ⟨u, hu, hN⟩ := ValPl.norm_eq_heightOne (O := Pl.O i) (F := F) (y : L) y.ne_zero hϖ
    have hu0 : (u : F) ≠ 0 := fun h => hu.ne_zero (Subtype.ext h)
    simp only [ValPl.addv_apply _ y.ne_zero, WithTop.untopD_coe] at hN
    have : Units.map (Algebra.norm F) y = Units.mk0 _ hϖ0 ^ (∑ᶠ P : HeightOneSpectrum (integralClosure (Pl.O i) L),
        ((P.asIdeal.inertiaDeg (Pl.O i) : ℤ) * -WithZero.log (P.valuation L y))) * Units.mk0 _ hu0 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val]
      exact hN
    rw [this, Pl.v_mul, v_zpow, v_unit Pl i hu (Units.mk0 _ hu0) rfl, add_zero, finsum_mul' _ _ (Set.toFinite _)]
end GlobalTheory.SS.PlacesExt
