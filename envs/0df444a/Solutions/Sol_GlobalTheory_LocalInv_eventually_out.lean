-- Prove2me | solution 1 for GlobalTheory.LocalInv.eventually_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:25:59.707402+00:00
-- url     : https://prove2.me/submissions/f6a206b2-bd4b-4a04-9be2-41cebf1c1f28

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_NoLocalInvariants
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_TemperedRepresentations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeightRegularOfExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LocalInv
open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace GlobalTheory.LocalInv
theorem _root_.solution (i : N.Loc) :
    ∀ᶠ w in Filter.cofinite, IsSplitPl H w → SplitOut N i w := by
  have h1 : (placesOver H.E (N.l i)).Finite := by
    have hne : Ideal.span {((N.l i : ℕ) : 𝓞 H.E)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : (N.l i).Prime).ne_zero
    refine (Ideal.finite_factors hne).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.mpr hv
  filter_upwards [h1.compl_mem_cofinite, (N.S i).finite_toSet.compl_mem_cofinite,
    (N.Q i).finite_toSet.compl_mem_cofinite] with w a b c hs
  exact ⟨hs, a, b, c⟩
end GlobalTheory.LocalInv
