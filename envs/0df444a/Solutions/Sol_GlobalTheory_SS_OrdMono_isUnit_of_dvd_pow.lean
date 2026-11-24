-- Prove2me | solution 1 for GlobalTheory.SS.OrdMono.isUnit_of_dvd_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:53:34.719335+00:00
-- url     : https://prove2.me/submissions/a200c97c-151e-4e3a-9a21-6e760e5b6d96

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ChainRuleAndJacobianCriterion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenImmersionOfExtendsIdOfEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobianOrderMonotoneSemistableModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.Ord
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.OrdMono
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}
  {I : Type} [Fintype I] [DecidableEq I]
namespace GlobalTheory.SS.OrdMono
theorem _root_.solution {B : Type} [CommRing B] {p s : B} (hp : Prime p) (h0 : p ∈ nonZeroDivisors B)
    (hs : ¬ p ∣ s) (k : ℕ) (h : s ∣ p ^ k) : IsUnit s := by
  induction k with
  | zero => exact isUnit_of_dvd_one (by simpa using h)
  | succ k ih =>
    obtain ⟨b, hb⟩ := h
    obtain ⟨b', rfl⟩ : p ∣ b := (hp.dvd_or_dvd (hb ▸ dvd_pow_self p k.succ_ne_zero)).resolve_left hs
    refine ih ⟨b', ?_⟩
    have : p * (p ^ k - s * b') = 0 := by linear_combination hb
    exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff_left.1 h0) _ this)
end GlobalTheory.SS.OrdMono
