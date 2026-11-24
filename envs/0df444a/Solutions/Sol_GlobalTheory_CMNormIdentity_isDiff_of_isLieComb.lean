-- Prove2me | solution 1 for GlobalTheory.CMNormIdentity.isDiff_of_isLieComb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:37:21.646968+00:00
-- url     : https://prove2.me/submissions/5f098cb2-4733-42a1-8559-e1ed31f526b8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsLinearOfIsMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingSmul
import Theorems.Thm_GlobalTheory_CMNormIdentity_primeSpectrum_dualNumber_eq
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CMNormIdentity
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.CMNormIdentity
theorem _root_.solution {w : Fin g → ℂ} {v v' : epsR ℂ ⟶ A} (h : u.IsDiff w v) (c : ℂ)
    (hc : IsLieComb ![c] ![v] v') : u.IsDiff (c • w) v' := by
  obtain ⟨y, hy, hv'⟩ := hc
  have hl : v'.left = spMap (epsScaleR c) ≫ v.left := by
    have := hy 0
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, _root_.mul_one] at hv'
    rw [hv']
    simpa using this
  intro U
  rw [hl]
  intro hU f
  have hU' : ⊤ ≤ v.left ⁻¹ᵁ U := fun x _ => by
    have := hU (Set.mem_univ x)
    have hx : (spMap (epsScaleR c)) x = x := primeSpectrum_dualNumber_eq _ _
    change v.left ((spMap (epsScaleR c)) x) ∈ U at this
    rwa [hx] at this
  rw [map_smul, ← h U hU' f]
  have e : (spMap (epsScaleR c) ≫ v.left).appLE U ⊤ hU = v.left.appLE U ⊤ hU' ≫ (spMap (epsScaleR c)).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE (spMap (epsScaleR c)) v.left U ⊤ ⊤ hU' le_rfl).symm
  have e2 := congrArg (fun k => k.hom ((v.left.appLE U ⊤ hU').hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (epsScaleR c)))
  rw [e]
  refine (congrArg TrivSqZeroExt.snd e2).trans ?_
  simp [epsScaleR]
end GlobalTheory.CMNormIdentity
