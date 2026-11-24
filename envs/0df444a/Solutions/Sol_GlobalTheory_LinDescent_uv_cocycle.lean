-- Prove2me | solution 1 for GlobalTheory.LinDescent.uv_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:45:05.867159+00:00
-- url     : https://prove2.me/submissions/ec567e95-e2ac-44a0-9ee6-276466a43f2e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Theorems.Thm_GlobalTheory_LinDescent_uv_trans
import Theorems.Thm_GlobalTheory_LinDescent_val_eq_uv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
variable {X Y Z : Scheme.{0}}
variable {L : LB X}
namespace GlobalTheory.LinDescent
theorem _root_.solution (hL : L.IsLB) {t₁ t₂ t₃ : X ⟶ X} (e : t₁ ≫ t₂ = t₃)
    {u₁ : LB.Gen (twist L t₁)} {u₂ : LB.Gen (twist L t₂)} {u₃ : LB.Gen (twist L t₃)}
    (h₁ : u₁.IsGen) (h₂ : u₂.IsGen) (h₃ : u₃.IsGen)
    (h : LB.Gen.Corr L _ _ _ _ u₃ (LB.mulGen L _ _ _ _ u₁ (LB.pullGen L _ _ u₂ t₁)))
    (r : Z ⟶ X) (z : Z) {i j k : L.ι} (hi : r z ∈ L.U i) (hj : (r ≫ t₁) z ∈ L.U j)
    (hk : (r ≫ t₃) z ∈ L.U k) :
    uv u₃ r z i k = uv u₁ r z i j * uv u₂ (r ≫ t₁) z j k := by
  choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have hJ' : Good L z J := hJ
  have e' : (r ≫ t₁) ≫ t₂ = r ≫ t₃ := by rw [Category.assoc, e]
  have := val_corr hJ' h r
  rw [val_mul hJ', val_pull hJ', val_eq_uv, val_eq_uv, val_eq_uv, e'] at this
  rw [uv_trans h₃ r z hi hk (hJ r) (hJ _), uv_trans h₁ r z hi hj (hJ r) (hJ _),
    uv_trans h₂ (r ≫ t₁) z hj (e' ▸ hk) (hJ _) (e' ▸ hJ (r ≫ t₃)), this, e']
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end GlobalTheory.LinDescent
