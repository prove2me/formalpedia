-- Prove2me | solution 1 for GlobalTheory.GeneratorLaw.Rep.exists_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:15:18.815801+00:00
-- url     : https://prove2.me/submissions/83680d4d-cfb9-4962-aa2f-fd1b9764daad

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_PrimitiveCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGrpObjSplitExtensionOfGenerators
import Theorems.Thm_GlobalTheory_GeneratorLaw_compat_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GeneratorLaw
variable {X Y Y' : Scheme.{0}} {L : LB X}
namespace GlobalTheory.GeneratorLaw
namespace Rep
theorem _root_.solution (hL : L.IsLB) {b : Y ⟶ X} {F : Vals L Y} (h : Rep L (fun _ _ k => (k b)⁻¹) F) :
    ∃ s : ∀ i : L.ι, Γ(Y, b ⁻¹ᵁ L.U i)ˣ, GenScheme.Compat L b s ∧
      ∀ Z r z J, Good L z J → gm r z (b ⁻¹ᵁ L.U (J (r ≫ b))) (s _) = F Z r z J := by
  obtain ⟨K, _, φ, ε, t, ht, hs, hv⟩ := h
  obtain ⟨t', ht', h'⟩ := exists_gen hL (K' := PUnit) (φ' := fun _ => b) (ε' := fun _ => -1)
    (fun V _ k => (hs V k).trans (by simp)) t ht
  have le : ∀ i, b ⁻¹ᵁ L.U i ≤ LB.wchart L (fun _ : PUnit => b) fun _ => i :=
    fun i y hy => Set.mem_iInter.2 fun _ => hy
  refine ⟨fun i => res (le i) (t'.s fun _ => i), (compat_iff _).2 fun Z r z i i' hi hi' => ?_,
    fun Z r z J hJ => ?_⟩
  · refine (gm_res r z (le i') hi' _).trans (Eq.trans ?_ (congrArg (_ * ·) ((gm_res r z (le i) hi _).trans
      (gen_trans ht' r z (le i hi) (le i' hi')))).symm)
    simp [trF]
  · rw [← hv _ _ _ _ hJ, ← h' _ _ _ _ hJ]
    exact gm_res r z (le _) (hJ (r ≫ b)) _
end Rep
end GlobalTheory.GeneratorLaw
