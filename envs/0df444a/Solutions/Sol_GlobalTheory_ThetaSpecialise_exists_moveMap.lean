-- Prove2me | solution 1 for GlobalTheory.ThetaSpecialise.exists_moveMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:10:35.664639+00:00
-- url     : https://prove2.me/submissions/eb4c8582-1516-4187-912c-d51539e06715

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsMoveMap
import Theorems.Thm_GlobalTheory_SecPull_existsUnique_secPull
import Theorems.Thm_GlobalTheory_SecPull_mem_wchart_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange
variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]
variable {w : LB.Iso L' (L.pull Φ)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
  {S F : Type} [CommRing S] [CommRing F] {fS : S →+* F}
  {π : Y ⟶ Spec (CommRingCat.of S)} {π' : Y' ⟶ Spec (CommRingCat.of F)}
namespace GlobalTheory.ThetaSpecialise
theorem _root_.solution (hL : L.IsLB) (hL' : L'.IsLB) (hw : w.IsGen) (hc : ∀ κ, φ' κ ≫ Φ = h ≫ φ κ)
    (hp : h ≫ π = π' ≫ Spec.map (CommRingCat.ofHom fS)) :
    ∃ mv : SecOver π (LB.LinComb L φ ε) →ₛₗ[fS] SecOver π' (LB.LinComb L' φ' ε),
      ∀ s s', PSec w φ' φ ε h s' s ↔ mv s = s' := by
  have ex := SecPull.existsUnique_secPull _ _ _ _ _ _ _ hL hL' w hw K φ' φ ε h hc
  choose mv hmv using fun s : SecOver π (LB.LinComb L φ ε) => (ex s).exists
  have m : ∀ {Z : Scheme.{0}} {r : Z ⟶ Y'} {z : Z} {p : K → L.ι}, (∀ κ, Φ (φ' κ (r z)) ∈ L.U (p κ)) →
      (r ≫ h) z ∈ LB.wchart L φ p := fun hp => SecPull.mem_wchart_comp hc (Set.mem_iInter.2 hp)
  refine ⟨{ toFun := mv
            map_add' := fun a b => (ex _).unique (hmv _) fun Z r z p q hp hq => ?_
            map_smul' := fun c a => (ex _).unique (hmv _) fun Z r z p q hp₁ hq => ?_ },
    fun s s' => ⟨fun H => (ex s).unique (hmv s) H, fun H => H ▸ hmv s⟩⟩
  · refine (gs_add _ z _ (m hp) _ _).trans (Eq.trans ?_ (congrArg _ (gs_add r z _ (mem_wchart.2 hq) _ _)).symm)
    rw [mul_add]
    exact congrArg₂ (· + ·) (hmv a Z r z p q hp hq) (hmv b Z r z p q hp hq)
  · refine (gs_smul π _ z _ (m hp₁) _ _).trans
      (Eq.trans ?_ (congrArg _ (gs_smul π' r z _ (mem_wchart.2 hq) _ _)).symm)
    rw [mul_left_comm, Category.assoc, hp, ← Category.assoc, constVal_specMap]
    exact congrArg _ (hmv a Z r z p q hp₁ hq)
end GlobalTheory.ThetaSpecialise
