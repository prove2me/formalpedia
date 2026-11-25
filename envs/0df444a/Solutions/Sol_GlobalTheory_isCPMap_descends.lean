-- Prove2me | solution 1 for GlobalTheory.isCPMap_descends
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:18:14.582464+00:00
-- url     : https://prove2.me/submissions/d6c79ac2-6819-4c7f-bf11-84230fabbbeb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsCPMapDescends
import Theorems.Thm_GlobalTheory_IsoDesc_appLE_eq_of_gm
import Theorems.Thm_GlobalTheory_IsoDesc_exists_isQuot
import Theorems.Thm_GlobalTheory_IsoDesc_IsQuot_pgen
import Theorems.Thm_GlobalTheory_IsoDesc_eqns_quot
import Theorems.Thm_GlobalTheory_IsoDesc_isCPMap_of_lift
import Theorems.Thm_GlobalTheory_IsoDesc_quot_invariant
import Theorems.Thm_GlobalTheory_UU_IsWt_mul
import Theorems.Thm_GlobalTheory_invariant_functions_descend
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory.IsoDesc
namespace GlobalTheory
theorem _root_.solution : ∀ (S S' : Scheme.{0}) [ConnectedSpace S'] (f : S' ⟶ S) (X : Type) [AddCommGroup X] [Module.Free ℤ X] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] [ConnectedSpace G'.left] (Q : TQ G' X) (P' : CP G') (D : Q.Desc P') (B : Over S) [GrpObj B] [IsCommMonObj B] (M : CP B) (β : Q.B.left ⟶ B.left) (hβ : β ≫ B.hom = Q.B.hom ≫ f) (hw) (w), (∀ (T : Over S') (x y : T ⟶ Q.B), toBase hβ (x * y) = toBase hβ x * toBase hβ y) → IsCPMap P' M f (Q.q.left ≫ β) hw w → ∃ v, IsCPMap D.M M f β hβ v := by
  intro S S' _ f X _ _ G _ _ _ Q P D B _ _ M β hβ hw w mul Hw
  have := Q.q_hom
  have := Q.q_flat
  have := Q.q_surj
  have := Q.q_affine
  have gu := (isGen_iff _).1 D.map.gen
  have gw' := (isGen_iff _).1 Hw.gen
  obtain ⟨s, hs⟩ := exists_isQuot P.L.isLB D.M.L.isLB M.L.isLB gu gw'
  have desc : ∀ j i, ∃ v : Γ(Q.B.left, dom D.M.L.L M.L.L β j i)ˣ, pullU Q.q.left _ v = s j i := fun j i => by
    obtain ⟨-, h₁, h₂⟩ := GlobalTheory.invariant_functions_descend S' G Q.B _ Q.q Q.i Q.q_hom Q.i_hom Q.q_flat Q.q_surj
      inferInstance Q.isKernel (dom D.M.L.L M.L.L β j i)
    obtain ⟨a, ha⟩ := h₂ (s j i).val fun Z t g k₁ k₂ => appLE_eq_of_gm _ _ _ k₁ k₂ _ fun z =>
      quot_invariant mul D.map Hw hs t g z j i (k₂ trivial)
    exact ⟨(h₁ a (ha ▸ (s j i).isUnit)).unit, Units.ext ha⟩
  choose v hv using desc
  have val_v : ∀ (Y : Scheme.{0}) (r : Y ⟶ G.left) (y : Y) j i, Q.q.left (r y) ∈ dom D.M.L.L M.L.L β j i →
      gw (⟨fun p => v (p.1 PUnit.unit) p.2⟩ : LB.Iso D.M.L.L (M.L.L.pull β)) (r ≫ Q.q.left) y j i =
        gm r y _ (s j i) := fun Y r y j i h => by
    rw [← hv]; exact (gm_pull r Q.q.left y _ h _).symm
  refine ⟨_, isCPMap_of_lift (q := Q.q) mul (hs.pgen P.L.isLB gu gw' val_v) fun T z I J hI hJ => ?_⟩
  have := eqns_quot (hβ := hβ) D.map Hw hs hI hJ
  refine cast (congrArg _ (funext fun x => ?_)) this
  exact (val_v _ x.left z _ _ ⟨mem_pull.2 (hJ ((x ≫ Q.q).left ≫ β)), hI (x ≫ Q.q).left⟩).symm
end GlobalTheory
