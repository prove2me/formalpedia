-- Prove2me | solution 1 for GlobalTheory.LamBiext.exists_laws
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:59:06.507646+00:00
-- url     : https://prove2.me/submissions/aacb8a43-18ea-440e-bbef-3d02c3e4a89b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_MulGenNegRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLaws
import Theorems.Thm_GlobalTheory_LamBiext_nest_isGen
import Theorems.Thm_GlobalTheory_LamBiext_val_nest
import Theorems.Thm_P2M_GlobalTheory_LamBiext_prod_law__e869053602e8
import Theorems.Thm_P2M_GlobalTheory_LamBiext_prod_law__08503da5c723
import Theorems.Thm_P2M_GlobalTheory_LamBiext_formEq__87630df18372
import Theorems.Thm_P2M_GlobalTheory_LamBiext_formEq__cd7eb449d15c
import Theorems.Thm_GlobalTheory_LamBiext_nest_isCube
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LamBiext
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
namespace GlobalTheory.LamBiext
theorem _root_.solution (L : RigLB G) (c : CubicalStr G L) :
    ∃ (l₁ : LB.Gen (LB.LinComb (lamLB L) (law1φ G (x3 G 0) (x3 G 1) (x3 G 2)) lawε))
      (l₂ : LB.Gen (LB.LinComb (lamLB L) (law2φ G (x3 G 0) (x3 G 1) (x3 G 2)) lawε)), l₁.IsGen ∧ l₂.IsGen ∧
      GlobalTheory.BiextSignTwist.LawIsCube G L c _ l₁ ∧ GlobalTheory.BiextSignTwist.LawIsCube G L c _ l₂ ∧
      ∀ {T : Over S} (y : T.left) (JP : (T.left ⟶ (G2 G).left) → ULift.{0} (Finset (Fin 2)) → L.L.ι)
        (_ : Good (lamLB L) y JP) (J : (T.left ⟶ G.left) → L.L.ι) (_ : Good L.L y J),
        (∀ a b d : T ⟶ G, val (L := lamLB L) l₁ (lift a (lift b d)).left y JP =
          adj (lamφ G) lamε y JP J (lift (a * b) d).left * (adj (lamφ G) lamε y JP J (lift a d).left)⁻¹ *
            (adj (lamφ G) lamε y JP J (lift b d).left)⁻¹ * cubV c y J a b d) ∧
        (∀ a b d : T ⟶ G, val (L := lamLB L) l₂ (lift a (lift b d)).left y JP =
          adj (lamφ G) lamε y JP J (lift a (b * d)).left * (adj (lamφ G) lamε y JP J (lift a b).left)⁻¹ *
            (adj (lamφ G) lamε y JP J (lift a d).left)⁻¹ * cubV c y J a b d) := by
  obtain ⟨t₁, g₁, v₁⟩ := exists_gen L.isLB (φ := thφ G (x3 G)) (ε := thε) formEq₁ c.t c.isGen
  obtain ⟨t₂, g₂, v₂⟩ := exists_gen L.isLB (φ := thφ G (x3 G)) (ε := thε) formEq₂ c.t c.isGen
  refine ⟨nest L.L _ _ _ _ t₁, nest L.L _ _ _ _ t₂, nest_isGen g₁, nest_isGen g₂,
    nest_isCube L c _ t₁ (corr_of_val L.isLB fun y J hJ => v₁ _ _ y J hJ),
    nest_isCube L c _ t₂ (corr_of_val L.isLB fun y J hJ => v₂ _ _ y J hJ),
    fun y JP hJP J hJ => ⟨fun a b d => ?_, fun a b d => ?_⟩⟩
  · rw [val_nest g₁ _ hJP hJ, prod_law₁ a b d (adj (lamφ G) lamε y JP J), v₁ _ _ y J hJ]
    rfl
  · rw [val_nest g₂ _ hJP hJ, prod_law₂ a b d (adj (lamφ G) lamε y JP J), v₂ _ _ y J hJ]
    rfl
end GlobalTheory.LamBiext
