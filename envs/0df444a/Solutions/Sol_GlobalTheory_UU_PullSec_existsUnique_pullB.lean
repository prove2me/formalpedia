-- Prove2me | solution 1 for GlobalTheory.UU.PullSec.existsUnique_pullB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:11:35.715358+00:00
-- url     : https://prove2.me/submissions/a37a9911-0960-437a-90e0-1e1169d523cd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniquePullB
import Theorems.Thm_GlobalTheory_UU_PullSec_sec_eq
import Theorems.Thm_GlobalTheory_UU_PullSec_exists_pullSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sec_ext_val


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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.PullSec
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
namespace GlobalTheory.UU.PullSec
theorem _root_.solution (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (k : ℕ) (f : ∀ α, SecBT D T k α) :
    ∃! s, PullB D F φ k f s := by
  have hc : ∀ (α : D.X) (i : Fin 4), DegPre.famφ D F α i = (φ ▷ D.P.A).left ≫ famφT D T α i := fun α i => by
    have u : φ ▷ D.P.A ≫ toUnit (T ⊗ D.P.A) = toUnit _ := toUnit_unique _ _
    have a₀ : snd (TF (R := R) F) D.P.A = φ ▷ D.P.A ≫ snd T D.P.A := (whiskerRight_snd _ _).symm
    have a₂ : ∀ c : 𝟙_ _ ⟶ D.P.A, toUnit (DegPre.BF D F) ≫ c = φ ▷ D.P.A ≫ toUnit (T ⊗ D.P.A) ≫ c := fun c => by
      rw [← Category.assoc, u]
    fin_cases i
    · exact congrArg (fun q => q.left) a₀
    · exact congrArg (fun q => q.left) ((congrArg₂ (· * ·) a₀ (a₂ (D.c α))).trans (MonObj.comp_mul _ _ _).symm)
    · exact congrArg (fun q => q.left) (a₂ (D.c α))
    · exact congrArg (fun q => q.left) (a₂ η[D.P.A])
  choose s hs using fun α => exists_pullSec D.P.isLB (φ ▷ D.P.A).left (hc α) (f α)
  have key : PullB D F φ k f s := fun α z J hJ => (hs α _ (𝟙 _) z J hJ).trans (by rw [Category.id_comp])
  exact ⟨s, key, fun s' key' => funext fun α => sec_eq fun j => sec_ext_val D.P.isLB
    (fun z J hJ => (key' α z J hJ).trans (key α z J hJ).symm) j⟩
end GlobalTheory.UU.PullSec
