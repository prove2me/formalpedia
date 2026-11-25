-- Prove2me | solution 1 for GlobalTheory.TwistZero.exists_untwist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:20:24.931956+00:00
-- url     : https://prove2.me/submissions/f0436c39-e517-40fc-a4ab-7299f1a2892a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_TorsionZeroCountTwist
import Theorems.Thm_GlobalTheory_TwistZero_Triv_inv
import Theorems.Thm_GlobalTheory_TwistZero_triv_iter
import Theorems.Thm_GlobalTheory_TwistZero_untransl_translPt
import Theorems.Thm_GlobalTheory_TwistZero_translPt_untransl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_genSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_sval_mulSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_sval_pullSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_formEq_of_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
  ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TwistZero
namespace GlobalTheory.TwistZero
theorem _root_.solution {k : Type} [Field k] (hsq : SquareSt) (P : PolAV (Sp k)) (q : ℕ) (hq : 2 ≤ q)
    (b : baseOver (Sp k) ⟶ P.A) (s : LB.Sec (twistLB P.A P.L q (b ^ q))) :
    ∃ s' : (lbPow P.L q).Sec, ∀ (Z : Scheme.{0}) (r : Z ⟶ (baseOver (Sp k) ⊗ P.A).left) (z : Z)
      (J : (Z ⟶ P.A.left) → P.L.ι), Good P.L z J → ∃ u : (Z.presheaf.stalk z)ˣ,
        sval s' (r ≫ (translPt P.A b).left) z J =
          sval (φ := ![(snd (baseOver (Sp k)) P.A).left, (translPt P.A (b ^ q)).left])
            (ε := ![(q : ℤ) - 1, 1]) s r z J * u := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 2 := ⟨q - 2, by omega⟩
  obtain ⟨t, ht⟩ := (triv_iter hsq P b n).inv
  have e1 : (untransl P.A b).left ≫ (translPt P.A b).left = 𝟙 _ := by
    rw [← Over.comp_left, untransl_translPt]; rfl
  have e2 : (translPt P.A b).left ≫ (untransl P.A b).left = 𝟙 _ := by
    rw [← Over.comp_left, translPt_untransl]; rfl
  obtain ⟨s', hs'⟩ := exists_sec P.isLB (K' := PUnit) (φ' := fun _ => 𝟙 P.A.left)
    (ε' := fun _ => ((n + 2 : ℕ) : ℤ))
    (formEq_of_add fun U _ hh => by
      simp [Fintype.sum_sum_type, Fin.sum_univ_succ, e1]
      module)
    (pullSec (mulSec (φ := ![(snd (baseOver (Sp k)) P.A).left, (translPt P.A (b ^ (n + 2))).left])
      (ε := ![((n + 2 : ℕ) : ℤ) - 1, 1]) s (genSec t ht)) (untransl P.A b).left)
  refine ⟨s', fun Z r z J hJ => ⟨val t r z J, ?_⟩⟩
  rw [hs' Z _ z J hJ, sval_pullSec _ _ _ z hJ, Category.assoc, e2, Category.comp_id]
  exact (sval_mulSec _ _ _ z hJ).trans (congrArg (_ * ·) (sval_genSec t ht r z hJ))
end GlobalTheory.TwistZero
