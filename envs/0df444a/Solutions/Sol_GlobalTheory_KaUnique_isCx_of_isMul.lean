-- Prove2me | solution 1 for GlobalTheory.KaUnique.isCx_of_isMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:00:40.452814+00:00
-- url     : https://prove2.me/submissions/21fd5d7e-9c09-49c5-b637-c8c105984c43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SignSwap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TopLeTranslate
import Theorems.Thm_GlobalTheory_KaUnique_comb_unique
import Theorems.Thm_GlobalTheory_KaUnique_isMul_comb
import Theorems.Thm_GlobalTheory_KaUnique_isCx_kosD


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KaUnique
variable {R : Type} [CommRing R]
namespace GlobalTheory.KaUnique
theorem _root_.solution {x : KeyIn R} {n l d : ℕ} {s : Fin x.P.g → RR x n} {z : Fin d → Pt x} {ch : Fin d → x.P.L.ι}
    {b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)} {m} (hm : IsMul x l s b m)
    (hb : ∀ j ≤ x.P.g, IsBasis x (b j)) (hz : EtZ x s z ch) :
    IsCx kdeg (kosD (N := fun j => (l - j * n) ^ x.P.g) m
      (fun j => Matrix.of fun a k => valT (T := R) (z a).left (x.P.L.U (ch a)) ((b j k).f (ch a)))) := by
  refine isCx_kosD (N := fun j => (l - j * n) ^ x.P.g) m _ (fun i i' j hj => ?_) (fun i => ?_)
  · ext a k
    have h1 := IsComb.mulVec (isMul_comb hm i j (by omega)) (isMul_comb hm i' (j + 1) hj k)
    have h2 := IsComb.mulVec (isMul_comb hm i' j (by omega)) (isMul_comb hm i (j + 1) hj k)
    simp only [mul_left_comm (fam x s i' _) (fam x s i _)] at h2
    exact congrFun (comb_unique (hb j (by omega)) h1 h2) a
  · ext a k
    have h1 := (isMul_comb hm i 0 x.g_pos k).valT (z a).left (Over.w (z a)) (ch a) (hz.1 a)
    refine h1.symm.trans ?_
    have h2 : valT (T := R) (z a).left (x.P.L.U (ch a)) (fam x s i (ch a)) = 0 := hz.2.1 a i
    rw [valT_eq _ _ (hz.1 a)] at h2
    beta_reduce
    rw [valT_eq _ _ (hz.1 a), map_mul, h2, zero_mul]
    rfl
end GlobalTheory.KaUnique
