-- Prove2me | solution 1 for GlobalTheory.SS.frobG_splitTorus_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:09:12.251297+00:00
-- url     : https://prove2.me/submissions/0d3cf758-b020-47bf-9899-b3bf2b98faf5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FrobGSplitTorusPow
import Theorems.Thm_GlobalTheory_SS_appTop_pow_mul
import Theorems.Thm_GlobalTheory_SS_isAffine_splitTorus
import Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val


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
open GlobalTheory GlobalTheory.SS
namespace GlobalTheory.SS
theorem _root_.solution :
    ∀ (k : Type) [Field k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (F : End (splitTorus (Sp k) X)) (q : ℕ), FrobG (splitTorus (Sp k) X) F q → ∃ m, 1 ≤ m ∧ ∀ l, (show splitTorus (Sp k) X ⟶ splitTorus (Sp k) X from F ^ (m * l)) = (𝟙 (splitTorus (Sp k) X)) ^ (q ^ (m * l)) := by
  intro k _ X _ _ _ F q hF
  classical
  have := isAffine_splitTorus k X
  have key : ∀ χ : X, ∃ m : ℕ, 1 ≤ m ∧
      (show splitTorus (Sp k) X ⟶ splitTorus (Sp k) X from F ^ m).left.appTop.hom
        (charUnit (Sp k) X χ).val = (charUnit (Sp k) X χ).val ^ (q ^ m) := by
    intro χ
    obtain ⟨m, hm, h, hh⟩ := hF.2 ⊤ (isAffineOpen_top _) (charUnit (Sp k) X χ).val
    refine ⟨m, hm, ?_⟩
    rw [← hh, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  choose n0 hn1 hn using key
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := X)
  refine ⟨∏ x ∈ s, n0 x, Nat.succ_le_of_lt (Finset.prod_pos fun x _ => hn1 x), fun l => ?_⟩
  let e := splitTorusPointsEquiv (Sp k) X (splitTorus (Sp k) X)
  apply e.injective
  rw [map_pow]
  have hgen : ∀ χ ∈ s, e (show splitTorus (Sp k) X ⟶ splitTorus (Sp k) X from
      F ^ ((∏ x ∈ s, n0 x) * l)) (Multiplicative.ofAdd χ) =
      (e (𝟙 _) ^ (q ^ ((∏ x ∈ s, n0 x) * l))) (Multiplicative.ofAdd χ) := by
    intro χ hχ
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n0 hχ
    apply Units.ext
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, splitTorusPointsEquiv_val,
      splitTorusPointsEquiv_val, hc, Nat.mul_assoc, appTop_pow_mul F q _ _ (hn χ)]
    congr 1
  refine MonoidHom.ext fun x => ?_
  have hx : x.toAdd ∈ Submodule.span ℤ (s : Set X) := by rw [hs]; trivial
  generalize e (show splitTorus (Sp k) X ⟶ splitTorus (Sp k) X from
      F ^ ((∏ x ∈ s, n0 x) * l)) = a at hgen ⊢
  generalize (e (𝟙 _) ^ (q ^ ((∏ x ∈ s, n0 x) * l))) = b at hgen ⊢
  change a (Multiplicative.ofAdd x.toAdd) = b (Multiplicative.ofAdd x.toAdd)
  generalize x.toAdd = w at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add y z _ _ h1 h2 => rw [ofAdd_add, map_mul, map_mul, h1, h2]
  | smul n y _ h => rw [ofAdd_zsmul, map_zpow, map_zpow, h]
end GlobalTheory.SS
