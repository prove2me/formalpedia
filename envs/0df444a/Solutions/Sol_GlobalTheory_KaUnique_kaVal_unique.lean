-- Prove2me | solution 1 for GlobalTheory.KaUnique.kaVal_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:24:30.658649+00:00
-- url     : https://prove2.me/submissions/bdce39ac-96d7-4ec5-a297-3b47fc260d6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TopLeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KosBlockMulKosD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsSquareDetComparisonEqMulDetPowOfBasisChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KaFormHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubmatrixMulOfVanish
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KeyInvariantFromIntersectionUnique
import Theorems.Thm_GlobalTheory_KaUnique_exists_perm
import Theorems.Thm_GlobalTheory_KaUnique_degree_compare
import Theorems.Thm_GlobalTheory_KaUnique_tComb_congr
import Theorems.Thm_GlobalTheory_BoxDetUnique_exists_perm
import Theorems.Thm_GlobalTheory_KaUnique_jac_chart
import Theorems.Thm_GlobalTheory_KaUnique_valT_sec
import Theorems.Thm_GlobalTheory_kaForm_homogeneous


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
namespace GlobalTheory.KaUnique
theorem _root_.solution : Out.Laws → ∀ (K : Type) [Field K] [CharZero K] (x : KeyIn K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (s : Fin x.P.g → RR x n) (κ κ' : Kˣ), admitted x.P.g n l l' al → KaVal x n l l' al s κ → KaVal x n l l' al s κ' → κ = κ' := by
  intro hL K _ _ x n l l' al s κ κ' ⟨_, hl, hl', hal⟩
    ⟨z, ch, b₁, b₂, t₁, t₂, J, lam₁, lam₂, hz, hJ, hb₁, hb₂, ht₁, ht₂, hκ⟩
    ⟨z', ch', b₁', b₂', t₁', t₂', J', lam₁', lam₂', hz', hJ', hb₁', hb₂', ht₁', ht₂', hκ'⟩
  obtain ⟨σ, hσ⟩ := exists_perm hz hz'
  have hc : ∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch' (σ a)) := fun a => hσ a ▸ hz'.1 (σ a)
  let ga := fun a => trU (T := K) (z a).left x.P.L (ch a) (ch' (σ a)) (hz.1 a) (hc a)
  have hga : ∀ (k : ℕ) a (r : RR x k), valT (T := K) (z a).left (x.P.L.U (ch a)) (r.f (ch a)) =
      (ga a).val ^ k * valT (T := K) (z' (σ a)).left (x.P.L.U (ch' (σ a))) (r.f (ch' (σ a))) := fun k a r => by
    rw [hσ a]
    exact valT_sec (T := K) (z a).left x.P.L _ _ (hz.1 a) (hc a) k r
  obtain ⟨be₁, e₁, f₁⟩ := degree_compare hL x hal hl hz hz' σ ga (hga _) hb₁ hb₁' ht₁ ht₁'
  obtain ⟨be₂, e₂, f₂⟩ := degree_compare hL x hal (hl.trans hl') hz hz' σ ga (hga _) hb₂ hb₂' ht₂ ht₂'
  have eJ : J' = J * (∏ a, ga a) ^ (-((x.P.g * n : ℕ) : ℤ)) * 1 ^ 2 := by
    rw [one_pow, _root_.mul_one, zpow_neg, zpow_natCast, eq_mul_inv_iff_mul_eq]
    apply Units.ext
    rw [Units.val_mul, hJ, hJ', ← Equiv.prod_comp σ, Units.val_pow_eq_pow_val, Units.coe_prod, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    have h0 := hz'.2.1 (σ a)
    rw [hσ a] at h0 ⊢
    rw [jac_chart x s (z a) (ch a) (ch' (σ a)) (hz.1 a) (hc a) h0, mul_comm]
  have key := GlobalTheory.kaForm_homogeneous K x.P.g n l l' t₁ t₂ J (∏ a, ga a) 1 1 lam₁ lam₂ be₁ be₂ hl hl'
  rw [one_pow (8 * kaExp _ _ _ _), _root_.mul_one, ← e₁, ← e₂, ← eJ] at key
  rw [hκ, hκ', ← key]
  unfold kaForm
  rw [tComb_congr _ _ _ _ t₁' f₁, tComb_congr _ _ _ _ t₂' f₂]
end GlobalTheory.KaUnique
