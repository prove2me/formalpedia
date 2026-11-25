-- Prove2me | solution 1 for GlobalTheory.KaScale.kaVal_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:17:20.569191+00:00
-- url     : https://prove2.me/submissions/39298f2d-6032-4208-b4fe-b0bdf7173c75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KaFormHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubsingletonPrimeSpectrum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsSquareDetComparisonScaleSec
import Theorems.Thm_GlobalTheory_KaScale_isSquareDetComparison_scale_sec
import Theorems.Thm_GlobalTheory_KaScale_jac_scale
import Theorems.Thm_GlobalTheory_LieComb_lieComb_algebra
import Theorems.Thm_GlobalTheory_SqZero_IsAway_lift
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_kaForm_homogeneous
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD scaleD prodPts isTan_iff isLieComb_iff comp_one' isTan_mul isTan_one
  isTan_scale)
open GlobalTheory.UnifDifferential GlobalTheory.SqZero
noncomputable section
open GlobalTheory GlobalTheory.KaScale
variable {K : Type} [Field K] {P : Out.PolAV (Sp K)} {hg rig hr th hth v hv th' hth' v' hv'}
namespace GlobalTheory.KaScale
theorem _root_.solution : ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K) (M : Matrix (Fin P.g) (Fin P.g) K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (s : Fin P.g → LB.Sec (pw P.L (n : ℤ))) (κ : Kˣ), admitted P.g n l l' al → (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (M i) v (v' i)) → KaVal ⟨P, hg, rig, hr, th, hth, v, hv⟩ n l l' al s κ → ∃ κ' : Kˣ, KaVal ⟨P, hg, rig, hr, th', hth', v', hv'⟩ n l l' al s κ' ∧ a ^ (8 * kaExp P.g n l l') * (κ' : K) = M.det ^ (4 * kaExp P.g n l l') * κ := by
  intro K _ P hg rig hr th hth v hv th' hth' v' hv' a M n l l' al s κ hadm hth₀ hM hκ
  have ha : a ≠ 0 := by
    rintro rfl
    obtain ⟨y, -, hy⟩ := hth' (IsLocalRing.closedPoint K)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    rw [hth₀, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  have : IsCommMonObj P.A := P.isAb.comm
  have hdet : IsUnit M.det := ((LieComb.lieComb_algebra K P.A P.g v hv.1).2.2.2.2 M v' hv hM).1 hv'
  lift a to Kˣ using ha.isUnit
  obtain ⟨D, hD⟩ := hdet
  obtain ⟨z, ch, b, b', t, t', J, lam, lam', ⟨e₁, e₂, e₃, e₄, e₅⟩, hJ, hb, hb', ht, ht', rfl⟩ := hκ
  refine ⟨_, ⟨z, ch, b, b', t, t', J * D ^ (P.g.factorial * n ^ P.g),
    fun j => lam j * a ^ (8 * (l - j * n) ^ (4 * P.g + 2)),
    fun j => lam' j * a ^ (8 * (l' - j * n) ^ (4 * P.g + 2)), ⟨e₁, e₂, fun k => ?_, e₄, e₅⟩, ?_,
    fun j hj => ⟨(hb j hj).1, isSquareDetComparison_scale_sec a hth₀ _ _ _ _ (hb j hj).2⟩,
    fun j hj => ⟨(hb' j hj).1, isSquareDetComparison_scale_sec a hth₀ _ _ _ _ (hb' j hj).2⟩, ht, ht', rfl⟩, ?_⟩
  · rw [jac_scale (th := th) (hth := hth) (hv := hv) M hM, ← hD]
    exact (e₃ k).mul D.isUnit
  · rw [Units.val_mul, hJ, Units.val_pow_eq_pow_val, hD]
    simp only [jac_scale (th := th) (hth := hth) (hv := hv) (th' := th') (hth' := hth') (hv' := hv') M hM]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · have key := kaForm_homogeneous K P.g n l l' t t' J 1 a 1 lam lam' (fun _ => 1) (fun _ => 1)
      hadm.2.1 hadm.2.2.1
    simp only [one_zpow, one_pow, _root_.mul_one, Finset.prod_const_one] at key
    rw [← hD]
    norm_cast
    rw [← key]
    unfold kaForm kaExp
    generalize tComb P.g n l _ t _ = X
    generalize tComb P.g n l' _ t' _ = X'
    generalize degProd P.g n l l' ^ (3 * P.g + 2) = N
    generalize P.g.factorial * n ^ P.g = F
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ← natCast_zsmul]
    push_cast [Nat.cast_sub hadm.2.2.1.le]
    module
end GlobalTheory.KaScale
