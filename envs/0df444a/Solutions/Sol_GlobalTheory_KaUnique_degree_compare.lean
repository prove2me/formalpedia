-- Prove2me | solution 1 for GlobalTheory.KaUnique.degree_compare
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:06:47.670341+00:00
-- url     : https://prove2.me/submissions/a871ec79-e31f-4541-9360-317e18e6ba75

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
import Theorems.Thm_GlobalTheory_BoxDetUnique_isSquareDetComparison_eq_mul_det_pow_of_basis_change
import Theorems.Thm_GlobalTheory_KaUnique_comb_unique
import Theorems.Thm_GlobalTheory_KaUnique_exists_change
import Theorems.Thm_GlobalTheory_KaUnique_isCx_of_isMul
import Theorems.Thm_GlobalTheory_KaUnique_isMul_comb
import Theorems.Thm_GlobalTheory_KeyKa_torsSq_kosD_conj
import Theorems.Thm_GlobalTheory_KuennethOne_appLE_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_appLE
import Theorems.Thm_GlobalTheory_KuennethOne_rs_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_self
import Theorems.Thm_GlobalTheory_TorsionUnique_torsSq_unique
import Theorems.Thm_P2M_GlobalTheory_KaUnique_IsComb_mulVec__bb52f65ceb5b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.KuennethOne.appLE_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_appLE
attribute [local simp] GlobalTheory.KuennethOne.rs_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_self



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KaUnique
namespace GlobalTheory.KaUnique
theorem _root_.solution (hL : Out.Laws) {K : Type} [Field K] [CharZero K] (x : KeyIn K) {n l d : ℕ}
    {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ}
    (hal : ∀ m, (al m).transpose * al m = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (hl : x.P.g * n < l)
    {s : Fin x.P.g → RR x n} {z z' : Fin d → Pt x} {ch ch' : Fin d → x.P.L.ι} (hz : EtZ x s z ch) (hz' : EtZ x s z' ch')
    (σ : Equiv.Perm (Fin d)) (ga : Fin d → Kˣ)
    (hga : ∀ a (r : RR x (l - 0 * n)), valT (T := K) (z a).left (x.P.L.U (ch a)) (r.f (ch a)) =
      (ga a).val ^ (l - 0 * n) * valT (T := K) (z' (σ a)).left (x.P.L.U (ch' (σ a))) (r.f (ch' (σ a))))
    {b b' : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)} {t t' : Kˣ} {lam lam' : ℕ → Kˣ}
    (hb : ∀ j ≤ x.P.g, IsBasis x (b j) ∧ IsSquareDeterminantComparison x (l - j * n) (al (l - j * n)) (b j) (lam j))
    (hb' : ∀ j ≤ x.P.g, IsBasis x (b' j) ∧ IsSquareDeterminantComparison x (l - j * n) (al (l - j * n)) (b' j) (lam' j))
    (ht : KosVal x l s z ch b t) (ht' : KosVal x l s z' ch' b' t') :
    ∃ be : ℕ → Kˣ, t' = t * (∏ a, ga a) ^ (-2 * (l : ℤ)) * 1 ^ 2 *
        ∏ j ∈ Finset.range (x.P.g + 1), be j ^ (2 * (-1 : ℤ) ^ j * (x.P.g.choose j : ℤ)) ∧
      ∀ j ≤ x.P.g, lam' j = lam j * be j ^ (-8 * ((l - j * n) ^ (3 * x.P.g + 2) : ℕ) : ℤ) *
        1 ^ (8 * (l - j * n) ^ (4 * x.P.g + 2)) := by
  have hB : ∀ j, ∃ B : (Matrix (Fin ((l - j * n) ^ x.P.g)) (Fin ((l - j * n) ^ x.P.g)) K)ˣ, j ≤ x.P.g →
      ∀ k, IsComb x.P.A.hom x.P.L (fam x (b j)) (fun k' => B.val k' k) (fam x (b' j) k) := fun j => by
    by_cases hj : j ≤ x.P.g
    · obtain ⟨B, hB⟩ := exists_change (hb j hj).1 (hb' j hj).1
      exact ⟨B, fun _ => hB⟩
    · exact ⟨1, fun h => absurd h hj⟩
  choose B hB using hB
  obtain ⟨m, hm, ht⟩ := ht
  obtain ⟨m', hm', ht'⟩ := ht'
  let P : Matrix (Fin d) (Fin d) K := (Matrix.diagonal fun a => (ga a).val ^ (l - 0 * n)).submatrix id σ.symm
  have hP : P.det ^ 2 = (((∏ a, ga a) ^ (2 * l) : Kˣ) : K) := by
    simp only [P]
    rw [Matrix.det_permute', Matrix.det_diagonal, mul_pow, Finset.prod_pow, ← pow_mul]
    have : ((Equiv.Perm.sign σ.symm : ℤ) : K) ^ 2 = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ.symm) with h | h <;> simp [h]
    rw [this]
    simp [mul_comm]
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2
    ((isUnit_pow_iff two_ne_zero).1 (hP ▸ Units.isUnit _))
  obtain ⟨t'', h1, h2⟩ := GlobalTheory.KeyKa.torsSq_kosD_conj K x.P.g d (fun j => (l - j * n) ^ x.P.g) m m' _
    (fun j => Matrix.of fun a k => valT (T := K) (z' a).left (x.P.L.U (ch' a)) ((b' j k).f (ch' a))) B hPu.unit t
    (fun i j hj => by
      ext a k
      have e1 := IsComb.mulVec' (hB j hj.le) (isMul_comb hm' i j hj k)
      have e2 := IsComb.mulVec (isMul_comb hm i j hj) (hB (j + 1) hj k)
      exact congrFun (comb_unique (hb j hj.le).1 e1 e2) a)
    (by
      ext a k
      have e1 := (hB 0 (Nat.zero_le _) k).valT (z a).left (Over.w (z a)) (ch a) (hz.1 a)
      refine Eq.trans ?_ e1
      refine Eq.trans ?_ (hga a (b' 0 k)).symm
      rw [IsUnit.unit_spec, Matrix.mul_apply, Finset.sum_eq_single (σ a)]
      · simp [P]
      · intro a' _ h
        have : a ≠ σ.symm a' := fun e => h (by rw [e, Equiv.apply_symm_apply])
        simp [P, Matrix.diagonal_apply_ne _ this]
      · intro h; exact absurd (Finset.mem_univ _) h)
    (isCx_of_isMul hm (fun j hj => (hb j hj).1) hz) ht
  have h3 : t'' = t' := Units.ext (GlobalTheory.TorsionUnique.torsSq_unique K _ _ _ _ _
    (isCx_of_isMul hm' (fun j hj => (hb' j hj).1) hz') h1 ht').1
  subst h3
  have h4 : Matrix.GeneralLinearGroup.det hPu.unit ^ 2 = (∏ a, ga a) ^ (2 * l) := Units.ext hP
  refine ⟨fun j => Matrix.GeneralLinearGroup.det (B j), ?_, fun j hj => ?_⟩
  · rw [h4] at h2
    rw [one_pow, _root_.mul_one, mul_right_comm, ← h2, neg_mul, zpow_neg]
    have : (∏ a, ga a) ^ (2 * (l : ℤ)) = (∏ a, ga a) ^ (2 * l) := by
      rw [← zpow_natCast]; push_cast; rfl
    rw [this, mul_inv_cancel_right]
  · rw [one_pow, _root_.mul_one]
    have hpos : l - j * n ≠ 0 := by
      have : j * n ≤ x.P.g * n := Nat.mul_le_mul_right _ hj
      omega
    exact GlobalTheory.BoxDetUnique.isSquareDetComparison_eq_mul_det_pow_of_basis_change hL K x (l - j * n) _ (b j) (b' j) (B j) _ _ (Nat.cast_ne_zero.2 hpos) (hal _) (hb j hj).1
      (hB j hj) (hb j hj).2 (hb' j hj).2
end GlobalTheory.KaUnique
