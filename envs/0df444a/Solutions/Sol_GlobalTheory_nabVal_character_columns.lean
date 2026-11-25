-- Prove2me | solution 1 for GlobalTheory.nabVal_character_columns
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:30:13.824703+00:00
-- url     : https://prove2.me/submissions/8eb8f40f-f719-4725-9ba5-f7ea9dd35f92

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfSubMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NabValColumnsCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ConstantCoeffDmonOfEigen
import Theorems.Thm_GlobalTheory_CharacterColumns_nabVal_congr_dir
import Theorems.Thm_GlobalTheory_CharacterColumns_constantCoeff_dmonOf_eigen
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
open CharacterColumns
namespace GlobalTheory
theorem _root_.solution :
  (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 a c : O) (N m : ℕ) (I : Ideal R), star a * a = (N : O) * c → (N : R) ∈ I →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (α : ι → R), (∀ l, α l - 1 ∈ I) → (∀ l, IsUnit (α l)) →
    (∀ l, (dAct k B a).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α l) • (fun i => algebraMap R k (u l i))) →
    (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ χ : PS R 1 d, ∃ g : PS R 1 d, ∀ mo : ι →₀ ℕ, ∃ r ∈ I,
      B.nabVal k h w0 m (FB.toK k g) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial mo 1) =
        algebraMap R k (constantCoeff (DmonOf B.G.F u mo χ) + r)) →
  (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 : O) (N m n : ℕ) (I : Ideal R), (N : R) ∈ I → ∀ (a c : Fin n → O), (∀ b, star (a b) * a b = (N : O) * c b) →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (S : Fin n → Set ι) (α : Fin n → ι → R), (∀ b, ∀ l ∈ S b, α b l - 1 ∈ I ∧ IsUnit (α b l) ∧
      (dAct k B (a b)).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α b l) • (fun i => algebraMap R k (u l i))) →
    (∀ b, ∀ l ∈ S b, ∀ l' ∈ S b, dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c b * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ (χ : Fin n → PS R 1 d) (y : ι × Fin n → R), (∀ b, constantCoeff (χ b) = 1) → (∀ b, ∀ l ∈ S b, Dof B.G.F (u l) (χ b) = C (y (l, b)) * χ b) →
    ∀ P : MvPolynomial (ι × Fin n) R, (∀ mo ∈ P.support, ∀ l b, mo (l, b) ≠ 0 → l ∈ S b) →
    ∃ g : Fin n → PS R 1 d, ∃ r ∈ I, ∑ mo ∈ P.support, algebraMap R k (P.coeff mo) *
      ∏ b, B.nabVal k h w0 m (FB.toK k (g b)) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial (colM mo b) 1) =
        algebraMap R k (MvPolynomial.eval y P + r)) := by
  intro COL R _ d O _ _ k _ _ _ B h hh hinj w0 N m n I hN a c hac ι _ u S α hα hβ χ y h1 hχ P hP
  classical
  have hcol : ∀ b, ∃ g : PS R 1 d, ∀ mo : ι →₀ ℕ, (∀ l, mo l ≠ 0 → l ∈ S b) → ∃ s : R,
      s - ∏ l, y (l, b) ^ mo l ∈ I ∧
      B.nabVal k h w0 m (FB.toK k g) (fun l i => algebraMap R k (u l i))
        (MvPolynomial.monomial mo 1) = algebraMap R k s := by
    intro b
    have hz : (fun i => algebraMap R k ((0 : Fin d → R) i)) = 0 := by
      funext i; simp
    obtain ⟨g, hg⟩ := COL R d O k B h hh hinj w0 (a b) (c b) N m I (hac b) hN ι ((S b).indicator u)
      (fun l => if l ∈ S b then α b l else 1)
      (by
        intro l
        by_cases hl : l ∈ S b
        · rw [if_pos hl]; exact (hα b l hl).1
        · rw [if_neg hl, sub_self]; exact I.zero_mem)
      (by
        intro l
        by_cases hl : l ∈ S b
        · rw [if_pos hl]; exact (hα b l hl).2.1
        · rw [if_neg hl]; exact isUnit_one)
      (by
        intro l
        by_cases hl : l ∈ S b
        · rw [if_pos hl, Set.indicator_of_mem hl]; exact (hα b l hl).2.2
        · rw [Set.indicator_of_notMem hl, hz, Matrix.mulVec_zero, smul_zero])
      (by
        intro l l'
        by_cases hl : l ∈ S b
        · by_cases hl' : l' ∈ S b
          · rw [Set.indicator_of_mem hl, Set.indicator_of_mem hl']; exact hβ b l hl l' hl'
          · rw [Set.indicator_of_notMem hl', hz, Matrix.mulVec_zero, Matrix.mulVec_zero,
              dotProduct_zero]
            exact zero_mem _
        · rw [Set.indicator_of_notMem hl, hz, zero_dotProduct]
          exact zero_mem _)
      (χ b)
    refine ⟨g, fun mo hmo => ?_⟩
    obtain ⟨r, hr, e⟩ := hg mo
    refine ⟨∏ l, y (l, b) ^ mo l + r, by rwa [add_sub_cancel_left], ?_⟩
    rw [constantCoeff_dmonOf_eigen B.G.F u (S b) (χ b) (fun l => y (l, b)) (h1 b) (hχ b) mo hmo] at e
    rw [← e]
    refine nabVal_congr_dir B h w0 m _ _ _ mo fun l hl => ?_
    rw [Set.indicator_of_mem (hmo l hl)]
  choose g hg using hcol
  have hs : ∀ (mo : ι × Fin n →₀ ℕ) (b : Fin n), ∃ s : R, mo ∈ P.support →
      s - ∏ l, y (l, b) ^ mo (l, b) ∈ I ∧
      B.nabVal k h w0 m (FB.toK k (g b)) (fun l i => algebraMap R k (u l i))
        (MvPolynomial.monomial (colM mo b) 1) = algebraMap R k s := by
    intro mo b
    by_cases hmo : mo ∈ P.support
    · obtain ⟨s, hs⟩ := hg b (colM mo b) (fun l hl => hP mo hmo l b hl)
      exact ⟨s, fun _ => hs⟩
    · exact ⟨0, fun h' => absurd h' hmo⟩
  choose s hs using hs
  refine ⟨g, ∑ mo ∈ P.support, P.coeff mo * ∏ b, s mo b - MvPolynomial.eval y P, ?_, ?_⟩
  · rw [MvPolynomial.eval_eq', ← Finset.sum_sub_distrib]
    refine I.sum_mem fun mo hmo => ?_
    rw [← mul_sub]
    refine I.mul_mem_left _ ?_
    rw [Fintype.prod_prod_type_right, ← Ideal.Quotient.eq, map_prod, map_prod]
    exact Finset.prod_congr rfl fun b _ => Ideal.Quotient.eq.2 (hs mo b hmo).1
  · rw [add_sub_cancel, map_sum]
    refine Finset.sum_congr rfl fun mo hmo => ?_
    rw [map_mul, map_prod]
    congr 1
    exact Finset.prod_congr rfl fun b _ => (hs mo b hmo).2
end GlobalTheory
