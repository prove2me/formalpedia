-- Prove2me | solution 1 for GlobalTheory.nabVal_columns_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:45:17.48463+00:00
-- url     : https://prove2.me/submissions/0ca96036-f2d6-4b94-8f94-506c29f419ed

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvariantDerivAlongEndo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGroupedOfSublist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfSubMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NabValPullbackMonomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NabValColumnsCongr
import Theorems.Thm_GlobalTheory_ColumnValue_column_value
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory
open ColumnValue
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (w0 a : O) (N m : ℕ) (w : PS R 1 d), FB.toK k w = FB.expS k (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0) → ∀ (I : Ideal R) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (α : ι → R), (∀ l, α l ∈ I) → (∀ l, (dAct k B a).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α l) • (fun i => algebraMap R k (u l i))) → (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B w0).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) → ∀ (n : ℕ) (f : Fin n → PS R 1 d) (y : ι × Fin n → R), (∀ l b mo, coeff mo (Dof B.G.F (u l) (f b) - C (y (l, b)) * f b) ∈ I) → ∀ P : MvPolynomial (ι × Fin n) R, ∃ r ∈ I, ∑ mo ∈ P.support, algebraMap R k (P.coeff mo) * ∏ b, B.nabVal k h w0 (N * m) (FB.toK k (f b * w ^ m)) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial (colM mo b) 1) = algebraMap R k (MvPolynomial.eval y P * ∏ b, constantCoeff (f b) + r) := by
  intro R _ d O _ _ k _ _ _ B h hh w0 a N m w hw I ι _ u α hI hα hβ n f y hf P
  choose s hs he using fun (mo : ι × Fin n →₀ ℕ) (b : Fin n) =>
    column_value B h hh w0 a N m w hw I u α hI hα hβ (f b) (fun l => y (l, b)) (fun l => hf l b) (colM mo b)
  refine ⟨∑ mo ∈ P.support, P.coeff mo * ∏ b, s mo b -
    MvPolynomial.eval y P * ∏ b, constantCoeff (f b), ?_, ?_⟩
  · rw [MvPolynomial.eval_eq', Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine I.sum_mem fun mo _ => ?_
    rw [mul_assoc, ← mul_sub]
    refine I.mul_mem_left _ ?_
    rw [Fintype.prod_prod_type_right, ← Finset.prod_mul_distrib, ← Ideal.Quotient.eq, map_prod, map_prod]
    exact Finset.prod_congr rfl fun b _ => Ideal.Quotient.eq.2 (hs mo b)
  · rw [add_sub_cancel]
    simp only [he]
    simp only [map_sum, map_mul, map_prod]
end GlobalTheory
