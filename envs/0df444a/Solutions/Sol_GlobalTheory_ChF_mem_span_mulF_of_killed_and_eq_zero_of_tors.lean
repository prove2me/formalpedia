-- Prove2me | solution 1 for GlobalTheory.ChF.mem_span_mulF_of_killed_and_eq_zero_of_tors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:55:10.698538+00:00
-- url     : https://prove2.me/submissions/12f6b37a-9986-4794-a0ef-dc1b13495446

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemSupSpanXPowIffAndIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LinMulFAndCompAndSpanLeAndMemPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupSeriesSeparatedByTorsion
import Theorems.Thm_GlobalTheory_ChF_mem_sup_span_X_pow_iff_and_isAdicComplete
import Theorems.Thm_GlobalTheory_T_mulF_span_mul_le_and_mulF_pow_mem_ideal_pow
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.pderivEval_X
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
private theorem mem_span_of_killed {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) (N : ℕ)
    (h : ∀ q : QF F N, (∀ φ : QF F N →ₐ[R] R, φ q = 0) → q = 0) (f : PS R 1 d)
    (hf : ∀ φ, Killed F N φ → φ f = 0) : f ∈ Ideal.span (Set.range (mulF F N)) := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine h _ fun φ => ?_
  refine hf (φ.comp (Ideal.Quotient.mkₐ R _)) fun j => ?_
  have : Ideal.Quotient.mk (Ideal.span (Set.range (mulF F N))) (mulF F N j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)
  simp [this]
end GlobalTheory.ChF
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChF
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), FH p F.F → (∀ (k : ℕ) (f : PS O 1 d), (∀ φ, Killed F.F (p ^ k) φ → φ f = 0) → f ∈ Ideal.span (Set.range (mulF F.F (p ^ k)))) ∧ ∀ f : PS O 1 d, (∀ φ, Tors p F.F φ → φ f = 0) → f = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ hc d F hFH
  have h1 : ∀ (k : ℕ) (f : PS O 1 d), (∀ φ, Killed F.F (p ^ k) φ → φ f = 0) →
      f ∈ Ideal.span (Set.range (mulF F.F (p ^ k))) :=
    fun k f hf => mem_span_of_killed F.F (p ^ k) (hFH k).2.2 f hf
  refine ⟨h1, fun f hf => ?_⟩
  have hH := ((mem_sup_span_X_pow_iff_and_isAdicComplete O (Ideal.span {(p : O)}) (Fin 1 × Fin d)).2
    hc).toIsHausdorff
  refine hH.haus f fun k => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, sub_zero]
  refine Ideal.pow_le_pow_right (Nat.le_succ k) ?_
  refine (Ideal.span_le.2 ?_) (h1 k f fun φ hφ => hf φ ⟨k, hφ⟩)
  rintro _ ⟨j, rfl⟩
  exact (GlobalTheory.T.mulF_span_mul_le_and_mulF_pow_mem_ideal_pow O d F).2.2.2 p k j
end GlobalTheory.ChF
