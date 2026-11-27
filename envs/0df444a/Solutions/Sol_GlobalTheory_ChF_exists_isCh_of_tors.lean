-- Prove2me | solution 1 for GlobalTheory.ChF.exists_isCh_of_tors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:23:35.322891+00:00
-- url     : https://prove2.me/submissions/c2133ca2-046c-40f0-9f0c-7fce6a84e762

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemSupSpanXPowIffAndIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalDiscPointsValuationIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CharacterOnTorsionPointsEqSeriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LinMulFAndCompAndSpanLeAndMemPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PointsAddCommMonoidStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupSeriesSeparatedByTorsionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqZeroOfForallPairPointsValuationIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIsChOfTors
import Theorems.Thm_GlobalTheory_ChF_mem_sup_span_X_pow_iff_and_isAdicComplete
import Theorems.Thm_GlobalTheory_T_eq_zero_of_forall_pair_points_valuationIntegers
import Theorems.Thm_GlobalTheory_T_exists_addCommMonoid_algHom_powerSeries_fgLaw
import Theorems.Thm_GlobalTheory_T_exists_series_eq_character_on_torsion
import Theorems.Thm_GlobalTheory_T_formalDisc_points_valuationIntegers
import Theorems.Thm_GlobalTheory_T_formalGroup_series_separated_by_torsion
import Theorems.Thm_GlobalTheory_T_mulF_span_mul_le_and_mulF_pow_mem_ideal_pow
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_const
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
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
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
private theorem apply_eq_zero_of_killed {R : Type} [CommRing R] {d : ℕ} {F : Fin d → PS R 2 d} {N : ℕ}
    {φ : PS R 1 d →ₐ[R] R} (h : Killed F N φ) {f : PS R 1 d}
    (hf : f ∈ Ideal.span (Set.range (mulF F N))) : φ f = 0 := by
  have hle : Ideal.span (Set.range (mulF F N)) ≤ RingHom.ker φ := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact h j
  exact hle hf
private theorem killed_pow_mono {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) (p : ℕ) {m n : ℕ}
    (hmn : m ≤ n) {φ : PS R 1 d →ₐ[R] R} (h : Killed F.F (p ^ m) φ) : Killed F.F (p ^ n) φ := by
  intro j
  apply apply_eq_zero_of_killed h
  have hn : p ^ n = p ^ (n - m) * p ^ m := by rw [← pow_add, Nat.sub_add_cancel hmn]
  rw [hn]
  exact (GlobalTheory.T.mulF_span_mul_le_and_mulF_pow_mem_ideal_pow R d F).2.2.1 _ _ (Ideal.subset_span ⟨j, rfl⟩)
private theorem addOf_pt {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) :
    addOf F (pt R (n := 2) d 0) (pt R (n := 2) d 1) = F := by
  funext i
  unfold addOf ev
  have h : (fun q : Fin 2 × Fin d => (![pt R (n := 2) d 0, pt R (n := 2) d 1] : Fin 2 → Pt R 2 d) q.1 q.2)
      = MvPowerSeries.X := by
    funext ⟨a, b⟩
    fin_cases a <;> rfl
  rw [h, MvPowerSeries.subst_self]
  rfl
private theorem hasSubst_law {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) :
    MvPowerSeries.HasSubst (fun q : Fin 1 × Fin d => (![F.F] : Fin 1 → Pt R 2 d) q.1 q.2) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  rintro ⟨a, b⟩
  fin_cases a
  exact F.const b
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
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), FH p F.F → ∀ (κ : (PS O 1 d →ₐ[O] O) → C), (∀ φ φ' ψ, Tors p F.F φ → Tors p F.F φ' → IsSum F.F φ φ' ψ → κ ψ = κ φ * κ φ') → (∀ φ, (∀ f, φ f = MvPowerSeries.constantCoeff f) → κ φ = 1) → ∃ u : PS O 1 d, IsCh F.F u ∧ ∀ φ, Tors p F.F φ → algebraMap O C (φ u) = κ φ := by
  intro p _ C _ _ _ v O _ _ hv _ _ d F hFH κ hmul hone
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  choose w hw using fun k : ℕ => GlobalTheory.T.exists_series_eq_character_on_torsion p C v O hv d F hFH k κ
    (fun φ φ' ψ h h' hs => hmul φ φ' ψ ⟨k, h⟩ ⟨k, h'⟩ hs) hone
  obtain ⟨hsep, hsepT⟩ := GlobalTheory.T.formalGroup_series_separated_by_torsion p C v O hv d F hFH
  have hsame : ∀ {m n : ℕ}, m ≤ n → ∀ φ, Killed F.F (p ^ m) φ → φ (w m) = φ (w n) := by
    intro m n hmn φ h
    apply hinj
    rw [hw m φ h, hw n φ (killed_pow_mono F p hmn h)]
  set J : Ideal (PS O 1 d) := (Ideal.span {(p : O)}).map (MvPowerSeries.C : O →+* PS O 1 d) ⊔
    Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS O 1 d)) with hJ
  have hcomp : IsAdicComplete J (PS O 1 d) :=
    (mem_sup_span_X_pow_iff_and_isAdicComplete O (Ideal.span {(p : O)}) (Fin 1 × Fin d)).2 inferInstance
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → w m ≡ w n [SMOD (J ^ m • ⊤ : Submodule (PS O 1 d) (PS O 1 d))] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    have h1 := hsep m (w m - w n) (fun φ h => by rw [map_sub, hsame hmn φ h, sub_self])
    have h2 : Ideal.span (Set.range (mulF F.F (p ^ m))) ≤ J ^ (m + 1) := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact (GlobalTheory.T.mulF_span_mul_le_and_mulF_pow_mem_ideal_pow O d F).2.2.2 p m j
    exact Ideal.pow_le_pow_right (Nat.le_succ m) (h2 h1)
  obtain ⟨u, hu⟩ := hcomp.toIsPrecomplete.prec hcauchy
  have hval : ∀ φ, Tors p F.F φ → algebraMap O C (φ u) = κ φ := by
    rintro φ ⟨k, hk⟩
    rw [← hw k φ hk]
    congr 1
    have hH : IsHausdorff (Ideal.span {(p : O)}) O := inferInstance
    rw [← sub_eq_zero]
    apply hH.haus
    intro n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    obtain ⟨N, hN⟩ := (GlobalTheory.T.formalDisc_points_valuationIntegers p C v O hv (Fin 1 × Fin d)).2.2 φ n
    have h1 := hu (max N k)
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
    have h2 := hN _ (Ideal.pow_le_pow_right (le_max_left N k) h1)
    rw [map_sub, ← hsame (le_max_right N k) φ hk] at h2
    rw [← neg_sub]
    exact neg_mem h2
  obtain ⟨inst, hsum, hzero, hkill⟩ := GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw p C v O hv d F
  refine ⟨u, ⟨?_, ?_⟩, hval⟩
  · apply hinj
    rw [← hzero u, hval _ ⟨0, (hkill _ _).1 (smul_zero _)⟩, hone _ hzero, map_one]
  · rw [addOf_pt, ← sub_eq_zero]
    apply GlobalTheory.T.eq_zero_of_forall_pair_points_valuationIntegers p C v O hv d (Tors p F.F) hsepT
    intro Φ φ φ' h0 h1 hφ hφ'
    let ψ : PS O 1 d →ₐ[O] O := Φ.comp (MvPowerSeries.substAlgHom (hasSubst_law F))
    have hψ : ∀ f, Φ (ev (n := 2) ![F.F] f) = ψ f := by
      intro f
      simp only [ψ, AlgHom.comp_apply, MvPowerSeries.coe_substAlgHom]
      rfl
    have hs : IsSum F.F φ φ' ψ := ⟨Φ, h0, h1, hψ⟩
    have hT : Tors p F.F ψ := by
      obtain ⟨k, hk⟩ := hφ
      obtain ⟨k', hk'⟩ := hφ'
      refine ⟨max k k', (hkill _ _).1 ?_⟩
      rw [(hsum _ _ _).1 hs, smul_add, (hkill _ _).2 (killed_pow_mono F p (le_max_left k k') hk),
        (hkill _ _).2 (killed_pow_mono F p (le_max_right k k') hk'), add_zero]
    apply hinj
    rw [map_sub, map_mul, hψ, h0, h1, map_sub, map_mul, hval _ hT, hval _ hφ, hval _ hφ',
      hmul _ _ _ hφ hφ' hs, sub_self, map_zero]
end GlobalTheory.ChF
