-- Prove2me | solution 1 for GlobalTheory.ChF.lin_mulF_and_comp_and_span_le_and_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:22:14.895451+00:00
-- url     : https://prove2.me/submissions/33c190c8-4ea0-4b3f-ba8b-beee36e9055c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MulFConstAndMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvRegaugedSecondLawFamily
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LinMulFAndCompAndSpanLeAndMemPow
import Theorems.Thm_GlobalTheory_FormalMul_constantCoeff_mulF
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_germIdeal_eq_span
import Theorems.Thm_GlobalTheory_mem_germIdeal_pow_iff
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_zero__bb72846b09b6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_addOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_evP_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_ev_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_hasSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_pair_points_zero_constant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h3
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
attribute [local simp] GlobalTheory.pderivEval_X
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChF
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.Regauge
variable {R : Type} [CommRing R] {d : ℕ}
private theorem gp_mulF (F : FGLaw R d) (N : ℕ) : GP (mulF F.F N) :=
  FormalMul.constantCoeff_mulF F.F F.const N
private theorem nsum_add (F : FGLaw R d) (a b : ℕ) :
    mulF F.F (a + b) = addOf F.F (mulF F.F a) (mulF F.F b) := by
  induction b with
  | zero => exact (addOf_zero F (gp_mulF F a)).symm
  | succ b ih =>
    change addOf F.F (mulF F.F (a + b)) (pt R d 0) = addOf F.F _ (addOf F.F (mulF F.F b) (pt R d 0))
    rw [ih, addOf_assoc F (gp_mulF F a) (gp_mulF F b) (gp_pt 0)]
private theorem nsum_mul (F : FGLaw R d) (N M : ℕ) :
    mulF F.F (N * M) = comp1 (mulF F.F N) (mulF F.F M) := by
  have hV := single_point_zero_constant (gp_mulF F M)
  induction N with
  | zero =>
    rw [Nat.zero_mul]
    exact (evP_zero _ hV).symm
  | succ N ih =>
    rw [Nat.succ_mul, nsum_add, ih]
    change _ = evP ![mulF F.F M] (addOf F.F (mulF F.F N) (pt R d 0))
    rw [evP_addOf _ hV _ _ _ (gp_mulF F N) (gp_pt 0), evP_pt _ hV]
    rfl
private theorem ev_mem_pow {m n : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j, GP (a j))
    {K : Ideal (PS R n d)} (hK : ∀ j i, a j i ∈ K) {N : ℕ} {f : PS R m d}
    (hf : f ∈ germIdeal (Fin m × Fin d) R ^ N) : ev a f ∈ K ^ N := by
  have h : (germIdeal (Fin m × Fin d) R ^ N).map (substAlgHom (R := R) (gt_hasSubst a ha)) ≤ K ^ N := by
    rw [Ideal.map_pow, germIdeal_eq_span]
    refine Ideal.pow_right_mono ?_ N
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    rw [substAlgHom_X]
    exact hK _ _
  have := h (Ideal.mem_map_of_mem _ hf)
  rwa [substAlgHom_apply] at this
private theorem mem_sq_iff {σ : Type} [Finite σ] {g : MvPowerSeries σ R} :
    g ∈ germIdeal σ R ^ 2 ↔ constantCoeff g = 0 ∧ ∀ s, coeff (Finsupp.single s 1) g = 0 := by
  rw [mem_germIdeal_pow_iff]
  constructor
  · intro h
    exact ⟨by simpa using h 0 (by simp), fun s => h _ (by simp)⟩
  · rintro ⟨h0, h1⟩ e he
    rcases (by omega : e.degree = 0 ∨ e.degree = 1) with h | h
    · obtain rfl := (Finsupp.degree_eq_zero_iff e).1 h
      simpa using h0
    · obtain ⟨s, rfl⟩ : e ∈ Set.range (fun s : σ => Finsupp.single s 1) := by
        rw [Finsupp.range_single_one]; exact h
      exact h1 s
private theorem coeff_single_X' {σ : Type} [DecidableEq σ] (s t : σ) :
    coeff (Finsupp.single s 1) (X t : MvPowerSeries σ R) = if s = t then 1 else 0 := by
  rw [coeff_X]
  simp [Finsupp.single_left_inj]
private theorem sub_lin_mem {σ : Type} [Fintype σ] {g : MvPowerSeries σ R} (hg : constantCoeff g = 0) :
    g - ∑ s, coeff (Finsupp.single s 1) g • X s ∈ germIdeal σ R ^ 2 := by
  classical
  refine mem_sq_iff.2 ⟨by simp [hg], fun s => ?_⟩
  simp [coeff_single_X']
private theorem ev_sub_lin_mem {m n : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j, GP (a j))
    {f : PS R m d} (hf : constantCoeff f = 0) :
    ev a f - ∑ s : Fin m × Fin d, coeff (Finsupp.single s 1) f • a s.1 s.2 ∈
      germIdeal (Fin n × Fin d) R ^ 2 := by
  have h := ev_mem_pow ha (K := germIdeal (Fin n × Fin d) R) (fun j i => ha j i) (sub_lin_mem hf)
  unfold ev at h ⊢
  rw [← substAlgHom_apply (gt_hasSubst a ha)] at h ⊢
  simpa only [map_sub, map_sum, map_smul, substAlgHom_X] using h
private theorem coeff_law (F : FGLaw R d) (i : Fin d) (l : Fin 2) (j : Fin d) :
    coeff (Finsupp.single (l, j) 1) (F.F i) = if j = i then 1 else 0 := by
  have hp : GP (pt R (n := 1) d 0) := gp_pt 0
  fin_cases l
  · have h := (mem_sq_iff.1 (ev_sub_lin_mem (pair_points_zero_constant hp gp_zero₂) (F.const i))).2 (0, j)
    have e : ev ![pt R (n := 1) d 0, 0] (F.F i) = X (0, i) := congrFun (addOf_zero F hp) i
    rw [e] at h
    simp [Fintype.sum_prod_type, pt, coeff_single_X', sub_eq_zero] at h
    simpa using h.symm
  · have h := (mem_sq_iff.1 (ev_sub_lin_mem (pair_points_zero_constant gp_zero₂ hp) (F.const i))).2 (0, j)
    rw [F.unit i] at h
    simp [Fintype.sum_prod_type, pt, coeff_single_X', sub_eq_zero] at h
    simpa using h.symm
private theorem nsum_sub_mem (F : FGLaw R d) (N : ℕ) (i : Fin d) :
    mulF F.F N i - (N : R) • X (0, i) ∈ germIdeal (Fin 1 × Fin d) R ^ 2 := by
  induction N with
  | zero => simp [mulF]
  | succ N ih =>
    have h := ev_sub_lin_mem (pair_points_zero_constant (gp_mulF F N) (gp_pt 0)) (F.const i)
    simp only [Fintype.sum_prod_type, coeff_law, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    convert add_mem h ih using 1
    change ev ![mulF F.F N, pt R d 0] (F.F i) - _ = _
    simp only [pt, Nat.cast_succ, add_smul, one_smul]
    abel
private theorem lin_nsum (F : FGLaw R d) (N : ℕ) :
    lin (mulF F.F N) = (N : R) • (1 : Matrix (Fin d) (Fin d) R) := by
  ext i j
  have h := (mem_sq_iff.1 (nsum_sub_mem F N i)).2 (0, j)
  rw [map_sub, sub_eq_zero, map_smul, coeff_single_X'] at h
  simp [lin, h, Matrix.one_apply, eq_comm]
private theorem span_nsum_le (F : FGLaw R d) (N M : ℕ) :
    Ideal.span (Set.range (mulF F.F (N * M))) ≤ Ideal.span (Set.range (mulF F.F M)) := by
  rw [Ideal.span_le, nsum_mul]
  rintro _ ⟨j, rfl⟩
  have := ev_mem_pow (single_point_zero_constant (gp_mulF F M)) (K := Ideal.span (Set.range (mulF F.F M))) (N := 1)
    (f := mulF F.F N j) (fun l i => by fin_cases l; exact Ideal.subset_span ⟨i, rfl⟩)
    (by rw [pow_one]; exact gp_mulF F N j)
  rwa [pow_one] at this
private theorem nsum_pow_mem (F : FGLaw R d) (p k : ℕ) (j : Fin d) :
    mulF F.F (p ^ k) j ∈ ((Ideal.span {(p : R)}).map (C : R →+* PS R 1 d) ⊔
      Ideal.span (Set.range (X : Fin 1 × Fin d → PS R 1 d))) ^ (k + 1) := by
  set J := (Ideal.span {(p : R)}).map (C : R →+* PS R 1 d) ⊔
      Ideal.span (Set.range (X : Fin 1 × Fin d → PS R 1 d)) with hJ
  induction k generalizing j with
  | zero =>
    rw [zero_add, pow_one, hJ, ← germIdeal_eq_span]
    exact Ideal.mem_sup_right (gp_mulF F _ j)
  | succ k ih =>
    have hV := single_point_zero_constant (gp_mulF F (p ^ k))
    have h := ev_mem_pow hV (K := J ^ (k + 1)) (fun l i => by fin_cases l; exact ih i)
      (nsum_sub_mem F p j)
    rw [← pow_mul, gt_ev_sub _ hV, smul_eq_C_mul, gt_ev_mul _ hV, gt_ev_X _ hV] at h
    have h1 := Ideal.pow_le_pow_right (show k + 1 + 1 ≤ (k + 1) * 2 by omega) h
    have hC : ev ![mulF F.F (p ^ k)] (C (p : R) : PS R 1 d) = C (p : R) := subst_C _
    have h2 : C (p : R) * mulF F.F (p ^ k) j ∈ J ^ (k + 1 + 1) := by
      rw [pow_succ' J (k + 1)]
      exact Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_map_of_mem _
        (Ideal.subset_span rfl))) (ih j)
    rw [hC] at h1
    have h3 := add_mem h1 h2
    rw [pow_succ' p k, nsum_mul]
    simpa [comp1] using h3
end
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
end GlobalTheory.ChF
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ChF
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d), (∀ N : ℕ, lin (mulF F.F N) = (N : R) • (1 : Matrix (Fin d) (Fin d) R)) ∧ (∀ N M : ℕ, mulF F.F (N * M) = comp1 (mulF F.F N) (mulF F.F M)) ∧ (∀ N M : ℕ, Ideal.span (Set.range (mulF F.F (N * M))) ≤ Ideal.span (Set.range (mulF F.F M))) ∧ ∀ (p k : ℕ) (j : Fin d), mulF F.F (p ^ k) j ∈ ((Ideal.span {(p : R)}).map (MvPowerSeries.C : R →+* PS R 1 d) ⊔ Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS R 1 d))) ^ (k + 1) :=
  fun _ _ _ F => ⟨lin_nsum F, nsum_mul F, span_nsum_le F, nsum_pow_mem F⟩
end GlobalTheory.ChF
