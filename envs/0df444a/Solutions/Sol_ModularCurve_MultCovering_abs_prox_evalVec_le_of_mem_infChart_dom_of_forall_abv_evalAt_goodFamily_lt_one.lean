-- Prove2me | solution 1 for ModularCurve.MultCovering.abs_prox_evalVec_le_of_mem_infChart_dom_of_forall_abv_evalAt_goodFamily_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/4d5cecaa-d808-58d2-9a5e-943218d55cc5

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringLink
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_AlgebraicCurve_exists_evalVec_eq_smul_mulVec_of_eq_sum_smul
import Theorems.Thm_AlgebraicCurve_prox_smul_smul
import Theorems.Thm_AlgebraicCurve_abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le
import Theorems.Thm_AlgebraicCurve_prox_eq_zero_of_far_of_chart
import Theorems.Thm_ModularCurve_MultCovering_linkMatrixInv_mul
import Theorems.Thm_ModularCurve_MultCovering_linkMatrix_mul_inv
import Theorems.Thm_ModularCurve_MultCovering_eq_sum_linkMatrix_smul_goodFamily
import Theorems.Thm_ModularCurve_MultCovering_linkBudget_spec
import Theorems.Thm_ModularCurve_MultCovering_goodFamily_zero_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_abs_prox_evalVec_le_of_mem_infChart_dom_of_forall_abv_evalAt_goodFamily_lt_one
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_abs_prox_evalVec_le_of_mem_infChart_dom_of_forall_abv_evalAt_goodFamily_lt_one.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_abs_prox_evalVec_le_of_mem_infChart_dom_of_forall_abv_evalAt_goodFamily_lt_one.ModularCurve.MultCovering"

namespace ModularCurve
p2m_export "ModularCurve" "IsEmbBasis modularFunctionFieldBar modularFunctionFieldC hasPrincipalDivisors_modularFunctionFieldBar_unconditional"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "modulusExp ChartCtx infChart chart FamCtx goodFamily linkMatrix linkMatrixInv linkBudget compConst compConst_eq linkMatrixInv_mul linkMatrix_mul_inv eq_sum_linkMatrix_smul_goodFamily linkBudget_spec goodFamily_zero_eq_one"
p2m_open "ModularCurve.MultCovering ModularCurve"
theorem minor_mulVec_D {K : Type*} [Field K] {r : ℕ} (M : Matrix (Fin r) (Fin r) K)
    (x y : Fin r → K) (i j : Fin r) :
    M.mulVec x i * M.mulVec y j - M.mulVec x j * M.mulVec y i
      = ∑ p : Fin r × Fin r, M i p.1 * M j p.2 * (x p.1 * y p.2 - x p.2 * y p.1) := by
  have hswap : ∑ p : Fin r × Fin r, M j p.1 * x p.1 * (M i p.2 * y p.2)
      = ∑ p : Fin r × Fin r, M j p.2 * x p.2 * (M i p.1 * y p.1) := by
    rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_product, Finset.sum_comm]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
  rw [hswap, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

end ModularCurve.MultCovering

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_abs_prox_evalVec_le_of_mem_infChart_dom_of_forall_abv_evalAt_goodFamily_lt_one.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_abs_prox_evalVec_le_of_mem_infChart_dom_of_forall_abv_evalAt_goodFamily_lt_one.ModularCurve.MultCovering"

theorem solution (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    {r : ℕ} (Φ : FamCtx p r) (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ)
    (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)

    (hint : ∀ i, goodFamily Φ i ∈ (infChart Γ).integers)
    (cQ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) → Fin r)
    (hrat : ∀ P ∈ (infChart Γ).dom, P.IsRational)
    (hratio : ∀ P ∈ (infChart Γ).dom, ∀ j, goodFamily Φ j * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹ ∈ (infChart Γ).integers)
    (hreg : ∀ P ∈ (infChart Γ).dom, ∀ j, goodFamily Φ j * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹ ∈ P.toValuationSubring)
    (hhasse : ∀ P ∈ (infChart Γ).dom, ∃ l : Fin r, 1 ≤ (l : ℕ) ∧
      μ (P.evalAt (goodFamily Φ l * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹)) = 1) :
    ∀ P ∈ (infChart Γ).dom, ∀ Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
      Q.IsRational →
      (∀ l : Fin r, 1 ≤ (l : ℕ) → goodFamily Φ l ∈ Q.toValuationSubring ∧ μ (Q.evalAt (goodFamily Φ l)) < 1) →
      (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
      |prox μ (evalVec s P) (evalVec s Q)| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
  classical
  intro P hP Q hQrat hsmall hnonprop
  have hp : p.Prime := Fact.out
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  obtain ⟨i', j', hij⟩ := hnonprop
  have hr : 0 < r := Fin.pos i'
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have ht0 : ∀ i, goodFamily Φ i ≠ 0 := (fun i => Φ.t_basis.1.ne_zero i)
  set t := goodFamily Φ with ht
  set M := linkMatrix Φ s hs with hM
  set Minv := linkMatrixInv Φ s hs with hMinv
  set B := linkBudget Φ s hs with hB
  have hPrat : P.IsRational := (hrat P hP)
  set cP : Fin r := cQ ((infChart Γ).placeMap P) with hcP

  set o : Fin r := ⟨0, hr⟩ with ho
  have hto : t o = 1 := goodFamily_zero_eq_one p Φ o rfl

  have htQ : ∀ i, t i ∈ Q.toValuationSubring := by
    intro i
    by_cases hi : 1 ≤ (i : ℕ)
    · exact (hsmall i hi).1
    · have : i = o := Fin.ext (by push_neg at hi; simp [ho]; omega)
      rw [this, hto]; exact one_mem _

  set x : Fin r → AlgebraicClosure ℚ := fun i => P.evalAt (t i * (t cP)⁻¹) with hx
  set y : Fin r → AlgebraicClosure ℚ := fun i => Q.evalAt (t i * (t o)⁻¹) with hy
  have hyeval : ∀ i, y i = Q.evalAt (t i) := fun i => by simp [hy, hto]

  obtain ⟨dP, hdP0, hdP⟩ := AlgebraicCurve.exists_evalVec_eq_smul_mulVec_of_eq_sum_smul hr s t hs0 ht0 M Minv
    (linkMatrixInv_mul Φ s hs) (linkMatrix_mul_inv Φ s hs) (eq_sum_linkMatrix_smul_goodFamily Φ s hs)
    P hPrat cP (hreg P hP)
  obtain ⟨dQ, hdQ0, hdQ⟩ := AlgebraicCurve.exists_evalVec_eq_smul_mulVec_of_eq_sum_smul hr s t hs0 ht0 M Minv
    (linkMatrixInv_mul Φ s hs) (linkMatrix_mul_inv Φ s hs) (eq_sum_linkMatrix_smul_goodFamily Φ s hs)
    Q hQrat o (fun j => by rw [hto, inv_one, mul_one]; exact htQ j)

  have hminor : ∀ i j, evalVec s P i * evalVec s Q j - evalVec s P j * evalVec s Q i
      = dP * dQ * (M.mulVec x i * M.mulVec y j - M.mulVec x j * M.mulVec y i) := by
    intro i j; rw [hdP, hdQ]; simp only [Pi.smul_apply, smul_eq_mul]; ring
  have hMm : M.mulVec x i' * M.mulVec y j' - M.mulVec x j' * M.mulVec y i' ≠ 0 := by
    intro h0; apply hij; exact sub_eq_zero.1 (by rw [hminor, h0, mul_zero])
  have hsupM : (⨆ q : Fin r × Fin r, μ (M.mulVec x q.1 * M.mulVec y q.2 - M.mulVec x q.2 * M.mulVec y q.1)) ≠ 0 :=
    ((μ.pos hMm).trans_le (le_ciSup (Finite.bddAbove_range
      (fun q : Fin r × Fin r => μ (M.mulVec x q.1 * M.mulVec y q.2 - M.mulVec x q.2 * M.mulVec y q.1))) (i', j'))).ne'
  have hrowminor : ∃ i j, x i * y j - x j * y i ≠ 0 := by
    by_contra hall; push_neg at hall; apply hMm
    rw [minor_mulVec_D]; exact Finset.sum_eq_zero fun q _ => by rw [hall q.1 q.2, mul_zero]
  obtain ⟨i1, j1, hm1⟩ := hrowminor
  have hsupxy : (⨆ q : Fin r × Fin r, μ (x q.1 * y q.2 - x q.2 * y q.1)) ≠ 0 :=
    ((μ.pos hm1).trans_le (le_ciSup (Finite.bddAbove_range
      (fun q : Fin r × Fin r => μ (x q.1 * y q.2 - x q.2 * y q.1))) (i1, j1))).ne'
  have htc0 : t cP ≠ 0 := ht0 cP
  have hx0 : x ≠ 0 := by
    intro h0; have := congrFun h0 cP
    simp only [hx, Pi.zero_apply] at this
    rw [mul_inv_cancel₀ htc0, Place.evalAt_one] at this
    exact one_ne_zero this
  have hy0 : y ≠ 0 := by
    intro h0; have := congrFun h0 o
    rw [hyeval, hto, Place.evalAt_one] at this
    exact one_ne_zero this

  set β : ℝ := (μ (p : AlgebraicClosure ℚ))⁻¹ ^ B with hβ
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0
  have hμp1 : μ (p : AlgebraicClosure ℚ) ≤ 1 := (hμA _).1 hpA
  have hβ1 : 1 ≤ β := one_le_pow₀ ((one_le_inv₀ hμp0).2 hμp1)
  have hlogβ : Real.log β = (B : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
    rw [hβ, Real.log_pow, Real.log_inv]
  have hentry : ∀ m : AlgebraicClosure ℚ, (p : AlgebraicClosure ℚ) ^ B * m ∈ A → μ m ≤ β := by
    intro m hm
    have h1 : μ ((p : AlgebraicClosure ℚ) ^ B * m) ≤ 1 := (hμA _).1 hm
    rw [map_mul, map_pow] at h1
    have hpB : 0 < μ (p : AlgebraicClosure ℚ) ^ B := pow_pos hμp0 _
    rw [hβ, inv_pow]
    calc μ m = (μ (p : AlgebraicClosure ℚ) ^ B * μ m) * (μ (p : AlgebraicClosure ℚ) ^ B)⁻¹ := by field_simp
      _ ≤ 1 * (μ (p : AlgebraicClosure ℚ) ^ B)⁻¹ := mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hpB.le)
      _ = (μ (p : AlgebraicClosure ℚ) ^ B)⁻¹ := one_mul _
  have hMβ : ∀ i j, μ (M i j) ≤ β := fun i j => hentry _ (linkBudget_spec Φ s hs A hA i j).1
  have hMβ' : ∀ i j, μ (Minv i j) ≤ β := fun i j => hentry _ (linkBudget_spec Φ s hs A hA i j).2

  have hprox1 : prox μ (evalVec s P) (evalVec s Q) = prox μ (M.mulVec x) (M.mulVec y) := by
    rw [hdP, hdQ]; exact AlgebraicCurve.prox_smul_smul μ _ _ hdP0 hdQ0 hsupM
  have hL := AlgebraicCurve.abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le μ hμ M Minv (linkMatrixInv_mul Φ s hs)
    β hβ1 hMβ hMβ' x y hx0 hy0 ⟨i1, j1, hm1⟩
  rw [hlogβ, ← hprox1] at hL

  obtain ⟨l, hl1, hxl⟩ := hhasse P hP
  have hxl' : μ (x l) = 1 := hxl
  have hxl0 : x l ≠ 0 := fun h0 => by rw [h0, map_zero] at hxl'; exact zero_ne_one hxl'

  have hxA : ∀ i, x i ∈ A := by
    intro i
    have hfib : ∀ w ∈ (infChart Γ).dom, (infChart Γ).placeMap w = (infChart Γ).placeMap P →
        t i * (t cP)⁻¹ ∈ w.toValuationSubring := by
      intro w hw hw'
      have := hreg w hw i
      rw [hw'] at this; exact this
    exact ((infChart Γ).pointwise P hP hPrat _ (hratio P hP i) hfib).2.1
  set x' : Fin r → AlgebraicClosure ℚ := (x l)⁻¹ • x with hx'
  have hx'l : x' l = 1 := by simp [hx', inv_mul_cancel₀ hxl0]
  have hx'le : ∀ i, μ (x' i) ≤ 1 := by
    intro i
    simp only [hx', Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, hxl', inv_one, one_mul]
    exact (hμA _).1 (hxA i)
  have hyo : y o = 1 := by rw [hyeval, hto, Place.evalAt_one]
  have hyl : μ (y l) < 1 := by rw [hyeval]; exact (hsmall l hl1).2
  have hzero : prox μ x' y = 0 :=
    AlgebraicCurve.prox_eq_zero_of_far_of_chart μ hμ x' y l o hx'l hyo hx'le hyl
  have hprox2 : prox μ x y = 0 := by
    have h1 : prox μ x' ((1 : AlgebraicClosure ℚ) • y) = prox μ x y :=
      AlgebraicCurve.prox_smul_smul μ x y (inv_ne_zero hxl0) one_ne_zero hsupxy
    rw [one_smul] at h1
    rw [← h1]; exact hzero
  rw [hprox2, sub_zero] at hL

  have hlam : 0 ≤ -Real.log (μ (p : AlgebraicClosure ℚ)) := by linarith [Real.log_nonpos hμp0.le hμp1]
  calc |prox μ (evalVec s P) (evalVec s Q)| ≤ 4 * ((B : ℝ) * -Real.log (μ (p : AlgebraicClosure ℚ))) := hL
    _ = (4 * (linkBudget Φ s hs : ℕ) : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by rw [hB]; push_cast; ring
    _ ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
        refine mul_le_mul_of_nonneg_right ?_ hlam
        rw [compConst_eq]
        have : (0 : ℝ) ≤ modulusExp := by positivity
        push_cast; linarith

end S_ModularCurve_MultCovering_abs_prox_evalVec_le_of_mem_infChart_dom_of_forall_abv_evalAt_goodFamily_lt_one
end P2MW
export P2MW.S_ModularCurve_MultCovering_abs_prox_evalVec_le_of_mem_infChart_dom_of_forall_abv_evalAt_goodFamily_lt_one (solution)
