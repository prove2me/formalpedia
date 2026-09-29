-- Prove2me | solution 1 for ModularCurve.MultCovering.mem_of_eq_sum_smul_goodFamily
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/aba31584-7e37-5f8b-a913-195d6432a0c3

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_mem_of_eq_sum_smul_goodFamily

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_mem_of_eq_sum_smul_goodFamily.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_mem_of_eq_sum_smul_goodFamily.ModularCurve.MultCovering"

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar jqModC modularFunctionFieldC transcendental_jqModC"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "ssPolyBar FamCtx jBar mAnnuli ChartCtx infChart chart ssValue"
namespace GaussAux
p2m_open "ModularCurve.MultCovering ModularCurve"

theorem aeval_jBar_injective (K : Type) [Field K] :
    Function.Injective (Polynomial.aeval (R := K) (jBar K)) := by
  intro q₁ q₂ h
  have hinj := transcendental_iff_injective.mp (ModularCurve.transcendental_jqModC K)
  apply hinj
  have h1 : ∀ q : Polynomial K, Polynomial.aeval (jqModC K) q
      = (((Polynomial.aeval (jBar K) q : ↥(modularFunctionFieldC K 1))) : LaurentSeries K) := by
    intro q
    rw [show jqModC K = (IntermediateField.val (modularFunctionFieldC K 1)) (jBar K) from rfl,
      Polynomial.aeval_algHom_apply]
    rfl
  show Polynomial.aeval (jqModC K) q₁ = Polynomial.aeval (jqModC K) q₂
  rw [h1, h1, h]

section LI
variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]

set_option synthInstance.maxHeartbeats 1600000 in

theorem aeval_prod_X_sub_C_eq_ssPolyBar (Γ : ChartCtx p A) :
    Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A))
        (∏ e : Fin (mAnnuli p), (Polynomial.X - Polynomial.C (ssValue Γ e))) = ssPolyBar Γ := by
  rw [map_prod]
  unfold ssPolyBar
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem linearIndependent_residue_t (Γ : ChartCtx p A) (hA : A.LiesOverPrime p) {r : ℕ} (Ψ : FamCtx p r)
    (hint : ∀ l, Ψ.t l ∈ (infChart Γ).integers) :
    LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l => (infChart Γ).residue ⟨Ψ.t l, hint l⟩) := by
  classical
  obtain ⟨hint', h0res, P, hP, hPind, -⟩ := Ψ.t_inf A hA Γ
  have h0 : ∀ l : Fin r, (l : ℕ) = 0 → (infChart Γ).residue ⟨Ψ.t l, hint l⟩ = 1 := fun l hl => h0res l hl
  have h1 : ∀ l : Fin r, 1 ≤ (l : ℕ) →
      (infChart Γ).residue ⟨Ψ.t l, hint l⟩ = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l) :=
    fun l hl => (hP l hl).2
  rw [Fintype.linearIndependent_iff]
  intro g hg

  set S : Polynomial (IsLocalRing.ResidueField ↥A) := ∏ e : Fin (mAnnuli p), (Polynomial.X - Polynomial.C (ssValue Γ e)) with hS
  set T : Polynomial (IsLocalRing.ResidueField ↥A) := ∑ l ∈ Finset.univ.filter (fun l : Fin r => 1 ≤ (l : ℕ)), g l • P l with hT
  set g0 : IsLocalRing.ResidueField ↥A := ∑ l ∈ Finset.univ.filter (fun l : Fin r => (l : ℕ) = 0), g l with hg0
  have hfilt : Finset.univ.filter (fun l : Fin r => ¬ (l : ℕ) = 0) = Finset.univ.filter (fun l : Fin r => 1 ≤ (l : ℕ)) := by
    ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  have hsum : ∑ l, g l • (infChart Γ).residue ⟨Ψ.t l, hint l⟩
      = Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (Polynomial.C g0 + S * T) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l : Fin r => (l : ℕ) = 0)]
    have hA' : ∑ l ∈ Finset.univ.filter (fun l : Fin r => (l : ℕ) = 0), g l • (infChart Γ).residue ⟨Ψ.t l, hint l⟩
        = algebraMap (IsLocalRing.ResidueField ↥A) _ g0 := by
      rw [hg0, map_sum]
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [Finset.mem_filter] at hl
      rw [h0 l hl.2, Algebra.smul_def, mul_one]
    have hB' : ∑ l ∈ Finset.univ.filter (fun l : Fin r => ¬ (l : ℕ) = 0), g l • (infChart Γ).residue ⟨Ψ.t l, hint l⟩
        = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) T := by
      rw [hT, map_sum, Finset.mul_sum, hfilt]
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [Finset.mem_filter] at hl
      rw [h1 l hl.2, Polynomial.smul_eq_C_mul, map_mul, Polynomial.aeval_C, Algebra.smul_def]
      ring
    rw [hA', hB', map_add, Polynomial.aeval_C, map_mul, aeval_prod_X_sub_C_eq_ssPolyBar]
  rw [hsum] at hg
  have hQ : Polynomial.C g0 + S * T = 0 :=
    aeval_jBar_injective (IsLocalRing.ResidueField ↥A) (by rw [hg, map_zero])

  have hSmonic : S.Monic := by
    rw [hS]; exact Polynomial.monic_prod_of_monic _ _ fun e _ => Polynomial.monic_X_sub_C _
  have hSdeg : S.natDegree = mAnnuli p := by
    rw [hS, Polynomial.natDegree_prod_of_monic _ _ (fun e _ => Polynomial.monic_X_sub_C _)]
    simp
  have hT0 : T = 0 := by
    by_contra hT0
    have hTdeg : T.natDegree < mAnnuli p := by
      have hm : 0 < mAnnuli p := by

        by_contra hm0
        apply hT0
        rw [hT]
        refine Finset.sum_eq_zero fun l hl => ?_
        rw [Finset.mem_filter] at hl
        have := (hP l hl.2).1
        omega
      have hle : T.natDegree ≤ mAnnuli p - 1 := by
        rw [hT]
        refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun l hl => ?_
        rw [Finset.mem_filter] at hl
        exact (Polynomial.natDegree_smul_le _ _).trans (by have := (hP l hl.2).1; omega)
      omega
    have hST : (S * T).natDegree = mAnnuli p + T.natDegree := by rw [hSmonic.natDegree_mul' hT0, hSdeg]
    have h2 : (Polynomial.C g0 + S * T).natDegree = (S * T).natDegree := by
      apply Polynomial.natDegree_add_eq_right_of_natDegree_lt
      rw [Polynomial.natDegree_C, hST]; omega
    rw [hQ, Polynomial.natDegree_zero, hST] at h2
    omega

  have hg1 : ∀ l : Fin r, 1 ≤ (l : ℕ) → g l = 0 := by
    have hT' : ∑ l' : {l : Fin r // 1 ≤ (l : ℕ)}, g l' • P l' = 0 := by
      rw [← hT0, hT]
      exact (Finset.sum_subtype (Finset.univ.filter (fun l : Fin r => 1 ≤ (l : ℕ))) (fun l => by simp)
        (fun l => g l • P l)).symm
    have := Fintype.linearIndependent_iff.mp hPind (fun l' => g l') hT'
    intro l hl; exact this ⟨l, hl⟩

  have hg0' : g0 = 0 := by
    rw [hT0, mul_zero, add_zero, Polynomial.C_eq_zero] at hQ; exact hQ
  intro i
  by_cases hi : 1 ≤ (i : ℕ)
  · exact hg1 i hi
  · have hi0 : (i : ℕ) = 0 := by omega
    have hfi : Finset.univ.filter (fun l : Fin r => (l : ℕ) = 0) = {i} := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hl; exact Fin.ext (by omega)
      · intro hl; rw [hl]; exact hi0
    rw [hg0, hfi, Finset.sum_singleton] at hg0'
    exact hg0'

end LI

end ModularCurve.MultCovering.GaussAux

open ModularCurve.MultCovering.GaussAux in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    {r : ℕ} (Ψ : FamCtx p r) (c : Fin r → AlgebraicClosure ℚ) (x : ↥(modularFunctionFieldBar (1 * p)))
    (hx : x ∈ (infChart Γ).integers) (heq : x = ∑ j, c j • Ψ.t j) :
    ∀ j, c j ∈ A := by
  classical
  obtain ⟨hint, -⟩ := Ψ.t_inf A hA Γ
  have hLI := linearIndependent_residue_t Γ hA Ψ hint

  rcases Nat.eq_zero_or_pos r with hr | hr
  · intro j; exact absurd j.isLt (by omega)
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩

  obtain ⟨j₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun j => A.valuation (c j)) Finset.univ_nonempty
  by_cases hc0 : c j₀ = 0
  · intro j
    have h := hmax j (Finset.mem_univ _)
    rw [hc0, map_zero, le_zero_iff, map_eq_zero] at h
    rw [h]; exact zero_mem _
  have hv0 : A.valuation (c j₀) ≠ 0 := (map_ne_zero _).mpr hc0

  have hd : ∀ j, c j * (c j₀)⁻¹ ∈ A := by
    intro j
    rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
    calc A.valuation (c j) * (A.valuation (c j₀))⁻¹
        ≤ A.valuation (c j₀) * (A.valuation (c j₀))⁻¹ := mul_le_mul_left (hmax j (Finset.mem_univ _)) _
      _ = 1 := mul_inv_cancel₀ hv0
  by_cases hA0 : c j₀ ∈ A
  · intro j
    have := mul_mem (hd j) hA0
    rwa [inv_mul_cancel_right₀ hc0] at this

  exfalso
  have huA : (c j₀)⁻¹ ∈ A := by
    rcases A.mem_or_inv_mem (c j₀) with h | h
    · exact absurd h hA0
    · exact h
  have hu𝔪 : (⟨(c j₀)⁻¹, huA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    apply hA0
    rw [← A.valuation_le_one_iff]
    have h1 : A.valuation ((c j₀)⁻¹) = 1 := by
      have := A.valuation_unit hunit.unit
      rwa [IsUnit.unit_spec] at this
    rw [map_inv₀, inv_eq_one] at h1
    exact h1.le

  have huC : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (c j₀)⁻¹ ∈ (infChart Γ).integers :=
    ((infChart Γ).algebraMap_mem_iff _).2 huA
  have hdC : ∀ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (c j * (c j₀)⁻¹) ∈ (infChart Γ).integers :=
    fun j => ((infChart Γ).algebraMap_mem_iff _).2 (hd j)
  have hid : (⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (c j₀)⁻¹, huC⟩ : (infChart Γ).integers) * ⟨x, hx⟩
      = ∑ j, ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (c j * (c j₀)⁻¹), hdC j⟩ * ⟨Ψ.t j, hint j⟩ := by
    apply Subtype.ext
    push_cast
    rw [heq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
    push_cast
    ring
  have hres := congrArg (infChart Γ).residue hid
  rw [map_mul, map_sum, (infChart Γ).residue_algebraMap ⟨(c j₀)⁻¹, huA⟩,
    (IsLocalRing.residue_eq_zero_iff _).2 hu𝔪, map_zero, zero_mul] at hres
  have hsummand : ∀ j, (infChart Γ).residue (⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (c j * (c j₀)⁻¹), hdC j⟩ * ⟨Ψ.t j, hint j⟩)
      = (IsLocalRing.residue ↥A ⟨c j * (c j₀)⁻¹, hd j⟩) • (infChart Γ).residue ⟨Ψ.t j, hint j⟩ := by
    intro j
    rw [map_mul, Algebra.smul_def, ← (infChart Γ).residue_algebraMap ⟨c j * (c j₀)⁻¹, hd j⟩]
  have hrel : ∑ j, (IsLocalRing.residue ↥A ⟨c j * (c j₀)⁻¹, hd j⟩) • (infChart Γ).residue ⟨Ψ.t j, hint j⟩ = 0 := by
    rw [show ∑ j, (IsLocalRing.residue ↥A ⟨c j * (c j₀)⁻¹, hd j⟩) • (infChart Γ).residue ⟨Ψ.t j, hint j⟩
        = ∑ j, (infChart Γ).residue (⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (c j * (c j₀)⁻¹), hdC j⟩ * ⟨Ψ.t j, hint j⟩)
        from Finset.sum_congr rfl fun j _ => (hsummand j).symm]
    exact hres.symm
  have hcoef := Fintype.linearIndependent_iff.mp hLI _ hrel j₀
  have hone : (⟨c j₀ * (c j₀)⁻¹, hd j₀⟩ : ↥A) = 1 := Subtype.ext (mul_inv_cancel₀ hc0)
  rw [hone, map_one] at hcoef
  exact one_ne_zero hcoef

end S_ModularCurve_MultCovering_mem_of_eq_sum_smul_goodFamily
end P2MW
export P2MW.S_ModularCurve_MultCovering_mem_of_eq_sum_smul_goodFamily (solution)
