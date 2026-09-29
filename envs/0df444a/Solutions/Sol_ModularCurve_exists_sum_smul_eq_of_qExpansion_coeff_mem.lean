-- Prove2me | solution 1 for ModularCurve.exists_sum_smul_eq_of_qExpansion_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/83376f24-0803-54ed-8171-7dc0aa4472aa

import Mathlib
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gamma1
import Theorems.Thm_PowerSeries_exists_sum_smul_eq_of_forall_coeff_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_sum_smul_eq_of_qExpansion_coeff_mem
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite"

set_option autoImplicit false

open scoped MatrixGroups ModularForm

namespace SPLIT

open UpperHalfPlane

abbrev Γ1 (N : ℕ) : Subgroup (GL (Fin 2) ℝ) := ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods {N : ℕ} : (1 : ℝ) ∈ (Γ1 N).strictPeriods := by simp [Γ1]

variable {N : ℕ} {k : ℤ}

theorem qExpansion_coe_smul (c : ℂ) (G : ModularForm (Γ1 N) k) :
    qExpansion 1 (⇑(c • G) : ℍ → ℂ) = c • qExpansion 1 (⇑G : ℍ → ℂ) := by
  rw [ModularForm.IsGLPos.coe_smul]; exact ModularForm.qExpansion_smul one_pos one_mem_strictPeriods c G

theorem qExpansion_coe_sum {n : ℕ} (c : Fin n → ℂ) (G : Fin n → ModularForm (Γ1 N) k) :
    qExpansion 1 (⇑(∑ i, c i • G i) : ℍ → ℂ) = ∑ i, c i • qExpansion 1 (⇑(G i) : ℍ → ℂ) := by
  classical
  have key : ∀ s : Finset (Fin n), qExpansion 1 (⇑(∑ i ∈ s, c i • G i) : ℍ → ℂ) = ∑ i ∈ s, c i • qExpansion 1 (⇑(G i) : ℍ → ℂ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, ModularForm.coe_zero, qExpansion_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add,
        ModularForm.qExpansion_add one_pos one_mem_strictPeriods (c a • G a) (∑ i ∈ s, c i • G i), ih, qExpansion_coe_smul]
  exact key Finset.univ

theorem coe_sum {n : ℕ} (c : Fin n → ℂ) (G : Fin n → ModularForm (Γ1 N) k) :
    (⇑(∑ i, c i • G i) : ℍ → ℂ) = ∑ i, c i • (⇑(G i) : ℍ → ℂ) := by
  rw [show (⇑(∑ i, c i • G i) : ℍ → ℂ) = FunLike.coeAddMonoidHom (ModularForm _ k) ℍ ℂ (∑ i, c i • G i) from rfl, map_sum]
  rfl

end SPLIT

open SPLIT UpperHalfPlane in
open scoped MatrixGroups ModularForm in
theorem solution
    (N : ℕ) [NeZero N] {k : ℤ} (K₀ : IntermediateField ℚ ℂ)
    (F : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hF : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (⇑F : UpperHalfPlane → ℂ)).coeff n ∈ K₀) :
    ∃ (n : ℕ) (c : Fin n → ℂ)
      (G : Fin n → ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k)
      (r : Fin n → PowerSeries ℤ),
      (∀ i, c i ∈ K₀) ∧ (∀ i, ModularCurve.IsIntegralQExp (G i) (r i)) ∧
      (⇑F : UpperHalfPlane → ℂ) = ∑ i, c i • (⇑(G i) : UpperHalfPlane → ℂ) := by
  classical
  obtain ⟨n, c, G, r, hG, hsum⟩ := ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1 N F
  let g : Fin n → PowerSeries ℂ := fun i => (r i).map (Int.castRingHom ℂ)
  have hgq : ∀ i, g i = qExpansion 1 (⇑(G i) : UpperHalfPlane → ℂ) := fun i => hG i
  have hg : ∀ (i : Fin n) (m : ℕ), (g i).coeff m ∈ K₀.toSubfield := by
    intro i m
    simp only [g, PowerSeries.coeff_map, eq_intCast]
    exact intCast_mem _ _

  have hF' : F = ∑ i, c i • G i := DFunLike.coe_injective (by
    show (⇑F : UpperHalfPlane → ℂ) = ⇑(∑ i, c i • G i); rw [hsum, coe_sum])
  have hqF : qExpansion 1 (⇑F : UpperHalfPlane → ℂ) = ∑ i, c i • g i := by
    rw [hF', qExpansion_coe_sum]; simp only [hgq]
  have hcoef : ∀ m : ℕ, (∑ i, c i • g i).coeff m ∈ K₀.toSubfield := fun m => by rw [← hqF]; exact hF m
  obtain ⟨c', hc', heq⟩ := PowerSeries.exists_sum_smul_eq_of_forall_coeff_mem K₀.toSubfield g hg c hcoef
  refine ⟨n, c', G, r, fun i => hc' i, hG, ?_⟩

  have hq : qExpansion 1 (⇑(∑ i, c' i • G i) : UpperHalfPlane → ℂ) = qExpansion 1 (⇑F : UpperHalfPlane → ℂ) := by
    rw [qExpansion_coe_sum, hqF, ← heq]; simp only [hgq]
  have hform : (∑ i, c' i • G i) = F := by
    have h0 : qExpansion 1 (⇑((∑ i, c' i • G i) - F) : UpperHalfPlane → ℂ) = 0 := by
      rw [ModularForm.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods (∑ i, c' i • G i) F, hq, sub_self]
    exact sub_eq_zero.mp ((ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods _).mp h0)
  rw [← hform, coe_sum]

end S_ModularCurve_exists_sum_smul_eq_of_qExpansion_coeff_mem
end P2MW
export P2MW.S_ModularCurve_exists_sum_smul_eq_of_qExpansion_coeff_mem (solution)
