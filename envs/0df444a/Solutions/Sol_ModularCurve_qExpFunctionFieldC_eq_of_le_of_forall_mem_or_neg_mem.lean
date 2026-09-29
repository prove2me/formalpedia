-- Prove2me | solution 1 for ModularCurve.qExpFunctionFieldC_eq_of_le_of_forall_mem_or_neg_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/2fa2a641-080f-5eaa-aacd-6b8046f90c7e

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpFunctionFieldC_eq_of_le_of_forall_mem_or_neg_mem

set_option autoImplicit false

namespace QExpFieldPM

open scoped MatrixGroups ModularForm
open Matrix.SpecialLinearGroup UpperHalfPlane ModularForm

theorem slash_neg_of_even {m : ℤ} (hm : Even m) (F : ℍ → ℂ) (g : GL (Fin 2) ℝ) :
    F ∣[m] (-g) = F ∣[m] g := by
  ext τ
  rw [ModularForm.slash_apply, ModularForm.slash_apply, σ_neg, UpperHalfPlane.neg_smul, denom_neg,
    (Even.neg hm).neg_zpow]
  congr 2
  simp [Units.val_neg, Matrix.det_neg]

theorem mapGL_neg (A : SL(2, ℤ)) : (mapGL ℝ) (-A) = -((mapGL ℝ) A) := by
  refine Units.ext ?_
  rw [Units.val_neg, mapGL_coe_matrix, mapGL_coe_matrix]
  have : (map (algebraMap ℤ ℝ)) (-A) = -((map (algebraMap ℤ ℝ)) A) := by
    ext i j
    simp [Matrix.SpecialLinearGroup.coe_neg]
  rw [this, Matrix.SpecialLinearGroup.coe_neg]

theorem coe_le_adjoinNegOne {Γ Γ' : Subgroup SL(2, ℤ)} (hpm : ∀ γ ∈ Γ, γ ∈ Γ' ∨ -γ ∈ Γ') :
    (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ (Γ' : Subgroup (GL (Fin 2) ℝ)).adjoinNegOne := by
  rintro g ⟨A, hA, rfl⟩
  rw [Subgroup.mem_adjoinNegOne_iff]
  rcases hpm A hA with h | h
  · exact Or.inl ⟨A, h, rfl⟩
  · exact Or.inr ⟨-A, h, by rw [mapGL_neg]⟩

theorem isCusp_of_isCusp {Γ Γ' : Subgroup SL(2, ℤ)} (hpm : ∀ γ ∈ Γ, γ ∈ Γ' ∨ -γ ∈ Γ') {c : OnePoint ℝ}
    (hc : IsCusp c (Γ : Subgroup (GL (Fin 2) ℝ))) : IsCusp c (Γ' : Subgroup (GL (Fin 2) ℝ)) :=
  ((Γ' : Subgroup (GL (Fin 2) ℝ)).commensurable_adjoinNegOne_self).isCusp_iff.mp
    (hc.mono (coe_le_adjoinNegOne hpm))

noncomputable def liftEven {Γ Γ' : Subgroup SL(2, ℤ)} (hpm : ∀ γ ∈ Γ, γ ∈ Γ' ∨ -γ ∈ Γ') {m : ℤ} (hm : Even m)
    (F : ModularForm (Γ' : Subgroup (GL (Fin 2) ℝ)) m) : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) m where
  toFun := F
  slash_action_eq' := by
    rintro g ⟨A, hA, rfl⟩
    rcases hpm A hA with h | h
    · exact SlashInvariantForm.slash_action_eqn F _ ⟨A, h, rfl⟩
    · have hneg : (mapGL ℝ) A = -((mapGL ℝ) (-A)) := by rw [mapGL_neg, neg_neg]
      rw [hneg, slash_neg_of_even hm]
      exact SlashInvariantForm.slash_action_eqn F _ ⟨-A, h, rfl⟩
  holo' := F.holo'
  bdd_at_cusps' hc := F.bdd_at_cusps' (isCusp_of_isCusp hpm hc)

@[scoped simp] theorem coe_liftEven {Γ Γ' : Subgroup SL(2, ℤ)} (hpm : ∀ γ ∈ Γ, γ ∈ Γ' ∨ -γ ∈ Γ') {m : ℤ} (hm : Even m)
    (F : ModularForm (Γ' : Subgroup (GL (Fin 2) ℝ)) m) : ⇑(liftEven hpm hm F) = ⇑F := rfl

theorem isIntegralQExp_mul {Γ' : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ') {k : ℤ}
    (f g : ModularForm (Γ' : Subgroup (GL (Fin 2) ℝ)) k) {pf pg : PowerSeries ℤ}
    (hf : ModularCurve.IsIntegralQExp f pf) (hg : ModularCurve.IsIntegralQExp g pg) :
    ModularCurve.IsIntegralQExp (f.mul g) (pf * pg) := by
  unfold ModularCurve.IsIntegralQExp at hf hg ⊢
  have h1 : (1 : ℝ) ∈ (Γ' : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
    exact AddSubgroup.mem_zmultiples _
  rw [map_mul, hf, hg, ModularForm.qExpansion_mul one_pos h1]

end QExpFieldPM
p2m_reactivate "P2MW.S_ModularCurve_qExpFunctionFieldC_eq_of_le_of_forall_mem_or_neg_mem.QExpFieldPM"

open scoped MatrixGroups
open QExpFieldPM

theorem solution
    (K : Type*) [Field K] {Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} (hle : Γ' ≤ Γ)
    (hT : ModularGroup.T ∈ Γ') (hpm : ∀ γ ∈ Γ, γ ∈ Γ' ∨ -γ ∈ Γ') :
    ModularCurve.qExpFunctionFieldC K Γ' = ModularCurve.qExpFunctionFieldC K Γ := by
  refine le_antisymm ?_ (ModularCurve.qExpFunctionFieldC_mono K hle)
  rw [ModularCurve.qExpFunctionFieldC, IntermediateField.adjoin_le_iff]
  rintro x ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
  have hk : Even (k + k) := ⟨k, rfl⟩
  have hF := isIntegralQExp_mul hT f g hf hg
  have hG := isIntegralQExp_mul hT g g hg hg
  have hF' : ModularCurve.IsIntegralQExp (liftEven (Γ := Γ) hpm hk (f.mul g)) (pf * pg) := hF
  have hG' : ModularCurve.IsIntegralQExp (liftEven (Γ := Γ) hpm hk (g.mul g)) (pg * pg) := hG
  have hne : ModularCurve.intSeriesC K (pg * pg) ≠ 0 := by
    rw [ModularCurve.intSeriesC_mul]
    exact mul_ne_zero hg0 hg0
  have heq : ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K pg =
      ModularCurve.intSeriesC K (pf * pg) / ModularCurve.intSeriesC K (pg * pg) := by
    rw [ModularCurve.intSeriesC_mul, ModularCurve.intSeriesC_mul, mul_div_mul_right _ _ hg0]
  rw [heq]
  exact ModularCurve.div_mem_qExpFunctionFieldC _ _ hF' hG' hne

end S_ModularCurve_qExpFunctionFieldC_eq_of_le_of_forall_mem_or_neg_mem
end P2MW
export P2MW.S_ModularCurve_qExpFunctionFieldC_eq_of_le_of_forall_mem_or_neg_mem (solution)
