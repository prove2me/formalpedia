-- Prove2me | solution 1 for ModPForms.heckeV_mem_modPMod_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/d32e41e3-2e55-511b-91e3-4921354e9fb7

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_ModularForm_rescaleSlash_slash_eq_self_of_mem_Gamma0
import Theorems.Thm_ModularForm_mdifferentiable_slash_heckeDiagMatrix
import Theorems.Thm_ModularFormClass_isBoundedAt_slash_ratCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_heckeV_mem_modPMod_mul
p2m_attr_erase "simp" "FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat"

set_option autoImplicit false

open scoped MatrixGroups ModularForm

namespace FltWs24
namespace VOp

theorem T_mem_Gamma0 (N : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := by
  simp [CongruenceSubgroup.Gamma0_mem, ModularGroup.coe_T]

theorem one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma0 N)]
  exact AddSubgroup.mem_zmultiples 1

theorem Gamma0_le_of_dvd {N M : ℕ} (h : N ∣ M) :
    CongruenceSubgroup.Gamma0 M ≤ CongruenceSubgroup.Gamma0 N := by
  intro A hA
  rw [CongruenceSubgroup.Gamma0_mem] at hA ⊢
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hA ⊢
  exact dvd_trans (Int.natCast_dvd_natCast.mpr h) hA

theorem Gamma0GL_le_of_dvd {N M : ℕ} (h : N ∣ M) :
    ((CongruenceSubgroup.Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (Gamma0_le_of_dvd h)

theorem map_ratDiag_eq_heckeDiagMatrix {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ)
      (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(ℓ : ℚ), 0; 0, 1]
        (by rw [Matrix.det_fin_two_of]; simp [hℓ])) = ModularForm.heckeDiagMatrix ℓ := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, ModularForm.val_heckeDiagMatrix hℓ]
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]

noncomputable def vOp {N : ℕ} [NeZero N] (k : ℤ) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) :
    ModularForm (CongruenceSubgroup.Gamma0 (N * ℓ)) k :=
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) hℓ⟩
  ((ℓ : ℂ) ^ (1 - k)) •
  ({ toFun := ⇑f ∣[k] ModularForm.heckeDiagMatrix ℓ
     slash_action_eq' := fun γ hγ =>
       ModularForm.rescaleSlash_slash_eq_self_of_mem_Gamma0 (R := N) (M := N * ℓ) (d := ℓ)
         (by rw [mul_comm]) k (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
     holo' := ModularForm.mdifferentiable_slash_heckeDiagMatrix ℓ k (ModularFormClass.holo f)
     bdd_at_cusps' := fun {c} hc => by
       have hc' := IsCusp.mono (Gamma0GL_le_of_dvd (dvd_mul_right N ℓ)) hc
       have h := ModularFormClass.isBoundedAt_slash_ratCast f
         (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(ℓ : ℚ), 0; 0, 1]
           (by rw [Matrix.det_fin_two_of]; simp [hℓ])) hc'
       rwa [map_ratDiag_eq_heckeDiagMatrix hℓ] at h } : ModularForm (CongruenceSubgroup.Gamma0 (N * ℓ)) k)

theorem coe_vOp {N : ℕ} [NeZero N] (k : ℤ) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) :
    ⇑(vOp k hℓ f) = fun τ => f (ModularForm.heckeDiagMatrix ℓ • τ) := by
  funext τ
  unfold vOp
  rw [ModularForm.IsGLPos.coe_smul, Pi.smul_apply, smul_eq_mul]
  change (ℓ : ℂ) ^ (1 - k) * (⇑f ∣[k] ModularForm.heckeDiagMatrix ℓ) τ = _
  rw [ModularForm.slash_heckeDiagMatrix_apply k hℓ, ← mul_assoc, ← zpow_add₀ (by exact_mod_cast hℓ),
    show (1 - k + (k - 1) : ℤ) = 0 by ring, zpow_zero, one_mul]

theorem vOp_intCoeff {N : ℕ} [NeZero N] (k : ℤ) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (F : Type) [Field F]
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (c : ℕ → ℤ) (hc : ∀ n, ModularFormClass.qCoeff f n = (c n : ℂ)) :
    (∀ n, ModularFormClass.qCoeff (vOp k hℓ f) n = ((if ℓ ∣ n then c (n / ℓ) else 0 : ℤ) : ℂ)) ∧
    PowerSeries.heckeV ℓ (PowerSeries.mk fun n => ((c n : ℤ) : F)) =
      PowerSeries.mk fun n => (((if ℓ ∣ n then c (n / ℓ) else 0 : ℤ) : ℤ) : F) := by
  refine ⟨fun n => ?_, ?_⟩
  · rw [coe_vOp, ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul f (one_mem_strictPeriods_Gamma0 N) hℓ n]
    split_ifs <;> simp [hc]
  · ext n
    rw [PowerSeries.coeff_heckeV, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    split_ifs <;> simp

end FltWs24.VOp

open FltWs24.VOp in
theorem solution (N : ℕ) [NeZero N] (k : ℤ) (ℓ : ℕ) (hℓ : ℓ ≠ 0)
    (F : Type) [Field F] (φ : PowerSeries F) (hφ : φ ∈ ModPForms.modPMod N k F) :
    PowerSeries.heckeV ℓ φ ∈ ModPForms.modPMod (N * ℓ) k F := by
  unfold ModPForms.modPMod at hφ ⊢
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, c, hc, rfl⟩ := hx
    obtain ⟨he, hps⟩ := vOp_intCoeff k hℓ F f c hc
    rw [hps]
    exact Submodule.subset_span ⟨vOp k hℓ f, _, he, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

end S_ModPForms_heckeV_mem_modPMod_mul
end P2MW
export P2MW.S_ModPForms_heckeV_mem_modPMod_mul (solution)
