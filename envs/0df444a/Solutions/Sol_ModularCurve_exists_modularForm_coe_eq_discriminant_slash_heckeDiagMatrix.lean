-- Prove2me | solution 1 for ModularCurve.exists_modularForm_coe_eq_discriminant_slash_heckeDiagMatrix
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/6b4aa443-51cb-5301-9f92-2f3466c4b4a7

import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Discriminant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_modularForm_coe_eq_discriminant_slash_heckeDiagMatrix
open scoped ModularForm
set_option Elab.async false
open scoped MatrixGroups Pointwise Manifold

namespace S09C0

private theorem exists_mapGL_mul_heckeDiagMatrix_eq (p : ℕ) [NeZero p] (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 p) :
    ∃ γ' : SL(2, ℤ),
      Matrix.SpecialLinearGroup.mapGL ℝ γ' * ModularForm.heckeDiagMatrix p
        = ModularForm.heckeDiagMatrix p * Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  have hp : p ≠ 0 := NeZero.ne p
  obtain ⟨c, hc⟩ : (p : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) p).mp
      (CongruenceSubgroup.Gamma0_mem.mp hγ)
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
      - (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  rw [hc] at hdet
  refine ⟨⟨!![(γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0, (p : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
      c, (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet
  · apply Units.ext
    simp only [Units.val_mul, ModularForm.val_heckeDiagMatrix hp,
      Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, hc] <;> ring

private theorem gamma0_le_conj (p : ℕ) [NeZero p] :
    (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ))
      ≤ ConjAct.toConjAct (ModularForm.heckeDiagMatrix p)⁻¹ • 𝒮ℒ := by
  rintro x ⟨γ, hγ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  obtain ⟨γ', hγ'⟩ := exists_mapGL_mul_heckeDiagMatrix_eq p γ hγ
  refine ⟨γ', ?_⟩
  rw [← hγ', mul_inv_cancel_right]

private noncomputable def deltaTranslate (p : ℕ) :
    ModularForm (ConjAct.toConjAct (ModularForm.heckeDiagMatrix p)⁻¹ • 𝒮ℒ) 12 :=
  ModularForm.translate CuspForm.discriminant (ModularForm.heckeDiagMatrix p)

private theorem coe_deltaTranslate (p : ℕ) :
    ⇑(deltaTranslate p) = ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix p := rfl

private theorem slash_eq_self (p : ℕ) [NeZero p] (γ : GL (Fin 2) ℝ)
    (hγ : γ ∈ (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ))) :
    (ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix p) ∣[(12 : ℤ)] γ
      = ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix p := by
  rw [← coe_deltaTranslate p]
  exact SlashInvariantFormClass.slash_action_eq (deltaTranslate p) γ (gamma0_le_conj p hγ)

private theorem _root_.S09C0.holo (p : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix p) := by
  rw [← coe_deltaTranslate p]
  exact ModularFormClass.holo (deltaTranslate p)

p2m_export "S09C0" "holo"
private theorem _root_.S09C0.bdd_at_cusps (p : ℕ) [NeZero p] {c : OnePoint ℝ}
    (hc : IsCusp c (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ))) :
    c.IsBoundedAt (ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix p) 12 := by
  rw [← coe_deltaTranslate p]
  exact ModularFormClass.bdd_at_cusps (deltaTranslate p) (hc.mono (gamma0_le_conj p))

p2m_export "S09C0" "bdd_at_cusps"

private noncomputable def deltaDiag (p : ℕ) [NeZero p] :
    ModularForm (CongruenceSubgroup.Gamma0 p) 12 where
  toFun := ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix p
  slash_action_eq' γ hγ := slash_eq_self p γ hγ
  holo' := holo p
  bdd_at_cusps' hc := bdd_at_cusps p hc

private theorem coe_deltaDiag (p : ℕ) [NeZero p] :
    ⇑(deltaDiag p) = ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix p := rfl

end S09C0

private theorem ModularCurve.exists_modularForm_coe_eq_discriminant_slash_heckeDiagMatrix (p : ℕ) [NeZero p] : ∃ D : ModularForm (CongruenceSubgroup.Gamma0 p) 12, ⇑D = ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix p := by
  exact ⟨S09C0.deltaDiag p, S09C0.coe_deltaDiag p⟩

theorem solution (p : ℕ) [NeZero p] : ∃ D : ModularForm (CongruenceSubgroup.Gamma0 p) 12, ⇑D = ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix p :=
  ModularCurve.exists_modularForm_coe_eq_discriminant_slash_heckeDiagMatrix p

end S_ModularCurve_exists_modularForm_coe_eq_discriminant_slash_heckeDiagMatrix
end P2MW
export P2MW.S_ModularCurve_exists_modularForm_coe_eq_discriminant_slash_heckeDiagMatrix (solution)
