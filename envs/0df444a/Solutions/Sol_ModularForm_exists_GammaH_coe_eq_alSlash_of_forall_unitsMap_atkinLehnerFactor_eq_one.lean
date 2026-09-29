-- Prove2me | solution 1 for ModularForm.exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d5a98a53-ab56-54d7-81ca-9b15849e9fab

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Theorems.Thm_ModularForm_AtkinLehnerDatum_exists_mem_Gamma0_alGL_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm Pointwise
open CongruenceSubgroup CohCarrier

namespace AlFactorHMod

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

abbrev Γ (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Subgroup (GL (Fin 2) ℝ) :=
  ((GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem mem_GammaH_of_unitsMap_mul_eq_one {Q : ℕ} (hQ : Q ∣ M)
    (hHQ : ∀ u : (ZMod M)ˣ, ZMod.unitsMap hQ u = 1 → u ∈ H)
    {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 M) {u : (ZMod M)ˣ} (hu : u ∈ H)
    (h : ZMod.unitsMap hQ (gamma0Units M ⟨δ, hδ⟩ * u) = 1) :
    δ ∈ GammaH M H := by
  rw [mem_GammaH_iff]
  refine ⟨hδ, ?_⟩
  have hker : gamma0Units M ⟨δ, hδ⟩ * u ∈ H := hHQ _ h
  simpa using H.mul_mem hker (H.inv_mem hu)

section AL

variable {Q : ℕ}

theorem Q_dvd (W : ModularForm.AtkinLehnerDatum M Q) : Q ∣ M := Dvd.intro W.R W.hM.symm

variable [NeZero M] (W : ModularForm.AtkinLehnerDatum M Q)

lemma mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

theorem exists_alGL_mul_eq_factor {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 M ∧
      W.alGL * Matrix.SpecialLinearGroup.mapGL ℝ γ = Matrix.SpecialLinearGroup.mapGL ℝ δ * W.alGL ∧
      (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod Q) * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod Q)
        = 1 := by
  obtain ⟨δ, hδ, hW⟩ := ModularForm.AtkinLehnerDatum.exists_mem_Gamma0_alGL_mul_eq W hγ
  refine ⟨δ, hδ, hW, ?_⟩

  have h01 := congrArg (fun A : GL (Fin 2) ℝ => (A : Matrix (Fin 2) (Fin 2) ℝ) 0 1) hW
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ModularForm.AtkinLehnerDatum.alGL_coe,
    mapGL_coe_eq, Matrix.map_apply, ModularForm.AtkinLehnerDatum.mat] at h01
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, eq_intCast] at h01
  have hZ : (Q : ℤ) * W.a * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + W.b * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
      = (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * W.b + (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (Q : ℤ) := by
    exact_mod_cast h01

  have hdet : (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
      - (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe δ
    rw [Matrix.det_fin_two] at this
    linear_combination this
  have hMδ : (M : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have := Gamma0_mem.mp hδ
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hQδ : (Q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (Int.natCast_dvd_natCast.mpr (Q_dvd W)).trans hMδ
  obtain ⟨s, hs⟩ := hQδ

  have hb : ((W.b : ℤ) : ZMod Q) * (-((W.R : ℕ) : ZMod Q)) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod Q)) W.bezout
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, zero_sub,
      Int.cast_one] at h
    linear_combination h
  have h1 : ((W.b : ℤ) : ZMod Q) * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod Q)
      = ((W.b : ℤ) : ZMod Q) * ((((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ)) : ZMod Q) := by
    have h := congrArg (fun z : ℤ => (z : ZMod Q)) hZ
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, zero_add,
      mul_zero, add_zero] at h
    linear_combination h
  have h2 : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod Q) = (((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod Q) := by
    have := congrArg (fun z : ZMod Q => (-((W.R : ℕ) : ZMod Q)) * z) h1
    simp only [← mul_assoc] at this
    rwa [mul_comm (-((W.R : ℕ) : ZMod Q)), hb, one_mul, one_mul] at this
  have h3 : (((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod Q) * (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod Q) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod Q)) hdet
    rw [hs] at h
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, mul_zero,
      sub_zero, Int.cast_one] at h
    exact h
  rw [h2, mul_comm]
  exact h3

theorem le_conj_alGL (hHQ : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Q_dvd W) u = 1 → u ∈ H) :
    Γ M H ≤ ConjAct.toConjAct W.alGL⁻¹ • Γ M H := by
  rintro x ⟨γ, hγ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  obtain ⟨hγ0, hγH⟩ := mem_GammaH_iff.mp hγ
  obtain ⟨δ, hδ, hW, hcong⟩ := exists_alGL_mul_eq_factor W hγ0
  refine ⟨δ, ?_, ?_⟩
  · refine mem_GammaH_of_unitsMap_mul_eq_one (Q_dvd W) hHQ hδ hγH ?_
    ext
    rw [ZMod.unitsMap_val, Units.val_mul, val_gamma0Units, val_gamma0Units, Units.val_one]
    show ((((((δ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) * (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M)).cast : ZMod Q)) = 1
    rw [ZMod.cast_mul (Q_dvd W), ZMod.cast_intCast (Q_dvd W), ZMod.cast_intCast (Q_dvd W)]
    exact hcong
  · show (Matrix.SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ)
      = W.alGL * Matrix.SpecialLinearGroup.mapGL ℝ γ * W.alGL⁻¹
    rw [hW, mul_inv_cancel_right]

end AL

section Forms

variable {k : ℤ}

def restrictMod {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (h : Γ₂ ≤ Γ₁) (f : ModularForm Γ₁ k) :
    ModularForm Γ₂ k where
  toFun := f
  slash_action_eq' A hA := SlashInvariantFormClass.slash_action_eq f A (h hA)
  holo' := f.holo'
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps f (hc.mono h)

@[scoped simp] theorem coe_restrictMod {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (h : Γ₂ ≤ Γ₁) (f : ModularForm Γ₁ k) :
    ⇑(restrictMod h f) = ⇑f := rfl

def slashMod {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (g : GL (Fin 2) ℝ)
    (hg : Γ₂ ≤ ConjAct.toConjAct g⁻¹ • Γ₁) (f : ModularForm Γ₁ k) : ModularForm Γ₂ k :=
  restrictMod hg (ModularForm.translate f g)

@[scoped simp] theorem coe_slashMod {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (g : GL (Fin 2) ℝ)
    (hg : Γ₂ ≤ ConjAct.toConjAct g⁻¹ • Γ₁) (f : ModularForm Γ₁ k) :
    ⇑(slashMod g hg f) = ⇑f ∣[k] g := rfl

end Forms

end AlFactorHMod
p2m_reactivate "P2MW.S_ModularForm_exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one.AlFactorHMod"

end
p2m_reactivate "P2MW.S_ModularForm_exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one.AlFactorHMod"

theorem solution
    {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) (H : Subgroup (ZMod M)ˣ)
    (hHq : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro W.R W.hM.symm) u = 1 → u ∈ H)
    (k : ℤ) (f : ModularForm (CohCarrier.GammaH M H) k) :
    ∃ X : ModularForm (CohCarrier.GammaH M H) k, ⇑X = ModularForm.alSlash W k ⇑f :=
  ⟨AlFactorHMod.slashMod W.alGL (AlFactorHMod.le_conj_alGL W hHq) f, rfl⟩

#print axioms solution

end S_ModularForm_exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one
end P2MW
export P2MW.S_ModularForm_exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one (solution)
