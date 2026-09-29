-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_smul_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/381a27d8-2c86-5f5b-9709-c4c783602974

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Theorems.Thm_ModularCurve_FullLevel_exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_smul_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace W1pRC

variable {q : ℕ} [Fact q.Prime] {M' : ℕ}

abbrev Γ (q M' : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  ((CohCarrier.GammaH (q ^ 2 * M') (levelH q M') : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

omit [Fact q.Prime] in
theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ q M').strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH _ _)]
  exact AddSubgroup.mem_zmultiples _

omit [Fact q.Prime] in

theorem exists_ratCast_of_isIntegralQExp {φ : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp φ p) (n : ℕ) :
    ∃ r : ℚ, (qExpansion 1 φ).coeff n = (r : ℂ) :=
  ⟨((PowerSeries.coeff n p : ℤ) : ℚ), by rw [← h.coeff n]; push_cast; rfl⟩

def res1 {k : ℤ} (g : ModularForm (Γ q M') k) :
    ModularForm ((Gamma1 (q ^ 2 * M') : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k :=
  restrictForm (Subgroup.map_mono (Gamma1_le_GammaH _ _)) g

omit [Fact q.Prime] in
@[scoped simp] theorem coe_res1 {k : ℤ} (g : ModularForm (Γ q M') k) : (⇑(res1 g) : ℍ → ℂ) = g := rfl

theorem exists_isIntegralQExp_smul [NeZero M'] {k : ℤ} (g : ModularForm (Γ q M') k)
    (hg : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 g).coeff n = (r : ℂ)) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ p : PowerSeries ℤ, IsIntegralQExp ((D : ℂ) • (⇑g : ℍ → ℂ)) p := by
  obtain ⟨D, p, hD, hp⟩ :=
    ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion (q ^ 2 * M') (res1 g) hg
  exact ⟨D, hD, p, hp⟩

omit [Fact q.Prime] in

theorem isIntegralQExp_smul_of_dvd {k : ℤ} (g : ModularForm (Γ q M') k) {D₁ D : ℤ} {p : PowerSeries ℤ}
    (hp : IsIntegralQExp ((D₁ : ℂ) • (⇑g : ℍ → ℂ)) p) {e : ℤ} (he : D = D₁ * e) :
    IsIntegralQExp (⇑((D : ℂ) • g) : ℍ → ℂ) (PowerSeries.C e * p) := by
  rw [IsIntegralQExp] at hp ⊢
  have h1 : (⇑((D : ℂ) • g) : ℍ → ℂ) = (e : ℂ) • (⇑((D₁ : ℂ) • g) : ℍ → ℂ) := by
    rw [ModularForm.IsGLPos.coe_smul, ModularForm.IsGLPos.coe_smul, smul_smul, he]
    push_cast
    rw [mul_comm]
  rw [h1, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods (e : ℂ) ((D₁ : ℂ) • g),
    ModularForm.IsGLPos.coe_smul, ← hp, map_mul, PowerSeries.map_C, PowerSeries.smul_eq_C_mul]
  rfl

end W1pRC
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_smul_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0.W1pRC"

theorem solution (q : ℕ) [Fact q.Prime] (M' : ℕ) (hqM' : ¬ q ∣ M') {k : ℤ} (hk : Even k)
    (f : ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :
      Subgroup (GL (Fin 2) ℝ)) k)
    (pf : PowerSeries ℤ) (hf : ModularCurve.IsIntegralQExp f pf)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') :
    ∃ D : ℤ, D ≠ 0 ∧
      ∃ (h : ℕ → ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :
          Subgroup (GL (Fin 2) ℝ)) k) (p : ℕ → PowerSeries ℤ),
        (∀ j : ℕ, ModularCurve.IsIntegralQExp (h j) (p j)) ∧
        ∀ (s : ℕ) (γ' : SL(2, ℤ)), Nat.Coprime s q → γ' ∈ CongruenceSubgroup.Gamma0 M' →
          !![(1 : ZMod q), 0; 0, (s : ZMod q)] * (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q)
            = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) * !![(1 : ZMod q), 0; 0, (s : ZMod q)] →
          (D : ℂ) • ((⇑f : UpperHalfPlane → ℂ) ∣[k] ModularCurve.FullLevel.conjElem q γ') =
            ∑ j ∈ Finset.range q,
              Complex.exp (2 * Real.pi * Complex.I * ((s * j : ℕ) : ℂ) / q) •
                (⇑(h j) : UpperHalfPlane → ℂ) := by
  classical
  haveI : NeZero M' := ⟨by rintro rfl; exact hqM' (dvd_zero q)⟩

  obtain ⟨hr, hrat, hrec⟩ :=
    ModularCurve.FullLevel.exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0 q M' hqM' hk f
      (W1pRC.exists_ratCast_of_isIntegralQExp hf) γ hγ

  have hBD : ∀ j : ℕ, ∃ D : ℤ, D ≠ 0 ∧ ∃ p : PowerSeries ℤ,
      ModularCurve.IsIntegralQExp ((D : ℂ) • (⇑(hr j) : UpperHalfPlane → ℂ)) p :=
    fun j => W1pRC.exists_isIntegralQExp_smul (hr j) (hrat j)
  choose D hD0 p hp using hBD

  set Dt : ℤ := ∏ j ∈ Finset.range q, D j with hDt
  have hDt0 : Dt ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hD0 j
  have hdvd : ∀ j ∈ Finset.range q, D j ∣ Dt := fun j hj => Finset.dvd_prod_of_mem D hj
  refine ⟨Dt, hDt0, fun j => if j < q then (Dt : ℂ) • hr j else 0,
    fun j => if j < q then PowerSeries.C (Dt / D j) * p j else 0, ?_, ?_⟩
  · intro j
    by_cases hj : j < q
    · simp only [if_pos hj]
      obtain ⟨e, he⟩ := hdvd j (Finset.mem_range.mpr hj)
      have hediv : Dt / D j = e := by rw [he, Int.mul_ediv_cancel_left _ (hD0 j)]
      rw [hediv]
      exact W1pRC.isIntegralQExp_smul_of_dvd (hr j) (hp j) he
    · simp only [if_neg hj]
      rw [ModularForm.coe_zero]
      exact ModularCurve.isIntegralQExp_zero
  · intro s γ' hs hγ' hγγ'
    rw [hrec s γ' hs hγ' hγγ', Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [if_pos (Finset.mem_range.mp hj), ModularForm.IsGLPos.coe_smul]
    rw [smul_comm]

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_smul_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0.W1pRC"

end S_ModularCurve_FullLevel_exists_smul_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_smul_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0 (solution)
