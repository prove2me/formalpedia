-- Prove2me | solution 1 for NoetherIVP.dependency_relations
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T16:22:51.129954+00:00
-- url     : https://prove2.me/submissions/8517d270-a953-45c9-ba6f-0518496b623a

import Mathlib
import Definitions.Def_NoetherIVP_core

open Finset NoetherIVP MeasureTheory

namespace NoetherAux

variable {n : ℕ}

/-- Integration by parts against a test function: for a `C¹` function `G` and a smooth compactly
supported `p`, `∫ G ∂_l p = -∫ (∂_l G) p`. -/
lemma integral_mul_dirD (l : Fin n) (G p : (Fin n → ℝ) → ℝ)
    (hG : ContDiff ℝ 1 G) (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hps : HasCompactSupport p) :
    (∫ y, G y * dirD l p y) = -∫ y, dirD l G y * p y := by
  have hp1 : ContDiff ℝ 1 p := hp.of_le (by exact_mod_cast le_top)
  have hGc : Continuous G := hG.continuous
  have hpc : Continuous p := hp1.continuous
  have hdG : Continuous fun x => (fderiv ℝ G x) (Pi.single l (1:ℝ)) :=
    (hG.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdp : Continuous fun x => (fderiv ℝ p x) (Pi.single l (1:ℝ)) :=
    (hp1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcsdp : HasCompactSupport fun x => (fderiv ℝ p x) (Pi.single l (1:ℝ)) :=
    (hps.fderiv ℝ).comp_left (g := fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single l 1)) (by simp)
  have i1 : Integrable (fun x => (fderiv ℝ G x) (Pi.single l (1:ℝ)) * p x) :=
    (hdG.mul hpc).integrable_of_hasCompactSupport hps.mul_left
  have i2 : Integrable (fun x => G x * (fderiv ℝ p x) (Pi.single l (1:ℝ))) :=
    (hGc.mul hdp).integrable_of_hasCompactSupport hcsdp.mul_left
  have i3 : Integrable (fun x => G x * p x) :=
    (hGc.mul hpc).integrable_of_hasCompactSupport hps.mul_left
  simpa [dirD] using
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable i1 i2 i3 (fun x _ => hG.differentiable_one x)
      (fun x _ => hp1.differentiable_one x)

/-- The fundamental lemma of the calculus of variations: a continuous function on `ℝⁿ` that
integrates to zero against every smooth compactly supported function vanishes identically. -/
lemma eq_zero_of_integral_mul_test_eq_zero (H : (Fin n → ℝ) → ℝ) (hH : Continuous H)
    (h0 : ∀ p : (Fin n → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) p → HasCompactSupport p →
      (∫ y, H y * p y) = 0) : ∀ x, H x = 0 := by
  have hae : ∀ᵐ x : (Fin n → ℝ), H x = 0 :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero hH.locallyIntegrable
      (fun g hg hgs => by simpa [smul_eq_mul, mul_comm] using h0 g hg hgs)
  have hEq : H = fun _ => (0:ℝ) := by
    refine (Continuous.ae_eq_iff_eq (volume : Measure (Fin n → ℝ)) hH continuous_const).mp ?_
    filter_upwards [hae] with x hx using hx
  intro x
  rw [hEq]

end NoetherAux

theorem solution {n m : ℕ} (psi a : Fin m → (Fin n → ℝ) → ℝ)
    (b : Fin n → Fin m → (Fin n → ℝ) → ℝ)
    (hpsi : ∀ i : Fin m, Continuous (psi i))
    (ha : ∀ i : Fin m, Continuous (a i))
    (hb : ∀ (l : Fin n) (i : Fin m), Continuous (b l i))
    (hG : ∀ l : Fin n, ContDiff ℝ 1 fun y => ∑ i : Fin m, b l i y * psi i y)
    (hint : ∀ p : (Fin n → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) p → HasCompactSupport p →
      (∫ y : Fin n → ℝ, ∑ i : Fin m,
          psi i y * (a i y * p y + ∑ l : Fin n, b l i y * dirD l p y)) = 0) :
    ∀ x : Fin n → ℝ, (∑ i : Fin m, a i x * psi i x)
      - ∑ l : Fin n, dirD l (fun y => ∑ i : Fin m, b l i y * psi i y) x = 0 := by
  classical
  set G : Fin n → (Fin n → ℝ) → ℝ := fun l y => ∑ i : Fin m, b l i y * psi i y with hGdef
  set A : (Fin n → ℝ) → ℝ := fun y => ∑ i : Fin m, a i y * psi i y with hAdef
  have hAc : Continuous A := continuous_finsetSum _ fun i _ => (ha i).mul (hpsi i)
  have hGc : ∀ l, Continuous (G l) := fun l => (hG l).continuous
  have hdGc : ∀ l, Continuous fun x => dirD l (G l) x := fun l =>
    ((hG l).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hHc : Continuous fun x => A x - ∑ l : Fin n, dirD l (G l) x :=
    hAc.sub (continuous_finsetSum _ fun l _ => hdGc l)
  refine NoetherAux.eq_zero_of_integral_mul_test_eq_zero _ hHc ?_
  intro p hp hps
  have hp1 : ContDiff ℝ 1 p := hp.of_le (by exact_mod_cast le_top)
  have hdpc : ∀ l : Fin n, Continuous fun x => dirD l p x := fun l =>
    (hp1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcsdp : ∀ l : Fin n, HasCompactSupport fun x => dirD l p x := fun l =>
    (hps.fderiv ℝ).comp_left (g := fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single l 1)) (by simp)
  -- integrability of the pieces
  have iAp : Integrable fun y => A y * p y :=
    (hAc.mul hp1.continuous).integrable_of_hasCompactSupport hps.mul_left
  have iGp : ∀ l : Fin n, Integrable fun y => G l y * dirD l p y := fun l =>
    ((hGc l).mul (hdpc l)).integrable_of_hasCompactSupport (hcsdp l).mul_left
  have iDp : ∀ l : Fin n, Integrable fun y => dirD l (G l) y * p y := fun l =>
    ((hdGc l).mul hp1.continuous).integrable_of_hasCompactSupport hps.mul_left
  -- the integrand of the hypothesis, rewritten
  have hpt : ∀ y : Fin n → ℝ,
      (∑ i : Fin m, psi i y * (a i y * p y + ∑ l : Fin n, b l i y * dirD l p y))
        = A y * p y + ∑ l : Fin n, G l y * dirD l p y := by
    intro y
    simp only [hAdef, hGdef, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring
  have hint2 : (∫ y : Fin n → ℝ, (A y * p y + ∑ l : Fin n, G l y * dirD l p y)) = 0 := by
    rw [← hint p hp hps]
    exact (integral_congr_ae (Filter.Eventually.of_forall fun y => hpt y)).symm
  rw [integral_add iAp (integrable_finsetSum _ fun l _ => iGp l),
    integral_finsetSum _ fun l _ => iGp l] at hint2
  have hparts : ∀ l : Fin n, (∫ y, G l y * dirD l p y) = -∫ y, dirD l (G l) y * p y :=
    fun l => NoetherAux.integral_mul_dirD l (G l) p (hG l) hp hps
  have hsplit : (∫ y : Fin n → ℝ, (A y - ∑ l : Fin n, dirD l (G l) y) * p y)
      = (∫ y, A y * p y) - ∑ l : Fin n, ∫ y, dirD l (G l) y * p y := by
    have : ∀ y : Fin n → ℝ, (A y - ∑ l : Fin n, dirD l (G l) y) * p y
        = A y * p y - ∑ l : Fin n, dirD l (G l) y * p y := by
      intro y; simp [sub_mul, Finset.sum_mul]
    rw [integral_congr_ae (Filter.Eventually.of_forall this),
      integral_sub iAp (integrable_finsetSum _ fun l _ => iDp l),
      integral_finsetSum _ fun l _ => iDp l]
  rw [hsplit]
  have : ∑ l : Fin n, ∫ y, dirD l (G l) y * p y = -∑ l : Fin n, ∫ y, G l y * dirD l p y := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [hparts l, neg_neg]
  rw [this]
  linarith [hint2]
