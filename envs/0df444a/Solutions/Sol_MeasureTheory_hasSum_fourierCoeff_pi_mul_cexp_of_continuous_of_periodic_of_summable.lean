-- Prove2me | solution 1 for MeasureTheory.hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/84a0d0e9-4afd-5b21-bc05-99f2ae9b565e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable

set_option autoImplicit false

open MeasureTheory Complex

namespace K4Aux44

theorem periodic_intCast {c : ℕ} (F : (Fin c → ℝ) → ℂ)
    (hper : ∀ (θ : Fin c → ℝ) (j : Fin c), F (θ + Pi.single j 1) = F θ)
    (θ : Fin c → ℝ) (k : Fin c → ℤ) : F (θ + fun i => (k i : ℝ)) = F θ := by
  classical
  let P : AddSubgroup (Fin c → ℝ) :=
    { carrier := {v | ∀ θ, F (θ + v) = F θ}
      add_mem' := fun {a b} ha hb θ => by
        show F (θ + (a + b)) = F θ
        rw [← add_assoc, hb, ha]
      zero_mem' := fun θ => by show F (θ + 0) = F θ; rw [add_zero]
      neg_mem' := fun {a} ha θ => by
        show F (θ + -a) = F θ
        have h := ha (θ + -a)
        rw [neg_add_cancel_right] at h
        exact h.symm }
  have hsingle : ∀ (j : Fin c) (n : ℤ), (Pi.single j ((n : ℝ)) : Fin c → ℝ) ∈ P := by
    intro j n
    have h1 : (Pi.single j (1 : ℝ) : Fin c → ℝ) ∈ P := fun θ => hper θ j
    have : (Pi.single j ((n : ℝ)) : Fin c → ℝ) = n • (Pi.single j (1 : ℝ) : Fin c → ℝ) := by
      ext i
      by_cases h : i = j
      · subst h; simp
      · simp [h]
    rw [this]
    exact P.zsmul_mem h1 n
  have hk : (fun i => (k i : ℝ)) ∈ P := by
    have : (fun i => (k i : ℝ)) = ∑ j : Fin c, (Pi.single j ((k j : ℝ)) : Fin c → ℝ) :=
      (Finset.univ_sum_single (fun i => (k i : ℝ))).symm
    rw [this]
    exact P.sum_mem fun j _ => hsingle j (k j)
  exact hk θ

theorem mFourier_coe_apply {c : ℕ} (m : Fin c → ℤ) (x : Fin c → ℝ) :
    UnitAddTorus.mFourier m (fun i => (x i : UnitAddCircle)) =
      cexp (2 * Real.pi * I * ((∑ j, (m j : ℝ) * x j : ℝ) : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end K4Aux44

open K4Aux44 in
theorem solution
    {c : ℕ} (F : (Fin c → ℝ) → ℂ) (hF : Continuous F)
    (hper : ∀ (θ : Fin c → ℝ) (j : Fin c), F (θ + Pi.single j 1) = F θ)
    (hsum : Summable fun m : Fin c → ℤ =>
      ‖∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
          F θ * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))‖)
    (θ : Fin c → ℝ) :
    HasSum (fun m : Fin c → ℤ =>
      (∫ θ' in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
          F θ' * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ' j : ℝ) : ℂ)))) *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))) (F θ) := by
  classical

  let q : (Fin c → ℝ) → UnitAddTorus (Fin c) := fun θ i => (θ i : UnitAddCircle)
  have hqo : IsOpenQuotientMap q :=
    IsOpenQuotientMap.piMap (f := fun (_ : Fin c) (t : ℝ) => (t : UnitAddCircle))
      fun _ => QuotientAddGroup.isOpenQuotientMap_mk

  let sec : UnitAddTorus (Fin c) → (Fin c → ℝ) := fun x i => ((AddCircle.equivIco (1 : ℝ) 0 (x i) : ℝ))
  have hsec : ∀ θ' : Fin c → ℝ, ∃ k : Fin c → ℤ, sec (q θ') = θ' + fun i => (k i : ℝ) := by
    intro θ'
    refine ⟨fun i => -⌊θ' i⌋, funext fun i => ?_⟩
    show ((AddCircle.equivIco (1 : ℝ) 0 ((θ' i : ℝ) : UnitAddCircle) : ℝ)) = θ' i + ((-⌊θ' i⌋ : ℤ) : ℝ)
    rw [AddCircle.coe_equivIco_mk_apply, div_one, mul_one, Int.fract, Int.cast_neg, sub_eq_add_neg]
  let fF : UnitAddTorus (Fin c) → ℂ := fun x => F (sec x)
  have hfq : ∀ θ', fF (q θ') = F θ' := by
    intro θ'
    obtain ⟨k, hk⟩ := hsec θ'
    show F (sec (q θ')) = F θ'
    rw [hk]
    exact periodic_intCast F hper θ' k
  have hfc : Continuous fF := by
    rw [← hqo.continuous_comp_iff]
    have : fF ∘ q = F := funext hfq
    rw [this]
    exact hF
  let f : C(UnitAddTorus (Fin c), ℂ) := ⟨fF, hfc⟩
  have hfq' : ∀ θ', f (q θ') = F θ' := hfq

  have hcoef : ∀ m : Fin c → ℤ, UnitAddTorus.mFourierCoeff f m =
      ∫ θ' in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
        F θ' * cexp (-(2 * Real.pi * I * ((∑ j, (m j : ℝ) * θ' j : ℝ) : ℂ))) := by
    intro m
    rw [UnitAddTorus.mFourierCoeff_eq_integral _ _ (0 : Fin c → ℝ)]
    have hset : {x : Fin c → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin c → ℝ) i) ((0 : Fin c → ℝ) i + 1)}
        =ᵐ[volume] Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1) := by
      have h1 : {x : Fin c → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin c → ℝ) i) ((0 : Fin c → ℝ) i + 1)}
          = Set.pi Set.univ (fun i => Set.Ioc ((0 : Fin c → ℝ) i) ((1 : Fin c → ℝ) i)) := by
        ext x; simp
      have h2 : Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1)
          = Set.pi Set.univ (fun i => Set.Ico ((0 : Fin c → ℝ) i) ((1 : Fin c → ℝ) i)) := by
        ext x; simp
      rw [h1, h2, volume_pi]
      exact Measure.univ_pi_Ioc_ae_eq_Icc.trans Measure.univ_pi_Ico_ae_eq_Icc.symm
    rw [setIntegral_congr_set hset]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show (UnitAddTorus.mFourier (-m)) (q x) • f (q x) = _
    rw [hfq' x, smul_eq_mul, mul_comm, mFourier_coe_apply]
    congr 2
    push_cast
    simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, mul_neg]

  have hs : Summable (UnitAddTorus.mFourierCoeff f) := by
    refine Summable.of_norm ?_
    have : (fun m => ‖UnitAddTorus.mFourierCoeff f m‖) = fun m : Fin c → ℤ =>
        ‖∫ θ' in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
            F θ' * cexp (-(2 * Real.pi * I * ((∑ j, (m j : ℝ) * θ' j : ℝ) : ℂ)))‖ := funext fun m => by rw [hcoef]
    rw [this]
    exact hsum

  have H := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs (q θ)
  rw [hfq' θ] at H
  convert H using 2 with m
  rw [hcoef m, smul_eq_mul, mFourier_coe_apply]

end S_MeasureTheory_hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable
end P2MW
export P2MW.S_MeasureTheory_hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable (solution)
