-- Prove2me | solution 1 for Maldacena2003.scalar_vertex_time_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:15:11.391804+00:00
-- url     : https://prove2.me/submissions/ca5bc094-877f-46b9-a0da-93a8de74163d

import Mathlib
import Definitions.Def_Maldacena2003_InflationDefs
open Filter Topology Maldacena2003

lemma perm_sum (k : Fin 3 → ℝ) : ∑ σ : Equiv.Perm (Fin 3), k (σ 0) ^ 2 * k (σ 1) ^ 2
    = 2 * (k 1 ^ 2 * k 0 ^ 2 + k 2 ^ 2 * k 0 ^ 2 + k 2 ^ 2 * k 1 ^ 2) := by
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
      {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2, Equiv.swap 0 1 * Equiv.swap 0 2,
        Equiv.swap 0 2 * Equiv.swap 0 1} := by decide
  rw [hu]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [Equiv.swap_apply_def, Equiv.Perm.mul_apply]
  ring

lemma vertex_int (a : ℂ) (K ε : ℝ) (hε : 0 < ε) :
    ∫ η in Set.Iic (0 : ℝ), a * Complex.exp (Complex.I * (K : ℂ) * (η : ℂ)) * (Real.exp (ε * η) : ℂ)
      = a / (ε + Complex.I * K) := by
  have e : ∀ η : ℝ, a * Complex.exp (Complex.I * (K : ℂ) * (η : ℂ)) * (Real.exp (ε * η) : ℂ)
      = a * Complex.exp ((ε + Complex.I * K) * η) := by
    intro η
    rw [Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
    congr 2; push_cast; ring
  simp_rw [e]
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_complex_Iic (by simpa using hε) 0]
  simp [div_eq_mul_inv]

theorem solution (k : Fin 3 → ℝ) (hk : ∀ i, 0 < k i) :
    Tendsto
      (fun ε : ℝ => ∑ σ : Equiv.Perm (Fin 3),
        2 * (Complex.I * ∫ η in Set.Iic (0 : ℝ),
          ((k (σ 0) : ℂ) ^ 2 * (k (σ 1) : ℂ) ^ 2)
            * Complex.exp (Complex.I * ((k 0 + k 1 + k 2 : ℝ) : ℂ) * (η : ℂ))
            * (Real.exp (ε * η) : ℂ)).re)
      (𝓝[>] 0)
      (𝓝 (4 * (k 1 ^ 2 * k 0 ^ 2 + k 2 ^ 2 * k 0 ^ 2 + k 2 ^ 2 * k 1 ^ 2)
        / (k 0 + k 1 + k 2))) := by
  set K := k 0 + k 1 + k 2 with hK
  have hK0 : 0 < K := by have := hk 0; have := hk 1; have := hk 2; linarith
  set F : ℝ → ℝ := fun ε => ∑ σ : Equiv.Perm (Fin 3),
      2 * (Complex.I * (((k (σ 0) : ℂ) ^ 2 * (k (σ 1) : ℂ) ^ 2) / (ε + Complex.I * K))).re with hF
  have hne0 : ((0:ℝ) : ℂ) + Complex.I * K ≠ 0 := by
    simp [hK0.ne']
  have hc : ContinuousAt F 0 := by
    simp only [hF]
    refine tendsto_finset_sum _ (fun σ _ => ?_)
    apply ContinuousAt.mul continuousAt_const
    apply Complex.continuous_re.continuousAt.comp
    apply ContinuousAt.mul continuousAt_const
    exact ContinuousAt.div (f := fun _ => _) (g := fun ε : ℝ => (ε:ℂ) + Complex.I * K)
      continuousAt_const (by fun_prop) hne0
  have hv : F 0 = 4 * (k 1 ^ 2 * k 0 ^ 2 + k 2 ^ 2 * k 0 ^ 2 + k 2 ^ 2 * k 1 ^ 2) / K := by
    have e : ∀ σ : Equiv.Perm (Fin 3),
        2 * (Complex.I * (((k (σ 0) : ℂ) ^ 2 * (k (σ 1) : ℂ) ^ 2) / (((0:ℝ):ℂ) + Complex.I * K))).re
          = 2 / K * (k (σ 0) ^ 2 * k (σ 1) ^ 2) := by
      intro σ
      have : Complex.I * (((k (σ 0) : ℂ) ^ 2 * (k (σ 1) : ℂ) ^ 2) / (((0:ℝ):ℂ) + Complex.I * K))
          = ((k (σ 0) ^ 2 * k (σ 1) ^ 2 / K : ℝ) : ℂ) := by
        have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast hK0.ne'
        rw [Complex.ofReal_zero, zero_add]
        push_cast
        field_simp
      rw [this, Complex.ofReal_re]; ring
    rw [hF]; dsimp only
    rw [Finset.sum_congr rfl (fun σ _ => e σ), ← Finset.mul_sum, perm_sum]
    ring
  have h1 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  rw [hv] at h1
  apply h1.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  simp only [hF]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [vertex_int _ K ε hε]
