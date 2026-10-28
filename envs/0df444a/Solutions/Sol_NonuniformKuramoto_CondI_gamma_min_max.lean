-- Prove2me | solution 1 for NonuniformKuramoto.CondI.gamma_min_max
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:08:59.857831+00:00
-- url     : https://prove2.me/submissions/19156d7d-d041-457d-aa82-150e4c366e29

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model
import Definitions.Def_NonuniformKuramoto_CondI_Constants

open NonuniformKuramoto.CondI in
theorem solution {n : ℕ} (hn : 2 ≤ n) (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (hD : ∀ i, 0 < D i)
    (hP : ∀ i j, i ≠ j → 0 < P i j) (hPii : ∀ i, P i i = 0) (hϕii : ∀ i, ϕ i i = 0)
    (hϕ : ∀ i j, i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi / 2)
    (h26 : GammaCrit D ω P ϕ < GammaMin D P ϕ) :
    gammaMin D ω P ϕ ∈ Set.Ico 0 (Real.pi / 2 - phiMax ϕ) ∧
    gammaMax D ω P ϕ ∈ Set.Ioc (Real.pi / 2) Real.pi ∧
    Real.sin (gammaMin D ω P ϕ) = Real.cos (phiMax ϕ) * GammaCrit D ω P ϕ / GammaMin D P ϕ ∧
    Real.sin (gammaMax D ω P ϕ) = Real.cos (phiMax ϕ) * GammaCrit D ω P ϕ / GammaMin D P ϕ ∧
    (∀ γ ∈ Set.Ico 0 (Real.pi / 2 - phiMax ϕ),
      Real.sin γ = Real.cos (phiMax ϕ) * GammaCrit D ω P ϕ / GammaMin D P ϕ →
        γ = gammaMin D ω P ϕ) ∧
    (∀ γ ∈ Set.Ioc (Real.pi / 2) Real.pi,
      Real.sin γ = Real.cos (phiMax ϕ) * GammaCrit D ω P ϕ / GammaMin D P ϕ →
        γ = gammaMax D ω P ϕ) ∧
    (∀ γ ∈ Set.Icc 0 Real.pi,
      (Real.cos (phiMax ϕ) * GammaCrit D ω P ϕ ≤ GammaMin D P ϕ * Real.sin γ ↔
        γ ∈ Set.Icc (gammaMin D ω P ϕ) (gammaMax D ω P ϕ))) := by
  classical
  have hpi := Real.pi_pos
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hϕlt : ∀ i j, ϕ i j < Real.pi / 2 := by
    intro i j
    by_cases h : i = j
    · subst h; rw [hϕii]; linarith
    · exact (hϕ i j h).2
  have hϕnn : ∀ i j, 0 ≤ ϕ i j := by
    intro i j
    by_cases h : i = j
    · subst h; rw [hϕii]
    · exact (hϕ i j h).1
  -- phiMax ∈ [0, π/2)
  have hmax_le : ∀ (f : Fin n → ℝ) (i : Fin n), f i ≤ maxIdx f := by
    intro f i
    unfold maxIdx; rw [dif_pos hne]
    exact Finset.le_sup' f (Finset.mem_univ i)
  have hmax_lt : ∀ (f : Fin n → ℝ) (c : ℝ), (∀ i, f i < c) → maxIdx f < c := by
    intro f c h
    unfold maxIdx; rw [dif_pos hne]
    exact (Finset.sup'_lt_iff _).mpr fun i _ => h i
  set Φ := phiMax ϕ with hΦ
  have hΦ0 : 0 ≤ Φ := by
    have i0 : Fin n := ⟨0, by omega⟩
    calc (0 : ℝ) = ϕ i0 i0 := (hϕii i0).symm
      _ ≤ maxIdx (fun j => ϕ i0 j) := hmax_le (fun j => ϕ i0 j) i0
      _ ≤ Φ := hmax_le (fun i => maxIdx fun j => ϕ i j) i0
  have hΦlt : Φ < Real.pi / 2 := hmax_lt _ _ fun i => hmax_lt _ _ fun j => hϕlt i j
  have hcos : 0 < Real.cos Φ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hΦlt⟩
  have hcos1 : Real.cos Φ ≤ 1 := Real.cos_le_one _
  -- GammaMin > 0
  have hoff : (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2)).Nonempty :=
    ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.ext_iff]⟩
  have hGM : 0 < GammaMin D P ϕ := by
    unfold GammaMin minOffDiag
    rw [dif_pos hoff]
    apply mul_pos (by exact_mod_cast (show 0 < n by omega))
    rw [Finset.lt_inf'_iff]
    intro p hp
    have hp' : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    exact mul_pos (div_pos (hP _ _ hp') (hD _))
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [hϕnn p.1 p.2], hϕlt p.1 p.2⟩)
  -- GammaCrit ≥ 0
  have hGC : 0 ≤ GammaCrit D ω P ϕ := by
    unfold GammaCrit
    apply mul_nonneg (by rw [← hΦ]; positivity)
    have h1 : 0 ≤ omegaSpread D ω := by
      unfold omegaSpread maxOffDiag
      rw [dif_pos hoff]
      obtain ⟨p, hp⟩ := hoff
      exact le_trans (abs_nonneg _) (Finset.le_sup' (fun p : Fin n × Fin n =>
        |ω p.1 / D p.1 - ω p.2 / D p.2|) hp)
    have h2 : 0 ≤ lossMax D P ϕ := by
      unfold lossMax
      have i0 : Fin n := ⟨0, by omega⟩
      refine le_trans ?_ (hmax_le _ i0)
      refine Finset.sum_nonneg fun j _ => ?_
      by_cases h : i0 = j
      · subst h; rw [hPii]; simp
      · exact mul_nonneg (div_nonneg (hP _ _ h).le (hD _).le)
          (Real.sin_nonneg_of_nonneg_of_le_pi (hϕnn _ _) (by linarith [hϕlt i0 j]))
    linarith
  set x := Real.cos Φ * GammaCrit D ω P ϕ / GammaMin D P ϕ with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hxc : x < Real.cos Φ := by
    rw [hx, div_lt_iff₀ hGM]
    exact mul_lt_mul_of_pos_left h26 hcos
  have hx1 : x < 1 := lt_of_lt_of_le hxc hcos1
  have hxI : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, hx1.le⟩
  have hgmin : gammaMin D ω P ϕ = Real.arcsin x := rfl
  have hgmax : gammaMax D ω P ϕ = Real.pi - Real.arcsin x := rfl
  rw [hgmin, hgmax]
  set a := Real.arcsin x with ha
  have ha0 : 0 ≤ a := Real.arcsin_nonneg.mpr hx0
  have hapi : a < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hx1
  have hsa : Real.sin a = x := Real.sin_arcsin hxI.1 hxI.2
  have haI : a ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, hapi.le⟩
  have hcosΦ : Real.cos Φ = Real.sin (Real.pi / 2 - Φ) := (Real.sin_pi_div_two_sub Φ).symm
  -- monotone characterization on [0, π]
  have hchar : ∀ γ ∈ Set.Icc 0 Real.pi, (x ≤ Real.sin γ ↔ γ ∈ Set.Icc a (Real.pi - a)) := by
    intro γ hγ
    rcases le_or_gt γ (Real.pi / 2) with hle | hgt
    · have hγI : γ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith [hγ.1], hle⟩
      rw [← Real.arcsin_le_iff_le_sin hxI hγI]
      constructor
      · intro h; exact ⟨h, by linarith⟩
      · intro h; exact h.1
    · have hγI : Real.pi - γ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨by linarith [hγ.2], by linarith⟩
      rw [← Real.sin_pi_sub, ← Real.arcsin_le_iff_le_sin hxI hγI]
      constructor
      · intro h; exact ⟨by linarith, by linarith⟩
      · intro h; linarith [h.2]
  refine ⟨⟨ha0, ?_⟩, ⟨by linarith, by linarith⟩, hsa, ?_, ?_, ?_, ?_⟩
  · rw [ha, Real.arcsin_lt_iff_lt_sin hxI ⟨by linarith, by linarith⟩, ← hcosΦ]
    exact hxc
  · rw [Real.sin_pi_sub, hsa]
  · intro γ hγ hs
    have hγI : γ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [hγ.1], by linarith [hγ.2]⟩
    exact Real.injOn_sin hγI haI (by rw [hs, hsa])
  · intro γ hγ hs
    have hγI : Real.pi - γ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [hγ.2], by linarith [hγ.1]⟩
    have := Real.injOn_sin hγI haI (by rw [Real.sin_pi_sub, hs, hsa])
    linarith
  · intro γ hγ
    rw [← hchar γ hγ]
    rw [hx, div_le_iff₀ hGM, mul_comm (Real.sin γ)]
