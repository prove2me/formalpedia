-- Prove2me | solution 1 for MaxPressure.Throughput.energy_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:45:34.301821+00:00
-- url     : https://prove2.me/submissions/8e2d1a97-7891-42ec-9b78-a28855e143f2

import Mathlib
import Definitions.Def_MaxPressure_Throughput_Network

open MaxPressure.Throughput in
theorem energy_derivative_aux1 {I J K : ℕ} (N : Network I J K)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ)
    (hfluid : IsFluidSolution N Zb Tb) :
    ∀ s, 0 ≤ s → Zb s = Zb 0 - Matrix.mulVec (R N) (Tb s) := by
  intro s hs
  funext i
  rw [hfluid.1 s hs i]
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, R]
  have h1 : ∑ i' : Fin (I + 1), ∑ j : Fin J,
        Tb s j * mu N j * N.B j i' * N.P j i' i.succ
      = ∑ j : Fin J, ∑ i' : Fin (I + 1),
        Tb s j * mu N j * N.B j i' * N.P j i' i.succ := Finset.sum_comm
  rw [h1]
  have h2 : ∀ j : Fin J, mu N j * (N.B j i.succ - ∑ i' : Fin (I + 1), N.B j i' * N.P j i' i.succ) * Tb s j
      = Tb s j * mu N j * N.B j i.succ - ∑ i' : Fin (I + 1),
        Tb s j * mu N j * N.B j i' * N.P j i' i.succ := by
    intro j
    rw [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · ring
    · refine Finset.sum_congr rfl ?_
      intro x _
      ring
  simp_rw [h2, Finset.sum_sub_distrib]
  ring

open MaxPressure.Throughput in
theorem solution {I J K : ℕ} (N : Network I J K)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ)
    (hfluid : IsFluidSolution N Zb Tb)
    (t : ℝ) (hregular : IsRegular Zb Tb t) :
    (∀ s, 0 ≤ s → Zb s = Zb 0 - Matrix.mulVec (R N) (Tb s)) ∧
    HasDerivAt (fun s => ∑ i, Zb s i ^ 2)
      (-2 * pressure N (deriv Tb t) (Zb t)) t := by
  have h1 := energy_derivative_aux1 N Zb Tb hfluid
  refine ⟨h1, ?_⟩
  obtain ⟨ht, _, hT⟩ := hregular
  have hTd : HasDerivAt Tb (deriv Tb t) t := hT.hasDerivAt
  have hTj : ∀ j, HasDerivAt (fun s => Tb s j) (deriv Tb t j) t :=
    fun j => (hasDerivAt_pi.1 hTd) j
  set g : Fin I → ℝ → ℝ := fun i s => Zb 0 i - ∑ j, R N i j * Tb s j with hg
  have hgd : ∀ i, HasDerivAt (g i) (-(∑ j, R N i j * deriv Tb t j)) t := by
    intro i
    have : HasDerivAt (fun s => ∑ j, R N i j * Tb s j) (∑ j, R N i j * deriv Tb t j) t :=
      HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hTj j).const_mul (R N i j))
    exact this.const_sub (Zb 0 i)
  have hev : (fun s => ∑ i, g i s ^ 2) =ᶠ[nhds t] (fun s => ∑ i, Zb s i ^ 2) := by
    filter_upwards [lt_mem_nhds ht] with s hs
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [h1 s hs.le]
    simp [hg, Matrix.mulVec, dotProduct]
  have hgt : ∀ i, g i t = Zb t i := by
    intro i; rw [h1 t ht.le]; simp [hg, Matrix.mulVec, dotProduct]
  have hsum : HasDerivAt (fun s => ∑ i, g i s ^ 2)
      (∑ i, ((2 : ℕ) : ℝ) * g i t ^ (2 - 1) * (-(∑ j, R N i j * deriv Tb t j))) t :=
    HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hgd i).fun_pow 2)
  refine (hsum.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  simp only [pressure, dotProduct]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [hgt]
  simp only [Matrix.mulVec, dotProduct]
  push_cast
  ring
