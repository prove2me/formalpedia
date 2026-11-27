-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_qv_jump_step_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:32:19.089721+00:00
-- url     : https://prove2.me/submissions/784267e5-4b74-4121-a9db-dbdcbb2281e0

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Theorems.Thm_Kyprianou_Ch04_ito43_path_jump_kernel_energy_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_qv_jump_step_identity
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
/-- Dominate the difference of actual jump kernels by delta times half the squared jump energy; combine with the strict-threshold identity. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (X L : NNReal → Ω → ℝ) (w : Ω)
    (hJ : ({s : NNReal | 0 < s ∧ X s w ≠ L s w}).Countable)
    (H t : NNReal) (ht : t ≤ H)
    (hE : Summable (fun s : Ioc (0:NNReal) H => (X s w-L s w)^2))
    (g : ℝ × ℝ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (m : ℕ) (b : ℕ → NNReal) (c : ℕ → ℝ)
    (hL : ∀ s : NNReal, 0 < s → s ≤ t →
      |g ((s:ℝ),L s w) -
        ∑ i ∈ Finset.range m, c i * (if b i < s then (1:ℝ) else 0)| ≤ δ) :
    let μ := Kyprianou.Ch04.pathJumpMeasure X L w
    let S : Set (ℝ × ℝ) := Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ)
    |(∫ z in S, g (z.1,L z.1.toNNReal w)*(z.2^2/2) ∂μ) -
      ∑ i ∈ Finset.range m, c i *
        ((∫ z in S, z.2^2/2 ∂μ) -
         ∫ z in Icc (0:ℝ) ((min t (b i):NNReal):ℝ) ×ˢ (univ : Set ℝ),
           z.2^2/2 ∂μ)| ≤
      (δ/2) * ∑' s : Ioc (0:NNReal) H, (X s w-L s w)^2 := by
  intro μ S
  let e : ℝ × ℝ → ℝ := fun z => z.2^2/2
  let W : ℝ → ℝ := fun r => ∑ i ∈ Finset.range m,
    c i * (if (b i:ℝ) < r then (1:ℝ) else 0)
  let a : ℝ × ℝ → ℝ := fun z => g (z.1,L z.1.toNNReal w)
  let K : ℝ × ℝ → ℝ := fun z => (a z-W z.1)*e z
  have he : IntegrableOn e S μ :=
    (Kyprianou.Ch04.ito43_path_jump_kernel_energy_bound X L w hJ H t ht
      (1/2) (by norm_num) hE e (by
        intro s _ _
        dsimp [e]
        rw [abs_of_nonneg (by positivity : 0 ≤ (X s w-L s w)^2/2)]
        ring_nf <;> exact le_rfl)).1
  obtain ⟨hWi,hWe⟩ := Kyprianou.Ch04.ito43_qv_jump_step_identity μ t he m b c
  change IntegrableOn (fun z => W z.1*e z) S μ at hWi
  have hK := Kyprianou.Ch04.ito43_path_jump_kernel_energy_bound X L w hJ H t ht
    (δ/2) (by positivity) hE K (by
      intro s hs hst
      have hw : W (s:ℝ) = ∑ i ∈ Finset.range m,
          c i * (if b i < s then (1:ℝ) else 0) := by simp [W]
      dsimp only [K,a,e]
      rw [Real.toNNReal_coe,hw,abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ (X s w-L s w)^2/2)]
      calc
        _ ≤ δ*((X s w-L s w)^2/2) :=
          mul_le_mul_of_nonneg_right (hL s hs hst) (by positivity)
        _ = _ := by ring)
  have hKi : IntegrableOn K S μ := hK.1
  have hAi : IntegrableOn (fun z => a z*e z) S μ := by
    apply (hKi.add hWi).congr
    exact Eventually.of_forall (fun z => by dsimp [K]; ring)
  have hdiff : (∫ z in S, a z*e z ∂μ) -
      (∫ z in S, W z.1*e z ∂μ) = ∫ z in S, K z ∂μ := by
    rw [← integral_sub hAi hWi]
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => by dsimp [K]; ring)
  change |(∫ z in S, a z*e z ∂μ) - _| ≤ _
  rw [← hWe,hdiff]
  exact hK.2
