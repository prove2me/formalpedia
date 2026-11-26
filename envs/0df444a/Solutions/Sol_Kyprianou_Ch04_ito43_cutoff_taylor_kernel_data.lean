-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_taylor_kernel_data
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:00:08.910278+00:00
-- url     : https://prove2.me/submissions/83c4251c-66f9-48de-8ada-74bc12d53cfe

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_zero_near_origin
open Set Filter
open scoped NNReal Topology
set_option autoImplicit false
theorem solution (f : Real × Real -> Real)
    (hfJointC1 : ContDiffOn Real 1 f
      (Set.prod (Set.Ici (0 : Real)) Set.univ))
    (hfSpaceC2 : forall s : NNReal,
      ContDiff Real 2 (fun x : Real => f ((s : Real), x)))
    (hfSpaceSecondContinuous :
      ContinuousOn
        (fun z : Real × Real =>
          iteratedDeriv 2 (fun x : Real => f (z.1, x)) z.2)
        (Set.prod (Set.Ici (0 : Real)) Set.univ)) :
    ∀ m : ℕ,
    let K : NNReal → ℝ → ℝ → ℝ := fun s x z =>
      (f ((s : ℝ),x+z) - f ((s : ℝ),x) -
        deriv (fun y : ℝ => f ((s : ℝ),y)) x*z -
        iteratedDeriv 2 (fun y : ℝ => f ((s : ℝ),y)) x*z^2/2) *
      min 1 (max 0 (|z| * ((m : ℝ)+1)-1))
    Continuous (fun p : NNReal × ℝ × ℝ => K p.1 p.2.1 p.2.2) ∧
      ∀ s x z, |z| ≤ 1/((m:ℝ)+1) → K s x z = 0 := by
  intro m K
  let S := Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set ℝ)
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hD (s : ℝ) (x : ℝ) (hs : 0 ≤ s) :
      deriv (fun y : ℝ => f (s,y)) x =
        fderivWithin ℝ f S (s,x) (0,1) := by
    have hd := (hfJointC1.differentiableOn (by norm_num) (s,x)
      (show (s,x) ∈ S from ⟨hs,Set.mem_univ _⟩)).hasFDerivWithinAt
    have hk : HasDerivAt (fun y : ℝ => (s,y)) (0,1) x :=
      (hasDerivAt_const x s).prodMk (hasDerivAt_id x)
    exact (hd.comp_hasDerivAt x hk (Eventually.of_forall
      fun y => show (s,y) ∈ S from ⟨hs,Set.mem_univ _⟩)).deriv
  let p : NNReal × ℝ × ℝ → ℝ × ℝ := fun a => ((a.1 : ℝ),a.2.1)
  let r : NNReal × ℝ × ℝ → ℝ × ℝ := fun a => ((a.1 : ℝ),a.2.1+a.2.2)
  have hp : Continuous p := by fun_prop
  have hr : Continuous r := by fun_prop
  have hpS (a : NNReal × ℝ × ℝ) : p a ∈ S := ⟨a.1.coe_nonneg,mem_univ _⟩
  have hrS (a : NNReal × ℝ × ℝ) : r a ∈ S := ⟨a.1.coe_nonneg,mem_univ _⟩
  have hf1 := hfJointC1.continuousOn.comp_continuous hp hpS
  have hf2 := hfJointC1.continuousOn.comp_continuous hr hrS
  have hd0 := hfJointC1.continuousOn_fderivWithin_apply hS (by norm_num)
  have hd : Continuous (fun a : NNReal × ℝ × ℝ =>
      deriv (fun y : ℝ => f ((a.1 : ℝ),y)) a.2.1) := by
    have h := hd0.comp_continuous (hp.prodMk continuous_const)
      (fun a => show (p a,(0,1)) ∈ S ×ˢ univ from ⟨hpS a,mem_univ _⟩)
    apply h.congr
    intro a
    exact (hD (a.1 : ℝ) a.2.1 a.1.coe_nonneg).symm
  have hdd := hfSpaceSecondContinuous.comp_continuous hp hpS
  obtain ⟨hchi,_,hz⟩ := Kyprianou.Ch04.ito43_cutoff_zero_near_origin m
  have hzproj : Continuous (fun a : NNReal × ℝ × ℝ => a.2.2) := by fun_prop
  constructor
  · exact (((hf2.sub hf1).sub (hd.mul hzproj)).sub
      ((hdd.mul (hzproj.pow 2)).div_const 2)).mul (hchi.comp hzproj)
  · intro s x z h
    have hh := (le_div_iff₀ (by positivity : 0 < (m:ℝ)+1)).mp h
    dsimp [K]
    have h0 := hz z hh
    dsimp at h0
    rw [h0,mul_zero]
