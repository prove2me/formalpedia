-- Prove2me | solution 1 for GroundTheory.Automorphic.ArchWhittaker.eq_zero_of_ode
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:47:49.917234+00:00
-- url     : https://prove2.me/submissions/003b70a5-68e6-4fc0-b46f-3f8c4d125116

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_WronskianEqZeroOfModerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ArchWhittaker
open Filter Topology Set
namespace GroundTheory.Automorphic.ArchWhittaker
theorem _root_.solution {q f f' : ℝ → ℂ} (hq : ContinuousOn q (Ioi 0))
    (hf : ∀ y > 0, HasDerivAt f (f' y) y) (hf' : ∀ y > 0, HasDerivAt f' (q y * f y) y)
    (h1 : f 1 = 0) (h1' : f' 1 = 0) : ∀ y > 0, f y = 0 := by
  intro y hy
  set a := min y 1 / 2 with ha
  set b := max y 1 + 1 with hb
  have ha0 : 0 < a := by rw [ha]; positivity
  have hab : Icc a b ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le ha0 ht.1
  obtain ⟨M, hM⟩ := (isCompact_Icc.exists_bound_of_continuousOn (hq.mono hab))
  set K : NNReal := ⟨1 + |M|, by positivity⟩ with hK
  set v : ℝ → ℂ × ℂ → ℂ × ℂ := fun t p => (p.2, q t * p.1) with hv
  have hlip : ∀ t ∈ Ioo a b, LipschitzOnWith K (v t) univ := by
    intro t ht
    refine LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun p p' => ?_)
    have hqt : ‖q t‖ ≤ |M| := le_trans (hM t (Ioo_subset_Icc_self ht)) (le_abs_self M)
    simp only [hv, Prod.dist_eq, hK]
    refine max_le ?_ ?_
    · calc dist p.2 p'.2 ≤ max (dist p.1 p'.1) (dist p.2 p'.2) := le_max_right _ _
        _ ≤ (1 + |M|) * max (dist p.1 p'.1) (dist p.2 p'.2) := by
          nlinarith [abs_nonneg M, le_max_right (dist p.1 p'.1) (dist p.2 p'.2), dist_nonneg (x := p.2) (y := p'.2)]
    · rw [dist_eq_norm, ← mul_sub, norm_mul, ← dist_eq_norm]
      calc ‖q t‖ * dist p.1 p'.1 ≤ |M| * max (dist p.1 p'.1) (dist p.2 p'.2) :=
            mul_le_mul hqt (le_max_left _ _) dist_nonneg (abs_nonneg M)
        _ ≤ (1 + |M|) * max (dist p.1 p'.1) (dist p.2 p'.2) := by
          nlinarith [le_max_left (dist p.1 p'.1) (dist p.2 p'.2), dist_nonneg (x := p.1) (y := p'.1)]
  have hsol : ∀ t ∈ Ioo a b, HasDerivAt (fun t => (f t, f' t)) (v t (f t, f' t)) t ∧
      (f t, f' t) ∈ (univ : Set (ℂ × ℂ)) := fun t ht =>
    ⟨(hf t (hab (Ioo_subset_Icc_self ht))).prodMk (hf' t (hab (Ioo_subset_Icc_self ht))), mem_univ _⟩
  have hzero : ∀ t ∈ Ioo a b, HasDerivAt (fun _ : ℝ => ((0 : ℂ), (0 : ℂ))) (v t (0, 0)) t ∧
      ((0 : ℂ), (0 : ℂ)) ∈ (univ : Set (ℂ × ℂ)) := fun t _ => by
    refine ⟨(hasDerivAt_const t ((0 : ℂ), (0 : ℂ))).congr_deriv ?_, mem_univ _⟩
    simp [hv]
    rfl
  have h1mem : (1 : ℝ) ∈ Ioo a b := by
    constructor
    · rw [ha]; have := min_le_right y 1; linarith
    · rw [hb]; have := le_max_right y 1; linarith
  have hymem : y ∈ Ioo a b := by
    constructor
    · rw [ha]; have := min_le_left y 1; linarith
    · rw [hb]; have := le_max_left y 1; linarith
  have := ODE_solution_unique_of_mem_Ioo (s := fun _ => univ) hlip h1mem hsol hzero
    (by simp [h1, h1']) hymem
  exact congrArg Prod.fst this
end GroundTheory.Automorphic.ArchWhittaker
