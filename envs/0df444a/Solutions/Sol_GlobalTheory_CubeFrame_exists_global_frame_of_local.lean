-- Prove2me | solution 1 for GlobalTheory.CubeFrame.exists_global_frame_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:41:17.763775+00:00
-- url     : https://prove2.me/submissions/044c7f9a-710e-45a9-8c0c-d86819cf103b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsGlobalFrameOfLocal
import Theorems.Thm_GlobalTheory_CubeFrame_exists_glue
import Theorems.Thm_GlobalTheory_CubeFrame_isOpen_cubeChart
import Theorems.Thm_GlobalTheory_CubeFrame_cube_eq_on_ball
import Theorems.Thm_GlobalTheory_CubeFrame_exists_double

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.CubeFrame
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {ι : Type} {W : ι → Set E} {c : ι → ι → E → ℂ}
  {T : (Finset (Fin 3) → ι) → (Fin 3 → E) → ℂ}
namespace GlobalTheory.CubeFrame
theorem _root_.solution (hW : ∀ i, IsOpen (W i)) (hcov : ∀ z, ∃ i, z ∈ W i)
    (hcd : ∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j))
    (hc0 : ∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0)
    (hcc : ∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z)
    (hT : ∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))})
    (hT0 : ∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0)
    (hTc : ∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
      (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) →
      T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) *
        T j' x)
    {r : ℝ} {fr : ι → E → ℂ} {κ : ℂ} (hr : 0 < r)
    (hfd : ∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Metric.ball 0 r))
    (hf0 : ∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr i z ≠ 0)
    (hfc : ∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 r → fr i z = c i j z * fr j z)
    (hev : ∀ᶠ x in 𝓝 (0 : Fin 3 → E), ∀ j, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
      T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) :
    ∃ fr' : ι → E → ℂ, (∀ i, DifferentiableOn ℂ (fr' i) (W i)) ∧
      (∀ i z, z ∈ W i → fr' i z ≠ 0) ∧
      (∀ i j z, z ∈ W i → z ∈ W j → fr' i z = c i j z * fr' j z) ∧
      (∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr' i z = fr i z) ∧
      ∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
        T j x = κ * ∏ I : Finset (Fin 3),
          fr' (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card)) := by
  let P : ℝ → (ι → E → ℂ) → Prop := fun ρ f =>
    (∀ i, DifferentiableOn ℂ (f i) (W i ∩ Metric.ball 0 ρ)) ∧
    (∀ i z, z ∈ W i → z ∈ Metric.ball 0 ρ → f i z ≠ 0) ∧
    (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 ρ → f i z = c i j z * f j z) ∧
    ∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
      (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ Metric.ball (0 : E) ρ) →
      T j x = κ * ∏ I : Finset (Fin 3), f (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))
  have hP0 : P (2 ^ 0 * r) fr := by
    rw [pow_zero, one_mul]
    exact ⟨hfd, hf0, hfc, cube_eq_on_ball hW hcov hc0 hT hTc hr hfd hf0 hfc hev⟩
  have hstep : ∀ (n : ℕ) (f : {f // P (2 ^ n * r) f}), ∃ f' : {f // P (2 ^ (n + 1) * r) f},
      ∀ i z, z ∈ W i → z ∈ Metric.ball 0 (2 ^ n * r) → f'.1 i z = f.1 i z := by
    rintro n ⟨f, h1, h2, h3, h4⟩
    have hρ : 0 < 2 ^ n * r := by positivity
    obtain ⟨f', k1, k2, k3, k4⟩ := exists_double hW hcov hcd hc0 hcc hT hT0 hTc hρ h1 h2 h3 h4
    have e : (2 : ℝ) ^ (n + 1) * r = 2 * (2 ^ n * r) := by ring
    refine ⟨⟨f', ?_⟩, k4⟩
    rw [e]
    refine ⟨k1, k2, k3, cube_eq_on_ball hW hcov hc0 hT hTc (by positivity) k1 k2 k3 ?_⟩
    have ho : IsOpen {x : Fin 3 → E |
        ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ Metric.ball (0 : E) (2 ^ n * r)} :=
      isOpen_cubeChart (p := fun x => x) continuous_id fun _ => Metric.isOpen_ball
    filter_upwards [ho.mem_nhds (x := 0) fun I => by simpa using hρ] with x hx j hj
    rw [h4 j x hj hx]
    congr 1
    exact Finset.prod_congr rfl fun I _ => by rw [k4 _ _ (hj I) (hx I)]
  choose nxt hnxt using hstep
  let s : ∀ n : ℕ, {f // P (2 ^ n * r) f} := fun n => Nat.rec ⟨fr, hP0⟩ nxt n
  have hmono : ∀ {m n : ℕ}, m ≤ n →
      Metric.ball (0 : E) (2 ^ m * r) ⊆ Metric.ball 0 (2 ^ n * r) := fun h =>
    Metric.ball_subset_ball (by gcongr; norm_num)
  have hs : ∀ m n, m ≤ n → ∀ i z, z ∈ W i → z ∈ Metric.ball 0 (2 ^ m * r) →
      (s n).1 i z = (s m).1 i z := by
    intro m n hmn i z hi hz
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih => rw [← ih]; exact hnxt n (s n) i z hi (hmono hmn hz)
  have hbig : ∀ t : ℝ, ∃ n : ℕ, t < 2 ^ n * r := fun t => by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (t / r) (one_lt_two (α := ℝ))
    exact ⟨n, (div_lt_iff₀ hr).mp hn⟩
  have hcov' : ∀ z : E, ∃ n : ℕ, z ∈ Metric.ball (0 : E) (2 ^ n * r) := fun z => by
    simpa only [mem_ball_zero_iff] using hbig ‖z‖
  have hglue := fun i : ι => exists_glue (U := W i)
    (A := fun n : ℕ => Metric.ball (0 : E) (2 ^ n * r)) (F := fun n => (s n).1 i)
    (fun _ => Metric.isOpen_ball) hcov' (fun n => (s n).2.1 i)
    (fun m n z hi hm hn => by
      rcases le_total m n with h | h
      · exact (hs m n h i z hi hm).symm
      · exact hs n m h i z hi hn)
  choose fr' hd hfr' using hglue
  refine ⟨fr', hd, fun i z hi => ?_, fun i j z hi hj => ?_, fun i z hi hz => ?_, fun j x hj => ?_⟩
  · obtain ⟨n, hn⟩ := hcov' z
    rw [hfr' i n z hi hn]
    exact (s n).2.2.1 i z hi hn
  · obtain ⟨n, hn⟩ := hcov' z
    rw [hfr' i n z hi hn, hfr' j n z hj hn]
    exact (s n).2.2.2.1 i j z hi hj hn
  · exact hfr' i 0 z hi (by simpa using hz)
  · obtain ⟨n, hn⟩ := hbig (∑ a, ‖x a‖)
    have hb : ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ Metric.ball (0 : E) (2 ^ n * r) := fun I => by
      rw [mem_ball_zero_iff]
      exact ((norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ I) fun _ _ _ => norm_nonneg _)).trans_lt hn
    rw [(s n).2.2.2.2 j x hj hb]
    congr 1
    exact Finset.prod_congr rfl fun I _ => by rw [hfr' _ n _ (hj I) (hb I)]
end GlobalTheory.CubeFrame
