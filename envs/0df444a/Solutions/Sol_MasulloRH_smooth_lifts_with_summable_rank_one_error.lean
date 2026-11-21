-- Prove2me | solution 1 for MasulloRH.smooth_lifts_with_summable_rank_one_error
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-21T04:35:28.798846+00:00
-- url     : https://prove2.me/submissions/9c391353-251d-41ae-8979-cfdf5948525d

import Theorems.Thm_MasulloRH_lifted_rank_one_schatten_norms

open MasulloGRH MasulloRH InnerProductSpace

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K F : Submodule ℂ H) (hd : K ≤ (K ⊓ F).topologicalClosure)
    (u η : ℕ → H) (hu : ∀ i, ∃ w ∈ F, w - u i ∈ K)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : ℕ → H, (∀ i, v i ∈ F ∧ v i - u i ∈ K ∧ ‖v i - u i‖ < r i) ∧
      ∀ A : H →L[ℂ] H,
        let e := fun i => traceNorm (rankOne ℂ (A (v i - u i)) (η i))
        Summable e ∧ ∑' i, e i ≤ ‖A‖ * ε := by
  classical
  let d := fun i : ℕ => ε/2/2^i
  have hdpos (i : ℕ) : 0 < d i := by dsimp [d]; positivity
  have hsum : HasSum d ε := hasSum_geometric_two' ε
  have hchoose (i : ℕ) : ∃ w ∈ F, w-u i ∈ K ∧ ‖w-u i‖ < r i ∧
      ‖w-u i‖ * ‖η i‖ ≤ d i := by
    obtain ⟨w, hw, hwK⟩ := hu i
    let δ := min (r i) (d i/(1+‖η i‖))
    have hδ : 0 < δ := lt_min (hr i) (div_pos (hdpos i) (by positivity))
    have hc : w-u i ∈ closure ((K ⊓ F : Submodule ℂ H) : Set H) := hd hwK
    obtain ⟨k, hk, hdist⟩ := Metric.mem_closure_iff.mp hc δ hδ
    have he : ‖w-k-u i‖ < δ := by
      rw [dist_eq_norm] at hdist
      rwa [show w-k-u i = (w-u i)-k by abel]
    refine ⟨w-k, F.sub_mem hw hk.2, ?_, he.trans_le (min_le_left _ _), ?_⟩
    · rw [show w-k-u i = (w-u i)-k by abel]
      exact K.sub_mem hwK hk.1
    · have h := (lt_div_iff₀ (by positivity : 0 < 1+‖η i‖)).mp
          (he.trans_le (min_le_right _ _))
      nlinarith [norm_nonneg (w-k-u i)]
  choose v hv hK hclose hcost using hchoose
  refine ⟨v, fun i => ⟨hv i, hK i, hclose i⟩, ?_⟩
  intro A
  let e := fun i => traceNorm (rankOne ℂ (A (v i-u i)) (η i))
  have en (i : ℕ) : 0 ≤ e i := by
    rw [show e i = _ from (lifted_rank_one_schatten_norms _ _).1]
    positivity
  have hle (i : ℕ) : e i ≤ ‖A‖ * d i := by
    calc
      e i = ‖A (v i-u i)‖ * ‖η i‖ := (lifted_rank_one_schatten_norms _ _).1
      _ ≤ (‖A‖ * ‖v i-u i‖) * ‖η i‖ :=
        mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
      _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hcost i) (norm_nonneg _)
  have hm := hsum.mul_left ‖A‖
  have he := hm.summable.of_nonneg_of_le en hle
  exact ⟨he, hm.tsum_eq ▸ he.tsum_le_tsum hle hm.summable⟩
