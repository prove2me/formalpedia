-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.of_norm_sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:25:41.082511+00:00
-- url     : https://prove2.me/submissions/4e2e6d0f-a46b-47bd-9483-c4605f6253be

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCriterion
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_surjective_pow_of_norm
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_norm_sub_pow_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime]
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]
    [CompleteSpace F] (p : ℕ) [Fact p.Prime] (hp : ‖(p : F)‖ < 1)
    (hnd : ∀ r : ℝ, r < 1 → ∃ x : F, r < ‖x‖ ∧ ‖x‖ < 1) {π : F} (hπ : ‖π‖ < 1)
    (h : ∀ x : F, ‖x‖ ≤ 1 → ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖π‖ ^ p) : IsPerfectoidField F p := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set c := ‖π‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _

  have key : ∀ x : F, ‖x‖ ≤ 1 → ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖(p : F)‖ := by
    intro x hx
    by_cases hpz : (p : F) = 0
    ·
      have hstep : ∀ (k : ℕ) (z : F), ‖z‖ ≤ 1 → ‖x - z ^ p‖ ≤ c ^ (p * k) →
          ∃ z' : F, ‖z'‖ ≤ 1 ∧ ‖z' - z‖ ≤ c ^ k ∧ ‖x - z' ^ p‖ ≤ c ^ (p * (k + 1)) := by
        intro k z hz hxz
        obtain ⟨z', h1, h2, h3⟩ := exists_norm_sub_pow_step p hπ.le h hz hxz
        refine ⟨z', h1, h2, h3.trans (max_le le_rfl ?_)⟩
        rw [hpz, norm_zero, zero_mul]
        exact pow_nonneg hc0 _
      let S : ℕ → Type _ := fun k => {z : F // ‖z‖ ≤ 1 ∧ ‖x - z ^ p‖ ≤ c ^ (p * k)}
      let next : (k : ℕ) → S k → S (k + 1) := fun k z =>
        ⟨Classical.choose (hstep k z.1 z.2.1 z.2.2),
          (Classical.choose_spec (hstep k z.1 z.2.1 z.2.2)).1,
          (Classical.choose_spec (hstep k z.1 z.2.1 z.2.2)).2.2⟩
      have hnext : ∀ (k : ℕ) (z : S k), ‖(next k z).1 - z.1‖ ≤ c ^ k := fun k z =>
        (Classical.choose_spec (hstep k z.1 z.2.1 z.2.2)).2.1
      have base : ‖x - (0 : F) ^ p‖ ≤ c ^ (p * 0) := by
        rw [mul_zero, pow_zero, zero_pow hp0, sub_zero]; exact hx
      let s : (k : ℕ) → S k := fun k => Nat.rec ⟨0, by simp, base⟩ next k
      let z : ℕ → F := fun k => (s k).1
      have hdist : ∀ k, dist (z k) (z (k + 1)) ≤ 1 * c ^ k := by
        intro k
        rw [one_mul, dist_comm, dist_eq_norm]
        exact hnext k (s k)
      have hcau : CauchySeq z := cauchySeq_of_le_geometric c 1 hπ hdist
      obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
      have hL1 : ‖L‖ ≤ 1 := le_of_tendsto' hL.norm fun k => (s k).2.1
      refine ⟨L, hL1, ?_⟩
      have ht0 : Filter.Tendsto (fun k => c ^ (p * k)) Filter.atTop (nhds 0) := by
        simp_rw [pow_mul]
        exact tendsto_pow_atTop_nhds_zero_of_lt_one (pow_nonneg hc0 _)
          (pow_lt_one₀ hc0 hπ hp0)
      have h1 : Filter.Tendsto (fun k => ‖x - z k ^ p‖) Filter.atTop (nhds 0) :=
        squeeze_zero (fun _ => norm_nonneg _) (fun k => (s k).2.2) ht0
      have h2 : Filter.Tendsto (fun k => ‖x - z k ^ p‖) Filter.atTop (nhds ‖x - L ^ p‖) :=
        (tendsto_const_nhds.sub (hL.pow p)).norm
      rw [tendsto_nhds_unique h2 h1]
      exact norm_nonneg _
    ·
      have hpos : 0 < ‖(p : F)‖ := norm_pos_iff.2 hpz
      have hind : ∀ k : ℕ, ∃ z : F, ‖z‖ ≤ 1 ∧
          (‖x - z ^ p‖ ≤ ‖(p : F)‖ ∨ ‖x - z ^ p‖ ≤ c ^ (p * k)) := by
        intro k
        induction k with
        | zero =>
          refine ⟨0, by simp, Or.inr ?_⟩
          rw [mul_zero, pow_zero, zero_pow hp0, sub_zero]; exact hx
        | succ k ih =>
          obtain ⟨z, hz, hz'⟩ := ih
          rcases hz' with hz' | hz'
          · exact ⟨z, hz, Or.inl hz'⟩
          · obtain ⟨z', h1, -, h3⟩ := exists_norm_sub_pow_step p hπ.le h hz hz'
            refine ⟨z', h1, ?_⟩
            rcases le_total (c ^ (p * (k + 1))) (‖(p : F)‖ * c ^ k) with hle | hle
            · left
              refine h3.trans ((max_eq_right hle).le.trans ?_)
              exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hc0 hπ.le)
            · right
              exact h3.trans (max_eq_left hle).le
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos hπ
      obtain ⟨z, hz, hz'⟩ := hind n
      refine ⟨z, hz, hz'.elim id fun h' => h'.trans ?_⟩
      refine le_trans ?_ hn.le
      exact pow_le_pow_of_le_one hc0 hπ.le (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hp0))
  exact
    { complete := inferInstance
      norm_natCast_lt_one := hp
      exists_norm_mem_Ioo := hnd
      surjective_pow := surjective_pow_of_norm p key }
end GroundTheory.PAdicHodge.IsPerfectoidField
