-- Prove2me | solution 1 for OAI.DiamondDistortion.SegmentSystem.small_color_tail_upper
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:15:25.041815+00:00
-- url     : https://prove2.me/submissions/f308708a-b006-46d5-a1f7-a8c6577c190c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Orthogonality.lean:L67-L133
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.SegmentSystem.small_color_tail_upper. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality
import Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_block_add_sq

-- ---- from OAI.Analysis.DiamondDistortion.SegmentNorm ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace SegmentSystem
variable {ι : Type*} (T : SegmentSystem ι)

variable {T}

variable (T)

lemma primal_eq_zero_iff (u : ι →₀ ℝ) : T.primalSeminorm u = 0 ↔ u = 0 := by
  constructor
  · intro h
    ext v
    have := T.coordinate_le_primal u v
    simpa [h] using this
  · rintro rfl
    exact map_zero _

variable {T}

variable (T)

lemma finiteEmbedding_norm (p : ι →₀ ℝ) :
    ‖T.finiteEmbedding p‖ = T.primalSeminorm p := by
  rw [finiteEmbedding_apply, UniformSpace.Completion.norm_coe]
  rfl

end SegmentSystem

end DiamondDistortion

end

end OAI

-- ---- from OAI.Analysis.DiamondDistortion.Orthogonality ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace SegmentSystem
variable {ι κ : Type*} (T : SegmentSystem ι)

/-- A functional on an orthogonal sum is uniformly small outside finitely many
    components. The proof uses finite blocks only, not a reflexivity library. -/
lemma small_color_tail_upper (c : ι → κ)
    (hsame : ∀ S, T.IsSegment S → ∀ u ∈ S, ∀ v ∈ S, c u=c v)
    (x : T.Dual) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Finset κ, ∀ p : ι →₀ ℝ, (∀ v ∈ p.support, c v ∉ C) →
      x (T.finiteEmbedding p) ≤ ε*T.primalSeminorm p := by
  classical
  by_contra hn
  push Not at hn
  have hchoose (C : Finset κ) : ∃ q : ι →₀ ℝ,
      (∀ v ∈ q.support,c v ∉ C) ∧ T.primalSeminorm q=1 ∧ ε < x (T.finiteEmbedding q) := by
    obtain ⟨p,hout,hval⟩ := hn C
    have hpn0 : T.primalSeminorm p ≠ 0 := by
      intro he
      have hp0 := (T.primal_eq_zero_iff p).mp he
      simp only [hp0,map_zero,mul_zero,lt_self_iff_false] at hval
    have hpn : 0 < T.primalSeminorm p := lt_of_le_of_ne (apply_nonneg _ _) hpn0.symm
    let q := (T.primalSeminorm p)⁻¹ • p
    refine ⟨q, ?_, ?_, ?_⟩
    · intro v hv
      apply hout v
      apply Finsupp.mem_support_iff.mpr
      intro hpv
      have hqv : q v=0 := by simp [q,Finsupp.smul_apply,hpv]
      exact (Finsupp.mem_support_iff.mp hv) hqv
    · simp only [q,map_smul_eq_mul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpn)]
      exact inv_mul_cancel₀ hpn0
    · simp only [q,map_smul,smul_eq_mul]
      rw [inv_mul_eq_div]
      exact (lt_div_iff₀ hpn).mpr hval
  have hblocks : ∀ n : ℕ, ∃ p : ι →₀ ℝ,
      (T.primalSeminorm p)^2 ≤ (n : ℝ) ∧ (n : ℝ)*ε ≤ x (T.finiteEmbedding p) := by
    intro n
    induction n with
    | zero => exact ⟨0,by simp only [map_zero,zero_pow (by decide : 2 ≠ 0),Nat.cast_zero,le_refl],
        by simp only [map_zero,Nat.cast_zero,zero_mul,le_refl]⟩
    | succ n ih =>
      obtain ⟨p,hpn,hpx⟩ := ih
      obtain ⟨q,hqout,hqn,hqx⟩ := hchoose (T.colorSupport c p)
      have hd : Disjoint (T.colorSupport c p) (T.colorSupport c q) := by
        apply Finset.disjoint_left.mpr
        intro a hap haq
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp haq
        exact hqout v hv hap
      refine ⟨p+q, ?_, ?_⟩
      · have h := T.block_add_sq c hsame p q hd
        rw [hqn] at h
        push_cast
        nlinarith
      · simp only [map_add,Nat.cast_add,Nat.cast_one]
        nlinarith
  obtain ⟨n,hn⟩ := exists_nat_gt (‖x‖^2/ε^2)
  have hn0 : (0:ℝ) < n := lt_of_le_of_lt (div_nonneg (sq_nonneg _) (sq_nonneg _)) hn
  have hnε : ‖x‖^2 < (n:ℝ)*ε^2 := (div_lt_iff₀ (sq_pos_of_pos hε)).mp hn
  obtain ⟨p,hpn,hpx⟩ := hblocks n
  have hxb : x (T.finiteEmbedding p) ≤ ‖x‖*T.primalSeminorm p := by
    calc
      _ ≤ ‖x (T.finiteEmbedding p)‖ := Real.le_norm_self _
      _ ≤ ‖x‖*‖T.finiteEmbedding p‖ := x.le_opNorm _
      _ = _ := by rw [T.finiteEmbedding_norm]
  have hprod : (n:ℝ)*ε ≤ ‖x‖*T.primalSeminorm p := hpx.trans hxb
  have hsquare := (sq_le_sq₀ (mul_nonneg hn0.le hε.le)
    (mul_nonneg (norm_nonneg _) (apply_nonneg _ _))).2 hprod
  have hmul := mul_le_mul_of_nonneg_left hpn (sq_nonneg ‖x‖)
  have hcontra := mul_pos hn0 (sub_pos.mpr hnε)
  nlinarith

end SegmentSystem

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.SegmentSystem
open scoped BigOperators Classical Topology
open Set


theorem solution : type_of% @_root_.OAI.DiamondDistortion.SegmentSystem.small_color_tail_upper := @_root_.OAI.DiamondDistortion.SegmentSystem.small_color_tail_upper
