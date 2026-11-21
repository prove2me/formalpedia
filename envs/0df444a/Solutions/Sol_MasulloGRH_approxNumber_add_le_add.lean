-- Prove2me | solution 1 for MasulloGRH.approxNumber_add_le_add
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:59:36.055161+00:00
-- url     : https://prove2.me/submissions/7eda948c-c9bd-42f6-8d81-11e8fc27bffe

import Mathlib
import Definitions.Def_MasulloGRH_ApproximationNumbers

/-!
# Approximation-number inequalities

The index is one-based, as in Masullo (C.3.6.2). The sum inequality
in Lemma C.3.6.3(1) uses index `m + n - 1`. Part (2) is a same-index
Lipschitz estimate. For part (3), the usual product argument gives
the stronger index `m + n - 1`.
-/

open Set

namespace MasulloGRH

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

private theorem approximationErrors_bddBelow (n : ℕ) (A : E →L[𝕜] F) :
    BddBelow (approximationErrors n A) := by
  refine ⟨0, ?_⟩
  rintro r ⟨R, _, rfl⟩
  exact norm_nonneg _

private theorem approximationErrors_nonempty {n : ℕ} (hn : 0 < n) (A : E →L[𝕜] F) :
    (approximationErrors n A).Nonempty := by
  refine ⟨‖A - 0‖, 0, ⟨?_, ?_⟩, rfl⟩
  · change FiniteDimensional 𝕜 (LinearMap.range (0 : E →ₗ[𝕜] F))
    rw [LinearMap.range_zero]
    infer_instance
  · change Module.finrank 𝕜 (LinearMap.range (0 : E →ₗ[𝕜] F)) < n
    rwa [LinearMap.range_zero, finrank_bot]

private theorem approxNumber_le_error {n : ℕ} (A R : E →L[𝕜] F)
    (hR : ApproximationRankBelow n R) : approxNumber n A ≤ ‖A - R‖ :=
  csInf_le (approximationErrors_bddBelow n A) ⟨R, hR, rfl⟩

private theorem approxNumber_mem_closure {n : ℕ} (hn : 0 < n) (A : E →L[𝕜] F) :
    approxNumber n A ∈ closure (approximationErrors n A) :=
  csInf_mem_closure (approximationErrors_nonempty hn A) (approximationErrors_bddBelow n A)

private theorem approxRank_add {m n : ℕ} {R S : E →L[𝕜] F}
    (hR : ApproximationRankBelow m R) (hS : ApproximationRankBelow n S) :
    ApproximationRankBelow (m + n - 1) (R + S) := by
  let P := LinearMap.range (R : E →ₗ[𝕜] F)
  let Q := LinearMap.range (S : E →ₗ[𝕜] F)
  let _ : FiniteDimensional 𝕜 P := hR.1
  let _ : FiniteDimensional 𝕜 Q := hS.1
  have hle : LinearMap.range ((R + S : E →L[𝕜] F) : E →ₗ[𝕜] F) ≤ P ⊔ Q :=
    LinearMap.range_add_le _ _
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  have h₁ := Submodule.finrank_mono hle
  have h₂ := Submodule.finrank_add_le_finrank_add_finrank P Q
  have hR' : Module.finrank 𝕜 P < m := hR.2
  have hS' : Module.finrank 𝕜 Q < n := hS.2
  omega

private theorem approxRank_precomp {n : ℕ} {R : F →L[𝕜] G}
    (hR : ApproximationRankBelow n R) (B : E →L[𝕜] F) :
    ApproximationRankBelow n (R.comp B) := by
  let _ : FiniteDimensional 𝕜 (LinearMap.range (R : F →ₗ[𝕜] G)) := hR.1
  have hle : LinearMap.range ((R.comp B : E →L[𝕜] G) : E →ₗ[𝕜] G) ≤
      LinearMap.range (R : F →ₗ[𝕜] G) :=
    LinearMap.range_comp_le_range _ _
  exact ⟨Submodule.finiteDimensional_of_le hle, (Submodule.finrank_mono hle).trans_lt hR.2⟩

private theorem approxRank_postcomp {n : ℕ} {S : E →L[𝕜] F}
    (hS : ApproximationRankBelow n S) (A : F →L[𝕜] G) :
    ApproximationRankBelow n (A.comp S) := by
  let _ : FiniteDimensional 𝕜 (LinearMap.range (S : E →ₗ[𝕜] F)) := hS.1
  have hRange : LinearMap.range ((A.comp S : E →L[𝕜] G) : E →ₗ[𝕜] G) =
      (LinearMap.range (S : E →ₗ[𝕜] F)).map (A : F →ₗ[𝕜] G) :=
    LinearMap.range_comp (S : E →ₗ[𝕜] F) (A : F →ₗ[𝕜] G)
  unfold ApproximationRankBelow
  rw [hRange]
  exact ⟨inferInstance, (Submodule.finrank_map_le _ _).trans_lt hS.2⟩

private theorem le_binary_of_le_errors {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {A : E →L[𝕜] F} {B : F →L[𝕜] G}
    {c : ℝ} {f : ℝ → ℝ → ℝ}
    (hleft : ∀ y, Continuous (fun x ↦ f x y))
    (hright : ∀ x, Continuous (fun y ↦ f x y))
    (hle : ∀ x ∈ approximationErrors m A, ∀ y ∈ approximationErrors n B, c ≤ f x y) :
    c ≤ f (approxNumber m A) (approxNumber n B) := by
  have hFor (y : ℝ) (hy : y ∈ approximationErrors n B) : c ≤ f (approxNumber m A) y :=
    closure_minimal (t := {x | c ≤ f x y}) (fun x hx ↦ hle x hx y hy)
      (isClosed_le continuous_const (hleft y)) (approxNumber_mem_closure hm A)
  exact closure_minimal (t := {y | c ≤ f (approxNumber m A) y}) (fun y hy ↦ hFor y hy)
    (isClosed_le continuous_const (hright _)) (approxNumber_mem_closure hn B)

private theorem le_add_approxNumber_of_le_errors {n : ℕ} (hn : 0 < n)
    (A : E →L[𝕜] F) {c d : ℝ} (h : ∀ r ∈ approximationErrors n A, c ≤ d + r) :
    c ≤ d + approxNumber n A :=
  closure_minimal (t := {r | c ≤ d + r}) h
    (isClosed_le continuous_const (continuous_const.add continuous_id))
    (approxNumber_mem_closure hn A)

/-- The corrected sum inequality in Lemma C.3.6.3(1). -/
theorem approxNumber_add_le_add {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A B : E →L[𝕜] F) :
    approxNumber (m + n - 1) (A + B) ≤ approxNumber m A + approxNumber n B := by
  have hBound (a : ℝ) (ha : a ∈ approximationErrors m A)
      (b : ℝ) (hb : b ∈ approximationErrors n B) :
      approxNumber (m + n - 1) (A + B) ≤ a + b := by
    obtain ⟨R, hR, rfl⟩ := ha
    obtain ⟨S, hS, rfl⟩ := hb
    calc
      _ ≤ ‖(A + B) - (R + S)‖ := approxNumber_le_error _ _ (approxRank_add hR hS)
      _ = ‖(A - R) + (B - S)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hFirst (b : ℝ) (hb : b ∈ approximationErrors n B) :
      approxNumber (m + n - 1) (A + B) ≤ approxNumber m A + b := by
    rw [add_comm (approxNumber m A) b]
    exact le_add_approxNumber_of_le_errors hm A
      (fun a ha ↦ by simpa only [add_comm b a] using hBound a ha b hb)
  exact le_add_approxNumber_of_le_errors hn B hFirst

/-- Same-index Lipschitz continuity in the operator norm, Lemma C.3.6.3(2). -/
theorem approxNumber_lipschitz {m : ℕ} (hm : 0 < m) (A B : E →L[𝕜] F) :
    |approxNumber m A - approxNumber m B| ≤ ‖A - B‖ := by
  have hBound (A B : E →L[𝕜] F) :
      approxNumber m A ≤ ‖A - B‖ + approxNumber m B := by
    apply le_add_approxNumber_of_le_errors hm B
    rintro r ⟨R, hR, rfl⟩
    calc
      _ ≤ ‖A - R‖ := approxNumber_le_error A R hR
      _ = ‖(A - B) + (B - R)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hAB := hBound A B
  have hBA := hBound B A
  rw [norm_sub_rev] at hBA
  rw [abs_le]
  constructor <;> linarith

/-- A sharper composition bound than the one printed in Lemma C.3.6.3(3). -/
theorem approxNumber_comp_le_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : F →L[𝕜] G) (B : E →L[𝕜] F) :
    approxNumber (m + n - 1) (A.comp B) ≤ approxNumber m A * approxNumber n B := by
  rw [mul_comm]
  apply le_binary_of_le_errors hn hm (f := (· * ·)) (fun _ ↦ continuous_id.mul_const _)
    (fun _ ↦ continuous_const.mul continuous_id)
  rintro b ⟨S, hS, rfl⟩ a ⟨R, hR, rfl⟩
  let T := R.comp B + (A - R).comp S
  have hT : ApproximationRankBelow (m + n - 1) T :=
    approxRank_add (approxRank_precomp hR B) (approxRank_postcomp hS (A - R))
  have heq : A.comp B - T = (A - R).comp (B - S) := by
    ext x
    simp only [T, sub_apply, ContinuousLinearMap.comp_apply,
      add_apply, map_sub]
    abel
  calc
    _ ≤ ‖A.comp B - T‖ := approxNumber_le_error _ _ hT
    _ = ‖(A - R).comp (B - S)‖ := congrArg norm heq
    _ ≤ ‖A - R‖ * ‖B - S‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = _ := mul_comm _ _

/-- The approximation numbers decrease with the allowed rank. -/
theorem approxNumber_antitone_of_pos {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (A : E →L[𝕜] F) : approxNumber n A ≤ approxNumber m A := by
  apply le_csInf (approximationErrors_nonempty hm A)
  rintro r ⟨R, hR, rfl⟩
  exact approxNumber_le_error A R ⟨hR.1, hR.2.trans_le hmn⟩

/-- The literal composition index in Lemma C.3.6.3(3). -/
theorem approxNumber_comp_le_mul_printed {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : F →L[𝕜] G) (B : E →L[𝕜] F) :
    approxNumber (m + n) (A.comp B) ≤ approxNumber m A * approxNumber n B :=
  (approxNumber_antitone_of_pos (by omega) (Nat.sub_le _ _) (A.comp B)).trans
    (approxNumber_comp_le_mul hm hn A B)

end MasulloGRH

open MasulloGRH

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem solution {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A B : E →L[𝕜] F) :
    approxNumber (m + n - 1) (A + B) ≤ approxNumber m A + approxNumber n B :=
  approxNumber_add_le_add hm hn A B
