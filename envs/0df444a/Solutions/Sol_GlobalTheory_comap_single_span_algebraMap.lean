-- Prove2me | solution 1 for GlobalTheory.comap_single_span_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:31:20.037685+00:00
-- url     : https://prove2.me/submissions/674f3fe3-4dc2-4a17-ac43-88b187b8ad54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ComapSingleSpanAlgebraMapNumberField
import Theorems.Thm_GlobalTheory_exists_integral_dual_family

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix
open scoped BigOperators
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (E M : Type) [Field E] [NumberField E] [Field M]
    [NumberField M] [Algebra E M] (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (ι → E)) (τ : ι) :
    (Submodule.span (𝓞 M) ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S)).comap
      (LinearMap.single (𝓞 M) (fun _ : ι => M) τ) =
    Submodule.span (𝓞 M) (algebraMap E M '' ((Submodule.span (𝓞 E) S).comap
      (LinearMap.single (𝓞 E) (fun _ : ι => E) τ) : Set E)) := by
  apply le_antisymm
  · obtain ⟨k, b, l, hl, hy⟩ := exists_integral_dual_family E M
    have key : ∀ j, ∀ w ∈ Submodule.span (𝓞 M)
        ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S), ∀ c : 𝓞 M,
        (fun i => l j ((c : M) * w i)) ∈ Submodule.span (𝓞 E) S := by
      intro j w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, hv, rfl⟩ := hx
        intro c
        obtain ⟨a, ha⟩ := hl j c
        have : (fun i => l j ((c : M) * algebraMap E M (v i))) = a • v := by
          ext i
          rw [mul_comm, ← Algebra.smul_def, map_smul, ha, smul_eq_mul, mul_comm]
          rfl
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span hv)
      | zero =>
        intro c
        have : (fun i => l j ((c : M) * (0 : ι → M) i)) = 0 := by ext i; simp
        rw [this]; exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        intro c
        have : (fun i => l j ((c : M) * (x + y) i)) =
            (fun i => l j ((c : M) * x i)) + (fun i => l j ((c : M) * y i)) := by
          ext i; simp [mul_add]
        rw [this]; exact Submodule.add_mem _ (hx c) (hy c)
      | smul a x _ hx =>
        intro c
        have : (fun i => l j ((c : M) * (a • x) i)) =
            (fun i => l j (((c * a : 𝓞 M) : M) * x i)) := by
          ext i
          congr 1
          rw [Pi.smul_apply, Algebra.smul_def, ← mul_assoc]
          simp
        rw [this]; exact hx _
    intro s hs
    rw [hy s]
    refine Submodule.sum_mem _ fun j _ => ?_
    have h1 : ((b j : 𝓞 M) : M) * algebraMap E M (l j s) = b j • algebraMap E M (l j s) := rfl
    rw [h1]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨l j s, ?_, rfl⟩)
    have h2 := key j _ hs 1
    rw [SetLike.mem_coe, Submodule.mem_comap]
    convert h2 using 1
    ext i
    by_cases h : i = τ
    · subst h; simp
    · simp [h]
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    have key : ∀ v ∈ Submodule.span (𝓞 E) S, (fun i => algebraMap E M (v i)) ∈
        Submodule.span (𝓞 M) ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S) := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero =>
        have : (fun i => algebraMap E M ((0 : ι → E) i)) = 0 := by ext i; simp
        rw [this]; exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        have : (fun i => algebraMap E M ((x + y) i)) =
            (fun i => algebraMap E M (x i)) + (fun i => algebraMap E M (y i)) := by
          ext i; simp
        rw [this]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx =>
        have : (fun i => algebraMap E M ((a • x) i)) =
            algebraMap (𝓞 E) (𝓞 M) a • (fun i => algebraMap E M (x i)) := by
          ext i
          rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul,
            ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
        rw [this]; exact Submodule.smul_mem _ _ hx
    have h2 := key _ hs
    rw [SetLike.mem_coe, Submodule.mem_comap]
    convert h2 using 1
    ext i
    by_cases h : i = τ
    · subst h; simp
    · simp [h]
end GlobalTheory
