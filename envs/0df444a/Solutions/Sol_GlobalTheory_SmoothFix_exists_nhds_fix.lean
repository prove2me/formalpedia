-- Prove2me | solution 1 for GlobalTheory.SmoothFix.exists_nhds_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:04:19.782561+00:00
-- url     : https://prove2.me/submissions/dac3033c-e4bd-4db0-8d50-8dded860b357

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNhdsFixOfContinuousCoefficients
import Theorems.Thm_GlobalTheory_SmoothFix_eq_one_of_pow_norm_sub_one_le_half

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter
open GlobalTheory GlobalTheory.SmoothFix
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace GlobalTheory.SmoothFix
theorem _root_.solution : (∀ {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V),
    (∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) → FiniteDimensional ℂ (Submodule.span ℂ s)) →
  ∀ {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G) {V : Type} [AddCommGroup V] [Module ℂ V]
    (S : G → Module.End ℂ V), (∀ x ∈ H, ∀ y ∈ H, S (x * y) = S x * S y) → S 1 = 1 →
    (∀ (l : V →ₗ[ℂ] ℂ) (w : V), ContinuousOn (fun x => l (S x w)) (H : Set G)) →
    (∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, K ≤ H ∧ IsCompact (K : Set G) ∧
      (∃ O : Set G, IsOpen O ∧ (1 : G) ∈ O ∧ ∀ x ∈ O, x ∈ H → x ∈ K) ∧ (K : Set G) ⊆ U) →
    ∀ v : V, ∃ U ∈ 𝓝 (1 : G), ∀ x ∈ U, x ∈ H → S x v = v := by
  intro hfd G _ _ H V _ _ S hmul h1 hcont hsmall v
  obtain ⟨K₀, hK₀H, hK₀c, ⟨O₀, hO₀o, hO₀1, hO₀K⟩, -⟩ := hsmall Set.univ univ_mem
  let s : Set V := (fun k => S k v) '' (K₀ : Set G)
  have hb : ∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C := by
    intro l
    obtain ⟨C, hC⟩ := hK₀c.exists_bound_of_continuousOn ((hcont l v).mono hK₀H)
    exact ⟨C, by rintro _ ⟨k, hk, rfl⟩; exact hC k hk⟩
  haveI : FiniteDimensional ℂ (Submodule.span ℂ s) := hfd s hb
  set W := Submodule.span ℂ s with hW
  have hinv : ∀ k ∈ K₀, ∀ w ∈ W, S k w ∈ W := by
    intro k hk w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k', hk', rfl⟩ := hx
      show S k (S k' v) ∈ W
      rw [← Module.End.mul_apply, ← hmul k (hK₀H hk) k' (hK₀H hk')]
      exact Submodule.subset_span ⟨k * k', K₀.mul_mem hk hk', rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact W.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact W.smul_mem c hx
  let R : K₀ → Module.End ℂ W := fun k => (S k).restrict (hinv k.1 k.2)
  have hRv : ∀ (k : K₀) (w : W), (R k w : V) = S k w := fun _ _ => rfl
  have hRpow : ∀ (k : K₀) (m : ℕ), R (k ^ m) = R k ^ m := by
    intro k m
    induction m with
    | zero =>
      ext w
      simp [hRv, h1]
    | succ m ih =>
      ext w
      rw [pow_succ, pow_succ, Module.End.mul_apply, ← ih, hRv, hRv, hRv]
      have hm : ((k ^ m : K₀) : G) ∈ H := hK₀H (k ^ m).2
      simp only [Subgroup.coe_mul]
      rw [hmul _ hm _ (hK₀H k.2), Module.End.mul_apply]
  let b := Module.finBasis ℂ W
  choose c hc using fun i => LinearMap.exists_extend (b.coord i)
  let M : G → Matrix (Fin (Module.finrank ℂ W)) (Fin (Module.finrank ℂ W)) ℂ := fun x i j => c i (S x (b j))
  have hMR : ∀ k : K₀, LinearMap.toMatrixAlgEquiv b (R k) = M k := by
    intro k
    ext i j
    rw [LinearMap.toMatrixAlgEquiv_apply]
    have := LinearMap.congr_fun (hc i) (R k (b j))
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply] at this
    rw [← this, hRv]
  have hR1 : R 1 = 1 := by
    ext w
    simp [hRv, h1]
  have hM1 : M 1 = 1 := by
    have := hMR 1
    rw [hR1, map_one] at this
    simpa using this.symm
  have hM : ContinuousOn M (H : Set G) :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hcont (c i) (b j)
  have hN : ContinuousWithinAt (fun x => ‖M x - 1‖) (H : Set G) 1 :=
    ((hM 1 H.one_mem).sub continuousWithinAt_const).norm
  have hev : {x | ‖M x - 1‖ < 1 / 2} ∈ 𝓝[(H : Set G)] 1 :=
    hN (Iio_mem_nhds (by show ‖M 1 - 1‖ < 1 / 2; rw [hM1, sub_self, norm_zero]; norm_num))
  obtain ⟨u, hu, h1u, hsub⟩ := mem_nhdsWithin.1 hev
  obtain ⟨K, hKH, -, ⟨O, hOo, hO1, hOK⟩, hKU⟩ :=
    hsmall (u ∩ O₀) (Filter.inter_mem (hu.mem_nhds h1u) (hO₀o.mem_nhds hO₀1))
  have hvW : v ∈ W := Submodule.subset_span ⟨1, K₀.one_mem, by simp [h1]⟩
  refine ⟨O, hOo.mem_nhds hO1, fun x hxO hxH => ?_⟩
  have hxK : x ∈ K := hOK x hxO hxH
  have hxK₀ : x ∈ K₀ := hO₀K x (hKU hxK).2 (hKH hxK)
  let kk : K₀ := ⟨x, hxK₀⟩
  have hpow : ∀ m : ℕ, ‖(LinearMap.toMatrixAlgEquiv b (R kk)) ^ m - 1‖ ≤ 1 / 2 := by
    intro m
    rw [← map_pow, ← hRpow, hMR]
    have hm : x ^ m ∈ K := K.pow_mem hxK m
    have := hsub ⟨(hKU hm).1, hKH hm⟩
    exact le_of_lt (by simpa using this)
  have hone := eq_one_of_pow_norm_sub_one_le_half hpow
  rw [← map_one (LinearMap.toMatrixAlgEquiv b)] at hone
  have hRk := (LinearMap.toMatrixAlgEquiv b).injective hone
  have := congrArg Subtype.val (LinearMap.congr_fun hRk ⟨v, hvW⟩)
  simpa [hRv] using this
end GlobalTheory.SmoothFix
