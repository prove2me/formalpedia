-- Prove2me | solution 1 for GlobalTheory.mem_span_genEigen_of_finiteDimensional_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:21:30.966545+00:00
-- url     : https://prove2.me/submissions/1309ff0a-c8b5-4266-8942-4c999c2471b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSpanGenEigenOfFiniteDimensionalOrbit
import Theorems.Thm_GlobalTheory_GenEigenFinOrbit_foldr_eq_prod
import Theorems.Thm_GlobalTheory_GenEigenFinOrbit_map_prod_eq_bot
import Theorems.Thm_GlobalTheory_GenEigenFinOrbit_exists_common_kernel
import Theorems.Thm_GlobalTheory_GenEigenFinOrbit_sub_pow_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
open GenEigenFinOrbit
namespace GlobalTheory
theorem _root_.solution :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (A : Subalgebra ℂ (Module.End ℂ V)),
    (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → ∀ (X' : Set (Module.End ℂ V → ℂ)) (D : ℕ) (ψ : V),
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A)) →
    Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A)) ≤ D →
    (∀ (χ' : Module.End ℂ V → ℂ) (u : V),
      u ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) → u ≠ 0 →
      (∀ z ∈ A, z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ A, χ' z = χ z) →
    ψ ∈ Submodule.span ℂ {ψ' | ψ' ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) ∧
      ∃ χ ∈ X', ∀ zs : List (Module.End ℂ V), zs.length = D → (∀ z ∈ zs, z ∈ A) →
        zs.foldr (fun z f => z f - χ z • f) ψ' = 0} := by
  intro V _ _ A hA X' D ψ hfin hD hX
  set U := Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) with hU
  have hUst : ∀ z ∈ A, Set.MapsTo z U U := by
    intro z hz
    have : U.map z ≤ U := by
      rw [hU, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨z * w, A.mul_mem hz hw, rfl⟩
    exact fun u hu => this ⟨u, hu, rfl⟩
  have hψU : ψ ∈ U := Submodule.subset_span ⟨1, A.one_mem, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : A → End ℂ U, ∀ (i : A) (u : U), (f i u : V) = (i : End ℂ V) u :=
    ⟨fun i => (i : End ℂ V).restrict (hUst i i.2), fun _ _ => rfl⟩
  have hcommAll : ∀ i j, Commute (f i) (f j) := by
    intro i j
    show f i * f j = f j * f i
    ext u
    have := congrArg (fun T : End ℂ V => T (u : V)) (hA i i.2 j j.2)
    simpa [Module.End.mul_apply, hf] using this
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    f (fun i j _ => hcommAll i j) (fun i => Module.End.iSup_maxGenEigenspace_eq_top _)
  set T := {ψ' | ψ' ∈ U ∧ ∃ χ ∈ X', ∀ zs : List (Module.End ℂ V), zs.length = D →
        (∀ z ∈ zs, z ∈ A) → zs.foldr (fun z f => z f - χ z • f) ψ' = 0} with hT
  have key : ∀ χ : A → ℂ, ∀ x ∈ ⨅ i, (f i).maxGenEigenspace (χ i),
      (x : V) ∈ Submodule.span ℂ T := by
    classical
    intro χ x hx
    set N := (⨅ i, (f i).maxGenEigenspace (χ i)).map U.subtype with hNdef
    have hxN : (x : V) ∈ N := ⟨x, hx, rfl⟩
    have hNU : N ≤ U := by
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    haveI : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le hNU
    obtain ⟨χ', hχ'⟩ : ∃ χ' : End ℂ V → ℂ, ∀ z (hz : z ∈ A), χ' z = χ ⟨z, hz⟩ :=
      ⟨fun y => if h : y ∈ A then χ ⟨y, h⟩ else 0, fun z hz => dif_pos hz⟩
    set G : Set (End ℂ V) := {g | ∃ z ∈ A, g = z - algebraMap ℂ _ (χ' z)} with hG
    have hGA : ∀ g ∈ G, g ∈ A := by
      rintro _ ⟨z, hz, rfl⟩
      exact A.sub_mem hz (A.algebraMap_mem _)
    have hcommG : ∀ a ∈ G, ∀ b ∈ G, a * b = b * a :=
      fun a ha b hb => hA a (hGA a ha) b (hGA b hb)
    have hNst : ∀ z ∈ A, N.map z ≤ N := by
      rintro z hz _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨f ⟨z, hz⟩ y, ?_, hf ⟨z, hz⟩ y⟩
      simp only [SetLike.mem_coe, Submodule.mem_iInf] at hy ⊢
      intro i
      exact Module.End.mapsTo_maxGenEigenspace_of_comm (hcommAll i ⟨z, hz⟩) (χ i) (hy i)
    have hstG : ∀ g ∈ G, N.map g ≤ N := by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨v, hv, rfl⟩
      simp only [LinearMap.sub_apply, Module.algebraMap_end_apply]
      exact N.sub_mem (hNst z hz ⟨v, hv, rfl⟩) (N.smul_mem _ hv)
    have hnil : ∀ g ∈ G, ∀ n ∈ N, (g ^ finrank ℂ U) n = 0 := by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨y, hy, rfl⟩
      have hy' := (Submodule.mem_iInf _).1 (SetLike.mem_coe.1 hy) ⟨z, hz⟩
      rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.mem_genEigenspace_nat,
        LinearMap.mem_ker] at hy'
      rw [hχ' z hz, Submodule.subtype_apply, ← sub_pow_coe z (f ⟨z, hz⟩) (hf ⟨z, hz⟩), hy']
      rfl
    by_cases hN : N = ⊥
    · rw [hN, Submodule.mem_bot] at hxN
      rw [hxN]
      exact zero_mem _
    obtain ⟨n, hnN, hn0, hnker⟩ := exists_common_kernel G N (finrank ℂ U) hcommG hstG hnil hN
    have heig : ∀ z ∈ A, z n = χ' z • n := by
      intro z hz
      have := hnker _ ⟨z, hz, rfl⟩
      simpa [sub_eq_zero] using this
    obtain ⟨χ0, hχ0X, hχ0⟩ := hX χ' n (hNU hnN) hn0 heig
    apply Submodule.subset_span
    refine ⟨hNU hxN, χ0, hχ0X, fun zs hlen hzs => ?_⟩
    rw [foldr_eq_prod]
    have hmap : zs.map (fun z => z - algebraMap ℂ (End ℂ V) (χ0 z)) =
        zs.map (fun z => z - algebraMap ℂ (End ℂ V) (χ' z)) :=
      List.map_congr_left fun z hz => by rw [hχ0 z (hzs z hz)]
    rw [hmap]
    have hbot := map_prod_eq_bot G N (finrank ℂ U) hcommG hstG hnil
      (zs.map fun z => z - algebraMap ℂ (End ℂ V) (χ' z))
      (by
        intro g hg
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hg
        exact ⟨z, hzs z hz, rfl⟩)
      (by rw [List.length_map, hlen]; exact (Submodule.finrank_mono hNU).trans hD)
    have hmem : (zs.map fun z => z - algebraMap ℂ (End ℂ V) (χ' z)).prod (x : V) ∈
        N.map (zs.map fun z => z - algebraMap ℂ (End ℂ V) (χ' z)).prod := ⟨_, hxN, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hmem
  have hmem : (⟨ψ, hψU⟩ : U) ∈ ⨆ χ : A → ℂ, ⨅ i, (f i).maxGenEigenspace (χ i) := by
    rw [htop]; exact Submodule.mem_top
  exact Submodule.iSup_induction _ (motive := fun x : U => (x : V) ∈ Submodule.span ℂ T) hmem key
    (by simp) (fun x y hx hy => by simpa using add_mem hx hy)
end GlobalTheory
