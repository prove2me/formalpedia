-- Prove2me | solution 1 for GlobalTheory.ker_le_span_image_ker_of_semilinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:42:42.324679+00:00
-- url     : https://prove2.me/submissions/5f35989b-286f-415b-92ae-485c22694025

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerLeSpanImageKerOfSemilinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K X Y H W : Type) [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup Y] [Module K Y] [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (θ : X →ₗ[K] Y) (j : X →ₛₗ[σ] H) (jW : Y →ₛₗ[σ] W) (T : H →ₗ[ℂ] W), Submodule.span ℂ (Set.range j) = ⊤ → (∀ (n : ℕ) (b : Fin n → Y), LinearIndependent K b → LinearIndependent ℂ fun k => jW (b k)) → (∀ x, T (j x) = jW (θ x)) → LinearMap.ker T ≤ Submodule.span ℂ (j '' (LinearMap.ker θ : Set X)) := by
  intro K X Y H W _ _ _ _ _ _ _ _ _ _ σ θ j jW T hspan hind hT
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker θ)
  let b := Module.finBasis K C
  have hinj : LinearMap.ker (θ ∘ₗ C.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro m hm
    have h1 : (m : X) ∈ LinearMap.ker θ := hm
    have h2 : (m : X) ∈ LinearMap.ker θ ⊓ C := ⟨h1, m.2⟩
    rw [hC.inf_eq_bot] at h2
    exact Subtype.ext (by simpa using h2)
  have hli : LinearIndependent K (fun k => θ (b k : X)) :=
    b.linearIndependent.map' (θ ∘ₗ C.subtype) hinj
  have hli2 := hind _ _ hli
  set N := Submodule.span ℂ (j '' (LinearMap.ker θ : Set X)) with hN
  have hNT : N ≤ LinearMap.ker T := by
    rw [hN, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : θ x = 0 := hx
    show T (j x) = 0
    rw [hT, hx', map_zero]
  have htop : N ⊔ Submodule.span ℂ (Set.range fun k => j (b k : X)) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ LinearMap.ker θ ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    refine Submodule.add_mem_sup (Submodule.subset_span ⟨u, hu, rfl⟩) ?_
    have hcs : c = ∑ k, b.repr ⟨c, hc⟩ k • (b k : X) := by
      have := congrArg (fun z : C => (z : X)) (b.sum_repr ⟨c, hc⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    rw [hcs, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  intro h hh
  have hmem : h ∈ N ⊔ Submodule.span ℂ (Set.range fun k => j (b k : X)) := by
    rw [htop]; trivial
  obtain ⟨u, hu, s, hs, rfl⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hs
  have hTu : T u = 0 := hNT hu
  have h0 : ∑ k, a k • jW (θ (b k : X)) = 0 := by
    have : T (u + ∑ k, a k • j (b k : X)) = 0 := hh
    rw [map_add, hTu, zero_add, map_sum] at this
    simpa [hT] using this
  have ha := Fintype.linearIndependent_iff.1 hli2 a h0
  simpa [ha] using hu
end GlobalTheory
