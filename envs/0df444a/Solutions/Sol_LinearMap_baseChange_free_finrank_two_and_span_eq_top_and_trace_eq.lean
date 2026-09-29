-- Prove2me | solution 1 for LinearMap.baseChange_free_finrank_two_and_span_eq_top_and_trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/2c7551bb-0b19-569c-86fb-d97611fa8f57

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_baseChange_free_finrank_two_and_span_eq_top_and_trace_eq

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped TensorProduct

theorem solution
    {R : Type} [CommRing R] {k : Type} [CommRing k] [Algebra R k] [Nontrivial k]
    {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V] (hV : Module.finrank R V = 2)
    (ρV : G →* Module.End R V) (hspan : Submodule.span R (Set.range ⇑ρV) = ⊤) :
    Module.finrank k (k ⊗[R] V) = 2 ∧
    Submodule.span k (Set.range (fun g : G => (ρV g).baseChange k)) = ⊤ ∧
    (∀ g : G, LinearMap.trace k (k ⊗[R] V) ((ρV g).baseChange k) = algebraMap R k (LinearMap.trace R V (ρV g))) ∧
    (∀ (g : G) (v : V), ((ρV g).baseChange k) ((1 : k) ⊗ₜ[R] v) = (1 : k) ⊗ₜ[R] (ρV g v)) ∧
    (Function.Injective (algebraMap R k) → Function.Injective (fun v : V => (1 : k) ⊗ₜ[R] v)) := by
  classical

  haveI : Nontrivial R := by
    rcases subsingleton_or_nontrivial R with h | h
    · exfalso
      have : Module.finrank R V = 1 := by simp [Module.finrank]
      omega
    · exact h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [Module.finrank_baseChange, hV]
  ·
    let b : Module.Basis (Fin 2) R V := Module.finBasisOfFinrankEq R V hV
    let bk := Algebra.TensorProduct.basis k b
    set S : Submodule k (Module.End k (k ⊗[R] V)) :=
      Submodule.span k (Set.range (fun g : G => (ρV g).baseChange k)) with hS

    have hmem : ∀ f : Module.End R V, f.baseChange k ∈ S := by
      intro f
      have hf : f ∈ Submodule.span R (Set.range ⇑ρV) := by rw [hspan]; trivial
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        exact Submodule.subset_span ⟨g, rfl⟩
      | zero => rw [LinearMap.baseChange_zero]; exact S.zero_mem
      | add x y _ _ hx hy => rw [LinearMap.baseChange_add]; exact S.add_mem hx hy
      | smul r x _ hx => rw [LinearMap.baseChange_smul]; exact S.smul_of_tower_mem r hx
    apply top_unique
    rw [← bk.end.span_eq, Submodule.span_le]
    rintro _ ⟨ij, rfl⟩
    rw [← Module.Basis.baseChange_end]
    exact hmem _
  ·
    intro g
    exact LinearMap.trace_baseChange (ρV g) k
  ·
    intro g v
    rfl
  ·
    intro hinj
    have h1 : Function.Injective ((Algebra.linearMap R k).rTensor V) :=
      Module.Flat.rTensor_preserves_injective_linearMap (M := V) (Algebra.linearMap R k) hinj
    have h2 : Function.Injective (TensorProduct.lid R V).symm := (TensorProduct.lid R V).symm.injective
    have h3 : (fun v : V => (1 : k) ⊗ₜ[R] v) = ((Algebra.linearMap R k).rTensor V) ∘ (TensorProduct.lid R V).symm := by
      funext v
      simp [LinearMap.rTensor_tmul]
    rw [h3]
    exact h1.comp h2

end S_LinearMap_baseChange_free_finrank_two_and_span_eq_top_and_trace_eq
end P2MW
export P2MW.S_LinearMap_baseChange_free_finrank_two_and_span_eq_top_and_trace_eq (solution)
