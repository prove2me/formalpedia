-- Prove2me | solution 1 for GroundTheory.Automorphic.PeterssonComplement.exists_apply_eq_zero_inner_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:56.26636+00:00
-- url     : https://prove2.me/submissions/d400f058-98df-434b-a241-bc79868f388f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_PeterssonComplement
import Theorems.Thm_GroundTheory_Automorphic_PeterssonComplement_inner_aeval_map_left
import Theorems.Thm_GroundTheory_Automorphic_PeterssonComplement_aeval_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.PeterssonComplement
open Polynomial
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H)
variable {ι}
namespace GroundTheory.Automorphic.PeterssonComplement
theorem _root_.solution (hι : Function.Injective ι) {T : Module.End ℂ V}
    (hT : ∀ x y, inner ℂ (ι (T x)) (ι y) = inner ℂ (ι x) (ι (T y))) (p : ℝ[X])
    (Z : Submodule ℂ V) [FiniteDimensional ℂ Z] (hZ : ∀ z ∈ Z, T z ∈ Z) {x : V} (hx : x ∈ Z) :
    ∃ m ∈ Z, aeval T (p.map (algebraMap ℝ ℂ)) m = 0 ∧
      ∀ w, aeval T (p.map (algebraMap ℝ ℂ)) w = 0 →
        inner ℂ (ι x) (ι w) = inner ℂ (ι m) (ι w) := by
  set S := aeval T (p.map (algebraMap ℝ ℂ)) with hS
  have hSym : ∀ a b, inner ℂ (ι (S a)) (ι b) = inner ℂ (ι a) (ι (S b)) :=
    inner_aeval_map_left hT p
  have hSZ : ∀ z ∈ Z, S z ∈ Z := aeval_mem hZ _
  set S' : Z →ₗ[ℂ] Z := S.restrict hSZ with hS'
  have hdisj : Disjoint (LinearMap.ker S') (LinearMap.range S') := by
    rw [Submodule.disjoint_def]
    rintro y hyk ⟨z, rfl⟩
    have h1 : S (S z) = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 hyk)
    have h2 : inner ℂ (ι (S z)) (ι (S z)) = 0 := by rw [hSym, h1, map_zero, inner_zero_right]
    rw [inner_self_eq_zero, ← map_zero ι] at h2
    exact Subtype.ext (hι h2)
  have hcompl : IsCompl (LinearMap.ker S') (LinearMap.range S') :=
    (Submodule.isCompl_iff_disjoint _ _ (by
      rw [add_comm, LinearMap.finrank_range_add_finrank_ker])).2 hdisj
  obtain ⟨m, hm, r, ⟨z, rfl⟩, hmr⟩ :=
    Submodule.mem_sup.1 (hcompl.sup_eq_top ▸ Submodule.mem_top : (⟨x, hx⟩ : Z) ∈ _)
  refine ⟨m, m.2, congrArg Subtype.val (LinearMap.mem_ker.1 hm), fun w hw => ?_⟩
  have hxe : x = (m : V) + S z := congrArg Subtype.val hmr.symm
  rw [hxe, map_add, inner_add_left, hSym, hw, map_zero, inner_zero_right, add_zero]
end GroundTheory.Automorphic.PeterssonComplement
