-- Prove2me | solution 1 for IsRegularLocalRing.notMem_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:48.833277+00:00
-- url     : https://prove2.me/submissions/344d20fd-3ca7-46af-8547-f446f2338912

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace IsRegularLocalRing
open IsLocalRing
universe u
private theorem false_of_eq_smul_of_linearIndependent {K M : Type*} {ι : Type*} [Field K]
    [AddCommGroup M] [Module K M] {v : ι → M} (h : LinearIndependent K v) {i j : ι}
    (hij : i ≠ j) (c : K) (he : v j = c • v i) : False := by
  classical
  have key : ∑ k ∈ ({i, j} : Finset ι),
      (fun k => if k = i then c else if k = j then (-1 : K) else 0) k • v k = 0 := by
    rw [Finset.sum_pair hij]
    simp [Ne.symm hij, he]
  have h2 := linearIndependent_iff'.mp h {i, j}
      (fun k => if k = i then c else if k = j then (-1 : K) else 0) key j (by simp)
  simp [Ne.symm hij] at h2
private theorem toCotangent_mul_eq_smul {R : Type*} [CommRing R] [IsLocalRing R] (r a : R)
    (ha : a ∈ IsLocalRing.maximalIdeal R) (hra : r * a ∈ IsLocalRing.maximalIdeal R) :
    ((IsLocalRing.maximalIdeal R).toCotangent ⟨r * a, hra⟩ : IsLocalRing.CotangentSpace R) =
      algebraMap R (IsLocalRing.ResidueField R) r •
        ((IsLocalRing.maximalIdeal R).toCotangent ⟨a, ha⟩ : IsLocalRing.CotangentSpace R) := by
  have h1 : (⟨r * a, hra⟩ : IsLocalRing.maximalIdeal R)
      = r • (⟨a, ha⟩ : IsLocalRing.maximalIdeal R) := Subtype.ext rfl
  rw [algebraMap_smul, h1, map_smul]
end IsRegularLocalRing
end

set_option autoImplicit false
open IsRegularLocalRing
open IsLocalRing
universe u
namespace IsRegularLocalRing
theorem _root_.solution {R : Type*} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
        ι → IsLocalRing.CotangentSpace R))
    {i j : ι} (hij : i ≠ j) : x j ∉ Ideal.span ({x i} : Set R) := by
  intro hmem
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  have hmem2 : r * x i ∈ IsLocalRing.maximalIdeal R := by
    rw [hr]
    exact hx j
  have key : ((IsLocalRing.maximalIdeal R).toCotangent ⟨x j, hx j⟩ :
      IsLocalRing.CotangentSpace R)
      = algebraMap R (IsLocalRing.ResidueField R) r •
        ((IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
          IsLocalRing.CotangentSpace R) := by
    have hsub : (⟨x j, hx j⟩ : IsLocalRing.maximalIdeal R) = ⟨r * x i, hmem2⟩ :=
      Subtype.ext hr.symm
    rw [hsub]
    exact toCotangent_mul_eq_smul r (x i) (hx i) hmem2
  exact false_of_eq_smul_of_linearIndependent hli hij _ key
end IsRegularLocalRing
