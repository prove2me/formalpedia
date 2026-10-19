-- Prove2me | solution 1 for OAI.MatchingSmoothing.binomial_le_finrank_of_eigenvector_mem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T05:38:30.375932+00:00
-- url     : https://prove2.me/submissions/7c6c379f-c58f-4c49-a2c9-27d62edc6fe2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/Involutions.lean:L155-L188
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.binomial_le_finrank_of_eigenvector_mem. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD

-- ---- from OAI.Combinatorics.MatchingPSD.Involutions ----
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing

section CommutingInvolutions

variable {ι : Type u_1} {V : Type u_2} [AddCommGroup V] [Module ℝ V]

lemma independent_eigenprofiles {κ : Type u_3} (A : ι → Module.End ℝ V)
    (hcomm : ∀ i j, Commute (A i) (A j)) (χ : κ → ι → ℝ)
    (hinj : Function.Injective χ) (v : κ → V) (hv : ∀ k, v k ≠ 0)
    (heig : ∀ k i, A i (v k) = χ k i • v k) : LinearIndependent ℝ v := by
  have hi := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo A
    (fun i j c => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) c)
  apply (hi.comp hinj).linearIndependent _ _ hv
  intro k
  change v k ∈ ⨅ i, (A i).maxGenEigenspace (χ k i)
  rw [Submodule.mem_iInf]
  intro i
  exact Module.End.eigenspace_le_maxGenEigenspace
    (Module.End.mem_eigenspace_iff.mpr (heig k i))

lemma binomial_le_finrank_of_eigenvector_mem [Fintype ι] [DecidableEq ι] [FiniteDimensional ℝ V]
    (A : ι → Module.End ℝ V) (hcomm : ∀ i j, Commute (A i) (A j))
    (P : Equiv.Perm ι → V ≃ₗ[ℝ] V)
    (hconj : ∀ p i v, A (p i) (P p v) = P p (A i v))
    (W : Submodule ℝ V) (hW : ∀ p v, v ∈ W → P p v ∈ W)
    (s : Finset ι) (v : V) (hvW : v ∈ W) (hv : v ≠ 0)
    (heig : ∀ i, A i v = (if i ∈ s then (-1 : ℝ) else 1) • v) :
    (Fintype.card ι).choose s.card ≤ Module.finrank ℝ W := by
  classical
  let T := ↥((Finset.univ : Finset ι).powersetCard s.card)
  have hp (t : T) : ∃ p : Equiv.Perm ι, s.map p.toEmbedding = t.1 :=
    Equiv.Perm.exists_map_finset_eq s t.1
      (Finset.mem_powersetCard.mp t.2).2.symm
  choose p hp using hp
  let χ (t : T) (i : ι) : ℝ := if i ∈ t.1 then -1 else 1
  have hχ : Function.Injective χ := by
    intro t u h
    apply Subtype.ext
    ext i
    have hh := congrFun h i
    dsimp [χ] at hh
    by_cases ht : i ∈ t.1 <;> by_cases hu : i ∈ u.1 <;> simp_all <;> norm_num at hh
  have hprof (t : T) (i : ι) : A i (P (p t) v) = χ t i • P (p t) v := by
    have hi : (p t).symm i ∈ s ↔ i ∈ t.1 := by
      rw [← hp t]
      simp
    by_cases hii : i ∈ t.1 <;>
      simpa [heig, χ, hi, hii] using hconj (p t) ((p t).symm i) v
  have hli := independent_eigenprofiles A hcomm χ hχ
    (fun t => P (p t) v) (fun t => by simpa using hv) hprof
  let vw (t : T) : W := ⟨P (p t) v, hW (p t) v hvW⟩
  have hliw : LinearIndependent ℝ vw := LinearIndependent.of_comp W.subtype hli
  have hc := hliw.fintype_card_le_finrank
  simpa only [T, Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ] using hc

end CommutingInvolutions
end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.binomial_le_finrank_of_eigenvector_mem := @_root_.OAI.MatchingSmoothing.binomial_le_finrank_of_eigenvector_mem
