-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_cellEnumeration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:25:32.907301+00:00
-- url     : https://prove2.me/submissions/61083fd1-c247-45ab-98f5-b29a3e34a34f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellRank_of_mem_doubleCoset
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_permGL_mem_doubleCoset
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_doubleCoset_of_cellRank_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
variable {F : Type*} [Field F] {n : ℕ} (β γ : Fin n → ℕ)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution :
    ∃ (k : ℕ) (w : Fin k → Equiv.Perm (Fin n)),
      (∀ g : GL (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j))
        (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) ∧
      Antitone fun j => cellHeight β γ (permGL F (w j)) := by
  classical
  let rk : Equiv.Perm (Fin n) → ℕ → ℕ → ℕ := fun w a b => cellRank β γ (permGL F w) a b
  let S : Finset (ℕ → ℕ → ℕ) := Finset.univ.image rk
  let e0 : Fin S.card ≃ S := S.equivFin.symm
  have hrep : ∀ r : S, ∃ w, rk w = r := fun r => by
    obtain ⟨w, -, hw⟩ := Finset.mem_image.1 r.2
    exact ⟨w, hw⟩
  choose rep hrep using hrep
  have hrep' : ∀ (r : S) (a b : ℕ), cellRank β γ (permGL F (rep r)) a b = (r : ℕ → ℕ → ℕ) a b :=
    fun r a b => congrFun (congrFun (hrep r) a) b
  let ht : Fin S.card → ℕ := fun i => cellHeight β γ (permGL F (rep (e0 i)))
  let s := Tuple.sort (fun i => OrderDual.toDual (ht i))
  have hs : Monotone ((fun i => OrderDual.toDual (ht i)) ∘ s) := Tuple.monotone_sort _
  refine ⟨S.card, fun j => rep (e0 (s j)), fun g => ?_, fun i j hij => ?_⟩
  · obtain ⟨w, hw⟩ := exists_permGL_mem_doubleCoset (β := β) (γ := γ) g
    have hmem : rk w ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ w)
    obtain ⟨j', hj⟩ := (s.trans e0).surjective ⟨rk w, hmem⟩
    have hj2 : e0 (s j') = ⟨rk w, hmem⟩ := hj
    have hg : g ∈ doubleCoset (permGL F (rep (e0 (s j')))) (blockUpper F n β : Set (GL (Fin n) F))
        (blockUpper F n γ) := by
      apply mem_doubleCoset_of_cellRank_eq
      intro a b
      rw [hrep', cellRank_of_mem_doubleCoset hw, hj2]
    refine ⟨j', hg, fun j'' hj'' => ?_⟩
    apply s.injective
    apply e0.injective
    apply Subtype.ext
    funext a b
    have h1 := hrep' (e0 (s j'')) a b
    have h2 := hrep' (e0 (s j')) a b
    rw [← cellRank_of_mem_doubleCoset hj''] at h1
    rw [← cellRank_of_mem_doubleCoset hg] at h2
    rw [← h1, ← h2]
  · exact hs hij
end GroundTheory.Automorphic.Parabolic
