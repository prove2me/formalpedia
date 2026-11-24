-- Prove2me | solution 1 for GlobalTheory.sub_rename_mem_span_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:35:22.248635+00:00
-- url     : https://prove2.me/submissions/ade4dce8-60d5-4e37-8149-78428b4f742b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPolynomialFinrankHomogeneousSubmoduleStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FinrankMapAddFinrankInfKerOfFinite
import Theorems.Thm_GlobalTheory_mem_homogeneousSubmodule_mul_of_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open MvPolynomial
namespace GlobalTheory
theorem _root_.solution {K σ : Type*} [Field K] (t : σ → σ)
    (I : Ideal (MvPolynomial σ K)) (hI : ∀ F, F - rename t F ∈ I) {d : ℕ} (hd : 1 ≤ d)
    {e : ℕ} (he : d ≤ e) : ∀ F : MvPolynomial σ K, F.IsHomogeneous e →
      F - rename t F ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d} := by
  have hk : ∀ (l : MvPolynomial σ K), l.IsHomogeneous 1 → l ∈ I → ∀ n, d ≤ n →
      ∀ H : MvPolynomial σ K, H.IsHomogeneous n →
      l * H ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d} := by
    intro l hl hlI n hn H hH
    have hn' : n = (d - 1) + (n - (d - 1)) := by omega
    rw [hn'] at hH
    refine Submodule.mul_induction_on (mem_homogeneousSubmodule_mul_of_add hH) ?_ ?_
    · intro A hA B _
      rw [← _root_.mul_assoc]
      refine Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨Ideal.mul_mem_right _ _ hlI, ?_⟩)
      have h := hl.mul hA
      rwa [show 1 + (d - 1) = d by omega] at h
    · intro x y hx hy
      rw [mul_add]
      exact add_mem hx hy
  induction e, he using Nat.le_induction with
  | base =>
    intro F hF
    exact Ideal.subset_span ⟨hI F, hF.sub hF.rename_isHomogeneous⟩
  | succ n hn ih =>
    intro F hF
    rw [add_comm] at hF
    refine Submodule.mul_induction_on (mem_homogeneousSubmodule_mul_of_add hF) ?_ ?_
    · intro l hl G hG
      have hl' : l.IsHomogeneous 1 := hl
      have hG' : G.IsHomogeneous n := hG
      have : l * G - rename t (l * G) =
          l * (G - rename t G) + (l - rename t l) * rename t G := by
        rw [map_mul]; ring
      rw [this]
      exact add_mem (Ideal.mul_mem_left _ _ (ih G hG'))
        (hk _ (hl'.sub hl'.rename_isHomogeneous) (hI l) n hn _ hG'.rename_isHomogeneous)
    · intro x y hx hy
      have : x + y - rename t (x + y) = (x - rename t x) + (y - rename t y) := by
        rw [map_add]; ring
      rw [this]
      exact add_mem hx hy
end GlobalTheory
