-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_cosetIntegral_isOpenQuotientMap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:27:35.279667+00:00
-- url     : https://prove2.me/submissions/85c81183-0f02-4e38-8704-c4eb55a3f1d9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Theorems.Thm_MasulloGRH_schwartzBruhat_cosetIntegral
import Theorems.Thm_MasulloGRH_open_mapping_LF
import Theorems.Thm_MasulloGRH_schwartzBruhat_isStrictLFOfNuclearFrechet
import Theorems.Thm_MasulloGRH_schwartzBruhat_main_structure

open MeasureTheory Topology

set_option autoImplicit false

open MasulloGRH

namespace Sol_MasulloGRH_schwartzBruhat_cosetIntegral_isOpenQuotientMap

/-- A Hausdorff locally convex strict LF-space (of nuclear Fréchet spaces) is an LF-space. -/
theorem isLF_of_isHLCS_of_isStrictLFOfNuclearFrechet (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hH : IsHLCS E) (hS : IsStrictLFOfNuclearFrechet E) : IsLF E := by
  obtain ⟨X, hmono, hcov, hX, htop⟩ := hS
  refine ⟨hH, X, fun n => inferInstance, hcov, fun n => (hX n).1, fun n => ?_, htop⟩
  have hle : X n ≤ X (n + 1) := hmono (Nat.le_succ n)
  exact ⟨hle, continuous_inclusion (s := (X n : Set E)) (t := (X (n + 1) : Set E)) hle⟩

end Sol_MasulloGRH_schwartzBruhat_cosetIntegral_isOpenQuotientMap

open Sol_MasulloGRH_schwartzBruhat_cosetIntegral_isOpenQuotientMap in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular]
    (Φ : SchwartzBruhat G →L[ℂ] SchwartzBruhat (G ⧸ H))
    (hΦ : ∀ (f : SchwartzBruhat G) (x : G),
      Φ f (x : G ⧸ H) = ∫ h : H, f (x * (h : G)) ∂μH) :
    IsOpenQuotientMap Φ := by
  -- the quotient `G ⧸ H` is a Hausdorff, locally compact, second-countable abelian group
  have : T3Space (G ⧸ H) := QuotientGroup.instT3Space H (hN := hH)
  -- `Φ` is the coset-integration map, which is surjective
  obtain ⟨Φ', hsurj', hΦ'⟩ := schwartzBruhat_cosetIntegral G H hH μH
  have hEq : ∀ f, Φ f = Φ' f := by
    intro f
    apply Subtype.ext
    funext q
    induction q using QuotientGroup.induction_on with
    | H x =>
      change Φ f (x : G ⧸ H) = Φ' f (x : G ⧸ H)
      rw [hΦ, (hΦ' f x).2]
  have hsurj : Function.Surjective Φ := by
    intro g
    obtain ⟨f, hf⟩ := hsurj' g
    exact ⟨f, (hEq f).trans hf⟩
  -- the topological vector space structure of `S(G)`
  obtain ⟨⟨ι, _, p, hp⟩, hT2⟩ := (schwartzBruhat_main_structure G).1
  have : IsTopologicalAddGroup (SchwartzBruhat G) := hp.topologicalAddGroup
  have : ContinuousSMul ℂ (SchwartzBruhat G) := hp.continuousSMul
  -- `S(G ⧸ H)` is an LF-space
  have hE : IsLF (SchwartzBruhat (G ⧸ H)) :=
    isLF_of_isHLCS_of_isStrictLFOfNuclearFrechet _
      (schwartzBruhat_main_structure (G ⧸ H)).1
      (schwartzBruhat_isStrictLFOfNuclearFrechet (G ⧸ H))
  -- `S(G)` is the union of an increasing sequence of Fréchet subspaces
  have hF : ∃ (X : ℕ → Submodule ℂ (SchwartzBruhat G)) (τ : ∀ n, TopologicalSpace (X n)),
      Monotone X ∧ (∀ x : SchwartzBruhat G, ∃ n, x ∈ X n) ∧
      (∀ n, @IsFrechet (X n) _ _ (τ n)) ∧
      ∀ n, @Continuous (X n) (SchwartzBruhat G) (τ n) _ Subtype.val := by
    obtain ⟨X, hmono, hcov, hX, -⟩ := schwartzBruhat_isStrictLFOfNuclearFrechet G
    exact ⟨X, fun n => inferInstance, hmono, hcov, fun n => (hX n).1,
      fun n => continuous_subtype_val⟩
  have hopen : IsOpenMap Φ :=
    open_mapping_LF (SchwartzBruhat (G ⧸ H)) (SchwartzBruhat G) hE hF
      (Φ : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat (G ⧸ H)) Φ.continuous hsurj
  exact ⟨hsurj, Φ.continuous, hopen⟩
