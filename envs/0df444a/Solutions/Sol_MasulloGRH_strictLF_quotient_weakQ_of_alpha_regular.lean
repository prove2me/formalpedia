-- Prove2me | solution 1 for MasulloGRH.strictLF_quotient_weakQ_of_alpha_regular
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:05:39.438335+00:00
-- url     : https://prove2.me/submissions/66a5142c-1c11-4205-9f6e-a2bee6e4353c

import Theorems.Thm_MasulloGRH_bounded_in_strict_frechet_stages
import Theorems.Thm_MasulloGRH_strictLF_quotient_weakQ_of_localized_closures

set_option autoImplicit false
open MasulloGRH Filter Topology

private theorem localized_closure
    {A Q : Type*} [TopologicalSpace A] [FirstCountableTopology A]
    [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q] [RegularSpace Q]
    [IsTopologicalAddGroup Q] [ContinuousSMul ℂ Q]
    (a : A) (f : A → Q) (hf : ContinuousAt f a)
    (P : ℕ → Set Q) (hα : ∀ B : Set Q, Bornology.IsVonNBounded ℂ B → ∃ j, B ⊆ P j) :
    ∃ U ∈ 𝓝 a, ∃ j, closure (f '' U) ⊆ P j := by
  classical
  obtain ⟨b, hb⟩ := (𝓝 a).exists_antitone_basis
  by_contra! h
  have hx (j : ℕ) := Set.not_subset.mp (h (b j) (hb.mem j) j)
  choose x hxcl hxout using hx
  have hconv : Tendsto x atTop (𝓝 (f a)) := by
    apply tendsto_def.mpr
    intro W hW
    obtain ⟨C, hC, hc, hCW⟩ := exists_mem_nhds_isClosed_subset hW
    obtain ⟨j, hj⟩ := hb.mem_iff.mp (hf.preimage_mem_nhds hC)
    filter_upwards [eventually_ge_atTop j] with n hn
    apply hCW
    apply closure_minimal _ hc (hxcl n)
    rintro _ ⟨v, hv, rfl⟩
    exact hj (hb.antitone hn hv)
  obtain ⟨j, hj⟩ := hα _ (hconv.isVonNBounded_range ℂ)
  exact hxout j (hj (Set.mem_range_self j))

theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hα : ∀ B : Set (E ⧸ V), Bornology.IsVonNBounded ℂ B →
      ∃ n : ℕ, B ⊆ Set.range (Submodule.mapQ (V.comap (X n).subtype) V (X n).subtype le_rfl)) :
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ U' ∈ nhds (0 : X k), ∃ r : ℝ, 0 < r ∧
        ∀ x ∈ U, ∀ y ∈ U', ((x : E) - (y : E)) ∈ V →
          ∃ w ∈ W, ((x : E) - (r : ℂ) • (w : E)) ∈ V := by
  classical
  apply strictLF_quotient_weakQ_of_localized_closures E X hmono hexh hX htop V hV
  intro n
  obtain ⟨hE, _⟩ := bounded_in_strict_frechet_stages E X hmono hexh hX htop
  obtain ⟨ι, _, p, hp⟩ := hE.1
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have : ContinuousSMul ℂ E := hp.continuousSMul
  have : TopologicalSpace.MetrizableSpace (X n) := (hX n).2.2
  exact localized_closure (0 : X n) (fun x : X n => V.mkQ (x : E))
    (V.continuous_mkQ.comp continuous_subtype_val).continuousAt _ hα
