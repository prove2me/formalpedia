-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.nonuniqueness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T18:41:48.009975+00:00
-- url     : https://prove2.me/submissions/428ba776-959b-46a1-bcfa-a8ebc671870c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BoltzmannConstruction_local_branching
import Theorems.Thm_BoltzmannContinuation_global_extension

noncomputable section
open MeasureTheory Set Filter
open OAI.BoltzmannNonuniqueness

theorem solution :
    ∃ f₀ : Density, BoundedVelocitySupport f₀ ∧
      ∃ (F G : Evolution) (T : ℝ), AdmissibleGlobal f₀ F ∧ AdmissibleGlobal f₀ G ∧
        StrongEarly T F ∧ StrongEarly T G ∧
        ∃ t ∈ Set.Icc 0 T, ¬(F t =ᵐ[MeasureTheory.volume] G t) := by
  obtain ⟨f₀, hsupp, F, G, T, hF, hG, hsF, hsG, t, ψ, ht, _, _, hsep⟩ :=
    BoltzmannConstruction.local_branching
  obtain ⟨F', hF', hsF', heqF⟩ :=
    BoltzmannContinuation.global_extension f₀ F T hF hsF
  obtain ⟨G', hG', hsG', heqG⟩ :=
    BoltzmannContinuation.global_extension f₀ G T hG hsG
  have ht' : t ∈ Set.Icc 0 T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  refine ⟨f₀, hsupp, F', G', T, hF', hG', hsF', hsG', t, ht', ?_⟩
  intro heq
  apply hsep
  apply integral_congr_ae
  filter_upwards [(heqF t ht').symm.trans (heq.trans (heqG t ht'))] with z hz
  exact congrArg (fun a : ℝ => a * ψ z) hz
