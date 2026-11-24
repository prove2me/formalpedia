-- Prove2me | solution 1 for GlobalTheory.Mass.SemiBasis.mem_locD_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:13:14.940681+00:00
-- url     : https://prove2.me/submissions/34f39f8c-b827-46bc-a372-b2a887462430

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLocDIffSpan
import Theorems.Thm_GlobalTheory_Mass_SemiBasis_mem_A
import Theorems.Thm_GlobalTheory_Mass_SemiBasis_alg_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.SemiBasis
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.Mass.SemiBasis
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) (x : K) :
    x ∈ locD (d : 𝓞 K) (1 : Submodule (𝓞 K) K) ↔ x ∈ A K hd := by
  constructor
  · rintro ⟨s, hs, hsx⟩
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 hsx
    refine (mem_A hd x).2 ⟨r, s, hs, ?_⟩
    have hs0 := alg_ne_zero hd hs
    rw [hr, Algebra.smul_def]
    field_simp
  · intro hx
    obtain ⟨r, s, hs, rfl⟩ := (mem_A hd x).1 hx
    refine ⟨s, hs, Submodule.mem_one.2 ⟨r, ?_⟩⟩
    have hs0 := alg_ne_zero hd hs
    rw [Algebra.smul_def]
    field_simp
end GlobalTheory.Mass.SemiBasis
