-- Prove2me | solution 1 for GlobalTheory.Mass.SemiBasis.mem_locD_iff_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:13:01.505314+00:00
-- url     : https://prove2.me/submissions/74365eb9-baec-4c41-8d57-a1ac20e4a1e5

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
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) (M : Submodule (𝓞 K) V) (x : V) :
    x ∈ locD (d : 𝓞 K) M ↔ x ∈ Submodule.span (A K hd) (M : Set V) := by
  constructor
  · rintro ⟨s, hs, hsx⟩
    have hs0 := alg_ne_zero hd hs
    have hu : (algebraMap (𝓞 K) K s)⁻¹ ∈ A K hd := (mem_A hd _).mpr ⟨1, s, hs, by simp⟩
    have hx : x = (⟨_, hu⟩ : A K hd) • (s • x) := by
      rw [Subalgebra.smul_def, ← algebraMap_smul K s x, smul_smul]
      simp [hs0]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, one_mem _, by simpa using hy⟩
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul a y _ hy =>
      obtain ⟨s, hs, hsy⟩ := hy
      obtain ⟨r, t, ht, hat⟩ := (mem_A hd (a : K)).mp a.2
      refine ⟨t * s, mul_mem ht hs, ?_⟩
      have ht0 := alg_ne_zero hd ht
      have he : (t * s) • (a • y) = r • (s • y) := by
        rw [Subalgebra.smul_def, hat, ← algebraMap_smul K (t * s), ← algebraMap_smul K r,
          ← algebraMap_smul K s, smul_smul, smul_smul]
        congr 1
        rw [map_mul]
        field_simp
      rw [he]
      exact M.smul_mem r hsy
end GlobalTheory.Mass.SemiBasis
