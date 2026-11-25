-- Prove2me | solution 1 for GlobalTheory.Mass.GenusOrb.trace_pos_of_PD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:01:39.943693+00:00
-- url     : https://prove2.me/submissions/fc120dd6-42fd-42ac-a562-557fe0f6b4bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitWeightedStabilizerSumEqSumOrbitReps
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianGenusMassEqOrbitStabilizerMass
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.GenusOrb
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
open NumberField Matrix
open scoped ENNReal Classical
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.Mass.GenusOrb
namespace _root_.GlobalTheory.Mass.GenusOrb
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hp : _root_.GlobalTheory.Mass.PD h) (x : V) (hx : x ≠ 0) :
    0 < Algebra.trace ℚ K (h x x) := by
  have hp' : ∀ (τ : K →+* ℂ) (x : V), x ≠ 0 → 0 < (τ ((h x) x)).re := hp
  have hsum := trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := h x x)
  have hre : (algebraMap ℚ ℂ (Algebra.trace ℚ K (h x x))).re =
      (Algebra.trace ℚ K (h x x) : ℝ) := by simp
  have hpos : (0 : ℝ) < (Algebra.trace ℚ K (h x x) : ℝ) := by
    rw [← hre, hsum, Complex.re_sum]
    obtain ⟨φ⟩ := (inferInstance : Nonempty (K →+* ℂ))
    haveI : Nonempty (K →ₐ[ℚ] ℂ) := ⟨φ.toRatAlgHom⟩
    exact Finset.sum_pos (fun σ _ => hp' σ.toRingHom x hx) Finset.univ_nonempty
  exact_mod_cast hpos
end _root_.GlobalTheory.Mass.GenusOrb
end GlobalTheory.Mass.GenusOrb
