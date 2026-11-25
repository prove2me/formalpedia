-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.exists_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:30:42.912346+00:00
-- url     : https://prove2.me/submissions/682e10e7-a76a-4b50-b20a-c079c7000ea6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosIso
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K]
namespace GlobalTheory.DegCnt.PosIso
theorem _root_.solution (M : Submodule (𝓞 K) V) (hM : M.FG) (φ : V →ₗ[K] K) (h0 : ∃ y ∈ M, φ y ≠ 0) :
    ∃ v ∈ Submodule.span K (M : Set V), φ v = 1 ∧ ∀ y ∈ M, φ y • v ∈ M := by
  let J : Submodule (𝓞 K) K := M.map (φ.restrictScalars (𝓞 K))
  have hJ : J.FG := hM.map _
  let I : FractionalIdeal (𝓞 K)⁰ K := ⟨J, FractionalIdeal.isFractional_of_fg hJ⟩
  have hI : I ≠ 0 := by
    obtain ⟨y, hy, hy0⟩ := h0
    intro h
    have : φ y ∈ I := ⟨y, hy, rfl⟩
    rw [h] at this
    exact hy0 (by simpa using this)
  have h1 : (1 : K) ∈ ((I * I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
    rw [mul_inv_cancel₀ hI]; exact FractionalIdeal.one_mem_one _
  rw [FractionalIdeal.coe_mul] at h1
  have key : ∀ w ∈ (I : Submodule (𝓞 K) K) * ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K),
      ∃ v ∈ Submodule.span K (M : Set V), φ v = w ∧ ∀ y ∈ M, φ y • v ∈ M := by
    intro w hw
    refine Submodule.mul_induction_on hw ?_ ?_
    · rintro _ ⟨y0, hy0, rfl⟩ β hβ
      refine ⟨β • y0, Submodule.smul_mem _ _ (Submodule.subset_span hy0), by simp [mul_comm], fun y hy => ?_⟩
      have hm : φ y * β ∈ (I * I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) :=
        FractionalIdeal.mul_mem_mul (show φ y ∈ I from ⟨y, hy, rfl⟩) hβ
      rw [mul_inv_cancel₀ hI, FractionalIdeal.mem_one_iff] at hm
      obtain ⟨o, ho⟩ := hm
      rw [smul_smul, ← ho, algebraMap_smul]
      exact M.smul_mem _ hy0
    · rintro _ _ ⟨v, hv, rfl, h⟩ ⟨v', hv', rfl, h'⟩
      exact ⟨v + v', add_mem hv hv', by simp, fun y hy => by rw [smul_add]; exact add_mem (h y hy) (h' y hy)⟩
  exact key 1 h1
end GlobalTheory.DegCnt.PosIso
