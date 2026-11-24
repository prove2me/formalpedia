-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LocInf.isOpenEmbedding_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:27:56.081804+00:00
-- url     : https://prove2.me/submissions/5a8a811b-cff0-41b3-94c5-f99fca1be6b2

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocInf_isOpen_pos
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocInf_isOpen_posU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocInf
namespace GlobalTheory.CompanionTheory.SW.LocInf
theorem _root_.solution (ι : Type) [Fintype ι] :
    IsOpenEmbedding (fun u : posU ι => ((u : (ι → ℝ)ˣ) ^ 2 : (ι → ℝ)ˣ)) := by
  have hv : IsOpenEmbedding (Units.val : (ι → ℝ)ˣ → (ι → ℝ)) := Units.isOpenEmbedding_val
  refine (IsOpenEmbedding.of_comp_iff _ hv).1 ?_
  set j : posU ι → (ι → ℝ) := fun u => ((u : (ι → ℝ)ˣ) : ι → ℝ) with hjdef
  have hj : IsOpenEmbedding j := hv.comp (isOpen_posU ι).isOpenEmbedding_subtypeVal
  set g : posU ι → (ι → ℝ) := Units.val ∘ (fun u : posU ι => ((u : (ι → ℝ)ˣ) ^ 2 : (ι → ℝ)ˣ)) with hgdef
  have hg : Continuous g :=
    Units.continuous_val.comp (continuous_subtype_val.pow 2)
  let r : (ι → ℝ) → (ι → ℝ) := fun x i => Real.sqrt (x i)
  have hr : Continuous r := continuous_pi fun i => (continuous_apply i).sqrt
  have hrg : r ∘ g = j := by
    funext u i
    have hu : 0 < ((u : (ι → ℝ)ˣ) : ι → ℝ) i := u.2 i
    simp [r, g, j, Real.sqrt_sq hu.le]
  have hind : IsInducing g := IsInducing.of_comp hg hr (by rw [hrg]; exact hj.isInducing)
  have hinj : Function.Injective g := Function.Injective.of_comp (f := r) (by rw [hrg]; exact hj.injective)
  have hrange : Set.range g = {x : ι → ℝ | ∀ i, 0 < x i} := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩ i
      have hu : 0 < ((u : (ι → ℝ)ˣ) : ι → ℝ) i := u.2 i
      simpa [g] using pow_pos hu 2
    · intro hx
      have hs : ∀ i, 0 < Real.sqrt (x i) := fun i => Real.sqrt_pos.2 (hx i)
      let w : (ι → ℝ)ˣ :=
        ⟨fun i => Real.sqrt (x i), fun i => (Real.sqrt (x i))⁻¹,
          by funext i; simp [(hs i).ne'], by funext i; simp [(hs i).ne']⟩
      refine ⟨⟨w, fun i => hs i⟩, ?_⟩
      funext i
      simp [g, w, Real.sq_sqrt (hx i).le]
  exact ⟨⟨hind, hinj⟩, by rw [hrange]; exact isOpen_pos ι⟩
end GlobalTheory.CompanionTheory.SW.LocInf
