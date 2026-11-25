-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.isAddFundamentalDomain_idealLatticePi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:09:39.444577+00:00
-- url     : https://prove2.me/submissions/432c111c-0e82-48d8-bd8f-fdeee0a421e1

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι]
variable {K}
namespace GroundTheory.Automorphic.GJMatrix
theorem _root_.solution (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsAddFundamentalDomain (idealLatticePi I)
      (Set.univ.pi fun i ↦ ZSpan.fundamentalDomain
        ((Module.Free.chooseBasis ℤ (idealLattice K (I i))).ofZLatticeBasis ℝ
          (idealLattice K (I i)))) (mixedMeasurePi K) := by
  set b := fun i ↦ (Module.Free.chooseBasis ℤ (idealLattice K (I i))).ofZLatticeBasis ℝ
    (idealLattice K (I i))
  have hspan : ∀ i, Submodule.span ℤ (Set.range (b i)) = idealLattice K (I i) := fun i ↦
    (Module.Free.chooseBasis ℤ (idealLattice K (I i))).ofZLatticeBasis_span ℝ _
  refine IsAddFundamentalDomain.mk'
    (MeasurableSet.univ_pi fun i ↦ ZSpan.fundamentalDomain_measurableSet _).nullMeasurableSet
    fun x ↦ ?_
  have h := fun i ↦ ZSpan.exist_unique_vadd_mem_fundamentalDomain (b i) (x i)
  choose v hv hvu using h
  have hvmem : ∀ i, (v i : mixedSpace K) ∈ idealLattice K (I i) := fun i ↦ by
    have key : ∀ z ∈ Submodule.span ℤ (Set.range (b i)), z ∈ idealLattice K (I i) :=
      fun z hz ↦ hspan i ▸ hz
    exact key _ (v i).2
  refine ⟨⟨fun i ↦ (v i : mixedSpace K), mem_idealLatticePi.mpr hvmem⟩, ?_, ?_⟩
  · intro i _
    exact hv i
  · rintro g hg
    apply Subtype.ext
    funext i
    have hgi : (g : ι → mixedSpace K) i ∈ Submodule.span ℤ (Set.range (b i)) := by
      rw [hspan i]
      exact mem_idealLatticePi.mp g.2 i
    have := hvu i ⟨_, hgi⟩ (hg i trivial)
    exact congrArg Subtype.val this
end GroundTheory.Automorphic.GJMatrix
