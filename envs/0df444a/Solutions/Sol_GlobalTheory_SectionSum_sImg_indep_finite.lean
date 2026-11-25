-- Prove2me | solution 1 for GlobalTheory.SectionSum.sImg_indep_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:57:42.522908+00:00
-- url     : https://prove2.me/submissions/dc93e104-8974-41f4-abd0-5e070b1f78d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AemeasurableFinsumSection
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_fieldOfS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.SectionSum
open MvPolynomial MeasureTheory
namespace GlobalTheory.SectionSum
theorem _root_.solution (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] (D N : ℕ)
    (j₀ : Fin (N + 1)) (x : Fin N → Ω) (hfg : (⊤ : IntermediateField K Ω).FG)
    (htr : Algebra.trdeg K Ω = D)
    (hJ : ∃ J : Fin D → Fin N, LinearIndependent Ω fun k => KaehlerDifferential.D K Ω (x (J k))) :
    Function.Injective (sHom (K := K) (D := D) j₀ x) ∧
      FiniteDimensional (IntermediateField.adjoin K (Set.range (sImg (D := D) j₀ x)))
        (OmS Ω D N) := by
  have hfs := ReciprocityTheory.MultiplicativeHeights.Closed.fieldOfS K Ω D N x hfg htr hJ
  let e : TVar D N ≃ TVar D N :=
    Equiv.prodCongr (Equiv.refl _) (Fin.cycleRange j₀).symm
  have key : (ReciprocityTheory.MultiplicativeHeights.sImage (D := D) x) = (sImg (D := D) j₀ x) ∘ e := by
    funext p
    obtain ⟨i, j⟩ := p
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [e, ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_zero]
    · simp [e, ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_succ]
  have hrange : Set.range (ReciprocityTheory.MultiplicativeHeights.sImage (D := D) x) = Set.range (sImg (D := D) j₀ x) := by
    rw [key, EquivLike.range_comp]
  refine ⟨?_, ?_⟩
  · have hind : AlgebraicIndependent K (ReciprocityTheory.MultiplicativeHeights.sImage (D := D) x) := hfs.1
    rw [key] at hind
    have h2 := hind.comp _ e.symm.injective
    have h3 : AlgebraicIndependent K (sImg (D := D) j₀ x) := by
      simpa [Function.comp_def] using h2
    exact h3
  · have h2 := hfs.2
    rw [hrange] at h2
    exact h2
end GlobalTheory.SectionSum
