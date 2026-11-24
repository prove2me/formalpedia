-- Prove2me | solution 1 for GlobalTheory.injective_of_injective_comp_aeval_of_trdeg_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:59:57.384797+00:00
-- url     : https://prove2.me/submissions/fbeaa7b2-8d83-40a6-acdf-b98c716af171

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_InjectiveOfInjectiveCompAevalOfTrdegLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open GlobalTheory
open MvPolynomial
namespace GlobalTheory
theorem _root_.solution {k A κ ι : Type} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [CommRing κ] [Finite ι] (b : ι → A)
    (hA : Algebra.trdeg k A ≤ Cardinal.mk ι) (χ : A →+* κ)
    (hχ : Function.Injective (fun q : MvPolynomial ι k => χ (aeval b q))) :
    Function.Injective χ := by
  have hb : AlgebraicIndependent k b := by
    rw [algebraicIndependent_iff_injective_aeval]
    exact Function.Injective.of_comp (f := χ) hχ
  have hT := hb.isTranscendenceBasis_of_trdeg_le_of_finite hA
  have := hT.isAlgebraic
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hne
  have hmem : a ∈ RingHom.ker χ := ha
  refine Ideal.comap_ne_bot_of_algebraic_mem hne hmem
    (Algebra.IsAlgebraic.isAlgebraic (R := Algebra.adjoin k (Set.range b)) a) (eq_bot_iff.2 fun y hy => ?_)
  rw [Ideal.mem_comap, RingHom.mem_ker] at hy
  rw [Ideal.mem_bot]
  obtain ⟨y, hy'⟩ := y
  have hr := hy'
  rw [Algebra.adjoin_range_eq_range_aeval] at hr
  obtain ⟨q, rfl⟩ := hr
  have h0 : χ (aeval b q) = 0 := hy
  have hq : q = 0 := hχ (show χ (aeval b q) = χ (aeval b 0) by rw [map_zero, map_zero]; exact h0)
  subst hq
  apply Subtype.ext
  simp
end GlobalTheory
