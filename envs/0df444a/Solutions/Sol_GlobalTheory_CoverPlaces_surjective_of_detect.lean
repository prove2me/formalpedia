-- Prove2me | solution 1 for GlobalTheory.CoverPlaces.surjective_of_detect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:56:30.911808+00:00
-- url     : https://prove2.me/submissions/76ded3b9-4504-4bd7-a6b3-710f6ff67240

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsIntegralIffMemSpanOneTmulIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemIntegralClosureOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsPtOrdEqAddValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FdegEqFinrankResidueFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsEquivCoverPointsPlacesBaseChange
import Theorems.Thm_GlobalTheory_CoverPlaces_ord_pos_iff
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ep_pos
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_mul
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_pow
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_unif
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_unif_mem
import Theorems.Thm_GlobalTheory_ResDegPlace_ord_pos_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_unif_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.CoverPlaces
variable {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A]
  [Algebra O A] {ϖ : O}
namespace GlobalTheory.CoverPlaces
theorem _root_.solution [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) {T : Type} [Finite T]
    (Z : T → Pts O A) (hZ : ∀ x, (∀ t, 0 ≤ ord ϖ (Z t) x) → x ∈ As O A) :
    Function.Surjective Z := by
  classical
  cases nonempty_fintype T
  intro ζ
  by_contra hne
  have hex : ∀ t, ∃ a ∈ (Z t).asIdeal, a ∉ ζ.asIdeal := by
    intro t
    by_contra hc
    push Not at hc
    exact hne ⟨t, MaximalSpectrum.ext ((Z t).isMaximal.eq_of_le ζ.isMaximal.ne_top hc)⟩
  choose a ha ha' using hex
  haveI := ζ.isMaximal.isPrime
  have hb : ∏ t, a t ∉ ζ.asIdeal := by
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨t, -, ht⟩
    exact ha' t ht
  have hbt : ∀ t, ∏ t, a t ∈ (Z t).asIdeal := fun t =>
    Ideal.prod_mem _ (Finset.mem_univ t) (ha t)
  generalize ∏ t, a t = b at hb hbt
  obtain ⟨v, hv⟩ := h.isUnit.exists_right_inv
  set n : ℕ := ∑ t, ep ϖ (Z t) with hn
  have hx : v * (b : A) ^ n ∈ As O A := by
    apply hZ
    intro t
    have h1 : ord ϖ (Z t) (algebraMap O A ϖ * (v * (b : A) ^ n)) = n • ord ϖ (Z t) b := by
      rw [← mul_assoc, hv, one_mul, ord_pow _ h]
    rw [ord_mul _ h, ord_unif _ h] at h1
    have h2 := (ord_pos_iff h (Z t) b).2 (hbt t)
    have h3 : ep ϖ (Z t) ≤ n :=
      Finset.single_le_sum (f := fun t => ep ϖ (Z t)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    have h4 := ep_pos (Z t) h
    generalize ord ϖ (Z t) (v * (b : A) ^ n) = p at h1
    generalize ord ϖ (Z t) (b : A) = q at h1 h2
    generalize ep ϖ (Z t) = e at h1 h3 h4
    induction p using WithTop.recTopCoe with
    | top => exact le_top
    | coe p =>
      induction q using WithTop.recTopCoe with
      | top =>
        obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [hm, succ_nsmul, add_top, ← WithTop.coe_add] at h1
        exact absurd h1 WithTop.coe_ne_top
      | coe q =>
        rw [← WithTop.coe_add, ← WithTop.coe_nsmul, WithTop.coe_inj, nsmul_eq_mul] at h1
        have h5 : 0 < q := by exact_mod_cast h2
        have h6 : (e : ℤ) ≤ n := by exact_mod_cast h3
        have h7 : 0 ≤ p := by nlinarith
        exact_mod_cast h7
  have hp : b ^ n = algebraMap O (As O A) ϖ * ⟨_, hx⟩ := by
    apply Subtype.ext
    change (b : A) ^ n = algebraMap O A ϖ * (v * (b : A) ^ n)
    rw [← mul_assoc, hv, one_mul]
  exact hb (ζ.isMaximal.isPrime.mem_of_pow_mem n (hp ▸ Ideal.mul_mem_right _ _ (unif_mem h ζ)))
end GlobalTheory.CoverPlaces
