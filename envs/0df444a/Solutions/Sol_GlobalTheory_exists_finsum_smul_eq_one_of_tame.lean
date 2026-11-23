-- Prove2me | solution 1 for GlobalTheory.exists_finsum_smul_eq_one_of_tame
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:35:35.906918+00:00
-- url     : https://prove2.me/submissions/4cba4a48-67a2-44fb-a8de-a0d735885224

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSumSmulSeparatingInertia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsumSmulEqOneOfTame
import Theorems.Thm_GlobalTheory_exists_sum_smul_separating_inertia


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct Pointwise
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (B : Type) [CommRing B] [MulSemiringAction Γ B],
      (∀ q : Ideal B, q.IsPrime → (Nat.card (q.inertia Γ) : B) ∉ q) →
        ∃ b : B, ∑ᶠ g : Γ, g • b = 1 := by
  intro Γ _ _ B _ _ htame
  classical
  haveI := Fintype.ofFinite Γ
  let A := FixedPoints.subring B Γ
  haveI : Algebra.IsInvariant A B Γ := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  haveI := Algebra.IsInvariant.isIntegral A B Γ
  have tr_inv : ∀ b : B, ∑ g : Γ, g • b ∈ A := by
    intro b h
    rw [Finset.smul_sum]
    simp_rw [← mul_smul]
    exact Equiv.sum_comp (Equiv.mulLeft h) (fun g => g • b)
  let T : Ideal A := Ideal.span {t | ∃ b : B, (t : B) = ∑ g : Γ, g • b}
  have hT : ∀ t ∈ T, ∃ b : B, (t : B) = ∑ g : Γ, g • b := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht => exact ht
    | zero => exact ⟨0, by simp⟩
    | add t u _ _ htb hub =>
      obtain ⟨b, hb⟩ := htb
      obtain ⟨c, hc⟩ := hub
      exact ⟨b + c, by simp [hb, hc, Finset.sum_add_distrib]⟩
    | smul a t _ htb =>
      obtain ⟨b, hb⟩ := htb
      refine ⟨(a : B) * b, ?_⟩
      simp only [smul_eq_mul, Subring.coe_mul, hb, Finset.mul_sum, smul_mul']
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [a.2 g]
  suffices h1 : (1 : A) ∈ T by
    obtain ⟨b, hb⟩ := hT 1 h1
    exact ⟨b, by rw [finsum_eq_sum_of_fintype, ← hb]; rfl⟩
  by_contra h1
  obtain ⟨m, hm, hTm⟩ := Ideal.exists_le_maximal T ((Ideal.ne_top_iff_one T).mpr h1)
  have hker : RingHom.ker (algebraMap A B) ≤ m := by
    intro z hz
    have : z = 0 := Subtype.ext hz
    rw [this]
    exact m.zero_mem
  obtain ⟨Q, hQ, hQm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral m hker
  obtain ⟨n, c, d, s, hs, hsep⟩ := _root_.GlobalTheory.exists_sum_smul_separating_inertia Γ B Q hQ.isPrime
  have trace_mem : ∀ j, ∑ g : Γ, g • c j ∈ Q := by
    intro j
    have hmemT : (⟨∑ g : Γ, g • c j, tr_inv (c j)⟩ : A) ∈ T :=
      Ideal.subset_span ⟨c j, rfl⟩
    have := hTm hmemT
    rw [← hQm, Ideal.mem_comap] at this
    exact this
  have hz : ∑ g : Γ, ∑ j, d j * g • c j ∈ Q := by
    rw [Finset.sum_comm]
    exact Q.sum_mem fun j _ => by
      rw [← Finset.mul_sum]
      exact Q.mul_mem_left _ (trace_mem j)
  have hdiff : ∑ g : Γ, (∑ j, d j * g • c j - if g ∈ Q.inertia Γ then s else 0) ∈ Q := by
    refine Q.sum_mem fun g _ => ?_
    split_ifs with hg
    · exact (hsep g).1 hg
    · simpa using (hsep g).2 hg
  rw [Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul] at hdiff
  have hcs := Q.sub_mem hz hdiff
  rw [sub_sub_cancel] at hcs
  rcases hQ.isPrime.mem_or_mem hcs with hc | hc
  · apply htame Q hQ.isPrime
    convert hc using 2
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  · exact hs hc
end _root_.GlobalTheory
end GlobalTheory
