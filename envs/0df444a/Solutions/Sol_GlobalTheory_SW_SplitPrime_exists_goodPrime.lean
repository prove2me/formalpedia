-- Prove2me | solution 1 for GlobalTheory.SW.SplitPrime.exists_goodPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:28:33.699094+00:00
-- url     : https://prove2.me/submissions/4b62fc99-f54e-4d7c-a0a1-ae51ec5f8522

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsGoodSplitPrimeCmField
import Theorems.Thm_GlobalTheory_SW_SplitPrime_exists_prim_den
import Theorems.Thm_GlobalTheory_SW_SplitPrime_exists_degree_one
import Theorems.Thm_GlobalTheory_SW_SplitPrime_absNorm_prime
import Theorems.Thm_GlobalTheory_SW_Base_isIntegral_cc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SplitPrime
open Polynomial
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real Classical
open Polynomial
namespace GlobalTheory.SW.SplitPrime
namespace _root_.GlobalTheory.SW.SplitPrime
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (m : ℕ), 0 < m → ∃ (q : ℕ) (P : Ideal (𝓞 E)), _root_.GlobalTheory.SW.GoodPrime m q P := by
  intro E _ _ _ m hm
  obtain ⟨θ, d, hd, hadj, hden⟩ := _root_.GlobalTheory.SW.SplitPrime.exists_prim_den E
  have hcc : ∀ x : E, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc x = IsCMField.complexConj E x := fun x => rfl
  let θc : 𝓞 E := ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.cc (θ : E), _root_.GlobalTheory.SW.Base.isIntegral_cc θ.2⟩
  have hβ : θ - θc ≠ 0 := by
    intro h
    have h' : IsCMField.complexConj E (θ : E) = θ := by
      rw [← hcc]; exact (congrArg Subtype.val (sub_eq_zero.mp h)).symm
    have : (((IsCMField.complexConj E).toAlgHom).restrictScalars ℚ) = AlgHom.id ℚ E :=
      AlgHom.ext_of_adjoin_eq_top hadj (by
        intro x hx; rw [Set.mem_singleton_iff.mp hx]; exact h')
    apply IsCMField.complexConj_ne_one E
    ext x
    exact DFunLike.congr_fun this x
  have hθ : θ ≠ 0 := by
    rintro rfl
    apply hβ
    rw [sub_eq_zero]
    apply Subtype.ext
    show (0 : E) = _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (0 : E)
    rw [hcc, map_zero]
  set Nv : ℤ := m * (2 * discr E) * Algebra.norm ℤ (θ - θc) with hNv
  have hNv0 : Nv ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by exact_mod_cast hm.ne')
      (mul_ne_zero two_ne_zero (discr_ne_zero E))) ?_
    rw [Ne, Algebra.norm_eq_zero_iff]; exact hβ
  obtain ⟨P, hP, hNP, hs⟩ := _root_.GlobalTheory.SW.SplitPrime.exists_degree_one θ hθ d hd hden Nv hNv0
  have hq := _root_.GlobalTheory.SW.SplitPrime.absNorm_prime P hP hs
  have hqN : ¬ ((Ideal.absNorm P : ℕ) : ℤ) ∣ Nv := by
    rintro ⟨k, hk⟩
    apply hNP
    rw [hk, Int.cast_mul, Int.cast_natCast]
    exact P.mul_mem_right _ (Ideal.absNorm_mem P)
  refine ⟨Ideal.absNorm P, P, ?_⟩
  unfold _root_.GlobalTheory.SW.GoodPrime
  refine ⟨hq, ?_, rfl, ?_, fun h => hqN ?_⟩
  · refine (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr fun h => hqN ?_)).symm
    rw [hNv, mul_assoc]
    exact Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr h) _
  · rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have hle : _root_.GlobalTheory.SW.conjI P ≤ P := by
      have := hP.eq_of_le hne le_sup_left
      exact le_sup_right.trans this.symm.le
    obtain ⟨n0, hn0⟩ := hs (Ideal.Quotient.mk P θ)
    have h1 : θ - (n0 : 𝓞 E) ∈ P := by
      rw [← Ideal.Quotient.eq, ← hn0, eq_intCast, map_intCast]
    have h2 : θc - (n0 : 𝓞 E) ∈ P := by
      apply hle
      unfold _root_.GlobalTheory.SW.conjI
      apply Ideal.subset_span
      refine ⟨θ - (n0 : 𝓞 E), h1, ?_⟩
      change ((θc : E) - ((n0 : 𝓞 E) : E)) = _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ((θ : E) - ((n0 : 𝓞 E) : E))
      have hn : ((n0 : 𝓞 E) : E) = (n0 : E) := by push_cast; rfl
      rw [hn, hcc, map_sub, map_intCast]
      rfl
    have h3 : θ - θc ∈ P := by
      have := P.sub_mem h1 h2
      rwa [sub_sub_sub_cancel_right] at this
    have h4 : ((Algebra.norm ℤ (θ - θc) : ℤ) : 𝓞 E) ∈ P := by
      have h5 : (((Algebra.norm ℤ (θ - θc)).natAbs : ℕ) : 𝓞 E) ∈ P := by
        have := Ideal.absNorm_mem (Ideal.span {θ - θc})
        rw [Ideal.absNorm_span_singleton] at this
        exact (Ideal.span_singleton_le_iff_mem P).mpr h3 this
      rcases Int.natAbs_eq (Algebra.norm ℤ (θ - θc)) with h6 | h6
      · rw [h6, Int.cast_natCast]; exact h5
      · rw [h6, Int.cast_neg, Int.cast_natCast]; exact P.neg_mem h5
    apply hNP
    rw [hNv, Int.cast_mul]
    exact P.mul_mem_left _ h4
  · rw [hNv, mul_comm (m : ℤ), mul_assoc]
    exact Dvd.dvd.mul_right h _
end _root_.GlobalTheory.SW.SplitPrime
end GlobalTheory.SW.SplitPrime
