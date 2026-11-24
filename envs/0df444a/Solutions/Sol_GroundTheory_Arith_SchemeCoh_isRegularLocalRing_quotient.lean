-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isRegularLocalRing_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:06.556849+00:00
-- url     : https://prove2.me/submissions/0d735ee1-4a21-4446-8d77-14c206cd36fe

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_spanFinrank_maximalIdeal_quotient_add_one_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open IsLocalRing Ideal
universe u
variable {R : Type u} [CommRing R]
private lemma exists_nat_of_le_add_one {d : WithBot ℕ∞} {n b : ℕ} (h2 : (n : WithBot ℕ∞) ≤ d + 1)
    (h3 : d ≤ b) : ∃ k : ℕ, d = k := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h2
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h4 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((b : ℕ∞) : WithBot ℕ∞) := h3
      rw [WithBot.coe_le_coe, top_le_iff] at h4
      exact ENat.natCast_ne_top b h4
    | coe k => exact ⟨k, rfl⟩
end GroundTheory.Arith.SchemeCoh
end

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing Ideal
universe u
variable {R : Type u} [CommRing R]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution [IsRegularLocalRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ span {x})] :
    IsRegularLocalRing (R ⧸ span {x}) ∧ ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R := by
  have h1 := spanFinrank_maximalIdeal_quotient_add_one_le hx hx2
  have hR : ringKrullDim R = ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
    ((isRegularLocalRing_iff R).mp inferInstance).symm
  have h2 : ringKrullDim R ≤ ringKrullDim (R ⧸ span {x}) + 1 := by
    refine (ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (span {x}) ?_).trans ?_
    · rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
      exact (span_singleton_le_iff_mem _).mpr hx
    · gcongr
      exact_mod_cast (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton x)).trans
        (by simp)
  have h3 := ringKrullDim_le_spanFinrank_maximalIdeal (R := R ⧸ span {x})
  rw [hR] at h2
  obtain ⟨k, hk⟩ := exists_nat_of_le_add_one h2 h3
  rw [hk] at h2 h3 ⊢
  have h2' : (maximalIdeal R).spanFinrank ≤ k + 1 := by exact_mod_cast h2
  have h3' : k ≤ (maximalIdeal (R ⧸ span {x})).spanFinrank := by exact_mod_cast h3
  have hk' : (maximalIdeal (R ⧸ span {x})).spanFinrank = k := by omega
  refine ⟨(isRegularLocalRing_iff _).mpr (by rw [hk, hk']), ?_⟩
  rw [hR]
  exact_mod_cast (by omega : k + 1 = (maximalIdeal R).spanFinrank)
end GroundTheory.Arith.SchemeCoh
