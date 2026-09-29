-- Prove2me | solution 1 for Ideal.forall_isPrime_mem_of_sum_finrank_quotient_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/9aaccf4f-ebd4-5dd6-b320-bba34bd5d174

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_forall_isPrime_mem_of_sum_finrank_quotient_eq_finrank

set_option autoImplicit false

theorem solution
    (F R : Type) [Field F] [CommRing R] [Algebra F R] [Module.Finite F R] [IsReduced R]
    (S : Finset (Ideal R)) (hS : ∀ 𝔭 ∈ S, 𝔭.IsPrime)
    (hsum : ∑ 𝔭 ∈ S, Module.finrank F (R ⧸ 𝔭) = Module.finrank F R) :
    ∀ 𝔭 : Ideal R, 𝔭.IsPrime → 𝔭 ∈ S := by
  classical
  haveI : IsArtinianRing R := IsArtinianRing.of_finite F R
  intro 𝔮 h𝔮
  by_contra hq

  have hmax : ∀ 𝔭 ∈ insert 𝔮 S, 𝔭.IsMaximal := by
    intro 𝔭 hp
    rcases Finset.mem_insert.mp hp with h | hp
    · rw [h]; haveI := h𝔮; exact IsArtinianRing.isMaximal_of_isPrime 𝔮
    · haveI := hS 𝔭 hp; exact IsArtinianRing.isMaximal_of_isPrime 𝔭
  set T : Finset (Ideal R) := insert 𝔮 S with hT

  have hcop : Pairwise fun (i j : ↥T) => IsCoprime (i : Ideal R) (j : Ideal R) := by
    intro i j hij
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne (hmax i i.2) (hmax j j.2)
      (fun h => hij (Subtype.ext h))

  haveI hfin : ∀ p : ↥T, Module.Finite F (R ⧸ (p : Ideal R)) := fun p =>
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ F (p : Ideal R)).toLinearMap
      (Ideal.Quotient.mkₐ_surjective F _)
  haveI hfree : ∀ p : ↥T, Module.Free F (R ⧸ (p : Ideal R)) := fun p =>
    Module.Free.of_divisionRing F _
  let φ : R →ₗ[F] (∀ p : ↥T, R ⧸ (p : Ideal R)) :=
    LinearMap.pi fun p => (Ideal.Quotient.mkₐ F (p : Ideal R)).toLinearMap
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨xb, hxb⟩ := Ideal.quotientInfToPiQuotient_surj hcop y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xb
    refine ⟨x, ?_⟩
    rw [← hxb]
    ext p
    rfl
  have hle : Module.finrank F (∀ p : ↥T, R ⧸ (p : Ideal R)) ≤ Module.finrank F R :=
    LinearMap.finrank_le_finrank_of_surjective hφ
  rw [Module.finrank_pi_fintype, Finset.sum_coe_sort T (fun p => Module.finrank F (R ⧸ p)),
    hT, Finset.sum_insert hq, hsum] at hle
  haveI := h𝔮
  haveI : Nontrivial (R ⧸ 𝔮) := inferInstance
  haveI : Module.Finite F (R ⧸ 𝔮) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ F 𝔮).toLinearMap (Ideal.Quotient.mkₐ_surjective F _)
  have hpos : 0 < Module.finrank F (R ⧸ 𝔮) := Module.finrank_pos
  omega

end S_Ideal_forall_isPrime_mem_of_sum_finrank_quotient_eq_finrank
end P2MW
export P2MW.S_Ideal_forall_isPrime_mem_of_sum_finrank_quotient_eq_finrank (solution)
