-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_fixedVectors_mk_eq_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:03:05.717206+00:00
-- url     : https://prove2.me/submissions/4a843d55-ca36-43b1-be64-151a3ede836f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {N M Nbar K : Subgroup G}
omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
namespace GroundTheory.Automorphic
theorem _root_.solution (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G))
    (hfact : ∀ k ∈ K, ∃ x ∈ K ⊓ N, ∃ y ∈ K ⊓ M, ∃ z ∈ K ⊓ Nbar, k = x * y * z)
    {w : V} (hwNbar : ∀ z ∈ K ⊓ Nbar, ρ z w = w)
    (hwM : ∀ y ∈ K ⊓ M, Representation.Coinvariants.mk (ρ.comp N.subtype) (ρ y w) =
      Representation.Coinvariants.mk (ρ.comp N.subtype) w) :
    ∃ x ∈ fixedVectors ρ K, Representation.Coinvariants.mk (ρ.comp N.subtype) x =
      Representation.Coinvariants.mk (ρ.comp N.subtype) w := by
  classical
  set S : Subgroup G := stabilizerOf ρ w ⊓ K with hS
  have hSo : IsOpen (S : Set G) := by
    rw [hS, Subgroup.coe_inf]
    exact (hρ w).inter hKo
  have : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have hfin : Finite (K ⧸ S.subgroupOf K) := by
    refine Subgroup.quotient_finite_of_isOpen _ ?_
    rw [Subgroup.coe_subgroupOf]
    exact hSo.preimage continuous_subtype_val
  have := Fintype.ofFinite (K ⧸ S.subgroupOf K)
  set n : ℂ := (Fintype.card (K ⧸ S.subgroupOf K) : ℂ)
  have hn : n ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero

  have hterm : ∀ k ∈ K, Representation.Coinvariants.mk (ρ.comp N.subtype) (ρ k w) =
      Representation.Coinvariants.mk (ρ.comp N.subtype) w := by
    intro k hk
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := hfact k hk
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hwNbar z hz,
      mk_apply_of_mem ρ N (Subgroup.mem_inf.1 hx).2, hwM y hy]

  have hrep : ∀ (k : K) (c : K ⧸ S.subgroupOf K),
      ρ ((k : G) * ((Quotient.out c : K) : G)) w = ρ ((Quotient.out (k • c) : K) : G) w := by
    intro k c
    have h1 : (QuotientGroup.mk (Quotient.out (k • c)) : K ⧸ S.subgroupOf K) =
        QuotientGroup.mk (k * Quotient.out c) := by
      rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk,
        QuotientGroup.out_eq']
    rw [QuotientGroup.eq] at h1
    have h2 : ((Quotient.out (k • c) : K) : G)⁻¹ * ((k : G) * ((Quotient.out c : K) : G)) ∈
        stabilizerOf ρ w := by
      have := (Subgroup.mem_subgroupOf.1 h1)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      exact (Subgroup.mem_inf.1 this).1
    rw [← mul_inv_cancel_left ((Quotient.out (k • c) : K) : G)
      ((k : G) * ((Quotient.out c : K) : G)), map_mul, Module.End.mul_apply,
      mem_stabilizerOf.1 h2]
  set y : V := ∑ c : K ⧸ S.subgroupOf K, ρ ((Quotient.out c : K) : G) w with hy
  have hyK : y ∈ fixedVectors ρ K := by
    intro k hk
    rw [hy, map_sum]
    simp only [← Module.End.mul_apply, ← map_mul]
    calc ∑ c : K ⧸ S.subgroupOf K, ρ (k * ((Quotient.out c : K) : G)) w
        = ∑ c : K ⧸ S.subgroupOf K,
            ρ ((Quotient.out ((⟨k, hk⟩ : K) • c) : K) : G) w :=
          Finset.sum_congr rfl fun c _ => hrep ⟨k, hk⟩ c
      _ = ∑ c : K ⧸ S.subgroupOf K, ρ ((Quotient.out c : K) : G) w :=
          Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _
            (fun c => by rw [MulAction.toPerm_apply])
  have hyq : Representation.Coinvariants.mk (ρ.comp N.subtype) y =
      n • Representation.Coinvariants.mk (ρ.comp N.subtype) w := by
    rw [hy, map_sum, Finset.sum_congr rfl fun c _ => hterm _ (Quotient.out c).2,
      Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
  refine ⟨n⁻¹ • y, Submodule.smul_mem _ _ hyK, ?_⟩
  rw [map_smul, hyq, smul_smul, inv_mul_cancel₀ hn, one_smul]
end GroundTheory.Automorphic
