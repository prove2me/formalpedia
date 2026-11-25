-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.mk_fixedProj_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:55:44.637786+00:00
-- url     : https://prove2.me/submissions/8d5ea7c9-7375-484a-9a03-d34e74805c7f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_eq_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
open scoped Pointwise
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {N M Nbar K : Subgroup G}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (hfact : ∀ k ∈ K, ∃ x ∈ K ⊓ N, ∃ y ∈ K ⊓ M, ∃ z ∈ K ⊓ Nbar, k = x * y * z)
    {w : V} (hwNbar : ∀ z ∈ K ⊓ Nbar, ρ z w = w)
    (hwM : ∀ y ∈ K ⊓ M, Representation.Coinvariants.mk (ρ.comp N.subtype) (ρ y w) =
      Representation.Coinvariants.mk (ρ.comp N.subtype) w) :
    Representation.Coinvariants.mk (ρ.comp N.subtype) (fixedProj ρ hρ hKc hKo w : V) =
      Representation.Coinvariants.mk (ρ.comp N.subtype) w := by
  classical
  have hterm : ∀ k ∈ K, Representation.Coinvariants.mk (ρ.comp N.subtype) (ρ k w) =
      Representation.Coinvariants.mk (ρ.comp N.subtype) w := by
    intro k hk
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := hfact k hk
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hwNbar z hz,
      mk_apply_of_mem ρ N (Subgroup.mem_inf.1 hx).2, hwM y hy]
  obtain ⟨N', -, -, hN'U, hnorm, hfin⟩ := exists_normal_subgroup hKc hKo
    ((hρ w).mem_nhds (one_mem (stabilizerOf ρ w)))
  have := Fintype.ofFinite (K ⧸ N'.subgroupOf K)
  have hw' : w ∈ fixedVectors ρ N' := fun k hk => hN'U hk
  set c : ℂ := (Fintype.card (K ⧸ N'.subgroupOf K) : ℂ)
  have hc : c ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hyK : c⁻¹ • cosetSum ρ K N' w ∈ fixedVectors ρ K :=
    Submodule.smul_mem _ _ (cosetSum_mem_fixedVectors ρ hnorm hw')
  have hey : fixedProj ρ hρ hKc hKo w = ⟨c⁻¹ • cosetSum ρ K N' w, hyK⟩ := by
    rw [fixedProj_eq_iff]
    have heq : w - c⁻¹ • cosetSum ρ K N' w =
        c⁻¹ • ∑ q : K ⧸ N'.subgroupOf K, (w - ρ ((Quotient.out q : K) : G) w) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← cosetSum_apply, smul_sub,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
    show w - c⁻¹ • cosetSum ρ K N' w ∈ coinvariantsKer ρ K
    rw [heq]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ?_)
    rw [← neg_sub]
    exact Submodule.neg_mem _ (sub_mem_coinvariantsKer (Quotient.out q).2 w)
  rw [hey]
  show Representation.Coinvariants.mk (ρ.comp N.subtype) (c⁻¹ • cosetSum ρ K N' w) = _
  rw [map_smul, cosetSum_apply, map_sum,
    Finset.sum_congr rfl fun q _ => hterm _ (Quotient.out q).2, Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
end GroundTheory.Automorphic.Parabolic
