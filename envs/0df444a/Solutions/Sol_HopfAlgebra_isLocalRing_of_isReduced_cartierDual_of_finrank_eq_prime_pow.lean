-- Prove2me | solution 1 for HopfAlgebra.isLocalRing_of_isReduced_cartierDual_of_finrank_eq_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/a47901c9-19d7-53be-a283-49e6db8d8d7f

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_CartierDual_exists_algHomEquiv_groupLike
import Theorems.Thm_AlgHom_natCard_eq_finrank_of_isReduced_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_isLocalRing_of_isReduced_cartierDual_of_finrank_eq_prime_pow

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

universe u v w

namespace HopfAlgebra
namespace MultLocal
p2m_open "HopfAlgebra"

variable (k : Type u) [Field k] (N : Type v) [CommRing N] [HopfAlgebra k N] [Coalgebra.IsCocomm k N]
  [Module.Finite k N]

noncomputable def groupLikeBaseChangeSelfEquiv : GroupLike k (k ⊗[k] N) ≃ GroupLike k N where
  toFun g := ⟨Bialgebra.TensorProduct.lid k N g.val, g.2.map (Bialgebra.TensorProduct.lid k N)⟩
  invFun g := ⟨(Bialgebra.TensorProduct.lid k N).symm g.val, g.2.map (Bialgebra.TensorProduct.lid k N).symm⟩
  left_inv g := by ext; exact (Bialgebra.TensorProduct.lid k N).symm_apply_apply g.val
  right_inv g := by ext; exact (Bialgebra.TensorProduct.lid k N).apply_symm_apply g.val

theorem natCard_groupLike_eq_finrank [IsAlgClosed k] (hred : IsReduced (CartierDual k N)) :
    Nat.card (GroupLike k N) = Module.finrank k N := by
  obtain ⟨e, -, -, -, -⟩ := CartierDual.exists_algHomEquiv_groupLike k N
  haveI := hred
  calc Nat.card (GroupLike k N) = Nat.card (GroupLike k (k ⊗[k] N)) :=
        Nat.card_congr (groupLikeBaseChangeSelfEquiv k N).symm
    _ = Nat.card (CartierDual k N →ₐ[k] k) := Nat.card_congr (e k).symm
    _ = Module.finrank k (CartierDual k N) :=
        AlgHom.natCard_eq_finrank_of_isReduced_of_isAlgClosed k (CartierDual k N)
    _ = Module.finrank k N := CartierDual.finrank_eq k N

theorem isLocalRing_of_isReduced_cartierDual [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hred : IsReduced (CartierDual k N)) (m : ℕ) (hN : Module.finrank k N = p ^ m) : IsLocalRing N := by
  classical

  have hpos : 0 < Module.finrank k N := by rw [hN]; exact pow_pos (Nat.Prime.pos Fact.out) _
  haveI : Nontrivial N := Module.nontrivial_of_finrank_pos (R := k) hpos
  haveI : CharP N p := charP_of_injective_algebraMap (algebraMap k N).injective p

  haveI : Finite (GroupLike k N) := Nat.finite_of_card_ne_zero (by
    rw [natCard_groupLike_eq_finrank k N hred]; exact hpos.ne')
  haveI := Fintype.ofFinite (GroupLike k N)
  have hcard : Fintype.card (GroupLike k N) = Module.finrank k N := by
    rw [← Nat.card_eq_fintype_card, natCard_groupLike_eq_finrank k N hred]
  have hspan : Submodule.span k (Set.range (GroupLike.val (R := k) (A := N))) = ⊤ :=
    (linearIndep_groupLikeVal (R := k) (A := N)).span_eq_top_of_card_eq_finrank' hcard

  have hnil : ∀ g : GroupLike k N, IsNilpotent (g.val - 1) := fun g => by
    refine ⟨p ^ m, ?_⟩
    have hg : g ^ p ^ m = 1 := by rw [← hN, ← hcard]; exact pow_card_eq_one
    rw [sub_pow_char_pow, one_pow, ← GroupLike.val_pow, hg, GroupLike.val_one, sub_self]

  let 𝔪 : Ideal N := RingHom.ker (Bialgebra.counitAlgHom k N)
  have hεsurj : Function.Surjective (Bialgebra.counitAlgHom k N) := fun c =>
    ⟨algebraMap k N c, Bialgebra.counit_algebraMap c⟩
  have h𝔪max : 𝔪.IsMaximal := RingHom.ker_isMaximal_of_surjective (Bialgebra.counitAlgHom k N) hεsurj

  have h𝔪nil : 𝔪 ≤ nilradical N := by
    intro x hx
    have hx0 : Coalgebra.counit (R := k) x = 0 := hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 (by rw [hspan]; exact Submodule.mem_top (x := x))
    have hsum : (∑ g, c g) = 0 := by
      have := hx0
      rw [map_sum] at this
      simpa only [map_smul, (GroupLike.isGroupLikeElem_val _).counit_eq_one, smul_eq_mul, mul_one]
        using this
    have hrw : (∑ g, c g • (g : GroupLike k N).val) = ∑ g, c g • ((g : GroupLike k N).val - 1) := by
      rw [← sub_zero (∑ g, c g • (g : GroupLike k N).val), ← zero_smul k (1 : N), ← hsum, Finset.sum_smul,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [smul_sub]
    rw [hrw]
    refine Ideal.sum_mem _ fun g _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (mem_nilradical.2 (hnil g))

  refine IsLocalRing.of_unique_max_ideal ⟨𝔪, h𝔪max, fun M hM => ?_⟩
  haveI := hM
  exact (h𝔪max.eq_of_le hM.ne_top (h𝔪nil.trans (nilradical_le_prime M))).symm

end HopfAlgebra.MultLocal

open HopfAlgebra.MultLocal in
theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (N : Type v) [CommRing N] [HopfAlgebra k N] [Coalgebra.IsCocomm k N] [Module.Finite k N]
    (hred : IsReduced (CartierDual k N)) (m : ℕ) (hN : Module.finrank k N = p ^ m) :
    IsLocalRing N :=
  HopfAlgebra.MultLocal.isLocalRing_of_isReduced_cartierDual k N p hred m hN

end S_HopfAlgebra_isLocalRing_of_isReduced_cartierDual_of_finrank_eq_prime_pow
end P2MW
export P2MW.S_HopfAlgebra_isLocalRing_of_isReduced_cartierDual_of_finrank_eq_prime_pow (solution)
