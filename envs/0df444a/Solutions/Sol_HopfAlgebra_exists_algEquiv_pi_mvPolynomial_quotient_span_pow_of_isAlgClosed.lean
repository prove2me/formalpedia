-- Prove2me | solution 1 for HopfAlgebra.exists_algEquiv_pi_mvPolynomial_quotient_span_pow_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/0f096e2f-76a7-5ee8-b2fa-58d708fdcd4e

import Mathlib
import Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_isLocalRing_algEquiv_pi_of_isAlgClosed
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Theorems.Thm_HopfAlgebra_exists_algEquiv_mvPolynomial_quotient_span_pow_of_isLocalRing_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_algEquiv_pi_mvPolynomial_quotient_span_pow_of_isAlgClosed
p2m_attr_erase "instance" "HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient HopfAlgebra.IsHopfTower.refl HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul"

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

universe u

open scoped TensorProduct

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] (B : Type u) [CommRing B] [HopfAlgebra k B] [Module.Finite k B] :
    ∃ (n r : ℕ) (q : Fin r → ℕ),
      (∀ i, 1 < q i ∧ ∃ e : ℕ, q i = ringExpChar k ^ e) ∧
      Nonempty (B ≃ₐ[k] (Fin n → (MvPolynomial (Fin r) k ⧸ Ideal.span (Set.range fun i => (MvPolynomial.X i : MvPolynomial (Fin r) k) ^ q i)))) := by
  classical
  obtain ⟨n, B₀, _, _, _, π, hn, hloc, hπ, ⟨eB⟩⟩ := HopfAlgebra.exists_hopfAlgebra_isLocalRing_algEquiv_pi_of_isAlgClosed k B
  haveI : IsLocalRing B₀ := hloc

  rcases CharP.exists k with ⟨p, hp⟩
  by_cases hp0 : p = 0
  ·
    subst hp0
    haveI : CharZero k := CharP.charP_to_charZero k
    haveI : Algebra.FiniteType k B₀ := Module.Finite.finiteType (R := k) (A := B₀)
    have hred : IsReduced B₀ := HopfAlgebra.isReduced_of_finiteType_of_charZero k B₀

    haveI : IsArtinianRing B₀ := IsArtinianRing.of_finite k B₀
    have hmax : IsLocalRing.maximalIdeal B₀ = ⊥ := by
      obtain ⟨m, hm⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B₀)
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hm
      refine le_bot_iff.1 fun x hx => ?_
      have : x ^ m ∈ (IsLocalRing.maximalIdeal B₀) ^ m := Ideal.pow_mem_pow hx m
      rw [hm, Ideal.zero_eq_bot, Ideal.mem_bot] at this
      exact (IsReduced.eq_zero x ⟨m, this⟩ : x = 0)
    have hF : IsField B₀ := (IsLocalRing.isField_iff_maximalIdeal_eq).2 hmax
    haveI : IsDomain B₀ := hF.isDomain
    have hbij : Function.Bijective (algebraMap k B₀) := IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e1 : B₀ ≃ₐ[k] k := (AlgEquiv.ofBijective (Algebra.ofId k B₀) hbij).symm

    have hI : Ideal.span (Set.range fun i : Fin 0 => (MvPolynomial.X i : MvPolynomial (Fin 0) k) ^ (Fin.elim0 i : ℕ)) =
        RingHom.ker (AlgHom.id k (MvPolynomial (Fin 0) k)) := by
      rw [Set.range_eq_empty, Ideal.span_empty]; ext x; simp
    let e2 : (MvPolynomial (Fin 0) k ⧸ Ideal.span (Set.range fun i : Fin 0 => (MvPolynomial.X i : MvPolynomial (Fin 0) k) ^ (Fin.elim0 i : ℕ)))
        ≃ₐ[k] k :=
      ((Ideal.quotientEquivAlgOfEq k hI).trans (Ideal.quotientKerAlgEquivOfSurjective Function.surjective_id)).trans
        (MvPolynomial.isEmptyAlgEquiv k (Fin 0))
    refine ⟨n, 0, Fin.elim0, fun i => Fin.elim0 i, ⟨eB.trans (AlgEquiv.piCongrRight fun _ => e1.trans e2.symm)⟩⟩
  ·
    have hpp : p.Prime := (CharP.char_is_prime_or_zero k p).resolve_right hp0
    haveI : Fact p.Prime := ⟨hpp⟩
    haveI : ExpChar k p := ExpChar.prime hpp
    obtain ⟨r, e, he, ⟨eI⟩⟩ := HopfAlgebra.exists_algEquiv_mvPolynomial_quotient_span_pow_of_isLocalRing_of_perfectField k p B₀
    refine ⟨n, r, fun i => p ^ e i, fun i => ⟨Nat.one_lt_pow (he i).ne' hpp.one_lt, e i, ?_⟩,
      ⟨eB.trans (AlgEquiv.piCongrRight fun _ => eI)⟩⟩
    rw [ringExpChar.eq k p]

end S_HopfAlgebra_exists_algEquiv_pi_mvPolynomial_quotient_span_pow_of_isAlgClosed
end P2MW
export P2MW.S_HopfAlgebra_exists_algEquiv_pi_mvPolynomial_quotient_span_pow_of_isAlgClosed (solution)
