-- Prove2me | solution 1 for ModularCurve.natCard_eisensteinPrimaryTorsionBar_quotient_eq_pow_alpha_of_multiplicativeTypeNat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/db8d56f2-f23a-5429-a3f0-0404855de194

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Definitions.Def_ModularCurve_MultiplicativeType
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_GaloisRep_natCard_quotient_eq_natCard_ringHom_algClosure_of_finiteFlatHopf_of_multiplicativeTypeNat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_natCard_eisensteinPrimaryTorsionBar_quotient_eq_pow_alpha_of_multiplicativeTypeNat
p2m_attr_erase "instance" "instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff"

open ModularCurve

namespace G1hEngine

theorem nsmul_pow_eq_zero (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (m : ℕ)
    (x : ↥(eisensteinPrimaryTorsionBar p q m)) : q ^ m • x = 0 := by
  refine Subtype.ext ?_
  have hx : (x : JZero p) ∈ eisensteinPrimaryTorsionBar p q m := x.2

  have hker : (x : JZero p) ∈ AddMonoidHom.ker ((q ^ m : ℤ) • AddMonoidHom.id (JZero p)) :=
    (AddSubgroup.mem_inf.mp hx).1
  have h0 : ((q : ℤ) ^ m) • (x : JZero p) = 0 := by
    change ((q : ℤ) ^ m) • (x : JZero p) = 0 at hker
    exact hker
  have hcoe : ((q ^ m • x : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)
      = (q ^ m : ℕ) • (x : JZero p) :=
    AddMonoidHom.map_nsmul ((eisensteinPrimaryTorsionBar p q m).subtype) (q ^ m) x
  rw [hcoe, ← natCast_zsmul, Nat.cast_pow, h0]
  rfl

def algHomEquivRingHom (q : ℕ) (B C : Type) [CommRing B] [CommRing C]
    [Algebra (ZMod q) B] [Algebra (ZMod q) C] : (B →ₐ[ZMod q] C) ≃ (B →+* C) where
  toFun f := f.toRingHom
  invFun g :=
    { g with
      commutes' := fun r =>
        congrArg (fun φ : ZMod q →+* C => φ r)
          (RingHom.ext_zmod (g.comp (algebraMap (ZMod q) B)) (algebraMap (ZMod q) C)) }
  left_inv f := by ext; rfl
  right_inv g := by ext; rfl

theorem bridge_ringHom_eq_algHom_barQ (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (hqp : q ≠ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (S : JZeroNeronPrimaryTorsionSheaf p q A hA) (m : ℕ) :
    Nat.card (S.ffModels.Hff m q Fact.out hqp →+* AlgebraicClosure (ZMod q))
      = Nat.card (WithConv (S.ffModels.HffBarQ m hqp →ₐ[ZMod q] AlgebraicClosure (ZMod q))) := by
  have hker : ∀ g : S.ffModels.Hff m q Fact.out hqp →+* AlgebraicClosure (ZMod q),
      RingHom.ker (S.ffModels.ffBarQ_red m hqp) ≤ RingHom.ker g := by
    intro g
    rw [S.ffModels.ffBarQ_red_ker m hqp, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      RingHom.mem_ker, map_intCast, Int.cast_natCast]
    exact CharP.cast_eq_zero _ q
  exact Nat.card_congr
    ((((Equiv.subtypeUnivEquiv hker).symm.trans
      ((S.ffModels.ffBarQ_red m hqp).liftOfSurjective (S.ffModels.ffBarQ_red_surjective m hqp))).trans
      (algHomEquivRingHom q _ _).symm).trans
      (WithConv.equiv _).symm)

end G1hEngine

theorem solution
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (S : JZeroNeronPrimaryTorsionSheaf p q A hA)
    (Aq : ValuationSubring (AlgebraicClosure ℚ)) (hAq : Aq.LiesOverPrime q) :
    ∀ m, ∀ n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ,
      (∀ σ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ (q ^ m) = 1 → σ ζ = ζ ^ n σ) →
    ∀ W : AddSubgroup (JZero p),
      W ≤ eisensteinPrimaryTorsionBar p q m →
      MultiplicativeTypeNat (Aq.inertiaSubgroupIn ℚ) n W →
      (∀ σ ∈ Aq.inertiaSubgroupIn ℚ, ∀ x ∈ eisensteinPrimaryTorsionBar p q m,
        σ • (x : JZero p) - x ∈ W) →
      Nat.card (↥(eisensteinPrimaryTorsionBar p q m) ⧸ W.addSubgroupOf (eisensteinPrimaryTorsionBar p q m))
        = q ^ (S.invPins.inv m).α := by
  intro m n hn W hWle hμ hcos
  have key :=
    GaloisRep.natCard_quotient_eq_natCard_ringHom_algClosure_of_finiteFlatHopf_of_multiplicativeTypeNat
      q hq2 (S.ffModels.Hff m q Fact.out hqp) (eisensteinPrimaryTorsionBar p q m)
      (S.ffModels.ffPoints m q Fact.out hqp) (S.ffModels.ffConv m q Fact.out hqp) (S.ffModels.ffGalois m q Fact.out hqp)
      Aq hAq m n hn (G1hEngine.nsmul_pow_eq_zero p q m) W hWle hμ hcos
  rw [key, G1hEngine.bridge_ringHom_eq_algHom_barQ p q hqp A hA S m, S.invPins.α_pin m hqp]

end S_ModularCurve_natCard_eisensteinPrimaryTorsionBar_quotient_eq_pow_alpha_of_multiplicativeTypeNat
end P2MW
export P2MW.S_ModularCurve_natCard_eisensteinPrimaryTorsionBar_quotient_eq_pow_alpha_of_multiplicativeTypeNat (solution)
