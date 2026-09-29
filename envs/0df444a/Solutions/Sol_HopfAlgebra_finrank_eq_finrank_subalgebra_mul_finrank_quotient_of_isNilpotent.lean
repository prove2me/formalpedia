-- Prove2me | solution 1 for HopfAlgebra.finrank_eq_finrank_subalgebra_mul_finrank_quotient_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/8e60943a-a70f-5275-b3a4-9e17f81bd318

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_HopfAlgebra_HopfTower
import Theorems.Thm_HopfAlgebra_faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_finrank_eq_finrank_subalgebra_mul_finrank_quotient_of_isNilpotent

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct
open Function

universe u v

namespace HopfAlgebra
p2m_export "HopfAlgebra" "faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem"
namespace OrderMultiplicativity
p2m_open "HopfAlgebra"

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H] [Module.Finite k H]
variable (hH : ∀ x : H, Coalgebra.counit (R := k) x = 0 → IsNilpotent x)
variable (S : Subalgebra k H)

theorem counit_algebraMap (c : k) : Coalgebra.counit (R := k) (algebraMap k H c) = c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one]

include k in
theorem nontrivial_H : Nontrivial H :=
  ⟨⟨0, 1, fun h => zero_ne_one (by
    have := congrArg (Coalgebra.counit (R := k) (A := H)) h
    rwa [map_zero, Bialgebra.counit_one] at this)⟩⟩

def εS : ↥S →ₐ[k] k := (Bialgebra.counitAlgHom k H).comp S.val

theorem εS_apply (x : ↥S) : εS S x = Coalgebra.counit (R := k) (x : H) := rfl

theorem εS_surjective : Surjective (εS S) := fun c =>
  ⟨algebraMap k (↥S) c, by rw [εS_apply, Subalgebra.coe_algebraMap, counit_algebraMap]⟩

def mS : Ideal ↥S := RingHom.ker (εS S)

theorem mem_mS {x : ↥S} : x ∈ mS S ↔ Coalgebra.counit (R := k) (x : H) = 0 := RingHom.mem_ker

theorem mS_ne_top : mS S ≠ ⊤ := by
  intro h
  have : (1 : ↥S) ∈ mS S := by rw [h]; exact Submodule.mem_top
  rw [mem_mS, OneMemClass.coe_one, Bialgebra.counit_one] at this
  exact one_ne_zero this

theorem map_mS_eq :
    (mS S).map (algebraMap (↥S) H) =
      Ideal.span {x : H | x ∈ S ∧ Coalgebra.counit (R := k) x = 0} := by
  change Ideal.span _ = Ideal.span _
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, (mem_mS S).1 hy⟩
  · rintro ⟨hxS, hx⟩
    exact ⟨⟨x, hxS⟩, (mem_mS S).2 hx, rfl⟩

include hH in

theorem isLocalRing_S : IsLocalRing ↥S := by
  haveI : Nontrivial H := nontrivial_H (k := k)
  haveI : Nontrivial ↥S := ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h : ((0 : ↥S) : H) = 1)⟩⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  have hnil : ∀ y : ↥S, Coalgebra.counit (R := k) (y : H) = 0 → IsNilpotent y := fun y hy => by
    obtain ⟨N, hN⟩ := hH (y : H) hy
    exact ⟨N, Subtype.ext (by rw [SubmonoidClass.coe_pow, hN]; rfl)⟩
  by_cases hx : Coalgebra.counit (R := k) (x : H) = 0
  · exact Or.inr (hnil x hx).isUnit_one_sub
  · left
    have hn : IsNilpotent (x - algebraMap k (↥S) (Coalgebra.counit (R := k) (x : H))) := hnil _ (by
      rw [AddSubgroupClass.coe_sub, Subalgebra.coe_algebraMap, map_sub, counit_algebraMap, sub_self])
    have hu : IsUnit (algebraMap k (↥S) (Coalgebra.counit (R := k) (x : H))) :=
      (isUnit_iff_ne_zero.2 hx).map _
    have := hn.isUnit_add_left_of_commute hu (Commute.all _ _)
    rwa [add_sub_cancel] at this

theorem finrank_quotient_mS : Module.finrank k (↥S ⧸ mS S) = 1 :=
  (Ideal.quotientKerAlgEquivOfSurjective (εS_surjective S)).toLinearEquiv.finrank_eq.trans
    (Module.finrank_self k)

theorem finrank_quotient_eq_card {ι : Type*} [Fintype ι] (b : Module.Basis ι (↥S) H) :
    Module.finrank k (H ⧸ Ideal.span {x : H | x ∈ S ∧ Coalgebra.counit (R := k) x = 0}) =
      Fintype.card ι := by
  classical
  set J : Ideal H := Ideal.span {x : H | x ∈ S ∧ Coalgebra.counit (R := k) x = 0} with hJdef

  let T : H →ₗ[k] (ι → k) :=
    { toFun := fun h i => εS S (b.repr h i)
      map_add' := fun u v => by
        funext i
        simp only [map_add, Finsupp.coe_add, Pi.add_apply]
      map_smul' := fun c u => by
        funext i
        rw [RingHom.id_apply, Pi.smul_apply, ← IsScalarTower.algebraMap_smul (↥S) c u, map_smul,
          Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, AlgHom.commutes, smul_eq_mul,
          Algebra.algebraMap_self_apply] }
  have hT : ∀ h i, T h i = εS S (b.repr h i) := fun h i => rfl

  have hTsurj : Function.Surjective T := fun c => by
    refine ⟨∑ i, algebraMap k (↥S) (c i) • b i, funext fun i => ?_⟩
    rw [hT, map_sum, Finset.sum_apply']
    simp_rw [map_smul, b.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ i), AlgHom.commutes, Algebra.algebraMap_self_apply]

  have hJS : (mS S • (⊤ : Submodule (↥S) H)) = J.restrictScalars (↥S) := by
    rw [Ideal.smul_top_eq_map, map_mS_eq]
  have hker : LinearMap.ker T = J.restrictScalars k := by
    have hJk : J.restrictScalars k = (mS S • (⊤ : Submodule (↥S) H)).restrictScalars k := by
      rw [hJS, Submodule.restrictScalars_restrictScalars]
    rw [hJk]
    ext h
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem]
    constructor
    · intro hh
      rw [← b.sum_repr h]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
      exact (mem_mS S).2 (by have := congrFun hh i; rwa [hT, εS_apply] at this)
    · intro hh
      funext i
      rw [hT, Pi.zero_apply]
      refine Submodule.smul_induction_on hh (fun m hm u _ => ?_) (fun u v hu hv => ?_)
      · rw [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul,
          show εS S m = 0 from hm, zero_mul]
      · rw [map_add, Finsupp.coe_add, Pi.add_apply, map_add, hu, hv, add_zero]
  have e : (H ⧸ J) ≃ₗ[k] (ι → k) :=
    (Submodule.Quotient.restrictScalarsEquiv k J).symm ≪≫ₗ
      (Submodule.quotEquivOfEq _ _ hker.symm) ≪≫ₗ T.quotKerEquivOfSurjective hTsurj
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card]

include hH in

theorem main
    (hΔ : ∀ x ∈ S, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : H ⊗[k] H | ∃ a ∈ S, ∃ b ∈ S, t = a ⊗ₜ[k] b})
    (hSant : ∀ x ∈ S, antipode k x ∈ S) :
    Module.finrank k H =
      Module.finrank k S *
        Module.finrank k (H ⧸ Ideal.span {x : H | x ∈ S ∧ Coalgebra.counit (R := k) x = 0}) := by
  haveI : IsLocalRing ↥S := isLocalRing_S hH S
  haveI : Module.FaithfullyFlat (↥S) H :=
    HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem S hΔ hSant
  haveI : Module.Finite (↥S) H := Module.Finite.of_restrictScalars_finite k (↥S) H
  haveI : Module.Free (↥S) H := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis (↥S) H
  haveI : Fintype (Module.Free.ChooseBasisIndex (↥S) H) := Fintype.ofFinite _
  rw [finrank_quotient_eq_card S b, ← Module.finrank_eq_card_basis b,
    Module.finrank_mul_finrank k (↥S) H]

end HopfAlgebra.OrderMultiplicativity

theorem solution
    (k : Type u) [Field k] (H : Type v) [CommRing H] [HopfAlgebra k H] [Module.Finite k H]
    (hH : ∀ x : H, Coalgebra.counit (R := k) x = 0 → IsNilpotent x)
    (S : Subalgebra k H)
    (hΔ : ∀ x ∈ S, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : TensorProduct k H H | ∃ a ∈ S, ∃ b ∈ S, t = a ⊗ₜ[k] b})
    (hS : ∀ x ∈ S, HopfAlgebra.antipode k x ∈ S) :
    Module.finrank k H =
      Module.finrank k S *
        Module.finrank k (H ⧸ Ideal.span {x : H | x ∈ S ∧ Coalgebra.counit (R := k) x = 0}) :=
  HopfAlgebra.OrderMultiplicativity.main hH S hΔ hS

end
end S_HopfAlgebra_finrank_eq_finrank_subalgebra_mul_finrank_quotient_of_isNilpotent
end P2MW
export P2MW.S_HopfAlgebra_finrank_eq_finrank_subalgebra_mul_finrank_quotient_of_isNilpotent (solution)
