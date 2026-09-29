-- Prove2me | solution 1 for HopfAlgebra.faithfullyFlat_hopfKer_of_forall_isLocalRing_faithfullyFlat_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/752f01d7-96c1-5a8a-a610-43b12757c8f0

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_hopfKer_baseChange_toSubmodule_eq_range_baseChange
import Theorems.Thm_Module_FaithfullyFlat_of_forall_isMaximal_exists_flat_algebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_faithfullyFlat_hopfKer_of_forall_isLocalRing_faithfullyFlat_baseChange

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped TensorProduct

namespace Subalgebra
p2m_export "Subalgebra" "inclusion toSubmodule algebraMap_apply val restrictScalars mk map toSubmodule_injective mem_toSubmodule baseChange coe_algebraMap algebra smul_def toAlgebra comap ext"
namespace BaseChangeRange
p2m_open "Subalgebra"

variable {R : Type} [CommRing R] {H : Type} [CommRing H] [Algebra R H]
  (B : Subalgebra R H) (R₁ : Type) [CommRing R₁] [Algebra R R₁]

noncomputable def bcMap : R₁ ⊗[R] B →ₐ[R₁] R₁ ⊗[R] H :=
  Algebra.TensorProduct.map (AlgHom.id R₁ R₁) B.val

theorem bcMap_tmul (r : R₁) (b : B) : bcMap B R₁ (r ⊗ₜ[R] b) = r ⊗ₜ[R] (b : H) := rfl

noncomputable abbrev bcRange : Subalgebra R₁ (R₁ ⊗[R] H) := (bcMap B R₁).range

theorem bcMap_eq_baseChange (t : R₁ ⊗[R] B) :
    bcMap B R₁ t = (B.val.toLinearMap.baseChange R₁) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul r b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem bcRange_toSubmodule :
    Subalgebra.toSubmodule (bcRange B R₁) = LinearMap.range (B.val.toLinearMap.baseChange R₁) := by
  ext x
  simp only [Subalgebra.mem_toSubmodule, AlgHom.mem_range, LinearMap.mem_range, bcMap_eq_baseChange]

theorem bcMap_injective [Module.Flat R R₁] : Function.Injective (bcMap B R₁) := by
  have h : Function.Injective (LinearMap.lTensor R₁ B.val.toLinearMap) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  have hfun : ⇑(bcMap B R₁) = ⇑(LinearMap.lTensor R₁ B.val.toLinearMap) := by
    funext t
    rw [bcMap_eq_baseChange, LinearMap.baseChange_eq_ltensor]
  rw [hfun]
  exact h

noncomputable def toRange : B →ₐ[R] bcRange B R₁ :=
  ((bcMap B R₁).rangeRestrict.restrictScalars R).comp
    (Algebra.TensorProduct.includeRight : B →ₐ[R] R₁ ⊗[R] B)

theorem coe_toRange (b : B) : ((toRange B R₁ b : bcRange B R₁) : R₁ ⊗[R] H) = (1 : R₁) ⊗ₜ[R] (b : H) := rfl

noncomputable scoped instance algebraRange : Algebra B (bcRange B R₁) := (toRange B R₁).toRingHom.toAlgebra

theorem algebraMap_range_apply (b : B) : algebraMap B (bcRange B R₁) b = toRange B R₁ b := rfl

theorem coe_algebraMap_range (b : B) :
    ((algebraMap B (bcRange B R₁) b : bcRange B R₁) : R₁ ⊗[R] H) = (1 : R₁) ⊗ₜ[R] (b : H) := rfl

scoped instance isScalarTower_range : IsScalarTower R B (bcRange B R₁) :=
  IsScalarTower.of_algebraMap_eq fun r => ((toRange B R₁).commutes r).symm

scoped instance smulCommClass_range : SMulCommClass B R₁ (bcRange B R₁) where
  smul_comm b r c := by
    simp only [Algebra.smul_def]
    exact mul_left_comm _ _ _

scoped instance smulCommClass_range' : SMulCommClass R₁ B (bcRange B R₁) where
  smul_comm r b c := (smul_comm b r c).symm

scoped instance smulCommClass_range_self : SMulCommClass B (bcRange B R₁) (bcRange B R₁) :=
  Algebra.to_smulCommClass

scoped instance isScalarTower_range_self : IsScalarTower B (bcRange B R₁) (bcRange B R₁) :=
  IsScalarTower.right

noncomputable scoped instance moduleRangeTensor : Module (bcRange B R₁) ((bcRange B R₁) ⊗[B] H) :=
  TensorProduct.leftModule

noncomputable scoped instance algebraTensor : Algebra R₁ ((bcRange B R₁) ⊗[B] H) :=
  Algebra.TensorProduct.leftAlgebra

noncomputable scoped instance (priority := high) smulRangeTensor :
    SMul (bcRange B R₁) ((bcRange B R₁) ⊗[B] H) :=
  TensorProduct.leftHasSMul

scoped instance isPushout [Module.Flat R R₁] : Algebra.IsPushout R R₁ B (bcRange B R₁) := by
  refine ⟨IsBaseChange.of_equiv (AlgEquiv.ofInjective (bcMap B R₁) (bcMap_injective B R₁)).toLinearEquiv
    fun b => ?_⟩
  apply Subtype.ext
  rw [AlgEquiv.toLinearEquiv_apply, AlgEquiv.ofInjective_apply]
  rfl

scoped instance flat [Module.Flat R R₁] : Module.Flat B (bcRange B R₁) :=
  haveI : Algebra.IsPushout R B R₁ (bcRange B R₁) := (isPushout B R₁).symm
  Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv R B R₁ (bcRange B R₁)).toLinearEquiv.symm

theorem rangeRestrict_tmul (r : R₁) (b : B) :
    (bcMap B R₁).rangeRestrict (r ⊗ₜ[R] b)
      = algebraMap R₁ (bcRange B R₁) r * algebraMap B (bcRange B R₁) b := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, coe_algebraMap_range,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rfl

section cancel

variable [Module.Flat R R₁]

noncomputable abbrev cancelAlg : (bcRange B R₁) ⊗[B] H ≃ₐ[R₁] R₁ ⊗[R] H :=
  Algebra.IsPushout.cancelBaseChangeAlg R R₁ B (bcRange B R₁) H

theorem cancelAlg_one_tmul (h : H) :
    cancelAlg B R₁ ((1 : bcRange B R₁) ⊗ₜ[B] h) = (1 : R₁) ⊗ₜ[R] h :=
  Algebra.IsPushout.cancelBaseChangeAlg_tmul R R₁ B (bcRange B R₁) H h

theorem cancelAlg_algebraMap_mul_tmul_one (r : R₁) (b : B) :
    cancelAlg B R₁ ((algebraMap R₁ (bcRange B R₁) r * algebraMap B (bcRange B R₁) b) ⊗ₜ[B] (1 : H))
      = r ⊗ₜ[R] (b : H) := by
  have h2 : (algebraMap R₁ (bcRange B R₁) r * algebraMap B (bcRange B R₁) b) ⊗ₜ[B] (1 : H)
      = (algebraMap R₁ ((bcRange B R₁) ⊗[B] H) r) * ((1 : bcRange B R₁) ⊗ₜ[B] (b : H)) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      Algebra.algebraMap_eq_smul_one b, mul_smul_comm, mul_one, TensorProduct.smul_tmul,
      Subalgebra.smul_def, smul_eq_mul, mul_one]
  rw [h2, map_mul, AlgEquiv.commutes, cancelAlg_one_tmul,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem cancelAlg_rangeRestrict_tmul_one (t : R₁ ⊗[R] B) :
    cancelAlg B R₁ ((bcMap B R₁).rangeRestrict t ⊗ₜ[B] (1 : H)) = bcMap B R₁ t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.zero_tmul]
  | tmul r b => rw [rangeRestrict_tmul, cancelAlg_algebraMap_mul_tmul_one, bcMap_tmul]
  | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]

theorem cancelAlg_tmul (c : bcRange B R₁) (h : H) :
    cancelAlg B R₁ (c ⊗ₜ[B] h) = (c : R₁ ⊗[R] H) * ((1 : R₁) ⊗ₜ[R] h) := by
  obtain ⟨t, ht⟩ := (AlgHom.mem_range _).1 c.2
  have hc : (bcMap B R₁).rangeRestrict t = c := Subtype.ext ht
  have hsplit : c ⊗ₜ[B] h = (c ⊗ₜ[B] (1 : H)) * ((1 : bcRange B R₁) ⊗ₜ[B] h) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hsplit, map_mul, cancelAlg_one_tmul, ← hc, cancelAlg_rangeRestrict_tmul_one, ht, hc]

theorem cancelAlg_smul (c : bcRange B R₁) (x : (bcRange B R₁) ⊗[B] H) :
    cancelAlg B R₁ (c • x) = c • cancelAlg B R₁ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul c' h =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, cancelAlg_tmul, cancelAlg_tmul, Subalgebra.coe_mul,
        Subalgebra.smul_def, smul_eq_mul, mul_assoc]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

noncomputable def cancelLinearEquiv : (bcRange B R₁) ⊗[B] H ≃ₗ[bcRange B R₁] R₁ ⊗[R] H :=
  AddEquiv.toLinearEquiv (cancelAlg B R₁).toAddEquiv (cancelAlg_smul B R₁)

theorem faithfullyFlat_tensor (hff : Module.FaithfullyFlat (bcRange B R₁) (R₁ ⊗[R] H)) :
    Module.FaithfullyFlat (bcRange B R₁) ((bcRange B R₁) ⊗[B] H) :=
  Module.FaithfullyFlat.of_linearEquiv _ _ (cancelLinearEquiv B R₁)

end cancel

theorem map_ne_top [Module.Flat R R₁] [IsLocalRing R₁] (p : Ideal R)
    [(IsLocalRing.maximalIdeal R₁).LiesOver p] (M : Ideal B) (hMp : M.comap (algebraMap R B) ≤ p) :
    M.map (algebraMap B (bcRange B R₁)) ≠ ⊤ := by
  set q : Ideal R := M.comap (algebraMap R B) with hq_def

  have hq : q.map (algebraMap R R₁) ≠ ⊤ := by
    intro htop
    have hle : q.map (algebraMap R R₁) ≤ IsLocalRing.maximalIdeal R₁ := by
      rw [Ideal.map_le_iff_le_comap]
      have hover : p = (IsLocalRing.maximalIdeal R₁).comap (algebraMap R R₁) :=
        Ideal.LiesOver.over
      exact hMp.trans hover.le
    exact (IsLocalRing.maximalIdeal.isMaximal R₁).ne_top (top_le_iff.1 (htop ▸ hle))
  haveI : Nontrivial (R₁ ⧸ q.map (algebraMap R R₁)) := Ideal.Quotient.nontrivial_iff.2 hq
  haveI : Nontrivial (R₁ ⊗[R] (R ⧸ q)) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot R₁ q).toEquiv.symm.nontrivial

  let ι : (R ⧸ q) →ₗ[R] (B ⧸ M) :=
    (Ideal.quotientMapₐ M (Algebra.ofId R B) (fun x hx => hx)).toLinearMap
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : Ideal.Quotient.mk M (algebraMap R B r) = 0 := hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx' ⊢
    exact hx'
  haveI : Nontrivial (R₁ ⊗[R] (B ⧸ M)) :=
    (Module.Flat.lTensor_preserves_injective_linearMap (M := R₁) ι hι).nontrivial
  haveI : Nontrivial ((bcRange B R₁) ⊗[B] (B ⧸ M)) :=
    (Algebra.IsPushout.cancelBaseChange R R₁ B (bcRange B R₁) (B ⧸ M)).toEquiv.nontrivial
  haveI : Nontrivial ((bcRange B R₁) ⧸ M.map (algebraMap B (bcRange B R₁))) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (bcRange B R₁) M).toEquiv.nontrivial
  exact Ideal.Quotient.nontrivial_iff.1 inferInstance

theorem exists_flat_algebra [Module.Flat R R₁] [IsLocalRing R₁] (p : Ideal R)
    [(IsLocalRing.maximalIdeal R₁).LiesOver p] (M : Ideal B) (hMp : M.comap (algebraMap R B) ≤ p)
    (hff : Module.FaithfullyFlat (bcRange B R₁) (R₁ ⊗[R] H)) :
    ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C) (_ : Module.Flat B C),
      M.map (algebraMap B C) ≠ ⊤ ∧ Module.FaithfullyFlat C (C ⊗[B] H) :=
  ⟨bcRange B R₁, inferInstance, inferInstance, inferInstance, map_ne_top B R₁ p M hMp,
    faithfullyFlat_tensor B R₁ hff⟩

private theorem _root_.Module.FaithfullyFlat.of_subalgebra_eq {S : Type} [CommRing S] {X : Type} [CommRing X] [Algebra S X]
    {C C' : Subalgebra S X} (h : C = C') (hC : Module.FaithfullyFlat C X) : Module.FaithfullyFlat C' X := by
  subst h; exact hC

p2m_alias "P2MW.S_HopfAlgebra_faithfullyFlat_hopfKer_of_forall_isLocalRing_faithfullyFlat_baseChange.Module.FaithfullyFlat.of_subalgebra_eq" "Module.FaithfullyFlat.of_subalgebra_eq"
end Subalgebra.BaseChangeRange
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_hopfKer_of_forall_isLocalRing_faithfullyFlat_baseChange.Subalgebra P2MW.S_HopfAlgebra_faithfullyFlat_hopfKer_of_forall_isLocalRing_faithfullyFlat_baseChange.Subalgebra.BaseChangeRange"
p2m_reactivate "P2MW.S_HopfAlgebra_faithfullyFlat_hopfKer_of_forall_isLocalRing_faithfullyFlat_baseChange.Subalgebra"

namespace HopfAlgebra p2m_export "HopfAlgebra" "mk hopfKer hopfKer_baseChange_toSubmodule_eq_range_baseChange" end HopfAlgebra
p2m_open_scoped "HopfAlgebra" in

theorem HopfAlgebra.faithfullyFlat_hopfKer_of_forall_isLocalRing_faithfullyFlat_baseChange
    (R : Type) [CommRing R]
    (H : Type) [CommRing H] [HopfAlgebra R H]
    (H' : Type) [CommRing H'] [HopfAlgebra R H']
    (qc : H →ₐc[R] H')
    (hloc : ∀ (p : Ideal R), p.IsMaximal →
      ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (_ : Module.Flat R R₁) (_ : IsLocalRing R₁),
        (IsLocalRing.maximalIdeal R₁).LiesOver p ∧
        Module.FaithfullyFlat
          ↥(HopfAlgebra.hopfKer (Bialgebra.TensorProduct.map (BialgHom.id R₁ R₁) qc :
              TensorProduct R R₁ H →ₐc[R₁] TensorProduct R R₁ H'))
          (TensorProduct R R₁ H)) :
    Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) H := by
  apply Module.FaithfullyFlat.of_forall_isMaximal_exists_flat_algebra
  intro M hM
  obtain ⟨p, hp, hqp⟩ := Ideal.exists_le_maximal (M.comap (algebraMap R ↥(HopfAlgebra.hopfKer qc)))
    (Ideal.comap_ne_top _ hM.ne_top)
  obtain ⟨R₁, _, _, _, _, hlies, hff⟩ := hloc p hp
  have hC : HopfAlgebra.hopfKer (Bialgebra.TensorProduct.map (BialgHom.id R₁ R₁) qc :
      TensorProduct R R₁ H →ₐc[R₁] TensorProduct R R₁ H')
        = Subalgebra.BaseChangeRange.bcRange (HopfAlgebra.hopfKer qc) R₁ :=
    Subalgebra.toSubmodule_injective
      ((HopfAlgebra.hopfKer_baseChange_toSubmodule_eq_range_baseChange R₁ qc).trans
        (Subalgebra.BaseChangeRange.bcRange_toSubmodule (HopfAlgebra.hopfKer qc) R₁).symm)
  exact Subalgebra.BaseChangeRange.exists_flat_algebra (HopfAlgebra.hopfKer qc) R₁ p M hqp
    (Module.FaithfullyFlat.of_subalgebra_eq hC hff)

theorem solution
    (R : Type) [CommRing R]
    (H : Type) [CommRing H] [HopfAlgebra R H]
    (H' : Type) [CommRing H'] [HopfAlgebra R H']
    (qc : H →ₐc[R] H')
    (hloc : ∀ (p : Ideal R), p.IsMaximal →
      ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (_ : Module.Flat R R₁) (_ : IsLocalRing R₁),
        (IsLocalRing.maximalIdeal R₁).LiesOver p ∧
        Module.FaithfullyFlat
          ↥(HopfAlgebra.hopfKer (Bialgebra.TensorProduct.map (BialgHom.id R₁ R₁) qc :
              TensorProduct R R₁ H →ₐc[R₁] TensorProduct R R₁ H'))
          (TensorProduct R R₁ H)) :
    Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) H :=
  HopfAlgebra.faithfullyFlat_hopfKer_of_forall_isLocalRing_faithfullyFlat_baseChange R H H' qc hloc

end S_HopfAlgebra_faithfullyFlat_hopfKer_of_forall_isLocalRing_faithfullyFlat_baseChange
end P2MW
export P2MW.S_HopfAlgebra_faithfullyFlat_hopfKer_of_forall_isLocalRing_faithfullyFlat_baseChange (solution)
