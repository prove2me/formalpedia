-- Prove2me | solution 1 for HopfAlgebra.exists_bialgHom_surjective_points_eq_of_submonoid_of_bijective_evalPoints_of_perfectField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/6e1e20a2-f3a3-5266-a540-3916ae34a0e7

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_HopfAlgebra_CharacterClosure
import Theorems.Thm_HopfAlgebra_lift_liftPoint_bijective_of_forall_exists_comp_eq
import Theorems.Thm_HopfAlgebra_map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet
import Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal
import Theorems.Thm_HopfAlgebra_toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique
import Theorems.Thm_HopfAlgebra_exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed
import Theorems.Thm_Algebra_TensorProduct_eq_zero_of_forall_lift_apply_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_bialgHom_surjective_points_eq_of_submonoid_of_bijective_evalPoints_of_perfectField

set_option autoImplicit false
open scoped TensorProduct

universe u v w

namespace HopfAlgebra p2m_export "HopfAlgebra" "mk antipode_one mul_antipode_lTensor_comul_apply antipode_mul mul_antipode_rTensor_comul_apply hopfKer vanishingIdealOfPoints liftPoint evalPair evalPair_tmul ptSet mem_ptSet_iff ofConv_mem_ptSet pointQuot evalQuot evalQuot_tmul lift_liftPoint_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed" namespace C5 end HopfAlgebra.C5
p2m_open_scoped "HopfAlgebra" in
theorem HopfAlgebra.C5.P2c
    {R : Type*} [CommRing R] {A : Type*} [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
    {B : Type*} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π)
    [Module.Flat R A] [Module.Flat R ↥(HopfAlgebra.hopfKer π)]
    (L : Type*) [CommRing L] [Algebra R L] :
    ∀ ν ν' : WithConv (A →ₐ[R] L),
        (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val
            = (WithConv.ofConv ν').comp (HopfAlgebra.hopfKer π).val
          ↔ ∃! χ : B →ₐ[R] L, ν' = ν * WithConv.toConv (χ.comp (π : A →ₐ[R] B)) :=
  (HopfAlgebra.toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique π hπ L).2.2

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one mul_antipode_lTensor_comul_apply antipode_mul mul_antipode_rTensor_comul_apply hopfKer vanishingIdealOfPoints liftPoint evalPair evalPair_tmul ptSet mem_ptSet_iff ofConv_mem_ptSet pointQuot evalQuot evalQuot_tmul lift_liftPoint_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed"
namespace C5
p2m_open "HopfAlgebra"

noncomputable def antipodeAlgHom' (K : Type*) [CommRing K] (A : Type*) [CommRing A] [HopfAlgebra K A] :
    A →ₐ[K] A :=
  AlgHom.ofLinearMap (HopfAlgebraStruct.antipode (R := K))
    (HopfAlgebra.antipode_one (R := K) (A := A))
    (fun a b => by rw [HopfAlgebra.antipode_mul, mul_comm])

theorem antipodeAlgHom'_apply {K : Type*} [CommRing K] {A : Type*} [CommRing A] [HopfAlgebra K A]
    (a : A) : antipodeAlgHom' K A a = HopfAlgebraStruct.antipode (R := K) a := rfl

theorem exists_inv_point
    {K : Type*} [CommRing K] {A : Type*} [CommRing A] [HopfAlgebra K A]
    {L : Type*} [CommRing L] [Algebra K L] (ν : A →ₐ[K] L) :
    ∃ ν' : A →ₐ[K] L, ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := K) ∧
      WithConv.toConv ν' * WithConv.toConv ν = 1 ∧ WithConv.toConv ν * WithConv.toConv ν' = 1 := by
  refine ⟨ν.comp (antipodeAlgHom' K A), ?_, ?_, ?_⟩
  · ext a; rfl
  · apply WithConv.ext
    apply AlgHom.ext
    intro a
    change (WithConv.toConv (ν.comp (antipodeAlgHom' K A)) * WithConv.toConv ν).ofConv a =
      (1 : WithConv (A →ₐ[K] L)).ofConv a
    rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
    have key : (Algebra.TensorProduct.lift (ν.comp (antipodeAlgHom' K A)) ν
        (fun _ _ => Commute.all _ _)).toLinearMap =
        ν.toLinearMap ∘ₗ LinearMap.mul' K A ∘ₗ (HopfAlgebraStruct.antipode (R := K)).rTensor A := by
      apply TensorProduct.ext'
      intro x y
      simp [Algebra.TensorProduct.lift_tmul, LinearMap.rTensor_tmul, antipodeAlgHom'_apply]
    have h := LinearMap.congr_fun key (Coalgebra.comul (R := K) a)
    simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply] at h
    change Algebra.TensorProduct.lift (ν.comp (antipodeAlgHom' K A)) ν _ (Coalgebra.comul (R := K) a) = _
    rw [h, HopfAlgebra.mul_antipode_rTensor_comul_apply, AlgHom.commutes]
  · apply WithConv.ext
    apply AlgHom.ext
    intro a
    change (WithConv.toConv ν * WithConv.toConv (ν.comp (antipodeAlgHom' K A))).ofConv a =
      (1 : WithConv (A →ₐ[K] L)).ofConv a
    rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
    have key : (Algebra.TensorProduct.lift ν (ν.comp (antipodeAlgHom' K A))
        (fun _ _ => Commute.all _ _)).toLinearMap =
        ν.toLinearMap ∘ₗ LinearMap.mul' K A ∘ₗ (HopfAlgebraStruct.antipode (R := K)).lTensor A := by
      apply TensorProduct.ext'
      intro x y
      simp [Algebra.TensorProduct.lift_tmul, LinearMap.lTensor_tmul, antipodeAlgHom'_apply]
    have h := LinearMap.congr_fun key (Coalgebra.comul (R := K) a)
    simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply] at h
    change Algebra.TensorProduct.lift ν (ν.comp (antipodeAlgHom' K A)) _ (Coalgebra.comul (R := K) a) = _
    rw [h, HopfAlgebra.mul_antipode_lTensor_comul_apply, AlgHom.commutes]

theorem mul_right_injective_point
    {K : Type*} [CommRing K] {A : Type*} [CommRing A] [HopfAlgebra K A]
    {L : Type*} [CommRing L] [Algebra K L] (ν : WithConv (A →ₐ[K] L)) :
    Function.Injective (fun μ : WithConv (A →ₐ[K] L) => ν * μ) := by
  intro μ₁ μ₂ h
  obtain ⟨ν', -, hl, -⟩ := exists_inv_point (K := K) ν.ofConv
  have hl' : WithConv.toConv ν' * ν = 1 := by simpa using hl
  simp only at h
  calc μ₁ = (WithConv.toConv ν' * ν) * μ₁ := by rw [hl', one_mul]
    _ = WithConv.toConv ν' * (ν * μ₁) := by rw [mul_assoc]
    _ = WithConv.toConv ν' * (ν * μ₂) := by rw [h]
    _ = (WithConv.toConv ν' * ν) * μ₂ := by rw [mul_assoc]
    _ = μ₂ := by rw [hl', one_mul]

theorem exists_mem_toLinearMap_eq_comp_antipode_of_finite
    {K : Type*} [CommRing K] {A : Type*} [CommRing A] [HopfAlgebra K A]
    {L : Type*} [CommRing L] [Algebra K L]
    (W : Submonoid (WithConv (A →ₐ[K] L))) [Finite ↥W]
    (ν : A →ₐ[K] L) (hν : WithConv.toConv ν ∈ W) :
    ∃ ν' : A →ₐ[K] L, WithConv.toConv ν' ∈ W ∧
      ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := K) := by
  obtain ⟨ν', hlin, hl, hr⟩ := exists_inv_point (K := K) ν
  refine ⟨ν', ?_, hlin⟩
  set x : WithConv (A →ₐ[K] L) := WithConv.toConv ν with hx

  have hpow : ∀ n : ℕ, x ^ n ∈ W := fun n => pow_mem hν n
  let f : ℕ → ↥W := fun n => ⟨x ^ n, hpow n⟩
  have hnotinj : ¬ Function.Injective f := not_injective_infinite_finite f
  obtain ⟨n, m, hne, hfeq⟩ : ∃ n m : ℕ, n ≠ m ∧ f n = f m := by
    by_contra h
    push Not at h
    exact hnotinj (fun a b hab => by_contra (fun hne => h a b hne hab))
  have hxeq : x ^ n = x ^ m := by
    have := congrArg Subtype.val hfeq; simpa [f] using this

  have key : ∀ n m : ℕ, n < m → x ^ n = x ^ m → WithConv.toConv ν' ∈ W := by
    intro n m hnm hnmeq
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hnm

    have h1 : x ^ n * x ^ (d + 1) = x ^ n * 1 := by
      rw [mul_one, ← pow_add]; exact hnmeq.symm
    have h2 : x ^ (d + 1) = 1 := mul_right_injective_point (K := K) (x ^ n) h1

    have h3 : WithConv.toConv ν' = x ^ d := by
      calc WithConv.toConv ν' = WithConv.toConv ν' * (x * x ^ d) := by
              rw [← pow_succ', h2, mul_one]
        _ = (WithConv.toConv ν' * x) * x ^ d := by rw [mul_assoc]
        _ = x ^ d := by rw [hx, hl, one_mul]
    rw [h3]; exact hpow d
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact key n m hlt hxeq
  · exact key m n hgt hxeq.symm

end HopfAlgebra.C5

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one mul_antipode_lTensor_comul_apply antipode_mul mul_antipode_rTensor_comul_apply hopfKer vanishingIdealOfPoints liftPoint evalPair evalPair_tmul ptSet mem_ptSet_iff ofConv_mem_ptSet pointQuot evalQuot evalQuot_tmul lift_liftPoint_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed"
namespace C5
p2m_open "HopfAlgebra"

theorem exists_eq_apply_of_algHom_pi {L : Type*} [Field L] {ι : Type*} [Finite ι]
    (ψ : (ι → L) →ₐ[L] L) : ∃ i : ι, ∀ f : ι → L, ψ f = f i := by
  classical
  haveI := Fintype.ofFinite ι

  have hidem : ∀ i : ι, ψ (Pi.single i 1) = 0 ∨ ψ (Pi.single i 1) = 1 := by
    intro i
    have h2 : ψ (Pi.single i 1) * ψ (Pi.single i 1) = ψ (Pi.single i 1) := by
      rw [← map_mul]; congr 1; ext j; by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rcases mul_eq_zero.mp (show ψ (Pi.single i 1) * (ψ (Pi.single i 1) - 1) = 0 by
      rw [mul_sub, mul_one, h2, sub_self]) with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hsum : ∑ i, ψ (Pi.single i 1) = 1 := by
    rw [← map_sum]
    have : (∑ i : ι, (Pi.single i (1 : L) : ι → L)) = 1 := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [this, map_one]

  obtain ⟨i, hi⟩ : ∃ i, ψ (Pi.single i 1) = 1 := by
    by_contra h
    push Not at h
    have : ∑ i, ψ (Pi.single i 1) = 0 :=
      Finset.sum_eq_zero fun i _ => (hidem i).resolve_right (h i)
    rw [this] at hsum
    exact zero_ne_one hsum
  refine ⟨i, fun f => ?_⟩

  have hzero : ∀ j, j ≠ i → ψ (Pi.single j 1) = 0 := by
    intro j hj
    have hprod : (Pi.single j (1 : L) : ι → L) * Pi.single i 1 = 0 := by
      ext k; by_cases hk : k = i
      · subst hk; simp [hj]
      · simp [hk]
    have := congrArg ψ hprod
    rw [map_mul, hi, mul_one, map_zero] at this
    exact this

  have hf : f = ∑ j, f j • (Pi.single j (1 : L) : ι → L) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hf]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [hzero j hj, mul_zero]) (fun h => absurd (Finset.mem_univ i) h),
    hi, mul_one]

theorem toConv_mem_of_forall_mem_vanishingIdeal_eq_zero
    {K : Type*} [Field K] {A : Type*} [CommRing A] [Bialgebra K A] [Module.Finite K A]
    {L : Type*} [Field L] [Algebra K L]
    (W : Submonoid (WithConv (A →ₐ[K] L))) [Finite ↥W]
    (hbij : Function.Bijective (HopfAlgebra.evalQuot W))
    (ν : A →ₐ[K] L) (hν : ∀ a ∈ HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet W), ν a = 0) :
    WithConv.toConv ν ∈ W := by
  classical

  let νbar : HopfAlgebra.pointQuot W →ₐ[K] L :=
    Ideal.Quotient.liftₐ (HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet W)) ν hν
  have hνbar : ∀ a : A, νbar (Ideal.Quotient.mk _ a) = ν a := fun a => rfl

  let νL : L ⊗[K] HopfAlgebra.pointQuot W →ₐ[L] L :=
    Algebra.TensorProduct.lift (Algebra.ofId L L) νbar (fun _ _ => Commute.all _ _)
  let e : (L ⊗[K] HopfAlgebra.pointQuot W) ≃ₐ[L] (↥W → L) :=
    AlgEquiv.ofBijective (HopfAlgebra.evalQuot W) hbij
  let ψ : (↥W → L) →ₐ[L] L := νL.comp (e.symm : (↥W → L) →ₐ[L] L ⊗[K] HopfAlgebra.pointQuot W)
  obtain ⟨w, hw⟩ := exists_eq_apply_of_algHom_pi ψ

  have hval : ∀ a : A, ν a = (WithConv.ofConv w.1) a := by
    intro a
    have h1 : ψ (e ((1 : L) ⊗ₜ[K] Ideal.Quotient.mk _ a)) = νL ((1 : L) ⊗ₜ[K] Ideal.Quotient.mk _ a) := by
      show νL (e.symm (e _)) = _
      rw [AlgEquiv.symm_apply_apply]
    have h2 : νL ((1 : L) ⊗ₜ[K] Ideal.Quotient.mk _ a) = ν a := by
      simp only [νL, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      exact hνbar a
    have h3 : e ((1 : L) ⊗ₜ[K] Ideal.Quotient.mk _ a) = fun s : ↥W => (WithConv.ofConv s.1) a := by
      ext s
      show HopfAlgebra.evalQuot W ((1 : L) ⊗ₜ[K] Ideal.Quotient.mk _ a) s = _
      rw [HopfAlgebra.evalQuot_tmul, one_mul]
    rw [← h2, ← h1, h3, hw]
  have hνeq : ν = WithConv.ofConv w.1 := AlgHom.ext hval
  rw [hνeq]
  exact w.2

end HopfAlgebra.C5

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one mul_antipode_lTensor_comul_apply antipode_mul mul_antipode_rTensor_comul_apply hopfKer vanishingIdealOfPoints liftPoint evalPair evalPair_tmul ptSet mem_ptSet_iff ofConv_mem_ptSet pointQuot evalQuot evalQuot_tmul lift_liftPoint_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed"
namespace C5
p2m_open "HopfAlgebra"

theorem finrank_pointQuot_eq_natCard
    {K : Type*} [Field K] {A : Type*} [CommRing A] [Bialgebra K A] [Module.Finite K A]
    {L : Type*} [Field L] [Algebra K L]
    (W : Submonoid (WithConv (A →ₐ[K] L))) [Finite ↥W]
    (hbij : Function.Bijective (HopfAlgebra.evalQuot W)) :
    Module.finrank K (HopfAlgebra.pointQuot W) = Nat.card ↥W := by
  classical
  haveI : Fintype ↥W := Fintype.ofFinite _

  let e : L ⊗[K] HopfAlgebra.pointQuot W ≃ₗ[L] (↥W → L) :=
    LinearEquiv.ofBijective (HopfAlgebra.evalQuot W).toLinearMap hbij
  have h1 : Module.finrank L (L ⊗[K] HopfAlgebra.pointQuot W) = Module.finrank K (HopfAlgebra.pointQuot W) :=
    Module.finrank_baseChange
  rw [← h1, e.finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end HopfAlgebra.C5

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one mul_antipode_lTensor_comul_apply antipode_mul mul_antipode_rTensor_comul_apply hopfKer vanishingIdealOfPoints liftPoint evalPair evalPair_tmul ptSet mem_ptSet_iff ofConv_mem_ptSet pointQuot evalQuot evalQuot_tmul lift_liftPoint_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed"
namespace C5
p2m_open "HopfAlgebra"

theorem natCard_algHom_le_finrank_aux
    {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
    {S : Type*} [CommRing S] [Algebra K S] [Module.Finite K S] [Finite (S →ₐ[K] L)] :
    Nat.card (S →ₐ[K] L) ≤ Module.finrank K S := by
  classical
  haveI : Fintype (S →ₐ[K] L) := Fintype.ofFinite _
  have hli : LinearIndependent L (fun χ : S →ₐ[K] L => (χ : S →ₗ[K] L)) := by
    apply LinearIndependent.of_comp (LinearMap.ltoFun K S L L)
    have h := linearIndependent_monoidHom S L
    have hinj : Function.Injective (fun χ : S →ₐ[K] L => (χ : S →* L)) := fun a b hab =>
      AlgHom.ext (fun x => DFunLike.congr_fun hab x)
    have h2 := h.comp _ hinj
    convert h2 using 1
    rfl
    rfl
  let b := Module.Free.chooseBasis K S
  have e : (S →ₗ[K] L) ≃ₗ[L] (Module.Free.ChooseBasisIndex K S → L) := (b.constr L).symm
  have hdim : Module.finrank L (S →ₗ[K] L) = Module.finrank K S := by
    rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_chooseBasisIndex]
  haveI : Module.Finite L (S →ₗ[K] L) := Module.Finite.of_injective e.toLinearMap e.injective
  rw [Nat.card_eq_fintype_card, ← hdim]
  exact hli.fintype_card_le_finrank

theorem finrank_eq_natCard_algHom_of_forall_exists_comp_val_eq
    {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
    {A : Type*} [CommRing A] [Algebra K A] [Module.Finite K A]
    [Finite (WithConv (A →ₐ[K] L))]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId L (WithConv (A →ₐ[K] L) → L))
        (Pi.algHom K _ fun ν : WithConv (A →ₐ[K] L) => (WithConv.ofConv ν : A →ₐ[K] L))
        (fun _ _ => Commute.all _ _) :
        L ⊗[K] A →ₐ[L] (WithConv (A →ₐ[K] L) → L)))
    (S : Subalgebra K A)
    (hext : ∀ h : ↥S →ₐ[K] L, ∃ ν : A →ₐ[K] L, ν.comp S.val = h) :
    Finite (↥S →ₐ[K] L) ∧ Module.finrank K ↥S = Nat.card (↥S →ₐ[K] L) := by
  classical
  haveI : Finite (A →ₐ[K] L) :=
    Finite.of_injective (fun ν : A →ₐ[K] L => (WithConv.toConv ν : WithConv (A →ₐ[K] L)))
      (fun a b h => by simpa using congrArg WithConv.ofConv h)
  let res : (A →ₐ[K] L) → (↥S →ₐ[K] L) := fun ν => ν.comp S.val
  have hres : Function.Surjective res := fun h => hext h
  haveI hfinS : Finite (↥S →ₐ[K] L) := Finite.of_surjective res hres
  refine ⟨hfinS, le_antisymm ?_ natCard_algHom_le_finrank_aux⟩
  haveI : Fintype (↥S →ₐ[K] L) := Fintype.ofFinite _
  let evS : L ⊗[K] ↥S →ₐ[L] ((↥S →ₐ[K] L) → L) :=
    Algebra.TensorProduct.lift (Algebra.ofId L ((↥S →ₐ[K] L) → L))
      (Pi.algHom K _ fun χ : ↥S →ₐ[K] L => χ) (fun _ _ => Commute.all _ _)
  let pull : ((↥S →ₐ[K] L) → L) →ₗ[L] (WithConv (A →ₐ[K] L) → L) :=
    { toFun := fun φ ν => φ (res (WithConv.ofConv ν))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let hevMap := (Algebra.TensorProduct.lift
        (Algebra.ofId L (WithConv (A →ₐ[K] L) → L))
        (Pi.algHom K _ fun ν : WithConv (A →ₐ[K] L) => (WithConv.ofConv ν : A →ₐ[K] L))
        (fun _ _ => Commute.all _ _) : L ⊗[K] A →ₐ[L] (WithConv (A →ₐ[K] L) → L))
  let incl : L ⊗[K] ↥S →ₗ[L] L ⊗[K] A := LinearMap.baseChange L S.val.toLinearMap
  have hsq : pull ∘ₗ evS.toLinearMap = hevMap.toLinearMap ∘ₗ incl := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c s
    funext ν
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, LinearMap.coe_mk,
      AddHom.coe_mk, incl, LinearMap.baseChange_tmul, evS, hevMap, pull,
      Algebra.TensorProduct.lift_tmul, Pi.mul_apply, Pi.algHom_apply]
    rfl
  have hincl : Function.Injective incl :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := L) S.val.toLinearMap Subtype.val_injective
  have hevS : Function.Injective evS.toLinearMap := by
    have hcomp : Function.Injective (hevMap.toLinearMap ∘ₗ incl) := hev.1.comp hincl
    rw [← hsq, LinearMap.coe_comp] at hcomp
    exact Function.Injective.of_comp hcomp
  have h1 : Module.finrank K ↥S = Module.finrank L (L ⊗[K] ↥S) := Module.finrank_baseChange.symm
  rw [h1, Nat.card_eq_fintype_card, ← Module.finrank_fintype_fun_eq_card L]
  exact LinearMap.finrank_le_finrank_of_injective hevS

end HopfAlgebra.C5

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one mul_antipode_lTensor_comul_apply antipode_mul mul_antipode_rTensor_comul_apply hopfKer vanishingIdealOfPoints liftPoint evalPair evalPair_tmul ptSet mem_ptSet_iff ofConv_mem_ptSet pointQuot evalQuot evalQuot_tmul lift_liftPoint_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed"
namespace C5
p2m_open "HopfAlgebra"

theorem evalQuot_bijective_of_bijective_lift_liftPoint_image
    {K : Type*} [Field K] {A : Type*} [CommRing A] [Bialgebra K A]
    {L : Type*} [Field L] [Algebra K L]
    (W : Submonoid (WithConv (A →ₐ[K] L)))
    (h : Function.Bijective (Algebra.TensorProduct.lift (Algebra.ofId L (↥(W : Set (WithConv (A →ₐ[K] L))) → L))
      (Pi.algHom K _ fun s : ↥(W : Set (WithConv (A →ₐ[K] L))) =>
        HopfAlgebra.liftPoint (WithConv.ofConv '' (W : Set (WithConv (A →ₐ[K] L)))) (WithConv.ofConv s.1)
          (Set.mem_image_of_mem WithConv.ofConv s.2))
      (fun _ _ => Commute.all _ _) :
      L ⊗[K] (A ⧸ HopfAlgebra.vanishingIdealOfPoints (WithConv.ofConv '' (W : Set (WithConv (A →ₐ[K] L))))) →ₐ[L]
        (↥(W : Set (WithConv (A →ₐ[K] L))) → L))) :
    Function.Bijective (HopfAlgebra.evalQuot W) := by
  have hS : WithConv.ofConv '' (W : Set (WithConv (A →ₐ[K] L))) = HopfAlgebra.ptSet W := by
    ext ν
    simp only [Set.mem_image, SetLike.mem_coe, HopfAlgebra.mem_ptSet_iff]
    constructor
    · rintro ⟨s, hs, rfl⟩; simpa using hs
    · intro hν; exact ⟨WithConv.toConv ν, hν, rfl⟩

  suffices key : ∀ (S : Set (A →ₐ[K] L))
      (hmem : ∀ s : ↥(W : Set (WithConv (A →ₐ[K] L))), WithConv.ofConv s.1 ∈ S),
      S = HopfAlgebra.ptSet W →
      Function.Bijective (Algebra.TensorProduct.lift (Algebra.ofId L (↥(W : Set (WithConv (A →ₐ[K] L))) → L))
        (Pi.algHom K _ fun s : ↥(W : Set (WithConv (A →ₐ[K] L))) =>
          HopfAlgebra.liftPoint S (WithConv.ofConv s.1) (hmem s))
        (fun _ _ => Commute.all _ _) :
        L ⊗[K] (A ⧸ HopfAlgebra.vanishingIdealOfPoints S) →ₐ[L] (↥(W : Set (WithConv (A →ₐ[K] L))) → L)) →
      Function.Bijective (HopfAlgebra.evalQuot W) from
    key _ (fun s => Set.mem_image_of_mem WithConv.ofConv s.2) hS h
  intro S hmem hS' hb
  subst hS'
  exact hb

end HopfAlgebra.C5

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one mul_antipode_lTensor_comul_apply antipode_mul mul_antipode_rTensor_comul_apply hopfKer vanishingIdealOfPoints liftPoint evalPair evalPair_tmul ptSet mem_ptSet_iff ofConv_mem_ptSet pointQuot evalQuot evalQuot_tmul lift_liftPoint_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed"
namespace C5
p2m_open "HopfAlgebra"

theorem natCard_eq_natCard_mul_natCard_of_fibre
    {M : Type*} [CommMonoid M] [Finite M] {X : Type*}
    (res : M → X) (hsurj : Function.Surjective res)
    (W : Submonoid M)
    (hfib : ∀ ν ν' : M, res ν = res ν' ↔ ∃ w ∈ W, ν' = ν * w)
    (hinj : ∀ ν : M, Function.Injective (fun μ : M => ν * μ)) :
    Nat.card M = Nat.card ↥W * Nat.card X := by
  classical

  choose s hs using hsurj

  let φ : X × ↥W → M := fun p => s p.1 * (p.2 : M)
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨x, w⟩ ⟨x', w'⟩ hxw
      simp only [φ] at hxw
      have hx : x = x' := by
        have h1 : res (s x) = res (s x * (w : M)) := (hfib (s x) (s x * w)).mpr ⟨w, w.2, rfl⟩
        have h2 : res (s x') = res (s x' * (w' : M)) := (hfib (s x') (s x' * w')).mpr ⟨w', w'.2, rfl⟩
        rw [hs x, hxw] at h1
        rw [hs x'] at h2
        exact h1.trans h2.symm
      subst hx
      have hw : (w : M) = w' := hinj (s x) hxw
      exact Prod.ext rfl (Subtype.ext hw)
    · intro m
      obtain ⟨w, hw, hm⟩ := (hfib (s (res m)) m).mp (hs (res m))
      exact ⟨(res m, ⟨w, hw⟩), hm.symm⟩
  have hcard := Nat.card_eq_of_bijective φ hφ
  rw [Nat.card_prod] at hcard
  rw [← hcard, mul_comm]

end HopfAlgebra.C5

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one mul_antipode_lTensor_comul_apply antipode_mul mul_antipode_rTensor_comul_apply hopfKer vanishingIdealOfPoints liftPoint evalPair evalPair_tmul ptSet mem_ptSet_iff ofConv_mem_ptSet pointQuot evalQuot evalQuot_tmul lift_liftPoint_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed"
namespace C5
p2m_open "HopfAlgebra"

theorem finrank_eq_natCard_of_bijective_eval
    {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
    {A : Type*} [CommRing A] [Algebra K A] [Module.Finite K A]
    [Finite (WithConv (A →ₐ[K] L))]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId L (WithConv (A →ₐ[K] L) → L))
        (Pi.algHom K _ fun ν : WithConv (A →ₐ[K] L) => (WithConv.ofConv ν : A →ₐ[K] L))
        (fun _ _ => Commute.all _ _) :
        L ⊗[K] A →ₐ[L] (WithConv (A →ₐ[K] L) → L))) :
    Module.finrank K A = Nat.card (WithConv (A →ₐ[K] L)) := by
  classical
  haveI : Fintype (WithConv (A →ₐ[K] L)) := Fintype.ofFinite _
  let e : L ⊗[K] A ≃ₗ[L] (WithConv (A →ₐ[K] L) → L) :=
    LinearEquiv.ofBijective (Algebra.TensorProduct.lift
        (Algebra.ofId L (WithConv (A →ₐ[K] L) → L))
        (Pi.algHom K _ fun ν : WithConv (A →ₐ[K] L) => (WithConv.ofConv ν : A →ₐ[K] L))
        (fun _ _ => Commute.all _ _) : L ⊗[K] A →ₐ[L] (WithConv (A →ₐ[K] L) → L)).toLinearMap hev
  have h1 : Module.finrank L (L ⊗[K] A) = Module.finrank K A := Module.finrank_baseChange
  rw [← h1, e.finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end HopfAlgebra.C5

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one mul_antipode_lTensor_comul_apply antipode_mul mul_antipode_rTensor_comul_apply hopfKer vanishingIdealOfPoints liftPoint evalPair evalPair_tmul ptSet mem_ptSet_iff ofConv_mem_ptSet pointQuot evalQuot evalQuot_tmul lift_liftPoint_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed"
namespace C5
p2m_open "HopfAlgebra"

set_option maxHeartbeats 3200000 in
theorem main
    (K : Type u) [Field K] [PerfectField K]
    (A : Type v) [CommRing A] [HopfAlgebra K A] [Module.Finite K A] [Coalgebra.IsCocomm K A]
    [Finite (WithConv (A →ₐ[K] AlgebraicClosure K))]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure K) (WithConv (A →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
        (Pi.algHom K _
          fun ν : WithConv (A →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : A →ₐ[K] AlgebraicClosure K))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure K ⊗[K] A →ₐ[AlgebraicClosure K]
          (WithConv (A →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)))
    (W : Submonoid (WithConv (A →ₐ[K] AlgebraicClosure K)))
    (hW : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ ν ∈ W,
      ∀ ν' : WithConv (A →ₐ[K] AlgebraicClosure K),
        (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) → ν' ∈ W) :
    ∃ (Ā : Type v) (_ : CommRing Ā) (_ : HopfAlgebra K Ā) (_ : Coalgebra.IsCocomm K Ā) (_ : Module.Finite K Ā)
      (π : A →ₐc[K] Ā), Function.Surjective π ∧
      (∀ ψ : Ā →ₐ[K] AlgebraicClosure K, WithConv.toConv (ψ.comp (π : A →ₐ[K] Ā)) ∈ W) ∧
      (∀ ν ∈ W, ∃ ψ : Ā →ₐ[K] AlgebraicClosure K, ψ.comp (π : A →ₐ[K] Ā) = WithConv.ofConv ν) ∧
      Module.finrank K Ā = Nat.card ↥W ∧
      (∀ h : ↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K,
        ∃ ν : WithConv (A →ₐ[K] AlgebraicClosure K), (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val = h) ∧
      (∀ ν ν' : WithConv (A →ₐ[K] AlgebraicClosure K),
        (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val = (WithConv.ofConv ν').comp (HopfAlgebra.hopfKer π).val
          ↔ ∃ w ∈ W, ν' = ν * w) ∧
      Module.finrank K ↥(HopfAlgebra.hopfKer π) * Nat.card ↥W = Module.finrank K A := by
  classical

  have hD : IntermediateField.fixedField (⊤ : Subgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) = ⊥ := by
    rw [← IntermediateField.fixingSubgroup_bot]
    exact InfiniteGalois.fixedField_fixingSubgroup ⊥

  have hstab : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, σ ∈ (⊤ : Subgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) →
      ∀ p ∈ (W : Set (WithConv (A →ₐ[K] AlgebraicClosure K))), ∃ p' ∈ (W : Set (WithConv (A →ₐ[K] AlgebraicClosure K))),
        ∀ a : A, WithConv.ofConv p' a = σ (WithConv.ofConv p a) := by
    intro σ _ p hp
    refine ⟨WithConv.toConv ((σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K).comp (WithConv.ofConv p)), ?_, fun a => rfl⟩
    exact hW σ p hp _ (fun a => rfl)
  have hbijW : Function.Bijective (HopfAlgebra.evalQuot W) :=
    evalQuot_bijective_of_bijective_lift_liftPoint_image W
      (HopfAlgebra.lift_liftPoint_bijective_of_forall_exists_comp_eq ⊤ hD
        (WithConv.ofConv : WithConv (A →ₐ[K] AlgebraicClosure K) → (A →ₐ[K] AlgebraicClosure K)) WithConv.ofConv_injective hev (W : Set (WithConv (A →ₐ[K] AlgebraicClosure K))) hstab)

  let pt : ↥W → (HopfAlgebra.pointQuot W →ₐ[K] AlgebraicClosure K) :=
    fun s => HopfAlgebra.liftPoint (HopfAlgebra.ptSet W) (WithConv.ofConv s.1) (HopfAlgebra.ofConv_mem_ptSet s)
  have hinj : Function.Injective
      (Algebra.TensorProduct.lift (Algebra.ofId (AlgebraicClosure K) (↥W → AlgebraicClosure K)) (Pi.algHom K _ fun p : ↥W => pt p)
        (fun _ _ => Commute.all _ _) : AlgebraicClosure K ⊗[K] HopfAlgebra.pointQuot W →ₐ[AlgebraicClosure K] (↥W → AlgebraicClosure K)) :=
    hbijW.1
  have hsep : ∀ x : HopfAlgebra.pointQuot W ⊗[K] HopfAlgebra.pointQuot W,
      (∀ (ν ν' : A →ₐ[K] AlgebraicClosure K) (hν : ν ∈ HopfAlgebra.ptSet W) (hν' : ν' ∈ HopfAlgebra.ptSet W),
        HopfAlgebra.evalPair (HopfAlgebra.ptSet W) ν ν' hν hν' x = 0) → x = 0 := by
    intro x hx
    apply Algebra.TensorProduct.eq_zero_of_forall_lift_apply_eq_zero pt hinj x
    intro p q
    have key : Algebra.TensorProduct.lift (pt p) (pt q) (fun _ _ => Commute.all _ _)
        = HopfAlgebra.evalPair (HopfAlgebra.ptSet W) (WithConv.ofConv p.1) (WithConv.ofConv q.1)
            (HopfAlgebra.ofConv_mem_ptSet p) (HopfAlgebra.ofConv_mem_ptSet q) := by
      apply Algebra.TensorProduct.ext'
      intro a b
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [Algebra.TensorProduct.lift_tmul, HopfAlgebra.evalPair_tmul]
      rfl
    rw [key]
    exact hx _ _ _ _
  have hinv : ∀ ν ∈ HopfAlgebra.ptSet W, ∃ ν' ∈ HopfAlgebra.ptSet W,
      ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := K) := by
    intro ν hν
    obtain ⟨ν', hν', h⟩ := exists_mem_toLinearMap_eq_comp_antipode_of_finite W ν hν
    exact ⟨ν', hν', h⟩
  obtain ⟨hcomul, hcounit, hanti⟩ :=
    HopfAlgebra.map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet
      W hsep hinv

  obtain ⟨Ā, instR, instH, π, hsurj, hker, hcoc, hfin, hUP⟩ :=
    HopfAlgebra.exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal
      (HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet W)) hcomul hcounit hanti
  haveI : Coalgebra.IsCocomm K Ā := hcoc inferInstance
  haveI : Module.Finite K Ā := hfin inferInstance

  have hπ0 : ∀ a ∈ HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet W), π a = 0 := by
    intro a ha
    have : a ∈ RingHom.ker (π : A →+* Ā) := by rw [hker]; exact ha
    exact this
  have c2 : ∀ ψ : Ā →ₐ[K] AlgebraicClosure K, WithConv.toConv (ψ.comp (π : A →ₐ[K] Ā)) ∈ W := by
    intro ψ
    apply toConv_mem_of_forall_mem_vanishingIdeal_eq_zero W hbijW
    intro a ha
    rw [AlgHom.comp_apply]
    show ψ (π a) = 0
    rw [hπ0 a ha, map_zero]

  have c3 : ∀ ν ∈ W, ∃ ψ : Ā →ₐ[K] AlgebraicClosure K, ψ.comp (π : A →ₐ[K] Ā) = WithConv.ofConv ν := by
    intro ν hν
    have hle : ∀ a ∈ RingHom.ker ((π : A →ₐ[K] Ā) : A →+* Ā), (WithConv.ofConv ν : A →ₐ[K] AlgebraicClosure K) a = 0 := by
      intro a ha
      have ha' : a ∈ HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet W) := by
        have : a ∈ RingHom.ker (π : A →+* Ā) := ha
        rwa [hker] at this
      exact ha' (WithConv.ofConv ν) hν
    let e1 : (A ⧸ RingHom.ker ((π : A →ₐ[K] Ā) : A →+* Ā)) ≃ₐ[K] Ā :=
      Ideal.quotientKerAlgEquivOfSurjective hsurj
    let ψ0 : (A ⧸ RingHom.ker ((π : A →ₐ[K] Ā) : A →+* Ā)) →ₐ[K] AlgebraicClosure K :=
      Ideal.Quotient.liftₐ _ (WithConv.ofConv ν) hle
    refine ⟨ψ0.comp (e1.symm : Ā →ₐ[K] _), ?_⟩
    apply AlgHom.ext
    intro a
    have hs : e1.symm (π a) = Ideal.Quotient.mk _ a := by
      rw [AlgEquiv.symm_apply_eq]
      show π a = Ideal.quotientKerAlgEquivOfSurjective hsurj (Ideal.Quotient.mk _ a)
      rw [Ideal.quotientKerAlgEquivOfSurjective_apply]
      exact (RingHom.kerLift_mk ((π : A →ₐ[K] Ā) : A →+* Ā) a).symm
    show ψ0 (e1.symm ((π : A →ₐ[K] Ā) a)) = WithConv.ofConv ν a
    rw [show (π : A →ₐ[K] Ā) a = π a from rfl, hs]
    rfl

  have c4 : Module.finrank K Ā = Nat.card ↥W := by
    have e1 : (A ⧸ RingHom.ker ((π : A →ₐ[K] Ā) : A →+* Ā)) ≃ₐ[K] Ā :=
      Ideal.quotientKerAlgEquivOfSurjective hsurj
    have hk : RingHom.ker ((π : A →ₐ[K] Ā) : A →+* Ā) = HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet W) :=
      hker
    have e2 : (A ⧸ RingHom.ker ((π : A →ₐ[K] Ā) : A →+* Ā)) ≃ₐ[K] HopfAlgebra.pointQuot W :=
      Ideal.quotientEquivAlgOfEq K hk
    rw [← finrank_pointQuot_eq_natCard W hbijW, ← e2.toLinearEquiv.finrank_eq, e1.toLinearEquiv.finrank_eq]

  have c5 : ∀ h : ↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K,
      ∃ ν : WithConv (A →ₐ[K] AlgebraicClosure K), (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val = h := by
    intro h
    obtain ⟨ν, hν⟩ := HopfAlgebra.exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed π hsurj (AlgebraicClosure K) h
    exact ⟨WithConv.toConv ν, hν⟩

  haveI : Module.Free K Ā := Module.Free.of_divisionRing K Ā
  have hP2 := P2c (R := K) π hsurj (AlgebraicClosure K)
  have c6 : ∀ ν ν' : WithConv (A →ₐ[K] AlgebraicClosure K),
      (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val = (WithConv.ofConv ν').comp (HopfAlgebra.hopfKer π).val
        ↔ ∃ w ∈ W, ν' = ν * w := by
    intro ν ν'
    rw [hP2]
    constructor
    · rintro ⟨χ, hχ, -⟩
      exact ⟨WithConv.toConv (χ.comp (π : A →ₐ[K] Ā)), c2 χ, hχ⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨χ, hχ⟩ := c3 w hw
      have htw : WithConv.toConv (χ.comp (π : A →ₐ[K] Ā)) = w := by rw [hχ]
      refine ⟨χ, ?_, ?_⟩
      · show ν * w = ν * WithConv.toConv (χ.comp (π : A →ₐ[K] Ā))
        rw [htw]
      · intro χ' h'
        have h'' : ν * w = ν * WithConv.toConv (χ'.comp (π : A →ₐ[K] Ā)) := h'
        have h1 : WithConv.toConv (χ'.comp (π : A →ₐ[K] Ā)) = WithConv.toConv (χ.comp (π : A →ₐ[K] Ā)) :=
          ((mul_right_injective_point ν h'').symm).trans htw.symm
        have h2 : χ'.comp (π : A →ₐ[K] Ā) = χ.comp (π : A →ₐ[K] Ā) := congrArg WithConv.ofConv h1
        apply AlgHom.ext
        intro b
        obtain ⟨a, rfl⟩ := hsurj b
        exact DFunLike.congr_fun h2 a

  have c7 : Module.finrank K ↥(HopfAlgebra.hopfKer π) * Nat.card ↥W = Module.finrank K A := by
    obtain ⟨hfinS, hS⟩ := finrank_eq_natCard_algHom_of_forall_exists_comp_val_eq hev (HopfAlgebra.hopfKer π)
      (HopfAlgebra.exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed π hsurj (AlgebraicClosure K))
    haveI := hfinS
    have hA := finrank_eq_natCard_of_bijective_eval hev
    have hM := natCard_eq_natCard_mul_natCard_of_fibre
      (fun ν : WithConv (A →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val)
      (fun h => c5 h) W c6 (fun ν => mul_right_injective_point ν)
    rw [hS, hA, hM, mul_comm]
  exact ⟨Ā, instR, instH, inferInstance, inferInstance, π, hsurj, c2, c3, c4, c5, c6, c7⟩

end HopfAlgebra.C5

theorem solution
    (K : Type u) [Field K] [PerfectField K]
    (A : Type v) [CommRing A] [HopfAlgebra K A] [Module.Finite K A] [Coalgebra.IsCocomm K A]
    [Finite (WithConv (A →ₐ[K] AlgebraicClosure K))]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure K) (WithConv (A →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
        (Pi.algHom K _
          fun ν : WithConv (A →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : A →ₐ[K] AlgebraicClosure K))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure K ⊗[K] A →ₐ[AlgebraicClosure K]
          (WithConv (A →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)))
    (W : Submonoid (WithConv (A →ₐ[K] AlgebraicClosure K)))
    (hW : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ ν ∈ W,
      ∀ ν' : WithConv (A →ₐ[K] AlgebraicClosure K),
        (∀ a : A, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) → ν' ∈ W) :
    ∃ (Ā : Type v) (_ : CommRing Ā) (_ : HopfAlgebra K Ā) (_ : Coalgebra.IsCocomm K Ā) (_ : Module.Finite K Ā)
      (π : A →ₐc[K] Ā), Function.Surjective π ∧
      (∀ ψ : Ā →ₐ[K] AlgebraicClosure K, WithConv.toConv (ψ.comp (π : A →ₐ[K] Ā)) ∈ W) ∧
      (∀ ν ∈ W, ∃ ψ : Ā →ₐ[K] AlgebraicClosure K, ψ.comp (π : A →ₐ[K] Ā) = WithConv.ofConv ν) ∧
      Module.finrank K Ā = Nat.card ↥W ∧
      (∀ h : ↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K,
        ∃ ν : WithConv (A →ₐ[K] AlgebraicClosure K), (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val = h) ∧
      (∀ ν ν' : WithConv (A →ₐ[K] AlgebraicClosure K),
        (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val = (WithConv.ofConv ν').comp (HopfAlgebra.hopfKer π).val
          ↔ ∃ w ∈ W, ν' = ν * w) ∧
      Module.finrank K ↥(HopfAlgebra.hopfKer π) * Nat.card ↥W = Module.finrank K A :=
  HopfAlgebra.C5.main K A hev W hW

end S_HopfAlgebra_exists_bialgHom_surjective_points_eq_of_submonoid_of_bijective_evalPoints_of_perfectField
end P2MW
export P2MW.S_HopfAlgebra_exists_bialgHom_surjective_points_eq_of_submonoid_of_bijective_evalPoints_of_perfectField (solution)
