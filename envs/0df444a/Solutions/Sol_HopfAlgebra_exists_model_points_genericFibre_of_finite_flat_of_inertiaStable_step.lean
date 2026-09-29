-- Prove2me | solution 1 for HopfAlgebra.exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4a594b8a-0b30-51a3-b2a0-8148f49d158a

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CharacterClosure
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_HopfAlgebra_HopfOrderData
import Theorems.Thm_HopfAlgebra_evalQuot_bijective_of_forall_exists_comp_eq
import Theorems.Thm_HopfAlgebra_map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet
import Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal
import Theorems.Thm_HopfOrder_finite_and_comul_mem_and_antipode_mem_and_counit_mem_range_comp_includeRight
import Theorems.Thm_HopfOrder_isHopfOrder_comap_hopfKer
import Theorems.Thm_HopfOrder_isHopfOrder_map
import Theorems.Thm_HopfOrder_finrank_eq_finrank
import Theorems.Thm_HopfOrder_finrank_eq_finrank_comap_hopfKer_mul_finrank_map
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_GaloisRep_natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf
import Theorems.Thm_GaloisRep_bijective_lift_pi_algHom_of_finiteFlatHopf
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed
import Theorems.Thm_HopfOrder_exists_equiv_algHom_apply_eq_and_toConv_mul
import Theorems.Thm_HopfAlgebra_toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique
import Theorems.Thm_AlgHom_liftEquiv_symm_withConv_mul
import Theorems.Thm_HopfAlgebra_forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one
import Theorems.Thm_AlgHom_exists_eq_comp_evalAlgHom_of_isDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step

set_option autoImplicit false
open scoped TensorProduct

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk ofAlgHom mul_antipode_lTensor_comul_apply mul_antipode_rTensor_comul_apply vanishingIdealOfPoints vanishingIdealOfPoints_antitone ptSet mem_ptSet_iff ofConv_mem_ptSet ptSet_mono pointQuot evalQuot evalQuot_tmul HopfKerHopf.coaction_repr HopfKerHopf.counit_coe HopfKerHopf.hopfKerVal coaction hopfKer evalQuot_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal natCard_algHom_eq_finrank_of_charZero toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one"
p2m_open "HopfAlgebra"
namespace StepOrder

open WithConv

section Factor

variable {F : Type*} [CommSemiring F] {A₀ : Type*} [CommRing A₀] [Algebra F A₀]
  {A' : Type*} [CommRing A'] [Algebra F A'] {T : Type*} [Semiring T] [Algebra F T]

noncomputable def factor (π : A₀ →ₐ[F] A') (hπ : Function.Surjective π) (φ : A₀ →ₐ[F] T)
    (h : ∀ a, π a = 0 → φ a = 0) : A' →ₐ[F] T :=
  (Ideal.Quotient.liftₐ (RingHom.ker π) φ (fun a ha => h a ha)).comp
    (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom

theorem factor_apply (π : A₀ →ₐ[F] A') (hπ : Function.Surjective π) (φ : A₀ →ₐ[F] T)
    (h : ∀ a, π a = 0 → φ a = 0) (a : A₀) : factor π hπ φ h (π a) = φ a := by
  have hq : (Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π a) = Ideal.Quotient.mk (RingHom.ker π) a := by
    rw [AlgEquiv.symm_apply_eq, Ideal.quotientKerAlgEquivOfSurjective_mk]
  change (Ideal.Quotient.liftₐ (RingHom.ker π) φ (fun a ha => h a ha))
      ((Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π a)) = φ a
  rw [hq]
  rfl

theorem factor_comp (π : A₀ →ₐ[F] A') (hπ : Function.Surjective π) (φ : A₀ →ₐ[F] T)
    (h : ∀ a, π a = 0 → φ a = 0) : (factor π hπ φ h).comp π = φ :=
  AlgHom.ext (factor_apply π hπ φ h)

theorem eq_of_comp_eq (π : A₀ →ₐ[F] A') (hπ : Function.Surjective π) {ψ ψ' : A' →ₐ[F] T}
    (h : ψ.comp π = ψ'.comp π) : ψ = ψ' := by
  apply AlgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := hπ x
  exact DFunLike.congr_fun h a

end Factor

section QuotBialgHom

variable {F : Type*} [CommRing F] {A₀ : Type*} [CommRing A₀] [Bialgebra F A₀]
  {A₁ : Type*} [CommRing A₁] [Bialgebra F A₁] {A₂ : Type*} [CommRing A₂] [Bialgebra F A₂]

noncomputable def quotBialgHom (π₁ : A₀ →ₐc[F] A₁) (h₁ : Function.Surjective π₁) (π₂ : A₀ →ₐc[F] A₂)
    (hk : ∀ a, π₁ a = 0 → π₂ a = 0) : A₁ →ₐc[F] A₂ :=
  BialgHom.ofAlgHom (factor (π₁ : A₀ →ₐ[F] A₁) h₁ (π₂ : A₀ →ₐ[F] A₂) hk)
    (by
      have h : ((Bialgebra.counitAlgHom F A₂).comp (factor (π₁ : A₀ →ₐ[F] A₁) h₁ (π₂ : A₀ →ₐ[F] A₂) hk)).comp
          (π₁ : A₀ →ₐ[F] A₁) = (Bialgebra.counitAlgHom F A₁).comp (π₁ : A₀ →ₐ[F] A₁) := by
        rw [AlgHom.comp_assoc, factor_comp, BialgHom.counitAlgHom_comp, BialgHom.counitAlgHom_comp]
      exact eq_of_comp_eq (π₁ : A₀ →ₐ[F] A₁) h₁ h)
    (by
      set f := factor (π₁ : A₀ →ₐ[F] A₁) h₁ (π₂ : A₀ →ₐ[F] A₂) hk with hf
      have hcomp : f.comp (π₁ : A₀ →ₐ[F] A₁) = (π₂ : A₀ →ₐ[F] A₂) := factor_comp _ h₁ _ hk
      have h : ((Algebra.TensorProduct.map f f).comp (Bialgebra.comulAlgHom F A₁)).comp (π₁ : A₀ →ₐ[F] A₁)
          = ((Bialgebra.comulAlgHom F A₂).comp f).comp (π₁ : A₀ →ₐ[F] A₁) := by
        rw [AlgHom.comp_assoc, ← BialgHom.map_comp_comulAlgHom, ← AlgHom.comp_assoc,
          ← Algebra.TensorProduct.map_comp, hcomp, BialgHom.map_comp_comulAlgHom, AlgHom.comp_assoc, hcomp]
      exact eq_of_comp_eq (π₁ : A₀ →ₐ[F] A₁) h₁ h)

theorem quotBialgHom_apply (π₁ : A₀ →ₐc[F] A₁) (h₁ : Function.Surjective π₁) (π₂ : A₀ →ₐc[F] A₂)
    (hk : ∀ a, π₁ a = 0 → π₂ a = 0) (a : A₀) : quotBialgHom π₁ h₁ π₂ hk (π₁ a) = π₂ a :=
  factor_apply (π₁ : A₀ →ₐ[F] A₁) h₁ (π₂ : A₀ →ₐ[F] A₂) hk a

theorem quotBialgHom_comp (π₁ : A₀ →ₐc[F] A₁) (h₁ : Function.Surjective π₁) (π₂ : A₀ →ₐc[F] A₂)
    (hk : ∀ a, π₁ a = 0 → π₂ a = 0) :
    (quotBialgHom π₁ h₁ π₂ hk : A₁ →ₐ[F] A₂).comp (π₁ : A₀ →ₐ[F] A₁) = (π₂ : A₀ →ₐ[F] A₂) :=
  AlgHom.ext (quotBialgHom_apply π₁ h₁ π₂ hk)

theorem quotBialgHom_surjective (π₁ : A₀ →ₐc[F] A₁) (h₁ : Function.Surjective π₁) (π₂ : A₀ →ₐc[F] A₂)
    (hk : ∀ a, π₁ a = 0 → π₂ a = 0) (h₂ : Function.Surjective π₂) :
    Function.Surjective (quotBialgHom π₁ h₁ π₂ hk) := by
  intro y
  obtain ⟨a, rfl⟩ := h₂ y
  exact ⟨π₁ a, quotBialgHom_apply π₁ h₁ π₂ hk a⟩

end QuotBialgHom

section Points

variable {F : Type*} [Field F] {A₀ : Type*} [CommRing A₀] [Bialgebra F A₀]
  {L : Type*} [Field L] [Algebra F L]
  (S : Submonoid (WithConv (A₀ →ₐ[F] L)))

theorem toConv_mem_of_forall_mem_vanishingIdeal [Finite ↥S] (hbij : Function.Bijective (evalQuot S))
    (μ : A₀ →ₐ[F] L) (hμ : ∀ a ∈ vanishingIdealOfPoints (ptSet S), μ a = 0) : toConv μ ∈ S := by
  classical
  let μb : pointQuot S →ₐ[F] L := Ideal.Quotient.liftₐ _ μ hμ
  let μt : L ⊗[F] pointQuot S →ₐ[L] L := AlgHom.liftEquiv F L (pointQuot S) L μb
  let E : L ⊗[F] pointQuot S ≃ₐ[L] (↥S → L) := AlgEquiv.ofBijective (evalQuot S) hbij
  let ψ : (↥S → L) →ₐ[L] L := μt.comp (E.symm : (↥S → L) →ₐ[L] L ⊗[F] pointQuot S)
  obtain ⟨s, φ₀, hψ⟩ :=
    AlgHom.exists_eq_comp_evalAlgHom_of_isDomain (K := L) (Ω := L) (A := fun _ : ↥S => L) ψ
  have hφ₀ : ∀ x : L, φ₀ x = x := fun x => by simpa using φ₀.commutes x
  have key : ∀ a : A₀, μ a = (ofConv s.1) a := by
    intro a
    have h1 : μ a = μt ((1 : L) ⊗ₜ[F] Ideal.Quotient.mk (vanishingIdealOfPoints (ptSet S)) a) := by
      simp only [μt, AlgHom.liftEquiv_tmul, one_smul]
      rfl
    have h2 : μt ((1 : L) ⊗ₜ[F] Ideal.Quotient.mk (vanishingIdealOfPoints (ptSet S)) a)
        = ψ (E ((1 : L) ⊗ₜ[F] Ideal.Quotient.mk (vanishingIdealOfPoints (ptSet S)) a)) := by
      change _ = μt (E.symm (E _))
      rw [AlgEquiv.symm_apply_apply]
    rw [h1, h2, hψ, AlgHom.comp_apply, Pi.evalAlgHom_apply, hφ₀]
    change evalQuot S ((1 : L) ⊗ₜ[F] Ideal.Quotient.mk _ a) s = _
    rw [evalQuot_tmul, one_mul]
  have hμs : μ = ofConv s.1 := AlgHom.ext key
  rw [hμs]
  exact s.2

variable {A' : Type*} [CommRing A'] [Bialgebra F A']
  (π : A₀ →ₐc[F] A') (hπ : Function.Surjective π)
  (hker : ∀ a, π a = 0 ↔ a ∈ vanishingIdealOfPoints (ptSet S))

include hker in
theorem apply_eq_zero_of_map_eq_zero (s : ↥S) (a : A₀) (ha : π a = 0) : (ofConv s.1) a = 0 :=
  ((hker a).mp ha) _ (ofConv_mem_ptSet s)

noncomputable def pt (s : ↥S) : A' →ₐ[F] L :=
  factor (π : A₀ →ₐ[F] A') hπ (ofConv s.1) (fun a ha => apply_eq_zero_of_map_eq_zero S π hker s a ha)

theorem pt_apply (s : ↥S) (a : A₀) : pt S π hπ hker s (π a) = (ofConv s.1) a :=
  factor_apply _ hπ _ _ a

theorem pt_comp (s : ↥S) : (pt S π hπ hker s).comp (π : A₀ →ₐ[F] A') = ofConv s.1 :=
  factor_comp _ hπ _ _

theorem pt_injective : Function.Injective (pt S π hπ hker) := by
  intro s t h
  apply Subtype.ext
  apply WithConv.ext
  rw [← pt_comp S π hπ hker s, ← pt_comp S π hπ hker t, h]

theorem toConv_pt_mul (s t : ↥S) :
    toConv (pt S π hπ hker (s * t)) = toConv (pt S π hπ hker s) * toConv (pt S π hπ hker t) := by
  apply WithConv.ext
  apply eq_of_comp_eq (π : A₀ →ₐ[F] A') hπ
  change (pt S π hπ hker (s * t)).comp (π : A₀ →ₐ[F] A')
    = (toConv (pt S π hπ hker s) * toConv (pt S π hπ hker t)).ofConv.comp (π : A₀ →ₐ[F] A')
  rw [AlgHom.convMul_comp_bialgHom_distrib, pt_comp, pt_comp, pt_comp]
  rfl

theorem pt_one : toConv (pt S π hπ hker 1) = 1 := by
  apply WithConv.ext
  apply eq_of_comp_eq (π : A₀ →ₐ[F] A') hπ
  change (pt S π hπ hker 1).comp (π : A₀ →ₐ[F] A') = (ofConv (1 : WithConv (A' →ₐ[F] L))).comp (π : A₀ →ₐ[F] A')
  rw [pt_comp]
  apply AlgHom.ext
  intro a
  change (1 : WithConv (A₀ →ₐ[F] L)) a = (1 : WithConv (A' →ₐ[F] L)) (π a)
  rw [AlgHom.convOne_apply, AlgHom.convOne_apply]
  congr 1
  exact (CoalgHomClass.counit_comp_apply π a).symm

theorem pt_surjective [Finite ↥S] (hbij : Function.Bijective (evalQuot S)) :
    Function.Surjective (pt S π hπ hker) := by
  intro μ
  have hmem : toConv (μ.comp (π : A₀ →ₐ[F] A')) ∈ S :=
    toConv_mem_of_forall_mem_vanishingIdeal S hbij _ (fun a ha => by
      rw [AlgHom.comp_apply]
      change μ (π a) = 0
      rw [(hker a).mpr ha, map_zero])
  refine ⟨⟨_, hmem⟩, ?_⟩
  apply eq_of_comp_eq (π : A₀ →ₐ[F] A') hπ
  rw [pt_comp]

theorem pt_eq_comp (τ : L →ₐ[F] L) (s t : ↥S) (h : ∀ a : A₀, (ofConv t.1) a = τ ((ofConv s.1) a)) :
    pt S π hπ hker t = τ.comp (pt S π hπ hker s) := by
  apply eq_of_comp_eq (π : A₀ →ₐ[F] A') hπ
  rw [pt_comp, AlgHom.comp_assoc, pt_comp]
  exact AlgHom.ext h

end Points

end StepOrder
end HopfAlgebra

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk ofAlgHom mul_antipode_lTensor_comul_apply mul_antipode_rTensor_comul_apply vanishingIdealOfPoints vanishingIdealOfPoints_antitone ptSet mem_ptSet_iff ofConv_mem_ptSet ptSet_mono pointQuot evalQuot evalQuot_tmul HopfKerHopf.coaction_repr HopfKerHopf.counit_coe HopfKerHopf.hopfKerVal coaction hopfKer evalQuot_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal natCard_algHom_eq_finrank_of_charZero toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one"
p2m_open "HopfAlgebra"
namespace StepOrder

open WithConv

section ConvPow
variable {R : Type*} [CommRing R] {C : Type*} [CommRing C] [Bialgebra R C]
  {A : Type*} [CommRing A] [Algebra R A] {A₂ : Type*} [CommRing A₂] [Algebra R A₂]
  {B : Type*} [CommRing B] [Bialgebra R B]

theorem algHom_comp_convOne (h : A →ₐ[R] A₂) :
    h.comp (ofConv (1 : WithConv (C →ₐ[R] A))) = ofConv (1 : WithConv (C →ₐ[R] A₂)) := by
  apply AlgHom.ext
  intro c
  change h ((1 : WithConv (C →ₐ[R] A)) c) = (1 : WithConv (C →ₐ[R] A₂)) c
  rw [AlgHom.convOne_apply, AlgHom.convOne_apply, AlgHom.commutes]

theorem toConv_algHom_comp_pow (h : A →ₐ[R] A₂) (f : WithConv (C →ₐ[R] A)) (n : ℕ) :
    (toConv (h.comp f.ofConv)) ^ n = toConv (h.comp (f ^ n).ofConv) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, algHom_comp_convOne]
  | succ n ih =>
    rw [pow_succ, pow_succ, ih, AlgHom.comp_convMul_distrib]

theorem convOne_comp_bialgHom (h : B →ₐc[R] C) :
    (ofConv (1 : WithConv (C →ₐ[R] A))).comp (h : B →ₐ[R] C) = ofConv (1 : WithConv (B →ₐ[R] A)) := by
  apply AlgHom.ext
  intro b
  change (1 : WithConv (C →ₐ[R] A)) (h b) = (1 : WithConv (B →ₐ[R] A)) b
  rw [AlgHom.convOne_apply, AlgHom.convOne_apply]
  congr 1
  exact CoalgHomClass.counit_comp_apply h b

theorem toConv_comp_bialgHom_pow (f : WithConv (C →ₐ[R] A)) (h : B →ₐc[R] C) (n : ℕ) :
    (toConv (f.ofConv.comp (h : B →ₐ[R] C))) ^ n = toConv ((f ^ n).ofConv.comp (h : B →ₐ[R] C)) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, convOne_comp_bialgHom]
  | succ n ih =>
    rw [pow_succ, pow_succ, ih, AlgHom.convMul_comp_bialgHom_distrib]

end ConvPow

section Transfer
variable {R : Type*} [CommRing R] {A₁ : Type*} [CommRing A₁] [Bialgebra R A₁]
  {A₂ : Type*} [CommRing A₂] [Bialgebra R A₂]

theorem comp_id_pow_eq_id_pow_comp (h : A₁ →ₐc[R] A₂) (n : ℕ) :
    (h : A₁ →ₐ[R] A₂).comp ((toConv (AlgHom.id R A₁)) ^ n).ofConv
      = ((toConv (AlgHom.id R A₂)) ^ n).ofConv.comp (h : A₁ →ₐ[R] A₂) := by
  have h1 := toConv_algHom_comp_pow (h : A₁ →ₐ[R] A₂) (toConv (AlgHom.id R A₁)) n
  have h2 := toConv_comp_bialgHom_pow (toConv (AlgHom.id R A₂)) h n
  rw [ofConv_toConv, AlgHom.comp_id] at h1
  rw [ofConv_toConv, AlgHom.id_comp] at h2
  exact congrArg ofConv (h1.symm.trans h2)

theorem toConv_id_pow_eq_one_of_injective (h : A₁ →ₐc[R] A₂) (hinj : Function.Injective h) (n : ℕ)
    (h₂ : (toConv (AlgHom.id R A₂)) ^ n = 1) : (toConv (AlgHom.id R A₁)) ^ n = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  apply hinj
  have hc := DFunLike.congr_fun (comp_id_pow_eq_id_pow_comp h n) a
  rw [h₂] at hc
  rw [AlgHom.comp_apply] at hc
  change (h : A₁ →ₐ[R] A₂) (((toConv (AlgHom.id R A₁)) ^ n).ofConv a)
    = (h : A₁ →ₐ[R] A₂) ((ofConv (1 : WithConv (A₁ →ₐ[R] A₁))) a)
  rw [hc]
  exact (DFunLike.congr_fun (convOne_comp_bialgHom (A := A₂) h) a).trans
    (DFunLike.congr_fun (algHom_comp_convOne (C := A₁) (h : A₁ →ₐ[R] A₂)) a).symm

theorem toConv_id_pow_eq_one_of_surjective (h : A₁ →ₐc[R] A₂) (hsurj : Function.Surjective h) (n : ℕ)
    (h₁ : (toConv (AlgHom.id R A₁)) ^ n = 1) : (toConv (AlgHom.id R A₂)) ^ n = 1 := by
  apply WithConv.ext
  apply eq_of_comp_eq (h : A₁ →ₐ[R] A₂) hsurj
  rw [← comp_id_pow_eq_id_pow_comp h n, h₁]
  exact (algHom_comp_convOne (C := A₁) (h : A₁ →ₐ[R] A₂)).trans (convOne_comp_bialgHom (A := A₂) h).symm

end Transfer

section PiCriterion
variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Bialgebra R A]
  {ι : Type*} {L : Type*} [CommRing L] [Algebra R L]

theorem toConv_id_pow_eq_one_of_points (ν : ι → (A →ₐ[R] L))
    (hinj : Function.Injective (Pi.algHom R (fun _ : ι => L) ν)) (n : ℕ)
    (hν : ∀ i, (toConv (ν i)) ^ n = 1) : (toConv (AlgHom.id R A)) ^ n = 1 := by
  set E : A →ₐ[R] (ι → L) := Pi.algHom R (fun _ : ι => L) ν with hE

  have hEn : (toConv E) ^ n = 1 := by
    apply WithConv.ext
    apply AlgHom.ext
    intro a
    funext i
    have h1 := toConv_algHom_comp_pow (Pi.evalAlgHom R (fun _ : ι => L) i) (toConv E) n
    have hcomp : (Pi.evalAlgHom R (fun _ : ι => L) i).comp (toConv E).ofConv = ν i := by
      apply AlgHom.ext; intro x; rfl
    rw [hcomp, hν i] at h1
    have h2 := DFunLike.congr_fun (congrArg ofConv h1) a
    change ((toConv E ^ n).ofConv a) i = ((1 : WithConv (A →ₐ[R] (ι → L))).ofConv a) i
    rw [show ((toConv E ^ n).ofConv a) i = (Pi.evalAlgHom R (fun _ : ι => L) i) ((toConv E ^ n).ofConv a)
      from rfl, ← AlgHom.comp_apply, ← h2]
    exact DFunLike.congr_fun (algHom_comp_convOne (C := A) (Pi.evalAlgHom R (fun _ : ι => L) i)) a

  have h3 := toConv_algHom_comp_pow E (toConv (AlgHom.id R A)) n
  rw [ofConv_toConv, AlgHom.comp_id, hEn] at h3
  apply WithConv.ext
  apply AlgHom.ext
  intro a
  apply hinj
  have h4 := DFunLike.congr_fun (congrArg ofConv h3) a
  change E (((toConv (AlgHom.id R A)) ^ n).ofConv a) = E ((ofConv (1 : WithConv (A →ₐ[R] A))) a)
  rw [AlgHom.comp_apply] at h4
  rw [← h4]
  exact (DFunLike.congr_fun (algHom_comp_convOne (C := A) E) a).symm

end PiCriterion

section BaseChangeDown
variable {R : Type*} [CommRing R] {F : Type*} [CommRing F] [Algebra R F]
  {B : Type*} [CommRing B] [Bialgebra R B]

theorem toConv_id_pow_eq_one_of_baseChange
    (hinj : Function.Injective (Algebra.TensorProduct.includeRight : B →ₐ[R] F ⊗[R] B)) (n : ℕ)
    (hF : (toConv (AlgHom.id F (F ⊗[R] B))) ^ n = 1) : (toConv (AlgHom.id R B)) ^ n = 1 := by
  set i : B →ₐ[R] F ⊗[R] B := Algebra.TensorProduct.includeRight with hi
  set LE := AlgHom.liftEquiv R F B (F ⊗[R] B) with hLE
  have hone : toConv (LE.symm (1 : WithConv (F ⊗[R] B →ₐ[F] F ⊗[R] B)).ofConv)
      = (1 : WithConv (B →ₐ[R] F ⊗[R] B)) := by
    apply WithConv.ext
    apply AlgHom.ext
    intro b
    change (1 : WithConv (F ⊗[R] B →ₐ[F] F ⊗[R] B)) ((1 : F) ⊗ₜ[R] b) = (1 : WithConv (B →ₐ[R] F ⊗[R] B)) b
    rw [AlgHom.convOne_apply, AlgHom.convOne_apply, TensorProduct.counit_tmul, CommSemiring.counit_apply,
      ← Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_apply]
  have hid : toConv (LE.symm (toConv (AlgHom.id F (F ⊗[R] B))).ofConv) = toConv i := by
    apply WithConv.ext
    apply AlgHom.ext
    intro b
    rfl
  have hpow : ∀ m : ℕ, toConv (LE.symm ((toConv (AlgHom.id F (F ⊗[R] B))) ^ m).ofConv) = (toConv i) ^ m := by
    intro m
    induction m with
    | zero => exact hone
    | succ m ih =>
      change toConv (LE.symm ((toConv (AlgHom.id F (F ⊗[R] B))) ^ m * toConv (AlgHom.id F (F ⊗[R] B))).ofConv)
        = (toConv i) ^ m * toConv i
      rw [hLE, AlgHom.liftEquiv_symm_withConv_mul, ← hLE, ih, hid]
  have h1 : (toConv i) ^ n = 1 := by rw [← hpow n, hF]; exact hone
  have h2 := toConv_algHom_comp_pow i (toConv (AlgHom.id R B)) n
  rw [ofConv_toConv, AlgHom.comp_id, h1] at h2

  apply WithConv.ext
  apply AlgHom.ext
  intro b
  apply hinj
  have h3 := DFunLike.congr_fun (congrArg ofConv h2) b
  change (ofConv (1 : WithConv (B →ₐ[R] F ⊗[R] B))) b = i (((toConv (AlgHom.id R B)) ^ n).ofConv b) at h3
  change i (((toConv (AlgHom.id R B)) ^ n).ofConv b) = i ((ofConv (1 : WithConv (B →ₐ[R] B))) b)
  rw [← h3]
  exact (DFunLike.congr_fun (algHom_comp_convOne (C := B) i) b).symm

end BaseChangeDown

end StepOrder
end HopfAlgebra

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk ofAlgHom mul_antipode_lTensor_comul_apply mul_antipode_rTensor_comul_apply vanishingIdealOfPoints vanishingIdealOfPoints_antitone ptSet mem_ptSet_iff ofConv_mem_ptSet ptSet_mono pointQuot evalQuot evalQuot_tmul HopfKerHopf.coaction_repr HopfKerHopf.counit_coe HopfKerHopf.hopfKerVal coaction hopfKer evalQuot_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal natCard_algHom_eq_finrank_of_charZero toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one"
p2m_open "HopfAlgebra"
namespace StepOrder

open WithConv

section GenericFibrePoints
variable (R₀ : Type*) [CommRing R₀] (F : Type*) [Field F] [Algebra R₀ F]
  (H : Type*) [CommRing H] [Bialgebra R₀ H]
  (L : Type*) [Field L] [Algebra R₀ L] [Algebra F L] [IsScalarTower R₀ F L]

noncomputable def ptsEquiv : WithConv (H →ₐ[R₀] L) ≃* WithConv (F ⊗[R₀] H →ₐ[F] L) where
  toEquiv := WithConv.congr (AlgHom.liftEquiv R₀ F H L)
  map_mul' f g := by
    apply (WithConv.congr (AlgHom.liftEquiv R₀ F H L).symm).injective
    change toConv ((AlgHom.liftEquiv R₀ F H L).symm ((AlgHom.liftEquiv R₀ F H L) (f * g).ofConv))
      = toConv ((AlgHom.liftEquiv R₀ F H L).symm
          (toConv ((AlgHom.liftEquiv R₀ F H L) f.ofConv) * toConv ((AlgHom.liftEquiv R₀ F H L) g.ofConv)).ofConv)
    rw [AlgHom.liftEquiv_symm_withConv_mul]
    change toConv ((AlgHom.liftEquiv R₀ F H L).symm ((AlgHom.liftEquiv R₀ F H L) (f * g).ofConv))
      = toConv ((AlgHom.liftEquiv R₀ F H L).symm ((AlgHom.liftEquiv R₀ F H L) f.ofConv))
        * toConv ((AlgHom.liftEquiv R₀ F H L).symm ((AlgHom.liftEquiv R₀ F H L) g.ofConv))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

variable {R₀ F H L}

theorem ptsEquiv_apply_tmul (f : WithConv (H →ₐ[R₀] L)) (c : F) (h : H) :
    ptsEquiv R₀ F H L f (c ⊗ₜ[R₀] h) = c • f h := rfl

theorem ptsEquiv_symm_apply (ν : WithConv (F ⊗[R₀] H →ₐ[F] L)) (h : H) :
    (ptsEquiv R₀ F H L).symm ν h = ν ((1 : F) ⊗ₜ[R₀] h) := rfl

theorem ptsEquiv_comp (τ : L →ₐ[F] L) (f : WithConv (H →ₐ[R₀] L)) :
    ptsEquiv R₀ F H L (toConv ((τ.restrictScalars R₀).comp f.ofConv))
      = toConv (τ.comp (ptsEquiv R₀ F H L f).ofConv) := by
  apply WithConv.ext
  apply Algebra.TensorProduct.ext'
  intro c h
  change c • τ (f h) = τ ((ptsEquiv R₀ F H L f) (c ⊗ₜ[R₀] h))
  rw [ptsEquiv_apply_tmul, map_smul]

theorem bijective_eval_baseChange
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId L (WithConv (H →ₐ[R₀] L) → L))
        (Pi.algHom R₀ _ fun ν : WithConv (H →ₐ[R₀] L) => (WithConv.ofConv ν : H →ₐ[R₀] L))
        (fun _ _ => Commute.all _ _) : L ⊗[R₀] H →ₐ[L] (WithConv (H →ₐ[R₀] L) → L))) :
    Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId L (WithConv (F ⊗[R₀] H →ₐ[F] L) → L))
        (Pi.algHom F _ fun ν : WithConv (F ⊗[R₀] H →ₐ[F] L) => (WithConv.ofConv ν : F ⊗[R₀] H →ₐ[F] L))
        (fun _ _ => Commute.all _ _) : L ⊗[F] (F ⊗[R₀] H) →ₐ[L] (WithConv (F ⊗[R₀] H →ₐ[F] L) → L)) := by
  set evH := (Algebra.TensorProduct.lift (Algebra.ofId L (WithConv (H →ₐ[R₀] L) → L))
        (Pi.algHom R₀ _ fun ν : WithConv (H →ₐ[R₀] L) => (WithConv.ofConv ν : H →ₐ[R₀] L))
        (fun _ _ => Commute.all _ _) : L ⊗[R₀] H →ₐ[L] (WithConv (H →ₐ[R₀] L) → L)) with hevH
  set evA := (Algebra.TensorProduct.lift (Algebra.ofId L (WithConv (F ⊗[R₀] H →ₐ[F] L) → L))
        (Pi.algHom F _ fun ν : WithConv (F ⊗[R₀] H →ₐ[F] L) => (WithConv.ofConv ν : F ⊗[R₀] H →ₐ[F] L))
        (fun _ _ => Commute.all _ _) : L ⊗[F] (F ⊗[R₀] H) →ₐ[L] (WithConv (F ⊗[R₀] H →ₐ[F] L) → L)) with hevA
  let κ : L ⊗[F] (F ⊗[R₀] H) ≃ₐ[L] L ⊗[R₀] H := Algebra.TensorProduct.cancelBaseChange R₀ F L L H
  let ρ : (WithConv (H →ₐ[R₀] L) → L) →ₐ[L] (WithConv (F ⊗[R₀] H →ₐ[F] L) → L) :=
    Pi.algHom L _ fun ν => Pi.evalAlgHom L (fun _ : WithConv (H →ₐ[R₀] L) => L) ((ptsEquiv R₀ F H L).symm ν)
  have hρ : Function.Bijective ρ :=
    (Equiv.piCongrLeft' (fun _ : WithConv (H →ₐ[R₀] L) => L) (ptsEquiv R₀ F H L).toEquiv).bijective
  have hfac : evA = ρ.comp (evH.comp (κ : L ⊗[F] (F ⊗[R₀] H) →ₐ[L] L ⊗[R₀] H)) := by
    apply Algebra.TensorProduct.ext
    · ext
    · apply AlgHom.ext
      intro x
      funext ν
      change evA ((1 : L) ⊗ₜ[F] x) ν = evH (κ ((1 : L) ⊗ₜ[F] x)) ((ptsEquiv R₀ F H L).symm ν)
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, map_add, Pi.add_apply, Pi.add_apply, hx, hy]
      | tmul c h =>
        rw [hevA, Algebra.TensorProduct.lift_tmul]
        change (Algebra.ofId L _ (1 : L) * (Pi.algHom F _ fun ν : WithConv (F ⊗[R₀] H →ₐ[F] L) =>
          (WithConv.ofConv ν : F ⊗[R₀] H →ₐ[F] L)) (c ⊗ₜ[R₀] h)) ν = _
        rw [map_one, one_mul, Pi.algHom_apply]
        change ν.ofConv (c ⊗ₜ[R₀] h) = evH (κ ((1 : L) ⊗ₜ[F] (c ⊗ₜ[R₀] h))) ((ptsEquiv R₀ F H L).symm ν)
        rw [show κ ((1 : L) ⊗ₜ[F] (c ⊗ₜ[R₀] h)) = (c • (1 : L)) ⊗ₜ[R₀] h from
          Algebra.TensorProduct.cancelBaseChange_tmul R₀ F L L H 1 c h, hevH, Algebra.TensorProduct.lift_tmul]
        change _ = (Algebra.ofId L _ (c • (1 : L)) * (Pi.algHom R₀ _ fun μ : WithConv (H →ₐ[R₀] L) =>
          (WithConv.ofConv μ : H →ₐ[R₀] L)) h) ((ptsEquiv R₀ F H L).symm ν)
        rw [Pi.mul_apply, Pi.algHom_apply, Algebra.ofId_apply, Pi.algebraMap_apply, Algebra.algebraMap_self,
          RingHom.id_apply]
        change ν.ofConv (c ⊗ₜ[R₀] h) = c • (1 : L) * ν.ofConv ((1 : F) ⊗ₜ[R₀] h)
        rw [smul_one_mul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hfac]
  exact hρ.comp (hev.comp κ.bijective)

end GenericFibrePoints

section InversePoint
variable {F : Type*} [CommRing F] {A : Type*} [CommRing A] [HopfAlgebra F A]
  {L : Type*} [CommRing L] [Algebra F L]

theorem toConv_comp_antipode_mul (ν : A →ₐ[F] L) :
    toConv (ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F) (A := A)) * toConv ν.toLinearMap = 1 ∧
    toConv ν.toLinearMap * toConv (ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F) (A := A)) = 1 := by
  constructor
  · apply WithConv.ext
    apply LinearMap.ext
    intro a
    rw [LinearMap.convMul_apply]
    change LinearMap.mul' F L (TensorProduct.map (ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F))
      ν.toLinearMap (Coalgebra.comul a)) = (1 : WithConv (A →ₗ[F] L)).ofConv a
    rw [show TensorProduct.map (ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)) ν.toLinearMap
        = TensorProduct.map ν.toLinearMap ν.toLinearMap ∘ₗ (HopfAlgebraStruct.antipode (R := F) (A := A)).rTensor A
        from by rw [LinearMap.rTensor, ← TensorProduct.map_comp, LinearMap.comp_id],
      LinearMap.comp_apply,
      show LinearMap.mul' F L (TensorProduct.map ν.toLinearMap ν.toLinearMap
          ((HopfAlgebraStruct.antipode (R := F) (A := A)).rTensor A (Coalgebra.comul a)))
        = ν (LinearMap.mul' F A ((HopfAlgebraStruct.antipode (R := F) (A := A)).rTensor A (Coalgebra.comul a)))
        from by
          induction (HopfAlgebraStruct.antipode (R := F) (A := A)).rTensor A (Coalgebra.comul a) using
            TensorProduct.induction_on with
          | zero => simp
          | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
          | tmul x y => simp,
      HopfAlgebra.mul_antipode_rTensor_comul_apply, AlgHom.commutes]
    rfl
  · apply WithConv.ext
    apply LinearMap.ext
    intro a
    rw [LinearMap.convMul_apply]
    change LinearMap.mul' F L (TensorProduct.map ν.toLinearMap
      (ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)) (Coalgebra.comul a)) = (1 : WithConv (A →ₗ[F] L)).ofConv a
    rw [show TensorProduct.map ν.toLinearMap (ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F))
        = TensorProduct.map ν.toLinearMap ν.toLinearMap ∘ₗ (HopfAlgebraStruct.antipode (R := F) (A := A)).lTensor A
        from by rw [LinearMap.lTensor, ← TensorProduct.map_comp, LinearMap.comp_id],
      LinearMap.comp_apply,
      show LinearMap.mul' F L (TensorProduct.map ν.toLinearMap ν.toLinearMap
          ((HopfAlgebraStruct.antipode (R := F) (A := A)).lTensor A (Coalgebra.comul a)))
        = ν (LinearMap.mul' F A ((HopfAlgebraStruct.antipode (R := F) (A := A)).lTensor A (Coalgebra.comul a)))
        from by
          induction (HopfAlgebraStruct.antipode (R := F) (A := A)).lTensor A (Coalgebra.comul a) using
            TensorProduct.induction_on with
          | zero => simp
          | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
          | tmul x y => simp,
      HopfAlgebra.mul_antipode_lTensor_comul_apply, AlgHom.commutes]
    rfl

theorem toLinearMap_pow_pred_eq_comp_antipode (ν : A →ₐ[F] L) (m : ℕ) (hm : 1 ≤ m)
    (h : (toConv ν) ^ m = 1) :
    ((toConv ν) ^ (m - 1)).ofConv.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F) (A := A) := by
  obtain ⟨hl, hr⟩ := toConv_comp_antipode_mul ν
  have hx : (toConv ν.toLinearMap) ^ m = 1 := by
    rw [← AlgHom.toLinearMap_convPow, h]; rfl
  have h1 : (toConv ν.toLinearMap) ^ (m - 1) * toConv ν.toLinearMap = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hm, hx]
  have h2 := left_inv_eq_right_inv h1 hr
  rw [← AlgHom.toLinearMap_convPow] at h2
  exact congrArg ofConv h2

end InversePoint

end StepOrder
end HopfAlgebra

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk ofAlgHom mul_antipode_lTensor_comul_apply mul_antipode_rTensor_comul_apply vanishingIdealOfPoints vanishingIdealOfPoints_antitone ptSet mem_ptSet_iff ofConv_mem_ptSet ptSet_mono pointQuot evalQuot evalQuot_tmul HopfKerHopf.coaction_repr HopfKerHopf.counit_coe HopfKerHopf.hopfKerVal coaction hopfKer evalQuot_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal natCard_algHom_eq_finrank_of_charZero toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one"
p2m_open "HopfAlgebra"
namespace StepOrder

set_option linter.unusedSectionVars false

section ImageOrder
variable {R₀ : Type*} [CommRing R₀] {R : Type*} [CommRing R] {F : Type*} [Field F]
  [Algebra R₀ R] [Algebra R₀ F] [Algebra R F] [IsScalarTower R₀ R F]
  {H : Type*} [CommRing H] [HopfAlgebra R₀ H] [Module.Finite R₀ H]
  {A' : Type*} [CommRing A'] [HopfAlgebra F A'] [Algebra R A'] [IsScalarTower R F A']
  [Algebra R₀ A'] [IsScalarTower R₀ F A'] [IsScalarTower R₀ R A']
  (ψ : F ⊗[R₀] H →ₐc[F] A')

noncomputable def imH : Subalgebra R₀ A' :=
  (((ψ : F ⊗[R₀] H →ₐ[F] A').restrictScalars R₀).comp
    (Algebra.TensorProduct.includeRight : H →ₐ[R₀] F ⊗[R₀] H)).range

theorem mem_imH (h : H) : ψ ((1 : F) ⊗ₜ[R₀] h) ∈ imH ψ := ⟨h, rfl⟩

variable (R) in

noncomputable def imOrder : Subalgebra R A' := Algebra.adjoin R (imH ψ : Set A')

theorem imH_subset_imOrder : (imH ψ : Set A') ⊆ imOrder R ψ := Algebra.subset_adjoin

theorem imOrder_toSubmodule : (imOrder R ψ).toSubmodule = Submodule.span R (imH ψ : Set A') := by
  rw [imOrder, Algebra.adjoin_eq_span]
  congr 1
  exact congrArg _ (Submonoid.closure_eq (imH ψ).toSubmonoid)

theorem mem_imOrder_iff (x : A') : x ∈ imOrder R ψ ↔ x ∈ Submodule.span R (imH ψ : Set A') := by
  rw [← imOrder_toSubmodule]; rfl

theorem finite_imOrder : Module.Finite R ↥(imOrder R ψ) := by
  obtain ⟨hfin, -, -, -⟩ :=
    HopfOrder.finite_and_comul_mem_and_antipode_mem_and_counit_mem_range_comp_includeRight (R := R₀) ψ
  change Module.Finite R₀ ↥(imH ψ) at hfin
  have hfg : (imH ψ).toSubmodule.FG := Module.Finite.iff_fg.mp hfin
  obtain ⟨t, ht⟩ := hfg
  have hfg' : (imOrder R ψ).toSubmodule.FG := by
    refine ⟨t, ?_⟩
    rw [imOrder_toSubmodule]
    have : (imH ψ : Set A') = (Submodule.span R₀ (t : Set A') : Set A') := by rw [ht]; rfl
    rw [this, Submodule.span_span_of_tower]
  have hF : Module.Finite R ↥(imOrder R ψ).toSubmodule := Module.Finite.iff_fg.mpr hfg'
  exact hF

theorem span_imOrder (hψ : Function.Surjective ψ) :
    Submodule.span F ((imOrder R ψ : Subalgebra R A') : Set A') = ⊤ := by
  rw [eq_top_iff]
  rintro a -
  obtain ⟨x, rfl⟩ := hψ a
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | tmul f h =>
    have : f ⊗ₜ[R₀] h = f • ((1 : F) ⊗ₜ[R₀] h) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Submodule.smul_mem _ f (Submodule.subset_span (imH_subset_imOrder ψ (mem_imH ψ h)))

theorem counit_mem_imOrder (x : A') (hx : x ∈ imOrder R ψ) :
    Coalgebra.counit (R := F) (A := A') x ∈ (algebraMap R F).range := by
  obtain ⟨-, -, -, hcounit⟩ :=
    HopfOrder.finite_and_comul_mem_and_antipode_mem_and_counit_mem_range_comp_includeRight (R := R₀) ψ
  rw [mem_imOrder_iff] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, hr⟩ := hcounit y hy
    exact ⟨algebraMap R₀ R r, by rw [← IsScalarTower.algebraMap_apply]; exact hr⟩
  | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha⟩ := hy; obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
  | smul r y _ hy =>
    obtain ⟨a, ha⟩ := hy
    refine ⟨r * a, ?_⟩
    rw [map_mul, ha, ← IsScalarTower.algebraMap_smul F r y, map_smul, smul_eq_mul]

theorem antipode_mem_imOrder (x : A') (hx : x ∈ imOrder R ψ) :
    HopfAlgebra.antipode F (A := A') x ∈ imOrder R ψ := by
  obtain ⟨-, -, hanti, -⟩ :=
    HopfOrder.finite_and_comul_mem_and_antipode_mem_and_counit_mem_range_comp_includeRight (R := R₀) ψ
  rw [mem_imOrder_iff] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span (hanti y hy)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
    rw [← IsScalarTower.algebraMap_smul F r y, map_smul, IsScalarTower.algebraMap_smul]
    exact Submodule.smul_mem _ r hy

theorem comul_mem_imOrder (x : A') (hx : x ∈ imOrder R ψ) :
    Coalgebra.comul (R := F) x ∈
      (Algebra.TensorProduct.productMap
        (((Algebra.TensorProduct.includeLeft : A' →ₐ[F] A' ⊗[F] A').restrictScalars R).comp (imOrder R ψ).val)
        (((Algebra.TensorProduct.includeRight : A' →ₐ[F] A' ⊗[F] A').restrictScalars R).comp (imOrder R ψ).val)).range := by
  obtain ⟨-, hcomul, -, -⟩ :=
    HopfOrder.finite_and_comul_mem_and_antipode_mem_and_counit_mem_range_comp_includeRight (R := R₀) ψ
  set P := Algebra.TensorProduct.productMap
        (((Algebra.TensorProduct.includeLeft : A' →ₐ[F] A' ⊗[F] A').restrictScalars R).comp (imOrder R ψ).val)
        (((Algebra.TensorProduct.includeRight : A' →ₐ[F] A' ⊗[F] A').restrictScalars R).comp (imOrder R ψ).val)
    with hP

  have hsub : ∀ z : ↥(imH ψ) ⊗[R₀] ↥(imH ψ),
      Algebra.TensorProduct.productMap
        (((Algebra.TensorProduct.includeLeft : A' →ₐ[F] A' ⊗[F] A').restrictScalars R₀).comp (imH ψ).val)
        (((Algebra.TensorProduct.includeRight : A' →ₐ[F] A' ⊗[F] A').restrictScalars R₀).comp (imH ψ).val) z
        ∈ P.range := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Subalgebra.zero_mem _
    | add x y hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
    | tmul s t =>
      rw [AlgHom.mem_range]
      refine ⟨(⟨(s : A'), imH_subset_imOrder ψ s.2⟩ : ↥(imOrder R ψ)) ⊗ₜ[R]
        (⟨(t : A'), imH_subset_imOrder ψ t.2⟩ : ↥(imOrder R ψ)), ?_⟩
      rw [hP, Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.productMap_apply_tmul]
      rfl
  rw [mem_imOrder_iff] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz⟩ := hcomul y hy
    rw [← hz]
    exact hsub z
  | zero => rw [map_zero]; exact Subalgebra.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Subalgebra.add_mem _ hy hz
  | smul r y _ hy =>
    rw [← IsScalarTower.algebraMap_smul F r y, map_smul, IsScalarTower.algebraMap_smul]
    exact Subalgebra.smul_mem _ hy r

end ImageOrder

end StepOrder
end HopfAlgebra

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk ofAlgHom mul_antipode_lTensor_comul_apply mul_antipode_rTensor_comul_apply vanishingIdealOfPoints vanishingIdealOfPoints_antitone ptSet mem_ptSet_iff ofConv_mem_ptSet ptSet_mono pointQuot evalQuot evalQuot_tmul HopfKerHopf.coaction_repr HopfKerHopf.counit_coe HopfKerHopf.hopfKerVal coaction hopfKer evalQuot_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal natCard_algHom_eq_finrank_of_charZero toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one"
p2m_open "HopfAlgebra"
namespace StepOrder

open WithConv

section EvalLemmas
variable {F : Type*} [Field F] {C : Type*} [CommRing C] [Algebra F C] {L : Type*} [Field L] [Algebra F L]

theorem eval_tmul (c : L) (a : C) (ν : WithConv (C →ₐ[F] L)) :
    (Algebra.TensorProduct.lift (Algebra.ofId L (WithConv (C →ₐ[F] L) → L))
        (Pi.algHom F _ fun ν : WithConv (C →ₐ[F] L) => (WithConv.ofConv ν : C →ₐ[F] L))
        (fun _ _ => Commute.all _ _) : L ⊗[F] C →ₐ[L] (WithConv (C →ₐ[F] L) → L)) (c ⊗ₜ[F] a) ν = c * ν.ofConv a := by
  rw [Algebra.TensorProduct.lift_tmul, Pi.mul_apply, Pi.algHom_apply, Algebra.ofId_apply, Pi.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply]

end EvalLemmas

section QuotEval
variable {F : Type*} [Field F] {A₀ : Type*} [CommRing A₀] [Bialgebra F A₀]
  {L : Type*} [Field L] [Algebra F L]
  (S : Submonoid (WithConv (A₀ →ₐ[F] L)))
  {A' : Type*} [CommRing A'] [Bialgebra F A']
  (π : A₀ →ₐc[F] A') (hπ : Function.Surjective π)
  (hker : ∀ a, π a = 0 ↔ a ∈ vanishingIdealOfPoints (ptSet S))

include hker in
theorem ker_eq : RingHom.ker (π : A₀ →ₐ[F] A') = vanishingIdealOfPoints (ptSet S) :=
  Ideal.ext fun a => hker a

noncomputable def quotEquiv (π : A₀ →ₐc[F] A') (hπ : Function.Surjective π)
    (hker : ∀ a, π a = 0 ↔ a ∈ vanishingIdealOfPoints (ptSet S)) : A' ≃ₐ[F] pointQuot S :=
  (Ideal.quotientKerAlgEquivOfSurjective (f := (π : A₀ →ₐ[F] A')) hπ).symm.trans
    (Ideal.quotientEquivAlgOfEq F (ker_eq S π hker))

theorem quotEquiv_apply (a : A₀) : quotEquiv S π hπ hker (π a) = Ideal.Quotient.mk _ a := by
  have h1 : (Ideal.quotientKerAlgEquivOfSurjective (f := (π : A₀ →ₐ[F] A')) hπ).symm (π a)
      = Ideal.Quotient.mk (RingHom.ker (π : A₀ →ₐ[F] A')) a := by
    rw [AlgEquiv.symm_apply_eq, Ideal.quotientKerAlgEquivOfSurjective_mk]
    rfl
  rw [quotEquiv, AlgEquiv.trans_apply, h1]
  rfl

include hπ hker in

theorem bijective_eval_quot [Finite ↥S] (hbij : Function.Bijective (evalQuot S)) :
    Function.Bijective (Algebra.TensorProduct.lift (Algebra.ofId L (WithConv (A' →ₐ[F] L) → L))
        (Pi.algHom F _ fun ν : WithConv (A' →ₐ[F] L) => (WithConv.ofConv ν : A' →ₐ[F] L))
        (fun _ _ => Commute.all _ _) : L ⊗[F] A' →ₐ[L] (WithConv (A' →ₐ[F] L) → L)) := by
  classical
  set ev' := (Algebra.TensorProduct.lift (Algebra.ofId L (WithConv (A' →ₐ[F] L) → L))
        (Pi.algHom F _ fun ν : WithConv (A' →ₐ[F] L) => (WithConv.ofConv ν : A' →ₐ[F] L))
        (fun _ _ => Commute.all _ _) : L ⊗[F] A' →ₐ[L] (WithConv (A' →ₐ[F] L) → L)) with hev'
  let θ := quotEquiv S π hπ hker
  let κ : L ⊗[F] A' ≃ₐ[L] L ⊗[F] pointQuot S := Algebra.TensorProduct.congr AlgEquiv.refl θ
  let e : ↥S ≃ WithConv (A' →ₐ[F] L) :=
    Equiv.ofBijective (fun s => toConv (pt S π hπ hker s))
      ⟨fun s t h => pt_injective S π hπ hker (WithConv.toConv_injective h),
       fun ν => by obtain ⟨s, hs⟩ := pt_surjective S π hπ hker hbij ν.ofConv; exact ⟨s, congrArg toConv hs⟩⟩
  let ρ : (↥S → L) → (WithConv (A' →ₐ[F] L) → L) := fun g ν => g (e.symm ν)
  have hρ : Function.Bijective ρ := (Equiv.piCongrLeft' (fun _ : ↥S => L) e).bijective
  have hfac : ∀ x, ev' x = ρ (evalQuot S (κ x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]; rfl
    | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy]; rfl
    | tmul c a' =>
      obtain ⟨a, rfl⟩ := hπ a'
      funext ν
      obtain ⟨s, rfl⟩ := e.surjective ν
      rw [hev', eval_tmul]
      change c * (pt S π hπ hker s) (π a) = evalQuot S (κ (c ⊗ₜ[F] π a)) (e.symm (e s))
      rw [Equiv.symm_apply_apply, pt_apply]
      have hκ : κ (c ⊗ₜ[F] π a) = c ⊗ₜ[F] θ (π a) := Algebra.TensorProduct.congr_apply _ _ _
      rw [hκ]
      change _ = evalQuot S (c ⊗ₜ[F] quotEquiv S π hπ hker (π a)) s
      rw [quotEquiv_apply, evalQuot_tmul]
  have : ⇑ev' = ρ ∘ evalQuot S ∘ κ := funext hfac
  rw [this]
  exact hρ.comp (hbij.comp κ.bijective)

end QuotEval

section KernelEval
variable {F : Type*} [Field F] {A' : Type*} [CommRing A'] [Bialgebra F A']
  {A : Type*} [CommRing A] [Bialgebra F A] (ρ : A' →ₐc[F] A)
  {L : Type*} [Field L] [Algebra F L]

theorem bijective_eval_hopfKer [Module.Finite F A'] [Finite (WithConv (↥(hopfKer ρ) →ₐ[F] L))]
    (hinj' : Function.Injective (Algebra.TensorProduct.lift (Algebra.ofId L (WithConv (A' →ₐ[F] L) → L))
        (Pi.algHom F _ fun ν : WithConv (A' →ₐ[F] L) => (WithConv.ofConv ν : A' →ₐ[F] L))
        (fun _ _ => Commute.all _ _) : L ⊗[F] A' →ₐ[L] (WithConv (A' →ₐ[F] L) → L)))
    (hcard : Nat.card (WithConv (↥(hopfKer ρ) →ₐ[F] L)) = Module.finrank F ↥(hopfKer ρ)) :
    Function.Bijective (Algebra.TensorProduct.lift (Algebra.ofId L (WithConv (↥(hopfKer ρ) →ₐ[F] L) → L))
        (Pi.algHom F _ fun ν : WithConv (↥(hopfKer ρ) →ₐ[F] L) => (WithConv.ofConv ν : ↥(hopfKer ρ) →ₐ[F] L))
        (fun _ _ => Commute.all _ _) : L ⊗[F] ↥(hopfKer ρ) →ₐ[L] (WithConv (↥(hopfKer ρ) →ₐ[F] L) → L)) := by
  classical
  set ev' := (Algebra.TensorProduct.lift (Algebra.ofId L (WithConv (A' →ₐ[F] L) → L))
        (Pi.algHom F _ fun ν : WithConv (A' →ₐ[F] L) => (WithConv.ofConv ν : A' →ₐ[F] L))
        (fun _ _ => Commute.all _ _) : L ⊗[F] A' →ₐ[L] (WithConv (A' →ₐ[F] L) → L)) with hev'
  set ev₁ := (Algebra.TensorProduct.lift (Algebra.ofId L (WithConv (↥(hopfKer ρ) →ₐ[F] L) → L))
        (Pi.algHom F _ fun ν : WithConv (↥(hopfKer ρ) →ₐ[F] L) => (WithConv.ofConv ν : ↥(hopfKer ρ) →ₐ[F] L))
        (fun _ _ => Commute.all _ _) : L ⊗[F] ↥(hopfKer ρ) →ₐ[L] (WithConv (↥(hopfKer ρ) →ₐ[F] L) → L)) with hev₁
  let ι : L ⊗[F] ↥(hopfKer ρ) →ₐ[L] L ⊗[F] A' := Algebra.TensorProduct.map (AlgHom.id L L) (hopfKer ρ).val
  have hι : Function.Injective ι := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := L) ((hopfKer ρ).val.toLinearMap)
      Subtype.val_injective
    intro x y hxy
    apply h
    change ι x = ι y
    exact hxy
  have key : ∀ (x : L ⊗[F] ↥(hopfKer ρ)) (ν : WithConv (A' →ₐ[F] L)),
      ev' (ι x) ν = ev₁ x (toConv ((ν.ofConv).comp (hopfKer ρ).val)) := by
    intro x ν
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]; rfl
    | add x y hx hy => rw [map_add, map_add, map_add, Pi.add_apply, Pi.add_apply, hx, hy]
    | tmul c a =>
      rw [show ι (c ⊗ₜ[F] a) = c ⊗ₜ[F] (a : A') from by
        rw [Algebra.TensorProduct.map_tmul]; rfl, hev', eval_tmul, hev₁, eval_tmul]
      rfl
  have hinj : Function.Injective ev₁ := by
    intro x y hxy
    apply hι
    apply hinj'
    funext ν
    rw [key, key, hxy]
  refine ⟨hinj, ?_⟩

  haveI : Fintype (WithConv (↥(hopfKer ρ) →ₐ[F] L)) := Fintype.ofFinite _
  have hdim : Module.finrank L (L ⊗[F] ↥(hopfKer ρ)) = Module.finrank L (WithConv (↥(hopfKer ρ) →ₐ[F] L) → L) := by
    rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, hcard]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := ev₁.toLinearMap)).mp hinj

end KernelEval

end StepOrder
end HopfAlgebra

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk ofAlgHom mul_antipode_lTensor_comul_apply mul_antipode_rTensor_comul_apply vanishingIdealOfPoints vanishingIdealOfPoints_antitone ptSet mem_ptSet_iff ofConv_mem_ptSet ptSet_mono pointQuot evalQuot evalQuot_tmul HopfKerHopf.coaction_repr HopfKerHopf.counit_coe HopfKerHopf.hopfKerVal coaction hopfKer evalQuot_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal natCard_algHom_eq_finrank_of_charZero toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one"
namespace StepOrder
p2m_open "HopfAlgebra"

open Coalgebra WithConv
p2m_open_scoped "TensorProduct Coalgebra.TensorProduct"

section KerPts
variable {F : Type*} [CommRing F] {A' : Type*} [CommRing A'] [HopfAlgebra F A'] {A : Type*} [CommRing A]
  [HopfAlgebra F A] (ρ : A' →ₐc[F] A)

theorem map_eq_algebraMap_counit_of_mem_hopfKer {a : A'} (ha : a ∈ HopfAlgebra.hopfKer ρ) :
    ρ a = algebraMap F A (Coalgebra.counit (R := F) a) := by
  have h1 : HopfAlgebra.coaction ρ a = a ⊗ₜ[F] 1 := ha
  rw [HopfAlgebra.HopfKerHopf.coaction_repr ρ (ℛ F a)] at h1
  have h2 := congrArg (fun z => TensorProduct.lid F A
    ((Coalgebra.counit (R := F) (A := A')).rTensor A z)) h1
  simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul] at h2

  rw [Algebra.algebraMap_eq_smul_one, ← h2]
  conv_lhs => rw [← sum_counit_smul (ℛ F a)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]

variable {L : Type*} [CommRing L] [Algebra F L]

theorem toConv_comp_comp_hopfKer_val_eq_one [Coalgebra.IsCocomm F A'] [Module.Flat F A'] [Module.Flat F A]
    [Module.Flat F ↥(HopfAlgebra.hopfKer ρ)] (χ : A →ₐ[F] L) :
    WithConv.toConv ((χ.comp (ρ : A' →ₐ[F] A)).comp (HopfAlgebra.hopfKer ρ).val)
      = (1 : WithConv (↥(HopfAlgebra.hopfKer ρ) →ₐ[F] L)) := by
  rw [AlgHom.convOne_def]
  congr 1
  apply AlgHom.ext
  intro s
  simp only [AlgHom.coe_comp, Function.comp_apply, Subalgebra.coe_val, Bialgebra.counitAlgHom_apply,
    HopfAlgebra.HopfKerHopf.counit_coe]
  change χ (ρ (s : A')) = algebraMap F L (Coalgebra.counit (R := F) (s : A'))
  rw [map_eq_algebraMap_counit_of_mem_hopfKer ρ s.2, AlgHom.commutes]

theorem comp_hopfKer_val_mul_toConv_comp [Coalgebra.IsCocomm F A'] [Module.Flat F A'] [Module.Flat F A]
    [Module.Flat F ↥(HopfAlgebra.hopfKer ρ)] (ν : WithConv (A' →ₐ[F] L)) (χ : A →ₐ[F] L) :
    (WithConv.ofConv (ν * WithConv.toConv (χ.comp (ρ : A' →ₐ[F] A)))).comp (HopfAlgebra.hopfKer ρ).val
      = (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer ρ).val := by
  have h := AlgHom.convMul_comp_bialgHom_distrib ν (WithConv.toConv (χ.comp (ρ : A' →ₐ[F] A)))
    (HopfAlgebra.HopfKerHopf.hopfKerVal ρ)

  have hval : ((HopfAlgebra.HopfKerHopf.hopfKerVal ρ : ↥(HopfAlgebra.hopfKer ρ) →ₐc[F] A') :
      ↥(HopfAlgebra.hopfKer ρ) →ₐ[F] A') = (HopfAlgebra.hopfKer ρ).val := by
    apply AlgHom.ext; intro s; rfl
  rw [hval] at h
  rw [toConv_comp_comp_hopfKer_val_eq_one ρ χ, mul_one] at h
  exact h

end KerPts

section KerFinite
variable {F : Type*} [Field F] {A' : Type*} [CommRing A'] [HopfAlgebra F A'] [Module.Finite F A']
  {A : Type*} [CommRing A] [HopfAlgebra F A] (ρ : A' →ₐc[F] A)

theorem finite_hopfKer : Module.Finite F ↥(HopfAlgebra.hopfKer ρ) :=
  Module.Finite.of_injective (HopfAlgebra.hopfKer ρ).val.toLinearMap Subtype.val_injective

omit [Field F] [CommRing A'] [HopfAlgebra F A'] [Module.Finite F A'] [CommRing A] [HopfAlgebra F A] in

theorem natCard_withConv (X : Type*) : Nat.card (WithConv X) = Nat.card X :=
  Nat.card_congr ⟨WithConv.ofConv, WithConv.toConv, fun _ => rfl, fun _ => rfl⟩

end KerFinite

end HopfAlgebra.StepOrder

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk ofAlgHom mul_antipode_lTensor_comul_apply mul_antipode_rTensor_comul_apply vanishingIdealOfPoints vanishingIdealOfPoints_antitone ptSet mem_ptSet_iff ofConv_mem_ptSet ptSet_mono pointQuot evalQuot evalQuot_tmul HopfKerHopf.coaction_repr HopfKerHopf.counit_coe HopfKerHopf.hopfKerVal coaction hopfKer evalQuot_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal natCard_algHom_eq_finrank_of_charZero toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one"
namespace StepOrder
p2m_open "HopfAlgebra"

open scoped TensorProduct

theorem isCocomm_hopfAlgebraOfFinite
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    [Coalgebra.IsCocomm K A]
    (S : Subalgebra R A) [Module.Finite R ↥S]
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range) :
    letI := HopfOrder.hopfAlgebraOfFinite S hcomul hcounit hanti
    Coalgebra.IsCocomm R ↥S := by
  letI := HopfOrder.hopfAlgebraOfFinite S hcomul hcounit hanti
  haveI := HopfOrder.moduleFlat_of_finite (K := K) S
  have hcomm : ∀ z : ↥S ⊗[R] ↥S, HopfOrder.tensorSqHom (K := K) S (TensorProduct.comm R ↥S ↥S z)
      = TensorProduct.comm K A A (HopfOrder.tensorSqHom (K := K) S z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [TensorProduct.comm_tmul, HopfOrder.tensorSqHom_tmul, HopfOrder.tensorSqHom_tmul,
        TensorProduct.comm_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨?_⟩
  apply LinearMap.ext
  intro t
  apply HopfOrder.tensorSqHom_injective (K := K) S
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hcomm]
  change TensorProduct.comm K A A (HopfOrder.tensorSqHom (K := K) S (HopfOrder.comulS hcomul t))
    = HopfOrder.tensorSqHom (K := K) S (HopfOrder.comulS hcomul t)
  rw [HopfOrder.tensorSqHom_comulS]
  exact Coalgebra.comm_comul (R := K) (t : A)

end HopfAlgebra.StepOrder

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk ofAlgHom mul_antipode_lTensor_comul_apply mul_antipode_rTensor_comul_apply vanishingIdealOfPoints vanishingIdealOfPoints_antitone ptSet mem_ptSet_iff ofConv_mem_ptSet ptSet_mono pointQuot evalQuot evalQuot_tmul HopfKerHopf.coaction_repr HopfKerHopf.counit_coe HopfKerHopf.hopfKerVal coaction hopfKer evalQuot_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal natCard_algHom_eq_finrank_of_charZero toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one"
p2m_open "HopfAlgebra"
namespace StepOrder
open WithConv

section Helpers
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {A : Type*} [CommRing A] [Algebra K A]
  {ι : Type*} (pt : ι → (A →ₐ[K] L))

theorem eq_of_forall_pt_apply_eq
    (hinj : Function.Injective
      (Algebra.TensorProduct.lift (Algebra.ofId L (ι → L)) (Pi.algHom K _ fun i : ι => pt i)
        (fun _ _ => Commute.all _ _) : L ⊗[K] A →ₐ[L] (ι → L)))
    {a a' : A} (h : ∀ i, pt i a = pt i a') : a = a' := by
  have hinc : Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective
  apply hinc
  apply hinj
  simp only [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  funext i
  exact h i

end Helpers

section PtPow
variable {F : Type*} [Field F] {A₀ : Type*} [CommRing A₀] [Bialgebra F A₀]
  {L : Type*} [Field L] [Algebra F L] (S : Submonoid (WithConv (A₀ →ₐ[F] L)))
  {A' : Type*} [CommRing A'] [Bialgebra F A'] (π : A₀ →ₐc[F] A') (hπ : Function.Surjective π)
  (hker : ∀ a, π a = 0 ↔ a ∈ vanishingIdealOfPoints (ptSet S))

theorem toConv_pt_pow (s : ↥S) (n : ℕ) :
    (toConv (pt S π hπ hker s)) ^ n = toConv (pt S π hπ hker (s ^ n)) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pt_one]
  | succ n ih => rw [pow_succ, pow_succ, ih, toConv_pt_mul]

end PtPow

end StepOrder
end HopfAlgebra

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk ofAlgHom mul_antipode_lTensor_comul_apply mul_antipode_rTensor_comul_apply vanishingIdealOfPoints vanishingIdealOfPoints_antitone ptSet mem_ptSet_iff ofConv_mem_ptSet ptSet_mono pointQuot evalQuot evalQuot_tmul HopfKerHopf.coaction_repr HopfKerHopf.counit_coe HopfKerHopf.hopfKerVal coaction hopfKer evalQuot_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal natCard_algHom_eq_finrank_of_charZero toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one"
p2m_open "HopfAlgebra"
namespace StepOrder
open WithConv

section Transported
variable {M : Type*} [Monoid M]
  {F : Type*} [Field F] {A₀ : Type*} [CommRing A₀] [HopfAlgebra F A₀]
  {L : Type*} [Field L] [Algebra F L]
  (ε : M ≃* WithConv (A₀ →ₐ[F] L))

noncomputable def KA (S : Submonoid M) : Submonoid (WithConv (A₀ →ₐ[F] L)) :=
  S.map ε.toMonoidHom

theorem mem_KA_iff (S : Submonoid M) (ν : WithConv (A₀ →ₐ[F] L)) :
    ν ∈ KA ε S ↔ ε.symm ν ∈ S := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    change ε.symm (ε f) ∈ S
    rwa [MulEquiv.symm_apply_apply]
  · intro h
    exact ⟨_, h, ε.apply_symm_apply ν⟩

theorem apply_mem_KA_iff (S : Submonoid M) (f : M) :
    ε f ∈ KA ε S ↔ f ∈ S := by
  rw [mem_KA_iff, MulEquiv.symm_apply_apply]

theorem KA_mono {S T : Submonoid M} (h : S ≤ T) : KA ε S ≤ KA ε T := by
  rintro ν ⟨f, hf, rfl⟩
  exact ⟨f, h hf, rfl⟩

theorem inv_KA {p : ℕ} (hp : p.Prime) (hMp : ∀ f : M, f ^ p = 1)
    (S : Submonoid M) :
    ∀ ν ∈ ptSet (KA ε S), ∃ ν' ∈ ptSet (KA ε S),
      ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F) := by
  intro ν hν
  rw [mem_ptSet_iff] at hν
  have hpow : (toConv ν) ^ p = 1 := by
    obtain ⟨f, -, hf⟩ := hν
    rw [← hf]
    change (ε f) ^ p = 1
    rw [← map_pow, hMp, map_one]
  refine ⟨((toConv ν) ^ (p - 1)).ofConv, ?_, toLinearMap_pow_pred_eq_comp_antipode ν p hp.one_lt.le hpow⟩
  rw [mem_ptSet_iff, toConv_ofConv]
  exact pow_mem hν (p - 1)

end Transported

end StepOrder
end HopfAlgebra

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk ofAlgHom mul_antipode_lTensor_comul_apply mul_antipode_rTensor_comul_apply vanishingIdealOfPoints vanishingIdealOfPoints_antitone ptSet mem_ptSet_iff ofConv_mem_ptSet ptSet_mono pointQuot evalQuot evalQuot_tmul HopfKerHopf.coaction_repr HopfKerHopf.counit_coe HopfKerHopf.hopfKerVal coaction hopfKer evalQuot_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal natCard_algHom_eq_finrank_of_charZero toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one"
p2m_open "HopfAlgebra"
namespace StepOrder

open WithConv

set_option maxHeartbeats 4800000 in

theorem order_package
    {R₀ : Type} [CommRing R₀] {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {F : Type} [Field F] [CharZero F] [Algebra R₀ F] [Algebra R F] [IsFractionRing R F]
    [Algebra R₀ R] [IsScalarTower R₀ R F]
    {H : Type} [CommRing H] [HopfAlgebra R₀ H] [Module.Finite R₀ H]
    {A' : Type} [CommRing A'] [HopfAlgebra F A'] [Coalgebra.IsCocomm F A'] [Module.Finite F A']
    [Algebra R A'] [IsScalarTower R F A'] [Algebra R₀ A'] [IsScalarTower R₀ F A'] [IsScalarTower R₀ R A']
    {A : Type} [CommRing A] [HopfAlgebra F A] [Module.Finite F A] [Algebra R A] [IsScalarTower R F A]
    {L : Type} [CommRing L] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
    (Psub : Subalgebra R L) (hPsub : ∀ x : L, IsIntegral R x → x ∈ Psub)
    (ψ : F ⊗[R₀] H →ₐc[F] A') (hψ : Function.Surjective ψ)
    (ρ : A' →ₐc[F] A) (hρ : Function.Surjective ρ)
    {p s nK : ℕ} (hnK : 0 < nK) (hdimA' : Module.finrank F A' = p ^ s * nK) (hdimA : Module.finrank F A = nK)
    (hA₁p : (toConv (AlgHom.id F ↥(HopfAlgebra.hopfKer ρ))) ^ p = 1) :
    ∃ (B : Type) (_ : CommRing B) (_ : HopfAlgebra R B) (_ : Module.Finite R B) (_ : Module.Free R B)
      (_ : Coalgebra.IsCocomm R B),
      Module.finrank R B = p ^ s ∧ Module.finrank F ↥(HopfAlgebra.hopfKer ρ) = p ^ s ∧
      (∀ (T : Type) [CommRing T] [Algebra R T] (f : WithConv (B →ₐ[R] T)), f ^ p ^ 1 = 1) ∧
      ∃ (e : ↥(HopfAlgebra.hopfKer ρ) ≃ₐc[F] F ⊗[R] B) (ι : B → ↥(HopfAlgebra.hopfKer ρ))
        (e₁ : (↥(HopfAlgebra.hopfKer ρ) →ₐ[F] L) ≃ (B →ₐ[R] ↥Psub)),
        (∀ b : B, e.symm ((1 : F) ⊗ₜ[R] b) = ι b) ∧
        (∀ (f : ↥(HopfAlgebra.hopfKer ρ) →ₐ[F] L) (x : B), ((e₁ f x : ↥Psub) : L) = f (ι x)) ∧
        (∀ f g : ↥(HopfAlgebra.hopfKer ρ) →ₐ[F] L,
          toConv (e₁ (ofConv (toConv f * toConv g))) = toConv (e₁ f) * toConv (e₁ g)) ∧
        toConv (e₁ (ofConv (1 : WithConv (↥(HopfAlgebra.hopfKer ρ) →ₐ[F] L)))) = 1 := by
  classical
  haveI := finite_hopfKer ρ

  let S' : Subalgebra R A' := imOrder R ψ
  have hS'fin : Module.Finite R ↥S' := finite_imOrder ψ
  have hS'span : Submodule.span F ((S' : Subalgebra R A') : Set A') = ⊤ := span_imOrder ψ hψ
  have hS'comul := comul_mem_imOrder (R := R) ψ
  have hS'anti := antipode_mem_imOrder (R := R) ψ
  have hS'counit := counit_mem_imOrder (R := R) ψ
  obtain ⟨hBfin, hBspan, hBcomul, hBanti, hBcounit⟩ :=
    HopfOrder.isHopfOrder_comap_hopfKer S' hS'fin hS'span hS'comul hS'anti hS'counit ρ
  set B₀ : Subalgebra R ↥(hopfKer ρ) :=
    S'.comap (((hopfKer ρ).val : ↥(hopfKer ρ) →ₐ[F] A').restrictScalars R) with hB₀
  haveI hBfinI := hBfin
  letI instB := HopfOrder.hopfAlgebraOfFinite B₀ hBcomul hBcounit hBanti
  haveI hBfree := HopfOrder.moduleFree_of_finite (K := F) B₀
  haveI hBcoc := isCocomm_hopfAlgebraOfFinite B₀ hBcomul hBanti hBcounit

  obtain ⟨hMfin, hMspan, -, -, -⟩ :=
    HopfOrder.isHopfOrder_map S' hS'fin hS'span hS'comul hS'anti hS'counit ρ hρ
  have hrk := HopfOrder.finrank_eq_finrank_comap_hopfKer_mul_finrank_map S' hS'fin hS'span hS'comul hS'anti
    hS'counit ρ hρ
  rw [HopfOrder.finrank_eq_finrank S' hS'fin hS'span, HopfOrder.finrank_eq_finrank _ hMfin hMspan,
    hdimA', hdimA] at hrk
  have hrank : Module.finrank R ↥B₀ = p ^ s := (Nat.eq_of_mul_eq_mul_right hnK hrk).symm

  let e₀ : F ⊗[R] ↥B₀ ≃ₐc[F] ↥(hopfKer ρ) := HopfOrder.baseChangeBialgEquivOfFinite B₀ hBspan hBcomul hBcounit
  have hFBp : (toConv (AlgHom.id F (F ⊗[R] ↥B₀))) ^ p = 1 :=
    toConv_id_pow_eq_one_of_injective e₀.toBialgHom e₀.injective p hA₁p
  haveI hBflat := HopfOrder.moduleFlat_of_finite (K := F) B₀
  have hincl : Function.Injective (Algebra.TensorProduct.includeRight : ↥B₀ →ₐ[R] F ⊗[R] ↥B₀) :=
    Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R F)
  have hBp : (toConv (AlgHom.id R ↥B₀)) ^ p = 1 := toConv_id_pow_eq_one_of_baseChange hincl p hFBp
  have hBkill : ∀ (T : Type) [CommRing T] [Algebra R T] (f : WithConv (↥B₀ →ₐ[R] T)), f ^ p ^ 1 = 1 := by
    intro T _ _ f
    rw [pow_one]
    exact (HopfAlgebra.forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one (H := ↥B₀) p).mpr hBp T f

  obtain ⟨e₁, he₁val, he₁mul, he₁one⟩ :=
    HopfOrder.exists_equiv_algHom_apply_eq_and_toConv_mul (R := R) (K := F) (A := ↥(hopfKer ρ))
      B₀ hBspan hBcomul hBanti hBcounit (L := L) Psub hPsub
  have hrankF : Module.finrank F ↥(hopfKer ρ) = p ^ s :=
    (HopfOrder.finrank_eq_finrank B₀ hBfin hBspan).symm.trans hrank
  refine ⟨↥B₀, inferInstance, instB, hBfinI, hBfree, hBcoc, hrank, hrankF, hBkill, e₀.symm, fun b => (b : ↥(hopfKer ρ)), e₁,
    fun b => ?_, he₁val, he₁mul, he₁one⟩
  change e₀ ((1 : F) ⊗ₜ[R] b) = (b : ↥(hopfKer ρ))
  change (1 : F) • (b : ↥(hopfKer ρ)) = (b : ↥(hopfKer ρ))
  rw [one_smul]

end StepOrder
end HopfAlgebra

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk ofAlgHom mul_antipode_lTensor_comul_apply mul_antipode_rTensor_comul_apply vanishingIdealOfPoints vanishingIdealOfPoints_antitone ptSet mem_ptSet_iff ofConv_mem_ptSet ptSet_mono pointQuot evalQuot evalQuot_tmul HopfKerHopf.coaction_repr HopfKerHopf.counit_coe HopfKerHopf.hopfKerVal coaction hopfKer evalQuot_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal natCard_algHom_eq_finrank_of_charZero toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one"
p2m_open "HopfAlgebra"
namespace StepOrder

open WithConv

set_option maxHeartbeats 6400000 in

theorem points_package
    {F : Type} [Field F] [CharZero F] {L : Type} [Field L] [Algebra F L] [IsAlgClosed L] [CharZero L]
    {A₀ : Type} [CommRing A₀] [HopfAlgebra F A₀]
    {M : Type} [Monoid M] [Finite M] (ε : M ≃* WithConv (A₀ →ₐ[F] L))
    (K K' : Submonoid M) (hKK' : K ≤ K')
    {A' : Type} [CommRing A'] [HopfAlgebra F A'] [Coalgebra.IsCocomm F A'] [Module.Finite F A']
    (π' : A₀ →ₐc[F] A') (hπ' : Function.Surjective π')
    (hker' : ∀ a, π' a = 0 ↔ a ∈ vanishingIdealOfPoints (ptSet (KA ε K')))
    (hbij' : Function.Bijective (evalQuot (KA ε K')))
    {A : Type} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
    (πK : A₀ →ₐc[F] A) (hπK : Function.Surjective πK)
    (hkerK : ∀ a, πK a = 0 ↔ a ∈ vanishingIdealOfPoints (ptSet (KA ε K)))
    (hbijK : Function.Bijective (evalQuot (KA ε K)))
    (hk : ∀ a, π' a = 0 → πK a = 0)
    {p : ℕ} (hMp : ∀ f : M, f ^ p = 1) :
    ∃ (r : M → WithConv (↥(hopfKer (quotBialgHom π' hπ' πK hk)) →ₐ[F] L))
      (_ : Finite (WithConv (↥(hopfKer (quotBialgHom π' hπ' πK hk)) →ₐ[F] L))),
      (∀ f ∈ K', ∀ g ∈ K', r (f * g) = r f * r g) ∧
      (∀ f ∈ K', ∀ g ∈ K', (r f = r g ↔ ∃ k ∈ K, g = f * k)) ∧
      (∀ f ∈ K', (r f = 1 ↔ f ∈ K)) ∧
      (∀ ν : WithConv (↥(hopfKer (quotBialgHom π' hπ' πK hk)) →ₐ[F] L), ∃ f ∈ K', r f = ν) ∧
      (∀ (τ : L →ₐ[F] L), ∀ f ∈ K', ∀ g ∈ K', ε g = toConv (τ.comp (ε f).ofConv) →
        ∀ a : ↥(hopfKer (quotBialgHom π' hπ' πK hk)), r g a = τ (r f a)) ∧
      Function.Bijective (Algebra.TensorProduct.lift (Algebra.ofId L (WithConv (↥(hopfKer (quotBialgHom π' hπ' πK hk)) →ₐ[F] L) → L))
        (Pi.algHom F _ fun ν : WithConv (↥(hopfKer (quotBialgHom π' hπ' πK hk)) →ₐ[F] L) => (WithConv.ofConv ν : ↥(hopfKer (quotBialgHom π' hπ' πK hk)) →ₐ[F] L))
        (fun _ _ => Commute.all _ _) : L ⊗[F] ↥(hopfKer (quotBialgHom π' hπ' πK hk)) →ₐ[L] (WithConv (↥(hopfKer (quotBialgHom π' hπ' πK hk)) →ₐ[F] L) → L)) ∧
      Nat.card (WithConv (↥(hopfKer (quotBialgHom π' hπ' πK hk)) →ₐ[F] L))
        = Module.finrank F ↥(hopfKer (quotBialgHom π' hπ' πK hk)) ∧
      Module.finrank F A' = Nat.card ↥K' ∧ Module.finrank F A = Nat.card ↥K ∧ 0 < Nat.card ↥K ∧
      (toConv (AlgHom.id F A')) ^ p = 1 := by
  classical
  haveI : Finite (WithConv (A₀ →ₐ[F] L)) := Finite.of_equiv _ ε.toEquiv
  haveI : Finite ↥(KA ε K') := Finite.of_injective _ Subtype.val_injective
  haveI : Finite ↥(KA ε K) := Finite.of_injective _ Subtype.val_injective
  set ρ : A' →ₐc[F] A := quotBialgHom π' hπ' πK hk with hρdef
  have hρ : Function.Surjective ρ := quotBialgHom_surjective π' hπ' πK hk hπK
  have hρπ : ∀ a, ρ (π' a) = πK a := quotBialgHom_apply π' hπ' πK hk
  have hρcomp : (ρ : A' →ₐ[F] A).comp (π' : A₀ →ₐ[F] A') = (πK : A₀ →ₐ[F] A) := quotBialgHom_comp π' hπ' πK hk
  haveI := finite_hopfKer ρ

  have hι : ∀ f : ↥K', ε f.1 ∈ KA ε K' := fun f => (apply_mem_KA_iff ε K' f.1).mpr f.2
  let ι' : ↥K' → ↥(KA ε K') := fun f => ⟨ε f.1, hι f⟩
  have hι'bij : Function.Bijective ι' := by
    constructor
    · intro f g h
      apply Subtype.ext
      exact (ε).injective (congrArg Subtype.val h)
    · intro k
      have hkk := (mem_KA_iff ε K' k.1).mp k.2
      exact ⟨⟨_, hkk⟩, Subtype.ext ((ε).apply_symm_apply k.1)⟩
  have hι'mul : ∀ f g : ↥K', ι' (f * g) = ι' f * ι' g := fun f g => Subtype.ext (map_mul _ _ _)
  have hι'one : ι' 1 = 1 := Subtype.ext (map_one _)
  have hptKsurj : Function.Surjective (pt (KA ε K') π' hπ' hker') := pt_surjective (KA ε K') π' hπ' hker' hbij'
  have hptKinj : Function.Injective (pt (KA ε K') π' hπ' hker') := pt_injective (KA ε K') π' hπ' hker'

  let νpt : M → (A' →ₐ[F] L) := fun f =>
    if hf : f ∈ K' then pt (KA ε K') π' hπ' hker' (ι' ⟨f, hf⟩) else pt (KA ε K') π' hπ' hker' (ι' 1)
  have hνpt : ∀ (f) (hf : f ∈ K'), νpt f = pt (KA ε K') π' hπ' hker' (ι' ⟨f, hf⟩) := fun f hf => dif_pos hf

  obtain ⟨hres1, hresmul, hresfib⟩ :=
    HopfAlgebra.toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique ρ hρ L
  let r : M → WithConv (↥(hopfKer ρ) →ₐ[F] L) := fun f =>
    toConv ((νpt f).comp (hopfKer ρ).val)
  have hr : ∀ (f) (hf : f ∈ K'), r f = toConv ((pt (KA ε K') π' hπ' hker' (ι' ⟨f, hf⟩)).comp (hopfKer ρ).val) := fun f hf => by
    change toConv ((νpt f).comp _) = _; rw [hνpt f hf]

  have hrmul : ∀ f ∈ K', ∀ g ∈ K', r (f * g) = r f * r g := by
    intro f hf g hg
    rw [hr f hf, hr g hg, hr (f * g) (K'.mul_mem hf hg)]
    have h1 : ι' ⟨f * g, K'.mul_mem hf hg⟩ = ι' ⟨f, hf⟩ * ι' ⟨g, hg⟩ := hι'mul ⟨f, hf⟩ ⟨g, hg⟩
    rw [h1]
    have h2 := toConv_pt_mul (KA ε K') π' hπ' hker' (ι' ⟨f, hf⟩) (ι' ⟨g, hg⟩)
    change toConv ((ofConv (toConv (pt (KA ε K') π' hπ' hker' (ι' ⟨f, hf⟩ * ι' ⟨g, hg⟩)))).comp (hopfKer ρ).val) = _
    rw [h2, hresmul]

  have hfacK : ∀ k : ↥K', (k.1 ∈ K) ↔ ∃ χ : A →ₐ[F] L, pt (KA ε K') π' hπ' hker' (ι' k) = χ.comp (ρ : A' →ₐ[F] A) := by
    intro k
    constructor
    · intro hk
      have hkA : ε k.1 ∈ KA ε K := (apply_mem_KA_iff ε K k.1).mpr hk
      let χ : A →ₐ[F] L := pt (KA ε K) πK hπK hkerK ⟨_, hkA⟩
      refine ⟨χ, ?_⟩
      apply eq_of_comp_eq (π' : A₀ →ₐ[F] A') hπ'
      rw [AlgHom.comp_assoc, hρcomp, pt_comp, pt_comp]
    · rintro ⟨χ, hχ⟩
      have hmem : toConv ((χ.comp (ρ : A' →ₐ[F] A)).comp (π' : A₀ →ₐ[F] A')) ∈ KA ε K := by
        apply toConv_mem_of_forall_mem_vanishingIdeal (KA ε K) hbijK
        intro a ha
        change χ (ρ (π' a)) = 0
        rw [hρπ a, (hkerK a).mpr ha, map_zero]
      rw [← hχ, pt_comp] at hmem
      exact (apply_mem_KA_iff ε K k.1).mp hmem

  have hrcoset : ∀ f ∈ K', ∀ g ∈ K', (r f = r g ↔ ∃ k ∈ K, g = f * k) := by
    intro f hf g hg
    rw [hr f hf, hr g hg]
    constructor
    · intro h
      have h' : (ofConv (toConv (pt (KA ε K') π' hπ' hker' (ι' ⟨f, hf⟩)))).comp (hopfKer ρ).val
          = (ofConv (toConv (pt (KA ε K') π' hπ' hker' (ι' ⟨g, hg⟩)))).comp (hopfKer ρ).val := congrArg ofConv h
      obtain ⟨χ, hχ, -⟩ := (hresfib _ _).mp h'

      obtain ⟨k, hkpt⟩ := hptKsurj (χ.comp (ρ : A' →ₐ[F] A))
      obtain ⟨k₀, rfl⟩ := hι'bij.2 k
      have hk₀K : k₀.1 ∈ K := (hfacK k₀).mpr ⟨χ, hkpt⟩
      refine ⟨k₀.1, hk₀K, ?_⟩

      have h3 : toConv (pt (KA ε K') π' hπ' hker' (ι' ⟨g, hg⟩)) = toConv (pt (KA ε K') π' hπ' hker' (ι' (⟨f, hf⟩ * k₀))) := by
        rw [hι'mul, toConv_pt_mul, hkpt]
        exact hχ
      have h4 : ι' ⟨g, hg⟩ = ι' (⟨f, hf⟩ * k₀) := hptKinj (WithConv.toConv_injective h3)
      exact congrArg Subtype.val (hι'bij.1 h4)
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨χ, hχ⟩ := (hfacK ⟨k, hKK' hk⟩).mp hk
      have h1 : ι' ⟨f * k, hg⟩ = ι' ⟨f, hf⟩ * ι' ⟨k, hKK' hk⟩ := hι'mul ⟨f, hf⟩ ⟨k, hKK' hk⟩
      rw [h1]
      apply congrArg toConv
      symm
      have h5 : pt (KA ε K') π' hπ' hker' (ι' ⟨f, hf⟩ * ι' ⟨k, hKK' hk⟩)
          = ofConv (toConv (pt (KA ε K') π' hπ' hker' (ι' ⟨f, hf⟩)) * toConv (χ.comp (ρ : A' →ₐ[F] A))) := by
        rw [← hχ, ← toConv_pt_mul]
      rw [h5]
      exact comp_hopfKer_val_mul_toConv_comp ρ (toConv (pt (KA ε K') π' hπ' hker' (ι' ⟨f, hf⟩))) χ

  have hr1 : r 1 = 1 := by
    rw [hr 1 K'.one_mem]
    have : ι' ⟨1, K'.one_mem⟩ = 1 := hι'one
    rw [this]
    change toConv ((ofConv (toConv (pt (KA ε K') π' hπ' hker' 1))).comp (hopfKer ρ).val) = 1
    rw [pt_one, hres1]
  have hrone : ∀ f ∈ K', (r f = 1 ↔ f ∈ K) := by
    intro f hf
    rw [← hr1, eq_comm, hrcoset 1 K'.one_mem f hf]
    constructor
    · rintro ⟨k, hk, rfl⟩; rwa [one_mul]
    · intro h; exact ⟨f, h, (one_mul f).symm⟩

  have hrsurj : ∀ μ : WithConv (↥(hopfKer ρ) →ₐ[F] L), ∃ f ∈ K', r f = μ := by
    intro μ
    obtain ⟨ν₀, hν₀⟩ := Subalgebra.exists_algHom_comp_val_eq_of_isAlgClosed (hopfKer ρ) L μ.ofConv
    obtain ⟨k, hkν⟩ := hptKsurj ν₀
    obtain ⟨k₀, rfl⟩ := hι'bij.2 k
    refine ⟨k₀.1, k₀.2, ?_⟩
    rw [hr k₀.1 k₀.2, hkν, hν₀]
  haveI : Finite (WithConv (↥(hopfKer ρ) →ₐ[F] L)) :=
    Finite.of_surjective (fun f : ↥K' => r f.1) (fun μ => by
      obtain ⟨f, hf, h⟩ := hrsurj μ; exact ⟨⟨f, hf⟩, h⟩)

  have hrequiv : ∀ (τ : L →ₐ[F] L), ∀ f ∈ K', ∀ g ∈ K', ε g = toConv (τ.comp (ε f).ofConv) →
      ∀ a : ↥(hopfKer ρ), r g a = τ (r f a) := by
    intro τ f hf g hgK hεg a
    have hpt : pt (KA ε K') π' hπ' hker' (ι' ⟨g, hgK⟩) = τ.comp (pt (KA ε K') π' hπ' hker' (ι' ⟨f, hf⟩)) :=
      pt_eq_comp (KA ε K') π' hπ' hker' τ _ _
        (fun a => congrArg (fun ν : WithConv (A₀ →ₐ[F] L) => ν.ofConv a) hεg)
    rw [hr g hgK, hr f hf, hpt]
    rfl

  have hev' := bijective_eval_quot (KA ε K') π' hπ' hker' hbij'
  have hcard₁ : Nat.card (WithConv (↥(hopfKer ρ) →ₐ[F] L)) = Module.finrank F ↥(hopfKer ρ) := by
    rw [natCard_withConv, HopfAlgebra.natCard_algHom_eq_finrank_of_charZero F ↥(hopfKer ρ) L]
  have hev₁ := bijective_eval_hopfKer ρ hev'.1 hcard₁
  have hNK' : Nat.card ↥(KA ε K') = Nat.card ↥K' := (Nat.card_eq_of_bijective ι' hι'bij).symm
  have hιK : ∀ f : ↥K, ε f.1 ∈ KA ε K := fun f => (apply_mem_KA_iff ε K f.1).mpr f.2
  have hNK : Nat.card ↥(KA ε K) = Nat.card ↥K := by
    refine (Nat.card_eq_of_bijective (fun f : ↥K => (⟨ε f.1, hιK f⟩ : ↥(KA ε K))) ⟨?_, ?_⟩).symm
    · intro f g h
      exact Subtype.ext ((ε).injective (congrArg Subtype.val h))
    · intro k
      exact ⟨⟨_, (mem_KA_iff ε K k.1).mp k.2⟩, Subtype.ext ((ε).apply_symm_apply k.1)⟩
  have hdimA' : Module.finrank F A' = Nat.card ↥K' := by
    rw [← HopfAlgebra.natCard_algHom_eq_finrank_of_charZero F A' L, ← hNK']
    exact (Nat.card_eq_of_bijective _ ⟨hptKinj, hptKsurj⟩).symm
  have hdimA : Module.finrank F A = Nat.card ↥K := by
    rw [← HopfAlgebra.natCard_algHom_eq_finrank_of_charZero F A L, ← hNK]
    exact (Nat.card_eq_of_bijective _ ⟨pt_injective (KA ε K) πK hπK hkerK,
      pt_surjective (KA ε K) πK hπK hkerK hbijK⟩).symm
  haveI : Finite ↥K := Finite.of_injective _ Subtype.val_injective
  have hKpos : 0 < Nat.card ↥K := Nat.card_pos_iff.mpr ⟨⟨⟨1, K.one_mem⟩⟩, inferInstance⟩

  have hA'p : (toConv (AlgHom.id F A')) ^ p = 1 := by
    apply toConv_id_pow_eq_one_of_points (fun k : ↥(KA ε K') => pt (KA ε K') π' hπ' hker' k) ?_ p ?_
    · intro a a' h
      apply eq_of_forall_pt_apply_eq (fun ν : WithConv (A' →ₐ[F] L) => ν.ofConv) hev'.1
      intro ν
      obtain ⟨k, hk⟩ := hptKsurj ν.ofConv
      have := congr_fun h k
      change pt (KA ε K') π' hπ' hker' k a = pt (KA ε K') π' hπ' hker' k a' at this
      rw [← hk]; exact this
    · intro k
      rw [toConv_pt_pow]
      have hk1 : k ^ p = 1 := by
        apply Subtype.ext
        obtain ⟨f, -, hf⟩ := k.2
        change (k.1) ^ p = 1
        rw [← hf]
        change (ε f) ^ p = 1
        rw [← map_pow, hMp, map_one]
      rw [hk1]
      exact pt_one (KA ε K') π' hπ' hker'
  exact ⟨r, inferInstance, hrmul, hrcoset, hrone, hrsurj, hrequiv, hev₁, hcard₁, hdimA', hdimA, hKpos, hA'p⟩
end StepOrder
end HopfAlgebra

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk ofAlgHom mul_antipode_lTensor_comul_apply mul_antipode_rTensor_comul_apply vanishingIdealOfPoints vanishingIdealOfPoints_antitone ptSet mem_ptSet_iff ofConv_mem_ptSet ptSet_mono pointQuot evalQuot evalQuot_tmul HopfKerHopf.coaction_repr HopfKerHopf.counit_coe HopfKerHopf.hopfKerVal coaction hopfKer evalQuot_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal natCard_algHom_eq_finrank_of_charZero toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one"
p2m_open "HopfAlgebra"
namespace StepOrder

open WithConv

theorem q_transport
    {R : Type} [CommRing R] {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] [Algebra R L]
    {A₁ : Type} [CommRing A₁] [Bialgebra F A₁] {B : Type} [CommRing B] [Bialgebra R B]
    {M : Type} [Monoid M] (K K' : Submonoid M)
    (r : M → WithConv (A₁ →ₐ[F] L))
    (hrmul : ∀ f ∈ K', ∀ g ∈ K', r (f * g) = r f * r g) (hrone : ∀ f ∈ K', (r f = 1 ↔ f ∈ K))
    (hrsurj : ∀ ν : WithConv (A₁ →ₐ[F] L), ∃ f ∈ K', r f = ν)
    (Psub : Subalgebra R L) {P' : Type} [CommRing P'] [Algebra R P'] (V : ↥Psub ≃ₐ[R] P')
    (ι : B → A₁) (e₁ : (A₁ →ₐ[F] L) ≃ (B →ₐ[R] ↥Psub))
    (he₁val : ∀ (f : A₁ →ₐ[F] L) (x : B), ((e₁ f x : ↥Psub) : L) = f (ι x))
    (he₁mul : ∀ f g : A₁ →ₐ[F] L, toConv (e₁ (ofConv (toConv f * toConv g))) = toConv (e₁ f) * toConv (e₁ g))
    (he₁one : toConv (e₁ (ofConv (1 : WithConv (A₁ →ₐ[F] L)))) = 1) :
    ∃ q : M → (B →ₐ[R] P'),
      Nat.card (B →ₐ[R] P') = Nat.card (WithConv (A₁ →ₐ[F] L)) ∧
      (∀ f ∈ K', ∀ g ∈ K', toConv (q (f * g)) = toConv (q f) * toConv (q g)) ∧
      (∀ f ∈ K', (toConv (q f) = 1 ↔ f ∈ K)) ∧
      (∀ b : B →ₐ[R] P', ∃ f ∈ K', q f = b) ∧
      (∀ f ∈ K', ∀ x : B, ((V.symm (q f x) : ↥Psub) : L) = r f (ι x)) := by
  classical
  set W : ↥Psub →ₐ[R] P' := V.toAlgHom with hW
  refine ⟨fun f => W.comp (e₁ (ofConv (r f))), ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [Nat.card_congr (AlgEquiv.arrowCongr (AlgEquiv.refl (R := R) (A₁ := B)) V.symm), Nat.card_congr e₁.symm]
    exact Nat.card_congr ⟨toConv, ofConv, fun _ => rfl, fun _ => rfl⟩
  ·
    intro f hf g hg
    show toConv (W.comp (e₁ (ofConv (r (f * g))))) = toConv (W.comp (e₁ (ofConv (r f)))) * toConv (W.comp (e₁ (ofConv (r g))))
    rw [hrmul f hf g hg]
    have h1 : e₁ (ofConv (r f * r g)) = ofConv (toConv (e₁ (ofConv (r f))) * toConv (e₁ (ofConv (r g)))) := by
      have := he₁mul (ofConv (r f)) (ofConv (r g))
      rw [toConv_ofConv, toConv_ofConv] at this
      rw [← this, ofConv_toConv]
    rw [h1, AlgHom.comp_convMul_distrib, toConv_ofConv]
  ·
    intro f hf
    show toConv (W.comp (e₁ (ofConv (r f)))) = 1 ↔ f ∈ K
    rw [← hrone f hf]
    have h2 : e₁ (ofConv (1 : WithConv (A₁ →ₐ[F] L))) = ofConv (1 : WithConv (B →ₐ[R] ↥Psub)) := by
      rw [← ofConv_toConv (e₁ (ofConv (1 : WithConv (A₁ →ₐ[F] L)))), he₁one]
    constructor
    · intro h
      have h1 : W.comp (e₁ (ofConv (r f))) = W.comp (e₁ (ofConv 1)) := by
        rw [h2, algHom_comp_convOne, ← ofConv_toConv (W.comp (e₁ (ofConv (r f)))), h]
      have hWinj : Function.Injective (fun φ : B →ₐ[R] ↥Psub => W.comp φ) := by
        intro φ ψ hφψ
        apply AlgHom.ext
        intro x
        have := congrArg (fun χ : B →ₐ[R] P' => χ x) hφψ
        exact V.injective this
      have h3 : e₁ (ofConv (r f)) = e₁ (ofConv 1) := hWinj h1
      have h4 := e₁.injective h3
      rw [← toConv_ofConv (r f), h4, toConv_ofConv]
    · intro h
      rw [h, h2, algHom_comp_convOne, toConv_ofConv]
  ·
    intro b
    obtain ⟨f, hf, hrf⟩ := hrsurj (toConv (e₁.symm (V.symm.toAlgHom.comp b)))
    refine ⟨f, hf, ?_⟩
    show W.comp (e₁ (ofConv (r f))) = b
    rw [hrf, ofConv_toConv, Equiv.apply_symm_apply]
    apply AlgHom.ext
    intro x
    exact V.apply_symm_apply (b x)
  ·
    intro f hf x
    show ((V.symm (V (e₁ (ofConv (r f)) x)) : ↥Psub) : L) = r f (ι x)
    rw [AlgEquiv.symm_apply_apply, he₁val]

end StepOrder
end HopfAlgebra

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk ofAlgHom mul_antipode_lTensor_comul_apply mul_antipode_rTensor_comul_apply vanishingIdealOfPoints vanishingIdealOfPoints_antitone ptSet mem_ptSet_iff ofConv_mem_ptSet ptSet_mono pointQuot evalQuot evalQuot_tmul HopfKerHopf.coaction_repr HopfKerHopf.counit_coe HopfKerHopf.hopfKerVal coaction hopfKer evalQuot_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal natCard_algHom_eq_finrank_of_charZero toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one"
namespace StepOrder
p2m_open "HopfAlgebra"

open ValuationSubring

variable {p : ℕ} (P : ValuationSubring (AlgebraicClosure ℚ))

scoped instance instIsScalarTower_ratLocalizedAt :
    IsScalarTower ↥(GaloisRep.ratLocalizedAt p) ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) :=
  IsScalarTower.of_algebraMap_eq (fun x => by
    show algebraMap ℚ (AlgebraicClosure ℚ) (x : ℚ) =
      algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) (algebraMap ℚ ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (x : ℚ))
    rw [← IsScalarTower.algebraMap_apply])

theorem charZero_R : CharZero ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) := inferInstance

theorem natCast_mem_nonunits_of_irreducible (hirr : Irreducible ((p : ℕ) : ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))) :
    ((p : ℕ) : AlgebraicClosure ℚ) ∈ P.nonunits := by

  have hp0 : ((p : ℕ) : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))) ≠ 0 := by
    intro h
    apply hirr.ne_zero
    exact Subtype.ext (by exact_mod_cast h)
  by_contra hnu

  have hpP : ((p : ℕ) : AlgebraicClosure ℚ) ∈ P := natCast_mem P p
  have hval : P.valuation ((p : ℕ) : AlgebraicClosure ℚ) = 1 :=
    le_antisymm ((P.valuation_le_one_iff _).mpr hpP) (not_lt.mp (fun h => hnu ((P.mem_nonunits_iff).mpr h)))
  have hinv : ((p : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ P := by
    rw [← P.valuation_le_one_iff, map_inv₀, hval, inv_one]

  apply hirr.not_isUnit
  have hmem : ((p : ℕ) : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)))⁻¹ ∈ P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)) := by
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast]
    exact hinv
  refine ⟨⟨((p : ℕ) : ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))), ⟨_, hmem⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    show ((p : ℕ) : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))) * ((p : ℕ) : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)))⁻¹ = 1
    exact mul_inv_cancel₀ hp0
  · apply Subtype.ext
    show ((p : ℕ) : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)))⁻¹ * ((p : ℕ) : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))) = 1
    exact inv_mul_cancel₀ hp0

theorem coe_ratLocalizedAt_mem (hp : p.Prime) (hirr : Irreducible ((p : ℕ) : ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))))
    (x : ↥(GaloisRep.ratLocalizedAt p)) : ((x : ℚ) : AlgebraicClosure ℚ) ∈ P := by
  have hpm : (⟨((p : ℕ) : AlgebraicClosure ℚ), natCast_mem P p⟩ : ↥P) ∈ IsLocalRing.maximalIdeal ↥P :=
    ValuationSubring.coe_mem_nonunits_iff.mp (natCast_mem_nonunits_of_irreducible P hirr)

  set d : ↥P := ⟨((x : ℚ).den : AlgebraicClosure ℚ), natCast_mem P _⟩ with hd
  have hcop : IsCoprime (((x : ℚ).den : ℤ)) (p : ℤ) := Nat.isCoprime_iff_coprime.mpr x.2
  have hcopP : IsCoprime d (⟨((p : ℕ) : AlgebraicClosure ℚ), natCast_mem P p⟩ : ↥P) := by
    have h := hcop.map (Int.castRingHom ↥P)
    have e1 : Int.castRingHom ↥P (((x : ℚ).den : ℤ)) = d := by
      apply Subtype.ext; simp [hd]
    have e2 : Int.castRingHom ↥P (p : ℤ) = ⟨((p : ℕ) : AlgebraicClosure ℚ), natCast_mem P p⟩ := by
      apply Subtype.ext; simp
    rwa [e1, e2] at h
  have hdu : IsUnit d := by
    by_contra hnd
    have hdm : d ∈ IsLocalRing.maximalIdeal ↥P := (IsLocalRing.mem_maximalIdeal _).mpr hnd
    obtain ⟨a, b, hab⟩ := hcopP
    have h1 : (1 : ↥P) ∈ IsLocalRing.maximalIdeal ↥P := by
      rw [← hab]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hdm) (Ideal.mul_mem_left _ _ hpm)
    exact (IsLocalRing.maximalIdeal.isMaximal ↥P).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨u, hu⟩ := hdu

  have hx : ((x : ℚ) : AlgebraicClosure ℚ) =
      (((x : ℚ).num : ℤ) : AlgebraicClosure ℚ) * (((x : ℚ).den : ℕ) : AlgebraicClosure ℚ)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact_mod_cast (Rat.num_div_den (x : ℚ)).symm
  have hcoe : ((↑(u⁻¹ : (↥P)ˣ) : ↥P) : AlgebraicClosure ℚ) = ((((x : ℚ).den : ℕ) : AlgebraicClosure ℚ))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    have h := congrArg (fun z : ↥P => (z : AlgebraicClosure ℚ)) u.inv_mul
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one, hu] at h
    exact h
  rw [hx, ← hcoe]
  exact P.mul_mem _ _ (intCast_mem P _) (SetLike.coe_mem _)

theorem exists_coe_eq_algebraMap (hp : p.Prime) (hirr : Irreducible ((p : ℕ) : ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))))
    (x : ↥(GaloisRep.ratLocalizedAt p)) :
    ∃ y : ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))), (y : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))) = algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) x := by
  refine ⟨⟨algebraMap ℚ ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (x : ℚ), ?_⟩, rfl⟩
  rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
  exact_mod_cast coe_ratLocalizedAt_mem P hp hirr x

noncomputable def fixedAlgHom (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    AlgebraicClosure ℚ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ :=
  { (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toRingEquiv.toRingHom with
    commutes' := fun a => by
      show σ (a : AlgebraicClosure ℚ) = (a : AlgebraicClosure ℚ)
      exact (IntermediateField.mem_fixedField_iff _ _).mp a.2 σ hσ }

@[scoped simp] theorem fixedAlgHom_apply (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (x : AlgebraicClosure ℚ) :
    fixedAlgHom P σ hσ x = σ x := rfl

def valSubalg : Subalgebra ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) (AlgebraicClosure ℚ) :=
  { P.toSubring with
    algebraMap_mem' := fun x => by
      show ((x : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))) : AlgebraicClosure ℚ) ∈ P.toSubring
      exact x.2 }

theorem mem_valSubalg_iff (x : AlgebraicClosure ℚ) : x ∈ valSubalg P ↔ x ∈ P := Iff.rfl

theorem mem_valSubalg_of_isIntegral (x : AlgebraicClosure ℚ) (hx : IsIntegral ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) x) : x ∈ valSubalg P := by
  rw [mem_valSubalg_iff]

  have hxP : IsIntegral ↥P x := by
    obtain ⟨f, hf, hfx⟩ := hx
    let φ : ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) →+* ↥P :=
      { toFun := fun r => ⟨((r : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))) : AlgebraicClosure ℚ), r.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    refine ⟨f.map φ, hf.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    convert hfx using 1 <;> try first | with_reducible_and_instances rfl | rfl
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥P) (K := AlgebraicClosure ℚ)).mp hxP
  rw [← hy]
  exact y.2

variable [Algebra ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) ↥P]

noncomputable def valSubalgEquiv
    (hiP : ∀ x : ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))), ((algebraMap ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) ↥P x : ↥P) : AlgebraicClosure ℚ) = ((x : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))) : AlgebraicClosure ℚ)) :
    ↥(valSubalg P) ≃ₐ[↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))] ↥P :=
  { toFun := fun x => ⟨(x : AlgebraicClosure ℚ), x.2⟩
    invFun := fun y => ⟨(y : AlgebraicClosure ℚ), y.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl
    commutes' := fun r => by
      apply Subtype.ext
      show ((algebraMap ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) ↥(valSubalg P) r : ↥(valSubalg P)) : AlgebraicClosure ℚ) =
        ((algebraMap ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) ↥P r : ↥P) : AlgebraicClosure ℚ)
      rw [hiP]
      rfl }

@[scoped simp] theorem coe_valSubalgEquiv
    (hiP : ∀ x : ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))), ((algebraMap ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) ↥P x : ↥P) : AlgebraicClosure ℚ) = ((x : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))) : AlgebraicClosure ℚ))
    (x : ↥(valSubalg P)) : ((valSubalgEquiv P hiP x : ↥P) : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ) := rfl

@[scoped simp] theorem coe_valSubalgEquiv_symm
    (hiP : ∀ x : ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))), ((algebraMap ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) ↥P x : ↥P) : AlgebraicClosure ℚ) = ((x : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))) : AlgebraicClosure ℚ))
    (y : ↥P) : (((valSubalgEquiv P hiP).symm y : ↥(valSubalg P)) : AlgebraicClosure ℚ) = (y : AlgebraicClosure ℚ) := rfl

theorem natCard_algHom_congr
    (hiP : ∀ x : ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))), ((algebraMap ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) ↥P x : ↥P) : AlgebraicClosure ℚ) = ((x : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))) : AlgebraicClosure ℚ))
    (B : Type) [CommRing B] [Algebra ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) B] :
    Nat.card (B →ₐ[↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))] ↥P) = Nat.card (B →ₐ[↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))] ↥(valSubalg P)) :=
  Nat.card_congr (AlgEquiv.arrowCongr AlgEquiv.refl (valSubalgEquiv P hiP).symm)

end HopfAlgebra.StepOrder
p2m_reactivate "P2MW.S_HopfAlgebra_exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step.HopfAlgebra P2MW.S_HopfAlgebra_exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step.HopfAlgebra.StepOrder"
p2m_reactivate "P2MW.S_HopfAlgebra_exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step.HopfAlgebra"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk ofAlgHom mul_antipode_lTensor_comul_apply mul_antipode_rTensor_comul_apply vanishingIdealOfPoints vanishingIdealOfPoints_antitone ptSet mem_ptSet_iff ofConv_mem_ptSet ptSet_mono pointQuot evalQuot evalQuot_tmul HopfKerHopf.coaction_repr HopfKerHopf.counit_coe HopfKerHopf.hopfKerVal coaction hopfKer evalQuot_bijective_of_forall_exists_comp_eq map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal natCard_algHom_eq_finrank_of_charZero toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one"
p2m_open "HopfAlgebra"
namespace StepOrder

open WithConv

section Concrete
variable {p : ℕ} (P : ValuationSubring (AlgebraicClosure ℚ))

set_option quotPrecheck false
local notation "ℤp" => ↥(GaloisRep.ratLocalizedAt p)
local notation "ℚb" => AlgebraicClosure ℚ
local notation "F′" => ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))
local notation "R′" => ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))

variable {P} in
theorem algebraMap_ratLocalizedAt_mem (hp : p.Prime) (hirr : Irreducible ((p : ℕ) : R′)) (x : ℤp) :
    algebraMap ℤp F′ x ∈ P.comap (algebraMap F′ ℚb) := by
  change algebraMap F′ ℚb ((x : ℚ) : F′) ∈ P
  rw [map_ratCast]
  exact coe_ratLocalizedAt_mem P hp hirr x

noncomputable def algZpR (hp : p.Prime) (hirr : Irreducible ((p : ℕ) : R′)) : ℤp →+* R′ where
  toFun x := ⟨algebraMap ℤp F′ x, algebraMap_ratLocalizedAt_mem hp hirr x⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

theorem stab_KA {H : Type} [CommRing H] [Bialgebra ℤp H]
    {A₀ : Type} [CommRing A₀] [HopfAlgebra F′ A₀]
    (ε : WithConv (H →ₐ[ℤp] ℚb) ≃* WithConv (A₀ →ₐ[F′] ℚb))
    (hε : ∀ (σ : ℚb ≃ₐ[ℚ] ℚb) (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (f : WithConv (H →ₐ[ℤp] ℚb)),
      ε (toConv (((fixedAlgHom P σ hσ).restrictScalars ℤp).comp f.ofConv))
        = toConv ((fixedAlgHom P σ hσ).comp (ε f).ofConv))
    (S : Submonoid (WithConv (H →ₐ[ℤp] ℚb)))
    (hS : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ S, ∀ g : WithConv (H →ₐ[ℤp] ℚb),
      (∀ h : H, g h = σ (f h)) → g ∈ S) :
    ∀ σ : ℚb ≃ₐ[ℚ] ℚb, σ ∈ P.inertiaSubgroupIn ℚ → ∀ ν ∈ KA ε S, ∃ ν' ∈ KA ε S,
      ∀ a : A₀, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a) := by
  intro σ hσ ν hν
  rw [mem_KA_iff] at hν
  set f := ε.symm ν with hf
  let g : WithConv (H →ₐ[ℤp] ℚb) := toConv (((fixedAlgHom P σ hσ).restrictScalars ℤp).comp f.ofConv)
  have hg : g ∈ S := hS σ hσ f hν g (fun h => rfl)
  refine ⟨ε g, (apply_mem_KA_iff ε S g).mpr hg, fun a => ?_⟩
  have h1 : ε g = toConv ((fixedAlgHom P σ hσ).comp (ε f).ofConv) := hε σ hσ f
  rw [h1, hf, MulEquiv.apply_symm_apply]
  rfl

variable {H : Type} [CommRing H] [HopfAlgebra ↥(GaloisRep.ratLocalizedAt p) H]
  [Module.Finite ↥(GaloisRep.ratLocalizedAt p) H] [Module.Flat ↥(GaloisRep.ratLocalizedAt p) H]
  [Coalgebra.IsCocomm ↥(GaloisRep.ratLocalizedAt p) H]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem main (hp : p.Prime)
    (hMp : ∀ f : WithConv (H →ₐ[ℤp] ℚb), f ^ p = 1)
    (K K' : Submonoid (WithConv (H →ₐ[ℤp] ℚb))) (hKK' : K ≤ K')
    (hK : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K, ∀ g : WithConv (H →ₐ[ℤp] ℚb), (∀ h : H, g h = σ (f h)) → g ∈ K)
    (hK' : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K', ∀ g : WithConv (H →ₐ[ℤp] ℚb), (∀ h : H, g h = σ (f h)) → g ∈ K')
    (s : ℕ) (hcard : Nat.card K' = p ^ s * Nat.card K)
    [Algebra R′ ↥P]
    (hiP : ∀ x : R′, ((algebraMap R′ ↥P x : ↥P) : ℚb) = ((x : F′) : ℚb))
    (hDVR : IsDiscreteValuationRing R′) (hirr : Irreducible ((p : ℕ) : R′)) :
    ∃ (B : Type) (_ : CommRing B) (_ : HopfAlgebra ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) B)
        (_ : Module.Finite ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) B) (_ : Module.Free ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) B) (_ : Coalgebra.IsCocomm ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) B),
      Module.finrank ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) B = p ^ s ∧
      (∀ (T : Type) [CommRing T] [Algebra ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) T] (f : WithConv (B →ₐ[↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))] T)), f ^ p ^ 1 = 1) ∧
      ∃ (A₁ : Type) (_ : CommRing A₁) (_ : HopfAlgebra ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) A₁) (_ : Module.Finite ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) A₁)
          (_ : Coalgebra.IsCocomm ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) A₁) (_ : Finite (WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ)))
          (e : A₁ ≃ₐc[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) ⊗[↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))] B)
          (r : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ) → WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ))
          (q : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ) → (B →ₐ[↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))] ↥P)),
        Function.Bijective
          (Algebra.TensorProduct.lift
            (Algebra.ofId (AlgebraicClosure ℚ) (WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ) → AlgebraicClosure ℚ))
            (Pi.algHom ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) _
              fun ν : WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ) =>
                (WithConv.ofConv ν : A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ))
            (fun _ _ => Commute.all _ _) :
            AlgebraicClosure ℚ ⊗[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] A₁ →ₐ[AlgebraicClosure ℚ]
              (WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ) → AlgebraicClosure ℚ)) ∧
        (∀ f ∈ K', ∀ g ∈ K', r (f * g) = r f * r g) ∧
        (∀ f ∈ K', ∀ g ∈ K', (r f = r g ↔ ∃ k ∈ K, g = f * k)) ∧
        (∀ f ∈ K', (r f = 1 ↔ f ∈ K)) ∧
        (∀ ν : WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ), ∃ f ∈ K', r f = ν) ∧
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
          ∀ g : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ),
            (∀ h : H, g h = σ (f h)) → ∀ a : A₁, r g a = σ (r f a)) ∧
        Nat.card (B →ₐ[↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))] ↥P) = p ^ s ∧
        (∀ f ∈ K', ∀ g ∈ K',
          WithConv.toConv (q (f * g)) = WithConv.toConv (q f) * WithConv.toConv (q g)) ∧
        (∀ f ∈ K', (WithConv.toConv (q f) = 1 ↔ f ∈ K)) ∧
        (∀ b : B →ₐ[↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))] ↥P, ∃ f ∈ K', q f = b) ∧
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
          ∀ g : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ),
            (∀ h : H, g h = σ (f h)) → ∀ x : B,
              ((q g x : ↥P) : AlgebraicClosure ℚ) = σ ((q f x : ↥P) : AlgebraicClosure ℚ)) ∧
        (∀ f ∈ K', ∀ b : B,
          ((q f b : ↥P) : AlgebraicClosure ℚ) = r f (e.symm ((1 : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))) ⊗ₜ[↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))] b))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsDiscreteValuationRing R′ := hDVR

  let A₀ : Type := F′ ⊗[ℤp] H
  letI : CommRing A₀ := Algebra.TensorProduct.instCommRing
  letI : HopfAlgebra F′ A₀ := inferInstance
  haveI : Module.Finite F′ A₀ := inferInstance
  haveI : Coalgebra.IsCocomm F′ A₀ := inferInstance
  let ε : WithConv (H →ₐ[ℤp] ℚb) ≃* WithConv (A₀ →ₐ[F′] ℚb) := ptsEquiv ℤp F′ H ℚb
  have hε : ∀ (σ : ℚb ≃ₐ[ℚ] ℚb) (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (f : WithConv (H →ₐ[ℤp] ℚb)),
      ε (toConv (((fixedAlgHom P σ hσ).restrictScalars ℤp).comp f.ofConv))
        = toConv ((fixedAlgHom P σ hσ).comp (ε f).ofConv) :=
    fun σ hσ f => ptsEquiv_comp (fixedAlgHom P σ hσ) f

  have hcardPts : Nat.card (WithConv (H →ₐ[ℤp] ℚb)) = Module.finrank ℤp H :=
    GaloisRep.natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf p H
  haveI : IsDiscreteValuationRing ℤp := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p hp
  haveI : Module.Free ℤp H := Module.free_of_flat_of_isLocalRing
  haveI : Nontrivial H := (Bialgebra.counitAlgHom ℤp H).toRingHom.domain_nontrivial
  haveI hfinPts : Finite (WithConv (H →ₐ[ℤp] ℚb)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardPts]; exact Module.finrank_pos.ne')
  haveI : Finite (WithConv (A₀ →ₐ[F′] ℚb)) := Finite.of_equiv _ ε.toEquiv
  haveI : Finite ↥(KA ε K') := Finite.of_injective _ Subtype.val_injective
  haveI : Finite ↥(KA ε K) := Finite.of_injective _ Subtype.val_injective

  have hevA := bijective_eval_baseChange (R₀ := ℤp) (F := F′) (H := H) (L := ℚb)
    (GaloisRep.bijective_lift_pi_algHom_of_finiteFlatHopf p H)
  obtain ⟨hbij', hsep'⟩ := HopfAlgebra.evalQuot_bijective_of_forall_exists_comp_eq (P.inertiaSubgroupIn ℚ)
    A₀ hevA (KA ε K') (stab_KA P ε hε K' hK')
  obtain ⟨hbijK, hsepK⟩ := HopfAlgebra.evalQuot_bijective_of_forall_exists_comp_eq (P.inertiaSubgroupIn ℚ)
    A₀ hevA (KA ε K) (stab_KA P ε hε K hK)

  obtain ⟨hc1, hc2, hc3⟩ :=
    HopfAlgebra.map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet
      (KA ε K') hsep' (inv_KA ε hp hMp K')
  obtain ⟨A', _instA'1, _instA'2, π', hπ', hkerπ', hcoc', hfin', -⟩ :=
    HopfAlgebra.exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal
      (vanishingIdealOfPoints (ptSet (KA ε K'))) hc1 hc2 hc3
  obtain ⟨hd1, hd2, hd3⟩ :=
    HopfAlgebra.map_mk_comul_eq_zero_and_counit_eq_zero_and_antipode_mem_of_mem_vanishingIdealOfPoints_ptSet
      (KA ε K) hsepK (inv_KA ε hp hMp K)
  obtain ⟨A, _instA1, _instA2, πK, hπK, hkerπK, hcocK, hfinK, -⟩ :=
    HopfAlgebra.exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal
      (vanishingIdealOfPoints (ptSet (KA ε K))) hd1 hd2 hd3
  haveI : Coalgebra.IsCocomm F′ A' := hcoc' inferInstance
  haveI : Module.Finite F′ A' := hfin' inferInstance
  haveI : Coalgebra.IsCocomm F′ A := hcocK inferInstance
  haveI : Module.Finite F′ A := hfinK inferInstance
  have hker' : ∀ a, π' a = 0 ↔ a ∈ vanishingIdealOfPoints (ptSet (KA ε K')) := fun a => by
    rw [← hkerπ']; exact (RingHom.mem_ker).symm
  have hkerK : ∀ a, πK a = 0 ↔ a ∈ vanishingIdealOfPoints (ptSet (KA ε K)) := fun a => by
    rw [← hkerπK]; exact (RingHom.mem_ker).symm

  have hanti : vanishingIdealOfPoints (ptSet (KA ε K')) ≤ vanishingIdealOfPoints (ptSet (KA ε K)) :=
    vanishingIdealOfPoints_antitone (ptSet_mono (KA_mono ε hKK'))
  have hk : ∀ a, π' a = 0 → πK a = 0 := fun a ha => (hkerK a).mpr (hanti ((hker' a).mp ha))
  let ρ : A' →ₐc[F′] A := quotBialgHom π' hπ' πK hk
  have hρ : Function.Surjective ρ := quotBialgHom_surjective π' hπ' πK hk hπK
  have hρπ : ∀ a, ρ (π' a) = πK a := quotBialgHom_apply π' hπ' πK hk
  have hρcomp : (ρ : A' →ₐ[F′] A).comp (π' : A₀ →ₐ[F′] A') = (πK : A₀ →ₐ[F′] A) := quotBialgHom_comp π' hπ' πK hk

  obtain ⟨r, hfinpts, hrmul, hrcoset, hrone, hrsurj, hrequivτ, hev₁, hcard₁, hdimA', hdimA, hKpos, hA'p⟩ :=
    points_package ε K K' hKK' π' hπ' hker' hbij' πK hπK hkerK hbijK hk hMp
  haveI := hfinpts
  have hrequiv : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K', ∀ g : WithConv (H →ₐ[ℤp] ℚb),
      (∀ h : H, g h = σ (f h)) → ∀ a : ↥(hopfKer ρ), r g a = σ (r f a) := by
    intro σ hσ f hf g hg a
    have hgK : g ∈ K' := hK' σ hσ f hf g hg
    have hg' : g = toConv (((fixedAlgHom P σ hσ).restrictScalars ℤp).comp f.ofConv) := by
      apply WithConv.ext; apply AlgHom.ext; intro h; exact hg h
    have hεg : ε g = toConv ((fixedAlgHom P σ hσ).comp (ε f).ofConv) := by rw [hg']; exact hε σ hσ f
    exact hrequivτ (fixedAlgHom P σ hσ) f hf g hgK hεg a
  have hA₁p : (toConv (AlgHom.id F′ ↥(hopfKer ρ))) ^ p = 1 :=
    toConv_id_pow_eq_one_of_injective (hopfKerVal ρ) (hopfKerVal_injective ρ) p hA'p

  letI algZpR' : Algebra ℤp R′ := (algZpR P hp hirr).toAlgebra
  haveI : IsScalarTower ℤp R′ F′ := IsScalarTower.of_algebraMap_eq fun x => rfl

  haveI : IsScalarTower R′ F′ A' := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : IsScalarTower R′ F′ A := IsScalarTower.of_algebraMap_eq fun x => rfl
  letI algZA' : Algebra ℤp A' := ((algebraMap F′ A').comp (algebraMap ℤp F′)).toAlgebra
  haveI : IsScalarTower ℤp F′ A' := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : IsScalarTower ℤp R′ A' := IsScalarTower.of_algebraMap_eq fun x => rfl
  have hdim' : Module.finrank F′ A' = p ^ s * Nat.card ↥K := by rw [hdimA', hcard]
  obtain ⟨B, _iB, instB, hBfinI, hBfree, hBcoc, hrank, hrankF, hBkill, e, ιB, e₁, he, he₁val, he₁mul, he₁one⟩ :=
    order_package (R₀ := ℤp) (R := R′) (F := F′) (L := ℚb) (valSubalg P) (mem_valSubalg_of_isIntegral P)
      π' hπ' ρ hρ hKpos hdim' hdimA hA₁p

  obtain ⟨q, hcardV, hqmul, hqker, hqsurj, hqval⟩ :=
    q_transport K K' r hrmul hrone hrsurj (valSubalg P) (valSubalgEquiv P hiP) ιB e₁ he₁val he₁mul he₁one
  have hqcoe : ∀ f ∈ K', ∀ x : B, ((q f x : ↥P) : ℚb) = r f (ιB x) := fun f hf x => by
    rw [← hqval f hf x]; rfl
  have hqequiv : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K', ∀ g : WithConv (H →ₐ[ℤp] ℚb),
      (∀ h : H, g h = σ (f h)) → ∀ x : B, ((q g x : ↥P) : ℚb) = σ ((q f x : ↥P) : ℚb) := by
    intro σ hσ f hf g hg x
    have hgK : g ∈ K' := hK' σ hσ f hf g hg
    rw [hqcoe g hgK x, hqcoe f hf x]
    exact hrequiv σ hσ f hf g hg (ιB x)
  have hcardV' : Nat.card (B →ₐ[R′] ↥P) = p ^ s := by rw [hcardV, hcard₁, hrankF]

  exact ⟨B, _iB, instB, hBfinI, hBfree, hBcoc, hrank, hBkill,
    ↥(hopfKer ρ), inferInstance, inferInstance, inferInstance, inferInstance, hfinpts,
    e, r, q, hev₁, hrmul, hrcoset, hrone, hrsurj, hrequiv, hcardV', hqmul, hqker, hqsurj, hqequiv,
    fun f hf b => by rw [he b]; exact hqcoe f hf b⟩

end Concrete
p2m_reactivate "P2MW.S_HopfAlgebra_exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step.HopfAlgebra P2MW.S_HopfAlgebra_exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step.HopfAlgebra.StepOrder"
end StepOrder
p2m_reactivate "P2MW.S_HopfAlgebra_exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step.HopfAlgebra P2MW.S_HopfAlgebra_exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step.HopfAlgebra.StepOrder"
end HopfAlgebra
p2m_reactivate "P2MW.S_HopfAlgebra_exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step.HopfAlgebra P2MW.S_HopfAlgebra_exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step.HopfAlgebra.StepOrder"

theorem solution
    {p : ℕ} (hp : p.Prime)
    {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hMp : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (K K' : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)))
    (hKK' : K ≤ K')
    (hK : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K,
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K))
    (hK' : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K'))
    (s : ℕ) (hcard : Nat.card K' = p ^ s * Nat.card K)
    [Algebra ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) ↥P]
    (hiP : ∀ x : ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))),
      ((algebraMap ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) ↥P x : ↥P) : AlgebraicClosure ℚ) = ((x : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))) : AlgebraicClosure ℚ))
    (hDVR : IsDiscreteValuationRing ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hirr : Irreducible ((p : ℕ) : ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))) :
    ∃ (B : Type) (_ : CommRing B) (_ : HopfAlgebra ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) B)
        (_ : Module.Finite ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) B) (_ : Module.Free ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) B) (_ : Coalgebra.IsCocomm ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) B),
      Module.finrank ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) B = p ^ s ∧
      (∀ (T : Type) [CommRing T] [Algebra ↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) T] (f : WithConv (B →ₐ[↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))] T)), f ^ p ^ 1 = 1) ∧
      ∃ (A₁ : Type) (_ : CommRing A₁) (_ : HopfAlgebra ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) A₁) (_ : Module.Finite ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) A₁)
          (_ : Coalgebra.IsCocomm ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) A₁) (_ : Finite (WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ)))
          (e : A₁ ≃ₐc[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) ⊗[↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))] B)
          (r : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ))
          (q : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → (B →ₐ[↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))] ↥P)),
        Function.Bijective
          (Algebra.TensorProduct.lift
            (Algebra.ofId (AlgebraicClosure ℚ) (WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ) → AlgebraicClosure ℚ))
            (Pi.algHom ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) _
              fun ν : WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ) =>
                (WithConv.ofConv ν : A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ))
            (fun _ _ => Commute.all _ _) :
            AlgebraicClosure ℚ ⊗[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] A₁ →ₐ[AlgebraicClosure ℚ]
              (WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ) → AlgebraicClosure ℚ)) ∧
        (∀ f ∈ K', ∀ g ∈ K', r (f * g) = r f * r g) ∧
        (∀ f ∈ K', ∀ g ∈ K', (r f = r g ↔ ∃ k ∈ K, g = f * k)) ∧
        (∀ f ∈ K', (r f = 1 ↔ f ∈ K)) ∧
        (∀ ν : WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ), ∃ f ∈ K', r f = ν) ∧
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
          ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
            (∀ h : H, g h = σ (f h)) → ∀ a : A₁, r g a = σ (r f a)) ∧
        Nat.card (B →ₐ[↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))] ↥P) = p ^ s ∧
        (∀ f ∈ K', ∀ g ∈ K',
          WithConv.toConv (q (f * g)) = WithConv.toConv (q f) * WithConv.toConv (q g)) ∧
        (∀ f ∈ K', (WithConv.toConv (q f) = 1 ↔ f ∈ K)) ∧
        (∀ b : B →ₐ[↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))] ↥P, ∃ f ∈ K', q f = b) ∧
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
          ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
            (∀ h : H, g h = σ (f h)) → ∀ x : B,
              ((q g x : ↥P) : AlgebraicClosure ℚ) = σ ((q f x : ↥P) : AlgebraicClosure ℚ)) ∧
        (∀ f ∈ K', ∀ b : B,
          ((q f b : ↥P) : AlgebraicClosure ℚ) = r f (e.symm ((1 : ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))) ⊗ₜ[↥(P.comap (algebraMap ↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))] b))) :=
  HopfAlgebra.StepOrder.main P hp hMp K K' hKK' hK hK' s hcard hiP hDVR hirr

end S_HopfAlgebra_exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step
end P2MW
export P2MW.S_HopfAlgebra_exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step (solution)
