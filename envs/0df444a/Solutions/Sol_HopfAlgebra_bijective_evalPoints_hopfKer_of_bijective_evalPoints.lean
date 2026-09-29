-- Prove2me | solution 1 for HopfAlgebra.bijective_evalPoints_hopfKer_of_bijective_evalPoints
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/a4a7d20f-60c5-5d16-848f-56508dfc1bff

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_bijective_evalPoints_hopfKer_of_bijective_evalPoints

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem solution
    (K : Type u) [Field K]
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
    (Ā : Type v) [CommRing Ā] [HopfAlgebra K Ā] (π : A →ₐc[K] Ā) (hπ : Function.Surjective π)
    (hker₁ : ∀ h : ↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K,
        ∃ ν : WithConv (A →ₐ[K] AlgebraicClosure K), (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val = h)
    (hker₂ : ∀ ν ν' : WithConv (A →ₐ[K] AlgebraicClosure K),
        (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val = (WithConv.ofConv ν').comp (HopfAlgebra.hopfKer π).val
          ↔ ∃ w ∈ W, ν' = ν * w)
    (hrank : Module.finrank K ↥(HopfAlgebra.hopfKer π) * Nat.card ↥W = Module.finrank K A) :
    ∃ (_ : Finite (WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K))),
      Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure K) (WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
        (Pi.algHom K _
          fun ν : WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : ↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure K ⊗[K] ↥(HopfAlgebra.hopfKer π) →ₐ[AlgebraicClosure K]
          (WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)) := by
  classical
  set Ω := AlgebraicClosure K with hΩ
  set C : Subalgebra K A := HopfAlgebra.hopfKer π with hC

  have hS1 : Module.finrank K A = Nat.card (WithConv (A →ₐ[K] Ω)) := by
    letI : Fintype (WithConv (A →ₐ[K] Ω)) := Fintype.ofFinite _
    let eS := LinearEquiv.ofBijective (Algebra.TensorProduct.lift
      (Algebra.ofId Ω (WithConv (A →ₐ[K] Ω) → Ω))
      (Pi.algHom K _ fun ν : WithConv (A →ₐ[K] Ω) => (WithConv.ofConv ν : A →ₐ[K] Ω))
      (fun _ _ => Commute.all _ _) : Ω ⊗[K] A →ₐ[Ω] (WithConv (A →ₐ[K] Ω) → Ω)).toLinearMap hev
    have h1 : Module.finrank Ω (Ω ⊗[K] A) = Module.finrank K A := Module.finrank_baseChange
    rw [← h1, eS.finrank_eq, Module.finrank_pi, Nat.card_eq_fintype_card]

  let res : WithConv (A →ₐ[K] Ω) → WithConv (↥C →ₐ[K] Ω) :=
    fun ν => WithConv.toConv ((WithConv.ofConv ν).comp C.val)
  have hres : Function.Surjective res := by
    intro h
    obtain ⟨ν, hν⟩ := hker₁ (WithConv.ofConv h)
    exact ⟨ν, by simp [res, hν]⟩

  haveI hfinC : Finite (WithConv (↥C →ₐ[K] Ω)) := Finite.of_surjective res hres
  refine ⟨hfinC, ?_⟩
  letI : Fintype (WithConv (A →ₐ[K] Ω)) := Fintype.ofFinite _
  letI : Fintype (WithConv (↥C →ₐ[K] Ω)) := Fintype.ofFinite _

  have hunit : ∀ ν : WithConv (A →ₐ[K] Ω), IsUnit ν := by
    intro ν
    let ψ : A →ₐ[K] Ω := WithConv.ofConv ν
    let Sa : A →ₐ[K] A := AlgHom.ofLinearMap (HopfAlgebra.antipode K) HopfAlgebra.antipode_one
      (fun a b => by rw [HopfAlgebra.antipode_mul, mul_comm])
    have hlin : (Algebra.TensorProduct.lift ψ (ψ.comp Sa) (fun _ _ => Commute.all _ _)).toLinearMap
        = ψ.toLinearMap ∘ₗ (LinearMap.mul' K A ∘ₗ (HopfAlgebra.antipode K).lTensor A) := by
      apply TensorProduct.ext'
      intro a b
      simp [Sa, LinearMap.mul'_apply]
    have hmul : ν * WithConv.toConv (ψ.comp Sa) = 1 := by
      apply WithConv.ofConv_injective
      apply AlgHom.ext
      intro c
      rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
      have hx := LinearMap.congr_fun hlin (Coalgebra.comul c)
      simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply,
        HopfAlgebra.mul_antipode_lTensor_comul_apply] at hx
      rw [WithConv.ofConv_toConv]
      exact hx.trans (ψ.commutes _)
    have hlin' : (Algebra.TensorProduct.lift (ψ.comp Sa) ψ (fun _ _ => Commute.all _ _)).toLinearMap
        = ψ.toLinearMap ∘ₗ (LinearMap.mul' K A ∘ₗ (HopfAlgebra.antipode K).rTensor A) := by
      apply TensorProduct.ext'
      intro a b
      simp [Sa, LinearMap.mul'_apply]
    have hmul' : WithConv.toConv (ψ.comp Sa) * ν = 1 := by
      apply WithConv.ofConv_injective
      apply AlgHom.ext
      intro c
      rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
      have hx := LinearMap.congr_fun hlin' (Coalgebra.comul c)
      simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply,
        HopfAlgebra.mul_antipode_rTensor_comul_apply] at hx
      rw [WithConv.ofConv_toConv]
      exact hx.trans (ψ.commutes _)
    exact ⟨⟨ν, WithConv.toConv (ψ.comp Sa), hmul, hmul'⟩, rfl⟩

  have hsec : ∀ c : WithConv (↥C →ₐ[K] Ω), ∃ ν, res ν = c := hres
  choose s hs using hsec
  have hfib : ∀ ν : WithConv (A →ₐ[K] Ω), ∃! w : ↥W, ν = s (res ν) * (w : WithConv (A →ₐ[K] Ω)) := by
    intro ν
    have h0 : (WithConv.ofConv (s (res ν))).comp C.val = (WithConv.ofConv ν).comp C.val := by
      have := hs (res ν)
      simpa [res] using congrArg WithConv.ofConv this
    obtain ⟨w, hwW, hw⟩ := (hker₂ (s (res ν)) ν).mp h0
    refine ⟨⟨w, hwW⟩, hw, ?_⟩
    rintro ⟨w', hw'W⟩ hw'
    apply Subtype.ext
    have : s (res ν) * w = s (res ν) * w' := hw.symm.trans hw'
    exact ((hunit (s (res ν))).mul_right_inj).mp this |>.symm ▸ rfl
  have hcardB : Nat.card (WithConv (A →ₐ[K] Ω)) = Nat.card (WithConv (↥C →ₐ[K] Ω)) * Nat.card ↥W := by
    rw [← Nat.card_prod]
    refine Nat.card_congr
      { toFun := fun ν => (res ν, (hfib ν).choose)
        invFun := fun cw => s cw.1 * (cw.2 : WithConv (A →ₐ[K] Ω))
        left_inv := fun ν => ((hfib ν).choose_spec.1).symm
        right_inv := fun cw => ?_ }
    obtain ⟨c, w⟩ := cw
    have hrc : res (s c * (w : WithConv (A →ₐ[K] Ω))) = c := by
      have h1 : (WithConv.ofConv (s c)).comp C.val = (WithConv.ofConv (s c * (w : WithConv (A →ₐ[K] Ω)))).comp C.val :=
        (hker₂ (s c) (s c * w)).mpr ⟨w, w.2, rfl⟩
      calc res (s c * (w : WithConv (A →ₐ[K] Ω))) = res (s c) := congrArg WithConv.toConv h1.symm
        _ = c := hs c
    refine Prod.ext hrc ?_

    have hu := (hfib (s c * (w : WithConv (A →ₐ[K] Ω)))).choose_spec.2 w (by rw [hrc])
    simpa using hu.symm

  have hWpos : 0 < Nat.card ↥W := Nat.card_pos_iff.mpr ⟨⟨⟨1, W.one_mem⟩⟩, inferInstance⟩
  have hrankC : Module.finrank K ↥C = Nat.card (WithConv (↥C →ₐ[K] Ω)) := by
    have h := hrank
    rw [hS1, hcardB] at h
    exact Nat.eq_of_mul_eq_mul_right hWpos h

  set evC := Algebra.TensorProduct.lift
      (Algebra.ofId Ω (WithConv (↥C →ₐ[K] Ω) → Ω))
      (Pi.algHom K _ fun ν : WithConv (↥C →ₐ[K] Ω) => (WithConv.ofConv ν : ↥C →ₐ[K] Ω))
      (fun _ _ => Commute.all _ _) with hevC
  set evB := Algebra.TensorProduct.lift
      (Algebra.ofId Ω (WithConv (A →ₐ[K] Ω) → Ω))
      (Pi.algHom K _ fun ν : WithConv (A →ₐ[K] Ω) => (WithConv.ofConv ν : A →ₐ[K] Ω))
      (fun _ _ => Commute.all _ _) with hevBdef
  let incl : Ω ⊗[K] ↥C →ₐ[Ω] Ω ⊗[K] A := Algebra.TensorProduct.map (AlgHom.id Ω Ω) C.val
  let pull : (WithConv (↥C →ₐ[K] Ω) → Ω) →ₐ[Ω] (WithConv (A →ₐ[K] Ω) → Ω) :=
    Pi.algHom Ω _ fun ν => Pi.evalAlgHom Ω (fun _ => Ω) (res ν)
  have hsq : evB.comp incl = pull.comp evC := by
    apply Algebra.TensorProduct.ext
    · ext
    · apply AlgHom.ext; intro c; funext ν
      simp [evB, evC, incl, pull, res, Algebra.TensorProduct.lift_tmul]
  have hincl : Function.Injective incl := by
    have : Function.Injective (C.val.toLinearMap.lTensor Ω) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    intro x y hxy
    apply this
    simp [incl] at hxy
    exact hxy
  have hinjC : Function.Injective evC := by
    intro x y hxy
    apply hincl
    apply hev.1
    have := congrArg (fun f => f x) (congrArg DFunLike.coe hsq)
    have h' := congrArg (fun f => f y) (congrArg DFunLike.coe hsq)
    simp only [AlgHom.coe_comp, Function.comp_apply] at this h'
    rw [this, h', hxy]
  have hdim : Module.finrank Ω (Ω ⊗[K] ↥C) = Module.finrank Ω (WithConv (↥C →ₐ[K] Ω) → Ω) := by
    rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card, hrankC, Nat.card_eq_fintype_card]
  exact ⟨hinjC, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    (show Function.Injective evC.toLinearMap from hinjC)⟩

end S_HopfAlgebra_bijective_evalPoints_hopfKer_of_bijective_evalPoints
end P2MW
export P2MW.S_HopfAlgebra_bijective_evalPoints_hopfKer_of_bijective_evalPoints (solution)
