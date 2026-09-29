-- Prove2me | solution 1 for ModularCurve.JZeroNeronPrimaryTorsionFlag.ringEquiv_apply_algHom_eq_convPow_of_range_eq_hopfKer_of_kind_eq_mult
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/50893ba3-c35c-5989-82c8-79b1ad9e4be1

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_bialgHom_toAlgHom_eq_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_ringEquiv_apply_algHom_eq_convPow_of_range_eq_hopfKer_of_kind_eq_mult

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory

set_option autoImplicit false

open scoped TensorProduct

namespace S17BlockD

def algHomInt {A B : Type*} [Ring A] [Ring B] [Algebra ℤ A] [Algebra ℤ B] (f : A →+* B) : A →ₐ[ℤ] B :=
  AlgHom.mk' f (fun c x => by rw [Algebra.smul_def, Algebra.smul_def, map_mul, eq_intCast, eq_intCast, map_intCast])

@[scoped simp] theorem algHomInt_apply {A B : Type*} [Ring A] [Ring B] [Algebra ℤ A] [Algebra ℤ B] (f : A →+* B) (x : A) :
    algHomInt f x = f x := rfl

theorem nonempty_algHom_of_finiteType (L B : Type*) [Field L] [IsAlgClosed L] [CommRing B] [Algebra L B]
    [Algebra.FiniteType L B] [Nontrivial B] : Nonempty (B →ₐ[L] L) := by
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal B
  letI : Field (B ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (inferInstance : Algebra.FiniteType L B)
  have hsurj : Function.Surjective ((Ideal.Quotient.mkₐ L 𝔪).comp f) :=
    (Ideal.Quotient.mkₐ_surjective L 𝔪).comp hf
  have halg : Algebra.IsAlgebraic L (B ⧸ 𝔪) := by
    rw [Algebra.isAlgebraic_iff_isIntegral, ← algebraMap_isIntegral_iff]
    have h := MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing
      (((Ideal.Quotient.mkₐ L 𝔪).comp f : MvPolynomial (Fin n) L →ₐ[L] B ⧸ 𝔪) : MvPolynomial (Fin n) L →+* B ⧸ 𝔪)
      hsurj
    have e : (((Ideal.Quotient.mkₐ L 𝔪).comp f : MvPolynomial (Fin n) L →ₐ[L] B ⧸ 𝔪) :
        MvPolynomial (Fin n) L →+* B ⧸ 𝔪).comp MvPolynomial.C = algebraMap L (B ⧸ 𝔪) := by
      ext x
      simp
    rwa [e] at h
  exact ⟨(IsAlgClosed.lift : B ⧸ 𝔪 →ₐ[L] L).comp (Ideal.Quotient.mkₐ L 𝔪)⟩

theorem exists_ringHom_of_faithfullyFlat {R G : Type*} [CommRing R] [CommRing G] [Algebra R G]
    [Algebra.FiniteType R G] (K' : Subalgebra R G) [Module.FaithfullyFlat ↥K' G]
    (L : Type*) [Field L] [IsAlgClosed L] (φ : ↥K' →+* L) :
    ∃ g : G →+* L, ∀ x : ↥K', g x = φ x := by
  letI : Algebra ↥K' L := φ.toAlgebra
  haveI : Algebra.FiniteType ↥K' G := Algebra.FiniteType.of_restrictScalars_finiteType R ↥K' G
  haveI : Nontrivial (L ⊗[↥K'] G) :=
    (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_left (↥K') L).2 inferInstance
  obtain ⟨pt⟩ := nonempty_algHom_of_finiteType L (L ⊗[↥K'] G)
  refine ⟨(pt : L ⊗[↥K'] G →+* L).comp
    ((Algebra.TensorProduct.includeRight : G →ₐ[↥K'] L ⊗[↥K'] G) : G →+* L ⊗[↥K'] G), fun x => ?_⟩
  change pt (Algebra.TensorProduct.includeRight (R := ↥K') (A := L) (x : G)) = φ x
  have hx : (x : G) = algebraMap ↥K' G x := rfl
  rw [hx, AlgHom.commutes, IsScalarTower.algebraMap_apply ↥K' L (L ⊗[↥K'] G), AlgHom.commutes]
  rfl

section Conv
variable {R : Type*} [CommRing R] {C D A : Type*} [CommRing C] [Bialgebra R C] [CommRing D] [Bialgebra R D]
  [CommRing A] [Algebra R A]

theorem convPow_comp_bialgHom (f : WithConv (C →ₐ[R] A)) (h : D →ₐc[R] C) (n : ℕ) :
    (f ^ n).ofConv.comp (h : D →ₐ[R] C) = (WithConv.toConv (f.ofConv.comp (h : D →ₐ[R] C)) ^ n).ofConv := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, AlgHom.convOne_def (R := R) (A := A) (C := C),
        AlgHom.convOne_def (R := R) (A := A) (C := D), WithConv.ofConv_toConv, WithConv.ofConv_toConv,
        AlgHom.comp_assoc, BialgHom.counitAlgHom_comp]
  | succ n ih =>
      rw [pow_succ, pow_succ, AlgHom.convMul_comp_bialgHom_distrib, ih, WithConv.toConv_ofConv]

theorem eq_of_comp_eq_of_surjective {B : Type*} [CommRing B] [Algebra R B] (π : B →ₐ[R] C)
    (hπ : Function.Surjective π) (f g : WithConv (C →ₐ[R] A))
    (h : f.ofConv.comp π = g.ofConv.comp π) : f = g := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro y
  obtain ⟨x, rfl⟩ := hπ y
  exact DFunLike.congr_fun h x

end Conv

theorem apply_eq_algebraMap_counit_of_mem_hopfKer {R : Type*} [CommRing R] {A B : Type*} [CommRing A]
    [Bialgebra R A] [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B) {x : A} (hx : x ∈ HopfAlgebra.hopfKer π) :
    π x = algebraMap R B (Coalgebra.counit (R := R) x) := by
  have h := HopfAlgebra.coaction_eq_of_mem π hx
  rw [HopfAlgebra.coaction_apply] at h

  have key : ∀ z : A ⊗[R] A,
      TensorProduct.lid R B ((Coalgebra.counit (R := R) (A := A)).rTensor B
        (Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] B) z)) =
      TensorProduct.lid R B (((π : A →ₐ[R] B).toLinearMap).lTensor R ((Coalgebra.counit (R := R) (A := A)).rTensor A z)) := by
    intro z
    induction z with
    | zero => simp
    | tmul a b => simp
    | add z w hz hw => simp only [map_add, hz, hw]
  have h2 := congrArg (fun z => TensorProduct.lid R B ((Coalgebra.counit (R := R) (A := A)).rTensor B z)) h
  rw [key, ← LinearMap.comp_apply (f := (Coalgebra.counit (R := R) (A := A)).rTensor A),
    Coalgebra.rTensor_counit_comp_comul] at h2
  simpa [Algebra.algebraMap_eq_smul_one] using h2

theorem toConv_comp_comp_eq_one {R : Type*} [CommRing R] {A B C T : Type*} [CommRing A] [Bialgebra R A]
    [CommRing B] [Bialgebra R B] [CommRing C] [Bialgebra R C] [CommRing T] [Algebra R T]
    (π : A →ₐc[R] B) (j : C →ₐc[R] A) (hj : ∀ x, j x ∈ HopfAlgebra.hopfKer π) (gb : B →ₐ[R] T) :
    WithConv.toConv ((gb.comp (π : A →ₐ[R] B)).comp (j : C →ₐ[R] A)) = (1 : WithConv (C →ₐ[R] T)) := by
  rw [AlgHom.convOne_def]
  congr 1
  apply AlgHom.ext
  intro x
  change gb (π (j x)) = algebraMap R T (Coalgebra.counit (R := R) x)
  rw [apply_eq_algebraMap_counit_of_mem_hopfKer π (hj x), AlgHom.commutes, CoalgHomClass.counit_comp_apply]

end S17BlockD
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_ringEquiv_apply_algHom_eq_convPow_of_range_eq_hopfKer_of_kind_eq_mult.S17BlockD"

set_option maxHeartbeats 1600000 in
open S17BlockD in
theorem solution
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m) (i : Fin flag.n)
    (hk : flag.kind i = JZeroFlagLayerKind.mult)
    (qc : flag.G i.succ →ₐc[ℤ] flag.G i.castSucc)
    (hqc : (qc : flag.G i.succ →ₐ[ℤ] flag.G i.castSucc) = flag.quot i)
    (K : Type) (_ : CommRing K) (_ : HopfAlgebra ℤ K)
    (j : K →ₐc[ℤ] flag.G i.succ) (hinj : Function.Injective j)
    (hrange : (j : K →ₐ[ℤ] flag.G i.succ).range = HopfAlgebra.hopfKer qc)
    (hflat : Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) (flag.G i.succ)) :
    ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (nσ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ) (k : K),
        σ (ψ k) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) k := by
  intro σ nσ hζ ψ k
  classical

  set Qb := AlgebraicClosure ℚ with hQb
  let G := flag.G i.succ
  let Gb := flag.G i.castSucc
  let π : C.H m →ₐ[ℤ] G := flag.π i.succ
  obtain ⟨πc, hπc⟩ := ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_bialgHom_toAlgHom_eq_pi p q A hA C m flag i.succ

  let K' : Subalgebra ℤ G := HopfAlgebra.hopfKer qc
  haveI : Module.FaithfullyFlat ↥K' G := hflat
  let eK : K ≃ₐ[ℤ] ↥K' :=
    (AlgEquiv.ofInjective (j : K →ₐ[ℤ] G) hinj).trans (Subalgebra.equivOfEq _ _ hrange)
  have heK : ∀ x : K, ((eK x : ↥K') : G) = j x := by intro x; rfl
  obtain ⟨g, hg'⟩ := exists_ringHom_of_faithfullyFlat K' Qb
    ((ψ : K →+* Qb).comp (eK.symm : ↥K' ≃ₐ[ℤ] K).toRingEquiv.toRingHom)

  let gA : G →ₐ[ℤ] Qb := algHomInt g
  have hgA : ∀ y, gA y = g y := fun y => rfl
  have hg : ∀ x : K, gA (j x) = ψ x := by
    intro x
    have h1 := hg' (eK x)
    rw [heK] at h1
    rw [hgA, h1]
    change ψ (eK.symm (eK x)) = ψ x
    rw [AlgEquiv.symm_apply_apply]
  let σg : G →ₐ[ℤ] Qb := algHomInt ((σ : Qb →+* Qb).comp g)
  have hσg : ∀ y, σg y = σ (gA y) := fun y => rfl

  let σ' : Qb ≃ₐ[ℚ] Qb := AlgEquiv.ofRingEquiv (f := σ) (fun x => RingHom.map_rat_algebraMap (σ : Qb →+* Qb) x)
  have hσ' : ∀ z, σ' z = σ z := fun z => rfl

  let f₀ : WithConv (C.H m →ₐ[ℤ] Qb) := WithConv.toConv (gA.comp π)
  let fσ : WithConv (C.H m →ₐ[ℤ] Qb) := WithConv.toConv (σg.comp π)

  have gP1 : C.genericPoints m (1 : WithConv (C.H m →ₐ[ℤ] Qb)) = 0 := by
    have h := C.genericConv m 1 1
    rw [mul_one] at h
    exact left_eq_add.mp h
  have gPpow : ∀ (f : WithConv (C.H m →ₐ[ℤ] Qb)) (n : ℕ),
      C.genericPoints m (f ^ n) = n • C.genericPoints m f := by
    intro f n
    induction n with
    | zero => rw [pow_zero, zero_nsmul]; exact gP1
    | succ n ih => rw [pow_succ, C.genericConv, ih, succ_nsmul]

  have hx : ((C.genericPoints m f₀ : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p) ∈ flag.genericStep i.succ :=
    (flag.genericStep_pin i.succ _).2 ⟨gA, rfl⟩
  have hζ' : ∀ ζ : Qb, ζ ^ q = 1 → σ' ζ = ζ ^ nσ := fun ζ hz => by rw [hσ']; exact hζ ζ hz
  have hact := flag.layerAction_mult i hk σ' nσ hζ' _ hx

  have h1 : ((C.genericPoints m fσ : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)
      = σ' • ((C.genericPoints m f₀ : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p) :=
    C.genericGalois m σ' f₀ fσ (fun h => rfl)
  have h2 : ((C.genericPoints m (f₀ ^ nσ) : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)
      = nσ • ((C.genericPoints m f₀ : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p) := by
    rw [gPpow, AddSubgroupClass.coe_nsmul]
  rw [← h1, ← h2] at hact
  obtain ⟨gb, hgb⟩ := (flag.genericStep_pin i.castSucc _).1 hact

  have hπ' : flag.π i.castSucc = ((qc : G →ₐ[ℤ] Gb).comp π) := by
    rw [hqc]; exact (flag.quot_π i).symm
  rw [hπ'] at hgb
  have h3 : C.genericPoints m (WithConv.toConv ((gb.comp (qc : G →ₐ[ℤ] Gb)).comp π) * f₀ ^ nσ)
      = C.genericPoints m fσ := by
    apply Subtype.ext
    have := hgb
    rw [C.genericConv]
    push_cast
    rw [← AlgHom.comp_assoc] at this
    rw [this]
    abel
  have h4 : WithConv.toConv ((gb.comp (qc : G →ₐ[ℤ] Gb)).comp π) * f₀ ^ nσ = fσ :=
    (C.genericPoints m).injective h3

  have h5 : (WithConv.toConv (gb.comp (qc : G →ₐ[ℤ] Gb)) * WithConv.toConv gA ^ nσ :
      WithConv (G →ₐ[ℤ] Qb)) = WithConv.toConv σg := by
    apply eq_of_comp_eq_of_surjective (πc : C.H m →ₐ[ℤ] G) (by rw [hπc]; exact flag.π_surj i.succ)
    rw [AlgHom.convMul_comp_bialgHom_distrib, WithConv.ofConv_toConv, convPow_comp_bialgHom,
      WithConv.ofConv_toConv, WithConv.toConv_ofConv, WithConv.ofConv_toConv, hπc]

    have := congrArg WithConv.ofConv h4
    simp only [f₀, fσ, WithConv.ofConv_toConv] at this
    exact this

  have h6 := congrArg (fun t : WithConv (G →ₐ[ℤ] Qb) => t.ofConv.comp (j : K →ₐ[ℤ] G)) h5
  simp only [WithConv.ofConv_toConv] at h6
  rw [AlgHom.convMul_comp_bialgHom_distrib, WithConv.ofConv_toConv, convPow_comp_bialgHom,
    WithConv.ofConv_toConv, WithConv.toConv_ofConv] at h6

  have hunit : WithConv.toConv ((gb.comp (qc : G →ₐ[ℤ] Gb)).comp (j : K →ₐ[ℤ] G)) = (1 : WithConv (K →ₐ[ℤ] Qb)) :=
    toConv_comp_comp_eq_one qc j (fun x => by rw [← hrange]; exact ⟨x, rfl⟩) gb
  have hgj : gA.comp (j : K →ₐ[ℤ] G) = ψ := AlgHom.ext hg
  rw [hunit, one_mul, hgj] at h6

  have h7 := DFunLike.congr_fun h6 k
  have h8 : (σg.comp (j : K →ₐ[ℤ] G)) k = σ (ψ k) := by
    rw [← hg k]
    rfl
  exact (h7.trans h8).symm

end S_ModularCurve_JZeroNeronPrimaryTorsionFlag_ringEquiv_apply_algHom_eq_convPow_of_range_eq_hopfKer_of_kind_eq_mult
end P2MW
export P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_ringEquiv_apply_algHom_eq_convPow_of_range_eq_hopfKer_of_kind_eq_mult (solution)
