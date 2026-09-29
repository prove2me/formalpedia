-- Prove2me | solution 1 for ModularCurve.raynaudFor_of_le_finiteFlat_model_eisensteinQuotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/4529c69e-95e0-5831-afbd-5963f5189895

import Theorems.Thm_GaloisRep_finiteFlat_point_eq_of_decomposition_fixed_of_valuation_sub_lt_one_of_pow_eq_one
import Definitions.Def_ModularCurve_StepThreeDoorPredicates
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_raynaudFor_of_le_finiteFlat_model_eisensteinQuotient

set_option autoImplicit false

open ModularCurve

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [NeZero p] (hcomm : HeckeOperatorsCommuteBar p)
    (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    {T : Type*} [AddCommGroup T] (sp : JZero p →+ T)
    (hmodel : letI := heckeModuleBar p
      ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt ℓ) H),
        Module.Finite (GaloisRep.ratLocalizedAt ℓ) H ∧ Module.Flat (GaloisRep.ratLocalizedAt ℓ) H ∧
        Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt ℓ) H ∧
        ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ) ≃
            ↥(Submodule.torsionBy ℤ (EisensteinQuotient p (heckeModuleBar p)) ((ℓ : ℤ) ^ n)),
          (∀ f g, e (f * g) = e f + e g) ∧
          (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
              (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ)),
            (∀ h : H, g h = σ (f h)) →
            ∀ x : JZero p, eisensteinQuotientMk p (heckeModuleBar p) x
                = (e f : EisensteinQuotient p (heckeModuleBar p)) →
              eisensteinQuotientMk p (heckeModuleBar p) (σ • x)
                = (e g : EisensteinQuotient p (heckeModuleBar p))) ∧
          (∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ),
            ((ℓ : ℤ) ^ k) • (e f : EisensteinQuotient p (heckeModuleBar p)) = 0 →
            (∀ x : JZero p, eisensteinQuotientMk p (heckeModuleBar p) x
                = (e f : EisensteinQuotient p (heckeModuleBar p)) → sp x ∈ spKernelImage sp) →
            ∀ h : H, A.valuation (f h - algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)
              (Coalgebra.counit h)) < 1)) :
    letI := heckeModuleBar p
    RaynaudFor ℓ sp := by
  intro hℓ2 z hz hk hsp
  letI instJ := heckeModuleBar p
  classical
  obtain ⟨k, hzk⟩ := hk
  obtain ⟨n, hkn, H, _, _, hHfin, hHflat, hHcocomm, e, he_add, he_act, he_red⟩ := hmodel k
  haveI := hHfin; haveI := hHflat; haveI := hHcocomm

  have hzk_int : ((ℓ : ℤ) ^ k) • z = 0 := by
    have : ((ℓ : ℤ) ^ k) • z = (ℓ ^ k : ℕ) • z := by
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    rw [this, hzk]

  have hz_tors : z ∈ Submodule.torsionBy ℤ (EisensteinQuotient p (heckeModuleBar p)) ((ℓ : ℤ) ^ n) := by
    rw [Submodule.mem_torsionBy_iff]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
    rw [pow_add, mul_comm, mul_smul, hzk_int]
    exact smul_zero _

  have he_one : e 1 = 0 := by
    have h := he_add 1 1
    rw [one_mul] at h
    exact left_eq_add.mp h
  have he_pow : ∀ (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ)) (n : ℕ), e (f ^ n) = n • e f := by
    intro f n
    induction n with
    | zero => rw [pow_zero, he_one, zero_smul]
    | succ n ih => rw [pow_succ, he_add, ih, succ_nsmul]
  have hord : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ), f ^ ℓ ^ n = 1 := by
    intro f
    apply e.injective
    have h1 : e (f ^ ℓ ^ n) = (ℓ ^ n) • e f := he_pow f (ℓ ^ n)
    have h2 : ((ℓ : ℤ) ^ n) • e f = 0 := Submodule.smul_torsionBy _ _
    have h3 : (ℓ ^ n : ℕ) • e f = ((ℓ : ℤ) ^ n) • e f := by
      rw [← Nat.cast_smul_eq_nsmul ℤ, Nat.cast_pow]
    rw [h1, he_one, h3, h2]

  let f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ) := e.symm ⟨z, hz_tors⟩
  have hef : (e f : EisensteinQuotient p (heckeModuleBar p)) = z := by
    simp [f]

  obtain ⟨x₀, hx₀inv, hx₀z⟩ := hz

  have hf_fix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ h : H, σ (f h) = f h := by
    intro σ h
    let g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ) :=
      WithConv.toConv (((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toAlgHom.restrictScalars
        (GaloisRep.ratLocalizedAt ℓ)).comp (WithConv.ofConv f))
    have hg : ∀ h : H, g h = σ (f h) := fun h => rfl
    have hmk : eisensteinQuotientMk p (heckeModuleBar p) (σ • x₀) = (e g : EisensteinQuotient p (heckeModuleBar p)) :=
      he_act σ f g hg x₀ (by rw [hef]; exact hx₀z)
    have hmk' : eisensteinQuotientMk p (heckeModuleBar p) (σ • x₀) = eisensteinQuotientMk p (heckeModuleBar p) x₀ := by
      have hsub := hx₀inv σ
      rw [← sub_eq_zero, ← map_sub]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hsub
    have hge : e g = e f := by
      apply Subtype.ext
      rw [← hmk, hmk', hx₀z, hef]
    have hgf : g = f := e.injective hge
    rw [← hg, hgf]

  have hone : ∀ h : H, (1 : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ)) h
      = algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) (Coalgebra.counit h) := fun h => rfl
  have h1_fix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ → ∀ h : H,
      σ ((1 : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ)) h)
        = (1 : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ)) h := by
    intro σ _ h
    rw [hone, IsScalarTower.algebraMap_apply (GaloisRep.ratLocalizedAt ℓ) ℚ (AlgebraicClosure ℚ), AlgEquiv.commutes]

  have hf_red : ∀ h : H, A.valuation (f h - (1 : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ)) h) < 1 := by
    intro h
    rw [hone]
    exact he_red f (by rw [hef]; exact hzk_int) (fun x hx => hsp x (by rw [hx, hef])) h

  have hf1 : f = 1 :=
    GaloisRep.finiteFlat_point_eq_of_decomposition_fixed_of_valuation_sub_lt_one_of_pow_eq_one ℓ hℓ2 A hA H n hord
      f 1 (fun σ _ h => hf_fix σ h) h1_fix hf_red
  rw [← hef, hf1, he_one]
  rfl

end S_ModularCurve_raynaudFor_of_le_finiteFlat_model_eisensteinQuotient
end P2MW
export P2MW.S_ModularCurve_raynaudFor_of_le_finiteFlat_model_eisensteinQuotient (solution)
