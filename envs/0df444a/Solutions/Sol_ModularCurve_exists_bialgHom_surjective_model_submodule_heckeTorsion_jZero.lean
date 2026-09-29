-- Prove2me | solution 1 for ModularCurve.exists_bialgHom_surjective_model_submodule_heckeTorsion_jZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/b9ac4a35-9857-5589-8873-63cef309dba5

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Flat

import Theorems.Thm_HopfAlgebra_exists_finiteFlat_pointClosure_of_isGaloisInvariant_rat_algebraicClosure
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_bialgHom_surjective_model_submodule_heckeTorsion_jZero

set_option autoImplicit false
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open ModularCurve in

theorem solution
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (𝔪 : Ideal HeckeAlg)
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (e : letI := heckeModuleBar N
      WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥(heckeTorsion (JZero N) 𝔪))
    (he_add : letI := heckeModuleBar N
      ∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), e (f * g) = e f + e g)
    (he_gal : letI := heckeModuleBar N
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ h : H, g h = σ (f h)) →
          ((e g : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N) = σ • ((e f : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N))
    (φ : HeckeAlg → (H →ₐ[GaloisRep.ratLocalizedAt p] H))
    (hφ : letI := heckeModuleBar N
      ∀ (t : HeckeAlg) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ h : H, g h = f (φ t h)) → ((e g : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N) = t • ((e f : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N))
    (hsmc : letI := heckeModuleBar N
      SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero N))
    (V : letI := heckeModuleBar N; Submodule (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (JZero N) 𝔪))
    (hV : letI := heckeModuleBar N; haveI := hsmc
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ↥(heckeTorsion (JZero N) 𝔪)),
        v ∈ V → mTorsionGaloisRep (JZero N) 𝔪 σ v ∈ V) :
    letI := heckeModuleBar N
    ∃ (HV : Type) (_ : CommRing HV) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) HV)
      (_ : Module.Finite (GaloisRep.ratLocalizedAt p) HV)
      (_ : Module.Free (GaloisRep.ratLocalizedAt p) HV)
      (_ : Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) HV)
      (π : H →ₐc[GaloisRep.ratLocalizedAt p] HV)
      (eV : WithConv (HV →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥V)
      (φV : HeckeAlg → (HV →ₐ[GaloisRep.ratLocalizedAt p] HV)),
      Function.Surjective π ∧
      (∀ f : WithConv (HV →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        ((eV f : ↥V) : ↥(heckeTorsion (JZero N) 𝔪)) =
          e (WithConv.toConv
            ((WithConv.ofConv f).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV)))) ∧
      (∀ t : HeckeAlg,
        (φV t).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV) =
          (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV).comp (φ t)) := by
  classical
  letI := heckeModuleBar N
  haveI := hsmc

  haveI hPID : IsPrincipalIdealRing ↥(GaloisRep.ratLocalizedAt p) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
  haveI hDVR : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  haveI : FaithfulSMul ↥(GaloisRep.ratLocalizedAt p) ℚ :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  haveI : IsFractionRing ↥(GaloisRep.ratLocalizedAt p) ℚ := by
    refine IsFractionRing.of_field _ _ (fun z => ?_)
    refine ⟨⟨(z.num : ℚ), ?_⟩, ⟨(z.den : ℚ), ?_⟩, ?_⟩
    · show ((z.num : ℚ)).den.Coprime p
      simp
    · show ((z.den : ℚ)).den.Coprime p
      simp
    · change z = (z.num : ℚ) / (z.den : ℚ)
      exact (Rat.num_div_den z).symm

  have he_one : e 1 = 0 := by
    have h := he_add 1 1
    rw [mul_one] at h
    exact left_eq_add.mp h
  let Γ : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) :=
    { carrier := {f | e f ∈ V}
      mul_mem' := fun {f g} hf hg => by
        show e (f * g) ∈ V
        rw [he_add]; exact V.add_mem hf hg
      one_mem' := by show e 1 ∈ V; rw [he_one]; exact V.zero_mem }
  have hΓ : ∀ f, f ∈ Γ ↔ e f ∈ V := fun f => Iff.rfl
  have hgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (ν : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)), ν ∈ Γ →
      WithConv.toConv (((σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).restrictScalars
        (GaloisRep.ratLocalizedAt p)).comp (WithConv.ofConv ν)) ∈ Γ := by
    intro σ ν hν
    set g := WithConv.toConv (((σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).restrictScalars
        (GaloisRep.ratLocalizedAt p)).comp (WithConv.ofConv ν)) with hg
    have hcoe : ((e g : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N) = σ • ((e ν : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N) :=
      he_gal σ ν g (fun h => rfl)
    have hmem := hV σ (e ν) hν
    have : e g = mTorsionGaloisRep (JZero N) 𝔪 σ (e ν) := by
      apply Subtype.ext
      rw [hcoe, coe_mTorsionGaloisRep_apply]
    show e g ∈ V
    rw [this]; exact hmem

  obtain ⟨HV, _, _, π, hπ, hfin, hflat, hcocomm, hker, hfac⟩ :=
    HopfAlgebra.exists_finiteFlat_pointClosure_of_isGaloisInvariant_rat_algebraicClosure
      (GaloisRep.ratLocalizedAt p) H Γ hgal
  haveI := hfin
  haveI := hflat
  haveI := hcocomm
  haveI : Module.Free ↥(GaloisRep.ratLocalizedAt p) HV := Module.free_of_flat_of_isLocalRing

  have hfac' : ∀ φ' : H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ,
      (∃ ψ : HV →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ,
        ψ.comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV) = φ') ↔ WithConv.toConv φ' ∈ Γ := by
    intro φ'
    have h := hfac (AlgebraicClosure ℚ) (AlgHom.id _ _) Function.injective_id φ'
    rwa [AlgHom.id_comp] at h

  let ev : WithConv (HV →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → ↥V := fun f =>
    ⟨e (WithConv.toConv ((WithConv.ofConv f).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV))),
      (hfac' _).mp ⟨WithConv.ofConv f, rfl⟩⟩
  have hev_inj : Function.Injective ev := by
    intro f₁ f₂ h
    have h1 := congrArg (fun v : ↥V => WithConv.ofConv (e.symm (v : ↥(heckeTorsion (JZero N) 𝔪)))) h
    simp only [ev, Equiv.symm_apply_apply, WithConv.ofConv_toConv] at h1
    have h2 := (AlgHom.cancel_right hπ).mp h1
    exact WithConv.ofConv_injective h2
  have hev_surj : Function.Surjective ev := by
    intro v
    have hv : e.symm (v : ↥(heckeTorsion (JZero N) 𝔪)) ∈ Γ := by
      show e (e.symm _) ∈ V
      rw [Equiv.apply_symm_apply]; exact v.2
    obtain ⟨ψ, hψ⟩ := (hfac' (WithConv.ofConv (e.symm (v : ↥(heckeTorsion (JZero N) 𝔪))))).mpr
      (by simpa only [WithConv.toConv_ofConv] using hv)
    refine ⟨WithConv.toConv ψ, ?_⟩
    apply Subtype.ext
    simp only [ev, WithConv.ofConv_toConv, hψ, WithConv.toConv_ofConv, Equiv.apply_symm_apply]
  let eV : WithConv (HV →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥V := Equiv.ofBijective ev ⟨hev_inj, hev_surj⟩

  have hkerφ : ∀ t : HeckeAlg, RingHom.ker (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV).toRingHom ≤
      RingHom.ker ((π : H →ₐ[GaloisRep.ratLocalizedAt p] HV).comp (φ t)).toRingHom := by
    intro t x hx
    have hx' : x ∈ RingHom.ker π := hx
    rw [hker] at hx'
    show π (φ t x) = 0
    have : φ t x ∈ RingHom.ker π := by
      rw [hker]
      simp only [Submodule.mem_iInf, Ideal.mem_iInf, RingHom.mem_ker] at hx' ⊢
      intro ν hν
      let g := WithConv.toConv ((WithConv.ofConv ν).comp (φ t))
      have hcoe : ((e g : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N) = t • ((e ν : ↥(heckeTorsion (JZero N) 𝔪)) : JZero N) :=
        hφ t ν g (fun h => rfl)
      have hmemV := V.smul_mem (Ideal.Quotient.mk 𝔪 t) hν
      have hg : g ∈ Γ := by
        show e g ∈ V
        convert hmemV using 1
        apply Subtype.ext
        rw [hcoe]; rfl
      exact hx' g hg
    exact this
  let φV : HeckeAlg → (HV →ₐ[GaloisRep.ratLocalizedAt p] HV) := fun t =>
    AlgHom.liftOfSurjective (π : H →ₐ[GaloisRep.ratLocalizedAt p] HV) hπ
      ((π : H →ₐ[GaloisRep.ratLocalizedAt p] HV).comp (φ t)) (hkerφ t)
  refine ⟨HV, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, π, eV, φV, hπ, ?_, ?_⟩
  · intro f; rfl
  · intro t
    ext x
    simp only [φV, AlgHom.comp_apply, AlgHom.liftOfSurjective_apply]

end S_ModularCurve_exists_bialgHom_surjective_model_submodule_heckeTorsion_jZero
end P2MW
export P2MW.S_ModularCurve_exists_bialgHom_surjective_model_submodule_heckeTorsion_jZero (solution)
