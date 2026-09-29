-- Prove2me | solution 1 for IsIntegrallyClosed.integralClosure_eq_adjoin_and_etale_and_finite_of_eq_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/02043bde-375c-5ee4-8a9c-e03c856d0bce

import Mathlib
import Theorems.Thm_AdjoinRoot_etale_and_finite_X_pow_sub_C_of_isUnit
import Theorems.Thm_IsIntegrallyClosed_integralClosure_eq_adjoin_root_X_pow_sub_C_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsIntegrallyClosed_integralClosure_eq_adjoin_and_etale_and_finite_of_eq_mul_pow

set_option autoImplicit false

open Polynomial

namespace KummerLocalKb

variable {B F : Type*} [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
  [Field F] [Algebra B F] [IsFractionRing B F]

variable (F) in

noncomputable abbrev fv (k : ℕ) (v : B) : F[X] := X ^ k - C (algebraMap B F v)

noncomputable abbrev fB (k : ℕ) (v : B) : B[X] := X ^ k - C v

noncomputable abbrev fg (k : ℕ) (g : F) : F[X] := X ^ k - C g

theorem root_fv_pow (k : ℕ) (v : B) :
    (AdjoinRoot.root (fv F k v)) ^ k = algebraMap F (AdjoinRoot (fv F k v)) (algebraMap B F v) := by
  have h := AdjoinRoot.eval₂_root (fv F k v)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [sub_eq_zero] at h
  exact h

theorem root_fg_pow (k : ℕ) (g : F) :
    (AdjoinRoot.root (fg k g)) ^ k = algebraMap F (AdjoinRoot (fg k g)) g := by
  have h := AdjoinRoot.eval₂_root (fg k g)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [sub_eq_zero] at h
  exact h

noncomputable def ψ₁ (k : ℕ) (v : B) : AdjoinRoot (fB k v) →ₐ[B] AdjoinRoot (fv F k v) :=
  AdjoinRoot.liftAlgHom (fB k v) (Algebra.ofId B (AdjoinRoot (fv F k v))) (AdjoinRoot.root (fv F k v)) (by
    change (fB k v).eval₂ (algebraMap B (AdjoinRoot (fv F k v))) (AdjoinRoot.root (fv F k v)) = 0
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, root_fv_pow, sub_eq_zero]
    rw [IsScalarTower.algebraMap_apply B F (AdjoinRoot (fv F k v))])

theorem ψ₁_root (k : ℕ) (v : B) : ψ₁ (F := F) k v (AdjoinRoot.root (fB k v)) = AdjoinRoot.root (fv F k v) := by
  simp [ψ₁]

theorem ψ₁_mk (k : ℕ) (v : B) (p : B[X]) :
    ψ₁ (F := F) k v (AdjoinRoot.mk (fB k v) p) = AdjoinRoot.mk (fv F k v) (p.map (algebraMap B F)) := by
  rw [ψ₁, AdjoinRoot.coe_liftAlgHom, AdjoinRoot.lift_mk, ← AdjoinRoot.aeval_eq, Polynomial.aeval_map_algebraMap,
    Polynomial.aeval_def]
  rfl

theorem ψ₁_injective (k : ℕ) (v : B) (hk0 : k ≠ 0) : Function.Injective (ψ₁ (F := F) k v) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  have hmonic : (fB k v).Monic := Polynomial.monic_X_pow_sub_C v hk0

  have hred : AdjoinRoot.mk (fB k v) p = AdjoinRoot.mk (fB k v) (p %ₘ fB k v) := by
    rw [AdjoinRoot.mk_eq_mk]
    refine ⟨p /ₘ fB k v, ?_⟩
    have := Polynomial.modByMonic_add_div p (fB k v)
    rw [sub_eq_iff_eq_add, add_comm, this]
  rw [hred] at hx ⊢
  set r := p %ₘ fB k v with hr
  have hdeg : r.degree < (k : WithBot ℕ) := by
    have h1 := Polynomial.degree_modByMonic_lt p hmonic
    rwa [Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero hk0)] at h1
  rw [ψ₁_mk, AdjoinRoot.mk_eq_zero] at hx
  have hzero : r.map (algebraMap B F) = 0 := by
    refine Polynomial.eq_zero_of_dvd_of_degree_lt hx ?_
    rw [Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero hk0)]
    exact lt_of_le_of_lt (Polynomial.degree_map_le) hdeg
  have hr0 : r = 0 := by
    rw [Polynomial.map_eq_zero_iff (IsFractionRing.injective B F)] at hzero
    exact hzero
  rw [hr0, map_zero]

theorem ψ₁_range (k : ℕ) (v : B) :
    (ψ₁ (F := F) k v).range = Algebra.adjoin B {AdjoinRoot.root (fv F k v)} := by
  rw [← Algebra.map_top, ← AdjoinRoot.adjoinRoot_eq_top, AlgHom.map_adjoin, Set.image_singleton, ψ₁_root]

section Twist

variable (k : ℕ) (v : B) (h : F) (g : F)

noncomputable def α (hh : h ≠ 0) (hg : g = algebraMap B F v * h ^ k) :
    AdjoinRoot (fv F k v) →ₐ[F] AdjoinRoot (fg k g) :=
  AdjoinRoot.liftAlgHom (fv F k v) (Algebra.ofId F (AdjoinRoot (fg k g)))
    (algebraMap F (AdjoinRoot (fg k g)) h⁻¹ * AdjoinRoot.root (fg k g)) (by
      change (fv F k v).eval₂ (algebraMap F (AdjoinRoot (fg k g))) _ = 0
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero]
      rw [mul_pow, root_fg_pow, ← map_pow, ← map_mul]
      congr 1
      rw [hg, inv_pow, ← mul_assoc, mul_comm (h ^ k)⁻¹, mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hh), mul_one])

noncomputable def β (hg : g = algebraMap B F v * h ^ k) :
    AdjoinRoot (fg k g) →ₐ[F] AdjoinRoot (fv F k v) :=
  AdjoinRoot.liftAlgHom (fg k g) (Algebra.ofId F (AdjoinRoot (fv F k v)))
    (algebraMap F (AdjoinRoot (fv F k v)) h * AdjoinRoot.root (fv F k v)) (by
      change (fg k g).eval₂ (algebraMap F (AdjoinRoot (fv F k v))) _ = 0
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero]
      rw [mul_pow, root_fv_pow, ← map_pow, ← map_mul, hg, mul_comm])

theorem α_root (hh : h ≠ 0) (hg : g = algebraMap B F v * h ^ k) :
    α k v h g hh hg (AdjoinRoot.root (fv F k v)) =
      algebraMap F (AdjoinRoot (fg k g)) h⁻¹ * AdjoinRoot.root (fg k g) := by
  simp [α]

theorem β_root (hg : g = algebraMap B F v * h ^ k) :
    β k v h g hg (AdjoinRoot.root (fg k g)) =
      algebraMap F (AdjoinRoot (fv F k v)) h * AdjoinRoot.root (fv F k v) := by
  simp [β]

noncomputable def τ (hh : h ≠ 0) (hg : g = algebraMap B F v * h ^ k) :
    AdjoinRoot (fv F k v) ≃ₐ[F] AdjoinRoot (fg k g) :=
  AlgEquiv.ofAlgHom (α k v h g hh hg) (β k v h g hg)
    (by
      apply AdjoinRoot.algHom_ext
      rw [AlgHom.comp_apply, β_root, map_mul, AlgHom.commutes, α_root, ← mul_assoc, ← map_mul,
        mul_inv_cancel₀ hh, map_one, one_mul, AlgHom.coe_id, id_eq])
    (by
      apply AdjoinRoot.algHom_ext
      rw [AlgHom.comp_apply, α_root, map_mul, AlgHom.commutes, β_root, ← mul_assoc, ← map_mul,
        inv_mul_cancel₀ hh, map_one, one_mul, AlgHom.coe_id, id_eq])

theorem τ_root (hh : h ≠ 0) (hg : g = algebraMap B F v * h ^ k) :
    τ k v h g hh hg (AdjoinRoot.root (fv F k v)) =
      algebraMap F (AdjoinRoot (fg k g)) h⁻¹ * AdjoinRoot.root (fg k g) := by
  simp [τ, α_root]

end Twist

theorem main (k : ℕ) (hk : IsUnit ((k : ℕ) : B)) (v : B) (hv : IsUnit v) (h : F) (hh : h ≠ 0) (g : F)
    (hg : g = algebraMap B F v * h ^ k) :
    integralClosure B (AdjoinRoot (fg k g)) =
        Algebra.adjoin B {algebraMap F (AdjoinRoot (fg k g)) h⁻¹ * AdjoinRoot.root (fg k g)} ∧
      Algebra.Etale B (integralClosure B (AdjoinRoot (fg k g))) ∧
      Module.Finite B (integralClosure B (AdjoinRoot (fg k g))) := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk

  have hKa : integralClosure B (AdjoinRoot (fv F k v)) = Algebra.adjoin B {AdjoinRoot.root (fv F k v)} :=
    IsIntegrallyClosed.integralClosure_eq_adjoin_root_X_pow_sub_C_of_isUnit k v hk hv

  set τB : AdjoinRoot (fv F k v) ≃ₐ[B] AdjoinRoot (fg k g) := (τ k v h g hh hg).restrictScalars B
  have hτB_root : τB (AdjoinRoot.root (fv F k v)) =
      algebraMap F (AdjoinRoot (fg k g)) h⁻¹ * AdjoinRoot.root (fg k g) := τ_root k v h g hh hg
  have h1 : integralClosure B (AdjoinRoot (fg k g)) =
      Algebra.adjoin B {algebraMap F (AdjoinRoot (fg k g)) h⁻¹ * AdjoinRoot.root (fg k g)} := by
    rw [← integralClosure_map_algEquiv τB, hKa, AlgHom.map_adjoin_singleton]
    change Algebra.adjoin B {τB (AdjoinRoot.root (fv F k v))} = _
    rw [hτB_root]

  have e₁ : AdjoinRoot (fB k v) ≃ₐ[B] (ψ₁ (F := F) k v).range :=
    AlgEquiv.ofInjective (ψ₁ k v) (ψ₁_injective k v hk0)
  have e₂ : (ψ₁ (F := F) k v).range ≃ₐ[B] Algebra.adjoin B {AdjoinRoot.root (fv F k v)} :=
    Subalgebra.equivOfEq _ _ (ψ₁_range k v)
  have e₃ : Algebra.adjoin B {AdjoinRoot.root (fv F k v)} ≃ₐ[B] integralClosure B (AdjoinRoot (fv F k v)) :=
    Subalgebra.equivOfEq _ _ hKa.symm
  have e₄ : integralClosure B (AdjoinRoot (fv F k v)) ≃ₐ[B] integralClosure B (AdjoinRoot (fg k g)) :=
    τB.mapIntegralClosure
  have e : AdjoinRoot (fB k v) ≃ₐ[B] integralClosure B (AdjoinRoot (fg k g)) :=
    e₁.trans (e₂.trans (e₃.trans e₄))

  obtain ⟨hE, hF⟩ := AdjoinRoot.etale_and_finite_X_pow_sub_C_of_isUnit k v hk hv
  haveI : Algebra.Etale B (AdjoinRoot (fB k v)) := hE
  haveI : Module.Finite B (AdjoinRoot (fB k v)) := hF
  exact ⟨h1, Algebra.Etale.of_equiv e, Module.Finite.equiv e.toLinearEquiv⟩

end KummerLocalKb

theorem solution
    {B F : Type*} [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Field F] [Algebra B F] [IsFractionRing B F]
    (k : ℕ) (hk : IsUnit (k : B)) (v : B) (hv : IsUnit v) (h : F) (hh : h ≠ 0) (g : F)
    (hg : g = algebraMap B F v * h ^ k) :
    integralClosure B (AdjoinRoot (X ^ k - C g : F[X])) =
        Algebra.adjoin B {algebraMap F (AdjoinRoot (X ^ k - C g : F[X])) h⁻¹ * AdjoinRoot.root (X ^ k - C g : F[X])} ∧
      Algebra.Etale B (integralClosure B (AdjoinRoot (X ^ k - C g : F[X]))) ∧
      Module.Finite B (integralClosure B (AdjoinRoot (X ^ k - C g : F[X]))) :=
  KummerLocalKb.main k hk v hv h hh g hg

end S_IsIntegrallyClosed_integralClosure_eq_adjoin_and_etale_and_finite_of_eq_mul_pow
end P2MW
export P2MW.S_IsIntegrallyClosed_integralClosure_eq_adjoin_and_etale_and_finite_of_eq_mul_pow (solution)
