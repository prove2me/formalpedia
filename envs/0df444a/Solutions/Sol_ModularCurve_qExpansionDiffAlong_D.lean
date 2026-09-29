-- Prove2me | solution 1 for ModularCurve.qExpansionDiffAlong_D
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/90d112d9-1e4c-5e79-8b0a-6ab7292a3918

import Definitions.Def_ModularCurve_QExpansionDiff
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpansionDiffAlong_D

set_option autoImplicit false

p2m_open "HahnSeries ModularCurve P2MW.S_ModularCurve_qExpansionDiffAlong_D.ModularCurve AlgebraicCurve P2MW.S_ModularCurve_qExpansionDiffAlong_D.AlgebraicCurve"

private theorem thetaL_coeff {L : Type*} [Field L] (f : LaurentSeries L) (n : ℤ) :
    (thetaL L f).coeff n = n • f.coeff n := by
  rw [thetaL_apply, HahnSeries.coeff_single_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff, one_mul]
  simp

private theorem thetaL_support_subset {L : Type*} [Field L] (f : LaurentSeries L) : (thetaL L f).support ⊆ f.support := by
  intro n hn
  rw [HahnSeries.mem_support, thetaL_coeff] at hn
  rw [HahnSeries.mem_support]
  intro h
  exact hn (by rw [h, smul_zero])

private theorem thetaL_mul {L : Type*} [Field L] (f g : LaurentSeries L) : thetaL L (f * g) = thetaL L f * g + f * thetaL L g := by
  ext n
  rw [thetaL_coeff, HahnSeries.coeff_mul, HahnSeries.coeff_add, Finset.smul_sum,
    HahnSeries.coeff_mul_left' f.isPWO_support (thetaL_support_subset f),
    HahnSeries.coeff_mul_right' g.isPWO_support (thetaL_support_subset g),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  rw [thetaL_coeff, thetaL_coeff, ← hij.2.2, add_smul, smul_mul_assoc, mul_smul_comm]

namespace ModularCurve p2m_export "ModularCurve" "thetaL thetaL_apply IsQExpansionDiffAlong qExpansionDiffAlong" end ModularCurve
p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.algebraMap_laurentSeries_mul {K L : Type*} [Field K] [Field L] [Algebra K L] (k : K) (x : LaurentSeries L) : algebraMap K (LaurentSeries L) k * x = k • x := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C,
    HahnSeries.C_mul_eq_smul, algebraMap_smul]

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.exists_isQExpansionDiffAlong {K F L : Type*} [Field K] [Field F] [Algebra K F] [Field L] [Algebra K L] (σ : F →ₐ[K] LaurentSeries L) : ∃ φ : Ω[F⁄K] →ₗ[K] LaurentSeries L, IsQExpansionDiffAlong σ φ := by
  letI instF : Module F (LaurentSeries L) := Module.compHom (LaurentSeries L) (σ : F →+* LaurentSeries L)
  haveI : IsScalarTower K F (LaurentSeries L) :=
    ⟨fun k f x => by
      change σ (k • f) * x = k • (σ f * x)
      rw [Algebra.smul_def k f, map_mul, σ.commutes, mul_assoc, algebraMap_laurentSeries_mul]⟩
  let d₀ : F →ₗ[K] LaurentSeries L :=
    { toFun := fun f => thetaL L (σ f)
      map_add' := fun a b => by rw [map_add, map_add]
      map_smul' := fun k f => by
        rw [RingHom.id_apply, Algebra.smul_def k f, map_mul, σ.commutes, algebraMap_laurentSeries_mul,
          ← algebraMap_smul (A := L) k (σ f), ← algebraMap_smul (A := L) k (thetaL L (σ f)),
          map_smul] }
  let d : Derivation K F (LaurentSeries L) :=
    Derivation.mk' d₀ fun a b => by
      change thetaL L (σ (a * b)) = σ a * thetaL L (σ b) + σ b * thetaL L (σ a)
      rw [map_mul, thetaL_mul, mul_comm (thetaL L (σ a)) (σ b), add_comm]
  refine ⟨{ toFun := d.liftKaehlerDifferential
            map_add' := fun ω₁ ω₂ => map_add _ ω₁ ω₂
            map_smul' := fun k ω => ?_ }, fun x => ?_, fun f ω => ?_⟩
  · rw [RingHom.id_apply, ← algebraMap_smul (A := F) k ω, map_smul]
    change σ (algebraMap K F k) * _ = _
    rw [σ.commutes, algebraMap_laurentSeries_mul]
  · exact d.liftKaehlerDifferential_comp_D x
  · change d.liftKaehlerDifferential (f • ω) = σ f * d.liftKaehlerDifferential ω
    rw [map_smul]
    rfl

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.isQExpansionDiffAlong_qExpansionDiffAlong {K F L : Type*} [Field K] [Field F] [Algebra K F] [Field L] [Algebra K L] (σ : F →ₐ[K] LaurentSeries L) : IsQExpansionDiffAlong σ (qExpansionDiffAlong σ) := by
  unfold qExpansionDiffAlong
  rw [dif_pos (exists_isQExpansionDiffAlong σ)]
  exact (exists_isQExpansionDiffAlong σ).choose_spec

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.qExpansionDiffAlong_D {K F L : Type*} [Field K] [Field F] [Algebra K F] [Field L] [Algebra K L] (σ : F →ₐ[K] LaurentSeries L) (x : F) : qExpansionDiffAlong σ (KaehlerDifferential.D K F x) = thetaL L (σ x) :=
  (isQExpansionDiffAlong_qExpansionDiffAlong σ).1 x

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.qExpansionDiffAlong_smul {K F L : Type*} [Field K] [Field F] [Algebra K F] [Field L] [Algebra K L] (σ : F →ₐ[K] LaurentSeries L) (f : F) (ω : Ω[F⁄K]) : qExpansionDiffAlong σ (f • ω) = σ f * qExpansionDiffAlong σ ω :=
  (isQExpansionDiffAlong_qExpansionDiffAlong σ).2 f ω

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.isQExpansionDiffAlong_unique {K F L : Type*} [Field K] [Field F] [Algebra K F] [Field L] [Algebra K L] (σ : F →ₐ[K] LaurentSeries L) {φ ψ : Ω[F⁄K] →ₗ[K] LaurentSeries L} (hφ : IsQExpansionDiffAlong σ φ) (hψ : IsQExpansionDiffAlong σ ψ) : φ = ψ := by
  apply LinearMap.ext
  intro ω
  have hω : ω ∈ Submodule.span F (Set.range (KaehlerDifferential.D K F)) := by
    rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
  induction hω using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨x, rfl⟩ := hx
    rw [hφ.1, hψ.1]
  | zero => rw [map_zero, map_zero]
  | add _ _ _ _ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | smul f _ _ h => rw [hφ.2, hψ.2, h]

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.eq_qExpansionDiffAlong_of_isQExpansionDiffAlong {K F L : Type*} [Field K] [Field F] [Algebra K F] [Field L] [Algebra K L] (σ : F →ₐ[K] LaurentSeries L) {φ : Ω[F⁄K] →ₗ[K] LaurentSeries L} (hφ : IsQExpansionDiffAlong σ φ) : φ = qExpansionDiffAlong σ :=
  isQExpansionDiffAlong_unique σ hφ (isQExpansionDiffAlong_qExpansionDiffAlong σ)

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "IsTraceDiff traceDiff" end AlgebraicCurve
p2m_open_scoped "AlgebraicCurve" in
open TensorProduct in
private theorem AlgebraicCurve.exists_isTraceDiff (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsSeparable F F'] : ∃ t : Ω[F'⁄K] →ₗ[F] Ω[F⁄K], IsTraceDiff K F F' t := by
  haveI := Algebra.FormallyEtale.of_isSeparable F F'
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F'
  let g : F' ⊗[F] Ω[F⁄K] →ₗ[F] Ω[F⁄K] :=
    TensorProduct.lift ((LinearMap.lsmul F Ω[F⁄K]).comp (Algebra.trace F F'))
  refine ⟨g.comp (e.symm.toLinearMap.restrictScalars F), fun y ω => ?_⟩
  have he : e.symm (y • KaehlerDifferential.map K K F F' ω) = y ⊗ₜ[F] ω := by
    rw [LinearEquiv.symm_apply_eq]
    simp [e]
  simp [he, g]

p2m_open_scoped "AlgebraicCurve" in
private theorem AlgebraicCurve.isTraceDiff_traceDiff (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsSeparable F F'] : IsTraceDiff K F F' (traceDiff K F F') := by
  unfold traceDiff
  rw [dif_pos (exists_isTraceDiff K F F')]
  exact (exists_isTraceDiff K F F').choose_spec

p2m_open_scoped "AlgebraicCurve" in
private theorem AlgebraicCurve.traceDiff_apply (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsSeparable F F'] (y : F') (ω : Ω[F⁄K]) : traceDiff K F F' (y • KaehlerDifferential.map K K F F' ω) = Algebra.trace F F' y • ω :=
  isTraceDiff_traceDiff K F F' y ω

p2m_open_scoped "AlgebraicCurve" in
private theorem AlgebraicCurve.isTraceDiff_unique (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsSeparable F F'] {t₁ t₂ : Ω[F'⁄K] →ₗ[F] Ω[F⁄K]} (h₁ : IsTraceDiff K F F' t₁) (h₂ : IsTraceDiff K F F' t₂) : t₁ = t₂ := by
  haveI := Algebra.FormallyEtale.of_isSeparable F F'
  apply LinearMap.ext
  intro η
  obtain ⟨z, rfl⟩ := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F').surjective η
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul y ω =>
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul, h₁, h₂]
  | add z₁ z₂ hz₁ hz₂ => rw [map_add, map_add, map_add, hz₁, hz₂]

p2m_open_scoped "AlgebraicCurve" in
private theorem AlgebraicCurve.eq_traceDiff_of_isTraceDiff (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsSeparable F F'] {t : Ω[F'⁄K] →ₗ[F] Ω[F⁄K]} (ht : IsTraceDiff K F F' t) : t = traceDiff K F F' :=
  isTraceDiff_unique K F F' ht (isTraceDiff_traceDiff K F F')

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.qExpansionDiffAlong_map {K F F' L : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Field L] [Algebra K L] (σ : F' →ₐ[K] LaurentSeries L) (ω : Ω[F⁄K]) : qExpansionDiffAlong σ (KaehlerDifferential.map K K F F' ω) = qExpansionDiffAlong (σ.comp (IsScalarTower.toAlgHom K F F')) ω := by
  have h : IsQExpansionDiffAlong (σ.comp (IsScalarTower.toAlgHom K F F'))
      ((qExpansionDiffAlong σ).comp ((KaehlerDifferential.map K K F F').restrictScalars K)) := by
    refine ⟨fun x => ?_, fun f ω => ?_⟩
    · rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, KaehlerDifferential.map_D,
        qExpansionDiffAlong_D, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
    · rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.map_smul,
        ← algebraMap_smul (A := F') f (KaehlerDifferential.map K K F F' ω), qExpansionDiffAlong_smul,
        AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', LinearMap.comp_apply,
        LinearMap.restrictScalars_apply]
  exact LinearMap.congr_fun (eq_qExpansionDiffAlong_of_isQExpansionDiffAlong _ h) ω

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.qExpansionDiffAlong_smul_map {K F F' L : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Field L] [Algebra K L] (σ : F' →ₐ[K] LaurentSeries L) (h : F') (ω : Ω[F⁄K]) : qExpansionDiffAlong σ (h • KaehlerDifferential.map K K F F' ω) = σ h * qExpansionDiffAlong (σ.comp (IsScalarTower.toAlgHom K F F')) ω := by
  rw [qExpansionDiffAlong_smul, qExpansionDiffAlong_map]

p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.qExpansionDiffAlong_smul_map_D {K F F' L : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Field L] [Algebra K L] (σ : F' →ₐ[K] LaurentSeries L) (h : F') (x : F) : qExpansionDiffAlong σ (h • KaehlerDifferential.map K K F F' (KaehlerDifferential.D K F x)) = σ h * thetaL L (σ (algebraMap F F' x)) := by
  rw [qExpansionDiffAlong_smul_map, qExpansionDiffAlong_D, AlgHom.comp_apply,
    IsScalarTower.coe_toAlgHom']

theorem solution {K F L : Type*} [Field K] [Field F] [Algebra K F] [Field L] [Algebra K L] (σ : F →ₐ[K] LaurentSeries L) (x : F) : qExpansionDiffAlong σ (KaehlerDifferential.D K F x) = thetaL L (σ x) :=
  ModularCurve.qExpansionDiffAlong_D σ x

#print axioms solution

end S_ModularCurve_qExpansionDiffAlong_D
end P2MW
export P2MW.S_ModularCurve_qExpansionDiffAlong_D (solution)
