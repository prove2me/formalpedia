-- Prove2me | solution 1 for ModularCurve.LevelModuliPackageAbs.existsUnique_map_comp_univ_eq_and_exists_comp_eq_of_factorsThrough
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e36e1b3a-9dd7-59ae-8b88-d197fda2d358

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_existsUnique_map_comp_univ_eq_and_exists_comp_eq_of_factorsThrough

set_option autoImplicit false

universe u

p2m_open "ModularCurve P2MW.S_ModularCurve_LevelModuliPackageAbs_existsUnique_map_comp_univ_eq_and_exists_comp_eq_of_factorsThrough.ModularCurve IsLocalRing"

namespace ModularCurve
p2m_export "ModularCurve" "LevelModuliDatum LevelModuliPackageAbs"
namespace LevelModuliPackageAbs
p2m_export "ModularCurve.LevelModuliPackageAbs" "classify map_classify classify_unique B₀ univ represents"
namespace ProRepAux
p2m_open "ModularCurve.LevelModuliPackageAbs ModularCurve"

variable {A : Type u} [CommRing A] {D : LevelModuliDatum.{u} A} (P : LevelModuliPackageAbs A D)

theorem classify_map_univ {T : Type u} [CommRing T] [Algebra A T] (φ : P.B₀ →ₐ[A] T) :
    P.classify (D.map φ P.univ) = φ :=
  (P.classify_unique (D.map φ P.univ) φ rfl).symm

theorem algHom_eq_of_map_univ_eq {T : Type u} [CommRing T] [Algebra A T] (φ ψ : P.B₀ →ₐ[A] T)
    (h : D.map φ P.univ = D.map ψ P.univ) : φ = ψ :=
  (P.classify_unique (D.map ψ P.univ) φ h).trans (P.classify_unique (D.map ψ P.univ) ψ rfl).symm

end ModularCurve.LevelModuliPackageAbs.ProRepAux

open ModularCurve.LevelModuliPackageAbs.ProRepAux in
theorem solution
    {A : Type u} [CommRing A] {D : LevelModuliDatum.{u} A} (P : LevelModuliPackageAbs A D)

    (R : Type u) [CommRing R] [Algebra A R] (ι : P.B₀ →ₐ[A] R)
    (k : Type u) [CommRing k] (resR : R →+* k)
    (W₀ : Type u) [CommRing W₀] (res₀ : W₀ →+* k) [Algebra W₀ R] [Algebra A W₀] [IsScalarTower A W₀ R]

    (hfac : ∀ (T : Type u) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        [Algebra A T] [IsScalarTower A W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ φ : P.B₀ →ₐ[A] T, (∀ b : P.B₀, resT (φ b) = resR (ι b)) →
          ∃! Φ : R →ₐ[W₀] T, (∀ r : R, resT (Φ r) = resR r) ∧ ∀ b : P.B₀, Φ (ι b) = φ b)

    (T : Type u) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T] [Algebra A T]
    [IsScalarTower A W₀ T]
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (hresT₀ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) :

    (∀ y : D.Pt T, (∀ b : P.B₀, resT (P.classify y b) = resR (ι b)) →
      ∃! Φ : R →ₐ[W₀] T, (∀ r : R, resT (Φ r) = resR r) ∧ D.map ((Φ.restrictScalars A).comp ι) P.univ = y) ∧
    (∀ Φ : R →ₐ[W₀] T, (∀ r : R, resT (Φ r) = resR r) →
      ∀ b : P.B₀, resT (P.classify (D.map ((Φ.restrictScalars A).comp ι) P.univ) b) = resR (ι b)) ∧

    (∀ (T' : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [Algebra W₀ T'] [Algebra A T']
        [IsScalarTower A W₀ T'] (resT' : T' →+* k), Function.Surjective resT' →
        RingHom.ker resT' = maximalIdeal T' → (∀ w : W₀, resT' (algebraMap W₀ T' w) = res₀ w) →
      ∀ π : T' →ₐ[W₀] T, (∀ t : T', resT (π t) = resT' t) →
      ∀ g : R →ₐ[W₀] T, (∀ r : R, resT (g r) = resR r) →
      ∀ y' : D.Pt T', D.map (π.restrictScalars A) y' = D.map ((g.restrictScalars A).comp ι) P.univ →
        ∃ g' : R →ₐ[W₀] T', (∀ r : R, resT' (g' r) = resR r) ∧ π.comp g' = g ∧
          D.map ((g'.restrictScalars A).comp ι) P.univ = y') ∧

    (∀ [Algebra A k] (ρT : T →ₐ[A] k) (ρ : P.B₀ →ₐ[A] k), (∀ t : T, ρT t = resT t) →
      (∀ b : P.B₀, ρ b = resR (ι b)) →
      ∀ y : D.Pt T, (∀ b : P.B₀, resT (P.classify y b) = resR (ι b)) ↔ D.map ρT y = D.map ρ P.univ) := by
  refine ⟨?_, ?_, ?_, ?_⟩

  · intro y hy
    obtain ⟨Φ, ⟨hΦres, hΦι⟩, hΦuniq⟩ := hfac T resT hresT hkerT hresT₀ (P.classify y) hy
    have hcomp : (Φ.restrictScalars A).comp ι = P.classify y := by
      apply AlgHom.ext
      intro b
      exact hΦι b
    refine ⟨Φ, ⟨hΦres, ?_⟩, ?_⟩
    · rw [hcomp, P.map_classify]
    · rintro Ψ ⟨hΨres, hΨy⟩
      apply hΦuniq
      refine ⟨hΨres, fun b => ?_⟩
      have h := P.classify_unique y ((Ψ.restrictScalars A).comp ι) hΨy
      exact congrArg (fun χ : P.B₀ →ₐ[A] T => χ b) h

  · intro Φ hΦ b
    rw [classify_map_univ]
    exact hΦ (ι b)

  · intro T' _ _ _ _ _ _ resT' hresT' hkerT' hresT'₀ π hπ g hg y' hy'

    set φ' : P.B₀ →ₐ[A] T' := P.classify y' with hφ'def
    have hπφ' : (π.restrictScalars A).comp φ' = (g.restrictScalars A).comp ι := by
      apply algHom_eq_of_map_univ_eq P
      rw [D.map_comp, P.map_classify, hy']
    have hφ'res : ∀ b : P.B₀, resT' (φ' b) = resR (ι b) := by
      intro b
      rw [← hπ, ← hg (ι b)]
      exact congrArg resT (congrArg (fun χ : P.B₀ →ₐ[A] T => χ b) hπφ')
    obtain ⟨g', ⟨hg'res, hg'ι⟩, -⟩ := hfac T' resT' hresT' hkerT' hresT'₀ φ' hφ'res

    obtain ⟨Φ, -, hΦuniq⟩ := hfac T resT hresT hkerT hresT₀ ((g.restrictScalars A).comp ι) (fun b => hg (ι b))
    have h1 : π.comp g' = Φ := by
      apply hΦuniq
      refine ⟨fun r => ?_, fun b => ?_⟩
      · rw [AlgHom.comp_apply, hπ, hg'res]
      · rw [AlgHom.comp_apply, hg'ι]
        exact congrArg (fun χ : P.B₀ →ₐ[A] T => χ b) hπφ'
    have h2 : g = Φ := hΦuniq g ⟨hg, fun _ => rfl⟩
    refine ⟨g', hg'res, h1.trans h2.symm, ?_⟩
    have hcomp : (g'.restrictScalars A).comp ι = φ' := by
      apply AlgHom.ext
      intro b
      exact hg'ι b
    rw [hcomp, hφ'def, P.map_classify]

  · intro _ ρT ρ hρT hρ y
    constructor
    · intro hy
      have hcomp : ρT.comp (P.classify y) = ρ := by
        apply AlgHom.ext
        intro b
        rw [AlgHom.comp_apply, hρT, hρ]
        exact hy b
      conv_lhs => rw [← P.map_classify y]
      rw [← D.map_comp, hcomp]
    · intro h b
      have hcomp : ρT.comp (P.classify y) = ρ := by
        apply algHom_eq_of_map_univ_eq P
        rw [D.map_comp, P.map_classify, h]
      rw [← hρT, ← hρ, ← hcomp, AlgHom.comp_apply]

end S_ModularCurve_LevelModuliPackageAbs_existsUnique_map_comp_univ_eq_and_exists_comp_eq_of_factorsThrough
end P2MW
export P2MW.S_ModularCurve_LevelModuliPackageAbs_existsUnique_map_comp_univ_eq_and_exists_comp_eq_of_factorsThrough (solution)
