-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.specMap_nsmulAlgHom_comp_eq_comp_schemeNsmul_of_forall_point_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/ddfb9c3e-8e21-5d7a-a644-f385629bdacd

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_specMap_nsmulAlgHom_comp_eq_comp_schemeNsmul_of_forall_point_mul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)

    (Rh : Type) [CommRing Rh] {h : ℕ} (𝒢 : PDivisibleGroup Rh p h)
    (ρh : R p →+* Rh) (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
    (hS1 : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
    (hS5 : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.Point B v)
          (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
          (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
          Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v =
            (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1)
    (v n : ℕ) :
    Spec.map (CommRingCat.ofHom (PDivisibleGroup.Hopf.nsmulAlgHom Rh (𝒢.level v) n : 𝒢.level v →+* 𝒢.level v)) ≫ ι v =
      ι v ≫ O.L.schemeNsmul n := by
  classical

  set t' : Spec (CommRingCat.of (𝒢.level v)) ⟶ _ :=
    Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh) with ht'def
  have ht' : ι v ≫ O.g = t' := hS1 v
  let pt : SchemeHomOver t' O.g := ⟨ι v, ht'⟩

  have hover : ∀ φ : 𝒢.level v →ₐ[Rh] 𝒢.level v,
      (Spec.map (CommRingCat.ofHom (φ : 𝒢.level v →+* 𝒢.level v)) ≫ ι v) ≫ O.g = t' := by
    intro φ
    rw [Category.assoc, ht', ht'def, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact φ.comp_algebraMap

  let x : 𝒢.Point (𝒢.level v) v := PDivisibleGroup.Point.ofAlgHom (AlgHom.id Rh (𝒢.level v))
  have hxpow : ∀ m : ℕ, (PDivisibleGroup.Point.toAlgHom (x ^ m) : 𝒢.level v →ₐ[Rh] 𝒢.level v) =
      PDivisibleGroup.Hopf.nsmulAlgHom Rh (𝒢.level v) m := by
    intro m
    rw [PDivisibleGroup.Point.toAlgHom_pow]
    exact AlgHom.id_comp _

  have hone : (⟨Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (1 : 𝒢.Point (𝒢.level v) v) :
      𝒢.level v →ₐ[Rh] 𝒢.level v) : 𝒢.level v →+* 𝒢.level v)) ≫ ι v, hover _⟩ : SchemeHomOver t' O.g) = O.L.one t' := by
    set e : SchemeHomOver t' O.g := ⟨Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (1 : 𝒢.Point (𝒢.level v) v) :
      𝒢.level v →ₐ[Rh] 𝒢.level v) : 𝒢.level v →+* 𝒢.level v)) ≫ ι v, hover _⟩ with hedef
    have hee : e = O.L.mul t' e e := by
      apply Subtype.ext
      have := hS5 v (𝒢.level v) 1 1 (hover _) (hover _)
      rw [mul_one] at this
      exact this
    calc e = O.L.mul t' (O.L.one t') e := (O.L.one_mul t' e).symm
      _ = O.L.mul t' (O.L.mul t' (O.L.inv t' e) e) e := by rw [O.L.inv_mul_cancel]
      _ = O.L.mul t' (O.L.inv t' e) (O.L.mul t' e e) := by rw [O.L.mul_assoc]
      _ = O.L.mul t' (O.L.inv t' e) e := by rw [← hee]
      _ = O.L.one t' := O.L.inv_mul_cancel t' e

  have hclaim : ∀ m : ℕ, (⟨Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x ^ m) :
      𝒢.level v →ₐ[Rh] 𝒢.level v) : 𝒢.level v →+* 𝒢.level v)) ≫ ι v, hover _⟩ : SchemeHomOver t' O.g) = O.L.nsmul t' m pt := by
    intro m
    induction m with
    | zero =>
      rw [O.L.nsmul_zero]
      simpa only [pow_zero] using hone
    | succ m ih =>
      rw [O.L.nsmul_succ, ← ih]
      apply Subtype.ext
      have h5 := hS5 v (𝒢.level v) (x ^ m) x (hover _) (hover _)
      have hx1 : (⟨Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] 𝒢.level v) :
          𝒢.level v →+* 𝒢.level v)) ≫ ι v, hover _⟩ : SchemeHomOver t' O.g) = pt := by
        apply Subtype.ext
        show Spec.map (CommRingCat.ofHom ((AlgHom.id Rh (𝒢.level v) : 𝒢.level v →ₐ[Rh] 𝒢.level v) : 𝒢.level v →+* 𝒢.level v)) ≫ ι v = ι v
        rw [show CommRingCat.ofHom ((AlgHom.id Rh (𝒢.level v) : 𝒢.level v →ₐ[Rh] 𝒢.level v) : 𝒢.level v →+* 𝒢.level v) = 𝟙 _ from rfl,
          Spec.map_id, Category.id_comp]
      rw [hx1] at h5
      simpa only [pow_succ] using h5

  have hL : Spec.map (CommRingCat.ofHom (PDivisibleGroup.Hopf.nsmulAlgHom Rh (𝒢.level v) n : 𝒢.level v →+* 𝒢.level v)) ≫ ι v =
      (O.L.nsmul t' n pt).1 := by
    rw [← hclaim n]
    show _ = Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x ^ n) : 𝒢.level v →ₐ[Rh] 𝒢.level v) : 𝒢.level v →+* 𝒢.level v)) ≫ ι v
    rw [hxpow]
  have hR : ι v ≫ O.L.schemeNsmul n = (O.L.nsmul t' n pt).1 := by
    have hnat := O.L.nsmul_natural O.g t' (ι v) ht' n RelativeGroupLaw.idPoint
    have hpt : schemeHomOverComp (ι v) ht' (RelativeGroupLaw.idPoint : SchemeHomOver O.g O.g) = pt := by
      apply Subtype.ext
      exact Category.comp_id _
    rw [hpt] at hnat
    rw [← hnat]
    rfl
  rw [hL, hR]

end S_ModularCurve_JHNeronObjectAtP_specMap_nsmulAlgHom_comp_eq_comp_schemeNsmul_of_forall_point_mul
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_specMap_nsmulAlgHom_comp_eq_comp_schemeNsmul_of_forall_point_mul (solution)
