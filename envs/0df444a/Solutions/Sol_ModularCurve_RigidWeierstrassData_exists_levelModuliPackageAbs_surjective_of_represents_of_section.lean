-- Prove2me | solution 1 for ModularCurve.RigidWeierstrassData.exists_levelModuliPackageAbs_surjective_of_represents_of_section
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/1f27fd90-d54b-5fdb-936c-95bd432e948a

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_RigidWeierstrassData_exists_levelModuliPackageAbs_surjective_of_represents_of_section

set_option autoImplicit false

universe u

open ModularCurve

theorem solution
    {A : Type u} [CommRing A] (R : RigidWeierstrassData.{u} A)

    (C : Type u) [CommRing C] [Algebra A C] (xᵤ : R.Raw C)
    (hrep : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : R.Raw T),
        ∃! ψ : C →ₐ[A] T, R.mapRing ψ xᵤ = x)

    (hrigid : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : R.Raw T) (C : WeierstrassCurve.VariableChange T),
      R.act C x = x → C = 1)

    (NF : ∀ (T : Type u) [CommRing T] [Algebra A T], R.Raw T → Prop)
    (hNF_map : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (x : R.Raw T), NF T x → NF T' (R.mapRing f x))
    (hNF_sec : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : R.Raw T),
      ∃! C : WeierstrassCurve.VariableChange T, NF T (R.act C x)) :
    ∃ (P : LevelModuliPackageAbs A R.toLevelModuliDatum) (π : C →ₐ[A] P.B₀), Function.Surjective π := by
  classical

  let Cn : ∀ (T : Type u) [CommRing T] [Algebra A T], R.Raw T → WeierstrassCurve.VariableChange T :=
    fun T _ _ x => (hNF_sec T x).exists.choose
  have hCn : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : R.Raw T), NF T (R.act (Cn T x) x) :=
    fun T _ _ x => (hNF_sec T x).exists.choose_spec
  have hCu : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : R.Raw T) (C' : WeierstrassCurve.VariableChange T),
      NF T (R.act C' x) → C' = Cn T x := fun T _ _ x C' h => (hNF_sec T x).unique h (hCn T x)
  let ν : ∀ (T : Type u) [CommRing T] [Algebra A T], R.Raw T → R.Raw T := fun T _ _ x => R.act (Cn T x) x
  have hν : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : R.Raw T), ν T x = R.act (Cn T x) x := fun T _ _ x => rfl
  have hνNF : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : R.Raw T), NF T (ν T x) := hCn

  have hνfix : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : R.Raw T), NF T x → ν T x = x := by
    intro T _ _ x hx
    have : (1 : WeierstrassCurve.VariableChange T) = Cn T x := hCu T x 1 (by rw [R.act_one]; exact hx)
    rw [hν, ← this, R.act_one]

  have hνact : ∀ (T : Type u) [CommRing T] [Algebra A T] (C' : WeierstrassCurve.VariableChange T) (x : R.Raw T),
      ν T (R.act C' x) = ν T x := by
    intro T _ _ C' x
    have h1 : NF T (R.act (Cn T (R.act C' x) * C') x) := by rw [R.act_mul]; exact hCn T (R.act C' x)
    have := hCu T x _ h1
    rw [hν, hν, ← R.act_mul, this]

  have hνmap : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (x : R.Raw T), ν T' (R.mapRing f x) = R.mapRing f (ν T x) := by
    intro T T' _ _ _ _ f x
    have h1 : NF T' (R.act ((Cn T x).map f.toRingHom) (R.mapRing f x)) := by
      rw [← R.mapRing_act]; exact hNF_map T T' f _ (hCn T x)
    have := hCu T' (R.mapRing f x) _ h1
    rw [hν, hν, ← this, R.mapRing_act]

  have hνν : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : R.Raw T), ν T (ν T x) = ν T x :=
    fun T _ _ x => hνfix T _ (hνNF T x)
  have hrel : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : R.Raw T), R.Rel x (ν T x) :=
    fun T _ _ x => ⟨Cn T x, rfl⟩

  let νbar : ∀ (T : Type u) [CommRing T] [Algebra A T], R.Pt T → R.Raw T := fun T _ _ =>
    Quot.lift (ν T) (by rintro x y ⟨C', rfl⟩; exact (hνact T C' x).symm)
  have hνbar : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : R.Raw T), νbar T (Quot.mk _ x) = ν T x :=
    fun T _ _ x => rfl

  let ψ : ∀ (T : Type u) [CommRing T] [Algebra A T], R.Raw T → (C →ₐ[A] T) := fun T _ _ x => (hrep T x).exists.choose
  have hψ : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : R.Raw T), R.mapRing (ψ T x) xᵤ = x :=
    fun T _ _ x => (hrep T x).exists.choose_spec
  have hψu : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : R.Raw T) (φ : C →ₐ[A] T),
      R.mapRing φ xᵤ = x → φ = ψ T x := fun T _ _ x φ h => (hrep T x).unique h (hψ T x)

  let e : C →ₐ[A] C := ψ C (ν C xᵤ)
  have he : R.mapRing e xᵤ = ν C xᵤ := hψ C _
  have hcompe : ∀ (T : Type u) [CommRing T] [Algebra A T] (g : C →ₐ[A] T),
      R.mapRing (g.comp e) xᵤ = ν T (R.mapRing g xᵤ) := by
    intro T _ _ g
    rw [R.mapRing_comp, he, ← hνmap]

  let I : Ideal C := Ideal.span (Set.range fun c : C => e c - c)
  let π : C →ₐ[A] C ⧸ I := Ideal.Quotient.mkₐ A I
  have hπe : π.comp e = π := by
    apply AlgHom.ext; intro c
    show Ideal.Quotient.mk I (e c) = Ideal.Quotient.mk I c
    rw [Ideal.Quotient.eq]
    exact Ideal.subset_span ⟨c, rfl⟩
  have hfac : ∀ (T : Type u) [CommRing T] [Algebra A T] (g : C →ₐ[A] T), g.comp e = g →
      ∃ φ : C ⧸ I →ₐ[A] T, φ.comp π = g := by
    intro T _ _ g hg
    have hI : ∀ a ∈ I, g a = 0 := by
      intro a ha
      have : I ≤ RingHom.ker g.toRingHom := by
        rw [Ideal.span_le]
        rintro _ ⟨c, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker]
        show g (e c - c) = 0
        rw [map_sub, ← AlgHom.comp_apply, hg, sub_self]
      exact this ha
    refine ⟨Ideal.Quotient.liftₐ I g hI, ?_⟩
    apply AlgHom.ext; intro c; rfl

  refine ⟨{ B₀ := C ⧸ I
            univ := Quot.mk _ (R.mapRing π xᵤ)
            represents := ?_ }, π, Ideal.Quotient.mkₐ_surjective A I⟩
  intro T _ _ xbar
  induction xbar using Quot.ind with
  | mk x =>

    have hfix : (ψ T (ν T x)).comp e = ψ T (ν T x) := by
      apply hψu
      rw [hcompe, hψ, hνν]
    obtain ⟨φ, hφ⟩ := hfac T (ψ T (ν T x)) hfix
    have hmapφ : R.toLevelModuliDatum.map φ (Quot.mk _ (R.mapRing π xᵤ)) = Quot.mk _ x := by
      show R.map φ (Quot.mk _ (R.mapRing π xᵤ)) = Quot.mk _ x
      rw [R.map_mk, ← R.mapRing_comp, hφ, hψ]
      exact (Quot.sound (hrel T x)).symm
    refine ⟨φ, hmapφ, ?_⟩
    intro φ' hφ'

    have h1 : R.mapRing (φ'.comp π) xᵤ = ν T x := by
      have h2 : R.map φ' (Quot.mk _ (R.mapRing π xᵤ)) = Quot.mk _ x := hφ'
      rw [R.map_mk, ← R.mapRing_comp] at h2
      have h3 := congrArg (νbar T) h2
      rw [hνbar, hνbar] at h3

      rw [← h3, ← hcompe, AlgHom.comp_assoc, hπe]
    have h4 : φ'.comp π = φ.comp π := by
      rw [hψu T _ _ h1, hφ]
    apply AlgHom.ext
    intro b
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mkₐ_surjective A I b
    exact AlgHom.congr_fun h4 c

end S_ModularCurve_RigidWeierstrassData_exists_levelModuliPackageAbs_surjective_of_represents_of_section
end P2MW
export P2MW.S_ModularCurve_RigidWeierstrassData_exists_levelModuliPackageAbs_surjective_of_represents_of_section (solution)
