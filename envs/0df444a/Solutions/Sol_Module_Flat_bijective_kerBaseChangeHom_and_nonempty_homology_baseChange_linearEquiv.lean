-- Prove2me | solution 1 for Module.Flat.bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/9c3fa686-a67a-5f1f-8c26-349ec27a3dc9

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Flat_bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv

set_option autoImplicit false

universe u uR uT uM

open TensorProduct

namespace LOCSOL

section FlatKer

variable {R : Type uR} [CommRing R] (T : Type uT) [CommRing T] [Algebra R T] [Module.Flat R T]
  {M N : Type uM} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem baseChange_subtype_injective (K : Submodule R M) :
    Function.Injective (K.subtype.baseChange T) := by
  intro x y h
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := T) K.subtype K.injective_subtype
  exact hinj h

theorem exists_baseChange_subtype_eq (f : M →ₗ[R] N) (y : T ⊗[R] M)
    (hy : f.baseChange T y = 0) :
    ∃ x : T ⊗[R] LinearMap.ker f, (LinearMap.ker f).subtype.baseChange T x = y := by
  have h := Module.Flat.lTensor_exact T (LinearMap.exact_subtype_ker_map f)
  exact (h y).mp hy

theorem kerBaseChangeHom_bijective (f : M →ₗ[R] N) :
    Function.Bijective (TwoChartCech.kerBaseChangeHom f T) := by
  constructor
  · intro x y h
    apply baseChange_subtype_injective T (LinearMap.ker f)
    rw [← TwoChartCech.kerBaseChangeHom_apply_coe, ← TwoChartCech.kerBaseChangeHom_apply_coe, h]
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := exists_baseChange_subtype_eq T f y hy
    exact ⟨x, Subtype.ext (by rw [TwoChartCech.kerBaseChangeHom_apply_coe, hx])⟩

noncomputable def kerEquiv (f : M →ₗ[R] N) :
    T ⊗[R] LinearMap.ker f ≃ₗ[T] LinearMap.ker (f.baseChange T) :=
  LinearEquiv.ofBijective _ (kerBaseChangeHom_bijective T f)

@[scoped simp] theorem kerEquiv_apply_coe (f : M →ₗ[R] N) (x : T ⊗[R] LinearMap.ker f) :
    (kerEquiv T f x : T ⊗[R] M) = (LinearMap.ker f).subtype.baseChange T x := by
  simp [kerEquiv, TwoChartCech.kerBaseChangeHom_apply_coe]

theorem baseChange_mkQ_eq_zero_iff {K : Type uM} [AddCommGroup K] [Module R K] (B : Submodule R K)
    (t : T ⊗[R] K) : (B.mkQ).baseChange T t = 0 ↔ ∃ b : T ⊗[R] B, B.subtype.baseChange T b = t := by
  have h := Module.Flat.lTensor_exact T (LinearMap.exact_subtype_mkQ B)
  exact h t

end FlatKer

end LOCSOL
p2m_reactivate "P2MW.S_Module_Flat_bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv.LOCSOL"

open LOCSOL in

theorem solution
    {R : Type u} [CommRing R] (T : Type u) [CommRing T] [Algebra R T] [Module.Flat R T]
    {M N P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hfg : g ∘ₗ f = 0) :
    letI : AddCommGroup ↥(LinearMap.ker (g.baseChange T)) :=
      Submodule.addCommGroup (M := T ⊗[R] N) (LinearMap.ker (g.baseChange T))
    Function.Bijective (TwoChartCech.kerBaseChangeHom g T) ∧
    Nonempty
      (T ⊗[R] (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype) ≃ₗ[T]
        (↥(LinearMap.ker (g.baseChange T)) ⧸
          (LinearMap.range (f.baseChange T)).comap (LinearMap.ker (g.baseChange T)).subtype)) ∧
    ((LinearMap.ker (g.baseChange T) ≤ LinearMap.range (f.baseChange T)) ↔
        Subsingleton (T ⊗[R] (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype))) ∧
    (Module.Finite R (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype) →
        Module.Finite T (↥(LinearMap.ker (g.baseChange T)) ⧸
          (LinearMap.range (f.baseChange T)).comap (LinearMap.ker (g.baseChange T)).subtype)) := by
  classical
  letI iK' : AddCommGroup ↥(LinearMap.ker (g.baseChange T)) :=
    Submodule.addCommGroup (M := T ⊗[R] N) (LinearMap.ker (g.baseChange T))

  have hfK : ∀ m, f m ∈ LinearMap.ker g := fun m => by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hfg, LinearMap.zero_apply]
  have hfB : ∀ m, f.codRestrict (LinearMap.ker g) hfK m ∈
      (LinearMap.range f).comap (LinearMap.ker g).subtype := fun m =>
    Submodule.mem_comap.mpr ⟨m, rfl⟩

  have hδ : Function.Surjective
      ((f.codRestrict (LinearMap.ker g) hfK).codRestrict _ hfB) := by
    rintro ⟨⟨y, hyK⟩, hyB⟩
    obtain ⟨m, hm⟩ := Submodule.mem_comap.mp hyB
    exact ⟨m, Subtype.ext (Subtype.ext hm)⟩
  have hfac : ((LinearMap.ker g).subtype ∘ₗ ((LinearMap.range f).comap (LinearMap.ker g).subtype).subtype) ∘ₗ
      ((f.codRestrict (LinearMap.ker g) hfK).codRestrict _ hfB) = f := by
    ext m
    rfl

  have hπ : Function.Surjective
      ((((LinearMap.range f).comap (LinearMap.ker g).subtype).mkQ).baseChange T) :=
    LinearMap.lTensor_surjective T (Submodule.mkQ_surjective _)
  have hΦ : Function.Surjective
      (((LinearMap.range (f.baseChange T)).comap (LinearMap.ker (g.baseChange T)).subtype).mkQ ∘ₗ
        (kerEquiv T g).toLinearMap) :=
    (Submodule.mkQ_surjective _).comp (kerEquiv T g).surjective
  have hker : LinearMap.ker ((((LinearMap.range f).comap (LinearMap.ker g).subtype).mkQ).baseChange T) =
      LinearMap.ker (((LinearMap.range (f.baseChange T)).comap
        (LinearMap.ker (g.baseChange T)).subtype).mkQ ∘ₗ (kerEquiv T g).toLinearMap) := by
    ext t
    rw [LinearMap.mem_ker, LinearMap.mem_ker, baseChange_mkQ_eq_zero_iff, LinearMap.comp_apply,
      LinearEquiv.coe_coe, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, kerEquiv_apply_coe, LinearMap.mem_range]
    constructor
    · rintro ⟨b, rfl⟩
      obtain ⟨c, rfl⟩ : ∃ c, ((f.codRestrict (LinearMap.ker g) hfK).codRestrict _ hfB).baseChange T c = b :=
        LinearMap.lTensor_surjective T hδ b
      refine ⟨c, ?_⟩
      symm
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← LinearMap.comp_apply,
        ← LinearMap.baseChange_comp, hfac]
    · rintro ⟨c, hc⟩
      have h2 : (LinearMap.ker g).subtype.baseChange T
          ((((LinearMap.range f).comap (LinearMap.ker g).subtype).subtype.baseChange T)
            (((f.codRestrict (LinearMap.ker g) hfK).codRestrict _ hfB).baseChange T c)) =
          (LinearMap.ker g).subtype.baseChange T t := by
        rw [← hc, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← LinearMap.comp_apply,
          ← LinearMap.baseChange_comp, hfac]
      exact ⟨_, baseChange_subtype_injective T _ h2⟩

  let e : T ⊗[R] (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype) ≃ₗ[T]
      (↥(LinearMap.ker (g.baseChange T)) ⧸
        (LinearMap.range (f.baseChange T)).comap (LinearMap.ker (g.baseChange T)).subtype) :=
    (LinearMap.quotKerEquivOfSurjective _ hπ).symm.trans
      ((Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective _ hΦ))
  refine ⟨kerBaseChangeHom_bijective T g, ⟨e⟩, ?_, fun hfin => ?_⟩
  · constructor
    · intro hle
      haveI : Subsingleton (↥(LinearMap.ker (g.baseChange T)) ⧸
          (LinearMap.range (f.baseChange T)).comap (LinearMap.ker (g.baseChange T)).subtype) := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ a
        obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ b
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap]
        exact hle (x - y).2
      exact e.toEquiv.subsingleton
    · intro hs y hy
      haveI := hs
      haveI : Subsingleton (↥(LinearMap.ker (g.baseChange T)) ⧸
          (LinearMap.range (f.baseChange T)).comap (LinearMap.ker (g.baseChange T)).subtype) :=
        e.symm.toEquiv.subsingleton
      have h0 : ((LinearMap.range (f.baseChange T)).comap
          (LinearMap.ker (g.baseChange T)).subtype).mkQ ⟨y, hy⟩ = 0 := Subsingleton.elim _ _
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h0
      exact h0
  · haveI := hfin
    exact Module.Finite.equiv e

end S_Module_Flat_bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv
end P2MW
export P2MW.S_Module_Flat_bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv (solution)
