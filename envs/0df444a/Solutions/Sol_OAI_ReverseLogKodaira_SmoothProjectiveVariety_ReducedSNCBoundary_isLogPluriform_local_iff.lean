-- Prove2me | solution 1 for OAI.ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary.isLogPluriform_local_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:13:22.00175+00:00
-- url     : https://prove2.me/submissions/9083c4ce-ca90-44e4-91c6-935495139311

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/LogLattice.lean:L180-L232
-- (upload_full_project.md Phase 4): solution for node OAI.ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary.isLogPluriform_local_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Specialization
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LocalCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_FiberCharts
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LatticeBaseChange
import Theorems.Thm_OAI_ReverseLogKodaira_DifferentialBaseChange_rationalLattice_formallyEtale
import Theorems.Thm_OAI_ReverseLogKodaira_SmoothProjectiveVariety_regularLattice_restriction

-- ---- from OAI.AlgebraicGeometry.LogKodaira.LogLattice ----
namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

noncomputable section
namespace ReverseLogKodaira.LocalizationLattice

 

theorem lattice_locality :
    (∀ (A C V : Type*) [CommRing A] [CommRing C] [Algebra A C]
      [AddCommGroup V] [Module A V] [Module C V] [IsScalarTower A C V]
      (T : Submonoid A) [IsLocalization T C] (N : Submodule A V) (x : V),
      x ∈ Submodule.span C (N : Set V) ↔ ∃ t : T, (t : A) • x ∈ N) ∧
    (∀ (A V : Type*) [CommRing A] [AddCommGroup V] [Module A V]
      (N : Submodule A V) (x : V),
      (∀ (P : Ideal A), P.IsMaximal → ∃ t : A, t ∉ P ∧ t • x ∈ N) → x ∈ N) := by
  constructor
  · intro A C V _ _ _ _ _ _ _ T _ N x
    let : IsLocalizedModule T (LinearMap.id : V →ₗ[A] V) :=
      isLocalizedModule_id T V C
    have he : N.localized' C T (LinearMap.id : V →ₗ[A] V) =
        Submodule.span C (N : Set V) := by
      rw [Submodule.localized'_eq_span]
      congr 1
      exact Set.image_id _
    rw [← he, Submodule.mem_localized']
    constructor
    · rintro ⟨y, hy, t, rfl⟩
      exact ⟨t, by simpa only [← Submonoid.smul_def, IsLocalizedModule.mk'_cancel',
        LinearMap.id_apply] using hy⟩
    · rintro ⟨t, ht⟩
      refine ⟨(t : A) • x, ht, t, ?_⟩
      exact IsLocalizedModule.mk'_cancel (LinearMap.id : V →ₗ[A] V) x t
  · intro A V _ _ _ N x hx
    let I : Ideal A := N.comap (LinearMap.toSpanSingleton A V x)
    suffices hI : I = ⊤ by
      have h := I.eq_top_iff_one.mp hI
      simpa only [I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply,
        one_smul] using h
    by_contra hI
    obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨t, ht, htx⟩ := hx P hP
    exact ht (hIP htx)

end ReverseLogKodaira.LocalizationLattice

namespace ReverseLogKodaira.SmoothProjectiveVariety

lemma basic_functionField_tower (X : SmoothProjectiveVariety)
    (U : X.scheme.affineOpens) [Nonempty U.1] (t : Γ(X.scheme, U.1))
    [Nonempty (X.scheme.basicOpen t)] :
    IsScalarTower Γ(X.scheme, U.1) Γ(X.scheme, X.scheme.basicOpen t) X.scheme.functionField := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change X.scheme.presheaf.germ U.1 (genericPoint X.scheme) _ a =
    X.scheme.presheaf.germ (X.scheme.basicOpen t) (genericPoint X.scheme) _
      (X.scheme.presheaf.map (homOfLE (X.scheme.basicOpen_le t)).op a)
  exact (X.scheme.presheaf.germ_res_apply (homOfLE (X.scheme.basicOpen_le t))
    (genericPoint X.scheme) _ a).symm

lemma basic_constants_tower (X : SmoothProjectiveVariety)
    (U : X.scheme.affineOpens) [Nonempty U.1] (t : Γ(X.scheme, U.1))
    [Nonempty (X.scheme.basicOpen t)] :
    IsScalarTower ℂ Γ(X.scheme, U.1) Γ(X.scheme, X.scheme.basicOpen t) := by
  let := basic_functionField_tower X U t
  apply IsScalarTower.of_algebraMap_eq
  intro c
  apply X.scheme.germToFunctionField_injective (X.scheme.basicOpen t)
  change algebraMap Γ(X.scheme, X.scheme.basicOpen t) X.scheme.functionField
      (algebraMap ℂ Γ(X.scheme, X.scheme.basicOpen t) c) =
    algebraMap Γ(X.scheme, X.scheme.basicOpen t) X.scheme.functionField
      (algebraMap Γ(X.scheme, U.1) Γ(X.scheme, X.scheme.basicOpen t)
        (algebraMap ℂ Γ(X.scheme, U.1) c))
  rw [germ_constants, ← IsScalarTower.algebraMap_apply Γ(X.scheme, U.1)
    Γ(X.scheme, X.scheme.basicOpen t) X.scheme.functionField, germ_constants]

lemma regularLattice_basic (X : SmoothProjectiveVariety)
    (U : X.scheme.affineOpens) [Nonempty U.1] (t : Γ(X.scheme, U.1))
    [Nonempty (X.scheme.basicOpen t)] (m : ℕ) :
    X.regularPluriformLattice ⟨X.scheme.basicOpen t, U.2.basicOpen t⟩ m =
      Submodule.span Γ(X.scheme, X.scheme.basicOpen t)
        (X.regularPluriformLattice U m : Set (X.RationalPluriform m)) := by
  let := basic_functionField_tower X U t
  let := basic_constants_tower X U t
  let := U.2.isLocalization_basicOpen t
  let := Algebra.FormallyEtale.of_isLocalization
    (Rₘ := Γ(X.scheme, X.scheme.basicOpen t)) (Submonoid.powers t)
  exact DifferentialBaseChange.rationalLattice_formallyEtale ℂ Γ(X.scheme, U.1)
    Γ(X.scheme, X.scheme.basicOpen t) X.scheme.functionField X.dimension m

 

theorem regularLattice_basic_locality (X : SmoothProjectiveVariety)
    (U : X.scheme.affineOpens) [Nonempty U.1] (m : ℕ) (s : X.RationalPluriform m)
    (hs : ∀ x : U.1, ∃ (t : Γ(X.scheme, U.1)) (h : Nonempty (X.scheme.basicOpen t)),
      x.1 ∈ X.scheme.basicOpen t ∧
        s ∈ @regularPluriformLattice X ⟨X.scheme.basicOpen t, U.2.basicOpen t⟩ h m) :
    s ∈ X.regularPluriformLattice U m := by
  apply LocalizationLattice.lattice_locality.{0,0,0,0,0}.2 Γ(X.scheme, U.1) (X.RationalPluriform m)
    (X.regularPluriformLattice U m) s
  intro P hP
  let := hP
  let p : PrimeSpectrum Γ(X.scheme, U.1) := ⟨P, inferInstance⟩
  have hx : U.2.fromSpec p ∈ U.1 := by
    change U.2.fromSpec p ∈ (U.1 : Set X.scheme)
    rw [← U.2.range_fromSpec]
    exact ⟨p, rfl⟩
  obtain ⟨t, ht, hxt, hst⟩ := hs ⟨U.2.fromSpec p, hx⟩
  let := ht
  let := U.2.isLocalization_basicOpen t
  let := basic_functionField_tower X U t
  have htP : t ∉ P := by
    change p ∈ PrimeSpectrum.basicOpen t
    rw [← U.2.fromSpec_preimage_basicOpen t]
    exact hxt
  rw [regularLattice_basic] at hst
  obtain ⟨u, hu⟩ := (LocalizationLattice.lattice_locality.{0,0,0,0,0}.1 Γ(X.scheme, U.1)
    Γ(X.scheme, X.scheme.basicOpen t) (X.RationalPluriform m)
    (Submonoid.powers t) (X.regularPluriformLattice U m) s).mp hst
  refine ⟨u, ?_, hu⟩
  obtain ⟨n, hn⟩ := u.2
  rw [← hn]
  exact P.primeCompl.pow_mem htP n

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety

 
theorem regularLattice_locality (X : SmoothProjectiveVariety)
    (U : X.scheme.affineOpens) [Nonempty U.1] (m : ℕ) (s : X.RationalPluriform m)
    (hs : ∀ x : U.1, ∃ (V : X.scheme.affineOpens) (h : Nonempty V.1), x.1 ∈ V.1 ∧
      s ∈ @regularPluriformLattice X V h m) :
    s ∈ X.regularPluriformLattice U m := by
  apply regularLattice_basic_locality X U m s
  intro x
  obtain ⟨V, hV, hxV, hsV⟩ := hs x
  let := hV
  obtain ⟨t, htV, hxt⟩ := U.2.exists_basicOpen_le ⟨x.1, hxV⟩ x.2
  let ht : Nonempty (X.scheme.basicOpen t) := ⟨⟨x.1, hxt⟩⟩
  refine ⟨t, ht, hxt, ?_⟩
  exact regularLattice_restriction X ⟨X.scheme.basicOpen t, U.2.basicOpen t⟩ V htV m hsV

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary

 

theorem isLogPluriform_local_iff {X : SmoothProjectiveVariety}
    (E : X.ReducedSNCBoundary) (m : ℕ) (s : X.RationalPluriform m) :
    E.IsLogPluriform m s ↔
      ∀ x : X.scheme, ∃ (U : X.scheme.affineOpens) (hU : Nonempty U.1), x ∈ U.1 ∧
        ∃ t : Γ(X.scheme, U.1), t ≠ 0 ∧ E.ideal.ideal U = Ideal.span {t} ∧
          (algebraMap Γ(X.scheme, U.1) X.scheme.functionField t)^m • s ∈
            @regularPluriformLattice X U hU m := by
  constructor
  · intro hs x
    obtain ⟨U, hxU, t, ht, hI⟩ := E.union_cartier x
    let hU : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
    exact ⟨U, hU, hxU, t, ht, hI, hs U hU t ht hI⟩
  · intro hs U hU u hu hI
    let := hU
    apply regularLattice_locality X U m
    intro x
    obtain ⟨V, hV, hxV, t, ht, hJ, hst⟩ := hs x.1
    let := hV
    obtain ⟨a, haV, hxa⟩ := U.2.exists_basicOpen_le ⟨x.1, hxV⟩ x.2
    let W : X.scheme.affineOpens := ⟨X.scheme.basicOpen a, U.2.basicOpen a⟩
    let hW : Nonempty W.1 := ⟨⟨x.1, hxa⟩⟩
    let ru : Γ(X.scheme, U.1) →+* Γ(X.scheme, W.1) :=
      (X.scheme.presheaf.map (homOfLE (X.scheme.basicOpen_le a)).op).hom
    let rt : Γ(X.scheme, V.1) →+* Γ(X.scheme, W.1) :=
      (X.scheme.presheaf.map (homOfLE haV).op).hom
    have hIu : E.ideal.ideal W = Ideal.span {ru u} := by
      rw [← E.ideal.map_ideal (show W ≤ U from X.scheme.basicOpen_le a), hI]
      simp only [ru, Ideal.map_span, Set.image_singleton]
      rfl
    have hJt : E.ideal.ideal W = Ideal.span {rt t} := by
      rw [← E.ideal.map_ideal (show W ≤ V from haV), hJ]
      simp only [rt, Ideal.map_span, Set.image_singleton]
      rfl
    have hud : rt t ∣ ru u := by
      apply Ideal.mem_span_singleton.mp
      rw [← hJt, hIu]
      exact Ideal.subset_span (Set.mem_singleton _)
    obtain ⟨b, hb⟩ := hud
    have hur (r : Γ(X.scheme, U.1)) :
        algebraMap Γ(X.scheme, W.1) X.scheme.functionField (ru r) =
          algebraMap Γ(X.scheme, U.1) X.scheme.functionField r :=
      X.scheme.presheaf.germ_res_apply (homOfLE (X.scheme.basicOpen_le a))
        (genericPoint X.scheme) _ r
    have htr (r : Γ(X.scheme, V.1)) :
        algebraMap Γ(X.scheme, W.1) X.scheme.functionField (rt r) =
          algebraMap Γ(X.scheme, V.1) X.scheme.functionField r :=
      X.scheme.presheaf.germ_res_apply (homOfLE haV) (genericPoint X.scheme) _ r
    refine ⟨W, hW, hxa, ?_⟩
    have hstW := regularLattice_restriction X W V haV m hst
    have h := (X.regularPluriformLattice W m).smul_mem (b^m) hstW
    rw [← IsScalarTower.algebraMap_smul X.scheme.functionField, map_pow] at h
    rw [← hur u, hb, map_mul, mul_pow, htr t, mul_smul, smul_comm]
    exact h

end ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary

end
end

end OAI

-- ---- platform node ----
open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.SmoothProjectiveVariety OAI.ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem solution {X : SmoothProjectiveVariety}
    (E : X.ReducedSNCBoundary) (m : ℕ) (s : X.RationalPluriform m) :
    E.IsLogPluriform m s ↔
      ∀ x : X.scheme, ∃ (U : X.scheme.affineOpens) (hU : Nonempty U.1), x ∈ U.1 ∧
        ∃ t : Γ(X.scheme, U.1), t ≠ 0 ∧ E.ideal.ideal U = Ideal.span {t} ∧
          (algebraMap Γ(X.scheme, U.1) X.scheme.functionField t)^m • s ∈
            @regularPluriformLattice X U hU m := by
  first
    | exact OAI.ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary.isLogPluriform_local_iff E m s
    | exact OAI.ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary.isLogPluriform_local_iff
    | (apply OAI.ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary.isLogPluriform_local_iff <;> assumption)
    | (intros; apply OAI.ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary.isLogPluriform_local_iff <;> assumption)
