-- Prove2me | solution 1 for NeronModelInfra.exists_antitone_isClosed_forall_indexOne_chart_of_smooth_pullback_snd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/bbc96a0b-b6de-504c-97de-c18e99196992

import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_NeronModelInfra_SmoothnessDefect

import Theorems.Thm_NeronModelInfra_mem_vanishingIdeal_closure_of_forall_indexOne_algHom
import Theorems.Thm_NeronModelInfra_isSmoothAt_and_mem_freeLocus_basicOpen_of_isSmoothAt_of_mem_freeLocus
import Theorems.Thm_NeronModelInfra_exists_opens_inter_closure_eq_setOf_isSmoothAt_and_mem_freeLocus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_antitone_isClosed_forall_indexOne_chart_of_smooth_pullback_snd

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TensorProduct

universe u

namespace Partition29

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

def IsIdxSpec (y : X) : Prop :=
  ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : Algebra R R')
    (_ : IsLocalHom (algebraMap R R')) (_ : IsIndexOneExtension R R')
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f), x.1 (IsLocalRing.closedPoint R') = y

def GoodClause (C : Set X) (U : X.Opens) (hU : IsAffineOpen U) (y : X) (hyU : y ∈ U) : Prop :=
  letI : Algebra R Γ(X, U) :=
    ((X.presheaf.map (homOfLE le_top).op).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
  let J : Ideal Γ(X, U) :=
    PrimeSpectrum.vanishingIdeal ((fun z : U => hU.primeIdealOf z) '' {z : U | (z : X) ∈ C})
  ∀ (𝔮 : Ideal (Γ(X, U) ⧸ J)) [𝔮.IsPrime],
    𝔮.comap (Ideal.Quotient.mk J) = (hU.primeIdealOf ⟨y, hyU⟩).asIdeal →
    (∀ [Algebra (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)]
      [IsScalarTower R (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)],
      Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮) ∧
    (⟨𝔮, ‹_›⟩ : PrimeSpectrum (Γ(X, U) ⧸ J)) ∈
      Module.freeLocus (Γ(X, U) ⧸ J) ((Γ(X, U) ⧸ J) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R])

def Good (C : Set X) : Set X := {y | ∃ (U : X.Opens) (hU : IsAffineOpen U) (hyU : y ∈ U), GoodClause f C U hU y hyU}

def step (S : Set X) : Set X := S \ Good f (closure S)

theorem step_subset (S : Set X) : step f S ⊆ S := Set.diff_subset

theorem iterate_step_subset (S : Set X) (n : ℕ) : (step f)^[n] S ⊆ S := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => rw [Function.iterate_succ_apply']; exact (step_subset f _).trans ih

theorem iterate_step_succ_subset (S : Set X) (n : ℕ) : (step f)^[n + 1] S ⊆ (step f)^[n] S := by
  rw [Function.iterate_succ_apply']; exact step_subset f _

end Partition29

open Partition29

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hK : Smooth (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃ (t : ℕ) (Y : ℕ → Set X), (∀ i, IsClosed (Y i)) ∧ (∀ i, Y (i + 1) ⊆ Y i) ∧ Y t = ∅ ∧
      (∀ y ∈ Y 0, f y = IsLocalRing.closedPoint R) ∧ (∀ y ∈ Y 0, y ∉ (f.smoothLocus : Set X)) ∧
      (∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
        [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
        ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
          x.1 (IsLocalRing.closedPoint R') ∉ (f.smoothLocus : Set X) →
          x.1 (IsLocalRing.closedPoint R') ∈ Y 0) ∧
      (∀ (i : ℕ), i < t → ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
        [Algebra R R'] [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
        ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
          x.1 (IsLocalRing.closedPoint R') ∈ Y i → x.1 (IsLocalRing.closedPoint R') ∉ Y (i + 1) →
          ∃ (U : X.Opens) (hU : IsAffineOpen U) (hxU : x.1 (IsLocalRing.closedPoint R') ∈ U),
            (∀ y ∈ (U : Set X), y ∉ Y (i + 1)) ∧
            letI : Algebra R Γ(X, U) :=
              ((X.presheaf.map (homOfLE le_top).op).hom.comp
                (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
            let J : Ideal Γ(X, U) :=
              PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y i})

            (∀ g : Γ(X, U),
              (∀ (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R R'']
                [IsLocalHom (algebraMap R R'')], IsIndexOneExtension R R'' →
                ∀ c : Γ(X, U) →ₐ[R] R'', J ≤ (IsLocalRing.maximalIdeal R'').comap c →
                  g ∈ (IsLocalRing.maximalIdeal R'').comap c) → g ∈ J) ∧

            (∀ (𝔮 : Ideal (Γ(X, U) ⧸ J)) [𝔮.IsPrime],
              𝔮.comap (Ideal.Quotient.mk J) = (hU.primeIdealOf ⟨x.1 (IsLocalRing.closedPoint R'), hxU⟩).asIdeal →
              (∀ [Algebra (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)]
                [IsScalarTower R (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)],
                Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮) ∧
              (⟨𝔮, ‹_›⟩ : PrimeSpectrum (Γ(X, U) ⧸ J)) ∈
                Module.freeLocus (Γ(X, U) ⧸ J) ((Γ(X, U) ⧸ J) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R]))) := by
  classical

  let S₀ : Set X := {y | IsIdxSpec f y ∧ y ∉ (f.smoothLocus : Set X)}
  let Sq : ℕ → Set X := fun n => (step f)^[n] S₀
  have hSq_succ : ∀ n, Sq (n + 1) = step f (Sq n) := fun n => Function.iterate_succ_apply' (step f) n S₀

  have hidx_k : ∀ y : X, IsIdxSpec f y → f y = IsLocalRing.closedPoint R := by
    rintro y ⟨R', _, _, _, _, _, _, x, rfl⟩
    show (x.1 ≫ f).base (IsLocalRing.closedPoint R') = _
    rw [x.2]
    exact IsLocalRing.comap_closedPoint (algebraMap R R')
  have hSqidx : ∀ n, ∀ y ∈ Sq n, IsIdxSpec f y := fun n y hy => (iterate_step_subset f S₀ n hy).1
  have hSqk : ∀ n, ∀ y ∈ Sq n, f y = IsLocalRing.closedPoint R := fun n y hy => hidx_k y (hSqidx n y hy)

  have hSq_shape : ∀ n, ∀ s ∈ Sq n, ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
      (_ : Algebra R R') (_ : IsLocalHom (algebraMap R R')) (_ : IsIndexOneExtension R R')
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f), x.1 (IsLocalRing.closedPoint R') = s :=
    fun n s hs => hSqidx n s hs

  have hfib : IsClosed {y : X | f y = IsLocalRing.closedPoint R} := by
    have h1 : IsClosed ({IsLocalRing.closedPoint R} : Set (Spec (CommRingCat.of R))) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr (IsLocalRing.maximalIdeal.isMaximal R)
    exact h1.preimage f.base.hom.continuous
  have hYk : ∀ n, ∀ y ∈ closure (Sq n), f y = IsLocalRing.closedPoint R := fun n =>
    (hfib.closure_subset_iff.mpr (fun y hy => hSqk n y hy))
  have hY0sm : ∀ y ∈ closure (Sq 0), y ∉ (f.smoothLocus : Set X) := by
    have : closure (Sq 0) ⊆ (f.smoothLocus : Set X)ᶜ :=
      (f.smoothLocus.2.isClosed_compl).closure_subset_iff.mpr (fun y hy => hy.2)
    exact fun y hy => this hy

  have hstrict : ∀ S : Set X, S ⊆ S₀ → S.Nonempty → ¬ closure S ⊆ closure (step f S) := by
    intro S hS ⟨s, hs⟩ hle

    obtain ⟨_, ⟨U, hU, rfl⟩, hsU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
    obtain ⟨W, hWU, hWne, hWgood⟩ :=
      NeronModelInfra.exists_opens_inter_closure_eq_setOf_isSmoothAt_and_mem_freeLocus f S
        (fun s hs => (hS hs).1) (fun s hs => hidx_k s (hS hs).1) U hU
    obtain ⟨w, hwS, hwW⟩ := hWne ⟨s, subset_closure hs, hsU⟩

    have hmiss : closure (step f S) ⊆ (W : Set X)ᶜ := by
      refine (W.2.isClosed_compl).closure_subset_iff.mpr ?_
      rintro y ⟨hyS, hyngood⟩ hyW
      exact hyngood ⟨U, hU, hWU hyW, (hWgood y (hWU hyW) (subset_closure hyS)).mp hyW⟩
    exact hmiss (hle hwS) hwW

  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsNoetherian X := {}
  have hterm : ∃ t : ℕ, Sq t = ∅ := by
    by_contra hne
    push_neg at hne

    have hchain : ∀ n, (⟨closure (Sq (n + 1)), isClosed_closure⟩ : TopologicalSpace.Closeds X) <
        ⟨closure (Sq n), isClosed_closure⟩ := by
      intro n
      refine lt_of_le_of_ne ?_ ?_
      · exact closure_mono (by rw [hSq_succ]; exact step_subset f _)
      · intro h
        have h' : closure (Sq n) ⊆ closure (Sq (n + 1)) := by
          have := congrArg (fun C : TopologicalSpace.Closeds X => (C : Set X)) h
          exact this.symm.subset
        rw [hSq_succ] at h'
        exact hstrict (Sq n) (iterate_step_subset f S₀ n) (hne n) h'
    exact (RelEmbedding.natGT (fun n => (⟨closure (Sq n), isClosed_closure⟩ : TopologicalSpace.Closeds X)) hchain).not_wellFounded
      wellFounded_lt
  obtain ⟨t, ht⟩ := hterm

  have hmemSq : ∀ (i : ℕ) (y : X), y ∈ S₀ → y ∈ closure (Sq i) → y ∈ Sq i := by
    intro i
    induction i with
    | zero => exact fun y hy _ => hy
    | succ j ih =>
      intro y hy0 hyY
      have hyj : y ∈ Sq j := ih y hy0 (closure_mono (by rw [hSq_succ]; exact step_subset f _) hyY)
      rw [hSq_succ]
      refine ⟨hyj, ?_⟩
      rintro ⟨U, hU, hyU, hgood⟩
      obtain ⟨W, hWU, -, hWgood⟩ :=
        NeronModelInfra.exists_opens_inter_closure_eq_setOf_isSmoothAt_and_mem_freeLocus f (Sq j)
          (hSq_shape j) (hSqk j) U hU
      have hyW : y ∈ W := (hWgood y hyU (subset_closure hyj)).mpr hgood
      have hmiss : closure (step f (Sq j)) ⊆ (W : Set X)ᶜ := by
        refine (W.2.isClosed_compl).closure_subset_iff.mpr ?_
        rintro y' ⟨hy'S, hy'ngood⟩ hy'W
        exact hy'ngood ⟨U, hU, hWU hy'W, (hWgood y' (hWU hy'W) (subset_closure hy'S)).mp hy'W⟩
      rw [hSq_succ] at hyY
      exact hmiss hyY hyW

  refine ⟨t, fun n => closure (Sq n), fun n => isClosed_closure,
    fun n => closure_mono (by rw [hSq_succ]; exact step_subset f _), by show closure (Sq t) = ∅; rw [ht, closure_empty],
    hYk 0, hY0sm, ?_, ?_⟩
  ·
    intro R' _ _ _ _ _ hR' x hx
    exact subset_closure ⟨⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hR', x, rfl⟩, hx⟩
  ·
    intro i hi R' _ _ _ _ _ hR' x hyi hyi1
    set y := x.1 (IsLocalRing.closedPoint R') with hy
    have hy0 : y ∈ S₀ := ⟨⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hR', x, rfl⟩,
      hY0sm y (closure_mono (iterate_step_subset f S₀ i) hyi)⟩
    have hySi : y ∈ Sq i := hmemSq i y hy0 hyi
    have hgood : y ∈ Good f (closure (Sq i)) := by
      by_contra h
      exact hyi1 (subset_closure (by rw [hSq_succ]; exact ⟨hySi, h⟩))
    obtain ⟨U, hU, hyU, hgoodU⟩ := hgood

    letI algU : Algebra R Γ(X, U) :=
      ((X.presheaf.map (homOfLE le_top).op).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    have hmem_basic : ∀ (h : Γ(X, U)) (z : X) (hz : z ∈ U), z ∈ X.basicOpen h ↔ h ∉ (hU.primeIdealOf ⟨z, hz⟩).asIdeal := by
      intro h z hz
      rw [← PrimeSpectrum.mem_basicOpen, show (hU.primeIdealOf ⟨z, hz⟩ ∈ PrimeSpectrum.basicOpen h) ↔
        hU.primeIdealOf ⟨z, hz⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen h from by rw [hU.fromSpec_preimage_basicOpen]; rfl]
      show z ∈ X.basicOpen h ↔ hU.fromSpec.base (hU.primeIdealOf ⟨z, hz⟩) ∈ X.basicOpen h
      rw [hU.fromSpec_primeIdealOf]
    obtain ⟨h, hhvan, hhy⟩ : ∃ h : Γ(X, U), (∀ z : U, (z : X) ∈ closure (Sq (i + 1)) → h ∈ (hU.primeIdealOf z).asIdeal) ∧
        h ∉ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal := by
      let T : Set (PrimeSpectrum Γ(X, U)) := (fun z : U => hU.primeIdealOf z) '' {z : U | (z : X) ∈ closure (Sq (i + 1))}
      have hT : IsClosed T := by
        have hcl : IsClosed {z : U | (z : X) ∈ closure (Sq (i + 1))} := isClosed_closure.preimage continuous_subtype_val
        have : T = Scheme.homeoOfIso hU.isoSpec '' {z : U | (z : X) ∈ closure (Sq (i + 1))} := by
          ext q
          simp only [T, Set.mem_image, Scheme.homeoOfIso_apply]
          rfl
        rw [this]
        exact (Scheme.homeoOfIso hU.isoSpec).isClosed_image.mpr hcl
      have hyT : hU.primeIdealOf ⟨y, hyU⟩ ∉ T := by
        rintro ⟨z, hz, hzy⟩
        apply hyi1
        have : (z : X) = y := by
          have := congrArg (fun q => hU.fromSpec.base q) hzy
          simpa only [IsAffineOpen.fromSpec_primeIdealOf] using this
        rw [← this]; exact hz
      have hnot : ¬ ((PrimeSpectrum.vanishingIdeal T : Ideal Γ(X, U)) ≤ (hU.primeIdealOf ⟨y, hyU⟩).asIdeal) := by
        intro hle
        apply hyT
        have : hU.primeIdealOf ⟨y, hyU⟩ ∈ PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal T : Set Γ(X, U)) := hle
        rwa [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hT.closure_eq] at this
      obtain ⟨h, hhI, hhy⟩ := Set.not_subset.mp hnot
      refine ⟨h, fun z hz => ?_, hhy⟩
      exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp hhI _ ⟨z, hz, rfl⟩
    have hyh : y ∈ X.basicOpen h := (hmem_basic h y hyU).mpr hhy
    refine ⟨X.basicOpen h, hU.basicOpen h, hyh, ?_, ?_, ?_⟩
    · intro z hz hz'
      have hzU : z ∈ U := X.basicOpen_le h hz
      exact (hmem_basic h z hzU).mp hz (hhvan ⟨z, hzU⟩ hz')
    ·
      exact NeronModelInfra.mem_vanishingIdeal_closure_of_forall_indexOne_algHom f (Sq i) (hSq_shape i)
        (X.basicOpen h) (hU.basicOpen h)
    ·
      exact NeronModelInfra.isSmoothAt_and_mem_freeLocus_basicOpen_of_isSmoothAt_of_mem_freeLocus f (closure (Sq i))
        (hYk i) U hU h y hyU hyh hgoodU

end S_NeronModelInfra_exists_antitone_isClosed_forall_indexOne_chart_of_smooth_pullback_snd
end P2MW
export P2MW.S_NeronModelInfra_exists_antitone_isClosed_forall_indexOne_chart_of_smooth_pullback_snd (solution)
