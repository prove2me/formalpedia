-- Prove2me | solution 1 for Module.length_quotient_torsionBySet_sup_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/a2943a4b-3cf7-5509-ba22-a8a41ebb1ac8

import Mathlib.RingTheory.Length
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_length_quotient_torsionBySet_sup_eq_iff

set_option autoImplicit false

universe u v w x

namespace M4cP4NCMOD

open Module Submodule Pointwise

section PID

variable {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]

theorem length_quotient_smul_top (F : Type*) [AddCommGroup F] [Module 𝒪 F] [Module.Free 𝒪 F]
    [Module.Finite 𝒪 F] (e₀ : 𝒪) :
    Module.length 𝒪 (F ⧸ (e₀ • (⊤ : Submodule 𝒪 F))) =
      (Module.finrank 𝒪 F : ℕ∞) * Module.length 𝒪 (𝒪 ⧸ Ideal.span ({e₀} : Set 𝒪)) := by
  classical
  set n := Module.finrank 𝒪 F
  let b := Module.finBasis 𝒪 F
  let e : F ≃ₗ[𝒪] (Fin n → 𝒪) := b.equivFun
  have h1 : (e₀ • (⊤ : Submodule 𝒪 F)).map (e : F →ₗ[𝒪] (Fin n → 𝒪)) =
      e₀ • (⊤ : Submodule 𝒪 (Fin n → 𝒪)) := by
    rw [Submodule.map_pointwise_smul, Submodule.map_top, LinearEquiv.range]
  have h2 : (e₀ • (⊤ : Submodule 𝒪 (Fin n → 𝒪))) =
      Submodule.pi Set.univ (fun _ : Fin n => (Ideal.span ({e₀} : Set 𝒪) : Submodule 𝒪 𝒪)) := by
    ext f
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
      Submodule.mem_pi, Set.mem_univ, forall_const]
    constructor
    · rintro ⟨g, rfl⟩ i
      exact Ideal.mem_span_singleton'.mpr ⟨g i, by simp [mul_comm]⟩
    · intro h
      choose c hc using fun i => Ideal.mem_span_singleton'.mp (h i)
      exact ⟨c, funext fun i => by simp [← hc i, mul_comm]⟩
  calc Module.length 𝒪 (F ⧸ (e₀ • (⊤ : Submodule 𝒪 F)))
      = Module.length 𝒪 ((Fin n → 𝒪) ⧸ (e₀ • (⊤ : Submodule 𝒪 (Fin n → 𝒪)))) :=
        (Submodule.Quotient.equiv _ _ e h1).length_eq
    _ = Module.length 𝒪 ((Fin n → 𝒪) ⧸
          Submodule.pi Set.univ (fun _ : Fin n => (Ideal.span ({e₀} : Set 𝒪) : Submodule 𝒪 𝒪))) :=
        (Submodule.quotEquivOfEq _ _ h2).length_eq
    _ = Module.length 𝒪 (Fin n → 𝒪 ⧸ (Ideal.span ({e₀} : Set 𝒪))) :=
        (Submodule.quotientPi _).length_eq
    _ = ∑ _i : Fin n, Module.length 𝒪 (𝒪 ⧸ Ideal.span ({e₀} : Set 𝒪)) :=
        Module.length_pi_of_fintype 𝒪 _
    _ = (n : ℕ∞) * Module.length 𝒪 (𝒪 ⧸ Ideal.span ({e₀} : Set 𝒪)) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem length_quotient_span_singleton_ne_top {e₀ : 𝒪} (he₀ : e₀ ≠ 0) :
    Module.length 𝒪 (𝒪 ⧸ Ideal.span ({e₀} : Set 𝒪)) ≠ ⊤ := by
  set J : Ideal 𝒪 := Ideal.span ({e₀} : Set 𝒪)
  have hJ : J ≠ ⊥ := by
    simpa [J, Ideal.span_singleton_eq_bot] using he₀
  have hdim : Ring.KrullDimLE 0 (𝒪 ⧸ J) := by
    refine Ring.KrullDimLE.mk₀ fun K hK => ?_
    have hK' : (K.comap (Ideal.Quotient.mk J)).IsPrime := Ideal.comap_isPrime _ K
    have hne : K.comap (Ideal.Quotient.mk J) ≠ ⊥ := by
      intro h
      apply hJ
      refine le_bot_iff.mp ?_
      calc J ≤ K.comap (Ideal.Quotient.mk J) := by
            intro a ha
            rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
            exact K.zero_mem
        _ = ⊥ := h
    have hmax : (K.comap (Ideal.Quotient.mk J)).IsMaximal := hK'.isMaximal hne
    have := Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective hmax
    rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at this
    exact this.resolve_left hK.ne_top
  have hart : IsArtinianRing (𝒪 ⧸ J) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  have hsurj : Function.Surjective (algebraMap 𝒪 (𝒪 ⧸ J)) := Ideal.Quotient.mk_surjective
  rw [Module.length_eq_of_surjective (S := 𝒪) (R := 𝒪 ⧸ J) (M := 𝒪 ⧸ J) hsurj]
  exact Module.length_ne_top

end PID

section Ring

variable {𝒪 : Type u} {T : Type w} [CommRing 𝒪] [CommRing T] [Algebra 𝒪 T] (πT : T →ₐ[𝒪] 𝒪)

theorem πT_surjective : Function.Surjective πT :=
  fun c => ⟨algebraMap 𝒪 T c, πT.commutes c⟩

theorem sub_algebraMap_mem_ker (t : T) : t - algebraMap 𝒪 T (πT t) ∈ RingHom.ker πT := by
  simp [RingHom.mem_ker]

theorem mul_eq_zero_of_mem_annihilator {i a : T} (hi : i ∈ (RingHom.ker πT).annihilator)
    (ha : a ∈ RingHom.ker πT) : i * a = 0 := by
  rw [Submodule.mem_annihilator] at hi
  simpa [smul_eq_mul] using hi a ha

theorem exists_eq_smul_of_mem_annihilator [IsDomain 𝒪] [Module.Free 𝒪 T] {e₀ : 𝒪} (he₀ : e₀ ≠ 0)
    (hη : (RingHom.ker πT).annihilator.map πT = Ideal.span ({e₀} : Set 𝒪))
    {x₀ : T} (hx₀ : x₀ ∈ (RingHom.ker πT).annihilator) (hπx₀ : πT x₀ = e₀)
    {i : T} (hi : i ∈ (RingHom.ker πT).annihilator) : ∃ c : 𝒪, i = c • x₀ := by
  have hπi : πT i ∈ Ideal.span ({e₀} : Set 𝒪) := hη ▸ Ideal.mem_map_of_mem πT hi
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hπi
  refine ⟨c, ?_⟩

  set y := i - c • x₀ with hy
  have hyI : y ∈ (RingHom.ker πT).annihilator :=
    Submodule.sub_mem _ hi (Submodule.smul_of_tower_mem _ c hx₀)
  have hy℘ : y ∈ RingHom.ker πT := by
    rw [RingHom.mem_ker, hy, map_sub, map_smul, hπx₀, ← hc, smul_eq_mul, sub_self]
  have hey : e₀ • y = 0 := by
    have h1 : (algebraMap 𝒪 T e₀ - x₀) * y = 0 := by
      rw [mul_comm]
      refine mul_eq_zero_of_mem_annihilator πT hyI ?_
      have := Submodule.neg_mem _ (sub_algebraMap_mem_ker πT x₀)
      rwa [hπx₀, neg_sub] at this
    have h2 : x₀ * y = 0 := mul_eq_zero_of_mem_annihilator πT hx₀ hy℘
    calc e₀ • y = (algebraMap 𝒪 T e₀ - x₀) * y + x₀ * y := by rw [Algebra.smul_def]; ring
      _ = 0 := by rw [h1, h2, add_zero]
  have : y = 0 := (smul_eq_zero_iff_right he₀).mp hey
  rwa [hy, sub_eq_zero] at this

end Ring

section Module

variable {𝒪 : Type u} {T : Type w} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
  [CommRing T] [Algebra 𝒪 T] [Module.Free 𝒪 T] (πT : T →ₐ[𝒪] 𝒪)
  (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
  [Module.Finite 𝒪 M] [Module.Free 𝒪 M]

theorem core {e₀ : 𝒪} (he₀ : e₀ ≠ 0)
    (hη : (RingHom.ker πT).annihilator.map πT = Ideal.span ({e₀} : Set 𝒪)) :
    ∃ c : ℕ∞,
      Module.length 𝒪 (M ⧸ (Submodule.torsionBySet T M ↑(RingHom.ker πT) ⊔
          Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator)) + c =
        (Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) : ℕ∞) *
          Module.length 𝒪 (𝒪 ⧸ Ideal.span ({e₀} : Set 𝒪)) ∧
      (c = 0 ↔ Submodule.torsionBySet T M ↑(RingHom.ker πT) =
        (RingHom.ker πT).annihilator • ⊤) := by
  classical

  set ℘ : Ideal T := RingHom.ker πT with h℘
  set I : Ideal T := ℘.annihilator with hI
  set N℘ : Submodule T M := Submodule.torsionBySet T M ↑℘ with hN℘
  set NI : Submodule T M := Submodule.torsionBySet T M ↑I with hNI

  obtain ⟨x₀, hx₀, hπx₀⟩ : ∃ x₀, x₀ ∈ I ∧ πT x₀ = e₀ := by
    have : e₀ ∈ I.map πT := by rw [hη]; exact Ideal.mem_span_singleton_self e₀
    exact (Ideal.mem_map_iff_of_surjective πT (πT_surjective πT)).mp this
  have hIx₀ : ∀ i ∈ I, ∃ c : 𝒪, i = c • x₀ := fun i hi =>
    exists_eq_smul_of_mem_annihilator πT he₀ hη hx₀ hπx₀ hi

  set P : Submodule 𝒪 M := N℘.restrictScalars 𝒪 with hP
  set Q : Submodule 𝒪 M := NI.restrictScalars 𝒪 with hQ
  let μ : M →ₗ[𝒪] M :=
    { toFun := fun m => x₀ • m
      map_add' := fun m m' => smul_add x₀ m m'
      map_smul' := fun c m => by simp [smul_comm x₀ c m] }
  have hμ : ∀ m, μ m = x₀ • m := fun _ => rfl

  have hμP : ∀ m, μ m ∈ P := by
    intro m
    rw [hμ, hP, Submodule.restrictScalars_mem, hN℘, Submodule.mem_torsionBySet_iff]
    rintro ⟨a, ha⟩
    rw [smul_smul, mul_comm, mul_eq_zero_of_mem_annihilator πT hx₀ ha, zero_smul]

  have hμe : ∀ p ∈ P, μ p = e₀ • p := by
    intro p hp
    rw [hP, Submodule.restrictScalars_mem, hN℘, Submodule.mem_torsionBySet_iff] at hp
    have h1 : (x₀ - algebraMap 𝒪 T e₀) • p = 0 := by
      have := sub_algebraMap_mem_ker πT x₀
      rw [hπx₀] at this
      exact hp ⟨_, this⟩
    rw [hμ, ← algebraMap_smul T e₀ p, ← sub_eq_zero, ← sub_smul, h1]

  have hkerμ : ∀ m, μ m = 0 ↔ m ∈ Q := by
    intro m
    rw [hμ, hQ, Submodule.restrictScalars_mem, hNI, Submodule.mem_torsionBySet_iff]
    constructor
    · rintro h ⟨a, ha⟩
      obtain ⟨c, rfl⟩ := hIx₀ a ha
      rw [smul_assoc, h, smul_zero]
    · intro h
      exact h ⟨x₀, hx₀⟩

  set A : Submodule 𝒪 P := e₀ • (⊤ : Submodule 𝒪 P) with hA
  let θ : M →ₗ[𝒪] P ⧸ A := A.mkQ ∘ₗ LinearMap.codRestrict P μ hμP
  have hθ : ∀ m, θ m = A.mkQ ⟨μ m, hμP m⟩ := fun _ => rfl

  have hkerθ : LinearMap.ker θ = P ⊔ Q := by
    ext m
    rw [LinearMap.mem_ker, hθ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hA,
      Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_sup]
    constructor
    · rintro ⟨p, -, hp⟩
      have hp' : e₀ • (p : M) = x₀ • m := by
        have := congrArg Subtype.val hp
        simp at this
        exact this
      refine ⟨p, p.2, m - p, ?_, add_sub_cancel _ _⟩
      rw [← hkerμ, map_sub, hμe p p.2, hp', ← hμ m, sub_self]
    · rintro ⟨y, hy, z, hz, rfl⟩
      refine ⟨⟨y, hy⟩, Submodule.mem_top, ?_⟩
      apply Subtype.ext
      have hz0 : μ z = 0 := (hkerμ z).mpr hz
      simp only [SetLike.val_smul, map_add, hz0, add_zero]
      exact (hμe y hy).symm

  have hlenPA : Module.length 𝒪 (P ⧸ A) =
      (Module.finrank 𝒪 P : ℕ∞) * Module.length 𝒪 (𝒪 ⧸ Ideal.span ({e₀} : Set 𝒪)) :=
    length_quotient_smul_top P e₀
  have hexact : Module.length 𝒪 (P ⧸ A) =
      Module.length 𝒪 (LinearMap.range θ) + Module.length 𝒪 ((P ⧸ A) ⧸ LinearMap.range θ) :=
    Module.length_eq_add_of_exact (LinearMap.range θ).subtype (LinearMap.range θ).mkQ
      (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)

  have hΩ : Module.length 𝒪 (M ⧸ (N℘ ⊔ NI)) = Module.length 𝒪 (LinearMap.range θ) := by
    have e1 : (M ⧸ (N℘ ⊔ NI)) ≃ₗ[𝒪] M ⧸ (N℘ ⊔ NI).restrictScalars 𝒪 :=
      (Submodule.Quotient.restrictScalarsEquiv 𝒪 (N℘ ⊔ NI)).symm
    have e2 : (M ⧸ (N℘ ⊔ NI).restrictScalars 𝒪) ≃ₗ[𝒪] M ⧸ LinearMap.ker θ :=
      Submodule.quotEquivOfEq _ _ (by rw [Submodule.restrictScalars_sup, hkerθ])
    exact (e1.trans (e2.trans θ.quotKerEquivRange)).length_eq

  have hrank : Module.finrank 𝒪 P = Module.finrank 𝒪 N℘ := by
    let e : P ≃ₗ[𝒪] N℘ :=
      { toFun := fun p => ⟨p.1, p.2⟩
        invFun := fun p => ⟨p.1, p.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact e.finrank_eq

  have hIspan : I = Ideal.span ({x₀} : Set T) := by
    refine le_antisymm (fun i hi => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr hx₀)
    obtain ⟨c, rfl⟩ := hIx₀ i hi
    exact Submodule.smul_of_tower_mem _ c (Ideal.subset_span rfl)
  have hItop : (I • (⊤ : Submodule T M)) = x₀ • (⊤ : Submodule T M) := by
    rw [hIspan, Submodule.ideal_span_singleton_smul]
  refine ⟨Module.length 𝒪 ((P ⧸ A) ⧸ LinearMap.range θ), ?_, ?_⟩
  · rw [hΩ, ← hexact, hlenPA, hrank]
  ·
    rw [Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top,
      hItop]
    constructor
    · intro hsurj
      apply le_antisymm
      · intro p hp
        obtain ⟨m, hm⟩ := hsurj (A.mkQ ⟨p, hp⟩)
        rw [hθ, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hA,
          Submodule.mem_smul_pointwise_iff_exists] at hm
        obtain ⟨r, -, hr⟩ := hm
        have hr' : e₀ • (r : M) = x₀ • m - p := by
          have := congrArg Subtype.val hr
          simp at this
          exact this
        have : p = x₀ • (m - r) := by
          rw [smul_sub, ← hμ r, hμe r r.2, hr', sub_sub_cancel]
        rw [this, Submodule.mem_smul_pointwise_iff_exists]
        exact ⟨m - r, Submodule.mem_top, rfl⟩
      · rintro n hn
        rw [Submodule.mem_smul_pointwise_iff_exists] at hn
        obtain ⟨m, -, rfl⟩ := hn
        exact hμP m
    · intro h q
      obtain ⟨q, rfl⟩ := Submodule.mkQ_surjective A q
      have hq : (q : M) ∈ x₀ • (⊤ : Submodule T M) := h ▸ q.2
      rw [Submodule.mem_smul_pointwise_iff_exists] at hq
      obtain ⟨m, -, hm⟩ := hq
      refine ⟨m, ?_⟩
      rw [hθ]
      congr 1
      exact Subtype.ext hm

end Module

section Assembly

variable {𝒪 : Type u} {T : Type w} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
  [CommRing T] [Algebra 𝒪 T] [Module.Free 𝒪 T] (πT : T →ₐ[𝒪] 𝒪)
  (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
  [Module.Finite 𝒪 M] [Module.Free 𝒪 M]

theorem main (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥) :
    ∃ c : ℕ∞,
      Module.length 𝒪 (M ⧸ (Submodule.torsionBySet T M ↑(RingHom.ker πT) ⊔
          Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator)) + c =
        (Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) : ℕ∞) *
          Module.length 𝒪 (𝒪 ⧸ (RingHom.ker πT).annihilator.map πT) ∧
      (c = 0 ↔ Submodule.torsionBySet T M ↑(RingHom.ker πT) =
        (RingHom.ker πT).annihilator • ⊤) ∧
      (Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) : ℕ∞) *
          Module.length 𝒪 (𝒪 ⧸ (RingHom.ker πT).annihilator.map πT) ≠ ⊤ := by
  obtain ⟨e₀, he⟩ := (IsPrincipalIdealRing.principal ((RingHom.ker πT).annihilator.map πT)).principal
  have he' : (RingHom.ker πT).annihilator.map πT = Ideal.span ({e₀} : Set 𝒪) := he
  have he₀ : e₀ ≠ 0 := by
    rintro rfl
    apply hη
    rw [he', Ideal.span_singleton_eq_bot]
  obtain ⟨c, hc, hciff⟩ := core πT M he₀ he'
  rw [he']
  refine ⟨c, hc, hciff, ?_⟩
  exact WithTop.mul_ne_top (ENat.coe_ne_top _) (length_quotient_span_singleton_ne_top he₀)

end Assembly

end M4cP4NCMOD

theorem solution
    {𝒪 : Type u} {T : Type w} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    [CommRing T] [Algebra 𝒪 T] [Module.Free 𝒪 T]
    (πT : T →ₐ[𝒪] 𝒪) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M] :
    Module.length 𝒪 (M ⧸ (Submodule.torsionBySet T M ↑(RingHom.ker πT) ⊔
        Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator)) =
      (Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) : ℕ∞) *
        Module.length 𝒪 (𝒪 ⧸ (RingHom.ker πT).annihilator.map πT) ↔
    Submodule.torsionBySet T M ↑(RingHom.ker πT) = (RingHom.ker πT).annihilator • ⊤ := by
  obtain ⟨c, hc, hciff, hne⟩ := M4cP4NCMOD.main πT M hη
  rw [← hciff, ← hc]
  constructor
  · intro h
    have hΩ : Module.length 𝒪 (M ⧸ (Submodule.torsionBySet T M ↑(RingHom.ker πT) ⊔
        Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator)) ≠ ⊤ :=
      ne_top_of_le_ne_top hne (hc ▸ le_self_add)
    have h2 := (ENat.addLECancellable_of_ne_top hΩ).add_tsub_cancel_left (b := c)
    rw [← h, tsub_self] at h2
    exact h2.symm
  · intro h
    rw [h, add_zero]

end S_Module_length_quotient_torsionBySet_sup_eq_iff
end P2MW
export P2MW.S_Module_length_quotient_torsionBySet_sup_eq_iff (solution)
