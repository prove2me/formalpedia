-- Prove2me | solution 1 for HomogeneousLocalization.Away.flat_quotientMk_comp_of_forall_flat_piece
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ee37e2ad-ab78-5452-adaf-186a68ae7758

import Mathlib
import Theorems.Thm_HomogeneousLocalization_Away_flat_fromZeroRingHom_comp_algebraMap_of_forall_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HomogeneousLocalization_Away_flat_quotientMk_comp_of_forall_flat_piece

set_option autoImplicit false

universe u v

open HomogeneousLocalization

namespace AWAYQUOTSOL

open DirectSum

section Grading

variable {S : Type u} [CommRing S] {A : Type v} [CommRing A] [Algebra S A]
  (𝒜 : ℕ → Submodule S A) [GradedAlgebra 𝒜] (I : Ideal A)

def 𝓑 (k : ℕ) : Submodule S (A ⧸ I) := (𝒜 k).map (Ideal.Quotient.mkₐ S I).toLinearMap

omit [GradedAlgebra 𝒜] in
theorem mk_mem {k : ℕ} {a : A} (ha : a ∈ 𝒜 k) : Ideal.Quotient.mk I a ∈ 𝓑 𝒜 I k :=
  ⟨a, ha, rfl⟩

scoped instance gradedMonoid : SetLike.GradedMonoid (𝓑 𝒜 I) where
  one_mem := ⟨1, SetLike.one_mem_graded 𝒜, map_one (Ideal.Quotient.mkₐ S I)⟩
  mul_mem := by
    rintro i j x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, SetLike.mul_mem_graded ha hb, map_mul (Ideal.Quotient.mkₐ S I) a b⟩

def g (k : ℕ) : 𝒜 k →ₗ[S] 𝓑 𝒜 I k :=
  (Ideal.Quotient.mkₐ S I).toLinearMap.restrict (p := 𝒜 k) (q := 𝓑 𝒜 I k) (fun a ha => ⟨a, ha, rfl⟩)

omit [GradedAlgebra 𝒜] in
theorem g_apply_coe (k : ℕ) (a : 𝒜 k) : (g 𝒜 I k a : A ⧸ I) = Ideal.Quotient.mk I a := rfl

noncomputable def ψ : A →ₗ[S] ⨁ k, 𝓑 𝒜 I k :=
  (lmap (g 𝒜 I)) ∘ₗ (decomposeLinearEquiv 𝒜).toLinearMap

theorem ψ_apply (a : A) : ψ 𝒜 I a = lmap (g 𝒜 I) (decompose 𝒜 a) := rfl

omit [GradedAlgebra 𝒜] in
theorem coe_lmap [DecidableEq ℕ] (x : ⨁ k, 𝒜 k) :
    DirectSum.coeLinearMap (𝓑 𝒜 I) (lmap (g 𝒜 I) x) =
      Ideal.Quotient.mkₐ S I (DirectSum.coeLinearMap 𝒜 x) := by
  suffices h : DirectSum.coeLinearMap (𝓑 𝒜 I) ∘ₗ lmap (g 𝒜 I) =
      (Ideal.Quotient.mkₐ S I).toLinearMap ∘ₗ DirectSum.coeLinearMap 𝒜 from
    LinearMap.congr_fun h x
  refine linearMap_ext _ fun k => LinearMap.ext fun a => ?_
  simp only [LinearMap.comp_apply, lmap_lof]
  rw [lof_eq_of, lof_eq_of, coeLinearMap_of, coeLinearMap_of]
  rfl

theorem ψ_eq_zero (hI : ∀ a ∈ I, ∀ k : ℕ, (DirectSum.decompose 𝒜 a k : A) ∈ I)
    {a : A} (ha : a ∈ I) : ψ 𝒜 I a = 0 := by
  classical
  refine DFinsupp.ext fun k => ?_
  rw [ψ_apply, lmap_apply, DirectSum.zero_apply]
  apply Subtype.ext
  rw [g_apply_coe, Submodule.coe_zero, Ideal.Quotient.eq_zero_iff_mem]
  exact hI a ha k

noncomputable def δ (hI : ∀ a ∈ I, ∀ k : ℕ, (DirectSum.decompose 𝒜 a k : A) ∈ I) :
    (A ⧸ I) →ₗ[S] ⨁ k, 𝓑 𝒜 I k where
  toFun q := Quotient.liftOn' q (ψ 𝒜 I) (fun a b hab => by
    have hab' : a - b ∈ I := (Submodule.quotientRel_def I).1 hab
    have h0 := ψ_eq_zero 𝒜 I hI hab'
    rwa [map_sub, sub_eq_zero] at h0)
  map_add' x y := by
    induction x using Quotient.inductionOn' with | h a =>
    induction y using Quotient.inductionOn' with | h b =>
    exact map_add (ψ 𝒜 I) a b
  map_smul' s x := by
    induction x using Quotient.inductionOn' with | h a =>
    exact map_smul (ψ 𝒜 I) s a

theorem δ_mk (hI : ∀ a ∈ I, ∀ k : ℕ, (DirectSum.decompose 𝒜 a k : A) ∈ I) (a : A) :
    δ 𝒜 I hI (Ideal.Quotient.mk I a) = ψ 𝒜 I a := rfl

@[reducible] noncomputable def gradedAlgebra
    (hI : ∀ a ∈ I, ∀ k : ℕ, (DirectSum.decompose 𝒜 a k : A) ∈ I) : GradedAlgebra (𝓑 𝒜 I) :=
  { (gradedMonoid 𝒜 I),
    (Decomposition.ofLinearMap (𝓑 𝒜 I) (δ 𝒜 I hI)
      (by
        classical
        refine LinearMap.ext fun x => ?_
        induction x using Quotient.inductionOn with
        | h a =>
        change DirectSum.coeLinearMap (𝓑 𝒜 I) (δ 𝒜 I hI (Ideal.Quotient.mk I a)) = Ideal.Quotient.mk I a
        rw [δ_mk, ψ_apply, coe_lmap]
        change Ideal.Quotient.mk I (DirectSum.coeLinearMap 𝒜 (decompose 𝒜 a)) = Ideal.Quotient.mk I a
        congr 1
        exact (decompose 𝒜).symm_apply_apply a)
      (by
        classical
        refine linearMap_ext _ fun k => LinearMap.ext fun b => ?_
        obtain ⟨_, ⟨a, ha, rfl⟩⟩ := b
        simp only [LinearMap.comp_apply, LinearMap.id_apply]
        rw [lof_eq_of, coeLinearMap_of]
        change δ 𝒜 I hI (Ideal.Quotient.mk I a) = _
        rw [δ_mk, ψ_apply, decompose_of_mem 𝒜 ha, ← lof_eq_of S, lmap_lof]
        rfl)) with }

theorem flat_piece (hflat : ∀ k : ℕ, Module.Flat S (↥(𝒜 k) ⧸ Submodule.comap (𝒜 k).subtype (I.restrictScalars S)))
    (k : ℕ) : Module.Flat S (𝓑 𝒜 I k) := by
  haveI := hflat k
  have hker : LinearMap.ker (g 𝒜 I k) = Submodule.comap (𝒜 k).subtype (I.restrictScalars S) := by
    ext a
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.restrictScalars_mem, Submodule.subtype_apply,
      ← Ideal.Quotient.eq_zero_iff_mem]
    exact ⟨fun h => congr_arg Subtype.val h, fun h => Subtype.ext h⟩
  have hrange : LinearMap.range (g 𝒜 I k) = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨_, ⟨a, ha, rfl⟩⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  let e : (↥(𝒜 k) ⧸ Submodule.comap (𝒜 k).subtype (I.restrictScalars S)) ≃ₗ[S] 𝓑 𝒜 I k :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      ((g 𝒜 I k).quotKerEquivRange.trans (LinearEquiv.ofTop _ hrange))
  exact Module.Flat.of_linearEquiv e.symm

theorem algebraMap_mem (s : S) : algebraMap S A s ∈ 𝒜 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ s (SetLike.one_mem_graded 𝒜)

end Grading

section Localise

variable {S : Type u} [CommRing S] {A : Type v} [CommRing A] [Algebra S A]
  (𝒜 : ℕ → Submodule S A) [GradedAlgebra 𝒜] (I : Ideal A) [GradedAlgebra (𝓑 𝒜 I)]

def θ : 𝒜 →+*ᵍ 𝓑 𝒜 I :=
  { Ideal.Quotient.mk I with
    map_mem := fun ha => mk_mem 𝒜 I ha }

theorem θ_apply (a : A) : θ 𝒜 I a = Ideal.Quotient.mk I a := rfl

variable {d : ℕ} {f : A}

noncomputable def Φ (f : A) : Away 𝒜 f →+* Away (𝓑 𝒜 I) (θ 𝒜 I f) := Away.map (θ 𝒜 I) f

theorem Φ_surjective (hf : f ∈ 𝒜 d) : Function.Surjective (Φ 𝒜 I f) := by
  intro z
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective (𝓑 𝒜 I) ((θ 𝒜 I).map_mem hf) z
  obtain ⟨a, ha, rfl⟩ := hb
  exact ⟨Away.mk 𝒜 hf n a ha, by rw [Φ, Away.map_mk (θ 𝒜 I) f hf n a ha]; rfl⟩

def G (f : A) : Set (Away 𝒜 f) :=
  {x | ∃ y : NumDenSameDeg 𝒜 (Submonoid.powers f), (y.num : A) ∈ I ∧ HomogeneousLocalization.mk y = x}

theorem ker_Φ (hf : f ∈ 𝒜 d) : RingHom.ker (Φ 𝒜 I f) = Ideal.span (G 𝒜 I f) := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf x
    rw [Φ, Away.map_mk (θ 𝒜 I) f hf n a ha] at hx
    have hval := congr_arg HomogeneousLocalization.val hx
    rw [Away.val_mk, HomogeneousLocalization.val_zero,
      ← Localization.mk_zero (1 : Submonoid.powers (θ 𝒜 I f)),
      Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hval
    obtain ⟨c, hc⟩ := hval
    simp only [Submonoid.coe_one, one_mul, mul_zero] at hc
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).1 c.2
    have hmem : f ^ m * a ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, ← θ_apply 𝒜 I, ← θ_apply 𝒜 I, hm]
      exact hc
    apply Ideal.subset_span
    refine ⟨⟨(m + n) • d, ⟨f ^ m * a, ?_⟩, ⟨f ^ (m + n), SetLike.pow_mem_graded _ hf⟩, ⟨m + n, rfl⟩⟩, hmem, ?_⟩
    · rw [add_smul]; exact SetLike.mul_mem_graded (SetLike.pow_mem_graded _ hf) ha
    · apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.val_mk, Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      exact ⟨1, by simp only [Submonoid.coe_one, one_mul]; ring⟩
  · rw [Ideal.span_le]
    rintro x ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, Φ, Away.map, HomogeneousLocalization.map_mk]
    apply HomogeneousLocalization.mk_eq_zero_of_num
    apply Subtype.ext
    change Ideal.Quotient.mk I (y.num : A) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 hy

noncomputable abbrev φ (f : A) : S →+* Away 𝒜 f :=
  (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f)).comp
    ((GradedRing.projZeroRingHom' 𝒜).comp (algebraMap S A))

theorem Φ_comp_φ :
    (Φ 𝒜 I f).comp (φ 𝒜 f) =
      (HomogeneousLocalization.fromZeroRingHom (𝓑 𝒜 I) (Submonoid.powers (θ 𝒜 I f))).comp
        ((GradedRing.projZeroRingHom' (𝓑 𝒜 I)).comp (algebraMap S (A ⧸ I))) := by
  refine RingHom.ext fun s => ?_
  apply HomogeneousLocalization.val_injective
  simp only [RingHom.comp_apply, Φ, Away.map, HomogeneousLocalization.fromZeroRingHom,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk]
  have h1 : (GradedRing.projZeroRingHom' 𝒜 (algebraMap S A s) : A) = algebraMap S A s := by
    rw [GradedRing.coe_projZeroRingHom'_apply, GradedRing.projZeroRingHom_apply,
      decompose_of_mem_same 𝒜 (algebraMap_mem 𝒜 s)]
  have h2 : (GradedRing.projZeroRingHom' (𝓑 𝒜 I) (algebraMap S (A ⧸ I) s) : A ⧸ I) =
      algebraMap S (A ⧸ I) s := by
    rw [GradedRing.coe_projZeroRingHom'_apply, GradedRing.projZeroRingHom_apply]
    apply decompose_of_mem_same (𝓑 𝒜 I)
    exact mk_mem 𝒜 I (algebraMap_mem 𝒜 s)
  congr 1
  · change (θ 𝒜 I) (GradedRing.projZeroRingHom' 𝒜 (algebraMap S A s) : A) = _
    rw [h1, h2, θ_apply, Ideal.Quotient.mk_algebraMap]

end Localise

theorem flat_of_eq {R : Type u} {B : Type v} [CommRing R] [CommRing B] (φ' : R →+* B)
    {J J' : Ideal B} (h : J = J') (hJ' : ((Ideal.Quotient.mk J').comp φ').Flat) :
    ((Ideal.Quotient.mk J).comp φ').Flat := by
  subst h; exact hJ'

end AWAYQUOTSOL
p2m_reactivate "P2MW.S_HomogeneousLocalization_Away_flat_quotientMk_comp_of_forall_flat_piece.AWAYQUOTSOL"

open AWAYQUOTSOL DirectSum in

theorem solution
    {S : Type u} [CommRing S] {A : Type v} [CommRing A] [Algebra S A]
    (𝒜 : ℕ → Submodule S A) [GradedAlgebra 𝒜]
    (I : Ideal A) (hI : ∀ a ∈ I, ∀ k : ℕ, (DirectSum.decompose 𝒜 a k : A) ∈ I)
    (hflat : ∀ k : ℕ, Module.Flat S (↥(𝒜 k) ⧸ Submodule.comap (𝒜 k).subtype (I.restrictScalars S)))
    {d : ℕ} (f : A) (hf : f ∈ 𝒜 d) :
    ((Ideal.Quotient.mk (Ideal.span {x : Away 𝒜 f |
          ∃ y : NumDenSameDeg 𝒜 (Submonoid.powers f), (y.num : A) ∈ I ∧ HomogeneousLocalization.mk y = x})).comp
      ((HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f)).comp
        ((GradedRing.projZeroRingHom' 𝒜).comp (algebraMap S A)))).Flat := by
  letI := gradedAlgebra 𝒜 I hI

  have hB := HomogeneousLocalization.Away.flat_fromZeroRingHom_comp_algebraMap_of_forall_flat (𝓑 𝒜 I) (flat_piece 𝒜 I hflat) (θ 𝒜 I f) ((θ 𝒜 I).map_mem hf)
  rw [← Φ_comp_φ 𝒜 I] at hB

  change ((Ideal.Quotient.mk (Ideal.span (G 𝒜 I f))).comp (φ 𝒜 f)).Flat
  refine flat_of_eq (φ 𝒜 f) (ker_Φ 𝒜 I hf).symm ?_
  let e := RingHom.quotientKerEquivOfSurjective (Φ_surjective 𝒜 I hf)
  have he : (Ideal.Quotient.mk (RingHom.ker (Φ 𝒜 I f))).comp (φ 𝒜 f) =
      e.symm.toRingHom.comp ((Φ 𝒜 I f).comp (φ 𝒜 f)) := by
    refine RingHom.ext fun s => ?_
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
  rw [he]
  exact RingHom.Flat.comp hB (RingHom.Flat.of_bijective e.symm.bijective)

end S_HomogeneousLocalization_Away_flat_quotientMk_comp_of_forall_flat_piece
end P2MW
export P2MW.S_HomogeneousLocalization_Away_flat_quotientMk_comp_of_forall_flat_piece (solution)
