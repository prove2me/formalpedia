-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.of_forall_isPullback_away
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/92f57264-881c-52fc-8936-ad5c0d97f290

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_forall_isPullback_away

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

namespace G2ASPBLocal

variable {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
  (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]

include hr in

theorem exists_not_mem (x : PrimeSpectrum S) : ∃ i, r i ∉ x.asIdeal := by
  by_contra h
  push_neg at h
  have hle : Ideal.span (Set.range r) ≤ x.asIdeal := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  rw [hr, top_le_iff] at hle
  exact x.isPrime.ne_top hle

include hr in

noncomputable def cov : (Spec (CommRingCat.of S)).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin k) (fun i => Spec (CommRingCat.of (B i)))
    (fun i => Spec.map (CommRingCat.ofHom (algebraMap S (B i))))
    (by
      intro x
      obtain ⟨i, hi⟩ := exists_not_mem r hr x
      have hx : x ∈ Set.range (PrimeSpectrum.comap (algebraMap S (B i))) := by
        rw [PrimeSpectrum.localization_away_comap_range (B i) (r i)]; exact hi
      obtain ⟨y, hy⟩ := hx
      exact ⟨i, y, hy⟩)
    (fun i => IsOpenImmersion.of_isLocalization (r i))

theorem cov_f (i : Fin k) : (cov r hr B).f i = Spec.map (CommRingCat.ofHom (algebraMap S (B i))) := rfl

variable {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
  {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (g : ∀ i, A' i ⟶ A)
  (hg : ∀ i, IsPullback (g i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))

include r hr hg in
theorem isOpenImmersion_g (i : Fin k) : IsOpenImmersion (g i) :=
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))) := IsOpenImmersion.of_isLocalization (r i)
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hg i).flip inferInstance

include r hr hg in

theorem of_pieces (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P] (h : ∀ i, P (f' i)) : P f := by
  refine IsZariskiLocalAtTarget.of_openCover (P := P) (cov r hr B) fun i => ?_
  dsimp only [Scheme.Cover.pullbackHom, cov, Scheme.Cover.mkOfCovers_X, Scheme.Cover.mkOfCovers_f]
  erw [← (hg i).isoPullback_inv_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).mpr (h i)

include r hr hg in

theorem fibre_eq_image (i : Fin k) (s' : ↥(Spec (CommRingCat.of (B i)))) :
    f.base ⁻¹' {(Spec.map (CommRingCat.ofHom (algebraMap S (B i)))).base s'} = (g i).base '' ((f' i).base ⁻¹' {s'}) := by
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))) := IsOpenImmersion.of_isLocalization (r i)
  have hinj := (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))).isOpenEmbedding.injective
  have hw : ∀ x, f.base ((g i).base x) = (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))).base ((f' i).base x) := by
    intro x
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, (hg i).w]
  ext y
  constructor
  · intro hy
    have hy' : y ∈ Set.range (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (B i))))).base := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨s', hy.symm⟩
    obtain ⟨z, hz⟩ := hy'
    have hy'' : y ∈ Set.range (g i).base := by
      refine ⟨(hg i).isoPullback.inv.base z, ?_⟩
      rw [← Scheme.Hom.comp_apply, (hg i).isoPullback_inv_fst]
      exact hz
    obtain ⟨x, rfl⟩ := hy''
    refine ⟨x, ?_, rfl⟩
    show (f' i).base x ∈ ({s'} : Set _)
    rw [Set.mem_singleton_iff]
    apply hinj
    rw [← hw]; exact hy
  · rintro ⟨x, hx, rfl⟩
    show f.base ((g i).base x) ∈ ({_} : Set _)
    rw [Set.mem_singleton_iff, hw, Set.mem_singleton_iff.mp hx]

include r hr hg in

theorem topologicalKrullDim_fibre_eq (i : Fin k) (s' : ↥(Spec (CommRingCat.of (B i)))) :
    topologicalKrullDim ↥(f.base ⁻¹' {(Spec.map (CommRingCat.ofHom (algebraMap S (B i)))).base s'}) =
      topologicalKrullDim ↥((f' i).base ⁻¹' {s'}) := by
  haveI := isOpenImmersion_g r hr B f f' g hg i
  have himg := fibre_eq_image r hr B f f' g hg i s'
  let φ : ↥((f' i).base ⁻¹' {s'}) → ↥(f.base ⁻¹' {(Spec.map (CommRingCat.ofHom (algebraMap S (B i)))).base s'}) :=
    fun x => ⟨(g i).base x.1, by rw [himg]; exact ⟨x.1, x.2, rfl⟩⟩
  have hemb : Topology.IsEmbedding φ :=
    ((g i).isOpenEmbedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal).codRestrict _ _
  have hsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [himg] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  exact (IsHomeomorph.topologicalKrullDim_eq φ (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hemb, hsurj⟩)).symm

end G2ASPBLocal

open G2ASPBLocal in
theorem solution
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (g : ∀ i, A' i ⟶ A)
    (hg : ∀ i, IsPullback (g i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
    (h : ∀ i, AbelianSchemePropertyBundle (B i) (f' i)) (g₀ : ℕ)
    (hdim : ∀ (i : Fin k) (s' : ↥(Spec (CommRingCat.of (B i)))), topologicalKrullDim ↥((f' i).base ⁻¹' {s'}) = g₀)
    (hL : Nonempty (RelativeGroupLaw S f)) :
    AbelianSchemePropertyBundle S f ∧
      ∀ s : ↥(Spec (CommRingCat.of S)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g₀ := by
  have hsm : Smooth f := of_pieces r hr B f f' g hg @Smooth fun i => (h i).smooth
  have hpr : IsProper f := of_pieces r hr B f f' g hg @IsProper fun i => (h i).proper

  have hpt : ∀ s : ↥(Spec (CommRingCat.of S)), ∃ (i : Fin k) (s' : ↥(Spec (CommRingCat.of (B i)))),
      (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))).base s' = s := by
    intro s
    obtain ⟨i, hi⟩ := exists_not_mem r hr s
    have hx : s ∈ Set.range (PrimeSpectrum.comap (algebraMap S (B i))) := by
      rw [PrimeSpectrum.localization_away_comap_range (B i) (r i)]; exact hi
    obtain ⟨y, hy⟩ := hx
    exact ⟨i, y, hy⟩
  refine ⟨⟨hsm, hpr, fun s => ?_, hL⟩, fun s => ?_⟩
  · obtain ⟨i, s', rfl⟩ := hpt s
    rw [fibre_eq_image r hr B f f' g hg i s']
    exact ((h i).connectedFibres s').image _ (g i).base.hom.continuous.continuousOn
  · obtain ⟨i, s', rfl⟩ := hpt s
    rw [topologicalKrullDim_fibre_eq r hr B f f' g hg i s', hdim i s']

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_forall_isPullback_away
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_of_forall_isPullback_away (solution)
