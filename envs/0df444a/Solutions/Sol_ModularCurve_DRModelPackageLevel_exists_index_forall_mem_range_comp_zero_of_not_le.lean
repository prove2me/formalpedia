-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_index_forall_mem_range_comp_zero_of_not_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e581e9f4-ba52-5cbe-969a-5f70742234e5

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_ModularCurve_DRModelPackageLevelAPI
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_AlgebraicGeometry_RelPicard_preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Theorems.Thm_GaloisRep_irreducible_natCast_ratLocalizedAt
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_index_forall_mem_range_comp_zero_of_not_le
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

noncomputable section

namespace N1dPack

variable (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]

private abbrev A : Type := ↥(IgusaScheme.chartAlgFin (N₀ * q) q)

private abbrev ιF : Spec (CommRingCat.of (A N₀ q)) ⟶ DRLevel.X N₀ q := IgusaScheme.ιFin (N₀ * q) q

private abbrev Fk {κ : Type} [CommRing κ] (toκ : DRLevel.R q →+* κ) : Scheme.{0} := DRLevel.fibre (N₀ := N₀) toκ

private abbrev fk {κ : Type} [CommRing κ] (toκ : DRLevel.R q →+* κ) : Fk N₀ q toκ ⟶ DRLevel.X N₀ q :=
  pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))

private def T : Set ↥(DRLevel.X N₀ q) := {x | ((DRLevel.toBase N₀ q).base x).asIdeal = Ideal.span {((q : ℕ) : DRLevel.R q)}}

private def xpt (Q : PrimeSpectrum (A N₀ q)) : ↥(DRLevel.X N₀ q) := (ιF N₀ q).base Q

private theorem isMaximal_span_q : (Ideal.span {((q : ℕ) : DRLevel.R q)}).IsMaximal := by
  haveI : IsPrincipalIdealRing (DRLevel.R q) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt q
  exact PrincipalIdealRing.isMaximal_of_irreducible (GaloisRep.irreducible_natCast_ratLocalizedAt q Fact.out)

private theorem ker_eq_span {κ : Type} [Field κ] [CharP κ q] (toκ : DRLevel.R q →+* κ) :
    RingHom.ker toκ = Ideal.span {((q : ℕ) : DRLevel.R q)} := by
  symm
  refine (isMaximal_span_q q).eq_of_le (RingHom.ker_ne_top toκ) ?_
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_natCast]
  exact CharP.cast_eq_zero κ q

private theorem ringHom_ext_R {S : Type} [CommRing S] (f g : DRLevel.R q →+* S) : f = g := by
  have hq : (q : ℕ).Prime := Fact.out
  haveI : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hq)
  haveI := GaloisRep.isLocalization_ratLocalizedAt hq
  exact IsLocalization.ringHom_ext (Ideal.span {(q : ℤ)}).primeCompl (RingHom.ext_int _ _)

private theorem asIdeal_eq_bot {k : Type} [Field k] (z : PrimeSpectrum k) : z.asIdeal = ⊥ :=
  (Ideal.eq_bot_or_top z.asIdeal).resolve_right z.isPrime.ne_top

private theorem specMap_base_apply {R S : CommRingCat} (φ : R ⟶ S) (z : PrimeSpectrum S) :
    (Spec.map φ).base z = PrimeSpectrum.comap φ.hom z := rfl

private theorem asIdeal_specMap {κ : Type} [Field κ] [CharP κ q] (toκ : DRLevel.R q →+* κ)
    (z : ↥(Spec (CommRingCat.of κ))) :
    ((Spec.map (CommRingCat.ofHom toκ)).base z).asIdeal = Ideal.span {((q : ℕ) : DRLevel.R q)} := by
  rw [specMap_base_apply, PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom, asIdeal_eq_bot,
    ← RingHom.ker_eq_comap_bot, ker_eq_span]

private theorem mem_range_specMap_iff {κ : Type} [Field κ] [CharP κ q] (toκ : DRLevel.R q →+* κ)
    (s : ↥(Spec (CommRingCat.of (DRLevel.R q)))) :
    s ∈ Set.range (Spec.map (CommRingCat.ofHom toκ)).base ↔ s.asIdeal = Ideal.span {((q : ℕ) : DRLevel.R q)} := by
  constructor
  · rintro ⟨z, rfl⟩
    exact asIdeal_specMap q toκ z
  · intro hs
    refine ⟨default, PrimeSpectrum.ext ?_⟩
    rw [asIdeal_specMap, hs]

private theorem mem_range_fk_iff {κ : Type} [Field κ] [CharP κ q] (toκ : DRLevel.R q →+* κ) (x : ↥(DRLevel.X N₀ q)) :
    x ∈ Set.range (fk N₀ q toκ).base ↔ x ∈ T N₀ q := by
  rw [Scheme.Pullback.range_fst]
  exact mem_range_specMap_iff q toκ _

private theorem fk_mem_T {κ : Type} [Field κ] [CharP κ q] (toκ : DRLevel.R q →+* κ) (y : ↥(Fk N₀ q toκ)) :
    (fk N₀ q toκ).base y ∈ T N₀ q :=
  (mem_range_fk_iff N₀ q toκ _).mp ⟨y, rfl⟩

private theorem toBase_xpt (Q : PrimeSpectrum (A N₀ q)) :
    (DRLevel.toBase N₀ q).base (xpt N₀ q Q) = (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) (A N₀ q)))).base Q := by
  have h := IgusaScheme.ιFin_igusaTo (N₀ * q) q
  exact congrArg (fun g => g.base Q) h

private theorem xpt_mem_T_iff (Q : PrimeSpectrum (A N₀ q)) : xpt N₀ q Q ∈ T N₀ q ↔ ((q : ℕ) : A N₀ q) ∈ Q.asIdeal := by
  change ((DRLevel.toBase N₀ q).base (xpt N₀ q Q)).asIdeal = _ ↔ _
  rw [toBase_xpt, specMap_base_apply, PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom]
  constructor
  · intro h
    have : ((q : ℕ) : DRLevel.R q) ∈ Ideal.comap (algebraMap (DRLevel.R q) (A N₀ q)) Q.asIdeal := by
      rw [h]; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this
  · intro h
    symm
    refine (isMaximal_span_q q).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    simpa [Ideal.mem_comap] using h

private theorem exists_xpt_of_specializes {x : ↥(DRLevel.X N₀ q)} {Q : PrimeSpectrum (A N₀ q)} (h : x ⤳ xpt N₀ q Q) :
    ∃ Q', x = xpt N₀ q Q' := by
  obtain ⟨Q', hQ'⟩ := (ιF N₀ q).isOpenEmbedding.isOpen_range.stableUnderGeneralization h ⟨Q, rfl⟩
  exact ⟨Q', hQ'.symm⟩

private theorem le_of_xpt_specializes {Q' Q : PrimeSpectrum (A N₀ q)} (h : xpt N₀ q Q' ⤳ xpt N₀ q Q) :
    Q'.asIdeal ≤ Q.asIdeal := by
  have h' : Q' ⤳ Q := ((ιF N₀ q).isOpenEmbedding.isInducing.specializes_iff).mp h
  exact (PrimeSpectrum.le_iff_specializes Q' Q).mpr h'

private theorem xpt_injective : Function.Injective (xpt N₀ q) := (ιF N₀ q).isOpenEmbedding.injective

private theorem eq_xpt_of_mem_T_of_specializes {x : ↥(DRLevel.X N₀ q)} (hx : x ∈ T N₀ q) {Q : PrimeSpectrum (A N₀ q)}
    (hQ : Q.asIdeal ∈ (Ideal.span {((q : ℕ) : A N₀ q)}).minimalPrimes) (h : x ⤳ xpt N₀ q Q) : x = xpt N₀ q Q := by
  obtain ⟨Q', rfl⟩ := exists_xpt_of_specializes N₀ q h
  have hle : Q'.asIdeal ≤ Q.asIdeal := le_of_xpt_specializes N₀ q h
  have hp : ((q : ℕ) : A N₀ q) ∈ Q'.asIdeal := (xpt_mem_T_iff N₀ q Q').mp hx
  have hge : Q.asIdeal ≤ Q'.asIdeal :=
    hQ.2 ⟨Q'.isPrime, (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp))⟩ hle
  rw [PrimeSpectrum.ext (le_antisymm hle hge)]

private theorem xpt_mem_T_of_mem_minimalPrimes {Q : PrimeSpectrum (A N₀ q)}
    (hQ : Q.asIdeal ∈ (Ideal.span {((q : ℕ) : A N₀ q)}).minimalPrimes) : xpt N₀ q Q ∈ T N₀ q :=
  (xpt_mem_T_iff N₀ q Q).mpr (hQ.1.2 (Ideal.mem_span_singleton_self _))

section TwoPoints

variable {P : Fin 2 → Ideal (A N₀ q)} {hP : ∀ i, (P i).IsPrime}

private theorem mem_minimalPrimes_of_hmin
    (hmin : (Ideal.span {((q : ℕ) : A N₀ q)}).minimalPrimes = {P 0, P 1}) (i : Fin 2) :
    P i ∈ (Ideal.span {((q : ℕ) : A N₀ q)}).minimalPrimes := by
  rw [hmin]
  fin_cases i <;> simp

private theorem xpt_ne_of_ne (hne : P 0 ≠ P 1) : xpt N₀ q ⟨P 0, hP 0⟩ ≠ xpt N₀ q ⟨P 1, hP 1⟩ := fun h =>
  hne (congrArg PrimeSpectrum.asIdeal (xpt_injective N₀ q h))

private theorem eq_xptP_of_specializes (hmin : (Ideal.span {((q : ℕ) : A N₀ q)}).minimalPrimes = {P 0, P 1}) (i : Fin 2)
    {x : ↥(DRLevel.X N₀ q)} (hx : x ∈ T N₀ q) (h : x ⤳ xpt N₀ q ⟨P i, hP i⟩) : x = xpt N₀ q ⟨P i, hP i⟩ :=
  eq_xpt_of_mem_T_of_specializes N₀ q hx (mem_minimalPrimes_of_hmin N₀ q hmin i) h

private theorem xptP_mem_range_fk (hmin : (Ideal.span {((q : ℕ) : A N₀ q)}).minimalPrimes = {P 0, P 1}) (i : Fin 2)
    {κ : Type} [Field κ] [CharP κ q] (toκ : DRLevel.R q →+* κ) : xpt N₀ q ⟨P i, hP i⟩ ∈ Set.range (fk N₀ q toκ).base :=
  (mem_range_fk_iff N₀ q toκ _).mpr (xpt_mem_T_of_mem_minimalPrimes N₀ q (mem_minimalPrimes_of_hmin N₀ q hmin i))

private theorem le_of_xptP_specializes (j : Fin 2) (𝔮 : PrimeSpectrum (A N₀ q)) (h : xpt N₀ q ⟨P j, hP j⟩ ⤳ xpt N₀ q 𝔮) :
    P j ≤ 𝔮.asIdeal :=
  le_of_xpt_specializes N₀ q h

end TwoPoints

private theorem match_two {F X : Type*} [TopologicalSpace F] [TopologicalSpace X] (f : F → X) (hf : Continuous f)
    (a b : F) (hab : ∀ z, a ⤳ z ∨ b ⤳ z) (T : Set X) (hT : ∀ z, f z ∈ T)
    (x₀ x₁ : X) (hne : x₀ ≠ x₁) (h₀ : x₀ ∈ Set.range f) (h₁ : x₁ ∈ Set.range f)
    (hmax₀ : ∀ x ∈ T, x ⤳ x₀ → x = x₀) (hmax₁ : ∀ x ∈ T, x ⤳ x₁ → x = x₁) :
    (f a = x₀ ∧ f b = x₁) ∨ (f a = x₁ ∧ f b = x₀) := by
  obtain ⟨z₀, rfl⟩ := h₀
  obtain ⟨z₁, rfl⟩ := h₁
  have key : ∀ (c : F) (z : F), c ⤳ z → (∀ x ∈ T, x ⤳ f z → x = f z) → f c = f z :=
    fun c z hcz hmax => hmax (f c) (hT c) (hcz.map hf)
  rcases hab z₀ with ha₀ | hb₀ <;> rcases hab z₁ with ha₁ | hb₁
  · exact absurd ((key a z₀ ha₀ hmax₀).symm.trans (key a z₁ ha₁ hmax₁)) hne
  · exact Or.inl ⟨key a z₀ ha₀ hmax₀, key b z₁ hb₁ hmax₁⟩
  · exact Or.inr ⟨key a z₁ ha₁ hmax₁, key b z₀ hb₀ hmax₀⟩
  · exact absurd ((key b z₀ hb₀ hmax₀).symm.trans (key b z₁ hb₁ hmax₁)) hne

private theorem match_fibre {P : Fin 2 → Ideal (A N₀ q)} {hP : ∀ i, (P i).IsPrime}
    (hmin : (Ideal.span {((q : ℕ) : A N₀ q)}).minimalPrimes = {P 0, P 1}) (hne : P 0 ≠ P 1)
    {κ : Type} [Field κ] [CharP κ q] (toκ : DRLevel.R q →+* κ) (a b : ↥(Fk N₀ q toκ)) (hab : ∀ z, a ⤳ z ∨ b ⤳ z) :
    ((fk N₀ q toκ).base a = xpt N₀ q ⟨P 0, hP 0⟩ ∧ (fk N₀ q toκ).base b = xpt N₀ q ⟨P 1, hP 1⟩) ∨
      ((fk N₀ q toκ).base a = xpt N₀ q ⟨P 1, hP 1⟩ ∧ (fk N₀ q toκ).base b = xpt N₀ q ⟨P 0, hP 0⟩) :=
  match_two (fk N₀ q toκ).base (fk N₀ q toκ).continuous a b hab (T N₀ q) (fk_mem_T N₀ q toκ) _ _ (xpt_ne_of_ne N₀ q hne)
    (xptP_mem_range_fk N₀ q hmin 0 toκ) (xptP_mem_range_fk N₀ q hmin 1 toκ)
    (fun _ hx h => eq_xptP_of_specializes N₀ q hmin 0 hx h) (fun _ hx h => eq_xptP_of_specializes N₀ q hmin 1 hx h)

section Rho

variable {N₀ q}
variable {K κ : Type} [Field K] [Field κ] {toK : DRLevel.R q →+* K} {toκ : DRLevel.R q →+* κ} (σ : K →+* κ)
  (hσ : σ.comp toK = toκ)

include hσ in
omit [Fact q.Prime] in
private theorem specMap_σ_comp :
    Spec.map (CommRingCat.ofHom σ) ≫ Spec.map (CommRingCat.ofHom toK) = Spec.map (CommRingCat.ofHom toκ) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hσ]

private def ρ : Fk N₀ q toκ ⟶ Fk N₀ q toK :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom σ))
    (by rw [pullback.condition, Category.assoc, specMap_σ_comp σ hσ])

private theorem ρ_fst : ρ (N₀ := N₀) σ hσ ≫ fk N₀ q toK = fk N₀ q toκ := pullback.lift_fst _ _ _

private theorem ρ_snd : ρ (N₀ := N₀) σ hσ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom σ) :=
  pullback.lift_snd _ _ _

private theorem fk_ρ_apply (y : ↥(Fk N₀ q toκ)) : (fk N₀ q toK).base ((ρ (N₀ := N₀) σ hσ).base y) = (fk N₀ q toκ).base y := by
  change (ρ (N₀ := N₀) σ hσ ≫ fk N₀ q toK) y = _
  rw [ρ_fst]

private theorem sectionFibre_ρ (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (DRLevel.R q)))) (DRLevel.toBase N₀ q)) :
    DRLevel.sectionFibre (N₀ := N₀) ε toκ ≫ ρ (N₀ := N₀) σ hσ =
      Spec.map (CommRingCat.ofHom σ) ≫ DRLevel.sectionFibre (N₀ := N₀) ε toK := by
  apply pullback.hom_ext
  · rw [Category.assoc, ρ_fst, DRLevel.sectionFibre_fst, Category.assoc, DRLevel.sectionFibre_fst, ← Category.assoc,
      specMap_σ_comp σ hσ]
  · rw [Category.assoc, ρ_snd, ← Category.assoc, DRLevel.sectionFibre_snd, Category.assoc, DRLevel.sectionFibre_snd,
      Category.id_comp, Category.comp_id]

private theorem ρ_sectionFibre_apply (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (DRLevel.R q)))) (DRLevel.toBase N₀ q))
    (z : ↥(Spec (CommRingCat.of κ))) (z' : ↥(Spec (CommRingCat.of K))) :
    (ρ (N₀ := N₀) σ hσ).base ((DRLevel.sectionFibre (N₀ := N₀) ε toκ).base z) =
      (DRLevel.sectionFibre (N₀ := N₀) ε toK).base z' := by
  change (DRLevel.sectionFibre (N₀ := N₀) ε toκ ≫ ρ (N₀ := N₀) σ hσ) z = _
  rw [sectionFibre_ρ, Scheme.Hom.comp_apply]
  congr 1
  exact Subsingleton.elim _ _

end Rho

private def K₀ : Type := AlgebraicClosure (ZMod q)

private scoped instance K₀field : Field (K₀ q) := inferInstanceAs (Field (AlgebraicClosure (ZMod q)))
private scoped instance K₀charP : CharP (K₀ q) q := inferInstanceAs (CharP (AlgebraicClosure (ZMod q)) q)
private scoped instance K₀algClosed : IsAlgClosed (K₀ q) := inferInstanceAs (IsAlgClosed (AlgebraicClosure (ZMod q)))
private scoped instance K₀decEq : DecidableEq (K₀ q) := Classical.decEq _

private def toK₀ : DRLevel.R q →+* K₀ q :=
  have hq : (q : ℕ).Prime := Fact.out
  haveI : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hq)
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := q) hq
  IsLocalization.lift (M := (Ideal.span {(q : ℤ)}).primeCompl) (g := Int.castRingHom (K₀ q)) (fun y => by
    rw [isUnit_iff_ne_zero, eq_intCast, Ne, CharP.intCast_eq_zero_iff (K₀ q) q]
    have := y.2
    rwa [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton] at this)

private def σ₀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] : K₀ q →+* κ :=
  letI := ZMod.algebra κ q
  (IsAlgClosed.lift (R := ZMod q) (M := κ) (S := AlgebraicClosure (ZMod q))).toRingHom

private theorem σ₀_comp (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] (toκ : DRLevel.R q →+* κ) :
    (σ₀ q κ).comp (toK₀ q) = toκ :=
  ringHom_ext_R q _ _

section Upstairs

variable {N₀ q}
variable {hqN : ¬ q ∣ N₀} (𝔓 : DRModelPackageLevel N₀ q hqN)

section U
variable {κ : Type} [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)

include 𝔓 in
private theorem irred_fibre0 : IrreducibleSpace ↥(DRLevel.fibre0 (N₀ := N₀) toκ) :=
  haveI := 𝔓.isIntegral_fibre0 toκ
  inferInstance

private def η (j : Fin 2) : ↥(Fk N₀ q toκ) :=
  haveI := 𝔓.isIntegral_fibre0 toκ
  (𝔓.comp κ toκ j).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ))

private def ePt : ↥(Fk N₀ q toκ) :=
  (DRLevel.sectionFibre (N₀ := N₀) 𝔓.εinf toκ).base (IsLocalRing.closedPoint κ)

private theorem mem_range_iff_specializes_of_isClosed {C Y : Type*} [TopologicalSpace C] [TopologicalSpace Y]
    [QuasiSober C] [IrreducibleSpace C] (g : C → Y) (hg : Continuous g) (hcl : IsClosed (Set.range g)) (y : Y) :
    y ∈ Set.range g ↔ g (genericPoint C) ⤳ y := by
  constructor
  · rintro ⟨c, rfl⟩
    exact (genericPoint_specializes c).map hg
  · intro h
    rw [specializes_iff_mem_closure] at h
    exact hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨_, rfl⟩) h

private theorem mem_range_comp_iff (j : Fin 2) (y : ↥(Fk N₀ q toκ)) :
    y ∈ Set.range (𝔓.comp κ toκ j).base ↔ η 𝔓 toκ j ⤳ y := by
  haveI := 𝔓.comp_isClosedImmersion κ toκ j
  haveI := 𝔓.isIntegral_fibre0 toκ
  exact mem_range_iff_specializes_of_isClosed (𝔓.comp κ toκ j).base (𝔓.comp κ toκ j).continuous
    (𝔓.comp κ toκ j).isClosedEmbedding.isClosed_range y

private theorem cover (y : ↥(Fk N₀ q toκ)) : η 𝔓 toκ 0 ⤳ y ∨ η 𝔓 toκ 1 ⤳ y := by
  rcases 𝔓.comp_jointly_surjective κ toκ y with h | h
  · exact Or.inl ((mem_range_comp_iff 𝔓 toκ 0 y).mp h)
  · exact Or.inr ((mem_range_comp_iff 𝔓 toκ 1 y).mp h)

private theorem η0_specializes_ePt : η 𝔓 toκ 0 ⤳ ePt 𝔓 toκ :=
  (mem_range_comp_iff 𝔓 toκ 0 _).mp (𝔓.εinf_mem_comp0 κ toκ ⟨IsLocalRing.closedPoint κ, rfl⟩)

omit [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] in

private theorem ePt_mem_trace : ePt 𝔓 toκ ∈ ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔓.smoothLocus :
      (Fk N₀ q toκ).Opens) : Set ↥(Fk N₀ q toκ)) := by
  show (fk N₀ q toκ).base (ePt 𝔓 toκ) ∈ (𝔓.smoothLocus : Set _)
  apply 𝔓.εinf_mem_smoothLocus
  refine ⟨(Spec.map (CommRingCat.ofHom toκ)).base (IsLocalRing.closedPoint κ), ?_⟩
  rw [ePt, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, DRLevel.sectionFibre_fst]

private theorem not_η1_specializes_ePt : ¬ η 𝔓 toκ 1 ⤳ ePt 𝔓 toκ := by
  intro h1
  have hp2 : ePt 𝔓 toκ ∈ Set.range (𝔓.comp κ toκ 1).base := (mem_range_comp_iff 𝔓 toκ 1 _).mpr h1
  have hp1 : ePt 𝔓 toκ ∈ Set.range (𝔓.comp κ toκ 0).base := (mem_range_comp_iff 𝔓 toκ 0 _).mpr (η0_specializes_ePt 𝔓 toκ)

  haveI hp0 : IsProper (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) := 𝔓.isProper_fibre0 toκ
  haveI hs0 : SmoothOfRelativeDimension 1 (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) :=
    𝔓.smoothOfRelativeDimension_one_fibre0 toκ
  haveI : IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ) := 𝔓.isIntegral_fibre0 toκ
  haveI hgi0 : GeometricallyIntegral (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) :=
    AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed _
  haveI := 𝔓.comp_isClosedImmersion κ toκ 0
  haveI := 𝔓.comp_isClosedImmersion κ toκ 1
  have hred := 𝔓.fibre_reduced κ toκ
  haveI := 𝔓.flat
  haveI := 𝔓.lfp
  haveI : Smooth (𝔓.smoothLocus.ι ≫ DRLevel.toBase N₀ q) := by
    haveI := 𝔓.smoothLocus_relDim
    infer_instance
  let i₁ : SchemeHomOver (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)))
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))) := ⟨𝔓.comp κ toκ 0, 𝔓.comp_over κ toκ 0⟩
  let i₂ : SchemeHomOver (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)))
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))) := ⟨𝔓.comp κ toκ 1, 𝔓.comp_over κ toκ 1⟩

  let wb : ↥(Fk N₀ q toκ) → ↥(Fk N₀ q toκ) := (DRLevel.fibreMap 𝔓.w.hom 𝔓.w_over toκ).base
  have hr1 : Set.range (𝔓.comp κ toκ 1).base = wb '' Set.range (𝔓.comp κ toκ 0).base := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun a =>
      (by rw [← 𝔓.comp_w κ toκ]; rfl : (𝔓.comp κ toκ 1).base a = wb ((𝔓.comp κ toκ 0).base a)))
  have hr0 : Set.range (𝔓.comp κ toκ 0).base = wb '' Set.range (𝔓.comp κ toκ 1).base := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun a =>
      (by rw [← 𝔓.comp1_fibreMap_w toκ]; rfl : (𝔓.comp κ toκ 0).base a = wb ((𝔓.comp κ toκ 1).base a)))
  have hne₁ : ¬ Set.range (𝔓.comp κ toκ 0).base ⊆ Set.range (𝔓.comp κ toκ 1).base := fun h =>
    𝔓.range_comp_ne κ toκ (Set.Subset.antisymm h (by rw [hr1]; nth_rw 2 [hr0]; exact Set.image_mono h))
  have hne₂ : ¬ Set.range (𝔓.comp κ toκ 1).base ⊆ Set.range (𝔓.comp κ toκ 0).base := fun h =>
    𝔓.range_comp_ne κ toκ (Set.Subset.antisymm (by rw [hr0]; nth_rw 2 [hr1]; exact Set.image_mono h) h)
  obtain ⟨hU, -, -, -, -⟩ :=
    AlgebraicGeometry.RelPicard.preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves
      (DRLevel.toBase N₀ q) 𝔓.smoothLocus 𝔓.smoothLocus_maximal (Spec.map (CommRingCat.ofHom toκ)) hred
      (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)))
      (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)))
      i₁ i₂ (𝔓.comp_jointly_surjective κ toκ) hne₁ hne₂ (ePt 𝔓 toκ) hp1 (ePt_mem_trace 𝔓 toκ)

  have hpc : ePt 𝔓 toκ ∈ Set.range (pullback.fst (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1) ≫ 𝔓.comp κ toκ 0).base := by
    obtain ⟨a, ha⟩ := hp1
    obtain ⟨b, hb⟩ := hp2
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback a b (ha.trans hb.symm)
    exact ⟨z, by rw [Scheme.Hom.comp_apply, hz1, ha]⟩
  have hpU := ePt_mem_trace 𝔓 toκ
  rw [hU] at hpU
  exact hpU hpc

end U

section K

variable {P : Fin 2 → Ideal (A N₀ q)} {hP : ∀ i, (P i).IsPrime}

private theorem exists_index (hmin : (Ideal.span {((q : ℕ) : A N₀ q)}).minimalPrimes = {P 0, P 1}) (hne : P 0 ≠ P 1)
    {κ : Type} [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ) :
    ∃ i : Fin 2, (fk N₀ q toκ).base (η 𝔓 toκ 0) = xpt N₀ q ⟨P i, hP i⟩ ∧
      ∀ j, j ≠ i → (fk N₀ q toκ).base (η 𝔓 toκ 1) = xpt N₀ q ⟨P j, hP j⟩ := by
  rcases match_fibre N₀ q (hP := hP) hmin hne toκ (η 𝔓 toκ 0) (η 𝔓 toκ 1) (cover 𝔓 toκ) with ⟨h0, h1⟩ | ⟨h1, h0⟩
  · refine ⟨0, h0, fun j hj => ?_⟩
    obtain rfl : j = 1 := by fin_cases j <;> simp_all
    exact h1
  · refine ⟨1, h1, fun j hj => ?_⟩
    obtain rfl : j = 0 := by fin_cases j <;> simp_all
    exact h0

include hP in

private theorem fk_η0_eq (hmin : (Ideal.span {((q : ℕ) : A N₀ q)}).minimalPrimes = {P 0, P 1}) (hne : P 0 ≠ P 1)
    {κ : Type} [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ) :
    (fk N₀ q toκ).base (η 𝔓 toκ 0) = (fk N₀ q (toK₀ q)).base (η 𝔓 (toK₀ q) 0) := by
  have hσ := σ₀_comp q κ toκ

  have h1 : (ρ (N₀ := N₀) (σ₀ q κ) hσ).base (η 𝔓 toκ 0) ⤳ ePt 𝔓 (toK₀ q) := by
    have := (η0_specializes_ePt 𝔓 toκ).map (ρ (N₀ := N₀) (σ₀ q κ) hσ).continuous
    rwa [ePt, ρ_sectionFibre_apply (σ₀ q κ) hσ 𝔓.εinf (IsLocalRing.closedPoint κ)
      (IsLocalRing.closedPoint (K₀ q))] at this

  have h2 : η 𝔓 (toK₀ q) 0 ⤳ (ρ (N₀ := N₀) (σ₀ q κ) hσ).base (η 𝔓 toκ 0) := by
    rcases cover 𝔓 (toK₀ q) ((ρ (N₀ := N₀) (σ₀ q κ) hσ).base (η 𝔓 toκ 0)) with h | h
    · exact h
    · exact absurd (h.trans h1) (not_η1_specializes_ePt 𝔓 (toK₀ q))

  have h3 : (fk N₀ q (toK₀ q)).base (η 𝔓 (toK₀ q) 0) ⤳ (fk N₀ q toκ).base (η 𝔓 toκ 0) := by
    have := h2.map (fk N₀ q (toK₀ q)).continuous
    rwa [fk_ρ_apply] at this
  obtain ⟨i, hi, -⟩ := exists_index 𝔓 (hP := hP) hmin hne toκ
  rw [hi] at h3 ⊢
  exact (eq_xptP_of_specializes N₀ q hmin i (fk_mem_T N₀ q (toK₀ q) _) h3).symm

private theorem goal_of_index (i : Fin 2) {κ : Type} [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ]
    (toκ : DRLevel.R q →+* κ)
    (hi : ∀ j, j ≠ i → (fk N₀ q toκ).base (η 𝔓 toκ 1) = xpt N₀ q ⟨P j, hP j⟩)
    (y : ↥(Fk N₀ q toκ)) (𝔮 : PrimeSpectrum (A N₀ q)) (hy : (fk N₀ q toκ).base y = xpt N₀ q 𝔮)
    (h𝔮 : ∀ j : Fin 2, j ≠ i → ¬ P j ≤ 𝔮.asIdeal) :
    y ∈ Set.range (𝔓.comp κ toκ 0).base ∧ y ∉ Set.range (𝔓.comp κ toκ 1).base := by
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, j ≠ i := ⟨i + 1, by fin_cases i <;> decide⟩
  have hy0 : y ∉ Set.range (𝔓.comp κ toκ 1).base := by
    intro hy0
    have hsp : (fk N₀ q toκ).base (η 𝔓 toκ 1) ⤳ (fk N₀ q toκ).base y :=
      ((mem_range_comp_iff 𝔓 toκ 1 y).mp hy0).map (fk N₀ q toκ).continuous
    rw [hi j hj, hy] at hsp
    exact h𝔮 j hj (le_of_xptP_specializes N₀ q j 𝔮 hsp)
  exact ⟨(𝔓.comp_jointly_surjective κ toκ y).resolve_right hy0, hy0⟩

end K

end Upstairs

end N1dPack
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_index_forall_mem_range_comp_zero_of_not_le.N1dPack"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_index_forall_mem_range_comp_zero_of_not_le.N1dPack"

open N1dPack in
open ModularCurve.DRModelPackageLevel in
theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (P : Fin 2 → Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) (hP : ∀ i, (P i).IsPrime)
    (hmin : (Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))}).minimalPrimes = {P 0, P 1}) (hne : P 0 ≠ P 1) :
    ∃ i : Fin 2, ∀ (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)
      (y : ↥(DRLevel.fibre (N₀ := N₀) toκ)) (𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q)),
      (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base y = (IgusaScheme.ιFin (N₀ * q) q).base 𝔮 →
      (∀ j : Fin 2, j ≠ i → ¬ P j ≤ 𝔮.asIdeal) →
      y ∈ Set.range (𝔓.comp κ toκ 0).base ∧ y ∉ Set.range (𝔓.comp κ toκ 1).base := by

  obtain ⟨i, hiK, -⟩ := exists_index 𝔓 (hP := hP) hmin hne (toK₀ q)
  refine ⟨i, fun κ _ _ _ _ toκ y 𝔮 hy h𝔮 => ?_⟩
  obtain ⟨i', hi', hi''⟩ := exists_index 𝔓 (hP := hP) hmin hne toκ
  have hii' : i = i' := by
    have h1 : xpt N₀ q ⟨P i, hP i⟩ = xpt N₀ q ⟨P i', hP i'⟩ := by
      rw [← hiK, ← hi', fk_η0_eq 𝔓 (hP := hP) hmin hne toκ]
    have h2 : P i = P i' := by simpa using congrArg PrimeSpectrum.asIdeal (xpt_injective N₀ q h1)
    by_contra hc
    apply hne
    fin_cases i <;> fin_cases i' <;> simp_all
  subst hii'
  exact goal_of_index 𝔓 i toκ hi'' y 𝔮 hy h𝔮

end S_ModularCurve_DRModelPackageLevel_exists_index_forall_mem_range_comp_zero_of_not_le
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_index_forall_mem_range_comp_zero_of_not_le (solution)
