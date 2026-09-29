-- Prove2me | solution 1 for ModularCurve.FullLevel.eq_of_centred_of_centred_twoChartIntegralModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/5d519c95-1729-5ccd-b0a0-9c8426bd3e67

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_eq_of_centred_of_centred_twoChartIntegralModel

set_option autoImplicit false

section E137gen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
universe u

namespace E137

open AlgebraicCurve.TwoChartIntegralModel

theorem exists_of_ιFin_eq_ιInf {R F : Type u} [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (y : ↥(XFin R F j)) (y' : ↥(XInf R F j))
    (h : (ιFin R F j).base y = (ιInf R F j).base y') :
    ∃ z : ↥(XMid R F j), (fFin R F j).base z = y ∧ (fInf R F j).base z = y' := by
  have h' : (colimit.ι (span (fFin R F j) (fInf R F j)) WalkingSpan.left).base y =
      (colimit.ι (span (fFin R F j) (fInf R F j)) WalkingSpan.right).base y' := h
  obtain ⟨k, fi, fj, z, h1, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff _).mp h'
  rcases k with (_ | _ | _)
  · obtain rfl : fi = WalkingSpan.Hom.fst := Subsingleton.elim _ _
    obtain rfl : fj = WalkingSpan.Hom.snd := Subsingleton.elim _ _
    refine ⟨z, ?_, ?_⟩
    · have h__ := h1
      try simp only [span_map_fst] at h__
      try simp only [span_map_fst]
      exact h__
    · have h__ := h2
      try simp only [span_map_snd] at h__
      try simp only [span_map_snd]
      exact h__
  · exact (by cases (show WidePushoutShape.Hom (some WalkingPair.left) (some WalkingPair.right) from fj))
  · exact (by cases (show WidePushoutShape.Hom (some WalkingPair.right) (some WalkingPair.left) from fi))

def InStalkG {R F : Type u} [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (x : ↥(TwoChartIntegralModel R F j)) (f : F) : Prop :=
  (∀ y : ↥(XFin R F j), (ιFin R F j).base y = x →
    ∃ g h : ↥(chartAlgFin R F j), h ∉ y.asIdeal ∧ f * (h : F) = (g : F)) ∧
  (∀ y : ↥(XInf R F j), (ιInf R F j).base y = x →
    ∃ g h : ↥(chartAlgInf R F j), h ∉ y.asIdeal ∧ f * (h : F) = (g : F))

def InMaxG {R F : Type u} [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (x : ↥(TwoChartIntegralModel R F j)) (f : F) : Prop :=
  (∀ y : ↥(XFin R F j), (ιFin R F j).base y = x →
    ∃ g h : ↥(chartAlgFin R F j), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : F) = (g : F)) ∧
  (∀ y : ↥(XInf R F j), (ιInf R F j).base y = x →
    ∃ g h : ↥(chartAlgInf R F j), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : F) = (g : F))

set_option maxHeartbeats 1600000 in

theorem chartFin_spec {R F : Type u} [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (V S : F → Prop) (y : ↥(XFin R F j))
    (hc : ∀ f : F, InStalkG j ((ιFin R F j).base y) f → V f ∧ (S f ↔ InMaxG j ((ιFin R F j).base y) f)) :
    ∀ b : ↥(chartAlgFin R F j), V (b : F) ∧ (S (b : F) ↔ b ∈ y.asIdeal) := by
  intro b
  have h1 : (1 : ↥(chartAlgFin R F j)) ∉ y.asIdeal := fun h => y.2.ne_top ((Ideal.eq_top_iff_one _).mpr h)

  have cross : ∀ y'' : ↥(XInf R F j), (ιInf R F j).base y'' = (ιFin R F j).base y →
      ∃ g h : ↥(chartAlgInf R F j), h ∉ y''.asIdeal ∧ (b : F) * (h : F) = (g : F) ∧
        (b ∈ y.asIdeal → g ∈ y''.asIdeal) := by
    intro y'' hy''
    obtain ⟨z, hz1, hz2⟩ := exists_of_ιFin_eq_ιInf j y y'' hy''.symm
    have hyz : y.asIdeal = Ideal.comap (inclFin R F j).toRingHom z.asIdeal := by
      rw [← hz1]; exact PrimeSpectrum.comap_asIdeal _ _
    have hy''z : y''.asIdeal = Ideal.comap (inclInf R F j).toRingHom z.asIdeal := by
      rw [← hz2]; exact PrimeSpectrum.comap_asIdeal _ _
    letI := (inclInf R F j).toRingHom.toAlgebra
    haveI := isLocalization_away_inclInf R F j
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hab⟩ :=
      IsLocalization.surj (Submonoid.powers (jInvChartInf R F j)) (inclFin R F j b)
    dsimp only at hab
    have hab' : (inclInf R F j) a = inclFin R F j b * (inclInf R F j) (jInvChartInf R F j ^ n) := hab.symm
    refine ⟨a, jInvChartInf R F j ^ n, ?_, ?_, ?_⟩
    · intro hmem
      have hu : IsUnit ((inclInf R F j) (jInvChartInf R F j ^ n)) := by
        rw [map_pow]; exact (isUnit_inclInf_jInvChartInf R F j).pow n
      rw [hy''z, Ideal.mem_comap] at hmem
      exact z.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
    · have := congrArg Subtype.val hab'
      simp only [Subalgebra.coe_mul, coe_chartIncl, map_pow, SubmonoidClass.coe_pow] at this
      exact this.symm
    · intro hb
      rw [hy''z, Ideal.mem_comap]
      change (inclInf R F j) a ∈ z.asIdeal
      rw [hab']
      rw [hyz, Ideal.mem_comap] at hb
      exact Ideal.mul_mem_right _ _ hb
  have hst : InStalkG j ((ιFin R F j).base y) b := by
    refine ⟨fun y₂ hy₂ => ?_, fun y'' hy'' => ?_⟩
    · obtain rfl : y₂ = y := (ιFin R F j).isOpenEmbedding.injective hy₂
      exact ⟨b, 1, h1, by simp⟩
    · obtain ⟨g, h, hh, hbh, -⟩ := cross y'' hy''
      exact ⟨g, h, hh, hbh⟩
  obtain ⟨hV, hS⟩ := hc b hst
  refine ⟨hV, hS.trans ⟨fun hm => ?_, fun hb => ?_⟩⟩
  · obtain ⟨g, h, hh, hg, hbh⟩ := hm.1 y rfl
    have hbh' : b * h = g := Subtype.ext (by simpa using hbh)
    have : b * h ∈ y.asIdeal := hbh' ▸ hg
    exact ((y.2.mem_or_mem this).resolve_right hh)
  · refine ⟨fun y₂ hy₂ => ?_, fun y'' hy'' => ?_⟩
    · obtain rfl : y₂ = y := (ιFin R F j).isOpenEmbedding.injective hy₂
      exact ⟨b, 1, h1, hb, by simp⟩
    · obtain ⟨g, h, hh, hbh, hg⟩ := cross y'' hy''
      exact ⟨g, h, hh, hg hb, hbh⟩

theorem exists_of_ιInf_eq_ιFin {R F : Type u} [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (y : ↥(XInf R F j)) (y' : ↥(XFin R F j))
    (h : (ιInf R F j).base y = (ιFin R F j).base y') :
    ∃ z : ↥(XMid R F j), (fInf R F j).base z = y ∧ (fFin R F j).base z = y' := by
  obtain ⟨z, h1, h2⟩ := exists_of_ιFin_eq_ιInf j y' y h.symm
  exact ⟨z, h2, h1⟩

set_option maxHeartbeats 1600000 in

theorem chartInf_spec {R F : Type u} [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (V S : F → Prop) (y : ↥(XInf R F j))
    (hc : ∀ f : F, InStalkG j ((ιInf R F j).base y) f → V f ∧ (S f ↔ InMaxG j ((ιInf R F j).base y) f)) :
    ∀ b : ↥(chartAlgInf R F j), V (b : F) ∧ (S (b : F) ↔ b ∈ y.asIdeal) := by
  intro b
  have h1 : (1 : ↥(chartAlgInf R F j)) ∉ y.asIdeal := fun h => y.2.ne_top ((Ideal.eq_top_iff_one _).mpr h)

  have cross : ∀ y'' : ↥(XFin R F j), (ιFin R F j).base y'' = (ιInf R F j).base y →
      ∃ g h : ↥(chartAlgFin R F j), h ∉ y''.asIdeal ∧ (b : F) * (h : F) = (g : F) ∧
        (b ∈ y.asIdeal → g ∈ y''.asIdeal) := by
    intro y'' hy''
    obtain ⟨z, hz1, hz2⟩ := exists_of_ιInf_eq_ιFin j y y'' hy''.symm
    have hyz : y.asIdeal = Ideal.comap (inclInf R F j).toRingHom z.asIdeal := by
      rw [← hz1]; exact PrimeSpectrum.comap_asIdeal _ _
    have hy''z : y''.asIdeal = Ideal.comap (inclFin R F j).toRingHom z.asIdeal := by
      rw [← hz2]; exact PrimeSpectrum.comap_asIdeal _ _
    letI := (inclFin R F j).toRingHom.toAlgebra
    haveI := isLocalization_away_inclFin R F j
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hab⟩ :=
      IsLocalization.surj (Submonoid.powers (jChartFin R F j)) (inclInf R F j b)
    dsimp only at hab
    have hab' : (inclFin R F j) a = inclInf R F j b * (inclFin R F j) (jChartFin R F j ^ n) := hab.symm
    refine ⟨a, jChartFin R F j ^ n, ?_, ?_, ?_⟩
    · intro hmem
      have hu : IsUnit ((inclFin R F j) (jChartFin R F j ^ n)) := by
        rw [map_pow]; exact (isUnit_inclFin_jChartFin R F j).pow n
      rw [hy''z, Ideal.mem_comap] at hmem
      exact z.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
    · have := congrArg Subtype.val hab'
      simp only [Subalgebra.coe_mul, coe_chartIncl, map_pow, SubmonoidClass.coe_pow] at this
      exact this.symm
    · intro hb
      rw [hy''z, Ideal.mem_comap]
      change (inclFin R F j) a ∈ z.asIdeal
      rw [hab']
      rw [hyz, Ideal.mem_comap] at hb
      exact Ideal.mul_mem_right _ _ hb
  have hst : InStalkG j ((ιInf R F j).base y) b := by
    refine ⟨fun y'' hy'' => ?_, fun y₂ hy₂ => ?_⟩
    · obtain ⟨g, h, hh, hbh, -⟩ := cross y'' hy''
      exact ⟨g, h, hh, hbh⟩
    · obtain rfl : y₂ = y := (ιInf R F j).isOpenEmbedding.injective hy₂
      exact ⟨b, 1, h1, by simp⟩
  obtain ⟨hV, hS⟩ := hc b hst
  refine ⟨hV, hS.trans ⟨fun hm => ?_, fun hb => ?_⟩⟩
  · obtain ⟨g, h, hh, hg, hbh⟩ := hm.2 y rfl
    have hbh' : b * h = g := Subtype.ext (by simpa using hbh)
    have : b * h ∈ y.asIdeal := hbh' ▸ hg
    exact ((y.2.mem_or_mem this).resolve_right hh)
  · refine ⟨fun y'' hy'' => ?_, fun y₂ hy₂ => ?_⟩
    · obtain ⟨g, h, hh, hbh, hg⟩ := cross y'' hy''
      exact ⟨g, h, hh, hg hb, hbh⟩
    · obtain rfl : y₂ = y := (ιInf R F j).isOpenEmbedding.injective hy₂
      exact ⟨b, 1, h1, hb, by simp⟩

theorem exists_ιInf_eq_ιFin_of_notMem {R F : Type u} [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (y : ↥(XFin R F j)) (hj : jChartFin R F j ∉ y.asIdeal) :
    ∃ y₃ : ↥(XInf R F j), (ιInf R F j).base y₃ = (ιFin R F j).base y := by
  letI := (inclFin R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R F j
  have hy : y ∈ Set.range (PrimeSpectrum.comap (algebraMap ↥(chartAlgFin R F j) ↥(chartAlgMid R F j))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ (jChartFin R F j)]
    exact hj
  obtain ⟨z, hz⟩ := hy
  refine ⟨(fInf R F j).base z, ?_⟩
  have := congrArg (fun k => k.base z) (glue_condition R F j)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
  rw [← this]
  congr 1
  try (rw [← hz]; rfl)

theorem exists_ιFin_eq_ιInf_of_notMem {R F : Type u} [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (y : ↥(XInf R F j)) (hj : jInvChartInf R F j ∉ y.asIdeal) :
    ∃ y₃ : ↥(XFin R F j), (ιFin R F j).base y₃ = (ιInf R F j).base y := by
  letI := (inclInf R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf R F j
  have hy : y ∈ Set.range (PrimeSpectrum.comap (algebraMap ↥(chartAlgInf R F j) ↥(chartAlgMid R F j))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ (jInvChartInf R F j)]
    exact hj
  obtain ⟨z, hz⟩ := hy
  refine ⟨(fFin R F j).base z, ?_⟩
  have := congrArg (fun k => k.base z) (glue_condition R F j)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
  rw [this]
  congr 1
  try (rw [← hz]; rfl)

theorem eq_of_stalk_spec {R F : Type u} [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (V S : F → Prop) (hVS : V j → V j⁻¹ → ¬ S j ∧ ¬ S j⁻¹)
    (x x' : ↥(TwoChartIntegralModel R F j))
    (hc : ∀ f : F, InStalkG j x f → V f ∧ (S f ↔ InMaxG j x f))
    (hc' : ∀ f : F, InStalkG j x' f → V f ∧ (S f ↔ InMaxG j x' f)) : x = x' := by
  have finfin : ∀ y y' : ↥(XFin R F j),
      (∀ f : F, InStalkG j ((ιFin R F j).base y) f → V f ∧ (S f ↔ InMaxG j ((ιFin R F j).base y) f)) →
      (∀ f : F, InStalkG j ((ιFin R F j).base y') f → V f ∧ (S f ↔ InMaxG j ((ιFin R F j).base y') f)) →
      (ιFin R F j).base y = (ιFin R F j).base y' := by
    intro y y' h h'
    congr 1
    apply PrimeSpectrum.ext
    ext b
    exact ((chartFin_spec j V S y h b).2.symm.trans (chartFin_spec j V S y' h' b).2)
  have infinf : ∀ y y' : ↥(XInf R F j),
      (∀ f : F, InStalkG j ((ιInf R F j).base y) f → V f ∧ (S f ↔ InMaxG j ((ιInf R F j).base y) f)) →
      (∀ f : F, InStalkG j ((ιInf R F j).base y') f → V f ∧ (S f ↔ InMaxG j ((ιInf R F j).base y') f)) →
      (ιInf R F j).base y = (ιInf R F j).base y' := by
    intro y y' h h'
    congr 1
    apply PrimeSpectrum.ext
    ext b
    exact ((chartInf_spec j V S y h b).2.symm.trans (chartInf_spec j V S y' h' b).2)

  have fin_to_inf : ∀ y : ↥(XFin R F j),
      (∀ f : F, InStalkG j ((ιFin R F j).base y) f → V f ∧ (S f ↔ InMaxG j ((ιFin R F j).base y) f)) →
      V j⁻¹ → ∃ y₃ : ↥(XInf R F j), (ιInf R F j).base y₃ = (ιFin R F j).base y := by
    intro y h hVinv
    obtain ⟨hVj, hSj⟩ := chartFin_spec j V S y h (jChartFin R F j)
    exact exists_ιInf_eq_ιFin_of_notMem j y (fun hm => (hVS hVj hVinv).1 (hSj.mpr hm))
  rcases mem_range_ιFin_or_mem_range_ιInf R F j x with ⟨y, rfl⟩ | ⟨y, rfl⟩ <;>
  rcases mem_range_ιFin_or_mem_range_ιInf R F j x' with ⟨y', rfl⟩ | ⟨y', rfl⟩
  · exact finfin y y' hc hc'
  · obtain ⟨hVinv, -⟩ := chartInf_spec j V S y' hc' (jInvChartInf R F j)
    obtain ⟨y₃, hy₃⟩ := fin_to_inf y hc hVinv
    rw [← hy₃] at hc ⊢
    exact infinf y₃ y' hc hc'
  · obtain ⟨hVinv, -⟩ := chartInf_spec j V S y hc (jInvChartInf R F j)
    obtain ⟨y₃, hy₃⟩ := fin_to_inf y' hc' hVinv
    rw [← hy₃] at hc' ⊢
    exact infinf y y₃ hc hc'
  · exact infinf y y' hc hc'

end E137

end E137gen

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hR : R.integers = OIg (lineInfty q))
    (hR₀O : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q))

    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ₀ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ₀⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))

    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)
    [IsDiscreteValuationRing ↥A₁] [HenselianLocalRing ↥A₁] :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra

    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ' γ f ∈ F₀) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →

    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∀ (j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))) →
    ∀ [Fact (j₁ ≠ 0)],

    let InStalk : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → Prop := fun x f =>
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
    let InMax : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → Prop := fun x f =>
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
    let Centred : Place (AlgebraicClosure ℚ) ↥(fieldBar q M') → ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun P x =>
      P.IsRational ∧ ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), InStalk x f →
        (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A ∧
          (A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ InMax x f)

    let GoodPt : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun x =>
      (AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base x = closedPoint ↥A₁ ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), x ⤳ y → y = x) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* Ω), RingHom.ker φ = y.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∉ ModularCurve.ssJSet q Ω)

    ∀ x x' : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), GoodPt x → GoodPt x' →
      ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), Centred P x → Centred P x' → x = x' := by
  letI instk₀ : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  intro F₀ hF₀1 hF₀2 hF₀3 hF₀4 instAlg hcompat j₁ hj₁ instFact InStalk InMax Centred GoodPt x x' hgx hgx' P hPx hPx'
  obtain ⟨hrat, hcx⟩ := hPx
  obtain ⟨-, hcx'⟩ := hPx'

  have hmul : ∀ a b : ↥(fieldBar q M'), a ∈ P.toValuationSubring → b ∈ P.toValuationSubring →
      P.evalAt (a * b) = P.evalAt a * P.evalAt b := by
    intro a b ha hb
    apply (algebraMap (AlgebraicClosure ℚ) P.ResidueField).injective
    rw [map_mul, P.algebraMap_evalAt hrat ha, P.algebraMap_evalAt hrat hb, P.algebraMap_evalAt hrat (mul_mem ha hb),
      ← map_mul]
    rfl
  refine E137.eq_of_stalk_spec j₁
    (fun f => ((f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A))
    (fun f => (((f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
      A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1)) ?_ x x' ?_ ?_
  ·
    rintro ⟨hj, hjA⟩ ⟨hji, hjiA⟩
    have hne : j₁ ≠ 0 := Fact.out
    have hjj := mul_inv_cancel₀ hne
    have hcoe : ((j₁ : _) : ↥(fieldBar q M')) * ((j₁⁻¹ : _) : ↥(fieldBar q M')) = 1 := by
      have := congrArg Subtype.val hjj
      simpa using this
    have hprod : P.evalAt ((j₁ : _) : ↥(fieldBar q M')) * P.evalAt ((j₁⁻¹ : _) : ↥(fieldBar q M')) = 1 := by
      rw [← hmul _ _ hj hji, hcoe, Place.evalAt_one]
    have hunit : IsUnit (⟨P.evalAt ((j₁ : _) : ↥(fieldBar q M')), hjA⟩ : ↥A) :=
      IsUnit.of_mul_eq_one ⟨_, hjiA⟩ (Subtype.ext hprod)
    have hunit' : IsUnit (⟨P.evalAt ((j₁⁻¹ : _) : ↥(fieldBar q M')), hjiA⟩ : ↥A) :=
      IsUnit.of_mul_eq_one ⟨_, hjA⟩ (Subtype.ext (by rw [mul_comm] at hprod; exact hprod))
    have h1 := (A.valuation_eq_one_iff _).mp hunit
    have h1' := (A.valuation_eq_one_iff _).mp hunit'
    refine ⟨fun hS => ?_, fun hS => ?_⟩
    · have hlt := hS.2
      change A.valuation (((⟨P.evalAt ((j₁ : _) : ↥(fieldBar q M')), hjA⟩ : ↥A) : AlgebraicClosure ℚ)) < 1 at hlt
      rw [h1] at hlt
      exact lt_irrefl _ hlt
    · have hlt := hS.2
      change A.valuation (((⟨P.evalAt ((j₁⁻¹ : _) : ↥(fieldBar q M')), hjiA⟩ : ↥A) : AlgebraicClosure ℚ)) < 1 at hlt
      rw [h1'] at hlt
      exact lt_irrefl _ hlt
  · intro f hst
    have h := hcx f hst
    exact ⟨⟨h.1, h.2.1⟩, ⟨fun hS => h.2.2.mp hS.2, fun hm => ⟨⟨h.1, h.2.1⟩, h.2.2.mpr hm⟩⟩⟩
  · intro f hst
    have h := hcx' f hst
    exact ⟨⟨h.1, h.2.1⟩, ⟨fun hS => h.2.2.mp hS.2, fun hm => ⟨⟨h.1, h.2.1⟩, h.2.2.mpr hm⟩⟩⟩

end S_ModularCurve_FullLevel_eq_of_centred_of_centred_twoChartIntegralModel
end P2MW
export P2MW.S_ModularCurve_FullLevel_eq_of_centred_of_centred_twoChartIntegralModel (solution)
