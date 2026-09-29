-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_reads_of_goodPt_twoChartIntegralModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/92a590e7-3a1e-5ea4-9526-e0078e281e75

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_ModularCurve_FullLevel_coe_chartAlg_mem_integers_and_exists_residue_algebraMap_eq_twoChartIntegralModel
import Theorems.Thm_ModularCurve_FullLevel_exists_mem_asIdeal_and_residue_ne_zero_of_goodPt_twoChartIntegralModel
import Theorems.Thm_ModularCurve_FullLevel_exists_finiteDimensional_adjoin_xHFunctionFieldC_levelH
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_reads_of_goodPt_twoChartIntegralModel
p2m_attr_erase "instance" "CuspForm.GammaH_finiteIndex ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.qExpandAlgHomC_apply"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory.Limits

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
    · simp only [span_map_fst] at h1
      exact h1
    · simp only [span_map_snd] at h2
      exact h2
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

end E137

namespace E140CR

open AlgebraicCurve.TwoChartIntegralModel E137

theorem cross_fin {R F : Type u} [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (y : ↥(XFin R F j)) (y'' : ↥(XInf R F j)) (hy'' : (ιInf R F j).base y'' = (ιFin R F j).base y)
    (b : ↥(chartAlgFin R F j)) :
    ∃ g h : ↥(chartAlgInf R F j), h ∉ y''.asIdeal ∧ (b : F) * (h : F) = (g : F) ∧
      (b ∈ y.asIdeal ↔ g ∈ y''.asIdeal) := by
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
  have hu : IsUnit ((inclInf R F j) (jInvChartInf R F j ^ n)) := by
    rw [map_pow]; exact (isUnit_inclInf_jInvChartInf R F j).pow n
  refine ⟨a, jInvChartInf R F j ^ n, ?_, ?_, ?_⟩
  · intro hmem
    rw [hy''z, Ideal.mem_comap] at hmem
    exact z.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
  · have := congrArg Subtype.val hab'
    simp only [Subalgebra.coe_mul, coe_chartIncl, map_pow, SubmonoidClass.coe_pow] at this
    exact this.symm
  · rw [hy''z, Ideal.mem_comap, hyz, Ideal.mem_comap]
    change _ ↔ (inclInf R F j) a ∈ z.asIdeal
    rw [hab']
    refine ⟨fun hb => Ideal.mul_mem_right _ _ hb, fun h => ?_⟩
    exact ((z.2.mem_or_mem h).resolve_right (fun h2 => z.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 hu)))

theorem cross_inf {R F : Type u} [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (y : ↥(XInf R F j)) (y'' : ↥(XFin R F j)) (hy'' : (ιFin R F j).base y'' = (ιInf R F j).base y)
    (b : ↥(chartAlgInf R F j)) :
    ∃ g h : ↥(chartAlgFin R F j), h ∉ y''.asIdeal ∧ (b : F) * (h : F) = (g : F) ∧
      (b ∈ y.asIdeal ↔ g ∈ y''.asIdeal) := by
  obtain ⟨z, hz2, hz1⟩ := exists_of_ιFin_eq_ιInf j y'' y hy''
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
  have hu : IsUnit ((inclFin R F j) (jChartFin R F j ^ n)) := by
    rw [map_pow]; exact (isUnit_inclFin_jChartFin R F j).pow n
  refine ⟨a, jChartFin R F j ^ n, ?_, ?_, ?_⟩
  · intro hmem
    rw [hy''z, Ideal.mem_comap] at hmem
    exact z.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
  · have := congrArg Subtype.val hab'
    simp only [Subalgebra.coe_mul, coe_chartIncl, map_pow, SubmonoidClass.coe_pow] at this
    exact this.symm
  · rw [hy''z, Ideal.mem_comap, hyz, Ideal.mem_comap]
    change _ ↔ (inclFin R F j) a ∈ z.asIdeal
    rw [hab']
    refine ⟨fun hb => Ideal.mul_mem_right _ _ hb, fun h => ?_⟩
    exact ((z.2.mem_or_mem h).resolve_right (fun h2 => z.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 hu)))

end E140CR

namespace E140CR

open AlgebraicCurve.TwoChartIntegralModel E137 IsLocalRing

theorem not_isUnit_map_of_mem_maximalIdeal {S T : Type*} [CommRing S] [CommRing T] [IsLocalRing S] [Nontrivial T]
    (f : S →+* T) (hf : Function.Surjective f) {m : S} (hm : m ∈ maximalIdeal S) : ¬ IsUnit (f m) := by
  intro hu
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨n, rfl⟩ := hf v
  have hker : RingHom.ker f ≤ maximalIdeal S :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f)
  have h1 : m * n - 1 ∈ maximalIdeal S := hker (by rw [RingHom.mem_ker, map_sub, map_mul, hv, map_one, sub_self])
  have h2 : m * n ∈ maximalIdeal S := Ideal.mul_mem_right _ _ hm
  have : (1 : S) ∈ maximalIdeal S := by
    have := Ideal.sub_mem _ h2 h1
    rwa [sub_sub_cancel] at this
  exact (maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).mpr this)

theorem exists_place_reads_fin {R F : Type u} [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {K Fbar : Type*} [Field K] [Field Fbar] [Algebra K Fbar] (t : Fbar)
    [FiniteDimensional ↥(IntermediateField.adjoin K ({t} : Set Fbar)) Fbar]
    (W : Subring F) (res : W →+* Fbar)
    (hFin : ∀ b : ↥(chartAlgFin R F j), (b : F) ∈ W)
    (hK : ∀ c : K, ∃ a : R, ∃ h : algebraMap R F a ∈ W, res ⟨_, h⟩ = algebraMap K Fbar c)
    (y : ↥(XFin R F j))
    (hunit : ∀ b : ↥(chartAlgFin R F j), b ∉ y.asIdeal → IsUnit (⟨(b : F), hFin b⟩ : W))
    (hng : ∃ b : ↥(chartAlgFin R F j), b ∈ y.asIdeal ∧ res ⟨(b : F), hFin b⟩ ≠ 0) :
    ∃ Q : AlgebraicCurve.Place K Fbar, ∀ f : F, InStalkG j ((ιFin R F j).base y) f →
      ∃ hW : f ∈ W, res ⟨f, hW⟩ ∈ Q.toValuationSubring ∧
        (res ⟨f, hW⟩ ∈ Q.toValuationSubring.nonunits ↔ InMaxG j ((ιFin R F j).base y) f) := by
  classical
  let P : Ideal ↥(chartAlgFin R F j) := y.asIdeal

  let φ₀ : ↥(chartAlgFin R F j) →+* W :=
    { toFun := fun b => ⟨(b : F), hFin b⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  let φ : ↥(chartAlgFin R F j) →+* Fbar := res.comp φ₀
  have hφ : ∀ b, φ b = res ⟨(b : F), hFin b⟩ := fun _ => rfl
  have hφu : ∀ s : P.primeCompl, IsUnit (φ s) := fun s => by
    rw [hφ]; exact (hunit s.1 s.2).map res
  let L := Localization.AtPrime P
  let ψ : Localization.AtPrime P →+* Fbar := IsLocalization.lift (M := P.primeCompl) hφu
  have hψ : ∀ b, ψ (algebraMap _ (Localization.AtPrime P) b) = φ b := fun b => IsLocalization.lift_eq hφu b
  let D : Subring Fbar := ψ.range
  let f' : Localization.AtPrime P →+* D := ψ.rangeRestrict
  have hf' : Function.Surjective f' := RingHom.rangeRestrict_surjective ψ
  haveI : IsLocalRing D := IsLocalRing.of_surjective' f' hf'
  have hrefl : ∀ m : Localization.AtPrime P, IsUnit (f' m) ↔ IsUnit m := fun m =>
    ⟨fun hu => by
      by_contra hm
      exact not_isUnit_map_of_mem_maximalIdeal f' hf' ((IsLocalRing.mem_maximalIdeal _).mpr hm) hu,
     fun hu => hu.map f'⟩

  have hKD : ∀ c : K, algebraMap K Fbar c ∈ D := by
    intro c
    obtain ⟨a, ha, he⟩ := hK c
    refine ⟨algebraMap _ (Localization.AtPrime P) (algebraMap R ↥(chartAlgFin R F j) a), ?_⟩
    rw [hψ, hφ, ← he]
    congr 1

  have hD : ∃ d : D, d ≠ 0 ∧ ¬ IsUnit d := by
    obtain ⟨b, hbP, hb0⟩ := hng
    refine ⟨f' (algebraMap _ (Localization.AtPrime P) b), ?_, ?_⟩
    · intro h0
      apply hb0
      have := congrArg (fun d : D => (d : Fbar)) h0
      simp only [f'] at this
      rw [← hφ, ← hψ]
      exact this
    · rw [hrefl]
      intro hu
      have : algebraMap _ (Localization.AtPrime P) b ∈ maximalIdeal (Localization.AtPrime P) :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P b).mpr hbP
      exact (IsLocalRing.mem_maximalIdeal _).mp this hu
  obtain ⟨Q, hQD, hiff⟩ :=
    AlgebraicCurve.Place.exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing t D hKD hD
  refine ⟨Q, fun f hst => ?_⟩
  obtain ⟨g, h, hh, hfh⟩ := hst.1 y rfl
  have hh0 : (h : F) ≠ 0 := by
    intro h0; apply hh
    have : h = 0 := Subtype.ext h0
    rw [this]; exact P.zero_mem

  obtain ⟨u, hu⟩ := hunit h hh
  let wf : W := φ₀ g * ↑u⁻¹
  have hwu : wf * u = φ₀ g := by simp [wf]
  have hwf : (wf : F) = f := by
    have h1 := congrArg (fun w : W => (w : F)) hwu
    simp only [Subring.coe_mul, hu] at h1

    exact mul_right_cancel₀ hh0 (h1.trans hfh.symm)
  have hW : f ∈ W := hwf ▸ wf.2
  have hfw : (⟨f, hW⟩ : W) = wf := Subtype.ext hwf.symm

  have hφh : IsUnit (φ h) := hφu ⟨h, hh⟩
  have key : res ⟨f, hW⟩ = ψ (IsLocalization.mk' (Localization.AtPrime P) g (⟨h, hh⟩ : P.primeCompl)) := by
    apply mul_right_cancel₀ hφh.ne_zero
    have lhs : res ⟨f, hW⟩ * φ h = φ g := by
      rw [hfw, hφ, ← map_mul]
      have : (⟨(h : F), hFin h⟩ : W) = u := hu.symm
      rw [this, hwu]
      rfl
    have rhs : ψ (IsLocalization.mk' (Localization.AtPrime P) g (⟨h, hh⟩ : P.primeCompl)) * φ h = φ g := by
      rw [← hψ h, ← map_mul]
      have := IsLocalization.mk'_spec (Localization.AtPrime P) g (⟨h, hh⟩ : P.primeCompl)
      rw [this, hψ]
    rw [lhs, rhs]
  refine ⟨hW, ?_, ?_⟩
  · rw [key]; exact hQD _ ⟨_, rfl⟩
  · rw [key]
    have hd := hiff (f' (IsLocalization.mk' (Localization.AtPrime P) g (⟨h, hh⟩ : P.primeCompl)))

    rw [show ((f' (IsLocalization.mk' (Localization.AtPrime P) g (⟨h, hh⟩ : P.primeCompl)) : D) : Fbar) =
        ψ (IsLocalization.mk' (Localization.AtPrime P) g (⟨h, hh⟩ : P.primeCompl)) from rfl] at hd
    rw [hd, hrefl, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal,
      IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime P) P]

    constructor
    · intro hg
      refine ⟨fun y₂ hy₂ => ?_, fun y'' hy'' => ?_⟩
      · obtain rfl : y₂ = y := (ιFin R F j).isOpenEmbedding.injective hy₂
        exact ⟨g, h, hh, hg, hfh⟩
      · obtain ⟨g₁, h₁, hh₁, hgh₁, hiff₁⟩ := cross_fin j y y'' hy'' g
        obtain ⟨g₂, h₂, hh₂, hhh₂, hiff₂⟩ := cross_fin j y y'' hy'' h
        refine ⟨g₁ * h₂, h₁ * g₂, ?_, Ideal.mul_mem_right _ _ (hiff₁.mp hg), ?_⟩
        · intro hmem
          rcases y''.2.mem_or_mem hmem with h1 | h2
          · exact hh₁ h1
          · exact hh (hiff₂.mpr h2)
        · simp only [Subalgebra.coe_mul]
          calc f * ((h₁ : F) * (g₂ : F)) = f * ((h₁ : F) * ((h : F) * (h₂ : F))) := by rw [hhh₂]
            _ = (f * (h : F)) * (h₁ : F) * (h₂ : F) := by ring
            _ = (g : F) * (h₁ : F) * (h₂ : F) := by rw [hfh]
            _ = (g₁ : F) * (h₂ : F) := by rw [hgh₁]
    · intro hmax
      obtain ⟨g', h', hh', hg', hfh'⟩ := hmax.1 y rfl
      have heq : g * h' = g' * h := by
        apply Subtype.ext
        simp only [Subalgebra.coe_mul]
        rw [← hfh, ← hfh']; ring
      have : g * h' ∈ P := heq ▸ Ideal.mul_mem_right _ _ hg'
      exact (y.2.mem_or_mem this).resolve_right hh'

end E140CR

namespace E140CR

open AlgebraicCurve.TwoChartIntegralModel E137 IsLocalRing

theorem exists_place_reads_inf {R F : Type u} [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {K Fbar : Type*} [Field K] [Field Fbar] [Algebra K Fbar] (t : Fbar)
    [FiniteDimensional ↥(IntermediateField.adjoin K ({t} : Set Fbar)) Fbar]
    (W : Subring F) (res : W →+* Fbar)
    (hInf : ∀ b : ↥(chartAlgInf R F j), (b : F) ∈ W)
    (hK : ∀ c : K, ∃ a : R, ∃ h : algebraMap R F a ∈ W, res ⟨_, h⟩ = algebraMap K Fbar c)
    (y : ↥(XInf R F j))
    (hunit : ∀ b : ↥(chartAlgInf R F j), b ∉ y.asIdeal → IsUnit (⟨(b : F), hInf b⟩ : W))
    (hng : ∃ b : ↥(chartAlgInf R F j), b ∈ y.asIdeal ∧ res ⟨(b : F), hInf b⟩ ≠ 0) :
    ∃ Q : AlgebraicCurve.Place K Fbar, ∀ f : F, InStalkG j ((ιInf R F j).base y) f →
      ∃ hW : f ∈ W, res ⟨f, hW⟩ ∈ Q.toValuationSubring ∧
        (res ⟨f, hW⟩ ∈ Q.toValuationSubring.nonunits ↔ InMaxG j ((ιInf R F j).base y) f) := by
  classical
  let P : Ideal ↥(chartAlgInf R F j) := y.asIdeal

  let φ₀ : ↥(chartAlgInf R F j) →+* W :=
    { toFun := fun b => ⟨(b : F), hInf b⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  let φ : ↥(chartAlgInf R F j) →+* Fbar := res.comp φ₀
  have hφ : ∀ b, φ b = res ⟨(b : F), hInf b⟩ := fun _ => rfl
  have hφu : ∀ s : P.primeCompl, IsUnit (φ s) := fun s => by
    rw [hφ]; exact (hunit s.1 s.2).map res
  let L := Localization.AtPrime P
  let ψ : Localization.AtPrime P →+* Fbar := IsLocalization.lift (M := P.primeCompl) hφu
  have hψ : ∀ b, ψ (algebraMap _ (Localization.AtPrime P) b) = φ b := fun b => IsLocalization.lift_eq hφu b
  let D : Subring Fbar := ψ.range
  let f' : Localization.AtPrime P →+* D := ψ.rangeRestrict
  have hf' : Function.Surjective f' := RingHom.rangeRestrict_surjective ψ
  haveI : IsLocalRing D := IsLocalRing.of_surjective' f' hf'
  have hrefl : ∀ m : Localization.AtPrime P, IsUnit (f' m) ↔ IsUnit m := fun m =>
    ⟨fun hu => by
      by_contra hm
      exact not_isUnit_map_of_mem_maximalIdeal f' hf' ((IsLocalRing.mem_maximalIdeal _).mpr hm) hu,
     fun hu => hu.map f'⟩

  have hKD : ∀ c : K, algebraMap K Fbar c ∈ D := by
    intro c
    obtain ⟨a, ha, he⟩ := hK c
    refine ⟨algebraMap _ (Localization.AtPrime P) (algebraMap R ↥(chartAlgInf R F j) a), ?_⟩
    rw [hψ, hφ, ← he]
    congr 1

  have hD : ∃ d : D, d ≠ 0 ∧ ¬ IsUnit d := by
    obtain ⟨b, hbP, hb0⟩ := hng
    refine ⟨f' (algebraMap _ (Localization.AtPrime P) b), ?_, ?_⟩
    · intro h0
      apply hb0
      have := congrArg (fun d : D => (d : Fbar)) h0
      simp only [f'] at this
      rw [← hφ, ← hψ]
      exact this
    · rw [hrefl]
      intro hu
      have : algebraMap _ (Localization.AtPrime P) b ∈ maximalIdeal (Localization.AtPrime P) :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P b).mpr hbP
      exact (IsLocalRing.mem_maximalIdeal _).mp this hu
  obtain ⟨Q, hQD, hiff⟩ :=
    AlgebraicCurve.Place.exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing t D hKD hD
  refine ⟨Q, fun f hst => ?_⟩
  obtain ⟨g, h, hh, hfh⟩ := hst.2 y rfl
  have hh0 : (h : F) ≠ 0 := by
    intro h0; apply hh
    have : h = 0 := Subtype.ext h0
    rw [this]; exact P.zero_mem

  obtain ⟨u, hu⟩ := hunit h hh
  let wf : W := φ₀ g * ↑u⁻¹
  have hwu : wf * u = φ₀ g := by simp [wf]
  have hwf : (wf : F) = f := by
    have h1 := congrArg (fun w : W => (w : F)) hwu
    simp only [Subring.coe_mul, hu] at h1

    exact mul_right_cancel₀ hh0 (h1.trans hfh.symm)
  have hW : f ∈ W := hwf ▸ wf.2
  have hfw : (⟨f, hW⟩ : W) = wf := Subtype.ext hwf.symm

  have hφh : IsUnit (φ h) := hφu ⟨h, hh⟩
  have key : res ⟨f, hW⟩ = ψ (IsLocalization.mk' (Localization.AtPrime P) g (⟨h, hh⟩ : P.primeCompl)) := by
    apply mul_right_cancel₀ hφh.ne_zero
    have lhs : res ⟨f, hW⟩ * φ h = φ g := by
      rw [hfw, hφ, ← map_mul]
      have : (⟨(h : F), hInf h⟩ : W) = u := hu.symm
      rw [this, hwu]
      rfl
    have rhs : ψ (IsLocalization.mk' (Localization.AtPrime P) g (⟨h, hh⟩ : P.primeCompl)) * φ h = φ g := by
      rw [← hψ h, ← map_mul]
      have := IsLocalization.mk'_spec (Localization.AtPrime P) g (⟨h, hh⟩ : P.primeCompl)
      rw [this, hψ]
    rw [lhs, rhs]
  refine ⟨hW, ?_, ?_⟩
  · rw [key]; exact hQD _ ⟨_, rfl⟩
  · rw [key]
    have hd := hiff (f' (IsLocalization.mk' (Localization.AtPrime P) g (⟨h, hh⟩ : P.primeCompl)))

    rw [show ((f' (IsLocalization.mk' (Localization.AtPrime P) g (⟨h, hh⟩ : P.primeCompl)) : D) : Fbar) =
        ψ (IsLocalization.mk' (Localization.AtPrime P) g (⟨h, hh⟩ : P.primeCompl)) from rfl] at hd
    rw [hd, hrefl, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal,
      IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime P) P]

    constructor
    · intro hg
      refine ⟨fun y'' hy'' => ?_, fun y₂ hy₂ => ?_⟩
      swap
      · obtain rfl : y₂ = y := (ιInf R F j).isOpenEmbedding.injective hy₂
        exact ⟨g, h, hh, hg, hfh⟩
      · obtain ⟨g₁, h₁, hh₁, hgh₁, hiff₁⟩ := cross_inf j y y'' hy'' g
        obtain ⟨g₂, h₂, hh₂, hhh₂, hiff₂⟩ := cross_inf j y y'' hy'' h
        refine ⟨g₁ * h₂, h₁ * g₂, ?_, Ideal.mul_mem_right _ _ (hiff₁.mp hg), ?_⟩
        · intro hmem
          rcases y''.2.mem_or_mem hmem with h1 | h2
          · exact hh₁ h1
          · exact hh (hiff₂.mpr h2)
        · simp only [Subalgebra.coe_mul]
          calc f * ((h₁ : F) * (g₂ : F)) = f * ((h₁ : F) * ((h : F) * (h₂ : F))) := by rw [hhh₂]
            _ = (f * (h : F)) * (h₁ : F) * (h₂ : F) := by ring
            _ = (g : F) * (h₁ : F) * (h₂ : F) := by rw [hfh]
            _ = (g₁ : F) * (h₂ : F) := by rw [hgh₁]
    · intro hmax
      obtain ⟨g', h', hh', hg', hfh'⟩ := hmax.2 y rfl
      have heq : g * h' = g' * h := by
        apply Subtype.ext
        simp only [Subalgebra.coe_mul]
        rw [← hfh, ← hfh']; ring
      have : g * h' ∈ P := heq ▸ Ideal.mul_mem_right _ _ hg'
      exact (y.2.mem_or_mem this).resolve_right hh'

end E140CR

namespace E140CR

open AlgebraicCurve.TwoChartIntegralModel E137 IsLocalRing

theorem exists_place_reads {R F : Type u} [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {K Fbar : Type*} [Field K] [Field Fbar] [Algebra K Fbar] (t : Fbar)
    [FiniteDimensional ↥(IntermediateField.adjoin K ({t} : Set Fbar)) Fbar]
    (W : Subring F) (res : W →+* Fbar)
    (hFin : ∀ b : ↥(chartAlgFin R F j), (b : F) ∈ W)
    (hInf : ∀ b : ↥(chartAlgInf R F j), (b : F) ∈ W)
    (hK : ∀ c : K, ∃ a : R, ∃ h : algebraMap R F a ∈ W, res ⟨_, h⟩ = algebraMap K Fbar c)
    (x : ↥(TwoChartIntegralModel R F j))
    (hunitFin : ∀ y : ↥(XFin R F j), (ιFin R F j).base y = x →
      ∀ b : ↥(chartAlgFin R F j), b ∉ y.asIdeal → IsUnit (⟨(b : F), hFin b⟩ : W))
    (hunitInf : ∀ y : ↥(XInf R F j), (ιInf R F j).base y = x →
      ∀ b : ↥(chartAlgInf R F j), b ∉ y.asIdeal → IsUnit (⟨(b : F), hInf b⟩ : W))
    (hngFin : ∀ y : ↥(XFin R F j), (ιFin R F j).base y = x →
      ∃ b : ↥(chartAlgFin R F j), b ∈ y.asIdeal ∧ res ⟨(b : F), hFin b⟩ ≠ 0)
    (hngInf : ∀ y : ↥(XInf R F j), (ιInf R F j).base y = x →
      ∃ b : ↥(chartAlgInf R F j), b ∈ y.asIdeal ∧ res ⟨(b : F), hInf b⟩ ≠ 0) :
    ∃ Q : AlgebraicCurve.Place K Fbar, ∀ f : F, InStalkG j x f →
      ∃ hW : f ∈ W, res ⟨f, hW⟩ ∈ Q.toValuationSubring ∧
        (res ⟨f, hW⟩ ∈ Q.toValuationSubring.nonunits ↔ InMaxG j x f) := by
  rcases mem_range_ιFin_or_mem_range_ιInf R F j x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · exact exists_place_reads_fin j t W res hFin hK y (hunitFin y rfl) (hngFin y rfl)
  · exact exists_place_reads_inf j t W res hInf hK y (hunitInf y rfl) (hngInf y rfl)

theorem isUnit_restrict {F E : Type*} [Field F] [Field E] [Algebra F E] (O : ValuationSubring E)
    (f : F) (hf : algebraMap F E f ∈ O) (hu : algebraMap F E f ∉ O.nonunits) :
    IsUnit (⟨f, hf⟩ : O.toSubring.comap (algebraMap F E)) := by
  have hv : O.valuation (algebraMap F E f) = 1 := by
    have hle := (O.valuation_le_one_iff _).mpr hf
    rw [ValuationSubring.mem_nonunits_iff] at hu
    exact le_antisymm hle (not_lt.mp hu)
  have hf0 : f ≠ 0 := by
    intro h0; rw [h0, map_zero, map_zero] at hv; exact zero_ne_one hv
  have hinv : algebraMap F E f⁻¹ ∈ O := by
    rw [map_inv₀]
    have hu' : IsUnit (⟨algebraMap F E f, hf⟩ : O) := (O.valuation_eq_one_iff _).mpr hv
    obtain ⟨u, hu'⟩ := hu'
    have : ((u⁻¹ : Oˣ) : O).1 = (algebraMap F E f)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have := congrArg (fun o : O => (o : E)) u.inv_mul
      simpa [hu'] using this
    exact this ▸ ((u⁻¹ : Oˣ) : O).2
  refine IsUnit.of_mul_eq_one ⟨f⁻¹, hinv⟩ (Subtype.ext ?_)
  change f * f⁻¹ = 1
  exact mul_inv_cancel₀ hf0

end E140CR

namespace E140CR

open AlgebraicCurve.TwoChartIntegralModel E137 IsLocalRing

theorem exists_place_reads' {R F : Type u} [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {K Fbar E : Type*} [Field K] [Field Fbar] [Algebra K Fbar] [Field E] (t : Fbar)
    [FiniteDimensional ↥(IntermediateField.adjoin K ({t} : Set Fbar)) Fbar]
    (ι : F →+* E) (O : ValuationSubring E) (r : O →+* Fbar)
    (hFin : ∀ b : ↥(chartAlgFin R F j), ι (b : F) ∈ O)
    (hInf : ∀ b : ↥(chartAlgInf R F j), ι (b : F) ∈ O)
    (hK : ∀ c : K, ∃ a : R, ∃ h : ι (algebraMap R F a) ∈ O, r ⟨_, h⟩ = algebraMap K Fbar c)
    (x : ↥(TwoChartIntegralModel R F j))
    (hbrFin : ∀ y : ↥(XFin R F j), (ιFin R F j).base y = x →
      ∀ b : ↥(chartAlgFin R F j), ι (b : F) ∈ O.nonunits → b ∈ y.asIdeal)
    (hbrInf : ∀ y : ↥(XInf R F j), (ιInf R F j).base y = x →
      ∀ b : ↥(chartAlgInf R F j), ι (b : F) ∈ O.nonunits → b ∈ y.asIdeal)
    (hngFin : ∀ y : ↥(XFin R F j), (ιFin R F j).base y = x →
      ∃ b : ↥(chartAlgFin R F j), ∃ h : ι (b : F) ∈ O, b ∈ y.asIdeal ∧ r ⟨ι (b : F), h⟩ ≠ 0)
    (hngInf : ∀ y : ↥(XInf R F j), (ιInf R F j).base y = x →
      ∃ b : ↥(chartAlgInf R F j), ∃ h : ι (b : F) ∈ O, b ∈ y.asIdeal ∧ r ⟨ι (b : F), h⟩ ≠ 0) :
    ∃ Q : AlgebraicCurve.Place K Fbar, ∀ f : F, InStalkG j x f →
      ∃ hO : ι f ∈ O, r ⟨ι f, hO⟩ ∈ Q.toValuationSubring ∧
        (r ⟨ι f, hO⟩ ∈ Q.toValuationSubring.nonunits ↔ InMaxG j x f) := by
  let W : Subring F := O.toSubring.comap ι
  let res : W →+* Fbar := r.comp (ι.restrict W O.toSubring (fun x hx => hx))
  have hres : ∀ (f : F) (hf : f ∈ W), res ⟨f, hf⟩ = r ⟨ι f, hf⟩ := fun _ _ => rfl

  have hunitW : ∀ (f : F) (hf : ι f ∈ O), ι f ∉ O.nonunits → IsUnit (⟨f, hf⟩ : W) := by
    intro f hf hnu
    have hv : O.valuation (ι f) = 1 := by
      have hle := (O.valuation_le_one_iff _).mpr hf
      rw [ValuationSubring.mem_nonunits_iff] at hnu
      exact le_antisymm hle (not_lt.mp hnu)
    have hf0 : f ≠ 0 := by
      intro h0; rw [h0, map_zero, map_zero] at hv; exact zero_ne_one hv
    have hinv : ι f⁻¹ ∈ O := by
      rw [map_inv₀]
      have hu' : IsUnit (⟨ι f, hf⟩ : O) := (O.valuation_eq_one_iff _).mpr hv
      obtain ⟨u, hu'⟩ := hu'
      have : ((u⁻¹ : Oˣ) : O).1 = (ι f)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        have := congrArg (fun o : O => (o : E)) u.inv_mul
        simpa [hu'] using this
      exact this ▸ ((u⁻¹ : Oˣ) : O).2
    refine IsUnit.of_mul_eq_one ⟨f⁻¹, hinv⟩ (Subtype.ext ?_)
    change f * f⁻¹ = 1
    exact mul_inv_cancel₀ hf0
  obtain ⟨Q, hQ⟩ := exists_place_reads j t W res (fun b => hFin b) (fun b => hInf b)
    (fun c => by obtain ⟨a, h, e⟩ := hK c; exact ⟨a, h, (hres _ _).trans e⟩) x
    (fun y hy b hb => hunitW (b : F) (hFin b) (fun hnu => hb (hbrFin y hy b hnu)))
    (fun y hy b hb => hunitW (b : F) (hInf b) (fun hnu => hb (hbrInf y hy b hnu)))
    (fun y hy => by obtain ⟨b, h, hbP, hne⟩ := hngFin y hy; exact ⟨b, hbP, fun h0 => hne ((hres _ _).symm.trans h0)⟩)
    (fun y hy => by obtain ⟨b, h, hbP, hne⟩ := hngInf y hy; exact ⟨b, hbP, fun h0 => hne ((hres _ _).symm.trans h0)⟩)
  refine ⟨Q, fun f hst => ?_⟩
  obtain ⟨hW, h1, h2⟩ := hQ f hst
  exact ⟨hW, (hres f hW) ▸ h1, (hres f hW) ▸ h2⟩

end E140CR

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

    ∀ (NIg : Finset (Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))),
      (∃ j : modularFunctionFieldC (ResidueField A) M' →+* xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'),
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers, R.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
        ∀ Q, Q ∈ NIg ↔ ∃ s : ↥W, ∀ g : modularFunctionFieldC (ResidueField A) M',
          g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
            j g ∈ Q.toValuationSubring) →

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

    let Reads : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Prop := fun x Q =>
      ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), InStalk x f →
        ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring ∧
          (R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring.nonunits ↔ InMax x f)

    let OffBranch : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun x =>
      ∀ ℓ : CuspidalType.ProjLine q, ℓ ≠ lineInfty q →
        (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
          ∃ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ (OIg ℓ).nonunits ∧ b ∉ y.asIdeal) ∧
        (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
          ∃ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ (OIg ℓ).nonunits ∧ b ∉ y.asIdeal)

    (∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), GoodPt x → ∃ Q, Reads x Q) := by
  intro F₀ hF₀sup hF₀stab hF₀lin hF₀q instAlg hA₁alg j₁ hj₁ instFact NIg hN
  intro InStalk InMax Centred GoodPt Reads OffBranch
  intro x hx
  obtain ⟨hIfin, hIinf, hIK⟩ := ModularCurve.FullLevel.coe_chartAlg_mem_integers_and_exists_residue_algebraMap_eq_twoChartIntegralModel q hq M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr R hR hR₀O π hπ hπP k₀ π₀ hπ₀ hdvr hunif hhens hres hκ ℓ hℓ hℓ3 hℓq hℓM' ζ₀ hζ₀ ϖt hϖtA hϖt K₁ hK₁ A₁ hA₁ F₀ hF₀sup hF₀stab hF₀lin hF₀q hA₁alg j₁ hj₁ NIg hN
  have hII := ModularCurve.FullLevel.exists_mem_asIdeal_and_residue_ne_zero_of_goodPt_twoChartIntegralModel q hq M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr R hR hR₀O π hπ hπP k₀ π₀ hπ₀ hdvr hunif hhens hres hκ ℓ hℓ hℓ3 hℓq hℓM' ζ₀ hζ₀ ϖt hϖtA hϖt K₁ hK₁ A₁ hA₁ F₀ hF₀sup hF₀stab hF₀lin hF₀q hA₁alg j₁ hj₁ NIg hN x hx
  obtain ⟨t, hfd⟩ := ModularCurve.FullLevel.exists_finiteDimensional_adjoin_xHFunctionFieldC_levelH q hq M' hqM' A hA
  haveI := hfd
  obtain ⟨hxcl, hxclosed, hbrFin, hbrInf, hnss⟩ := hx
  obtain ⟨Q, hQ⟩ := E140CR.exists_place_reads' j₁ t (IntermediateField.val (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).toRingHom R.integers R.residue
    hIfin hIinf hIK x hbrFin hbrInf hII.1 hII.2
  exact ⟨Q, fun f hst => hQ f hst⟩

end S_ModularCurve_FullLevel_exists_reads_of_goodPt_twoChartIntegralModel
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_reads_of_goodPt_twoChartIntegralModel (solution)
