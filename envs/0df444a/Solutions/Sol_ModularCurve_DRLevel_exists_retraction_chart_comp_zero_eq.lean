-- Prove2me | solution 1 for ModularCurve.DRLevel.exists_retraction_chart_comp_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/3e3679cd-7757-5776-b7f5-1807e4dcfe00

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRLevel_exists_retraction_chart_comp_zero_eq

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
p2m_open "ModularCurve P2MW.S_ModularCurve_DRLevel_exists_retraction_chart_comp_zero_eq.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel P2MW.S_ModularCurve_DRLevel_exists_retraction_chart_comp_zero_eq.ModularCurve.DRLevel"
open scoped TensorProduct

namespace ModularCurve
p2m_export "ModularCurve" "DRLevel.R DRLevel.toBase DRLevel.toBase0 DRLevel.fibre DRLevel.fibre0 DRLevel.fibreMap0 IgusaScheme.chartAlgFin IgusaScheme IgusaScheme.ιFin modularFunctionFieldFull"
namespace DRLevel
p2m_export "ModularCurve.DRLevel" "R X toBase toBase0 fibre fibre0 fibreMap0"
namespace SectionUniq
p2m_open "ModularCurve.DRLevel ModularCurve"

theorem range_subset_of_isOpen {A : Type} [CommRing A] [IsLocalRing A] {Y : Scheme.{0}}
    (f : Spec (CommRingCat.of A) ⟶ Y) {U : Set Y} (hU : IsOpen U)
    (h : f (IsLocalRing.closedPoint A) ∈ U) : Set.range f ⊆ U := by
  rintro _ ⟨x, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint x).map f.continuous).mem_open hU h

section Chart

variable (N : ℕ) [NeZero N] (q : ℕ) [Fact q.Prime] (κ : Type) [CommRing κ] [Algebra (R q) κ]

theorem isPullback_chart
    (c : Spec (CommRingCat.of (κ ⊗[R q] ↥(chartAlgFin N q))) ⟶
      pullback (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R q) (A := κ) (B := ↥(chartAlgFin N q))).toRingHom) ≫ ιFin N q)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R q) (A := κ) (B := ↥(chartAlgFin N q))))) :
    IsPullback c (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R q) (A := κ) (B := ↥(chartAlgFin N q))).toRingHom)) (pullback.fst _ _) (ιFin N q) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd _ _)
    (v₁₃ := Spec.map (CommRingCat.ofHom (algebraMap (R q) κ))) (h₂₂ := igusaTo N q) ?_ hcfst
    (IsPullback.of_hasPullback _ _).flip
  rw [hcsnd, ιFin_igusaTo]
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct (R q) κ ↥(chartAlgFin N q))

theorem isOpenImmersion_chart
    (c : Spec (CommRingCat.of (κ ⊗[R q] ↥(chartAlgFin N q))) ⟶
      pullback (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R q) (A := κ) (B := ↥(chartAlgFin N q))).toRingHom) ≫ ιFin N q)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R q) (A := κ) (B := ↥(chartAlgFin N q))))) :
    IsOpenImmersion c := by
  rw [← (isPullback_chart N q κ c hcfst hcsnd).isoPullback_hom_fst]
  infer_instance

theorem mem_range_chart
    (c : Spec (CommRingCat.of (κ ⊗[R q] ↥(chartAlgFin N q))) ⟶
      pullback (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R q) (A := κ) (B := ↥(chartAlgFin N q))).toRingHom) ≫ ιFin N q)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R q) (A := κ) (B := ↥(chartAlgFin N q)))))
    (x : ↥(pullback (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ)))))
    (hx : (pullback.fst (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ)))) x ∈ Set.range (ιFin N q)) : x ∈ Set.range c := by
  have H := isPullback_chart N q κ c hcfst hcsnd
  have hx' : x ∈ Set.range (pullback.fst (pullback.fst (igusaTo N q)
      (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ)))) (ιFin N q)) := by
    rw [Scheme.Pullback.range_fst]; exact hx
  obtain ⟨t, rfl⟩ := hx'
  exact ⟨H.isoPullback.inv t, by rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_fst]⟩

end Chart

section Key

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime]

theorem iota0_jChartFin
    (iota0 : ↥(chartAlgFin N₀ q) →ₐ[R q] ↥(chartAlgFin (N₀ * q) q))
    (hiota : ∀ b, (((iota0 b : ↥(chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) :
        LaurentSeries ℚ) = ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ)) :
    iota0 (jChartFin N₀ q) = jChartFin (N₀ * q) q := by
  apply Subtype.ext; apply Subtype.ext
  rw [hiota, coe_jChartFin, coe_jFull, coe_jChartFin, coe_jFull]

theorem specMap_val_ιInf (N : ℕ) [NeZero N] :
    Spec.map (CommRingCat.ofHom (chartAlgInf N q).val.toRingHom) ≫ ιInf N q =
      Spec.map (CommRingCat.ofHom (chartAlgFin N q).val.toRingHom) ≫ ιFin N q := by
  have h1 : (chartAlgInf N q).val.toRingHom = (chartAlgMid N q).val.toRingHom.comp (inclInf N q).toRingHom :=
    RingHom.ext fun _ => rfl
  have h2 : (chartAlgFin N q).val.toRingHom = (chartAlgMid N q).val.toRingHom.comp (inclFin N q).toRingHom :=
    RingHom.ext fun _ => rfl
  have hg : Spec.map (CommRingCat.ofHom (inclFin N q).toRingHom) ≫ ιFin N q =
      Spec.map (CommRingCat.ofHom (inclInf N q).toRingHom) ≫ ιInf N q := glue_condition N q
  rw [h1, h2, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, Category.assoc,
    Category.assoc, hg]

theorem mem_range_ιFin_of_pi
    (π : SchemeHomOver (toBase N₀ q) (toBase0 N₀ q))
    (iota0 : ↥(chartAlgFin N₀ q) →ₐ[R q] ↥(chartAlgFin (N₀ * q) q))
    (hiota : ∀ b, (((iota0 b : ↥(chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) :
        LaurentSeries ℚ) = ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ))
    (hpichart : ιFin (N₀ * q) q ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ ιFin N₀ q)
    (z : ↥(X N₀ q)) (hz : π.1 z ∈ Set.range (ιFin N₀ q)) : z ∈ Set.range (ιFin (N₀ * q) q) := by
  rcases mem_range_ιFin_or_mem_range_ιInf (N₀ * q) q z with h | ⟨w, rfl⟩
  · exact h

  let A : Type := ↥(chartAlgInf (N₀ * q) q)
  let F : Type := ↥(modularFunctionFieldFull (N₀ * q))
  let 𝔭 : Ideal A := (w : PrimeSpectrum A).asIdeal
  let L : Type := Localization.AtPrime 𝔭
  let g : Spec (CommRingCat.of L) ⟶ XInf (N₀ * q) q := Spec.map (CommRingCat.ofHom (algebraMap A L))
  have hg : g (IsLocalRing.closedPoint L) = w := by
    apply PrimeSpectrum.ext
    exact Localization.AtPrime.under_maximalIdeal (I := 𝔭)

  have hrange : Set.range (g ≫ ιInf (N₀ * q) q ≫ π.1) ⊆ Set.range (ιFin N₀ q) := by
    refine range_subset_of_isOpen _ (ιFin N₀ q).isOpenEmbedding.isOpen_range ?_
    simpa only [Scheme.Hom.comp_apply, hg] using hz
  let φ : Spec (CommRingCat.of L) ⟶ XFin N₀ q := IsOpenImmersion.lift (ιFin N₀ q) (g ≫ ιInf (N₀ * q) q ≫ π.1) hrange
  have hφ : φ ≫ ιFin N₀ q = g ≫ ιInf (N₀ * q) q ≫ π.1 := IsOpenImmersion.lift_fac _ _ _
  let ψ : ↥(chartAlgFin N₀ q) →+* L := (Spec.preimage φ).hom
  have hψ : Spec.map (CommRingCat.ofHom ψ) = φ := by
    rw [CommRingCat.ofHom_hom]; exact Spec.map_preimage φ

  have hunit : ∀ s : 𝔭.primeCompl, IsUnit ((chartAlgInf (N₀ * q) q).val.toRingHom s) := by
    intro s
    refine isUnit_iff_ne_zero.mpr fun h0 => s.2 ?_
    have : (s : A) = 0 := by
      apply Subtype.ext
      exact h0
    rw [this]; exact zero_mem _
  let v : L →+* F := IsLocalization.lift (M := 𝔭.primeCompl) hunit
  have hv_alg : ∀ a : A, v (algebraMap A L a) = (chartAlgInf (N₀ * q) q).val.toRingHom a :=
    fun a => IsLocalization.lift_eq hunit a
  have hvA : v.comp (algebraMap A L) = (chartAlgInf (N₀ * q) q).val.toRingHom := RingHom.ext hv_alg
  have hv_inj : Function.Injective v := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists 𝔭.primeCompl L).mp h
      have hc0 : (c : A) ≠ 0 := fun h0 => c.2 (by rw [h0]; exact zero_mem _)
      rw [mul_left_cancel₀ hc0 hc]
    · intro h
      have : x = y := Subtype.ext h
      rw [this]

  have hkey : v.comp ψ = (chartAlgFin (N₀ * q) q).val.toRingHom.comp iota0.toRingHom := by
    have h1 : Spec.map (CommRingCat.ofHom (v.comp ψ)) ≫ ιFin N₀ q =
        Spec.map (CommRingCat.ofHom ((chartAlgFin (N₀ * q) q).val.toRingHom.comp iota0.toRingHom)) ≫ ιFin N₀ q := by
      calc Spec.map (CommRingCat.ofHom (v.comp ψ)) ≫ ιFin N₀ q
          = Spec.map (CommRingCat.ofHom v) ≫ φ ≫ ιFin N₀ q := by
            rw [← hψ, ← Category.assoc, ← Spec.map_comp]; rfl
        _ = (Spec.map (CommRingCat.ofHom v) ≫ g) ≫ ιInf (N₀ * q) q ≫ π.1 := by rw [hφ, Category.assoc]
        _ = Spec.map (CommRingCat.ofHom (chartAlgInf (N₀ * q) q).val.toRingHom) ≫ ιInf (N₀ * q) q ≫ π.1 := by
            rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hvA]
        _ = Spec.map (CommRingCat.ofHom (chartAlgFin (N₀ * q) q).val.toRingHom) ≫ ιFin (N₀ * q) q ≫ π.1 := by
            rw [← Category.assoc, specMap_val_ιInf, Category.assoc]
        _ = Spec.map (CommRingCat.ofHom (chartAlgFin (N₀ * q) q).val.toRingHom) ≫
              Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ ιFin N₀ q := by rw [hpichart]
        _ = Spec.map (CommRingCat.ofHom ((chartAlgFin (N₀ * q) q).val.toRingHom.comp iota0.toRingHom)) ≫
              ιFin N₀ q := by
            rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have h2 := (cancel_mono (ιFin N₀ q)).mp h1
    rw [Spec.map_inj] at h2
    exact congrArg CommRingCat.Hom.hom h2

  have hvj : v (ψ (jChartFin N₀ q)) = (jFull (N₀ * q) : F) := by
    have h := RingHom.congr_fun hkey (jChartFin N₀ q)
    change v (ψ (jChartFin N₀ q)) = ((iota0 (jChartFin N₀ q) : ↥(chartAlgFin (N₀ * q) q)) : F) at h
    rw [h, iota0_jChartFin iota0 hiota, coe_jChartFin]
  have hprod : v (ψ (jChartFin N₀ q) * algebraMap A L (jInvChartInf (N₀ * q) q)) = v 1 := by
    rw [map_mul, map_one, hv_alg, hvj]
    change (jFull (N₀ * q) : F) * ((jInvChartInf (N₀ * q) q : A) : F) = 1
    rw [coe_jInvChartInf]
    exact mul_inv_cancel₀ (jFull_ne_zero _)
  have hU : IsUnit (algebraMap A L (jInvChartInf (N₀ * q) q)) := IsUnit.of_mul_eq_one_right _ (hv_inj hprod)
  have hnot : jInvChartInf (N₀ * q) q ∉ 𝔭 := (IsLocalization.AtPrime.isUnit_to_map_iff L 𝔭 _).mp hU

  have hw : w ∈ Set.range (fInf (N₀ * q) q) := by
    letI := (inclInf (N₀ * q) q).toRingHom.toAlgebra
    haveI := isLocalization_away_inclInf (N₀ * q) q
    have hr := PrimeSpectrum.localization_away_comap_range (R := A) ↥(chartAlgMid (N₀ * q) q)
      (jInvChartInf (N₀ * q) q)
    have hmem : (w : PrimeSpectrum A) ∈ (PrimeSpectrum.basicOpen (jInvChartInf (N₀ * q) q) : Set (PrimeSpectrum A)) :=
      hnot
    rw [← hr] at hmem
    obtain ⟨w', hw'⟩ := hmem
    exact ⟨w', hw'⟩
  obtain ⟨w', rfl⟩ := hw
  refine ⟨fFin (N₀ * q) q w', ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, glue_condition]

end Key

end ModularCurve.DRLevel.SectionUniq

open ModularCurve.DRLevel.SectionUniq in
theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)

    (π : SchemeHomOver (DRLevel.toBase N₀ q) (DRLevel.toBase0 N₀ q))
    (iota0 : ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hiota : ∀ b, (((iota0 b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ))
    (hpichart : IgusaScheme.ιFin (N₀ * q) q ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ IgusaScheme.ιFin N₀ q)

    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] [Algebra (DRLevel.R q) κ]

    (c₀ : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))) ⟶
      DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ))
    (hc₀fst : c₀ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q))).toRingHom) ≫ IgusaScheme.ιFin N₀ q)
    (hc₀snd : c₀ ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q)))))
    (c : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) ⟶
      DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q)))))

    (comp : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ) ⟶ DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ)))
    (hcomp_over : ∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _)
    (hcomp_ci : ∀ i, IsClosedImmersion (comp i))
    (hcomp_pi : comp 0 ≫ DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ) = 𝟙 _) :
    ∃ σ₀ : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[κ]
        κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q),
      (∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z) = z) ∧
      c₀ ≫ comp 0 = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c  := by

  haveI hcO : IsOpenImmersion c := isOpenImmersion_chart (N₀ * q) q κ c hcfst hcsnd
  haveI hc₀O : IsOpenImmersion c₀ := isOpenImmersion_chart N₀ q κ c₀ hc₀fst hc₀snd

  have hfm : fibreMap0 π (algebraMap (R q) κ) ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π.1 := by
    rw [fibreMap0, pullback.lift_fst]
  have hS : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0).toRingHom) ≫ c₀ =
      c ≫ fibreMap0 π (algebraMap (R q) κ) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hc₀fst, Category.assoc, hfm, reassoc_of% hcfst, hpichart, ← Spec.map_comp_assoc,
        ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 3
    · rw [Category.assoc, hc₀snd, Category.assoc, fibreMap0, pullback.lift_snd, Category.comp_id, hcsnd,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      all_goals exact RingHom.ext fun a => by simp

  have hrange : Set.range (c₀ ≫ comp 0) ⊆ Set.range c := by
    rintro _ ⟨y, rfl⟩
    apply mem_range_chart (N₀ * q) q κ c hcfst hcsnd
    apply mem_range_ιFin_of_pi π iota0 hiota hpichart
    have hm : (c₀ ≫ comp 0) ≫ pullback.fst _ _ ≫ π.1 =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := R q) (A := κ) (B := ↥(chartAlgFin N₀ q))).toRingHom) ≫ ιFin N₀ q := by
      rw [← hfm, Category.assoc, reassoc_of% hcomp_pi]
      rw [hc₀fst]
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hm, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

  let ℓ := IsOpenImmersion.lift c (c₀ ≫ comp 0) hrange
  have hℓ : ℓ ≫ c = c₀ ≫ comp 0 := IsOpenImmersion.lift_fac _ _ _
  let τ : κ ⊗[R q] ↥(chartAlgFin (N₀ * q) q) →+* κ ⊗[R q] ↥(chartAlgFin N₀ q) := (Spec.preimage ℓ).hom
  have hτ : Spec.map (CommRingCat.ofHom τ) = ℓ := by
    rw [CommRingCat.ofHom_hom]; exact Spec.map_preimage ℓ

  have hτleft : τ.comp Algebra.TensorProduct.includeLeftRingHom = Algebra.TensorProduct.includeLeftRingHom := by
    have h1 : Spec.map (CommRingCat.ofHom (τ.comp Algebra.TensorProduct.includeLeftRingHom)) =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := R q) (A := κ) (B := ↥(chartAlgFin N₀ q)))) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, hτ, ← hcsnd, reassoc_of% hℓ, hcomp_over 0, hc₀snd]
    rw [Spec.map_inj] at h1
    exact congrArg CommRingCat.Hom.hom h1
  let σ₀ : κ ⊗[R q] ↥(chartAlgFin (N₀ * q) q) →ₐ[κ] κ ⊗[R q] ↥(chartAlgFin N₀ q) :=
    { τ with
      commutes' := fun r => by
        have := RingHom.congr_fun hτleft r
        simpa [Algebra.TensorProduct.algebraMap_apply] using this }
  have hσ₀ : σ₀.toRingHom = τ := rfl
  refine ⟨σ₀, ?_, ?_⟩
  ·
    have h3 : (Spec.map (CommRingCat.ofHom τ) ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0).toRingHom)) ≫ c₀ = 𝟙 _ ≫ c₀ := by
      rw [Category.assoc, hS, hτ, reassoc_of% hℓ, hcomp_pi, Category.comp_id, Category.id_comp]
    have h4 := (cancel_mono c₀).mp h3
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id, ← CommRingCat.ofHom_id, Spec.map_inj] at h4
    have h5 := congrArg CommRingCat.Hom.hom h4
    intro z
    exact RingHom.congr_fun h5 z
  · change c₀ ≫ comp 0 = Spec.map (CommRingCat.ofHom τ) ≫ c
    rw [hτ, hℓ]

end S_ModularCurve_DRLevel_exists_retraction_chart_comp_zero_eq
end P2MW
export P2MW.S_ModularCurve_DRLevel_exists_retraction_chart_comp_zero_eq (solution)
