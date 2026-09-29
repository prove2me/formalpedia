-- Prove2me | solution 1 for ModularCurve.IgusaScheme.coeffEmb_sub_mem_nonunits_pointEquivPlace_ofGenerator_of_chartPin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/c1cbe752-5de7-5692-af37-63f0c4c2ee03

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_coeffEmb_sub_mem_nonunits_pointEquivPlace_ofGenerator_of_chartPin

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_IgusaScheme_coeffEmb_sub_mem_nonunits_pointEquivPlace_ofGenerator_of_chartPin.ModularCurve AlgebraicCurve IsLocalRing ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_coeffEmb_sub_mem_nonunits_pointEquivPlace_ofGenerator_of_chartPin.ModularCurve.IgusaScheme IsDedekindDomain"

open scoped TensorProduct

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme IgusaScheme.ιFin IgusaScheme.ιInf modularFunctionFieldFull CharPModel.jBar coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange modularFunctionFieldBar"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull coe_jFull jFull_ne_zero chartAlg chartAlg_mono coe_chartIncl exists_pow_mul_mem_chartAlg chartAlgFin chartAlgInf jChartFin jInvChartInf coe_jChartFin coe_jInvChartInf inclFin inclInf isLocalization_away_inclFin isLocalization_away_inclInf XFin XInf fFin fInf ιFin ιInf glue_condition igusaTo"
namespace CentreGen
p2m_open "ModularCurve.IgusaScheme ModularCurve"

universe u

theorem pushout_inl_eq_inr_iff {U X Y : Scheme.{u}} (f : U ⟶ X) (g : U ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion g] (x : X) (y : Y) :
    (pushout.inl f g).base x = (pushout.inr f g).base y ↔
      ∃ w : U, f.base w = x ∧ g.base w = y := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span f g)
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x) (xj := y)).mp h
    rcases k with (_ | _ | _)
    · have hfi : fi = WalkingSpan.Hom.fst := Subsingleton.elim _ _
      have hfj : fj = WalkingSpan.Hom.snd := Subsingleton.elim _ _
      subst hfi hfj
      exact ⟨w, by simp at h₁; exact h₁, by simp at h₂; exact h₂⟩
    · change WidePushoutShape.Hom (some WalkingPair.left) (some WalkingPair.right) at fj
      rcases fj with ⟨⟩
    · change WidePushoutShape.Hom (some WalkingPair.right) (some WalkingPair.left) at fi
      rcases fi with ⟨⟩
  · rintro ⟨w, rfl, rfl⟩
    change (f ≫ pushout.inl f g).base w = (g ≫ pushout.inr f g).base w
    rw [pushout.condition]

theorem exists_eq_spec_map_comp_of_mem_range {K : Type u} [Field K] {A : CommRingCat.{u}}
    {Z : Scheme.{u}} (ι : Spec A ⟶ Z) [IsOpenImmersion ι]
    (x : Spec (CommRingCat.of K) ⟶ Z)
    (hx : x.base (closedPoint K) ∈ Set.range ι.base) :
    ∃ χ : A ⟶ CommRingCat.of K, x = Spec.map χ ≫ ι := by
  have hrange : Set.range x.base ⊆ Set.range ι.base := by
    rintro _ ⟨q, rfl⟩
    rw [Subsingleton.elim q (closedPoint K)]
    exact hx
  refine ⟨Spec.preimage (IsOpenImmersion.lift ι x hrange), ?_⟩
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem spec_map_base_closedPoint_asIdeal {K : Type u} [Field K] {A : CommRingCat.{u}}
    (χ : A ⟶ CommRingCat.of K) :
    ((Spec.map χ).base (closedPoint K)).asIdeal = RingHom.ker χ.hom := by
  rw [Spec.map_base]
  show (PrimeSpectrum.comap χ.hom (closedPoint K)).asIdeal = _
  rw [PrimeSpectrum.comap_asIdeal, RingHom.ker_eq_comap_bot]
  congr 1
  exact (closedPoint K).asIdeal.eq_bot_of_prime

theorem ringHom_eq_of_spec_map_eq {A B : Type u} [CommRing A] [CommRing B] {φ ψ : A →+* B}
    (h : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ψ)) : φ = ψ := by
  have := Spec.map_injective h
  rw [← CommRingCat.hom_ofHom φ, this, CommRingCat.hom_ofHom]

theorem range_spec_map_of_away {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (r : R)
    (h : letI := φ.toAlgebra; IsLocalization.Away r S) :
    Set.range (Spec.map (CommRingCat.ofHom φ)).base =
      ((PrimeSpectrum.basicOpen r : TopologicalSpace.Opens (PrimeSpectrum R)) :
        Set (PrimeSpectrum R)) := by
  letI := φ.toAlgebra
  haveI := h
  rw [← PrimeSpectrum.localization_away_comap_range S r, Spec.map_base]
  rfl

theorem apply_algebraMap_of_spec_map_comp {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    (χ : A →+* K)
    (h : Spec.map (CommRingCat.ofHom χ) ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) =
      𝟙 (Spec (CommRingCat.of K))) (c : K) :
    χ (algebraMap K A c) = c := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, show 𝟙 (Spec (CommRingCat.of K)) =
    Spec.map (CommRingCat.ofHom (RingHom.id K)) by rw [CommRingCat.ofHom_id, Spec.map_id]] at h
  exact RingHom.congr_fun (ringHom_eq_of_spec_map_eq h) c

theorem mem_and_sub_mem_nonunits_ofHeightOneSpectrum {K L : Type*} [Field K] [Field L]
    [Algebra K L] {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R L] [IsFractionRing R L]
    [Algebra K R] [IsScalarTower K R L]
    (𝔭 : HeightOneSpectrum R) (χ : R →+* K) (hχ : RingHom.ker χ = 𝔭.asIdeal)
    (hχK : ∀ c : K, χ (algebraMap K R c) = c) (r : R) :
    algebraMap R L r ∈ (Place.ofHeightOneSpectrum (K := K) (F := L) 𝔭).toValuationSubring ∧
      algebraMap R L r - algebraMap K L (χ r) ∈
        (Place.ofHeightOneSpectrum (K := K) (F := L) 𝔭).toValuationSubring.nonunits := by
  rw [Place.ofHeightOneSpectrum_toValuationSubring]
  refine ⟨?_, ?_⟩
  · rw [Valuation.mem_valuationSubring_iff]
    exact 𝔭.valuation_le_one r
  · rw [ValuationSubring.mem_nonunits_iff,
      ← (Valuation.isEquiv_valuation_valuationSubring (𝔭.valuation L)).lt_one_iff_lt_one]
    have hmem : r - algebraMap K R (χ r) ∈ 𝔭.asIdeal := by
      rw [← hχ, RingHom.mem_ker, map_sub, hχK, sub_self]
    have h : 𝔭.valuation L (algebraMap R L (r - algebraMap K R (χ r))) < 1 :=
      (𝔭.valuation_lt_one_iff_mem (K := L) (r - algebraMap K R (χ r))).mpr hmem
    rwa [map_sub, ← IsScalarTower.algebraMap_apply] at h

section Igusa

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

theorem range_fFin_base : Set.range (fFin N ℓ).base =
    ((PrimeSpectrum.basicOpen (jChartFin N ℓ) :
        TopologicalSpace.Opens (PrimeSpectrum (chartAlgFin N ℓ))) :
      Set (PrimeSpectrum (chartAlgFin N ℓ))) :=
  range_spec_map_of_away _ _ (isLocalization_away_inclFin N ℓ)

theorem range_fInf_base : Set.range (fInf N ℓ).base =
    ((PrimeSpectrum.basicOpen (jInvChartInf N ℓ) :
        TopologicalSpace.Opens (PrimeSpectrum (chartAlgInf N ℓ))) :
      Set (PrimeSpectrum (chartAlgInf N ℓ))) :=
  range_spec_map_of_away _ _ (isLocalization_away_inclInf N ℓ)

theorem ιInf_base_mem_range_ιFin_iff (xi : XInf N ℓ) :
    (ιInf N ℓ).base xi ∈ Set.range (ιFin N ℓ).base ↔ jInvChartInf N ℓ ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_fInf_base, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨w, -, hw⟩ := (pushout_inl_eq_inr_iff (fFin N ℓ) (fInf N ℓ) x₀ xi).mp h
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(fFin N ℓ).base w, (pushout_inl_eq_inr_iff (fFin N ℓ) (fInf N ℓ) _ _).mpr ⟨w, rfl, rfl⟩⟩

theorem ιFin_base_mem_range_ιInf_iff (x₀ : XFin N ℓ) :
    (ιFin N ℓ).base x₀ ∈ Set.range (ιInf N ℓ).base ↔ jChartFin N ℓ ∉ x₀.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_fFin_base, Set.mem_range]
  constructor
  · rintro ⟨xi, h⟩
    obtain ⟨w, hw, -⟩ := (pushout_inl_eq_inr_iff (fFin N ℓ) (fInf N ℓ) x₀ xi).mp h.symm
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(fInf N ℓ).base w, ((pushout_inl_eq_inr_iff (fFin N ℓ) (fInf N ℓ) _ _).mpr ⟨w, rfl, rfl⟩).symm⟩

end Igusa

end ModularCurve.IgusaScheme.CentreGen

end

open AlgebraicCurve IsDedekindDomain
open scoped IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme IgusaScheme.ιFin IgusaScheme.ιInf modularFunctionFieldFull CharPModel.jBar coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange modularFunctionFieldBar"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull coe_jFull jFull_ne_zero chartAlg chartAlg_mono coe_chartIncl exists_pow_mul_mem_chartAlg chartAlgFin chartAlgInf jChartFin jInvChartInf coe_jChartFin coe_jInvChartInf inclFin inclInf isLocalization_away_inclFin isLocalization_away_inclInf XFin XInf fFin fInf ιFin ιInf glue_condition igusaTo"
namespace CentreGen
p2m_open "ModularCurve.IgusaScheme ModularCurve"

universe u

theorem overlap_value {K L : Type u} [Field K] [CharZero K] [Field L] [Algebra K L] (t : L)
    [FiniteDimensional K⟮t⟯ L]
    (𝔭 : HeightOneSpectrum ↥(CurveModel.chartRing K ({t} : Set L)))
    (χ : ↥(CurveModel.chartRing K ({t} : Set L)) →+* K)
    (hχ : RingHom.ker χ = 𝔭.asIdeal) (hχK : ∀ c : K, χ (algebraMap K _ c) = c)
    (hχt : χ (CurveModel.tChart K t) ≠ 0)
    (r : ↥(CurveModel.chartRing K ({t} : Set L))) (β : L) (n : ℕ) (g : K)
    (hr : (r : L) = t ^ n * β) (hg : χ r = (χ (CurveModel.tChart K t)) ^ n * g)
    (hβ : β ∈ CurveModel.chartRing K ({t⁻¹} : Set L)) :
    β ∈ (Place.ofHeightOneSpectrum (K := K) (F := L) 𝔭).toValuationSubring ∧
      β - algebraMap K L g ∈
        (Place.ofHeightOneSpectrum (K := K) (F := L) 𝔭).toValuationSubring.nonunits := by

  let v := 𝔭.valuation L
  have hO : (Place.ofHeightOneSpectrum (K := K) (F := L) 𝔭).toValuationSubring = v.valuationSubring :=
    Place.ofHeightOneSpectrum_toValuationSubring 𝔭

  have hcoe : ∀ x : ↥(CurveModel.chartRing K ({t} : Set L)), (x : L) = algebraMap (↥(CurveModel.chartRing K ({t} : Set L))) L x := fun x => rfl
  have hle : ∀ x : ↥(CurveModel.chartRing K ({t} : Set L)), v (x : L) ≤ 1 := fun x => by rw [hcoe]; exact 𝔭.valuation_le_one x
  have hlt_iff : ∀ x : ↥(CurveModel.chartRing K ({t} : Set L)), v (x : L) < 1 ↔ x ∈ 𝔭.asIdeal := fun x => by
    rw [hcoe]; exact 𝔭.valuation_lt_one_iff_mem x

  have hconst : ∀ c : K, algebraMap K L c = ((algebraMap K (↥(CurveModel.chartRing K ({t} : Set L))) c : ↥(CurveModel.chartRing K ({t} : Set L))) : L) := fun c =>
    (IsScalarTower.algebraMap_apply K (↥(CurveModel.chartRing K ({t} : Set L))) L c)
  have hvK : ∀ c : K, v (algebraMap K L c) ≤ 1 := fun c => by rw [hconst]; exact hle _

  have hsub : ∀ x : ↥(CurveModel.chartRing K ({t} : Set L)), v ((x : L) - algebraMap K L (χ x)) < 1 := by
    intro x
    have hmem : x - algebraMap K (↥(CurveModel.chartRing K ({t} : Set L))) (χ x) ∈ 𝔭.asIdeal := by
      rw [← hχ, RingHom.mem_ker, map_sub, hχK, sub_self]
    have := (hlt_iff _).mpr hmem
    rwa [Subalgebra.coe_sub, ← hconst] at this

  have ht : v t = 1 := by
    have h1 : v ((CurveModel.tChart K t : ↥(CurveModel.chartRing K ({t} : Set L))) : L) ≤ 1 := hle _
    have h2 : ¬ v ((CurveModel.tChart K t : ↥(CurveModel.chartRing K ({t} : Set L))) : L) < 1 := by
      rw [hlt_iff, ← hχ, RingHom.mem_ker]; exact hχt
    rw [CurveModel.coe_tChart] at h1 h2
    exact le_antisymm h1 (not_lt.mp h2)
  have ht0 : t ≠ 0 := fun h => by rw [h, map_zero] at ht; exact zero_ne_one ht

  have hβO : β ∈ v.valuationSubring := by
    refine CurveModel.chartRing_le_valuationSubring v.valuationSubring (fun a => ?_) (fun x hx => ?_) hβ
    · exact (Valuation.mem_valuationSubring_iff v _).mpr (hvK a)
    · rw [Set.mem_singleton_iff.mp hx]
      exact (Valuation.mem_valuationSubring_iff v _).mpr (by rw [map_inv₀, ht, inv_one])
  refine ⟨hO ▸ hβO, ?_⟩

  set τ : L := algebraMap K L (χ (CurveModel.tChart K t)) with hτ
  have hvτ : v τ ≤ 1 := hvK _
  have hτt : v (τ - t) < 1 := by
    rw [Valuation.map_sub_swap]
    have := hsub (CurveModel.tChart K t)
    rwa [CurveModel.coe_tChart] at this

  have hgeom : v (τ ^ n - t ^ n) < 1 := by
    rw [← geom_sum₂_mul, map_mul]
    have hs : v (∑ i ∈ Finset.range n, τ ^ i * t ^ (n - 1 - i)) ≤ 1 := by
      apply Valuation.map_sum_le
      intro i _
      rw [map_mul, map_pow, map_pow, ht, one_pow, mul_one]
      exact pow_le_one₀ zero_le' hvτ
    calc v (∑ i ∈ Finset.range n, τ ^ i * t ^ (n - 1 - i)) * v (τ - t) ≤ 1 * v (τ - t) := by
          gcongr
      _ < 1 := by rw [one_mul]; exact hτt

  have hχr : algebraMap K L (χ r) = τ ^ n * algebraMap K L g := by
    rw [hg, map_mul, map_pow]

  have hsplit : (r : L) - t ^ n * algebraMap K L g =
      ((r : L) - algebraMap K L (χ r)) + algebraMap K L g * (τ ^ n - t ^ n) := by
    rw [hχr]; ring
  have hmain : v ((r : L) - t ^ n * algebraMap K L g) < 1 := by
    rw [hsplit]
    refine Valuation.map_add_lt v (hsub r) ?_
    rw [map_mul]
    calc v (algebraMap K L g) * v (τ ^ n - t ^ n) ≤ 1 * v (τ ^ n - t ^ n) := by gcongr; exact hvK g
      _ < 1 := by rw [one_mul]; exact hgeom
  have hβg : v (β - algebraMap K L g) < 1 := by
    have : (r : L) - t ^ n * algebraMap K L g = t ^ n * (β - algebraMap K L g) := by rw [hr]; ring
    rw [this, map_mul, map_pow, ht, one_pow, one_mul] at hmain
    exact hmain

  rw [hO, ValuationSubring.mem_nonunits_iff]
  exact (Valuation.isEquiv_valuation_valuationSubring v).lt_one_iff_lt_one.mp hβg

end ModularCurve.IgusaScheme.CentreGen

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme IgusaScheme.ιFin IgusaScheme.ιInf modularFunctionFieldFull CharPModel.jBar coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange modularFunctionFieldBar"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull coe_jFull jFull_ne_zero chartAlg chartAlg_mono coe_chartIncl exists_pow_mul_mem_chartAlg chartAlgFin chartAlgInf jChartFin jInvChartInf coe_jChartFin coe_jInvChartInf inclFin inclInf isLocalization_away_inclFin isLocalization_away_inclInf XFin XInf fFin fInf ιFin ιInf glue_condition igusaTo"
namespace CentreGen
p2m_open "ModularCurve.IgusaScheme ModularCurve"

section Main

local notation "𝕂" => AlgebraicClosure ℚ

theorem centreGen
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    (htrans : Transcendental (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar p))
    [hne : Fact (ModularCurve.CharPModel.jBar p ≠ 0)]
    [hfd : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({ModularCurve.CharPModel.jBar p} : Set (modularFunctionFieldBar p)))
      (modularFunctionFieldBar p)]
    [hfd_inv : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(ModularCurve.CharPModel.jBar p)⁻¹} : Set (modularFunctionFieldBar p)))
      (modularFunctionFieldBar p)]
    (eFin : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin p ℓ)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({ModularCurve.CharPModel.jBar p} : Set (modularFunctionFieldBar p))))
    (hFin : ∀ b : chartAlgFin p ℓ, ((eFin (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({ModularCurve.CharPModel.jBar p} : Set (modularFunctionFieldBar p)))) : modularFunctionFieldBar p)
      = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull p)).2⟩ : modularFunctionFieldBar p))
    (eInf : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf p ℓ)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({(ModularCurve.CharPModel.jBar p)⁻¹} : Set (modularFunctionFieldBar p))))
    (hInf : ∀ b : chartAlgInf p ℓ, ((eInf (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({(ModularCurve.CharPModel.jBar p)⁻¹} : Set (modularFunctionFieldBar p)))) : modularFunctionFieldBar p)
      = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull p)).2⟩ : modularFunctionFieldBar p)) :
    let Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p) :=
      CurveModel.ofGenerator (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar p) htrans
    ∀ (eη : Mη.C ⟶ pullback (igusaTo p ℓ) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) (_ : IsIso eη)
      (heη : eη ≫ pullback.snd (igusaTo p ℓ) _ = Mη.toBase)
      (hchartFin : AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ)
          (ModularCurve.CharPModel.jBar p) ≫ eη ≫ pullback.fst (igusaTo p ℓ) _ =
        Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := AlgebraicClosure ℚ)
            (B := ↥(chartAlgFin p ℓ))).toRingHom)) ≫ ModularCurve.IgusaScheme.ιFin p ℓ)
      (hchartInf : AlgebraicCurve.CurveModel.ιInf (AlgebraicClosure ℚ)
          (ModularCurve.CharPModel.jBar p) ≫ eη ≫ pullback.fst (igusaTo p ℓ) _ =
        Spec.map (CommRingCat.ofHom (eInf.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := AlgebraicClosure ℚ)
            (B := ↥(chartAlgInf p ℓ))).toRingHom)) ≫ ModularCurve.IgusaScheme.ιInf p ℓ),
    (∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (γ : ↥(chartAlgFin p ℓ) →+* AlgebraicClosure ℚ),
        x.1 ≫ eη ≫ pullback.fst (igusaTo p ℓ) _ =
          Spec.map (CommRingCat.ofHom γ) ≫ ModularCurve.IgusaScheme.ιFin p ℓ →
        ∀ b : ↥(chartAlgFin p ℓ),
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ∈ (Mη.pointEquivPlace x).toValuationSubring ∧
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) -
              algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) (γ b) ∈
            (Mη.pointEquivPlace x).toValuationSubring.nonunits) ∧
    (∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (γ : ↥(chartAlgInf p ℓ) →+* AlgebraicClosure ℚ),
        x.1 ≫ eη ≫ pullback.fst (igusaTo p ℓ) _ =
          Spec.map (CommRingCat.ofHom γ) ≫ ModularCurve.IgusaScheme.ιInf p ℓ →
        ∀ b : ↥(chartAlgInf p ℓ),
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ∈ (Mη.pointEquivPlace x).toValuationSubring ∧
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) -
              algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) (γ b) ∈
            (Mη.pointEquivPlace x).toValuationSubring.nonunits) := by
  intro Mη eη _ heη hchartFin hchartInf

  obtain ⟨e, he⟩ : ∃ e : CurveModel.glued 𝕂 (ModularCurve.CharPModel.jBar p) ⟶
      pullback (igusaTo p ℓ) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) 𝕂))), e = eη := ⟨eη, rfl⟩
  have hchartFin' : CurveModel.ι₀ 𝕂 (ModularCurve.CharPModel.jBar p) ≫ e ≫
      pullback.fst (igusaTo p ℓ) _ = Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := 𝕂) (B := ↥(chartAlgFin p ℓ))).toRingHom)) ≫
        ιFin p ℓ := by rw [he]; exact hchartFin
  have hchartInf' : CurveModel.ιInf 𝕂 (ModularCurve.CharPModel.jBar p) ≫ e ≫
      pullback.fst (igusaTo p ℓ) _ = Spec.map (CommRingCat.ofHom (eInf.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := 𝕂) (B := ↥(chartAlgInf p ℓ))).toRingHom)) ≫
        ιInf p ℓ := by rw [he]; exact hchartInf
  have ht0 : ModularCurve.CharPModel.jBar p ≠ 0 := hne.out

  have hplace : ∀ x : {q : Spec (CommRingCat.of 𝕂) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _},
      Mη.pointEquivPlace x = CurveModel.gluedPlaceOfPoint 𝕂 (ModularCurve.CharPModel.jBar p) htrans
        (pointEquivClosedPoint Mη.toBase x) := fun x => rfl

  have hretype : ∀ x : {q : Spec (CommRingCat.of 𝕂) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _},
      ∃ x₁ : Spec (CommRingCat.of 𝕂) ⟶ CurveModel.glued 𝕂 (ModularCurve.CharPModel.jBar p),
        x₁ ≫ CurveModel.gluedToBase 𝕂 (ModularCurve.CharPModel.jBar p) = 𝟙 _ ∧
        (pointEquivClosedPoint Mη.toBase x).1 = x₁.base (closedPoint 𝕂) ∧
        x₁ ≫ e ≫ pullback.fst (igusaTo p ℓ) _ = x.1 ≫ eη ≫ pullback.fst (igusaTo p ℓ) _ := by
    intro x
    refine ⟨x.1, x.2, rfl, ?_⟩
    subst he
    rfl

  have heFinj : eFin (1 ⊗ₜ jChartFin p ℓ) = CurveModel.tChart 𝕂 (ModularCurve.CharPModel.jBar p) := by
    apply Subtype.ext
    rw [hFin, CurveModel.coe_tChart]
    rfl
  have heInfj : eInf (1 ⊗ₜ jInvChartInf p ℓ) =
      CurveModel.tInvChart 𝕂 (ModularCurve.CharPModel.jBar p) := by
    apply Subtype.ext
    rw [hInf, CurveModel.coe_tInvChart]
    apply Subtype.ext
    simp only [coe_jInvChartInf, IntermediateField.coe_inv, map_inv₀]
    rfl

  have hsec₀ : ∀ (x₁ : Spec (CommRingCat.of 𝕂) ⟶ CurveModel.glued 𝕂 (ModularCurve.CharPModel.jBar p))
      (_ : x₁ ≫ CurveModel.gluedToBase 𝕂 (ModularCurve.CharPModel.jBar p) = 𝟙 _)
      (χ : CommRingCat.of ↥(CurveModel.chartRing 𝕂 ({ModularCurve.CharPModel.jBar p} :
        Set (modularFunctionFieldBar p))) ⟶ CommRingCat.of 𝕂),
      x₁ = Spec.map χ ≫ CurveModel.ι₀ 𝕂 (ModularCurve.CharPModel.jBar p) →
        ∀ c : 𝕂, χ.hom (algebraMap 𝕂 _ c) = c := by
    intro x₁ hx₁ χ hfac c
    apply apply_algebraMap_of_spec_map_comp
    rw [CommRingCat.ofHom_hom, ← CurveModel.ι₀_gluedToBase, ← Category.assoc, ← hfac]
    exact hx₁
  have hsecInf : ∀ (x₁ : Spec (CommRingCat.of 𝕂) ⟶ CurveModel.glued 𝕂 (ModularCurve.CharPModel.jBar p))
      (_ : x₁ ≫ CurveModel.gluedToBase 𝕂 (ModularCurve.CharPModel.jBar p) = 𝟙 _)
      (χ : CommRingCat.of ↥(CurveModel.chartRing 𝕂 ({(ModularCurve.CharPModel.jBar p)⁻¹} :
        Set (modularFunctionFieldBar p))) ⟶ CommRingCat.of 𝕂),
      x₁ = Spec.map χ ≫ CurveModel.ιInf 𝕂 (ModularCurve.CharPModel.jBar p) →
        ∀ c : 𝕂, χ.hom (algebraMap 𝕂 _ c) = c := by
    intro x₁ hx₁ χ hfac c
    apply apply_algebraMap_of_spec_map_comp
    rw [CommRingCat.ofHom_hom, ← CurveModel.ιInf_gluedToBase, ← Category.assoc, ← hfac]
    exact hx₁

  have hbase : ∀ {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (z : X),
      (f ≫ g).base z = g.base (f.base z) := fun f g z => rfl
  refine ⟨?_, ?_⟩

  · intro x γ hx0 b
    obtain ⟨x₁, hx₁, hpt_val, hxe⟩ := hretype x
    have hx : x₁ ≫ e ≫ pullback.fst (igusaTo p ℓ) _ = Spec.map (CommRingCat.ofHom γ) ≫ ιFin p ℓ := by
      rw [hxe]; exact hx0
    by_cases h0 : x₁.base (closedPoint 𝕂) ∈
        Set.range (CurveModel.ι₀ 𝕂 (ModularCurve.CharPModel.jBar p)).base
    ·
      obtain ⟨χ, hfac⟩ := exists_eq_spec_map_comp_of_mem_range
        (CurveModel.ι₀ 𝕂 (ModularCurve.CharPModel.jBar p)) x₁ h0
      have hpt : x₁.base (closedPoint 𝕂) =
          (CurveModel.ι₀ 𝕂 (ModularCurve.CharPModel.jBar p)).base
            ((Spec.map χ).base (closedPoint 𝕂)) := by
        rw [hfac]; rfl
      have hcl : (CurveModel.ι₀ 𝕂 (ModularCurve.CharPModel.jBar p)).base
            ((Spec.map χ).base (closedPoint 𝕂)) ∈
          closedPoints (CurveModel.glued 𝕂 (ModularCurve.CharPModel.jBar p)) := by
        rw [← hpt, ← hpt_val]; exact (pointEquivClosedPoint Mη.toBase x).2
      have hv : Mη.pointEquivPlace x = Place.ofHeightOneSpectrum (K := 𝕂)
          (CurveModel.primeOfι₀ 𝕂 (ModularCurve.CharPModel.jBar p) htrans _ hcl) := by
        rw [hplace, ← CurveModel.gluedPlaceOfPoint_ι₀]
        congr 1
        exact Subtype.ext (hpt_val.trans hpt)

      have h1 := hx
      rw [hfac, Category.assoc, hchartFin', ← Category.assoc, cancel_mono, ← Spec.map_comp,
        ← CommRingCat.ofHom_hom χ, ← CommRingCat.ofHom_comp] at h1
      have hγ := ringHom_eq_of_spec_map_eq h1
      have hγb : γ b = χ.hom (eFin (1 ⊗ₜ b)) := by rw [← hγ]; rfl
      have hker : RingHom.ker χ.hom =
          (CurveModel.primeOfι₀ 𝕂 (ModularCurve.CharPModel.jBar p) htrans _ hcl).asIdeal := by
        rw [CurveModel.primeOfι₀_asIdeal, spec_map_base_closedPoint_asIdeal]
      have key := mem_and_sub_mem_nonunits_ofHeightOneSpectrum (K := 𝕂)
        (L := modularFunctionFieldBar p)
        (CurveModel.primeOfι₀ 𝕂 (ModularCurve.CharPModel.jBar p) htrans _ hcl) χ.hom hker
        (hsec₀ x₁ hx₁ χ hfac) (eFin (1 ⊗ₜ b))
      rw [hv, hγb]
      have hcoe : algebraMap _ (modularFunctionFieldBar p) (eFin (1 ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b)) =
          ((eFin (1 ⊗ₜ b) : ↥(CurveModel.chartRing 𝕂 ({ModularCurve.CharPModel.jBar p} :
            Set (modularFunctionFieldBar p)))) : modularFunctionFieldBar p) := rfl
      rw [hcoe, hFin] at key
      exact key
    ·
      exfalso
      have hI : x₁.base (closedPoint 𝕂) ∈
          Set.range (CurveModel.ιInf 𝕂 (ModularCurve.CharPModel.jBar p)).base :=
        (CurveModel.mem_range_ι₀_or_mem_range_ιInf 𝕂 (ModularCurve.CharPModel.jBar p) _).resolve_left h0
      obtain ⟨χ', hfac'⟩ := exists_eq_spec_map_comp_of_mem_range
        (CurveModel.ιInf 𝕂 (ModularCurve.CharPModel.jBar p)) x₁ hI
      have hpt : x₁.base (closedPoint 𝕂) =
          (CurveModel.ιInf 𝕂 (ModularCurve.CharPModel.jBar p)).base
            ((Spec.map χ').base (closedPoint 𝕂)) := by
        rw [hfac']; rfl
      have htinv : CurveModel.tInvChart 𝕂 (ModularCurve.CharPModel.jBar p) ∈
          ((Spec.map χ').base (closedPoint 𝕂)).asIdeal := by
        by_contra hne'
        exact h0 (hpt ▸ (CurveModel.ιInf_mem_range_ι₀_iff 𝕂 (ModularCurve.CharPModel.jBar p) _).mpr hne')
      rw [spec_map_base_closedPoint_asIdeal, RingHom.mem_ker] at htinv

      have h1 := hx
      rw [hfac', Category.assoc, hchartInf', ← Category.assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_hom χ', ← CommRingCat.ofHom_comp] at h1
      have h2 : (ιInf p ℓ).base ((Spec.map (CommRingCat.ofHom (χ'.hom.comp
          (eInf.toAlgHom.toRingHom.comp (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := 𝕂) (B := ↥(chartAlgInf p ℓ))).toRingHom)))).base
            (closedPoint 𝕂)) ∈ Set.range (ιFin p ℓ).base := by
        refine ⟨(Spec.map (CommRingCat.ofHom γ)).base (closedPoint 𝕂), ?_⟩
        rw [← hbase, ← hbase, h1]
      rw [ιInf_base_mem_range_ιFin_iff, spec_map_base_closedPoint_asIdeal, CommRingCat.hom_ofHom,
        RingHom.mem_ker] at h2
      apply h2
      show χ'.hom (eInf (1 ⊗ₜ jInvChartInf p ℓ)) = 0
      rw [heInfj]
      exact htinv

  · intro x γ hx0 b
    obtain ⟨x₁, hx₁, hpt_val, hxe⟩ := hretype x
    have hx : x₁ ≫ e ≫ pullback.fst (igusaTo p ℓ) _ = Spec.map (CommRingCat.ofHom γ) ≫ ιInf p ℓ := by
      rw [hxe]; exact hx0
    by_cases h0 : x₁.base (closedPoint 𝕂) ∈
        Set.range (CurveModel.ι₀ 𝕂 (ModularCurve.CharPModel.jBar p)).base
    swap
    ·
      have hI : x₁.base (closedPoint 𝕂) ∈
          Set.range (CurveModel.ιInf 𝕂 (ModularCurve.CharPModel.jBar p)).base :=
        (CurveModel.mem_range_ι₀_or_mem_range_ιInf 𝕂 (ModularCurve.CharPModel.jBar p) _).resolve_left h0
      obtain ⟨χ', hfac'⟩ := exists_eq_spec_map_comp_of_mem_range
        (CurveModel.ιInf 𝕂 (ModularCurve.CharPModel.jBar p)) x₁ hI
      have hpt : x₁.base (closedPoint 𝕂) =
          (CurveModel.ιInf 𝕂 (ModularCurve.CharPModel.jBar p)).base
            ((Spec.map χ').base (closedPoint 𝕂)) := by
        rw [hfac']; rfl
      have hcl : (CurveModel.ιInf 𝕂 (ModularCurve.CharPModel.jBar p)).base
            ((Spec.map χ').base (closedPoint 𝕂)) ∈
          closedPoints (CurveModel.glued 𝕂 (ModularCurve.CharPModel.jBar p)) := by
        rw [← hpt, ← hpt_val]; exact (pointEquivClosedPoint Mη.toBase x).2
      have h0' : (pointEquivClosedPoint Mη.toBase x).1 ∉
          Set.range (CurveModel.ι₀ 𝕂 (ModularCurve.CharPModel.jBar p)).base := by
        rw [hpt_val]; exact h0
      have hv : Mη.pointEquivPlace x = Place.ofHeightOneSpectrum (K := 𝕂)
          (CurveModel.primeOfιInf 𝕂 (ModularCurve.CharPModel.jBar p) htrans _ hcl) := by
        rw [hplace]
        exact CurveModel.gluedPlaceOfPoint_of_not_mem 𝕂 (ModularCurve.CharPModel.jBar p) htrans _ h0'
          _ (hpt_val.trans hpt).symm
      have h1 := hx
      rw [hfac', Category.assoc, hchartInf', ← Category.assoc, cancel_mono, ← Spec.map_comp,
        ← CommRingCat.ofHom_hom χ', ← CommRingCat.ofHom_comp] at h1
      have hγ := ringHom_eq_of_spec_map_eq h1
      have hγb : γ b = χ'.hom (eInf (1 ⊗ₜ b)) := by rw [← hγ]; rfl
      have hker : RingHom.ker χ'.hom =
          (CurveModel.primeOfιInf 𝕂 (ModularCurve.CharPModel.jBar p) htrans _ hcl).asIdeal := by
        rw [CurveModel.primeOfιInf_asIdeal, spec_map_base_closedPoint_asIdeal]
      have key := mem_and_sub_mem_nonunits_ofHeightOneSpectrum (K := 𝕂)
        (L := modularFunctionFieldBar p)
        (CurveModel.primeOfιInf 𝕂 (ModularCurve.CharPModel.jBar p) htrans _ hcl) χ'.hom hker
        (hsecInf x₁ hx₁ χ' hfac') (eInf (1 ⊗ₜ b))
      rw [hv, hγb]
      have hcoe : algebraMap _ (modularFunctionFieldBar p) (eInf (1 ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b)) =
          ((eInf (1 ⊗ₜ b) : ↥(CurveModel.chartRing 𝕂 ({(ModularCurve.CharPModel.jBar p)⁻¹} :
            Set (modularFunctionFieldBar p)))) : modularFunctionFieldBar p) := rfl
      rw [hcoe, hInf] at key
      exact key
    ·
      obtain ⟨χ, hfac⟩ := exists_eq_spec_map_comp_of_mem_range
        (CurveModel.ι₀ 𝕂 (ModularCurve.CharPModel.jBar p)) x₁ h0
      have hpt : x₁.base (closedPoint 𝕂) =
          (CurveModel.ι₀ 𝕂 (ModularCurve.CharPModel.jBar p)).base
            ((Spec.map χ).base (closedPoint 𝕂)) := by
        rw [hfac]; rfl
      have hcl : (CurveModel.ι₀ 𝕂 (ModularCurve.CharPModel.jBar p)).base
            ((Spec.map χ).base (closedPoint 𝕂)) ∈
          closedPoints (CurveModel.glued 𝕂 (ModularCurve.CharPModel.jBar p)) := by
        rw [← hpt, ← hpt_val]; exact (pointEquivClosedPoint Mη.toBase x).2
      have hv : Mη.pointEquivPlace x = Place.ofHeightOneSpectrum (K := 𝕂)
          (CurveModel.primeOfι₀ 𝕂 (ModularCurve.CharPModel.jBar p) htrans _ hcl) := by
        rw [hplace, ← CurveModel.gluedPlaceOfPoint_ι₀]
        congr 1
        exact Subtype.ext (hpt_val.trans hpt)
      generalize h𝔭 : CurveModel.primeOfι₀ 𝕂 (ModularCurve.CharPModel.jBar p) htrans _ hcl = 𝔭 at hv
      have hker : RingHom.ker χ.hom = 𝔭.asIdeal := by
        rw [← h𝔭, CurveModel.primeOfι₀_asIdeal, spec_map_base_closedPoint_asIdeal]
      have hsec := hsec₀ x₁ hx₁ χ hfac

      have h1 : Spec.map (CommRingCat.ofHom (χ.hom.comp (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := 𝕂) (B := ↥(chartAlgFin p ℓ))).toRingHom))) ≫
            ιFin p ℓ = Spec.map (CommRingCat.ofHom γ) ≫ ιInf p ℓ := by
        rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
          ← hchartFin', ← Category.assoc, ← hfac]
        exact hx

      have hj : jChartFin p ℓ ∉ ((Spec.map (CommRingCat.ofHom (χ.hom.comp (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := 𝕂) (B := ↥(chartAlgFin p ℓ))).toRingHom)))).base
            (closedPoint 𝕂)).asIdeal := by
        rw [← ιFin_base_mem_range_ιInf_iff]
        exact ⟨(Spec.map (CommRingCat.ofHom γ)).base (closedPoint 𝕂), by rw [← hbase, ← hbase, h1]⟩
      have hr : (Spec.map (CommRingCat.ofHom (χ.hom.comp (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := 𝕂) (B := ↥(chartAlgFin p ℓ))).toRingHom)))).base
            (closedPoint 𝕂) ∈ Set.range (fFin p ℓ).base := by
        rw [range_fFin_base]
        exact hj
      have hχt : χ.hom (CurveModel.tChart 𝕂 (ModularCurve.CharPModel.jBar p)) ≠ 0 := by
        rw [spec_map_base_closedPoint_asIdeal, CommRingCat.hom_ofHom, RingHom.mem_ker] at hj
        change ¬ χ.hom (eFin (1 ⊗ₜ jChartFin p ℓ)) = 0 at hj
        rwa [heFinj] at hj

      obtain ⟨δ, hδ⟩ := exists_eq_spec_map_comp_of_mem_range (fFin p ℓ) _ hr
      have hγ₀δ : χ.hom.comp (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := 𝕂) (B := ↥(chartAlgFin p ℓ))).toRingHom) =
          δ.hom.comp (inclFin p ℓ).toRingHom := by
        apply ringHom_eq_of_spec_map_eq
        rw [hδ, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp]
      have hγδ : γ = δ.hom.comp (inclInf p ℓ).toRingHom := by
        have h3 : Spec.map (CommRingCat.ofHom γ) ≫ ιInf p ℓ = (Spec.map δ ≫ fInf p ℓ) ≫ ιInf p ℓ := by
          rw [← h1, hδ, Category.assoc, Category.assoc]
          show _ = Spec.map δ ≫ fInf p ℓ ≫ ιInf p ℓ
          rw [← glue_condition]
        rw [cancel_mono] at h3
        apply ringHom_eq_of_spec_map_eq
        rw [h3, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp]
      have hγ₀_apply : ∀ a : ↥(chartAlgFin p ℓ), χ.hom (eFin (1 ⊗ₜ a)) = δ.hom (inclFin p ℓ a) :=
        fun a => RingHom.congr_fun hγ₀δ a
      have hγ_apply : ∀ c : ↥(chartAlgInf p ℓ), γ c = δ.hom (inclInf p ℓ c) :=
        fun c => RingHom.congr_fun hγδ c

      have hbmem : (b : ↥(modularFunctionFieldFull p)) ∈ chartAlg p ℓ (insert (jFull p)⁻¹ {jFull p}) :=
        chartAlg_mono p ℓ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) b.2
      obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartAlg (Set.mem_singleton (jFull p)) (jFull_ne_zero p) hbmem
      set a : ↥(chartAlgFin p ℓ) := ⟨(jFull p) ^ n * (b : ↥(modularFunctionFieldFull p)), hn⟩ with ha
      have hmid : inclFin p ℓ a = (inclFin p ℓ (jChartFin p ℓ)) ^ n * inclInf p ℓ b := by
        apply Subtype.ext
        simp only [coe_chartIncl, Subalgebra.coe_mul, Subalgebra.coe_pow, coe_jChartFin, ha]

      have hE1 : χ.hom (eFin (1 ⊗ₜ a)) =
          (χ.hom (CurveModel.tChart 𝕂 (ModularCurve.CharPModel.jBar p))) ^ n * γ b := by
        rw [hγ₀_apply, hmid, map_mul, map_pow, ← hγ₀_apply, heFinj, ← hγ_apply]

      have hE2 : ((eFin (1 ⊗ₜ a) : ↥(CurveModel.chartRing 𝕂 ({ModularCurve.CharPModel.jBar p} :
            Set (modularFunctionFieldBar p)))) : modularFunctionFieldBar p) =
          (ModularCurve.CharPModel.jBar p) ^ n *
            (⟨coeffEmb 𝕂 ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
              coeffEmb_mem_laurentBaseChange 𝕂 (b : ↥(modularFunctionFieldFull p)).2⟩ :
                modularFunctionFieldBar p) := by
        rw [hFin]
        apply Subtype.ext
        simp only [ha, IntermediateField.coe_mul, IntermediateField.coe_pow, map_mul, map_pow, coe_jFull]
        rfl
      have hβ : (⟨coeffEmb 𝕂 ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange 𝕂 (b : ↥(modularFunctionFieldFull p)).2⟩ :
            modularFunctionFieldBar p) ∈
          CurveModel.chartRing 𝕂 ({(ModularCurve.CharPModel.jBar p)⁻¹} : Set (modularFunctionFieldBar p)) := by
        rw [← hInf]; exact (eInf (1 ⊗ₜ b)).2
      rw [hv]
      exact overlap_value (ModularCurve.CharPModel.jBar p) 𝔭 χ.hom hker hsec hχt (eFin (1 ⊗ₜ a)) _ n (γ b)
        hE2 hE1 hβ

end Main

end ModularCurve.IgusaScheme.CentreGen

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry _root_.ModularCurve _root_.P2MW.S_ModularCurve_IgusaScheme_coeffEmb_sub_mem_nonunits_pointEquivPlace_ofGenerator_of_chartPin.ModularCurve ModularCurve.CharPModel AlgebraicCurve IsLocalRing _root_.ModularCurve.IgusaScheme _root_.P2MW.S_ModularCurve_IgusaScheme_coeffEmb_sub_mem_nonunits_pointEquivPlace_ofGenerator_of_chartPin.ModularCurve.IgusaScheme in
open scoped TensorProduct in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    (htrans : Transcendental (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar p))
    [hne : Fact (ModularCurve.CharPModel.jBar p ≠ 0)]
    [hfd : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({ModularCurve.CharPModel.jBar p} : Set (modularFunctionFieldBar p)))
      (modularFunctionFieldBar p)]
    [hfd_inv : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(ModularCurve.CharPModel.jBar p)⁻¹} : Set (modularFunctionFieldBar p)))
      (modularFunctionFieldBar p)]
    (eFin : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin p ℓ)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({ModularCurve.CharPModel.jBar p} : Set (modularFunctionFieldBar p))))
    (hFin : ∀ b : chartAlgFin p ℓ, ((eFin (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({ModularCurve.CharPModel.jBar p} : Set (modularFunctionFieldBar p)))) : modularFunctionFieldBar p)
      = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull p)).2⟩ : modularFunctionFieldBar p))
    (eInf : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf p ℓ)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({(ModularCurve.CharPModel.jBar p)⁻¹} : Set (modularFunctionFieldBar p))))
    (hInf : ∀ b : chartAlgInf p ℓ, ((eInf (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({(ModularCurve.CharPModel.jBar p)⁻¹} : Set (modularFunctionFieldBar p)))) : modularFunctionFieldBar p)
      = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull p)).2⟩ : modularFunctionFieldBar p)) :
    let Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p) :=
      CurveModel.ofGenerator (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar p) htrans
    ∀ (eη : Mη.C ⟶ pullback (igusaTo p ℓ) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) (_ : IsIso eη)
      (heη : eη ≫ pullback.snd (igusaTo p ℓ) _ = Mη.toBase)
      (hchartFin : AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ)
          (ModularCurve.CharPModel.jBar p) ≫ eη ≫ pullback.fst (igusaTo p ℓ) _ =
        Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := AlgebraicClosure ℚ)
            (B := ↥(chartAlgFin p ℓ))).toRingHom)) ≫ ModularCurve.IgusaScheme.ιFin p ℓ)
      (hchartInf : AlgebraicCurve.CurveModel.ιInf (AlgebraicClosure ℚ)
          (ModularCurve.CharPModel.jBar p) ≫ eη ≫ pullback.fst (igusaTo p ℓ) _ =
        Spec.map (CommRingCat.ofHom (eInf.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := AlgebraicClosure ℚ)
            (B := ↥(chartAlgInf p ℓ))).toRingHom)) ≫ ModularCurve.IgusaScheme.ιInf p ℓ),
    (∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (γ : ↥(chartAlgFin p ℓ) →+* AlgebraicClosure ℚ),
        x.1 ≫ eη ≫ pullback.fst (igusaTo p ℓ) _ =
          Spec.map (CommRingCat.ofHom γ) ≫ ModularCurve.IgusaScheme.ιFin p ℓ →
        ∀ b : ↥(chartAlgFin p ℓ),
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ∈ (Mη.pointEquivPlace x).toValuationSubring ∧
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) -
              algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) (γ b) ∈
            (Mη.pointEquivPlace x).toValuationSubring.nonunits) ∧
    (∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (γ : ↥(chartAlgInf p ℓ) →+* AlgebraicClosure ℚ),
        x.1 ≫ eη ≫ pullback.fst (igusaTo p ℓ) _ =
          Spec.map (CommRingCat.ofHom γ) ≫ ModularCurve.IgusaScheme.ιInf p ℓ →
        ∀ b : ↥(chartAlgInf p ℓ),
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ∈ (Mη.pointEquivPlace x).toValuationSubring ∧
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) -
              algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) (γ b) ∈
            (Mη.pointEquivPlace x).toValuationSubring.nonunits) := by
  exact ModularCurve.IgusaScheme.CentreGen.centreGen p ℓ hℓp htrans eFin hFin eInf hInf

end S_ModularCurve_IgusaScheme_coeffEmb_sub_mem_nonunits_pointEquivPlace_ofGenerator_of_chartPin
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_coeffEmb_sub_mem_nonunits_pointEquivPlace_ofGenerator_of_chartPin (solution)
