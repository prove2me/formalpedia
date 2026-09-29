-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.exists_blowupChart_ringHom_away_extends_chartMap_of_eq_adjoin_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/7e2a9906-43db-58e2-8153-4a0018c77720

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_blowupChart_ringHom_away_extends_chartMap_of_eq_adjoin_of_dvd

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace K4Phi

open IsLocalRing

theorem exists_ringHom_adjoin {C K S L : Type*} [CommRing C] [Field K] [Algebra C K]
    (hinj : Function.Injective (algebraMap C K))
    (t : C) (ht : t ≠ 0)
    (T : Set K) (hT : ∀ x ∈ T, ∃ i : C, x * algebraMap C K t = algebraMap C K i)
    [CommRing S] (Ψ : C →+* S) (s : S) (hs : Ψ t = s) [CommRing L] [Algebra S L] [IsLocalization.Away s L] :
    ∃ Φ : ↥(Algebra.adjoin C T) →+* L,
      (∀ a : C, Φ (algebraMap C _ a) = algebraMap S L (Ψ a)) ∧
      (∀ (x : ↥(Algebra.adjoin C T)) (i : C), (x : K) * algebraMap C K t = algebraMap C K i →
          Φ x * algebraMap S L s = algebraMap S L (Ψ i)) := by
  classical
  have htK : algebraMap C K t ≠ 0 := (map_ne_zero_iff _ hinj).mpr ht

  let Cl := Localization.Away t
  let f₁ : Cl →+* K := IsLocalization.Away.lift t (g := algebraMap C K) (isUnit_iff_ne_zero.mpr htK)
  have hf₁ : ∀ c : C, f₁ (algebraMap C Cl c) = algebraMap C K c := fun c =>
    IsLocalization.Away.lift_eq t _ c
  let f₁A : Cl →ₐ[C] K := { toRingHom := f₁, commutes' := fun c => hf₁ c }
  let f₂ : Cl →+* L := IsLocalization.Away.lift t (g := (algebraMap S L).comp Ψ)
    (by rw [RingHom.comp_apply, hs]; exact IsLocalization.Away.algebraMap_isUnit (S := L) s)
  have hf₂ : ∀ c : C, f₂ (algebraMap C Cl c) = algebraMap S L (Ψ c) := fun c =>
    IsLocalization.Away.lift_eq t _ c

  have hf₁inj : Function.Injective f₁A := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨c, d⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers t) z
    have hspec := IsLocalization.mk'_spec Cl c d
    have h1 : f₁ (IsLocalization.mk' Cl c d) * f₁ (algebraMap C Cl d) = f₁ (algebraMap C Cl c) := by
      rw [← map_mul, hspec]
    have hz' : f₁ (IsLocalization.mk' Cl c d) = 0 := hz
    rw [hz', zero_mul, hf₁] at h1
    have hc : c = 0 := hinj (by rw [← h1, map_zero])
    show IsLocalization.mk' Cl c d = 0
    rw [hc, IsLocalization.mk'_zero]
  let e : Cl ≃ₐ[C] ↥(f₁A.range) := AlgEquiv.ofInjective f₁A hf₁inj
  have he : ∀ z : Cl, ((e z : ↥(f₁A.range)) : K) = f₁ z := fun z => rfl
  have he' : ∀ w : ↥(f₁A.range), f₁ (e.symm w) = (w : K) := fun w => by
    rw [← he, AlgEquiv.apply_symm_apply]

  have hle : Algebra.adjoin C T ≤ f₁A.range := by
    refine Algebra.adjoin_le ?_
    intro x hx
    obtain ⟨i, hi⟩ := hT x hx
    refine ⟨IsLocalization.mk' Cl i (⟨t, Submonoid.mem_powers t⟩ : Submonoid.powers t), ?_⟩
    apply mul_right_cancel₀ htK
    have hsp : (IsLocalization.mk' Cl i (⟨t, Submonoid.mem_powers t⟩ : Submonoid.powers t)) * algebraMap C Cl t =
        algebraMap C Cl i := IsLocalization.mk'_spec Cl i ⟨t, Submonoid.mem_powers t⟩
    calc f₁A (IsLocalization.mk' Cl i (⟨t, Submonoid.mem_powers t⟩ : Submonoid.powers t)) * algebraMap C K t
        = f₁ (IsLocalization.mk' Cl i (⟨t, Submonoid.mem_powers t⟩ : Submonoid.powers t)) * f₁ (algebraMap C Cl t) := by
          rw [hf₁]; rfl
      _ = f₁ (algebraMap C Cl i) := by rw [← map_mul, hsp]
      _ = x * algebraMap C K t := by rw [hf₁, ← hi]
  let Φ : ↥(Algebra.adjoin C T) →+* L :=
    f₂.comp ((e.symm : ↥(f₁A.range) →ₐ[C] Cl).toRingHom.comp (Subalgebra.inclusion hle).toRingHom)
  have hΦ : ∀ x : ↥(Algebra.adjoin C T), Φ x = f₂ (e.symm (Subalgebra.inclusion hle x)) := fun x => rfl
  refine ⟨Φ, ?_, ?_⟩
  · intro a
    rw [hΦ, AlgHom.commutes, AlgEquiv.commutes, hf₂]
  · intro x i hxi
    have hz : e.symm (Subalgebra.inclusion hle x) * algebraMap C Cl t = algebraMap C Cl i := by
      apply hf₁inj
      show f₁ _ = f₁ _
      rw [map_mul, he', hf₁, hf₁, Subalgebra.coe_inclusion]
      exact hxi
    rw [hΦ, ← hs, ← hf₂ t, ← map_mul, hz, hf₂]

theorem mem_closure_of_forall {C K S L : Type*} [CommRing C] [Field K] [Algebra C K]
    (t : C) (T : Set K) [CommRing S] (Ψ : C →+* S) (s : S) [CommRing L] [Algebra S L] [IsLocalization.Away s L]
    (s₀ s₁ : S)
    (hT : ∀ x ∈ T, ∃ i : C, Ψ i ∈ Ideal.span {s, s₀, s₁} ∧ x * algebraMap C K t = algebraMap C K i)
    (Φ : ↥(Algebra.adjoin C T) →+* L)
    (hΦ₁ : ∀ a : C, Φ (algebraMap C _ a) = algebraMap S L (Ψ a))
    (hΦ₂ : ∀ (x : ↥(Algebra.adjoin C T)) (i : C), (x : K) * algebraMap C K t = algebraMap C K i →
          Φ x * algebraMap S L s = algebraMap S L (Ψ i)) :
    ∀ b : ↥(Algebra.adjoin C T), Φ b ∈ Subring.closure (Set.range (algebraMap S L) ∪
      {algebraMap S L s₀ * IsLocalization.Away.invSelf (S := L) s,
       algebraMap S L s₁ * IsLocalization.Away.invSelf (S := L) s}) := by
  intro b
  obtain ⟨b, hb⟩ := b
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨i, hi, hxi⟩ := hT x hx
      have h2 := hΦ₂ ⟨x, Algebra.subset_adjoin hx⟩ i hxi
      have hinv : algebraMap S L s * IsLocalization.Away.invSelf (S := L) s = 1 :=
        IsLocalization.Away.mul_invSelf s
      have hΦx : Φ ⟨x, Algebra.subset_adjoin hx⟩ = algebraMap S L (Ψ i) * IsLocalization.Away.invSelf (S := L) s := by
        rw [← h2, mul_assoc, hinv, mul_one]
      rw [hΦx]
      rw [Ideal.mem_span_insert] at hi
      obtain ⟨a, r, hr, hi⟩ := hi
      rw [Ideal.mem_span_insert] at hr
      obtain ⟨b', r', hr', hr⟩ := hr
      obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp hr'
      rw [hi, hr, ← hc']
      simp only [map_add, map_mul, add_mul]
      refine Subring.add_mem _ ?_ (Subring.add_mem _ ?_ ?_)
      · rw [mul_assoc, hinv, mul_one]
        exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
      · rw [mul_assoc]
        exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨b', rfl⟩))
          (Subring.subset_closure (Or.inr (Or.inl rfl)))
      · rw [mul_assoc]
        exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨c', rfl⟩))
          (Subring.subset_closure (Or.inr (Or.inr rfl)))
  | algebraMap c =>
      change Φ (algebraMap C (Algebra.adjoin C T) c) ∈ _
      rw [hΦ₁]
      exact Subring.subset_closure (Or.inl ⟨Ψ c, rfl⟩)
  | add x y hx hy ihx ihy =>
      have : (⟨x + y, Subalgebra.add_mem _ hx hy⟩ : ↥(Algebra.adjoin C T)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, map_add]
      exact Subring.add_mem _ ihx ihy
  | mul x y hx hy ihx ihy =>
      have : (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ : ↥(Algebra.adjoin C T)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul]
      exact Subring.mul_mem _ ihx ihy

theorem exists_residue_transport {A W : Type*} [CommRing A] [IsLocalRing A] [CommRing W] [IsLocalRing W]
    (σ : A →+* W) (hsurj : ∀ w : W, ∃ a : A, w - σ a ∈ maximalIdeal W)
    (hcomap : Ideal.comap σ (maximalIdeal W) = maximalIdeal A) :
    ∃ tW : W →+* ResidueField A, (∀ a : A, tW (σ a) = residue A a) ∧
      (∀ w : W, w ∈ maximalIdeal W → tW w = 0) := by
  let g : A →+* ResidueField W := (residue W).comp σ
  have hg0 : ∀ a : A, a ∈ maximalIdeal A → g a = 0 := by
    intro a ha
    rw [← hcomap, Ideal.mem_comap] at ha
    show residue W (σ a) = 0
    exact (residue_eq_zero_iff _).mpr ha
  let e₀ : ResidueField A →+* ResidueField W := Ideal.Quotient.lift (maximalIdeal A) g hg0
  have he₀ : ∀ a : A, e₀ (residue A a) = residue W (σ a) := fun a => rfl
  have hinj : Function.Injective e₀ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : residue W (σ a) = 0 := hx
    rw [residue_eq_zero_iff, ← Ideal.mem_comap, hcomap] at hx'
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx'
  have hsurj' : Function.Surjective e₀ := by
    intro w
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨a, ha⟩ := hsurj w
    refine ⟨residue A a, ?_⟩
    rw [he₀]
    show Ideal.Quotient.mk (maximalIdeal W) (σ a) = Ideal.Quotient.mk (maximalIdeal W) w
    rw [Ideal.Quotient.eq]
    have : σ a - w = -(w - σ a) := by ring
    rw [this]
    exact (maximalIdeal W).neg_mem ha
  let e : ResidueField A ≃+* ResidueField W := RingEquiv.ofBijective e₀ ⟨hinj, hsurj'⟩
  have he : ∀ a : A, e (residue A a) = residue W (σ a) := fun a => rfl
  refine ⟨e.symm.toRingHom.comp (residue W), fun a => ?_, fun w hw => ?_⟩
  · show e.symm (residue W (σ a)) = residue A a
    rw [← he, RingEquiv.symm_apply_apply]
  · show e.symm (residue W w) = 0
    rw [(residue_eq_zero_iff w).mpr hw, map_zero]

end K4Phi

theorem K4Phi.mem_nonZeroDivisors_of_flat {C S : Type*} [CommRing C] [IsDomain C] [CommRing S] (Ψ : C →+* S)
    (hflat : letI : Algebra C S := Ψ.toAlgebra; Module.Flat C S) (t : C) (ht : t ≠ 0) :
    Ψ t ∈ nonZeroDivisors S := by
  letI : Algebra C S := Ψ.toAlgebra
  haveI : Module.Flat C S := hflat
  have hreg : IsSMulRegular S t :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ht)
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  have h1 : t • x = t • (0 : S) := by
    rw [smul_zero, Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
    exact hx
  exact hreg h1

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})

    (ϖt : A) (hϖt : ∃ u : A, IsUnit u ∧ ϖt ^ (q ^ 2 - 1) = (q : A) * u)

    (y : Ideal ↥(chartAlgFin A (↥K) j)) (hy : y.IsMaximal) (hϖy : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K) j) →+* Ω), RingHom.ker φ = y → φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)

    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
        (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
        (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
        (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
        (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y'.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (hy'y : y'.asIdeal = y)
      (W₁ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁]
        [IsAdicComplete (IsLocalRing.maximalIdeal W₁) W₁] (σ₁ : A →+* W₁)
        (hσ₁ : IsLocalRing.maximalIdeal W₁ = Ideal.span {σ₁ ϖ})
        (f₁ u₁ v₁ : MvPowerSeries (Fin 2) W₁) (hu₁ : IsUnit u₁) (hv₁ : IsUnit v₁)
        (hf₁ : f₁ - DrinfeldCurve.LocalChart.drinfeldForm q W₁ ∈
          (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ (q + 2))
        (e₁ : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
          MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
    (J : Ideal ↥(chartAlgFin A (↥K) j))
    (B : Subalgebra A ↥K)
    (hB : B = (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A)
    (hCB : chartAlgFin A (↥K) j ≤ B)

    (hbridge :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY)) (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) = y ∧

        (∀ (n : ℕ) (s : S), ∃ a : ↥(chartAlgFin A (↥K) j), ((e₁ : CMP →+* S).comp (toC.comp germY)) a - s ∈ (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ n) ∧

        (∀ a : A, ((e₁ : CMP →+* S).comp (toC.comp germY)) (algebraMap A ↥(chartAlgFin A (↥K) j) a) = mkS (MvPowerSeries.C (σ₁ a))) ∧

        (∀ c : ↥(chartAlgFin A (↥K) j), ∃ a : A, c - algebraMap A ↥(chartAlgFin A (↥K) j) a ∈ y) ∧
        (∀ w : W₁, ∃ a : A, w - σ₁ a ∈ IsLocalRing.maximalIdeal W₁) ∧
        Ideal.comap σ₁ (IsLocalRing.maximalIdeal W₁) = IsLocalRing.maximalIdeal A ∧

        (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}).IsMaximal ∧ (∀ I : Ideal S, I.IsMaximal → I = Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ∧

        (letI : Algebra ↥(chartAlgFin A (↥K) j) S := (((e₁ : CMP →+* S).comp (toC.comp germY))).toAlgebra
         Module.Flat ↥(chartAlgFin A (↥K) j) S))

    (hcentre :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        Ideal.map ((e₁ : CMP →+* S).comp (toC.comp germY)) J = Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} ∧

        (∃ I : Ideal ↥(chartAlgFin A (↥K) j),
            J = Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY)) (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ⊓ I ∧ I ⊔ y = ⊤) ∧
        J ≤ y ∧ algebraMap A ↥(chartAlgFin A (↥K) j) ϖt ∈ J)
    (inst : Algebra (GaloisField q 2) (ResidueField A)) :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
        let Lloc := Localization.Away (mkS (MvPowerSeries.C (σ₁ ϖt)))
        let ιS : S →+* Lloc := algebraMap S Lloc
        let x₀ : Lloc := ιS (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt)))
        let x₁ : Lloc := ιS (mkS (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt)))
        let Rloc : Subring Lloc := Subring.closure (Set.range ιS ∪ {x₀, x₁})
        ∃ (Φ : ↥B →+* Lloc) (hιR : ∀ s : S, ιS s ∈ Rloc) (hx₀ : x₀ ∈ Rloc) (hx₁ : x₁ ∈ Rloc) (hΦR : ∀ b : ↥B, Φ b ∈ Rloc),

          (∀ a : ↥(chartAlgFin A (↥K) j), Φ ⟨(a : ↥K), hCB a.2⟩ = ιS (((e₁ : CMP →+* S).comp (toC.comp germY)) a)) ∧
          (∀ (x : ↥B) (i : ↥(chartAlgFin A (↥K) j)), i ∈ J → (x : ↥K) * algebraMap A ↥K ϖt = (i : ↥K) →
              Φ x * ιS (mkS (MvPowerSeries.C (σ₁ ϖt))) = ιS (((e₁ : CMP →+* S).comp (toC.comp germY)) i)) ∧

          σ₁ ϖt ≠ 0 ∧ mkS (MvPowerSeries.C (σ₁ ϖt)) ∈ nonZeroDivisors S := by
  intro STK CMP toC S mkS germY Lloc ιS x₀ x₁ Rloc
  classical
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ↥(chartAlgFin A (↥K) j) →+* S, Ψ = (e₁ : CMP →+* S).comp (toC.comp germY) := ⟨_, rfl⟩
  rw [← hΨ]
  have hb := hbridge
  obtain ⟨-, -, hconst, -, -, -, hmax, -, hflat⟩ := hb
  have hconst' : ∀ a : A, Ψ (algebraMap A ↥(chartAlgFin A (↥K) j) a) = mkS (MvPowerSeries.C (σ₁ a)) := by
    rw [hΨ]; exact hconst
  have hc := hcentre
  obtain ⟨hmapJ, -, -, -⟩ := hc
  have hmapJ' : Ideal.map Ψ J = Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} := by
    rw [hΨ]; exact hmapJ

  have hqp : q.Prime := Fact.out
  have hq0 : (q : A) ≠ 0 := by
    intro h
    have hL : (q : L) = 0 := by
      have := congrArg (algebraMap A L) h
      simpa using this
    exact (Nat.cast_ne_zero.mpr hqp.ne_zero) hL
  have hϖt0 : ϖt ≠ 0 := by
    rintro rfl
    obtain ⟨u, hu, h⟩ := hϖt
    have hpos : q ^ 2 - 1 ≠ 0 := by
      have h2 := hqp.two_le
      have : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h2 2
      omega
    rw [zero_pow hpos] at h
    exact hq0 ((hu.mul_left_eq_zero).mp h.symm)
  have hinjAK : Function.Injective (algebraMap A ↥K) := by
    rw [IsScalarTower.algebraMap_eq A L ↥K]
    exact (algebraMap L ↥K).injective.comp (IsFractionRing.injective A L)
  have hAK : ∀ a : A, algebraMap ↥(chartAlgFin A (↥K) j) ↥K (algebraMap A ↥(chartAlgFin A (↥K) j) a) = algebraMap A ↥K a :=
    fun a => (IsScalarTower.algebraMap_apply A ↥(chartAlgFin A (↥K) j) ↥K a).symm
  have hinj : Function.Injective (algebraMap ↥(chartAlgFin A (↥K) j) ↥K) := fun a b h => Subtype.ext h
  have hϖtC0 : algebraMap A ↥(chartAlgFin A (↥K) j) ϖt ≠ 0 := by
    intro h
    apply hϖt0
    apply hinjAK
    rw [← hAK, h, map_zero, map_zero]

  have hflat' : (letI : Algebra ↥(chartAlgFin A (↥K) j) S := Ψ.toAlgebra; Module.Flat ↥(chartAlgFin A (↥K) j) S) := by
    rw [hΨ]; exact hflat
  have hnzd : mkS (MvPowerSeries.C (σ₁ ϖt)) ∈ nonZeroDivisors S := by
    have h := K4Phi.mem_nonZeroDivisors_of_flat Ψ hflat' (algebraMap A ↥(chartAlgFin A (↥K) j) ϖt) hϖtC0
    rw [hconst' ϖt] at h
    exact h
  have hnz : σ₁ ϖt ≠ 0 := by
    intro h0
    have hz : mkS (MvPowerSeries.C (σ₁ ϖt)) = 0 := by rw [h0, map_zero, map_zero]
    have h1 : (1 : S) = 0 := (mem_nonZeroDivisors_iff_right.mp hnzd) 1 (by rw [hz, mul_zero])
    exact hmax.ne_top ((Ideal.eq_top_iff_one _).mpr (by rw [h1]; exact zero_mem _))

  have hT : ∀ x ∈ {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)},
      ∃ i : ↥(chartAlgFin A (↥K) j), x * algebraMap ↥(chartAlgFin A (↥K) j) ↥K (algebraMap A ↥(chartAlgFin A (↥K) j) ϖt) = algebraMap ↥(chartAlgFin A (↥K) j) ↥K i := by
    rintro x ⟨i, hi, hx⟩
    exact ⟨i, by rw [hAK]; exact hx⟩
  have hT2 : ∀ x ∈ {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)},
      ∃ i : ↥(chartAlgFin A (↥K) j), Ψ i ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} ∧
        x * algebraMap ↥(chartAlgFin A (↥K) j) ↥K (algebraMap A ↥(chartAlgFin A (↥K) j) ϖt) = algebraMap ↥(chartAlgFin A (↥K) j) ↥K i := by
    rintro x ⟨i, hi, hx⟩
    refine ⟨i, ?_, by rw [hAK]; exact hx⟩
    rw [← hmapJ']
    exact Ideal.mem_map_of_mem Ψ hi
  have hgen := K4Phi.exists_ringHom_adjoin hinj (algebraMap A ↥(chartAlgFin A (↥K) j) ϖt) hϖtC0
    {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)} hT Ψ (mkS (MvPowerSeries.C (σ₁ ϖt)))
    (hconst' ϖt) (L := Lloc)
  obtain ⟨Φ₀, hΦ₀1, hΦ₀2⟩ := hgen
  have hcl := K4Phi.mem_closure_of_forall (algebraMap A ↥(chartAlgFin A (↥K) j) ϖt)
    {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)} Ψ (mkS (MvPowerSeries.C (σ₁ ϖt))) (L := Lloc)
    (mkS (MvPowerSeries.X 0)) (mkS (MvPowerSeries.X 1)) hT2 Φ₀ hΦ₀1 hΦ₀2

  have hBmem : ∀ b : ↥B, (b : ↥K) ∈ Algebra.adjoin ↥(chartAlgFin A (↥K) j) {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)} := by
    intro b
    have hb2 : (b : ↥K) ∈ (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A :=
      (le_of_eq hB) b.2
    exact (Subalgebra.mem_restrictScalars (R := A)).mp hb2
  let ιB : ↥B →+* ↥(Algebra.adjoin ↥(chartAlgFin A (↥K) j) {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}) :=
    { toFun := fun b => ⟨(b : ↥K), hBmem b⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hιB : ∀ b : ↥B, ((ιB b : ↥(Algebra.adjoin ↥(chartAlgFin A (↥K) j) {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)})) : ↥K) = (b : ↥K) :=
    fun b => rfl
  refine ⟨Φ₀.comp ιB, fun s => Subring.subset_closure (Or.inl ⟨s, rfl⟩),
    Subring.subset_closure (Or.inr (Or.inl rfl)), Subring.subset_closure (Or.inr (Or.inr rfl)),
    fun b => hcl (ιB b), ?_, ?_, hnz, hnzd⟩
  · intro a
    have heq : ιB ⟨(a : ↥K), hCB a.2⟩ =
        algebraMap ↥(chartAlgFin A (↥K) j) ↥(Algebra.adjoin ↥(chartAlgFin A (↥K) j) {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}) a :=
      Subtype.ext rfl
    rw [RingHom.comp_apply, heq]
    exact hΦ₀1 a
  · intro x i hi hx
    rw [RingHom.comp_apply]
    exact hΦ₀2 (ιB x) i (by rw [hιB, hAK]; exact hx)

end S_ModularCurve_FullLevel_AuxLevelOne_exists_blowupChart_ringHom_away_extends_chartMap_of_eq_adjoin_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_blowupChart_ringHom_away_extends_chartMap_of_eq_adjoin_of_dvd (solution)
