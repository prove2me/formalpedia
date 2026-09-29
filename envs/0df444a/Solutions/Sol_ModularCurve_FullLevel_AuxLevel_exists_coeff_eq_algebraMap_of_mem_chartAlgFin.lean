-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.exists_coeff_eq_algebraMap_of_mem_chartAlgFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/1e4e8285-4781-5412-96ac-9931c40e1313

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_coeff_eq_algebraMap_of_mem_chartAlgFin

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry

open scoped MatrixGroups

namespace CoefInt

theorem isIntegralElem_of_comp {S T F : Type} [CommRing S] [CommRing T] [CommRing F]
    (f : S →+* F) (g : T →+* F) (e : S →+* T) (he : g.comp e = f) (x : F)
    (hx : f.IsIntegralElem x) : g.IsIntegralElem x := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map e, hp.map e, ?_⟩
  rw [Polynomial.eval₂_map, he]; exact hpx

theorem exists_eq_of_isIntegral_of_mul_eq {R F : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field F]
    [Algebra R F] (hinj : Function.Injective (algebraMap R F))
    (x : F) (a b : R) (hb : b ≠ 0) (hx : x * algebraMap R F b = algebraMap R F a)
    (hint : IsIntegral R x) : ∃ r : R, algebraMap R F r = x := by
  let Kf := FractionRing R
  let ψ : Kf →ₐ[R] F := IsFractionRing.liftAlgHom (g := Algebra.ofId R F) hinj
  have hψ : ∀ r : R, ψ (algebraMap R Kf r) = algebraMap R F r := fun r => by
    show IsFractionRing.lift hinj (algebraMap R Kf r) = _
    rw [IsFractionRing.lift_algebraMap]
  have hψinj : Function.Injective ψ := ψ.toRingHom.injective
  have hb' : algebraMap R Kf b ≠ 0 := fun h0 => hb (IsFractionRing.injective R Kf (by rw [h0, map_zero]))
  have hbF : algebraMap R F b ≠ 0 := fun h0 => hb (hinj (by rw [h0, map_zero]))
  set z : Kf := algebraMap R Kf a / algebraMap R Kf b with hz
  have hψz : ψ z = x := by
    rw [hz, map_div₀, hψ, hψ, ← hx, mul_div_cancel_right₀ _ hbF]
  have hzint : IsIntegral R z := by
    rw [← isIntegral_algHom_iff ψ hψinj, hψz]; exact hint
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hzint
  exact ⟨r, by rw [← hψz, ← hr, hψ]⟩

theorem coeffMap_ofPowerSeries {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (p : PowerSeries R) :
    ModularCurve.coeffMap f (HahnSeries.ofPowerSeries ℤ R p) = HahnSeries.ofPowerSeries ℤ S (p.map f) := by
  ext n
  rw [ModularCurve.coeffMap_coeff]
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · have h0 : ∀ {T : Type} [CommRing T] (x : PowerSeries T), (HahnSeries.ofPowerSeries ℤ T x).coeff n = 0 := by
      intro T _ x
      rw [HahnSeries.ofPowerSeries_apply]
      apply HahnSeries.embDomain_notin_range
      rintro ⟨m, hm⟩
      simp only [Nat.castOrderEmbedding_apply] at hm
      omega
    rw [h0, h0, map_zero]

theorem coeffMap_injective {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) : Function.Injective (ModularCurve.coeffMap f) := by
  intro x y h
  ext n
  apply hf
  have := congrArg (fun s => HahnSeries.coeff s n) h
  simpa [ModularCurve.coeffMap_coeff] using this

end CoefInt

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
 :
    ∀ (x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) (n : ℤ), ∃ m : A, ((x : ↥K) : LaurentSeries L).coeff n = algebraMap A L m := by
  intro x n
  classical

  let φ : LaurentSeries A →+* LaurentSeries L := ModularCurve.coeffMap (algebraMap A L)
  have hφinj : Function.Injective φ := CoefInt.coeffMap_injective _ (IsFractionRing.injective A L)
  suffices hmain : ∃ r : LaurentSeries A, φ r = ((x : ↥K) : LaurentSeries L) by
    obtain ⟨r, hr⟩ := hmain
    exact ⟨r.coeff n, by rw [← hr]; exact ModularCurve.coeffMap_coeff _ _ _⟩

  haveI : IsIntegrallyClosed (LaurentSeries A) :=
    isIntegrallyClosed_of_isLocalization (R := PowerSeries A) (LaurentSeries A) (Submonoid.powers (PowerSeries.X : PowerSeries A))
      (powers_le_nonZeroDivisors_of_noZeroDivisors PowerSeries.X_ne_zero)

  letI algφ : Algebra (LaurentSeries A) (LaurentSeries L) := φ.toAlgebra
  have halgφ : algebraMap (LaurentSeries A) (LaurentSeries L) = φ := rfl

  obtain ⟨W₀, hW₀, -, -, -, -⟩ := ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
    (CohCarrier.GammaH ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M')) L K hK A j hj
  have hquot : ∃ a b : LaurentSeries A, b ≠ 0 ∧ ((x : ↥K) : LaurentSeries L) * φ b = φ a := by
    have hne : ∀ s : PowerSeries A, s.map (IsLocalRing.residue A) ≠ 0 → HahnSeries.ofPowerSeries ℤ A s ≠ 0 := by
      intro s hs h0
      apply hs
      have : s = 0 := HahnSeries.ofPowerSeries_injective (by rw [h0, map_zero])
      rw [this, map_zero]
    rcases W₀.mem_or_inv_mem (x : ↥K) with hx | hx
    · obtain ⟨p, s, hs, he⟩ := (hW₀ _).mp hx
      refine ⟨HahnSeries.ofPowerSeries ℤ A p, HahnSeries.ofPowerSeries ℤ A s, hne s hs, ?_⟩
      rw [CoefInt.coeffMap_ofPowerSeries, CoefInt.coeffMap_ofPowerSeries]; exact he
    · by_cases hx0 : ((x : ↥K) : LaurentSeries L) = 0
      · exact ⟨0, 1, one_ne_zero, by rw [hx0, zero_mul, map_zero]⟩
      obtain ⟨p, s, hs, he⟩ := (hW₀ _).mp hx
      have he' : ((x : ↥K) : LaurentSeries L)⁻¹ * HahnSeries.ofPowerSeries ℤ L (s.map (algebraMap A L)) =
          HahnSeries.ofPowerSeries ℤ L (p.map (algebraMap A L)) := by
        simpa using he
      refine ⟨HahnSeries.ofPowerSeries ℤ A s, HahnSeries.ofPowerSeries ℤ A p, ?_, ?_⟩
      · intro hp0
        apply hne s hs
        apply hφinj
        rw [map_zero, CoefInt.coeffMap_ofPowerSeries]
        have : HahnSeries.ofPowerSeries ℤ L (p.map (algebraMap A L)) = 0 := by
          rw [← CoefInt.coeffMap_ofPowerSeries, hp0, map_zero]
        rw [this, mul_eq_zero] at he'
        rcases he' with h | h
        · exact absurd (inv_eq_zero.mp h) hx0
        · exact h
      · rw [CoefInt.coeffMap_ofPowerSeries, CoefInt.coeffMap_ofPowerSeries, ← he', ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
  obtain ⟨a, b, hb, hab⟩ := hquot

  let jA : LaurentSeries A := ModularCurve.jqModC A
  have hφjA : φ jA = ((j : ↥K) : LaurentSeries L) := by
    rw [hj]
    show (ModularCurve.jqModC A).map (algebraMap A L) = ModularCurve.coeffEmb L ModularCurve.jq
    rw [ModularCurve.map_jqModC, ← ModularCurve.jqModC_rat, ModularCurve.coeffEmb]
    show ModularCurve.jqModC L = (ModularCurve.jqModC ℚ).map (algebraMap ℚ L)
    rw [ModularCurve.map_jqModC]

  let ι : ↥K →+* LaurentSeries L := algebraMap ↥K (LaurentSeries L)
  have hιapply : ∀ k : ↥K, ι k = (k : LaurentSeries L) := fun _ => rfl
  have hx_int : (algebraMap ↥(Algebra.adjoin A {j}) ↥K).IsIntegralElem (x : ↥K) := x.2

  have hrange_sub : ∀ s : ↥(Algebra.adjoin A {j}), ∃ r : LaurentSeries A, φ r = ι (s : ↥K) := by
    intro s
    obtain ⟨s, hs⟩ := s
    induction hs using Algebra.adjoin_induction with
    | mem y hy =>
        rw [Set.mem_singleton_iff] at hy; subst hy
        exact ⟨jA, hφjA⟩
    | algebraMap r =>
        refine ⟨HahnSeries.C r, ?_⟩
        show ModularCurve.coeffMap (algebraMap A L) (HahnSeries.single 0 r) = ((algebraMap A ↥K r : ↥K) : LaurentSeries L)
        rw [ModularCurve.coeffMap_single, IsScalarTower.algebraMap_apply A L ↥K]
        exact (ModularCurve.algebraMap_laurentSeries_eq_single L (algebraMap A L r)).symm
    | add y z _ _ hy hz =>
        obtain ⟨r₁, h₁⟩ := hy; obtain ⟨r₂, h₂⟩ := hz
        exact ⟨r₁ + r₂, by rw [map_add, h₁, h₂]; rfl⟩
    | mul y z _ _ hy hz =>
        obtain ⟨r₁, h₁⟩ := hy; obtain ⟨r₂, h₂⟩ := hz
        exact ⟨r₁ * r₂, by rw [map_mul, h₁, h₂]; rfl⟩
  choose θf hθf using hrange_sub
  let θ : ↥(Algebra.adjoin A {j}) →+* LaurentSeries A :=
    { toFun := θf
      map_one' := hφinj (by rw [hθf, map_one]; rfl)
      map_mul' := fun s t => hφinj (by rw [hθf, map_mul, hθf, hθf]; rfl)
      map_zero' := hφinj (by rw [hθf, map_zero]; rfl)
      map_add' := fun s t => hφinj (by rw [hθf, map_add, hθf, hθf]; rfl) }
  have hθ : φ.comp θ = ι.comp (algebraMap ↥(Algebra.adjoin A {j}) ↥K) := RingHom.ext fun s => hθf s
  have hx_int' : (ι.comp (algebraMap ↥(Algebra.adjoin A {j}) ↥K)).IsIntegralElem ((x : ↥K) : LaurentSeries L) := by
    obtain ⟨p, hp, hpx⟩ := hx_int
    refine ⟨p, hp, ?_⟩
    have := congrArg ι hpx
    rw [Polynomial.hom_eval₂, map_zero] at this
    exact this
  have hint : IsIntegral (LaurentSeries A) ((x : ↥K) : LaurentSeries L) :=
    CoefInt.isIntegralElem_of_comp _ φ θ hθ _ hx_int'
  exact CoefInt.exists_eq_of_isIntegral_of_mul_eq (R := LaurentSeries A) (F := LaurentSeries L) hφinj _ a b hb hab hint

end S_ModularCurve_FullLevel_AuxLevel_exists_coeff_eq_algebraMap_of_mem_chartAlgFin
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_coeff_eq_algebraMap_of_mem_chartAlgFin (solution)
