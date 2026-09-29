-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.mem_maximalIdeal_iff_mem_span_image_of_blowupChart_exceptionalValuation_of_isPrime_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/ab20a420-408c-591a-930c-5623ba24c676

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

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_mem_maximalIdeal_iff_mem_span_image_of_blowupChart_exceptionalValuation_of_isPrime_of_dvd

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace BlowupEq

theorem mem_of_mem_maximalIdeal_of_isPrime_of_le
    {A K : Type} [CommRing A] [Field K] [Algebra A K]
    (B : Subalgebra A K) (W : ValuationSubring K) (hBW : ∀ f : K, f ∈ B → f ∈ W)
    (hdvr : IsDiscreteValuationRing ↥W)
    (ϖ : ↥B) (hϖ : maximalIdeal ↥W = Ideal.span {(⟨(ϖ : K), hBW _ ϖ.2⟩ : ↥W)})
    (hloc : ∀ f : K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : K), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : K) = (g : K))
    (P : Ideal ↥B) (hP : P.IsPrime)
    (hPle : ∀ b : ↥B, b ∈ P → (⟨(b : K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W)
    (p : ↥B) (hpP : p ∈ P) (hp0 : (p : K) ≠ 0) :
    ∀ b : ↥B, (⟨(b : K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W → b ∈ P := by
  classical
  intro b hb
  haveI := hdvr

  set ϖW : ↥W := ⟨(ϖ : K), hBW _ ϖ.2⟩ with hϖW
  have hirr : Irreducible ϖW := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖW).mpr hϖ

  set pW : ↥W := ⟨(p : K), hBW _ p.2⟩ with hpW
  have hpW0 : pW ≠ 0 := by
    intro h; apply hp0; have := congrArg (fun x : ↥W => (x : K)) h; simpa [hpW] using this
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hpW0 hirr

  set bW : ↥W := ⟨(b : K), hBW _ b.2⟩ with hbW
  rw [hϖ, Ideal.mem_span_singleton'] at hb
  obtain ⟨c, hc⟩ := hb

  have hbn : bW ^ n = pW * ((u : ↥W) * c ^ n) := by
    rw [← hc, mul_pow, mul_comm (c ^ n), ← hu]; ring

  obtain ⟨g, h, hh, hgh⟩ := (hloc (((u : ↥W) * c ^ n : ↥W) : K)).mp (((u : ↥W) * c ^ n)).2

  have hK : ((b : K)) ^ n * (h : K) = (p : K) * (g : K) := by
    have h1 : ((bW ^ n : ↥W) : K) = ((pW : ↥W) : K) * ((((u : ↥W) * c ^ n : ↥W)) : K) := by
      rw [hbn]; rfl
    have h2 : ((bW ^ n : ↥W) : K) = (b : K) ^ n := by simp [hbW]
    rw [← h2, h1, mul_assoc, hgh]

  have hB : b ^ n * h = p * g := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow]
    exact hK
  have hmem : b ^ n * h ∈ P := by rw [hB]; exact P.mul_mem_right _ hpP
  have hhP : h ∉ P := fun hhP => hh (hPle h hhP)
  have hbnP : b ^ n ∈ P := ((hP.mem_or_mem hmem).resolve_right hhP)
  exact hP.mem_of_pow_mem n hbnP

end BlowupEq

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
    (J : Ideal ↥(chartAlgFin A (↥K) j))
    (B : Subalgebra A ↥K)
    (hB : B = (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A)

    (W : ValuationSubring ↥K) (hBW : ∀ f : ↥K, f ∈ B → f ∈ W)
    (hR1 :

      chartAlgFin A (↥K) j ≤ B ∧
      (∀ f : ↥K, ∃ g h : ↥B, (h : ↥K) ≠ 0 ∧ f * (h : ↥K) = (g : ↥K)))
    (hR2 :

      Algebra.FormallySmooth A ↥B ∧ Algebra.FinitePresentation A ↥B ∧
      Ring.KrullDimLE 1 (↥B ⧸ Ideal.span {algebraMap A ↥B ϖ}))
    (hR3 :

      (∀ x : L, algebraMap L ↥K x ∈ W ↔ ∃ a : A, algebraMap A L a = x) ∧
      maximalIdeal ↥W = Ideal.span {(⟨algebraMap A ↥K ϖ, hBW _ (B.algebraMap_mem ϖ)⟩ : ↥W)} ∧
      IsDiscreteValuationRing ↥W ∧
      (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y ↔
        ∃ hb : (b : ↥K) ∈ W, (⟨(b : ↥K), hb⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
      (∀ f : ↥K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : ↥K), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : ↥K) = (g : ↥K)))

    (hprime : (Ideal.span ((fun c : ↥(chartAlgFin A (↥K) j) => (⟨(c : ↥K), hR1.1 c.2⟩ : ↥B)) '' (y : Set ↥(chartAlgFin A (↥K) j)))).IsPrime) :

      (∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W ↔
          b ∈ Ideal.span ((fun c : ↥(chartAlgFin A (↥K) j) => (⟨(c : ↥K), hR1.1 c.2⟩ : ↥B)) '' (y : Set ↥(chartAlgFin A (↥K) j)))) ∧

      (∀ Q : Ideal ↥B, Q.IsPrime → algebraMap A ↥B ϖ ∈ Q →
        (∀ b : ↥(chartAlgFin A (↥K) j), (⟨(b : ↥K), hR1.1 b.2⟩ : ↥B) ∈ Q ↔ b ∈ y) →
        ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W → b ∈ Q) := by
  classical

  let ι : ↥B →+* ↥W :=
    { toFun := fun b => ⟨(b : ↥K), hBW _ b.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hι : ∀ b : ↥B, ι b = ⟨(b : ↥K), hBW _ b.2⟩ := fun b => rfl
  obtain ⟨-, hmax, hdvr, hcen, hloc⟩ := hR3
  set yB : Ideal ↥B := Ideal.span ((fun c : ↥(chartAlgFin A (↥K) j) => (⟨(c : ↥K), hR1.1 c.2⟩ : ↥B)) '' (y : Set ↥(chartAlgFin A (↥K) j))) with hyB

  have ha : ∀ b : ↥B, b ∈ yB → (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W := by
    intro b hb
    have hle : yB ≤ Ideal.comap ι (maximalIdeal ↥W) := by
      rw [hyB, Ideal.span_le]
      rintro _ ⟨c, hc, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, hι]
      obtain ⟨hcW, hcm⟩ := (hcen c).mp hc
      exact hcm
    have := hle hb
    rw [Ideal.mem_comap, hι] at this
    exact this

  set ϖB : ↥B := algebraMap A ↥B ϖ with hϖB
  have hϖB_mem : ϖB ∈ yB := by
    rw [hyB]
    refine Ideal.subset_span ⟨algebraMap A ↥(chartAlgFin A (↥K) j) ϖ, hϖy, ?_⟩
    apply Subtype.ext
    simp [hϖB, Subalgebra.coe_algebraMap]
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    apply IsDiscreteValuationRing.not_a_field A
    rw [hϖ, h, Ideal.span_singleton_eq_bot]
  have hϖK : ((ϖB : ↥B) : ↥K) ≠ 0 := by
    rw [hϖB, Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply A L ↥K]
    intro h
    rw [map_eq_zero] at h
    exact hϖ0 ((IsFractionRing.injective A L) (by rw [h, map_zero]))

  have hmax' : maximalIdeal ↥W = Ideal.span {(⟨((ϖB : ↥B) : ↥K), hBW _ ϖB.2⟩ : ↥W)} := by
    rw [hmax]
    congr 2

  have hb : ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W → b ∈ yB :=
    BlowupEq.mem_of_mem_maximalIdeal_of_isPrime_of_le B W hBW hdvr ϖB hmax' hloc yB hprime ha ϖB hϖB_mem hϖK
  refine ⟨fun b => ⟨hb b, ha b⟩, ?_⟩

  intro Q hQ hϖQ hQy b hbm
  have hbyB := hb b hbm
  have hle : yB ≤ Q := by
    rw [hyB, Ideal.span_le]
    rintro _ ⟨c, hc, rfl⟩
    exact (hQy c).mpr hc
  exact hle hbyB

end S_ModularCurve_FullLevel_AuxLevelOne_mem_maximalIdeal_iff_mem_span_image_of_blowupChart_exceptionalValuation_of_isPrime_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_mem_maximalIdeal_iff_mem_span_image_of_blowupChart_exceptionalValuation_of_isPrime_of_dvd (solution)
