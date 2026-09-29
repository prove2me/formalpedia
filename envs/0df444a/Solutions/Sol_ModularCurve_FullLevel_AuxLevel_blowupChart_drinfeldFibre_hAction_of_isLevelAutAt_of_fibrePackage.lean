-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.blowupChart_drinfeldFibre_hAction_of_isLevelAutAt_of_fibrePackage
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/41646558-0b4a-5439-b31b-2358fbc41c3b

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
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
import Theorems.Thm_CongruenceSubgroup_exists_mem_Gamma_mem_Gamma0_mul_inv_mem_Gamma_of_not_dvd
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_levelAut_eq_one_of_map_eq_one_or_eq_neg_one_of_exists_ringHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_blowupChart_drinfeldFibre_hAction_of_isLevelAutAt_of_fibrePackage
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace BlowupEq

theorem map_mem_span_triple_of_linearPart {S F : Type} [CommRing S] [FunLike F S S] [RingHomClass F S S]
    (θ : F) (a : S) (x : Fin 2 → S)
    (ha : θ a = a) (l : Fin 2 → Fin 2 → S)
    (hlin : ∀ jj : Fin 2, θ (x jj) - ∑ ii : Fin 2, l ii jj * x ii ∈ (Ideal.span {x 0, x 1}) ^ 2) :
    ∀ s : S, s ∈ Ideal.span {a, x 0, x 1} → θ s ∈ Ideal.span {a, x 0, x 1} := by
  classical
  have hsub : Ideal.span ({x 0, x 1} : Set S) ≤ Ideal.span {a, x 0, x 1} :=
    Ideal.span_mono (by intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢; tauto)
  have hx : ∀ jj : Fin 2, θ (x jj) ∈ Ideal.span {a, x 0, x 1} := by
    intro jj
    have h1 : θ (x jj) = (θ (x jj) - ∑ ii : Fin 2, l ii jj * x ii) + ∑ ii : Fin 2, l ii jj * x ii := by ring
    rw [h1]
    refine Ideal.add_mem _ ?_ ?_
    · exact hsub (Ideal.pow_le_self two_ne_zero (hlin jj))
    · refine Ideal.sum_mem _ (fun ii _ => Ideal.mul_mem_left _ _ (hsub (Ideal.subset_span ?_)))
      fin_cases ii <;> simp
  intro s hs
  have : Ideal.map θ (Ideal.span {a, x 0, x 1}) ≤ Ideal.span {a, x 0, x 1} := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨g, hg, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · rw [ha]; exact Ideal.subset_span (by simp)
    · exact hx 0
    · exact hx 1
  exact this (Ideal.mem_map_of_mem θ hs)

theorem map_mem_adjoin_div_of_forall_mem
    {A K F : Type} [CommRing A] [Field K] [Algebra A K] [FunLike F K K] [RingHomClass F K K]
    (C : Subalgebra A K) (J : Ideal ↥C) (t : A)
    (B : Subalgebra A K)
    (hB : B = (Algebra.adjoin ↥C
        {x : K | ∃ i ∈ J, x * algebraMap A K t = ((i : ↥C) : K)}).restrictScalars A)
    (σ : F)
    (hσt : σ (algebraMap A K t) = algebraMap A K t)
    (hσC : ∀ a : K, a ∈ C → σ a ∈ C)
    (hσJ : ∀ (i : ↥C) (hi : σ (i : K) ∈ C), i ∈ J → (⟨σ (i : K), hi⟩ : ↥C) ∈ J) :
    ∀ f : K, f ∈ B → σ f ∈ B := by
  intro f hf
  subst hB
  rw [Subalgebra.mem_restrictScalars] at hf ⊢
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨i, hiJ, hx⟩ := hx
      refine Algebra.subset_adjoin ?_
      refine ⟨⟨σ (i : K), hσC _ i.2⟩, hσJ i _ hiJ, ?_⟩
      simp only
      rw [← hσt, ← map_mul, hx]
  | algebraMap c =>
      have hc : σ ((c : ↥C) : K) ∈ C := hσC _ c.2
      have : σ (algebraMap (↥C) K c) = algebraMap (↥C) K ⟨σ (c : K), hc⟩ := rfl
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy

end BlowupEq

namespace BlowupEqK5

theorem exists_of_mem_span_pair_sq {S : Type} [CommRing S] (a b r : S)
    (hr : r ∈ (Ideal.span {a, b}) ^ 2) :
    ∃ z₁ ∈ Ideal.span {a, b}, ∃ z₂ ∈ Ideal.span {a, b}, r = a * z₁ + b * z₂ := by
  rw [pow_two, Ideal.span_insert, Ideal.sup_mul, Submodule.mem_sup] at hr
  obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := hr
  rw [Ideal.mem_span_singleton_mul] at hr₁ hr₂
  obtain ⟨z₁, hz₁, rfl⟩ := hr₁
  obtain ⟨z₂, hz₂, rfl⟩ := hr₂
  refine ⟨z₁, ?_, z₂, ?_, rfl⟩
  · simpa [Ideal.span_insert] using hz₁
  · simpa [Ideal.span_insert] using hz₂

theorem exists_units_algebraMap_eq_of_pow_eq_one (q : ℕ) [Fact q.Prime] (k : Type) [Field k]
    [Algebra (GaloisField q 2) k] (u : k) (hu : u ^ (q + 1) = 1) :
    ∃ ζ : (GaloisField q 2)ˣ, ζ ∈ rootsOfUnity (q + 1) (GaloisField q 2) ∧
      algebraMap (GaloisField q 2) k (ζ : GaloisField q 2) = u := by
  classical
  haveI : NeZero (q + 1) := ⟨Nat.succ_ne_zero q⟩
  have hu0 : u ≠ 0 := by
    intro h; rw [h, zero_pow (Nat.succ_ne_zero q)] at hu; exact zero_ne_one hu

  set uu : kˣ := Units.mk0 u hu0 with huu
  have huu_mem : uu ∈ rootsOfUnity (q + 1) k := by
    rw [mem_rootsOfUnity]; ext; simp [huu, Units.val_pow_eq_pow_val, hu]

  let f : rootsOfUnity (q + 1) (GaloisField q 2) → rootsOfUnity (q + 1) k :=
    fun ζ => ⟨Units.map (algebraMap (GaloisField q 2) k : GaloisField q 2 →* k) ζ.1, by
      rw [mem_rootsOfUnity]; ext
      have := congrArg (fun x : (GaloisField q 2)ˣ => algebraMap (GaloisField q 2) k (x : GaloisField q 2)) ((mem_rootsOfUnity _ _).mp ζ.2)
      simpa [Units.val_pow_eq_pow_val] using this⟩
  have hf : Function.Injective f := by
    intro ζ₁ ζ₂ h
    apply Subtype.ext; apply Units.ext
    have := congrArg (fun x : rootsOfUnity (q + 1) k => ((x : kˣ) : k)) h
    simpa [f] using this
  classical
  haveI : Fintype (rootsOfUnity (q + 1) (GaloisField q 2)) := Fintype.ofFinite _
  haveI : Fintype (rootsOfUnity (q + 1) k) := Fintype.ofFinite _
  have hcard_src : Fintype.card (rootsOfUnity (q + 1) (GaloisField q 2)) = q + 1 := by
    rw [← Nat.card_eq_fintype_card]; exact DrinfeldCurve.natCard_rootsOfUnity_galoisField_two q
  have hcard_tgt : Fintype.card (rootsOfUnity (q + 1) k) ≤ q + 1 := by
    rw [← Nat.card_eq_fintype_card]; exact card_rootsOfUnity k (q + 1)
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hf, le_antisymm (Fintype.card_le_of_injective f hf) ?_⟩
    rw [hcard_src]; exact hcard_tgt
  obtain ⟨ζ, hζ⟩ := hbij.2 ⟨uu, huu_mem⟩
  refine ⟨ζ.1, ζ.2, ?_⟩
  have := congrArg (fun x : rootsOfUnity (q + 1) k => ((x : kˣ) : k)) hζ
  simpa [f, huu] using this

end BlowupEqK5

namespace BlowupEqK5

open MvPolynomial in
theorem hAction_mk_X (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k]
    (p : ↥(DrinfeldCurve.hSubgroup q)) (jj : Fin 2) :
    DrinfeldCurve.hAction q k p (DrinfeldCurve.mk q k (X jj)) =
      ∑ ii : Fin 2, algebraMap k (DrinfeldCurve.CoordRing q k)
        (DrinfeldCurve.ofZMod q k (((p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 : Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj) *
          DrinfeldCurve.scalarOf q k (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2) *
        DrinfeldCurve.mk q k (X ii) := by
  have hC : ∀ a : k, DrinfeldCurve.mk q k (C a) = algebraMap k (DrinfeldCurve.CoordRing q k) a := by
    intro a; rw [← MvPolynomial.algebraMap_eq]; exact AlgHom.commutes _ a
  rw [DrinfeldCurve.hAction_mk, DrinfeldCurve.substPoly_X, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun ii _ => ?_)
  rw [map_mul, DrinfeldCurve.scalePoly_X, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_eq,
    map_mul, map_mul, hC, hC, map_mul, mul_assoc]

end BlowupEqK5

namespace BlowupEqK5

theorem ringHom_eq_of_eqOn_gens {R T : Type} [Ring R] [Ring T] {s : Set R}
    {f g : ↥(Subring.closure s) →+* T}
    (h : ∀ (x : R) (hx : x ∈ s), f ⟨x, Subring.subset_closure hx⟩ = g ⟨x, Subring.subset_closure hx⟩) : f = g := by
  apply RingHom.ext
  rintro ⟨x, hx⟩
  induction hx using Subring.closure_induction with
  | mem x hx => exact h x hx
  | zero => change f 0 = g 0; rw [map_zero, map_zero]
  | one => change f 1 = g 1; rw [map_one, map_one]
  | add x y hx hy ihx ihy =>
      change f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
      rw [map_add, map_add, ihx, ihy]
  | neg x hx ihx =>
      change f (-⟨x, hx⟩) = g (-⟨x, hx⟩)
      rw [map_neg, map_neg, ihx]
  | mul x y hx hy ihx ihy =>
      change f (⟨x, hx⟩ * ⟨y, hy⟩) = g (⟨x, hx⟩ * ⟨y, hy⟩)
      rw [map_mul, map_mul, ihx, ihy]

end BlowupEqK5

namespace BlowupEqK5

theorem neg_one_entry (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] (ii jj : Fin 2) :
    algebraMap k (DrinfeldCurve.CoordRing q k)
        (DrinfeldCurve.ofZMod q k ((((-1 : Matrix (Fin 2) (Fin 2) ℤ) ii jj) : ℤ) : ZMod q) *
          algebraMap (GaloisField q 2) k ((1 : (GaloisField q 2)ˣ) : GaloisField q 2)) *
        DrinfeldCurve.mk q k (MvPolynomial.X ii) =
      algebraMap k (DrinfeldCurve.CoordRing q k)
        (DrinfeldCurve.ofZMod q k (((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj) *
          algebraMap (GaloisField q 2) k ((-1 : (GaloisField q 2)ˣ) : GaloisField q 2)) *
        DrinfeldCurve.mk q k (MvPolynomial.X ii) := by
  congr 2
  by_cases hij : ii = jj
  · subst hij; simp [Units.val_neg]
  · simp [Matrix.one_apply_ne hij, Units.val_neg]

end BlowupEqK5

set_option maxHeartbeats 32000000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))

    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hξA : ∃ x : A, algebraMap A L x = ξ)
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

    (hW₁ :
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

        (∀ a : A, e₁ (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (σ₁ a))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → γ ∈ CongruenceSubgroup.Gamma ℓ →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) →
                ∃ (θ : S ≃+* S) (c : W₁) (M : Matrix (Fin 2) (Fin 2) W₁),

                  (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                    θ (e₁ (toC (germY a))) = e₁ (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                  (∀ w : W₁, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                  (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                      mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                    (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                  (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W₁) ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧

                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W₁)) ∧

        (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

          (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
          (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₂ →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₁ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₁) →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₂ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₂) →
          ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
            Ideal.comap ((e₁ : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e₁ : CMP →+* S).comp toC) P₂) ∧

        (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C (1 : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W₁) * MvPowerSeries.X 1 + h) ∈ P) →
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            toC (germY a) ∈ Ideal.comap (e₁ : CMP →+* S) P ↔
              ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
                (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

        (∃ (hjK : ModularCurve.jqNModC L (q * ℓ) ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W₁)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W₁, (a ∉ IsLocalRing.maximalIdeal W₁ ∨ b ∉ IsLocalRing.maximalIdeal W₁) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W₁ →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e₁ : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))

    (J : Ideal ↥(chartAlgFin A (↥K) j))
    (hJ :
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
        J = sInf {J' : Ideal ↥(chartAlgFin A (↥K) j) | ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma q)
          (_ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
          (_ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)
          (hpres : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
          J' = Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres)
            (Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY))
              (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}))})

    (B : Subalgebra A ↥K)
    (hB : B = (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A)
    (hCB : chartAlgFin A (↥K) j ≤ B)

    (hK1 :
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

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
              (∀ a : ↥(chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) a : ↥(chartAlgFin A (↥K) j)) - a ∈ y) →
              ∀ a : ↥(chartAlgFin A (↥K) j),
                (e₁ : CMP →+* S) (toC (germY a)) ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} ↔
                (e₁ : CMP →+* S) (toC (germY (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) a))) ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ (a : ↥(chartAlgFin A (↥K) j)) (ha : τ (a : ↥K) ∈ chartAlgFin A (↥K) j),
              a ∈ J ↔ (⟨τ (a : ↥K), ha⟩ : ↥(chartAlgFin A (↥K) j)) ∈ J) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ f : ↥K, f ∈ B → τ f ∈ B))

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
        ∀ (Φ : ↥B →+* Lloc) (hιR : ∀ s : S, ιS s ∈ Rloc) (hx₀ : x₀ ∈ Rloc) (hx₁ : x₁ ∈ Rloc) (hΦR : ∀ b : ↥B, Φ b ∈ Rloc)
          (tW : W₁ →+* ResidueField A) (cR : ResidueField A)
          (ρR : ↥Rloc →+* DrinfeldCurve.CoordRing q (ResidueField A))
          (ρ : ↥B →+* DrinfeldCurve.CoordRing q (ResidueField A)),

          (∀ a : ↥(chartAlgFin A (↥K) j), Φ ⟨(a : ↥K), hCB a.2⟩ = ιS (((e₁ : CMP →+* S).comp (toC.comp germY)) a)) →
          (∀ (x : ↥B) (i : ↥(chartAlgFin A (↥K) j)), i ∈ J → (x : ↥K) * algebraMap A ↥K ϖt = (i : ↥K) →
              Φ x * ιS (mkS (MvPowerSeries.C (σ₁ ϖt))) = ιS (((e₁ : CMP →+* S).comp (toC.comp germY)) i)) →
          (∀ a : A, tW (σ₁ a) = residue A a) → (∀ w : W₁, w ∈ IsLocalRing.maximalIdeal W₁ → tW w = 0) →
          cR ≠ 0 →
          (∀ F : MvPowerSeries (Fin 2) W₁, ρR ⟨ιS (mkS F), hιR (mkS F)⟩ =
              algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (MvPowerSeries.constantCoeff F))) →
          ρR ⟨x₀, hx₀⟩ = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.x q (ResidueField A) →
          ρR ⟨x₁, hx₁⟩ = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.y q (ResidueField A) →
          (∀ b : ↥B, ρ b = ρR ⟨Φ b, hΦR b⟩) →

          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
              (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
                  b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y) →
              ∃ (c : (GaloisField q 2)ˣ) (hmem : (ModularCurve.FullLevel.redQ q γ, c) ∈ DrinfeldCurve.hSubgroup q),
                (∀ (b : ↥B) (hb : τ (b : ↥K) ∈ B), ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρ b)) ∧
                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c ≠ 1) ∧
                (∃ (γ' : SL(2, ℤ)) (_ : γ' ∈ CongruenceSubgroup.Gamma q) (_ : γ' ∈ CongruenceSubgroup.Gamma0 M') (τ' : ↥K ≃ₐ[L] ↥K)
                   (_ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ'⁻¹ K τ')
                   (_ : (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ' (b : ↥K) ∈ chartAlgFin A (↥K) j),
                  b ∈ y ↔ (⟨τ' (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y))
                   (hmem' : ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)), c) ∈ DrinfeldCurve.hSubgroup q),
                   ∀ (b : ↥B) (hb : τ' (b : ↥K) ∈ B), ρ ⟨τ' (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem'⟩ (ρ b))) ∧

          (∃ (γ' : SL(2, ℤ)) (_ : γ' ∈ CongruenceSubgroup.Gamma q) (_ : γ' ∈ CongruenceSubgroup.Gamma0 M') (τ' : ↥K ≃ₐ[L] ↥K)
             (_ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ'⁻¹ K τ')
             (_ : (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ' (b : ↥K) ∈ chartAlgFin A (↥K) j),
                  b ∈ y ↔ (⟨τ' (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y))
             (hmem' : ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)), (-1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q),
             ∀ (b : ↥B) (hb : τ' (b : ↥K) ∈ B), ρ ⟨τ' (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem'⟩ (ρ b)) := by
  intro STK CMP toC S mkS germY Lloc ιS x₀ x₁ Rloc
  intro Φ hιR hx₀ hx₁ hΦR tW cR ρR ρ hΦC hΦJ htW1 htW2 hcR hρRS hρRx0 hρRx1 hρΦ
  classical
  have hW := hW₁
  obtain ⟨-, hfin, hfix, hlin, -, -, -⟩ := hW

  have hCOMP := ModularCurve.FullLevel.AuxLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK
  obtain ⟨hU, hM, hI⟩ := hCOMP
  have hE := ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK
  have hmul : ∀ γ δ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → δ ∈ CongruenceSubgroup.Gamma0 M' → ∀ τ σ : ↥K ≃ₐ[L] ↥K,
      ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ → ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') δ⁻¹ K σ → ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') (γ * δ)⁻¹ K (τ * σ) := by
    intro γ δ hγ hδ τ σ hτ hσ
    have h := hM γ⁻¹ δ⁻¹ (inv_mem hγ) (inv_mem hδ) τ σ hτ hσ
    rw [← mul_inv_rev] at h
    exact h
  have hone : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') (1 : SL(2, ℤ))⁻¹ K 1 := by
    rw [inv_one]; exact hI 1 (one_mem _) (one_mem _)
  have huniq : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ∀ τ τ' : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ → ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ' → τ = τ' :=
    fun γ hγ τ τ' h h' => hU γ⁻¹ (inv_mem hγ) τ τ' h h'
  have hinv : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ → ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹⁻¹ K τ⁻¹ := by
    intro γ hγ τ hτ
    have hex := hE γ⁻¹ (inv_mem hγ)
    obtain ⟨τ', hτ'⟩ := hex
    have h1 := hmul γ⁻¹ γ (inv_mem hγ) hγ τ' τ hτ' hτ
    rw [inv_mul_cancel] at h1
    have h2 : τ' * τ = 1 := huniq 1 (one_mem _) _ _ h1 hone
    have h3 : τ' = τ⁻¹ := eq_inv_of_mul_eq_one_left h2
    rw [← h3]; exact hτ'
  have hK1ii := hK1.2.1
  have hK1iii := hK1.2.2
  have hcenΨ := hbridge.1
  have hconstΨ := hbridge.2.2.1
  have hres := hbridge.2.2.2.1
  have hJgen := hcentre.1

  let ιR : S →+* ↥Rloc := ιS.codRestrict Rloc hιR
  let χS : S →+* DrinfeldCurve.CoordRing q (ResidueField A) := ρR.comp ιR
  have hχS_mk : ∀ F : MvPowerSeries (Fin 2) W₁,
      χS (mkS F) = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (MvPowerSeries.constantCoeff F)) :=
    fun F => hρRS F
  have hχS_M : ∀ s : S, s ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} → χS s = 0 := by
    have hle : Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} ≤ RingHom.ker χS := by
      rw [Ideal.span_le]
      intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rw [SetLike.mem_coe, RingHom.mem_ker]
      rcases hs with rfl | rfl | rfl
      · rw [hχS_mk, MvPowerSeries.constantCoeff_C, htW1]
        have : residue A ϖ = 0 := by
          rw [IsLocalRing.residue_eq_zero_iff, hϖ]; exact Ideal.mem_span_singleton_self ϖ
        rw [this, map_zero]
      · rw [hχS_mk, MvPowerSeries.constantCoeff_X, map_zero, map_zero]
      · rw [hχS_mk, MvPowerSeries.constantCoeff_X, map_zero, map_zero]
    intro s hs; exact hle hs

  have hgeom : ∀ (τ : ↥K ≃ₐ[L] ↥K) (hpres : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
      (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
          b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y) →
      ∀ a : ↥(chartAlgFin A (↥K) j), (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) a : ↥(chartAlgFin A (↥K) j)) - a ∈ y := by
    intro τ hpres hfixy a
    have hra := hres a
    obtain ⟨a₀, ha₀⟩ := hra
    have hA : ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) (algebraMap A ↥(chartAlgFin A (↥K) j) a₀) = algebraMap A ↥(chartAlgFin A (↥K) j) a₀ := by
      apply Subtype.ext
      show τ (((algebraMap A ↥(chartAlgFin A (↥K) j) a₀ : ↥(chartAlgFin A (↥K) j)) : ↥K)) = _
      rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply A L ↥K, AlgEquiv.commutes]
    have h1 : ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) a - a =
        (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) (a - algebraMap A ↥(chartAlgFin A (↥K) j) a₀) - (a - algebraMap A ↥(chartAlgFin A (↥K) j) a₀)) := by
      rw [map_sub, hA]; abel
    rw [h1]
    refine Ideal.sub_mem _ ?_ ha₀
    exact (hfixy (a - algebraMap A ↥(chartAlgFin A (↥K) j) a₀) (hpres _ (a - algebraMap A ↥(chartAlgFin A (↥K) j) a₀).2)).mp ha₀
  have hcore : ∀ (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K) (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)
      (hpres : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j)
      (θ : S ≃+* S) (c : W₁) (M : Matrix (Fin 2) (Fin 2) W₁),
      (∀ a : ↥(chartAlgFin A (↥K) j), θ (e₁ (toC (germY a))) = e₁ (toC (germY (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) a)))) →
      (∀ w : W₁, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) →
      (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) - mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
          (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) →
      ∀ (ζ : (GaloisField q 2)ˣ), algebraMap (GaloisField q 2) (ResidueField A) (ζ : GaloisField q 2) = tW c →
      ∀ (hmem : (ModularCurve.FullLevel.redQ q γ, ζ) ∈ DrinfeldCurve.hSubgroup q),
      (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W₁) ∈ IsLocalRing.maximalIdeal W₁) →
      ∀ (b : ↥B) (hb : τ (b : ↥K) ∈ B), ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρ b) := by
    intro γ hγ τ hτ hpres θ c M hθΨ hθW hθlin ζ hζ hmem hM

    have hunit : IsUnit ((ιS.comp (θ : S →+* S)) (mkS (MvPowerSeries.C (σ₁ ϖt)))) := by
      rw [RingHom.comp_apply]
      have : (θ : S →+* S) (mkS (MvPowerSeries.C (σ₁ ϖt))) = mkS (MvPowerSeries.C (σ₁ ϖt)) := hθW _
      rw [this]
      exact IsLocalization.Away.algebraMap_isUnit (mkS (MvPowerSeries.C (σ₁ ϖt)))
    let θL : Lloc →+* Lloc := IsLocalization.Away.lift (mkS (MvPowerSeries.C (σ₁ ϖt))) hunit
    have hθLι : ∀ s : S, θL (ιS s) = ιS (θ s) := fun s => IsLocalization.Away.lift_eq _ hunit s
    have hθLinv : θL (IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt)))) = IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt))) := by
      have hu : IsUnit (ιS (mkS (MvPowerSeries.C (σ₁ ϖt)))) := IsLocalization.Away.algebraMap_isUnit _
      have h1 : ιS (mkS (MvPowerSeries.C (σ₁ ϖt))) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt))) = 1 := IsLocalization.Away.mul_invSelf _
      have h2 : ιS (mkS (MvPowerSeries.C (σ₁ ϖt))) * θL (IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt)))) = 1 := by
        have h3 : θL (ιS (mkS (MvPowerSeries.C (σ₁ ϖt)))) = ιS (mkS (MvPowerSeries.C (σ₁ ϖt))) := by
          rw [hθLι]; exact congrArg ιS (hθW _)
        rw [← h3, ← map_mul, h1, map_one]
      exact hu.mul_right_injective (h2.trans h1.symm)

    have hθlin' : ∀ jj : Fin 2, θ ((fun i : Fin 2 => mkS (MvPowerSeries.X i)) jj) -
          ∑ ii : Fin 2, (fun i j : Fin 2 => mkS (MvPowerSeries.C (M i j))) ii jj * (fun i : Fin 2 => mkS (MvPowerSeries.X i)) ii ∈
          (Ideal.span {(fun i : Fin 2 => mkS (MvPowerSeries.X i)) 0, (fun i : Fin 2 => mkS (MvPowerSeries.X i)) 1}) ^ 2 := by
      intro jj; have h := hθlin jj; simp only [map_sum, map_mul] at h; exact h
    have hθM : ∀ s : S, s ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} → θ s ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} :=
      BlowupEq.map_mem_span_triple_of_linearPart θ (mkS (MvPowerSeries.C (σ₁ ϖ))) (fun i => mkS (MvPowerSeries.X i))
        (hθW _) (fun i j => mkS (MvPowerSeries.C (M i j))) hθlin'
    have hdense := hbridge.2.1
    have hχθ : ∀ s : S, χS (θ s) = χS s := by
      intro s
      have hda := hdense 1 s
      obtain ⟨a, ha⟩ := hda
      have hra := hres a
      obtain ⟨a₀, ha₀⟩ := hra
      replace ha := Ideal.pow_le_self one_ne_zero ha
      have h1 : s - mkS (MvPowerSeries.C (σ₁ a₀)) ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} := by
        have h2 : ((e₁ : CMP →+* S).comp (toC.comp germY)) (a - algebraMap A ↥(chartAlgFin A (↥K) j) a₀) ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} := by
          have : a - algebraMap A ↥(chartAlgFin A (↥K) j) a₀ ∈ Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY)) (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) := by
            rw [hcenΨ]; exact ha₀
          exact Ideal.mem_comap.mp this
        rw [map_sub, hconstΨ] at h2
        have : s - mkS (MvPowerSeries.C (σ₁ a₀)) =
            (((e₁ : CMP →+* S).comp (toC.comp germY)) a - mkS (MvPowerSeries.C (σ₁ a₀))) - (((e₁ : CMP →+* S).comp (toC.comp germY)) a - s) := by ring
        rw [this]; exact Ideal.sub_mem _ h2 ha
      have e1 : χS s = χS (mkS (MvPowerSeries.C (σ₁ a₀))) := by
        rw [← sub_eq_zero, ← map_sub]; exact hχS_M _ h1
      have e2 : χS (θ s) = χS (mkS (MvPowerSeries.C (σ₁ a₀))) := by
        rw [← sub_eq_zero, ← map_sub, ← hθW (σ₁ a₀), ← map_sub]; exact hχS_M _ (hθM _ h1)
      rw [e1, e2]

    have hBstab := hK1iii γ hγ τ hτ
    let τB : ↥B →+* ↥B := (τ : ↥K →+* ↥K).restrict B B hBstab
    have hτB : ∀ b : ↥B, ((τB b : ↥B) : ↥K) = τ (b : ↥K) := fun b => rfl
    have hBmem : ∀ x : ↥K, x ∈ Algebra.adjoin ↥(chartAlgFin A (↥K) j) {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)} ↔ x ∈ B := by
      intro x; rw [hB, Subalgebra.mem_restrictScalars]
    have hτϖt : τ (algebraMap A ↥K ϖt) = algebraMap A ↥K ϖt := by
      rw [IsScalarTower.algebraMap_apply A L ↥K, AlgEquiv.commutes]
    have hu : IsUnit (ιS (mkS (MvPowerSeries.C (σ₁ ϖt)))) := IsLocalization.Away.algebraMap_isUnit _
    have hPSI : ∀ a : ↥(chartAlgFin A (↥K) j), ((e₁ : CMP →+* S).comp (toC.comp germY)) a = e₁ (toC (germY a)) := fun a => rfl
    have hΦτ : ∀ b : ↥B, Φ (τB b) = θL (Φ b) := by
      suffices h : ∀ x : ↥K, x ∈ Algebra.adjoin ↥(chartAlgFin A (↥K) j) {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)} →
          ∀ hx : x ∈ B, Φ (τB ⟨x, hx⟩) = θL (Φ ⟨x, hx⟩) by
        intro b; exact h b.1 ((hBmem _).mpr b.2) b.2
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem x hxS =>
          intro hxB
          obtain ⟨i, hiJ, hxi⟩ := hxS

          have hi' : (⟨τ ((i : ↥(chartAlgFin A (↥K) j)) : ↥K), hpres _ i.2⟩ : ↥(chartAlgFin A (↥K) j)) ∈ J :=
            (hK1ii γ hγ τ hτ i (hpres _ i.2)).mp hiJ
          have hx'i : ((τB ⟨x, hxB⟩ : ↥B) : ↥K) * algebraMap A ↥K ϖt =
              (((⟨τ ((i : ↥(chartAlgFin A (↥K) j)) : ↥K), hpres _ i.2⟩ : ↥(chartAlgFin A (↥K) j))) : ↥K) := by
            rw [hτB]
            show τ x * algebraMap A ↥K ϖt = τ ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)
            rw [← hxi, map_mul, hτϖt]
          have e1 := hΦJ ⟨x, hxB⟩ i hiJ hxi
          have e2 := hΦJ (τB ⟨x, hxB⟩) _ hi' hx'i

          have e3 : ((e₁ : CMP →+* S).comp (toC.comp germY)) (⟨τ ((i : ↥(chartAlgFin A (↥K) j)) : ↥K), hpres _ i.2⟩ : ↥(chartAlgFin A (↥K) j)) = θ (((e₁ : CMP →+* S).comp (toC.comp germY)) i) := by
            rw [hPSI, hPSI, hθΨ i]
            rfl
          rw [e3, ← hθLι, ← e1, map_mul, hθLι] at e2
          have e4 : θ (mkS (MvPowerSeries.C (σ₁ ϖt))) = mkS (MvPowerSeries.C (σ₁ ϖt)) := hθW _
          rw [e4] at e2
          exact (hu.mul_left_inj).mp e2
      | algebraMap c =>
          intro hxB
          have e1 : Φ ⟨algebraMap ↥(chartAlgFin A (↥K) j) ↥K c, hxB⟩ = ιS (((e₁ : CMP →+* S).comp (toC.comp germY)) c) := hΦC c
          have e2 : Φ (τB ⟨algebraMap ↥(chartAlgFin A (↥K) j) ↥K c, hxB⟩) = ιS (((e₁ : CMP →+* S).comp (toC.comp germY)) (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) c)) := by
            have : τB ⟨algebraMap ↥(chartAlgFin A (↥K) j) ↥K c, hxB⟩ =
                ⟨((((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) c : ↥(chartAlgFin A (↥K) j)) : ↥K), hCB (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) c).2⟩ := by
              apply Subtype.ext; rfl
            rw [this]; exact hΦC _
          rw [e1, e2, hθLι, hPSI, hPSI, hθΨ c]
      | add x y hx hy ihx ihy =>
          intro hxyB
          have hxB : x ∈ B := (hBmem _).mp hx
          have hyB : y ∈ B := (hBmem _).mp hy
          have : (⟨x + y, hxyB⟩ : ↥B) = ⟨x, hxB⟩ + ⟨y, hyB⟩ := rfl
          rw [this]; simp only [map_add]; rw [ihx hxB, ihy hyB]
      | mul x y hx hy ihx ihy =>
          intro hxyB
          have hxB : x ∈ B := (hBmem _).mp hx
          have hyB : y ∈ B := (hBmem _).mp hy
          have : (⟨x * y, hxyB⟩ : ↥B) = ⟨x, hxB⟩ * ⟨y, hyB⟩ := rfl
          rw [this]; simp only [map_mul]; rw [ihx hxB, ihy hyB]

    have hXle : Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} ≤ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} :=
      Ideal.span_mono (by intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢; tauto)
    have hcoef : ∀ jj : Fin 2, ∃ t₀ t₁ : S, θ (mkS (MvPowerSeries.X jj)) = mkS (MvPowerSeries.X 0) * t₀ + mkS (MvPowerSeries.X 1) * t₁ ∧
        χS t₀ = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M 0 jj)) ∧ χS t₁ = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M 1 jj)) := by
      intro jj
      have hsq := BlowupEqK5.exists_of_mem_span_pair_sq (mkS (MvPowerSeries.X 0)) (mkS (MvPowerSeries.X 1)) _ (hθlin jj)
      obtain ⟨z₁, hz₁, z₂, hz₂, hr⟩ := hsq
      refine ⟨mkS (MvPowerSeries.C (M 0 jj)) + z₁, mkS (MvPowerSeries.C (M 1 jj)) + z₂, ?_, ?_, ?_⟩
      · have h2 : θ (mkS (MvPowerSeries.X jj)) = mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) +
            (mkS (MvPowerSeries.X 0) * z₁ + mkS (MvPowerSeries.X 1) * z₂) := by
          rw [← hr]; abel
        rw [h2, map_sum, Fin.sum_univ_two, map_mul, map_mul]
        ring
      · rw [map_add, hχS_mk, MvPowerSeries.constantCoeff_C, hχS_M _ (hXle hz₁), add_zero]
      · rw [map_add, hχS_mk, MvPowerSeries.constantCoeff_C, hχS_M _ (hXle hz₂), add_zero]
    have hcoef0 := hcoef 0
    have hcoef1 := hcoef 1
    obtain ⟨t₀₀, t₁₀, hθX0, hχt₀₀, hχt₁₀⟩ := hcoef0
    obtain ⟨t₀₁, t₁₁, hθX1, hχt₀₁, hχt₁₁⟩ := hcoef1
    have hθLx : ∀ (jj : Fin 2) (t₀ t₁ : S), θ (mkS (MvPowerSeries.X jj)) = mkS (MvPowerSeries.X 0) * t₀ + mkS (MvPowerSeries.X 1) * t₁ →
        θL (ιS (mkS (MvPowerSeries.X jj)) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt)))) = ιS t₀ * x₀ + ιS t₁ * x₁ := by
      intro jj t₀ t₁ h
      rw [map_mul, hθLι, hθLinv, h, map_add, map_mul, map_mul]
      show (ιS (mkS (MvPowerSeries.X 0)) * ιS t₀ + ιS (mkS (MvPowerSeries.X 1)) * ιS t₁) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt))) =
        ιS t₀ * (ιS (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt)))) + ιS t₁ * (ιS (mkS (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt))))
      ring
    have hθLx0 : θL x₀ = ιS t₀₀ * x₀ + ιS t₁₀ * x₁ := hθLx 0 t₀₀ t₁₀ hθX0
    have hθLx1 : θL x₁ = ιS t₀₁ * x₀ + ιS t₁₁ * x₁ := hθLx 1 t₀₁ t₁₁ hθX1

    have hθLR : ∀ r : Lloc, r ∈ Rloc → θL r ∈ Rloc := by
      have hle : Rloc ≤ Subring.comap θL Rloc := by
        show Subring.closure (Set.range ιS ∪ {x₀, x₁}) ≤ _
        rw [Subring.closure_le]
        rintro r (⟨s, rfl⟩ | hr01)
        · show θL (ιS s) ∈ Rloc
          rw [hθLι]; exact hιR _
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr01
          rcases hr01 with rfl | rfl
          · show θL x₀ ∈ Rloc
            rw [hθLx0]
            exact Subring.add_mem _ (Subring.mul_mem _ (hιR _) hx₀) (Subring.mul_mem _ (hιR _) hx₁)
          · show θL x₁ ∈ Rloc
            rw [hθLx1]
            exact Subring.add_mem _ (Subring.mul_mem _ (hιR _) hx₀) (Subring.mul_mem _ (hιR _) hx₁)
      intro r hr; exact hle hr

    have hρRι : ∀ (s : S) (h : ιS s ∈ Rloc), ρR ⟨ιS s, h⟩ = χS s := fun s h => rfl
    have hactC : ∀ t : ResidueField A, DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) t) = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) t := fun t => AlgEquiv.commutes _ t
    have htWM : ∀ ii jj : Fin 2, tW (M ii jj) = tW c * ((γ ii jj : ℤ) : ResidueField A) := by
      intro ii jj
      have h1 : tW (M ii jj - c * ((γ ii jj : ℤ) : W₁)) = 0 := htW2 _ (hM ii jj)
      rw [map_sub, sub_eq_zero, map_mul, map_intCast] at h1
      exact h1
    have hred : ∀ ii jj : Fin 2,
        (((ModularCurve.FullLevel.redQ q γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj)
          = ((γ ii jj : ℤ) : ZMod q) := fun ii jj => rfl
    have hactx : ∀ jj : Fin 2, DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (DrinfeldCurve.mk q (ResidueField A) (MvPolynomial.X jj)) = ∑ ii : Fin 2, algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M ii jj)) * DrinfeldCurve.mk q (ResidueField A) (MvPolynomial.X ii) := by
      intro jj
      rw [BlowupEqK5.hAction_mk_X]
      refine Finset.sum_congr rfl (fun ii _ => ?_)
      show algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (DrinfeldCurve.ofZMod q (ResidueField A)
          ((((ModularCurve.FullLevel.redQ q γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj)) *
          algebraMap (GaloisField q 2) (ResidueField A) (ζ : GaloisField q 2)) * DrinfeldCurve.mk q (ResidueField A) (MvPolynomial.X ii) = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M ii jj)) * DrinfeldCurve.mk q (ResidueField A) (MvPolynomial.X ii)
      rw [hred, map_intCast, hζ, htWM, mul_comm (tW c)]

    have hρx0 : DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.x q (ResidueField A)) =
        algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M 0 0)) * (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.x q (ResidueField A)) + algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M 1 0)) * (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.y q (ResidueField A)) := by
      show DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.mk q (ResidueField A) (MvPolynomial.X 0)) =
        algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M 0 0)) * (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.mk q (ResidueField A) (MvPolynomial.X 0)) + algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M 1 0)) * (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.mk q (ResidueField A) (MvPolynomial.X 1))
      rw [map_mul, hactC, hactx, Fin.sum_univ_two]; ring
    have hρx1 : DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.y q (ResidueField A)) =
        algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M 0 1)) * (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.x q (ResidueField A)) + algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M 1 1)) * (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.y q (ResidueField A)) := by
      show DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.mk q (ResidueField A) (MvPolynomial.X 1)) =
        algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M 0 1)) * (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.mk q (ResidueField A) (MvPolynomial.X 0)) + algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M 1 1)) * (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.mk q (ResidueField A) (MvPolynomial.X 1))
      rw [map_mul, hactC, hactx, Fin.sum_univ_two]; ring

    let θR : ↥Rloc →+* ↥Rloc := θL.restrict Rloc Rloc hθLR
    let G₁ : ↥Rloc →+* DrinfeldCurve.CoordRing q (ResidueField A) := ρR.comp θR
    let G₂ : ↥Rloc →+* DrinfeldCurve.CoordRing q (ResidueField A) :=
      (DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩).toAlgHom.toRingHom.comp ρR
    have hG₁ : ∀ (r : Lloc) (hr : r ∈ Rloc), G₁ ⟨r, hr⟩ = ρR ⟨θL r, hθLR r hr⟩ := fun r hr => rfl
    have hG₂ : ∀ (r : Lloc) (hr : r ∈ Rloc), G₂ ⟨r, hr⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρR ⟨r, hr⟩) := fun r hr => rfl
    have hG : G₁ = G₂ := by
      apply BlowupEqK5.ringHom_eq_of_eqOn_gens
      intro r hr
      rw [hG₁, hG₂]
      rcases hr with ⟨s, rfl⟩ | hr01
      · have e1 : (⟨θL (ιS s), hθLR _ (Subring.subset_closure (Or.inl ⟨s, rfl⟩))⟩ : ↥Rloc) = ⟨ιS (θ s), hιR _⟩ :=
          Subtype.ext (hθLι s)
        rw [e1, hρRι, hρRι, hχθ]
        have hF := Ideal.Quotient.mk_surjective s
        obtain ⟨F, rfl⟩ := hF
        have e5 : χS (Ideal.Quotient.mk _ F) = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (MvPowerSeries.constantCoeff F)) := hχS_mk F
        rw [e5, hactC]
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr01
        rcases hr01 with rfl | rfl
        · have e1 : (⟨θL x₀, hθLR _ (Subring.subset_closure (Or.inr (by simp)))⟩ : ↥Rloc) =
              ιR t₀₀ * ⟨x₀, hx₀⟩ + ιR t₁₀ * ⟨x₁, hx₁⟩ := Subtype.ext hθLx0
          have e2 : (⟨x₀, Subring.subset_closure (Or.inr (by simp))⟩ : ↥Rloc) = ⟨x₀, hx₀⟩ := rfl
          rw [e1, e2, map_add, map_mul, map_mul]
          show χS t₀₀ * ρR ⟨x₀, hx₀⟩ + χS t₁₀ * ρR ⟨x₁, hx₁⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρR ⟨x₀, hx₀⟩)
          rw [hρRx0, hρRx1, hρx0, hχt₀₀, hχt₁₀]
        · have e1 : (⟨θL x₁, hθLR _ (Subring.subset_closure (Or.inr (by simp)))⟩ : ↥Rloc) =
              ιR t₀₁ * ⟨x₀, hx₀⟩ + ιR t₁₁ * ⟨x₁, hx₁⟩ := Subtype.ext hθLx1
          have e2 : (⟨x₁, Subring.subset_closure (Or.inr (by simp))⟩ : ↥Rloc) = ⟨x₁, hx₁⟩ := rfl
          rw [e1, e2, map_add, map_mul, map_mul]
          show χS t₀₁ * ρR ⟨x₀, hx₀⟩ + χS t₁₁ * ρR ⟨x₁, hx₁⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρR ⟨x₁, hx₁⟩)
          rw [hρRx0, hρRx1, hρx1, hχt₀₁, hχt₁₁]

    intro b hb
    have e2 : (⟨Φ (τB b), hΦR (τB b)⟩ : ↥Rloc) = ⟨θL (Φ b), hθLR _ (hΦR b)⟩ := Subtype.ext (hΦτ b)
    calc ρ ⟨τ (b : ↥K), hb⟩ = ρ (τB b) := rfl
      _ = ρR ⟨Φ (τB b), hΦR (τB b)⟩ := hρΦ _
      _ = ρR ⟨θL (Φ b), hθLR _ (hΦR b)⟩ := by rw [e2]
      _ = G₁ ⟨Φ b, hΦR b⟩ := (hG₁ _ _).symm
      _ = G₂ ⟨Φ b, hΦR b⟩ := by rw [hG]
      _ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρR ⟨Φ b, hΦR b⟩) := hG₂ _ _
      _ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρ b) := by rw [hρΦ]

  have hζof : ∀ c : W₁, c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W₁ →
      ∃ ζ : (GaloisField q 2)ˣ, ζ ∈ rootsOfUnity (q + 1) (GaloisField q 2) ∧
        algebraMap (GaloisField q 2) (ResidueField A) (ζ : GaloisField q 2) = tW c := by
    intro c hc
    have h1 : tW c ^ (q + 1) = 1 := by
      have := htW2 _ hc
      rw [map_sub, map_pow, map_one, sub_eq_zero] at this
      exact this
    exact BlowupEqK5.exists_units_algebraMap_eq_of_pow_eq_one q (ResidueField A) (tW c) h1

  have hmemof : ∀ (γ : SL(2, ℤ)) (ζ : (GaloisField q 2)ˣ), ζ ∈ rootsOfUnity (q + 1) (GaloisField q 2) →
      (ModularCurve.FullLevel.redQ q γ, ζ) ∈ DrinfeldCurve.hSubgroup q := by
    intro γ ζ hζ
    rw [DrinfeldCurve.mem_hSubgroup_iff, Units.ext_iff, DrinfeldCurve.coe_hChar_apply, Units.val_one]
    have hdet : (((ModularCurve.FullLevel.redQ q γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q))).det = 1 :=
      Matrix.SpecialLinearGroup.det_coe (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ)
    have hζ' : ((ζ : (GaloisField q 2)ˣ) : GaloisField q 2) ^ (q + 1) = 1 := by
      rw [mem_rootsOfUnity] at hζ
      rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
    show algebraMap (ZMod q) (GaloisField q 2) (((ModularCurve.FullLevel.redQ q γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q))).det *
      ((ζ : (GaloisField q 2)ˣ) : GaloisField q 2) ^ (q + 1) = 1
    rw [hdet, hζ', map_one, one_mul]

  have htWker : ∀ w : W₁, tW w = 0 → w ∈ IsLocalRing.maximalIdeal W₁ := by
    intro w hw
    by_contra hwu
    have hu : IsUnit w := by
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hwu
    exact (hu.map tW).ne_zero hw

  have hfix_of_geom : ∀ (τ : ↥K ≃ₐ[L] ↥K) (hpres : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
      (∀ a : ↥(chartAlgFin A (↥K) j), (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) a : ↥(chartAlgFin A (↥K) j)) - a ∈ y) →
      ∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
        b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y := by
    intro τ hpres hg b hb
    have e : (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) = b + (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) b - b) := by
      apply Subtype.ext; show τ (b : ↥K) = (b : ↥K) + (τ (b : ↥K) - (b : ↥K)); ring
    rw [e]
    constructor
    · intro h; exact Ideal.add_mem _ h (hg b)
    · intro h; have := Ideal.sub_mem _ h (hg b); rwa [add_sub_cancel_right] at this

  have hmain : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
        (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
            b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y) →
        ∃ (c : (GaloisField q 2)ˣ) (hmem : (ModularCurve.FullLevel.redQ q γ, c) ∈ DrinfeldCurve.hSubgroup q),
          (∀ (b : ↥B) (hb : τ (b : ↥K) ∈ B), ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρ b)) ∧
          (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c ≠ 1) ∧
          (∃ (γ' : SL(2, ℤ)) (_ : γ' ∈ CongruenceSubgroup.Gamma q) (_ : γ' ∈ CongruenceSubgroup.Gamma0 M') (τ' : ↥K ≃ₐ[L] ↥K)
             (_ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') γ'⁻¹ K τ')
             (_ : (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ' (b : ↥K) ∈ chartAlgFin A (↥K) j),
                  b ∈ y ↔ (⟨τ' (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y))
             (hmem' : ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)), c) ∈ DrinfeldCurve.hSubgroup q),
             ∀ (b : ↥B) (hb : τ' (b : ↥K) ∈ B), ρ ⟨τ' (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem'⟩ (ρ b)) := by
    intro γ hγ τ hτ hfixy
    have hpres := hfin γ hγ τ hτ
    have hg := hgeom τ hpres hfixy
    have hg' : ∀ a : ↥(chartAlgFin A (↥K) j), (((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres) a : ↥(chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal := by
      rw [hy'y]; exact hg
    have hl := hlin γ hγ τ hτ hpres hg'
    obtain ⟨θ, c, M, hθΨ, hθW, hθlin, hcpow, hM, hcℓ, hfaithW⟩ := hl
    have hz := hζof c hcpow
    obtain ⟨ζ, hζμ, hζ⟩ := hz
    have hmem := hmemof γ ζ hζμ
    have hequiv := hcore γ hγ τ hτ hpres θ c M hθΨ hθW hθlin ζ hζ hmem hM
    refine ⟨ζ, hmem, hequiv, ?_, ?_⟩
    · intro hγq hτne hζ1
      apply hfaithW hγq hτne
      apply htWker
      rw [map_sub, map_one, ← hζ, hζ1, Units.val_one, map_one, sub_self]
    ·
      have hK0 := CongruenceSubgroup.exists_mem_Gamma_mem_Gamma0_mul_inv_mem_Gamma_of_not_dvd q M' hqM' ℓ hℓq γ
      obtain ⟨δ, hδℓ, hδ0, hγδ, -⟩ := hK0
      have hexδ := hE δ hδ0
      obtain ⟨τδ, hτδ⟩ := hexδ
      have hpresδ := hfin δ hδ0 τδ hτδ
      have hgδ : ∀ a : ↥(chartAlgFin A (↥K) j), (((τδ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpresδ) a : ↥(chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal :=
        hfix δ hδ0 hδℓ τδ hτδ hpresδ
      have hgδy : ∀ a : ↥(chartAlgFin A (↥K) j), (((τδ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpresδ) a : ↥(chartAlgFin A (↥K) j)) - a ∈ y := by
        rw [← hy'y]; exact hgδ
      have hlδ := hlin δ hδ0 τδ hτδ hpresδ hgδ
      obtain ⟨θδ, cδ, Mδ, hθΨδ, hθWδ, hθlinδ, -, hMδ, hcℓδ, -⟩ := hlδ
      have hcδ1 : tW cδ = 1 := by
        have := htW2 _ (hcℓδ hδℓ)
        rw [map_sub, map_one, sub_eq_zero] at this
        exact this
      have hmemδ : (ModularCurve.FullLevel.redQ q δ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q :=
        hmemof δ 1 (one_mem _)
      have hequivδ := hcore δ hδ0 τδ hτδ hpresδ θδ cδ Mδ hθΨδ hθWδ hθlinδ 1
        (by rw [Units.val_one, map_one, hcδ1]) hmemδ hMδ
      have hτδinv := hinv δ hδ0 τδ hτδ
      have hτ' := hmul γ δ⁻¹ hγ (inv_mem hδ0) τ τδ⁻¹ hτ hτδinv
      have hfixδ := hfix_of_geom τδ hpresδ hgδy
      have hpresδ' := hfin δ⁻¹ (inv_mem hδ0) τδ⁻¹ hτδinv
      have hmem' : ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)), ζ) ∈ DrinfeldCurve.hSubgroup q :=
        DrinfeldCurve.one_mem_hSubgroup_of_mem q ⟨ζ, hζμ⟩
      refine ⟨γ * δ⁻¹, hγδ, mul_mem hγ (inv_mem hδ0), τ * τδ⁻¹, hτ', ?_, hmem', ?_⟩
      · intro b hb
        have hb1 : τδ⁻¹ (b : ↥K) ∈ chartAlgFin A (↥K) j := hpresδ' _ b.2
        have e1 : (τ * τδ⁻¹) (b : ↥K) = τ (τδ⁻¹ (b : ↥K)) := AlgEquiv.mul_apply _ _ _
        have hb0 : τδ (τδ⁻¹ (b : ↥K)) ∈ chartAlgFin A (↥K) j := by
          rw [show τδ (τδ⁻¹ (b : ↥K)) = (b : ↥K) from τδ.apply_symm_apply _]; exact b.2
        have h1 : b ∈ y ↔ (⟨τδ⁻¹ (b : ↥K), hb1⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y := by
          have h2 := hfixδ ⟨τδ⁻¹ (b : ↥K), hb1⟩ hb0
          have e3 : (⟨τδ (τδ⁻¹ (b : ↥K)), hb0⟩ : ↥(chartAlgFin A (↥K) j)) = b := by
            apply Subtype.ext; exact τδ.apply_symm_apply _
          rw [e3] at h2
          exact h2.symm
        rw [h1]
        have hb2 : τ (τδ⁻¹ (b : ↥K)) ∈ chartAlgFin A (↥K) j := hpres _ hb1
        have h3 := hfixy ⟨τδ⁻¹ (b : ↥K), hb1⟩ hb2
        rw [h3]
        have e5 : (⟨(τ * τδ⁻¹) (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) = ⟨τ (τδ⁻¹ (b : ↥K)), hb2⟩ := Subtype.ext e1
        rw [e5]
      · intro b hb
        have hb1 : τδ⁻¹ (b : ↥K) ∈ B := hK1iii δ⁻¹ (inv_mem hδ0) τδ⁻¹ hτδinv _ b.2
        have hb2 : τ (τδ⁻¹ (b : ↥K)) ∈ B := by
          have := hb; rwa [AlgEquiv.mul_apply] at this
        have e1 : (⟨(τ * τδ⁻¹) (b : ↥K), hb⟩ : ↥B) = ⟨τ (τδ⁻¹ (b : ↥K)), hb2⟩ := Subtype.ext (AlgEquiv.mul_apply _ _ _)
        rw [e1, hequiv ⟨τδ⁻¹ (b : ↥K), hb1⟩ hb2]

        have hb3 : τδ (((⟨τδ⁻¹ (b : ↥K), hb1⟩ : ↥B)) : ↥K) ∈ B := by
          show τδ (τδ⁻¹ (b : ↥K)) ∈ B
          rw [show τδ (τδ⁻¹ (b : ↥K)) = (b : ↥K) from τδ.apply_symm_apply _]; exact b.2
        have e2 := hequivδ ⟨τδ⁻¹ (b : ↥K), hb1⟩ hb3
        have e3 : (⟨τδ (((⟨τδ⁻¹ (b : ↥K), hb1⟩ : ↥B)) : ↥K), hb3⟩ : ↥B) = b := by
          apply Subtype.ext; exact τδ.apply_symm_apply _
        rw [e3] at e2

        have e4 : ρ ⟨τδ⁻¹ (b : ↥K), hb1⟩ = (DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmemδ⟩).symm (ρ b) := by
          rw [e2, AlgEquiv.symm_apply_apply]
        rw [e4, ← AlgEquiv.aut_inv, ← AlgEquiv.mul_apply, ← map_inv, ← map_mul]
        congr 2
        apply Subtype.ext
        show (ModularCurve.FullLevel.redQ q γ, ζ) * (ModularCurve.FullLevel.redQ q δ, (1 : (GaloisField q 2)ˣ))⁻¹ = ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)), ζ)
        rw [Prod.inv_mk, Prod.mk_mul_mk, inv_one, mul_one, ← map_inv, ← map_mul]
        congr 1
        have : γ * δ⁻¹ ∈ CongruenceSubgroup.Gamma q := hγδ
        rw [CongruenceSubgroup.Gamma_mem'] at this
        show Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) (γ * δ⁻¹)) = 1
        rw [this, map_one]
  refine ⟨hmain, ?_⟩
  ·
    have hneg1_0 : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 M' := by
      rw [CongruenceSubgroup.Gamma0_mem]
      simp [Matrix.SpecialLinearGroup.coe_neg]
    have hK0n := CongruenceSubgroup.exists_mem_Gamma_mem_Gamma0_mul_inv_mem_Gamma_of_not_dvd q M' hqM' ℓ hℓq (-1)
    obtain ⟨δ, hδℓ, hδ0, hnδ, -⟩ := hK0n
    have hγm0 : (-1) * δ⁻¹ ∈ CongruenceSubgroup.Gamma0 M' := mul_mem hneg1_0 (inv_mem hδ0)

    have hexn := hE (-1) hneg1_0
    obtain ⟨τn, hτn⟩ := hexn
    have hmapneg : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (q * ℓ))) (-1 : SL(2, ℤ)) = -1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one, Matrix.SpecialLinearGroup.coe_one, map_neg, map_one]
    have hτn1 : τn = 1 := ModularCurve.FullLevel.AuxLevel.levelAut_eq_one_of_map_eq_one_or_eq_neg_one_of_exists_ringHom q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK (-1) hneg1_0 (Or.inr hmapneg) τn hτn

    have hexδ := hE δ hδ0
    obtain ⟨τδ, hτδ⟩ := hexδ
    have hσ' := hinv δ hδ0 τδ hτδ
    have hσ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M') ((-1) * δ⁻¹)⁻¹ K τδ⁻¹ := by
      have := hmul (-1) δ⁻¹ hneg1_0 (inv_mem hδ0) τn τδ⁻¹ hτn hσ'
      rwa [hτn1, one_mul] at this
    have hpresσ := hfin δ⁻¹ (inv_mem hδ0) τδ⁻¹ hσ'
    have hgσ : ∀ a : ↥(chartAlgFin A (↥K) j), ((((τδ⁻¹ : ↥K ≃ₐ[L] ↥K) : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpresσ) a : ↥(chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal :=
      hfix δ⁻¹ (inv_mem hδ0) (inv_mem hδℓ) τδ⁻¹ hσ' hpresσ
    have hgσy : ∀ a : ↥(chartAlgFin A (↥K) j), ((((τδ⁻¹ : ↥K ≃ₐ[L] ↥K) : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpresσ) a : ↥(chartAlgFin A (↥K) j)) - a ∈ y := by
      rw [← hy'y]; exact hgσ
    have hlσ := hlin δ⁻¹ (inv_mem hδ0) τδ⁻¹ hσ' hpresσ hgσ
    obtain ⟨θσ, cσ, Mσ, hθΨσ, hθWσ, hθlinσ, -, hMσ, hcℓσ, -⟩ := hlσ
    have hcσ1 : tW cσ = 1 := by
      have := htW2 _ (hcℓσ (inv_mem hδℓ))
      rw [map_sub, map_one, sub_eq_zero] at this
      exact this
    have hmemσ : (ModularCurve.FullLevel.redQ q δ⁻¹, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q :=
      hmemof δ⁻¹ 1 (one_mem _)
    have hequivσ := hcore δ⁻¹ (inv_mem hδ0) τδ⁻¹ hσ' hpresσ θσ cσ Mσ hθΨσ hθWσ hθlinσ 1
      (by rw [Units.val_one, map_one, hcσ1]) hmemσ hMσ

    have hq2 : q ≠ 2 := by omega
    have hqodd : Odd q := (Fact.out : q.Prime).odd_of_ne_two hq2
    have hneg1μ : (-1 : (GaloisField q 2)ˣ) ∈ rootsOfUnity (q + 1) (GaloisField q 2) := by
      rw [mem_rootsOfUnity]
      exact (hqodd.add_one).neg_one_pow
    have hmem' : ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)), (-1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q :=
      DrinfeldCurve.one_mem_hSubgroup_of_mem q ⟨-1, hneg1μ⟩

    have hred1 : ModularCurve.FullLevel.redQ q δ⁻¹ = ModularCurve.FullLevel.redQ q (-1) := by
      have h1 : (-1) * δ⁻¹ ∈ CongruenceSubgroup.Gamma q := hnδ
      rw [CongruenceSubgroup.Gamma_mem', map_mul] at h1
      have h2 : ModularCurve.FullLevel.redQ q ((-1) * δ⁻¹) = 1 := by
        show Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) ((-1) * δ⁻¹)) = 1
        rw [map_mul, h1, map_one]
      rw [map_mul] at h2
      have h3 : ModularCurve.FullLevel.redQ q δ⁻¹ = (ModularCurve.FullLevel.redQ q (-1))⁻¹ := eq_inv_of_mul_eq_one_right h2
      rw [h3, ← map_inv]
      congr 1
      rw [inv_eq_iff_mul_eq_one, neg_mul_neg, one_mul]

    have hredn : ∀ ii jj : Fin 2,
        (((ModularCurve.FullLevel.redQ q (-1) : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj)
          = (((-1 : SL(2, ℤ)) ii jj : ℤ) : ZMod q) := fun ii jj => rfl
    have hactEq : ∀ z : DrinfeldCurve.CoordRing q (ResidueField A),
        DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmemσ⟩ z = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem'⟩ z := by
      have h : ((DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmemσ⟩ : DrinfeldCurve.CoordRing q (ResidueField A) ≃ₐ[ResidueField A] DrinfeldCurve.CoordRing q (ResidueField A)) :
            DrinfeldCurve.CoordRing q (ResidueField A) →ₐ[ResidueField A] DrinfeldCurve.CoordRing q (ResidueField A)) =
          (DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem'⟩ : DrinfeldCurve.CoordRing q (ResidueField A) →ₐ[ResidueField A] DrinfeldCurve.CoordRing q (ResidueField A)) := by
        apply DrinfeldCurve.algHom_ext
        apply MvPolynomial.algHom_ext
        intro jj
        show DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmemσ⟩ (DrinfeldCurve.mk q (ResidueField A) (MvPolynomial.X jj)) = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem'⟩ (DrinfeldCurve.mk q (ResidueField A) (MvPolynomial.X jj))
        rw [BlowupEqK5.hAction_mk_X, BlowupEqK5.hAction_mk_X]
        refine Finset.sum_congr rfl (fun ii _ => ?_)
        show algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (DrinfeldCurve.ofZMod q (ResidueField A)
            ((((ModularCurve.FullLevel.redQ q δ⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod q))) : Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj) *
            algebraMap (GaloisField q 2) (ResidueField A) ((1 : (GaloisField q 2)ˣ) : GaloisField q 2)) * DrinfeldCurve.mk q (ResidueField A) (MvPolynomial.X ii) =
          algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (DrinfeldCurve.ofZMod q (ResidueField A) (((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj) *
            algebraMap (GaloisField q 2) (ResidueField A) ((-1 : (GaloisField q 2)ˣ) : GaloisField q 2)) * DrinfeldCurve.mk q (ResidueField A) (MvPolynomial.X ii)
        rw [hred1, hredn, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
        exact BlowupEqK5.neg_one_entry q (ResidueField A) ii jj
      intro z
      exact congrArg (fun f : DrinfeldCurve.CoordRing q (ResidueField A) →ₐ[ResidueField A] DrinfeldCurve.CoordRing q (ResidueField A) => f z) h
    refine ⟨(-1) * δ⁻¹, hnδ, hγm0, τδ⁻¹, hσ, hfix_of_geom τδ⁻¹ hpresσ hgσy, hmem', ?_⟩
    intro b hb
    rw [hequivσ b hb, hactEq]

end S_ModularCurve_FullLevel_AuxLevel_blowupChart_drinfeldFibre_hAction_of_isLevelAutAt_of_fibrePackage
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_blowupChart_drinfeldFibre_hAction_of_isLevelAutAt_of_fibrePackage (solution)
