-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.mem_and_hasValue_nodeResidueFst_of_hasValue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/737b6e53-19b9-5100-a3ad-bf5929d6d8e7

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_and_hasValue_nodeResidueFst_of_hasValue
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace FltWs21
namespace Val

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

section Generic
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem hasValue_sub_algebraMap (W : Place K F) (f : F) (b c : K) (hb : W.HasValue f b) :
    W.HasValue (f - algebraMap K F c) (b - c) := by
  obtain ⟨hmem, hres⟩ := hb
  refine ⟨sub_mem hmem (W.algebraMap_mem' c), ?_⟩
  have : (⟨f - algebraMap K F c, sub_mem hmem (W.algebraMap_mem' c)⟩ : W.toValuationSubring)
      = ⟨f, hmem⟩ - algebraMap K W.toValuationSubring c := by
    apply Subtype.ext; simp [AlgebraicCurve.Place.coe_algebraMap]
  rw [this, map_sub, hres, AlgebraicCurve.Place.residue_algebraMap, map_sub]

theorem hasValue_add_algebraMap (W : Place K F) (f : F) (b c : K) (hb : W.HasValue f b) :
    W.HasValue (f + algebraMap K F c) (b + c) := by
  have h := hasValue_sub_algebraMap W f b (-c) hb
  rwa [map_neg, sub_neg_eq_add, sub_neg_eq_add] at h

theorem ord_pos_of_hasValue_zero (W : Place K F) {f : F} (h : W.HasValue f 0) (hf : f ≠ 0) : 0 < W.ord f := by
  obtain ⟨hm, hr⟩ := h
  have h0 : 0 ≤ W.ord f := W.ord_nonneg_of_mem hm
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm', hu⟩ := W.exists_isUnit_of_ord_eq_zero hf heq.symm
    have hres : IsLocalRing.residue W.toValuationSubring ⟨f, hm'⟩ = 0 := by
      have e : (⟨f, hm'⟩ : W.toValuationSubring) = ⟨f, hm⟩ := rfl
      rw [e, hr, map_zero]
    exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu) hres

end Generic

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

theorem ι_algebraMap (R : ProlongationTuple P) (x : ResidueField A) :
    R.ι (algebraMap (ResidueField A) (↥(modularFunctionFieldFullC (ResidueField A) N)) x)
      = algebraMap k (↥(modularFunctionFieldC k N)) (R.redBar x) := by
  apply Subtype.ext
  rw [R.ι_coe]
  change coeffMap R.redBar (algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) x)
    = algebraMap k (LaurentSeries k) (R.redBar x)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem residue₁_const (R : ProlongationTuple P) (a : A) (h : algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers) :
    (R.residue₁ ⟨algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ), h⟩ : ↥(modularFunctionFieldC k N)) = algebraMap k (↥(modularFunctionFieldC k N)) (red a) := by
  have e : (⟨algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ), h⟩ : R.R₁.integers)
      = ⟨algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ), (R.R₁.algebraMap_mem_iff _).mpr a.2⟩ := rfl
  rw [ProlongationTuple.residue₁_apply, e, R.R₁.residue_algebraMap a, ι_algebraMap, R.redBar_residue]

theorem residue₂_const (R : ProlongationTuple P) (a : A) (h : algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers) :
    (R.residue₂ ⟨algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ), h⟩ : ↥(modularFunctionFieldC k N)) = algebraMap k (↥(modularFunctionFieldC k N)) (red a) := by
  have e : (⟨algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ), h⟩ : R.R₂.integers)
      = ⟨algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ), (R.R₂.algebraMap_mem_iff _).mpr a.2⟩ := rfl
  rw [ProlongationTuple.residue₂_apply, e, R.R₂.residue_algebraMap a, ι_algebraMap, R.redBar_residue]

theorem common_value_eq_zero (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q)))]
    (hord : R.OrderLawFixed)
    (W : Finset (Place k (↥(modularFunctionFieldC k N)))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (w : Place k (↥(modularFunctionFieldC k N))) (hw : w ∈ W)
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w)
    (h : ↥(modularFunctionFieldBar (N * q))) (hh : h ∈ R.nodeIntegers w)
    (V : Place (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q)))) (hV : P.reduceFst V = w) (hV0 : 0 < V.ord h)
    (cval : k) (hc₁ : w.HasValue (R.residue₁ ⟨h, hh.1⟩ : ↥(modularFunctionFieldC k N)) cval)
    (hc₂ : (arithFrobC q k N • w).HasValue (R.residue₂ ⟨h, hh.2.1⟩ : ↥(modularFunctionFieldC k N)) cval) :
    cval = 0 := by
  classical
  by_contra hne
  have hne₁ : (R.residue₁ ⟨h, hh.1⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := hc₁.ne_zero hne
  have hne₂ : (R.residue₂ ⟨h, hh.2.1⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := hc₂.ne_zero hne
  have hr₁ : R.R₁.residue ⟨h, hh.1⟩ ≠ 0 := by
    intro h0; apply hne₁; rw [ProlongationTuple.residue₁_apply, h0, map_zero]
  have hr₂ : R.R₂.residue ⟨h, hh.2.1⟩ ≠ 0 := by
    intro h0; apply hne₂; rw [ProlongationTuple.residue₂_apply, h0, map_zero]
  have hh0 : h ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hV0
    exact lt_irrefl _ hV0
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) h hh0
  have haff : IsAffineGeomPlace k N w := (hW w hw).2.1
  have hlaw := hord h hh.1 hh.2.1 hr₁ hr₂ D hD w hfix haff
  have ho₁ : w.ord (R.residue₁ ⟨h, hh.1⟩ : ↥(modularFunctionFieldC k N)) = 0 := hc₁.ord_eq_zero hne
  have ho₂ : (frobOnPlacesGeomLevel k N data hKr w).ord (R.residue₂ ⟨h, hh.2.1⟩ : ↥(modularFunctionFieldC k N)) = 0 := by
    rw [← arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr w]
    exact hc₂.ord_eq_zero hne
  rw [ho₁, ho₂, add_zero] at hlaw

  have hVsupp : V ∈ D.support := Finsupp.mem_support_iff.mpr (by rw [hD]; exact hV0.ne')
  have hsum : Finsupp.mapDomain P.reduceFst D w = ∑ V' ∈ D.support, (Finsupp.single (P.reduceFst V') (D V')) w := by
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  have hterm : ∀ V' ∈ D.support, 0 ≤ (Finsupp.single (P.reduceFst V') (D V')) w := by
    intro V' _
    rw [Finsupp.single_apply]
    split_ifs with hV'
    · rw [hD]; exact R.ord_nonneg_of_mem_nodeIntegers hh hV'
    · exact le_rfl
  have hVterm : (Finsupp.single (P.reduceFst V) (D V)) w = D V := by rw [hV, Finsupp.single_eq_same]
  have hpos : 0 < Finsupp.mapDomain P.reduceFst D w := by
    rw [hsum, ← Finset.add_sum_erase _ _ hVsupp, hVterm]
    have h2 : 0 ≤ ∑ V' ∈ D.support.erase V, (Finsupp.single (P.reduceFst V') (D V')) w :=
      Finset.sum_nonneg fun V' hV' => hterm V' (Finset.mem_of_mem_erase hV')
    have h3 : 0 < D V := by rw [hD]; exact hV0
    omega
  omega

end FltWs21.Val

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))]
    (hord : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w)
    (f : ↥(modularFunctionFieldBar (N * q))) (hf : f ∈ R.nodeIntegers w)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w)
    (c : AlgebraicClosure ℚ) (hc : V.HasValue f c) :
    ∃ hcA : c ∈ A, w.HasValue (R.nodeResidue₁ w ⟨f, hf⟩ : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩) := by
  classical
  haveI : PerfectField k := inferInstance
  have hs : smulNodePair (arithFrobC q k N) w ∈ nodePairsOfPlaces (arithFrobC q k N) W :=
    smulNodePair_mem_nodePairsOfPlaces _ hw

  have hnode : ∀ (g : ↥(modularFunctionFieldBar (N * q))) (hg : g ∈ R.nodeIntegers w), ∃ cv : k,
      w.HasValue (R.residue₁ ⟨g, hg.1⟩ : ↥(modularFunctionFieldC k N)) cv ∧
      (arithFrobC q k N • w).HasValue (R.residue₂ ⟨g, hg.2.1⟩ : ↥(modularFunctionFieldC k N)) cv := by
    intro g hg
    exact hreg.2 g hg.1 hg.2.1 _ hs (fun V' hV' => R.ord_nonneg_of_mem_nodeIntegers hg hV')

  have hcA : c ∈ A := by
    by_contra hcA
    have hc0 : c ≠ 0 := fun h0 => hcA (h0 ▸ A.zero_mem)
    have hcinv : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
    set a : A := ⟨c⁻¹, hcinv⟩ with ha
    have hreda : red a = 0 := by
      have hval1 : 1 < A.valuation c := not_le.mp (fun hle => hcA ((A.valuation_le_one_iff c).mp hle))
      have ha𝔪 : a ∈ IsLocalRing.maximalIdeal A := by
        rw [ValuationSubring.valuation_lt_one_iff]
        show A.valuation c⁻¹ < 1
        rw [map_inv₀]
        exact inv_lt_one_of_one_lt₀ hval1
      have : IsLocalRing.residue A a = 0 := (IsLocalRing.residue_eq_zero_iff a).mpr ha𝔪
      rw [← R.redBar_residue a, this, map_zero]
    set h' : ↥(modularFunctionFieldBar (N * q)) := algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ) * f - 1 with hh'
    have hmem : h' ∈ R.nodeIntegers w :=
      sub_mem (mul_mem (R.algebraMap_mem_nodeIntegers w a) hf) (one_mem _)
    have hval0 : V.HasValue h' 0 := by
      have h1 := (Place.hasValue_algebraMap V (a : AlgebraicClosure ℚ)).mul hc
      rw [show (a : AlgebraicClosure ℚ) * c = 1 from inv_mul_cancel₀ hc0] at h1
      have h2 := FltWs21.Val.hasValue_sub_algebraMap V _ _ 1 h1
      rwa [map_one, sub_self] at h2
    have hres₁ : (R.residue₁ ⟨h', hmem.1⟩ : ↥(modularFunctionFieldC k N)) = -1 := by
      have e : (⟨h', hmem.1⟩ : R.R₁.integers)
          = ⟨_, (R.algebraMap_mem_nodeIntegers w a).1⟩ * ⟨f, hf.1⟩ - 1 := rfl
      rw [e, map_sub, map_mul, map_one, FltWs21.Val.residue₁_const, hreda, map_zero, zero_mul, zero_sub]
    have hres₂ : (R.residue₂ ⟨h', hmem.2.1⟩ : ↥(modularFunctionFieldC k N)) = -1 := by
      have e : (⟨h', hmem.2.1⟩ : R.R₂.integers)
          = ⟨_, (R.algebraMap_mem_nodeIntegers w a).2.1⟩ * ⟨f, hf.2.1⟩ - 1 := rfl
      rw [e, map_sub, map_mul, map_one, FltWs21.Val.residue₂_const, hreda, map_zero, zero_mul, zero_sub]
    have hh'0 : h' ≠ 0 := by
      intro h0
      have : (R.residue₁ ⟨h', hmem.1⟩ : ↥(modularFunctionFieldC k N)) = 0 := by
        have e : (⟨h', hmem.1⟩ : R.R₁.integers) = 0 := Subtype.ext h0
        rw [e, map_zero]
      rw [hres₁] at this
      exact neg_ne_zero.mpr one_ne_zero this
    have hord0 : 0 < V.ord h' := FltWs21.Val.ord_pos_of_hasValue_zero V hval0 hh'0
    obtain ⟨cv, hcv₁, hcv₂⟩ := hnode h' hmem
    have hcv : cv = -1 := by
      rw [hres₁] at hcv₁
      have hm1 : w.HasValue (-1 : ↥(modularFunctionFieldC k N)) (-1 : k) := by
        have := Place.hasValue_algebraMap w (-1 : k)
        rwa [map_neg, map_one] at this
      exact hcv₁.unique hm1
    have h0 := FltWs21.Val.common_value_eq_zero R hord W hW w hw hfix h' hmem V hV hord0 cv hcv₁ hcv₂
    rw [hcv] at h0
    exact neg_ne_zero.mpr one_ne_zero h0
  refine ⟨hcA, ?_⟩

  set a : A := ⟨c, hcA⟩ with ha
  set h : ↥(modularFunctionFieldBar (N * q)) := f - algebraMap (AlgebraicClosure ℚ) (↥(modularFunctionFieldBar (N * q))) (a : AlgebraicClosure ℚ) with hhdef
  have hmem : h ∈ R.nodeIntegers w := sub_mem hf (R.algebraMap_mem_nodeIntegers w a)
  have hval0 : V.HasValue h 0 := by
    have := FltWs21.Val.hasValue_sub_algebraMap V f c c hc
    rwa [sub_self] at this
  have hres₁h : (R.residue₁ ⟨h, hmem.1⟩ : ↥(modularFunctionFieldC k N)) = (R.residue₁ ⟨f, hf.1⟩ : ↥(modularFunctionFieldC k N)) - algebraMap k (↥(modularFunctionFieldC k N)) (red a) := by
    have e : (⟨h, hmem.1⟩ : R.R₁.integers) = ⟨f, hf.1⟩ - ⟨_, (R.algebraMap_mem_nodeIntegers w a).1⟩ := rfl
    rw [e, map_sub, FltWs21.Val.residue₁_const]
  show w.HasValue (R.residue₁ ⟨f, hf.1⟩ : ↥(modularFunctionFieldC k N)) (red a)
  by_cases hz : h = 0
  ·
    have hfc : (R.residue₁ ⟨f, hf.1⟩ : ↥(modularFunctionFieldC k N)) = algebraMap k (↥(modularFunctionFieldC k N)) (red a) := by
      have : (R.residue₁ ⟨h, hmem.1⟩ : ↥(modularFunctionFieldC k N)) = 0 := by
        have e : (⟨h, hmem.1⟩ : R.R₁.integers) = 0 := Subtype.ext hz
        rw [e, map_zero]
      rw [hres₁h, sub_eq_zero] at this
      exact this
    rw [hfc]
    exact Place.hasValue_algebraMap w (red a)
  · have hord0 : 0 < V.ord h := FltWs21.Val.ord_pos_of_hasValue_zero V hval0 hz
    obtain ⟨cv, hcv₁, hcv₂⟩ := hnode h hmem
    have hcv0 := FltWs21.Val.common_value_eq_zero R hord W hW w hw hfix h hmem V hV hord0 cv hcv₁ hcv₂
    rw [hcv0, hres₁h] at hcv₁
    have := FltWs21.Val.hasValue_add_algebraMap w _ _ (red a) hcv₁
    rwa [sub_add_cancel, zero_add] at this

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_and_hasValue_nodeResidueFst_of_hasValue
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_and_hasValue_nodeResidueFst_of_hasValue (solution)
