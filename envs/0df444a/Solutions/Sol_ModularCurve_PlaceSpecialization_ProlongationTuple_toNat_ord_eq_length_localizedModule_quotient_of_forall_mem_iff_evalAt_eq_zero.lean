-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.toNat_ord_eq_length_localizedModule_quotient_of_forall_mem_iff_evalAt_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/8905daef-ffdf-5c17-a91b-e772894b6ce5

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_modularFunctionField_eq_full
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isIntegrallyClosed_nodeIntegersOver
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_Localization_AtPrime_isDiscreteValuationRing_of_height_eq_one
import Theorems.Thm_ValuationSubring_isPrincipalIdealRing_and_maximalIdeal_eq_span_of_irreducible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_toNat_ord_eq_length_localizedModule_quotient_of_forall_mem_iff_evalAt_eq_zero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace PlaceOrderLength

open IsLocalRing

section DVR
variable {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

theorem length_quotient_span_irreducible (ϖ : W) (hϖ : Irreducible ϖ) :
    Module.length W (W ⧸ (Ideal.span {ϖ} : Ideal W)) = 1 := by
  rw [Module.length_eq_one_iff, isSimpleModule_iff_quot_maximal]
  refine ⟨Ideal.span {ϖ}, ?_, ⟨LinearEquiv.refl W _⟩⟩
  rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
  exact IsLocalRing.maximalIdeal.isMaximal W

noncomputable def mulQuot (x y : W) :
    (W ⧸ (Ideal.span {y} : Ideal W)) →ₗ[W] (W ⧸ (Ideal.span {x * y} : Ideal W)) :=
  Submodule.mapQ (Ideal.span {y}) (Ideal.span {x * y}) (LinearMap.mulLeft W x) (by
    intro z hz
    rw [Submodule.mem_comap]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    exact Ideal.mem_span_singleton'.mpr ⟨c, by simp [LinearMap.mulLeft_apply]; ring⟩)

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem mulQuot_mk (x y r : W) : mulQuot x y (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (x * r) := rfl

noncomputable def projQuot (x y : W) :
    (W ⧸ (Ideal.span {x * y} : Ideal W)) →ₗ[W] (W ⧸ (Ideal.span {x} : Ideal W)) :=
  Submodule.mapQ (Ideal.span {x * y}) (Ideal.span {x}) LinearMap.id (by
    intro z hz
    rw [Submodule.mem_comap, LinearMap.id_apply]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    exact Ideal.mem_span_singleton'.mpr ⟨c * y, by ring⟩)

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem projQuot_mk (x y r : W) : projQuot x y (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ r := rfl

theorem length_quotient_span_pow_irreducible (ϖ : W) (hϖ : Irreducible ϖ) (n : ℕ) :
    Module.length W (W ⧸ (Ideal.span {ϖ ^ n} : Ideal W)) = n := by
  induction n with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one, Nat.cast_zero, Module.length_eq_zero_iff]
    refine ⟨fun a b => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact (Ideal.Quotient.eq).mpr (Submodule.mem_top)
  | succ n ih =>
    have hinj : Function.Injective (mulQuot ϖ (ϖ ^ n)) := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [mulQuot_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hz
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact (mul_dvd_mul_iff_left hϖ.ne_zero).mp hz
    have hsurj : Function.Surjective (projQuot ϖ (ϖ ^ n)) := by
      intro z
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨Ideal.Quotient.mk _ r, rfl⟩
    have hex : Function.Exact (mulQuot ϖ (ϖ ^ n)) (projQuot ϖ (ϖ ^ n)) := by
      intro z
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [projQuot_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨Ideal.Quotient.mk _ c, by rw [mulQuot_mk]⟩
      · rintro ⟨w, hw⟩
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective w
        rw [mulQuot_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton] at hw
        obtain ⟨d, hd⟩ := hw
        exact ⟨c - ϖ ^ n * d, by linear_combination -hd⟩
    have h := Module.length_eq_add_of_exact (mulQuot ϖ (ϖ ^ n)) (projQuot ϖ (ϖ ^ n)) hinj hsurj hex
    rw [pow_succ', h, ih, length_quotient_span_irreducible ϖ hϖ, Nat.cast_succ]

theorem length_quotient_span_singleton_eq_addVal (a : W) (ha : a ≠ 0) :
    Module.length W (W ⧸ (Ideal.span {a} : Ideal W)) = IsDiscreteValuationRing.addVal W a := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hspan : (Ideal.span {(u : W) * ϖ ^ n} : Ideal W) = Ideal.span {ϖ ^ n} :=
    Ideal.span_singleton_eq_span_singleton.mpr ⟨u⁻¹, by rw [mul_comm, ← mul_assoc, Units.inv_mul, one_mul]⟩
  rw [hspan, length_quotient_span_pow_irreducible ϖ hϖ, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ,
    (IsDiscreteValuationRing.addVal_eq_zero_iff).mpr u.isUnit, zero_add, nsmul_eq_mul, mul_one]

end DVR

section Localized
variable {B : Type*} [CommRing B] (𝔮 : Ideal B) [𝔮.IsPrime]

theorem length_localizedModule_quotient_span_singleton (g : B) :
    Module.length (Localization.AtPrime 𝔮) (LocalizedModule 𝔮.primeCompl (B ⧸ Ideal.span {g})) =
      Module.length (Localization.AtPrime 𝔮)
        (Localization.AtPrime 𝔮 ⧸ Ideal.span {algebraMap B (Localization.AtPrime 𝔮) g}) := by
  have hI : (Ideal.span {g} : Ideal B).localized' (Localization.AtPrime 𝔮) 𝔮.primeCompl
      (Algebra.linearMap B (Localization.AtPrime 𝔮)) = Ideal.span {algebraMap B (Localization.AtPrime 𝔮) g} := by
    rw [Ideal.localized'_eq_map, Ideal.map_span, Set.image_singleton]
  have e₁ := IsLocalizedModule.iso 𝔮.primeCompl
    ((Ideal.span {g} : Ideal B).toLocalizedQuotient' (Localization.AtPrime 𝔮) 𝔮.primeCompl
      (Algebra.linearMap B (Localization.AtPrime 𝔮)))
  have e₂ := e₁.extendScalarsOfIsLocalization 𝔮.primeCompl (Localization.AtPrime 𝔮)
  rw [e₂.length_eq]
  exact (Submodule.quotEquivOfEq _ _ hI).length_eq

theorem length_localizedModule_quotient_span_singleton_eq_addVal
    [IsDomain (Localization.AtPrime 𝔮)] [IsDiscreteValuationRing (Localization.AtPrime 𝔮)] (g : B)
    (hg : algebraMap B (Localization.AtPrime 𝔮) g ≠ 0) :
    Module.length (Localization.AtPrime 𝔮) (LocalizedModule 𝔮.primeCompl (B ⧸ Ideal.span {g})) =
      IsDiscreteValuationRing.addVal (Localization.AtPrime 𝔮) (algebraMap B (Localization.AtPrime 𝔮) g) := by
  rw [length_localizedModule_quotient_span_singleton, length_quotient_span_singleton_eq_addVal _ hg]

end Localized

end PlaceOrderLength

namespace PlaceOrderLength

theorem height_eq_one_of_forall_lt_eq_bot {B : Type*} [CommRing B] [IsDomain B] (𝔮 : Ideal B) [𝔮.IsPrime]
    (h0 : 𝔮 ≠ ⊥) (hht : ∀ 𝔭 : Ideal B, 𝔭.IsPrime → 𝔭 < 𝔮 → 𝔭 = ⊥) : 𝔮.height = 1 := by
  apply le_antisymm
  · refine (Ideal.height_le_iff (n := 1)).mpr fun 𝔭 h𝔭 hlt => ?_
    rw [hht 𝔭 h𝔭 hlt, Ideal.height_bot, Nat.cast_one]
    exact zero_lt_one
  · rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot B,
      Set.mem_singleton_iff]
    exact h0

end PlaceOrderLength

namespace PlaceOrderLength

theorem closure_nodeIntegersOver_union_range_algebraMap_eq_top
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N))
    (hfrac : ∀ z ∈ NodeLocalized.fieldOver (N * q) K, ∃ x y : ↥(modularFunctionFieldBar (N * q)),
      x ∈ R.nodeIntegersOver K w ∧ y ∈ R.nodeIntegersOver K w ∧ y ≠ 0 ∧
        z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
          ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))) :
    Subfield.closure ((R.nodeIntegersOver K w : Set ↥(modularFunctionFieldBar (N * q))) ∪
      Set.range (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) = ⊤ := by
  classical
  set T := Subfield.closure ((R.nodeIntegersOver K w : Set ↥(modularFunctionFieldBar (N * q))) ∪
      Set.range (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) with hT

  set val : ↥(modularFunctionFieldBar (N * q)) →+* LaurentSeries (AlgebraicClosure ℚ) :=
    (modularFunctionFieldBar (N * q)).val.toRingHom with hval
  have hval_apply : ∀ x : ↥(modularFunctionFieldBar (N * q)), val x = (x : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun x => rfl

  have hconst : ∀ a : AlgebraicClosure ℚ,
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a ∈ T.map val := by
    intro a
    refine ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) a,
      Subfield.subset_closure (Or.inr ⟨a, rfl⟩), rfl⟩

  have hquot : ∀ z : LaurentSeries (AlgebraicClosure ℚ), z ∈ NodeLocalized.fieldOver (N * q) K → z ∈ T.map val := by
    intro z hz
    obtain ⟨x, y, hx, hy, hy0, hz⟩ := hfrac z hz
    have hyv : val y ≠ 0 := by
      rw [hval_apply]
      exact fun h => hy0 (Subtype.ext h)
    have hxT : x ∈ T := Subfield.subset_closure (Or.inl hx)
    have hyT : y ∈ T := Subfield.subset_closure (Or.inl hy)
    refine ⟨x / y, div_mem hxT hyT, ?_⟩
    rw [map_div₀, div_eq_iff hyv, hval_apply, hval_apply]
    exact hz.symm

  have key : ∀ u : LaurentSeries (AlgebraicClosure ℚ), u ∈ modularFunctionFieldBar (N * q) → u ∈ T.map val := by
    intro u hu
    rw [mem_laurentBaseChange_iff] at hu
    refine Subfield.closure_le.mpr ?_ hu
    rintro z (⟨a, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact hconst a
    · have hu' : u ∈ modularFunctionField (N * q) := by
        rw [ModularCurve.modularFunctionField_eq_full]; exact hu
      change u ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ {jq, qExpand ℚ (N * q) jq}) at hu'
      have hle : Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ {jq, qExpand ℚ (N * q) jq}) ≤
          (T.map val).comap (coeffEmb (AlgebraicClosure ℚ)) := by
        refine Subfield.closure_le.mpr ?_
        rintro z (⟨r, rfl⟩ | hz)
        · rw [SetLike.mem_coe, Subfield.mem_comap, coeffEmb, algebraMap_laurentSeries_eq_single, coeffMap_single,
            ← algebraMap_laurentSeries_eq_single]
          exact hconst _
        · rw [SetLike.mem_coe, Subfield.mem_comap]
          rcases hz with rfl | rfl
          · rw [coeffEmb, ← jqModC_rat, coeffMap_jqModC]
            exact hquot _ (Subfield.subset_closure (Or.inr (Set.mem_insert _ _)))
          · rw [coeffEmb, ← jqModC_rat, show qExpand ℚ (N * q) (jqModC ℚ) = jqNModC ℚ (N * q) from rfl,
              coeffMap_jqNModC]
            exact hquot _ (Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl)))
      exact hle hu'

  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨t, ht, htx⟩ := key (x : LaurentSeries (AlgebraicClosure ℚ)) x.2
  have : t = x := Subtype.ext (by rw [← hval_apply t, htx])
  exact this ▸ ht

end PlaceOrderLength

set_option maxHeartbeats 3200000 in

theorem PlaceOrderLength.toNat_ord_eq_length_frame
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hfrac : ∀ z ∈ NodeLocalized.fieldOver (N * q) K, ∃ x y : ↥(modularFunctionFieldBar (N * q)),
      x ∈ R.nodeIntegersOver K w ∧ y ∈ R.nodeIntegersOver K w ∧ y ≠ 0 ∧
        z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w)
    (𝔮 : Ideal ↥(R.nodeIntegersOver K w)) [𝔮.IsPrime] (h𝔮 : ∀ g : ↥(R.nodeIntegersOver K w), g ∈ 𝔮 ↔ V.evalAt ((g : ↥(modularFunctionFieldBar (N * q)))) = 0)
    (hht : ∀ 𝔭 : Ideal ↥(R.nodeIntegersOver K w), 𝔭.IsPrime → 𝔭 < 𝔮 → 𝔭 = ⊥)
    (g : ↥(R.nodeIntegersOver K w)) (hg : g ≠ 0) :
    ((V.ord ((g : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ∞) =
      Module.length (Localization.AtPrime 𝔮) (LocalizedModule 𝔮.primeCompl (↥(R.nodeIntegersOver K w) ⧸ Ideal.span {g})) := by

  classical
  haveI hcurve := ModularCurve.isCurveOver_modularFunctionFieldBar (N * q)
  have hVrat : V.IsRational :=
    (AlgebraicCurve.Place.isRational_iff_deg_eq_one V).2 (AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed V)
  haveI hIC := R.isIntegrallyClosed_nodeIntegersOver K w

  have hBV : ∀ b : ↥(R.nodeIntegersOver K w), (b : ↥(modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring :=
    fun b => R.mem_toValuationSubring_of_mem_nodeIntegers b.2.1 hV

  let φ : ↥(R.nodeIntegersOver K w) →+* ↥V.toValuationSubring :=
    { toFun := fun b => ⟨(b : ↥(modularFunctionFieldBar (N * q))), hBV b⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun a b => Subtype.ext rfl }
  have hφ : ∀ b, ((φ b : ↥V.toValuationSubring) : ↥(modularFunctionFieldBar (N * q))) = b := fun b => rfl

  have hmem𝔮 : ∀ b : ↥(R.nodeIntegersOver K w), b ∈ 𝔮 ↔ φ b ∈ IsLocalRing.maximalIdeal ↥V.toValuationSubring := by
    intro b
    rw [h𝔮, V.evalAt_of_mem (hBV b), ← IsLocalRing.residue_eq_zero_iff]
    constructor
    · intro h0
      have h1 := V.algebraMap_residueInv hVrat (IsLocalRing.residue _ (φ b))
      rw [show (φ b) = ⟨(b : ↥(modularFunctionFieldBar (N * q))), hBV b⟩ from rfl, h0, map_zero] at h1
      exact h1.symm
    · intro hm
      rw [show (⟨(b : ↥(modularFunctionFieldBar (N * q))), hBV b⟩ : ↥V.toValuationSubring) = φ b from rfl, hm,
        ← map_zero (algebraMap (AlgebraicClosure ℚ) V.ResidueField), V.residueInv_algebraMap]
  have hunit : ∀ s : 𝔮.primeCompl, IsUnit (φ s) := by
    intro s
    have hs : (s : ↥(R.nodeIntegersOver K w)) ∉ 𝔮 := s.2
    rw [hmem𝔮] at hs
    by_contra hu
    exact hs ((IsLocalRing.mem_maximalIdeal _).mpr hu)

  let ψ : Localization.AtPrime 𝔮 →+* ↥V.toValuationSubring := IsLocalization.lift hunit
  have hψ : ∀ b : ↥(R.nodeIntegersOver K w), ψ (algebraMap _ (Localization.AtPrime 𝔮) b) = φ b :=
    fun b => IsLocalization.lift_eq hunit b
  letI instAlg : Algebra (Localization.AtPrime 𝔮) ↥(modularFunctionFieldBar (N * q)) :=
    ((algebraMap ↥V.toValuationSubring ↥(modularFunctionFieldBar (N * q))).comp ψ).toAlgebra
  have halg : ∀ x : Localization.AtPrime 𝔮, algebraMap (Localization.AtPrime 𝔮) ↥(modularFunctionFieldBar (N * q)) x =
      (ψ x : ↥(modularFunctionFieldBar (N * q))) := fun x => rfl
  have hinjB : Function.Injective (algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime 𝔮)) :=
    IsLocalization.injective (Localization.AtPrime 𝔮) 𝔮.primeCompl_le_nonZeroDivisors

  by_cases hg𝔮 : g ∉ 𝔮
  · have hu : IsUnit (φ g) := hunit ⟨g, hg𝔮⟩
    have hord : V.ord ((g : ↥(modularFunctionFieldBar (N * q)))) = 0 := by
      rw [← hφ g, show φ g = ((hu.unit : (↥V.toValuationSubring)ˣ) : ↥V.toValuationSubring) from rfl]
      exact V.ord_coe_unit hu.unit
    have hunitO : IsUnit (algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime 𝔮) g) :=
      IsLocalization.map_units (Localization.AtPrime 𝔮) (⟨g, hg𝔮⟩ : 𝔮.primeCompl)
    rw [hord, Int.toNat_zero, Nat.cast_zero, PlaceOrderLength.length_localizedModule_quotient_span_singleton,
      eq_comm, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top]
    exact hunitO

  rw [not_not] at hg𝔮
  have h𝔮0 : 𝔮 ≠ ⊥ := by
    intro h
    apply hg
    rw [h, Ideal.mem_bot] at hg𝔮
    exact hg𝔮
  haveI hDVR : IsDiscreteValuationRing (Localization.AtPrime 𝔮) :=
    Localization.AtPrime.isDiscreteValuationRing_of_height_eq_one 𝔮
      (PlaceOrderLength.height_eq_one_of_forall_lt_eq_bot 𝔮 h𝔮0 hht)

  have hψinj : Function.Injective ψ := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h; rw [hinjB h]
    · intro h
      have : (x : ↥(modularFunctionFieldBar (N * q))) = y := by rw [← hφ x, ← hφ y, h]
      rw [Subtype.ext this]
  have hinj : Function.Injective (algebraMap (Localization.AtPrime 𝔮) ↥(modularFunctionFieldBar (N * q))) := by
    intro x y h
    rw [halg, halg] at h
    exact hψinj (Subtype.ext h)

  letI instAlgQ : Algebra ℚ ↥(modularFunctionFieldBar (N * q)) :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).comp (algebraMap ℚ (AlgebraicClosure ℚ))).toAlgebra
  have halgQ : ∀ c : ℚ, algebraMap ℚ ↥(modularFunctionFieldBar (N * q)) c =
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (algebraMap ℚ (AlgebraicClosure ℚ) c) :=
    fun c => rfl
  let ι₀ : AlgebraicClosure ℚ →ₐ[ℚ] ↥(modularFunctionFieldBar (N * q)) :=
    { algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) with commutes' := fun _ => rfl }
  have hKO : ∀ c : ℚ, algebraMap ℚ ↥(modularFunctionFieldBar (N * q)) c ∈
      (algebraMap (Localization.AtPrime 𝔮) ↥(modularFunctionFieldBar (N * q))).range := by
    intro c
    have hnum : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c.num : AlgebraicClosure ℚ) ∈
        R.nodeIntegersOver K w := by
      rw [map_intCast]; exact intCast_mem _ c.num
    have hden : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (c.den : AlgebraicClosure ℚ) ∈
        R.nodeIntegersOver K w := by
      rw [map_natCast]; exact natCast_mem _ c.den
    have hden0 : ((c.den : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast c.den_ne_zero
    have hden𝔮 : (⟨_, hden⟩ : ↥(R.nodeIntegersOver K w)) ∉ 𝔮 := by
      intro hmem
      rw [h𝔮] at hmem
      exact hden0 (by rw [← V.evalAt_algebraMap ((c.den : ℕ) : AlgebraicClosure ℚ)]; exact hmem)
    refine ⟨IsLocalization.mk' (Localization.AtPrime 𝔮) (⟨_, hnum⟩ : ↥(R.nodeIntegersOver K w))
      (⟨⟨_, hden⟩, hden𝔮⟩ : 𝔮.primeCompl), ?_⟩
    have hspec := IsLocalization.mk'_spec (Localization.AtPrime 𝔮) (⟨_, hnum⟩ : ↥(R.nodeIntegersOver K w))
      (⟨⟨_, hden⟩, hden𝔮⟩ : 𝔮.primeCompl)
    have h2 := congrArg (algebraMap (Localization.AtPrime 𝔮) ↥(modularFunctionFieldBar (N * q))) hspec
    rw [map_mul, halg (algebraMap _ _ _), hψ, hφ, halg (algebraMap _ _ _), hψ, hφ] at h2
    have hdenF : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((c.den : ℕ) : AlgebraicClosure ℚ) ≠ 0 :=
      (map_ne_zero _).mpr hden0
    rw [halgQ, eq_ratCast, Rat.cast_def, map_div₀, eq_div_iff hdenF]
    exact h2

  have hE : ∀ x ∈ (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).fieldRange, IsSeparable ℚ x := by
    rintro x ⟨a, rfl⟩
    haveI : Algebra.IsSeparable ℚ (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.isSeparable_of_perfectField
    exact IsSeparable.map ι₀
      (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).injective
      (Algebra.IsSeparable.isSeparable ℚ a)

  have hgen : Subfield.closure (((algebraMap (Localization.AtPrime 𝔮) ↥(modularFunctionFieldBar (N * q))).range :
      Set ↥(modularFunctionFieldBar (N * q))) ∪
      ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).fieldRange : Set ↥(modularFunctionFieldBar (N * q)))) = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← PlaceOrderLength.closure_nodeIntegersOver_union_range_algebraMap_eq_top R K w hfrac]
    refine Subfield.closure_mono (Set.union_subset_union ?_ ?_)
    · intro b hb
      refine ⟨algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime 𝔮) ⟨b, hb⟩, ?_⟩
      rw [halg, hψ, hφ]
    · rw [RingHom.coe_fieldRange]
  have hOV : ∀ b : Localization.AtPrime 𝔮,
      algebraMap (Localization.AtPrime 𝔮) ↥(modularFunctionFieldBar (N * q)) b ∈ V.toValuationSubring :=
    fun b => (ψ b).2
  have hdom : ∀ b : Localization.AtPrime 𝔮, b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔮) →
      V.toValuationSubring.valuation (algebraMap (Localization.AtPrime 𝔮) ↥(modularFunctionFieldBar (N * q)) b) < 1 := by
    intro b hb
    rw [← IsLocalization.mk'_sec (M := 𝔮.primeCompl) (Localization.AtPrime 𝔮) b] at hb ⊢
    have ha : (IsLocalization.sec 𝔮.primeCompl b).1 ∈ 𝔮 :=
      (IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime 𝔮) 𝔮 _ _).mp hb
    rw [hmem𝔮] at ha
    have hm : ψ (IsLocalization.mk' (Localization.AtPrime 𝔮) (IsLocalization.sec 𝔮.primeCompl b).1
        (IsLocalization.sec 𝔮.primeCompl b).2) ∈ IsLocalRing.maximalIdeal ↥V.toValuationSubring := by
      rw [IsLocalization.lift_mk']
      exact Ideal.mul_mem_right _ _ ha
    rw [halg]
    exact (ValuationSubring.valuation_lt_one_iff _ _).mp hm

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime 𝔮)
  obtain ⟨-, -, hmax⟩ := ValuationSubring.isPrincipalIdealRing_and_maximalIdeal_eq_span_of_irreducible
    (K := ℚ) hinj hKO (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))).fieldRange hE hgen
    V.toValuationSubring hOV hdom π hπ
  have hgen_eq : (⟨algebraMap (Localization.AtPrime 𝔮) ↥(modularFunctionFieldBar (N * q)) π, hOV π⟩ :
      ↥V.toValuationSubring) = ψ π := Subtype.ext rfl
  rw [hgen_eq] at hmax
  have hπV : Irreducible (ψ π) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax

  have hg'0 : algebraMap ↥(R.nodeIntegersOver K w) (Localization.AtPrime 𝔮) g ≠ 0 := by
    intro h
    exact hg (hinjB (by rw [h, map_zero]))
  obtain ⟨n, u, hgu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg'0 hπ
  rw [PlaceOrderLength.length_localizedModule_quotient_span_singleton_eq_addVal 𝔮 g hg'0,
    IsDiscreteValuationRing.addVal_def _ u hπ n hgu]

  have hu' : IsUnit (ψ (u : Localization.AtPrime 𝔮)) := u.isUnit.map ψ
  have hgF : (g : ↥(modularFunctionFieldBar (N * q))) =
      ((hu'.unit : (↥V.toValuationSubring)ˣ) : ↥V.toValuationSubring) * (((ψ π : ↥V.toValuationSubring) :
        ↥(modularFunctionFieldBar (N * q)))) ^ (n : ℤ) := by
    have h1 := congrArg (fun x : Localization.AtPrime 𝔮 => ((ψ x : ↥V.toValuationSubring) : ↥(modularFunctionFieldBar (N * q)))) hgu
    simp only [map_mul, map_pow, hψ, hφ] at h1
    rw [zpow_natCast, h1]
    rfl
  rw [hgF, V.ord_unit_smul_zpow hu'.unit hπV (n : ℤ), Int.toNat_natCast]

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hfrac : ∀ z ∈ NodeLocalized.fieldOver (N * q) K, ∃ x y : ↥(modularFunctionFieldBar (N * q)),
      x ∈ R.nodeIntegersOver K w ∧ y ∈ R.nodeIntegersOver K w ∧ y ≠ 0 ∧
        z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w)
    (𝔮 : Ideal ↥(R.nodeIntegersOver K w)) [𝔮.IsPrime] (h𝔮 : ∀ g : ↥(R.nodeIntegersOver K w), g ∈ 𝔮 ↔ V.evalAt ((g : ↥(modularFunctionFieldBar (N * q)))) = 0)
    (hht : ∀ 𝔭 : Ideal ↥(R.nodeIntegersOver K w), 𝔭.IsPrime → 𝔭 < 𝔮 → 𝔭 = ⊥)
    (g : ↥(R.nodeIntegersOver K w)) (hg : g ≠ 0) :
    ((V.ord ((g : ↥(modularFunctionFieldBar (N * q))))).toNat : ℕ∞) =
      Module.length (Localization.AtPrime 𝔮) (LocalizedModule 𝔮.primeCompl (↥(R.nodeIntegersOver K w) ⧸ Ideal.span {g})) := by
  exact PlaceOrderLength.toNat_ord_eq_length_frame R K w hfrac V hV 𝔮 h𝔮 hht g hg

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_toNat_ord_eq_length_localizedModule_quotient_of_forall_mem_iff_evalAt_eq_zero
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_toNat_ord_eq_length_localizedModule_quotient_of_forall_mem_iff_evalAt_eq_zero (solution)
