-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.finite_setOf_fixed_of_eq_gammaLift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/d0541ead-5297-59f5-b605-b5ff9a633ffd

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_QExpFrobeniusModL
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
import Theorems.Thm_ModularCurve_diamondActionModL_gammaLift_mul_and_eq_one_of_mem_and_ofAlgAut_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_finite_setOf_fixed_of_eq_gammaLift
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

noncomputable section

namespace P2mFixFinH

section FixedScalars

open Polynomial

theorem exists_algebraMap_eq_of_pow_eq {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] {c : K} (hc : c ^ p = c) : ∃ a : ZMod p, algebraMap (ZMod p) K a = c := by
  classical
  have hp : p.Prime := Fact.out
  set f : K[X] := X ^ p - X with hf
  have hf0 : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hp.one_lt
  set T : Finset K := Finset.univ.image (algebraMap (ZMod p) K) with hT
  have hTcard : T.card = p := by
    rw [hT, Finset.card_image_of_injective _ (algebraMap (ZMod p) K).injective, Finset.card_univ,
      ZMod.card]
  have hroot : ∀ y : K, y ^ p = y → y ∈ f.roots.toFinset := fun y hy => by
    rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot, hf, eval_sub, eval_pow, eval_X, hy, sub_self]
  have hTroots : T ⊆ f.roots.toFinset := by
    intro y hy
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hy
    exact hroot _ (by rw [← map_pow, ZMod.pow_card])
  have hcard_le : f.roots.toFinset.card ≤ T.card := by
    rw [hTcard]
    exact (Multiset.toFinset_card_le _).trans ((card_roots' f).trans
      (FiniteField.X_pow_card_sub_X_natDegree_eq K hp.one_lt).le)
  have hTeq : T = f.roots.toFinset := Finset.eq_of_subset_of_card_le hTroots hcard_le
  have hc' := hroot c hc
  rw [← hTeq] at hc'
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hc'
  exact ⟨a, ha⟩

end FixedScalars

section Descent

open MvPolynomial

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {p : ℕ} [Fact p.Prime]

theorem frobenius_aeval {R : Type*} [CommRing R] [Algebra R F] [CharP R p] [CharP F p]
    {ι : Type*} (v : ι → F) (P : MvPolynomial ι R) :
    frobenius F p (aeval v P) = aeval (fun i => v i ^ p) (map (frobenius R p) P) := by
  rw [aeval_def, aeval_def, eval₂_map, eval₂_comp_left]
  have h1 : (frobenius F p).comp (algebraMap R F) = (algebraMap R F).comp (frobenius R p) := by
    ext c
    simp only [RingHom.comp_apply, frobenius_def, map_pow]
  rw [h1]
  exact congrArg (fun g => eval₂ _ g P) (funext fun i => frobenius_def (p := p) (v i))

variable (φ : F →ₐ[K] F)

omit [Fact p.Prime] in

theorem aeval_pow_eq_zero_of_aeval_eq_zero {ι : Type*} {v : ι → F} (hv : ∀ i, φ (v i) = v i ^ p)
    {Q : MvPolynomial ι K} (hQ : aeval v Q = 0) : aeval (fun i => v i ^ p) Q = 0 := by
  have h := comp_aeval_apply φ (f := v) Q
  rw [hQ, map_zero] at h
  rw [show (fun i => v i ^ p) = fun i => φ (v i) from funext fun i => (hv i).symm]
  exact h.symm

theorem exists_relation_zmod_of_relation [CharP K p] [CharP F p] [PerfectRing K p]
    [Algebra (ZMod p) K] [Algebra (ZMod p) F] [IsScalarTower (ZMod p) K F]
    {ι : Type*} {z : ι → F} (hz : ∀ i, φ (z i) = z i ^ p)
    {P : MvPolynomial ι K} (hP0 : P ≠ 0) (hP : aeval z P = 0) :
    ∃ P₀ : MvPolynomial ι (ZMod p), P₀ ≠ 0 ∧ P₀.support ⊆ P.support ∧ aeval z P₀ = 0 := by
  classical
  set w : ι → F := fun i => z i ^ p with hw
  have hwφ : ∀ i, φ (w i) = w i ^ p := fun i => by simp only [hw, map_pow, hz]

  have hex : ∃ n, ∃ Q : MvPolynomial ι K, Q ≠ 0 ∧ Q.support ⊆ P.support ∧ aeval w Q = 0 ∧
      Q.support.card = n :=
    ⟨_, P, hP0, subset_rfl, aeval_pow_eq_zero_of_aeval_eq_zero φ hz hP, rfl⟩
  obtain ⟨Q, hQ0, hQsupp, hQw, hQcard⟩ := Nat.find_spec hex
  have hmin : ∀ Q' : MvPolynomial ι K, Q'.support ⊆ P.support → aeval w Q' = 0 →
      Q'.support.card < Q.support.card → Q' = 0 := by
    intro Q' h1 h2 h3
    by_contra h0
    exact Nat.find_min hex (hQcard ▸ h3) ⟨Q', h0, h1, h2, rfl⟩

  obtain ⟨m, hm⟩ := ne_zero_iff.mp hQ0
  set c : K := Q.coeff m with hc
  have hmsupp : m ∈ Q.support := mem_support_iff.mpr hm
  set Q₁ : MvPolynomial ι K := c⁻¹ • Q with hQ₁
  have hQ₁supp : Q₁.support = Q.support := support_smul_eq (inv_ne_zero hm) Q
  have hQ₁m : Q₁.coeff m = 1 := by
    rw [hQ₁, coeff_smul, smul_eq_mul, ← hc, inv_mul_cancel₀ hm]
  have hQ₁w : aeval w Q₁ = 0 := by rw [hQ₁, map_smul, hQw, smul_zero]

  set D : MvPolynomial ι K := Q₁ - map (frobenius K p) Q₁ with hD
  have hDw : aeval (fun i => w i ^ p) D = 0 := by
    rw [hD, map_sub, aeval_pow_eq_zero_of_aeval_eq_zero φ hwφ hQ₁w, ← frobenius_aeval, hQ₁w,
      map_zero, sub_zero]
  have hDsupp : D.support ⊆ Q.support.erase m := by
    intro m' hm'
    rw [Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · rintro rfl
      rw [mem_support_iff, hD, coeff_sub, coeff_map, hQ₁m, map_one, sub_self] at hm'
      exact hm' rfl
    · have hsub := support_sub (p := Q₁) (q := map (frobenius K p) Q₁)
      rcases Finset.mem_union.mp (hsub hm') with h | h
      · rwa [← hQ₁supp]
      · rw [← hQ₁supp]
        exact support_map_subset _ _ h

  set D₁ : MvPolynomial ι K := map ((frobeniusEquiv K p).symm : K →+* K) D with hD₁
  have hD₁D : map (frobenius K p) D₁ = D := by
    rw [hD₁, map_map]
    have : (frobenius K p).comp ((frobeniusEquiv K p).symm : K →+* K) = RingHom.id K := by
      ext a
      exact frobenius_apply_frobeniusEquiv_symm K p a
    rw [this, map_id]
  have hD₁w : aeval w D₁ = 0 := by
    apply frobenius_inj F p
    rw [frobenius_aeval, hD₁D, hDw, map_zero]
  have hD₁supp : D₁.support = D.support :=
    support_map_of_injective _ (frobeniusEquiv K p).symm.injective
  have hD₁zero : D₁ = 0 := by
    apply hmin D₁
    · rw [hD₁supp]
      exact hDsupp.trans ((Finset.erase_subset _ _).trans hQsupp)
    · exact hD₁w
    · rw [hD₁supp]
      exact (Finset.card_le_card hDsupp).trans_lt (Finset.card_erase_lt_of_mem hmsupp)
  have hD0 : D = 0 := by rw [← hD₁D, hD₁zero, map_zero]

  have hfix : ∀ m', (Q₁.coeff m') ^ p = Q₁.coeff m' := by
    intro m'
    have h := congrArg (coeff m') hD0
    rw [hD, coeff_sub, coeff_map, coeff_zero, sub_eq_zero, frobenius_def] at h
    exact h.symm
  have hrange : Q₁ ∈ Set.range (map (algebraMap (ZMod p) K)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro c' hc'
    obtain ⟨m', -, rfl⟩ := mem_coeffs_iff.mp hc'
    exact exists_algebraMap_eq_of_pow_eq (hfix m')
  obtain ⟨P₀, hP₀⟩ := hrange
  have hP₀supp : P₀.support = Q₁.support := by
    rw [← hP₀]
    exact (support_map_of_injective P₀ (algebraMap (ZMod p) K).injective).symm
  refine ⟨P₀, ?_, ?_, ?_⟩
  · rintro rfl
    rw [map_zero] at hP₀
    have h := hQ₁m
    rw [← hP₀, coeff_zero] at h
    exact zero_ne_one h
  · rw [hP₀supp, hQ₁supp]
    exact hQsupp
  ·
    have h1 : aeval w P₀ = 0 := by
      rw [← aeval_map_algebraMap K w P₀, hP₀]
      exact hQ₁w
    apply frobenius_inj F p
    rw [map_zero, frobenius_aeval, ZMod.frobenius_zmod, map_id]
    exact h1

theorem algebraicIndependent_of_algebraicIndependent_zmod [CharP K p] [CharP F p]
    [PerfectRing K p] [Algebra (ZMod p) K] [Algebra (ZMod p) F] [IsScalarTower (ZMod p) K F]
    {ι : Type*} {z : ι → F} (hz : ∀ i, φ (z i) = z i ^ p)
    (h : AlgebraicIndependent (ZMod p) z) : AlgebraicIndependent K z := by
  rw [algebraicIndependent_iff]
  intro P hP
  by_contra hP0
  obtain ⟨P₀, hP₀0, -, hP₀z⟩ := exists_relation_zmod_of_relation φ hz hP0 hP
  exact hP₀0 (h.eq_zero_of_aeval_eq_zero P₀ hP₀z)

end Descent

section Form

open IntermediateField

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {p : ℕ} [Fact p.Prime]
  [CharP F p] [Algebra (ZMod p) F] (φ : F →ₐ[K] F)

omit [CharP F p] in

theorem apply_algebraMap_zmod (a : ZMod p) : φ (algebraMap (ZMod p) F a) = algebraMap (ZMod p) F a := by
  have h : (φ : F →+* F).comp (algebraMap (ZMod p) F) = algebraMap (ZMod p) F := Subsingleton.elim _ _
  exact RingHom.congr_fun h a

omit [CharP F p] in

theorem not_algebraicIndependent_of_val {ι : Type*} (E : IntermediateField (ZMod p) F)
    (z' : ι → E) (h : ¬ AlgebraicIndependent (ZMod p) (fun i => (z' i : F))) :
    ¬ AlgebraicIndependent (ZMod p) z' := fun h' =>
  h (h'.map' (f := E.val) (fun _ _ hab => Subtype.ext hab))

variable [CharP K p] [PerfectRing K p] [Algebra (ZMod p) K] [IsScalarTower (ZMod p) K F]

theorem exists_primeField_form (S : Set F) (hS : ∀ s ∈ S, φ s = s ^ p)
    (hgenS : IntermediateField.adjoin K S = ⊤)
    (hF : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ∃ E : IntermediateField (ZMod p) F,
      (∃ s : Finset E, IntermediateField.adjoin (ZMod p) (s : Set E) = ⊤) ∧
      IntermediateField.adjoin K (Set.range (algebraMap E F)) = ⊤ ∧
      (∀ y : E, φ (algebraMap E F y) = algebraMap E F (y ^ Nat.card (ZMod p))) ∧
      AlgebraicCurve.IsCurveOver (ZMod p) E := by
  classical
  obtain ⟨x, hx, hxfin⟩ := hF
  haveI := hxfin
  set Kx : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F) with hKx

  haveI : Algebra.EssFiniteType K Kx :=
    essFiniteType_iff.mpr (fg_adjoin_of_finite (Set.finite_singleton x))
  haveI : Algebra.EssFiniteType Kx F := inferInstance
  haveI : Algebra.EssFiniteType K F := Algebra.EssFiniteType.comp K Kx F
  obtain ⟨G, hG⟩ := IntermediateField.fg_top K F
  have hmem : ∀ g : F, ∃ Tg : Finset F, (Tg : Set F) ⊆ S ∧
      g ∈ IntermediateField.adjoin K (Tg : Set F) :=
    fun g => exists_finset_of_mem_adjoin (by rw [hgenS]; exact mem_top)
  choose Tg hTgS hTg using hmem
  set T : Finset F := G.biUnion Tg with hTdef
  have hTS : (T : Set F) ⊆ S := by
    intro y hy
    obtain ⟨g, -, hyg⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hy)
    exact hTgS g hyg
  have hTφ : ∀ y ∈ (T : Set F), φ y = y ^ p := fun y hy => hS y (hTS hy)
  have hTtopK : IntermediateField.adjoin K (T : Set F) = ⊤ := by
    apply top_le_iff.mp
    rw [← hG]
    apply adjoin_le_iff.mpr
    intro g hg
    have h1 : IntermediateField.adjoin K (Tg g : Set F) ≤ IntermediateField.adjoin K (T : Set F) :=
      adjoin.mono K _ _ (fun y hy => Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨g, hg, hy⟩))
    exact h1 (hTg g)

  have htex : ∃ t ∈ T, Transcendental K t := by
    by_contra hcon
    have hint : ∀ y ∈ (T : Set F), IsIntegral K y := fun y hy => by
      have : IsAlgebraic K y := by
        by_contra h
        exact hcon ⟨y, hy, h⟩
      exact this.isIntegral
    haveI : Algebra.IsAlgebraic K (IntermediateField.adjoin K (T : Set F)) := isAlgebraic_adjoin hint
    have hxmem : x ∈ IntermediateField.adjoin K (T : Set F) := by rw [hTtopK]; exact mem_top
    have h1 : IsAlgebraic K (⟨x, hxmem⟩ : IntermediateField.adjoin K (T : Set F)) :=
      Algebra.IsAlgebraic.isAlgebraic _
    exact hx (IntermediateField.isAlgebraic_iff.mp h1)
  obtain ⟨t, htT, htK⟩ := htex
  have ht0 : Transcendental (ZMod p) t := Transcendental.of_tower_top (ZMod p) htK

  set E : IntermediateField (ZMod p) F := IntermediateField.adjoin (ZMod p) (T : Set F) with hEdef
  have hTE : (T : Set F) ⊆ E := subset_adjoin _ _
  set t' : E := ⟨t, hTE htT⟩ with ht'def
  have ht'0 : Transcendental (ZMod p) t' := fun h => ht0 (IntermediateField.isAlgebraic_iff.mp h)

  have hEφ : ∀ y : E, φ (y : F) = (y : F) ^ p := by
    intro y
    have hy : (y : F) ∈ IntermediateField.adjoin (ZMod p) (T : Set F) := y.2
    refine adjoin_induction (F := ZMod p) (p := fun w _ => φ w = w ^ p) ?_ ?_ ?_ ?_ ?_ hy
    · exact hTφ
    · intro a
      rw [apply_algebraMap_zmod, ← map_pow, ZMod.pow_card]
    · intro a b _ _ ha hb
      rw [map_add, ha, hb, add_pow_char]
    · intro a _ ha
      rw [map_inv₀, ha, inv_pow]
    · intro a b _ _ ha hb
      rw [map_mul, ha, hb, mul_pow]

  set ιt : Type _ := (({t'} : Set E) : Type _) with hιt
  set xt : ιt → F := fun i => ((i : E) : F) with hxtdef
  set xt' : ιt → E := fun i => (i : E) with hxt'def
  have hxt_apply : ∀ i : ιt, xt i = t := fun i => by
    have h := i.2
    rw [Set.mem_singleton_iff] at h
    show ((i : E) : F) = t
    rw [h]
  have hxt'_apply : ∀ i : ιt, xt' i = t' := fun i => by
    have h := i.2
    rw [Set.mem_singleton_iff] at h
    exact h
  have hxtind : AlgebraicIndependent K xt :=
    (algebraicIndependent_singleton_iff (⟨t', Set.mem_singleton t'⟩ : ιt)).mpr
      (by rw [hxt_apply]; exact htK)
  have hxt'ind : AlgebraicIndependent (ZMod p) xt' :=
    (algebraicIndependent_singleton_iff (⟨t', Set.mem_singleton t'⟩ : ιt)).mpr
      (by rw [hxt'_apply]; exact ht'0)

  set ιx : Type _ := (({x} : Set F) : Type _) with hιx
  have hxind : AlgebraicIndependent K (Subtype.val : ιx → F) :=
    (algebraicIndependent_singleton_iff (⟨x, Set.mem_singleton x⟩ : ιx)).mpr hx
  have halgKx : Algebra.IsAlgebraic
      (IntermediateField.adjoin K (Set.range (Subtype.val : ιx → F))) F := by
    rw [Subtype.range_coe]
    exact Algebra.IsAlgebraic.of_finite Kx F
  have halgKx' : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (Subtype.val : ιx → F))) F := by
    open scoped IntermediateField.algebraAdjoinAdjoin in
    exact (IsFractionRing.comap_isAlgebraic_iff
      (A := Algebra.adjoin K (Set.range (Subtype.val : ιx → F)))
      (K := IntermediateField.adjoin K (Set.range (Subtype.val : ιx → F))) (C := F)).mpr halgKx
  have hbx : IsTranscendenceBasis K (Subtype.val : ιx → F) :=
    hxind.isTranscendenceBasis_iff_isAlgebraic.mpr halgKx'
  have htr1 : Algebra.trdeg K F = 1 := by
    rw [← hbx.cardinalMk_eq_trdeg]
    exact Cardinal.mk_singleton x
  have hbt : IsTranscendenceBasis K xt :=
    hxtind.isTranscendenceBasis_of_trdeg_le_of_finite (by rw [htr1]; exact (Cardinal.mk_singleton t').ge)
  haveI halgKt : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range xt)) F := hbt.isAlgebraic

  set K₁ : IntermediateField (ZMod p) E := IntermediateField.adjoin (ZMod p) (Set.range xt') with hK₁
  set T'' : Set E := ((↑) : E → F) ⁻¹' (T : Set F) with hT''
  have hgenalg : ∀ y ∈ T'', IsAlgebraic K₁ y := by
    intro y hy

    set zK : Option ιt → F := fun o => o.elim (y : F) xt with hzK
    have hzKφ : ∀ o, φ (zK o) = zK o ^ p := by
      rintro (_ | i)
      · exact hEφ y
      · exact hEφ _
    have hnotK : ¬ AlgebraicIndependent K zK := by
      rw [hzK, hxtind.option_iff_transcendental]
      exact fun htr => htr (Algebra.IsAlgebraic.isAlgebraic _)

    have hnot0 : ¬ AlgebraicIndependent (ZMod p) zK := fun h0 =>
      hnotK (algebraicIndependent_of_algebraicIndependent_zmod φ hzKφ h0)

    set zE : Option ιt → E := fun o => o.elim y xt' with hzE
    have hzEval : (fun o => (zE o : F)) = zK := by
      funext o
      rcases o with _ | i <;> rfl
    have hnotE : ¬ AlgebraicIndependent (ZMod p) zE :=
      not_algebraicIndependent_of_val E zE (by rw [hzEval]; exact hnot0)
    rw [hzE, hxt'ind.option_iff_transcendental] at hnotE
    have halg : IsAlgebraic (Algebra.adjoin (ZMod p) (Set.range xt')) y := by
      by_contra h
      exact hnotE h
    open scoped IntermediateField.algebraAdjoinAdjoin in
    exact (IsFractionRing.isAlgebraic_iff (Algebra.adjoin (ZMod p) (Set.range xt')) K₁ E).mp halg

  have hvalT'' : ((↑) : E → F) '' T'' = (T : Set F) :=
    Set.image_preimage_eq_of_subset (by
      intro y hy
      exact ⟨⟨y, hTE hy⟩, rfl⟩)
  have hT''top : IntermediateField.adjoin (ZMod p) T'' = (⊤ : IntermediateField (ZMod p) E) := by
    apply lift_injective
    rw [lift_adjoin, lift_top, hvalT'']
  have hK₁top : IntermediateField.adjoin K₁ T'' = (⊤ : IntermediateField K₁ E) := by
    apply restrictScalars_injective (ZMod p)
    rw [restrictScalars_top, adjoin_adjoin_left]
    apply top_le_iff.mp
    rw [← hT''top]
    exact adjoin.mono _ _ _ Set.subset_union_right
  haveI : Finite T'' :=
    ((T.finite_toSet).preimage Subtype.val_injective.injOn).to_subtype
  haveI hK₁fin : FiniteDimensional K₁ (IntermediateField.adjoin K₁ T'') :=
    finiteDimensional_adjoin (fun y hy => (hgenalg y hy).isIntegral)
  set eK₁ : (IntermediateField.adjoin K₁ T'') ≃ₐ[K₁] E :=
    (equivOfEq hK₁top).trans topEquiv with heK₁
  have hfinE : FiniteDimensional K₁ E := LinearEquiv.finiteDimensional eK₁.toLinearEquiv
  have hfinE' : FiniteDimensional (IntermediateField.adjoin (ZMod p) ({t'} : Set E)) E := by
    have hr : Set.range xt' = ({t'} : Set E) := by
      rw [hxt'def]
      exact Subtype.range_coe
    rw [← hr]
    exact hfinE

  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · refine ⟨T.preimage ((↑) : E → F) Subtype.val_injective.injOn, ?_⟩
    rw [Finset.coe_preimage]
    exact hT''top
  · apply top_le_iff.mp
    rw [← hTtopK]
    apply adjoin_le_iff.mpr
    intro y hy
    exact subset_adjoin _ _ ⟨⟨y, hTE hy⟩, rfl⟩
  · intro y
    rw [Nat.card_zmod]
    exact hEφ y
  · exact AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField ht'0 hfinE'

end Form

end P2mFixFinH

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open P2mFixFinH in

theorem P2mFixFinH.finite_fixedPoints_qExpFrobeniusPlaceModL_iterate
    (K : Type) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) (r : ℕ) (hr : 0 < r) :
    (Function.fixedPoints (qExpFrobeniusPlaceModL K Γ p)^[r]).Finite := by
  classical

  letI algZK : Algebra (ZMod p) K := ZMod.algebra K p
  letI algZF : Algebra (ZMod p) ↥(qExpFunctionFieldC K Γ) :=
    ((algebraMap K ↥(qExpFunctionFieldC K Γ)).comp (algebraMap (ZMod p) K)).toAlgebra
  letI : SMul (ZMod p) ↥(qExpFunctionFieldC K Γ) := algZF.toSMul
  letI : Module (ZMod p) ↥(qExpFunctionFieldC K Γ) := algZF.toModule
  haveI : IsScalarTower (ZMod p) K ↥(qExpFunctionFieldC K Γ) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : CharP ↥(qExpFunctionFieldC K Γ) p :=
    charP_of_injective_algebraMap (algebraMap K ↥(qExpFunctionFieldC K Γ)).injective p

  set S : Set ↥(qExpFunctionFieldC K Γ) :=
    ((↑) : ↥(qExpFunctionFieldC K Γ) → LaurentSeries K) ⁻¹' ModularCurve.intFormRatiosC K Γ with hSdef
  have hS : ∀ s ∈ S, qExpFrobeniusModL K Γ p s = s ^ p := by
    intro s hs
    obtain ⟨k, f, g, pf, pg, hf, hg, hg0, hsv⟩ := hs
    apply Subtype.ext
    rw [ModularCurve.coe_qExpFrobeniusModL]
    push_cast
    rw [hsv, map_div₀, ModularCurve.qExpand_intSeriesC_eq_pow, ModularCurve.qExpand_intSeriesC_eq_pow, div_pow]

  have hgenS : IntermediateField.adjoin K S = ⊤ := by
    apply eq_top_iff.mpr
    intro z _
    set M' : IntermediateField K (LaurentSeries K) :=
      (IntermediateField.adjoin K S).map (qExpFunctionFieldC K Γ).val with hM'
    have hle : qExpFunctionFieldC K Γ ≤ M' := by
      show IntermediateField.adjoin K (ModularCurve.intFormRatiosC K Γ) ≤ M'
      apply IntermediateField.adjoin_le_iff.mpr
      intro w hw
      show w ∈ (M' : Set (LaurentSeries K))
      rw [hM', IntermediateField.coe_map]
      refine ⟨⟨w, ModularCurve.intFormRatiosC_subset K Γ hw⟩, ?_, rfl⟩
      exact IntermediateField.subset_adjoin K S (show (⟨w, _⟩ : ↥(qExpFunctionFieldC K Γ)) ∈ S from hw)
    have hz : (z : LaurentSeries K) ∈ (M' : Set (LaurentSeries K)) := hle z.2
    rw [hM', IntermediateField.coe_map] at hz
    obtain ⟨y, hy, hyz⟩ := hz
    have hyz' : y = z := Subtype.ext hyz
    rw [← hyz']
    exact hy

  obtain ⟨x, -, hx, hxfin⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K Γ hT

  obtain ⟨E, hfg, hgen, hφE, hcurve⟩ := exists_primeField_form (qExpFrobeniusModL K Γ p) S hS hgenS ⟨x, hx, hxfin⟩
  haveI := hcurve
  haveI : AlgebraicCurve.IsCurveOver K ↥(qExpFunctionFieldC K Γ) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hx hxfin

  exact (AlgebraicCurve.finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors (ZMod p) K ↥E
    ↥(qExpFunctionFieldC K Γ) hfg hgen (qExpFrobeniusModL K Γ p) (qExpFrobeniusModL_isIntegral K Γ p) hφE r hr).1

end

set_option maxHeartbeats 6400000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v) :
    {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) |
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite := by
  classical

  have hpN : ¬ p ∣ M / p := by
    rintro ⟨k, hk⟩
    apply hpM2
    refine ⟨k, ?_⟩
    calc M = M / p * p := (Nat.div_mul_cancel hpM).symm
      _ = p ^ 2 * k := by rw [hk]; ring
  have hT : ModularGroup.T ∈ JHNeronObjectAtP.ΓN p M H hpM :=
    ModularCurve.Gamma1_le_GammaH (M / p) _ (by rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T])

  have hcomm : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ w) =
        δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p w) := by
    intro w
    rw [hδ w, hδ]
    exact ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) hpN
      (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb) w
  have hδm : ∀ w, δ^[Fintype.card (ZMod (M / p))ˣ] w = w := by
    have h5 := (ModularCurve.diamondActionModL_gammaLift_mul_and_eq_one_of_mem_and_ofAlgAut_smul (ResidueField ↥A)
      (M / p) (infSubgroup p M H hpM)).2.2.2.2.1
      (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    have h6 := (ModularCurve.diamondActionModL_gammaLift_mul_and_eq_one_of_mem_and_ofAlgAut_smul (ResidueField ↥A)
      (M / p) (infSubgroup p M H hpM)).2.2.2.2.2.1
      (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    have hiter : ∀ (n : ℕ) (w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))),
        δ^[n] w = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) (pb ^ n))) • w := by
      intro n
      induction n with
      | zero =>
        intro w
        rw [Function.iterate_zero_apply, pow_zero]
        exact (h6 w 1 (one_mem _)).symm
      | succ n ih =>
        intro w
        rw [Function.iterate_succ_apply', ih, hδ, pow_succ']
        exact (h5 w pb (pb ^ n)).symm
    intro w
    rw [hiter (Fintype.card (ZMod (M / p))ˣ) w, pow_card_eq_one]
    exact h6 w 1 (one_mem _)

  have hsub : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) |
      JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v} ⊆
      Function.fixedPoints
        (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)^[2 * Fintype.card (ZMod (M / p))ˣ] := by
    intro v hv
    have hv' : qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
        (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v)) = v := hv
    have hc : Function.Commute δ
        (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)^[2] :=
      Function.Commute.iterate_right (fun w => (hcomm w).symm) 2
    have hψ : Function.IsFixedPt
        (δ ∘ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)^[2]) v := by
      show δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
        (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v)) = v
      rw [← hcomm]
      exact hv'
    have h1 : (δ^[Fintype.card (ZMod (M / p))ˣ] ∘
        ((qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)^[2])^[Fintype.card (ZMod (M / p))ˣ]) v = v := by
      rw [← hc.comp_iterate]
      exact hψ.iterate _
    rw [Function.comp_apply, hδm, ← Function.iterate_mul] at h1
    exact h1

  exact (P2mFixFinH.finite_fixedPoints_qExpFrobeniusPlaceModL_iterate (ResidueField ↥A) p
    (JHNeronObjectAtP.ΓN p M H hpM) hT (2 * Fintype.card (ZMod (M / p))ˣ)
    (Nat.mul_pos two_pos Fintype.card_pos)).subset hsub

end S_ModularCurve_JHPlaceSpecialization_finite_setOf_fixed_of_eq_gammaLift
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_finite_setOf_fixed_of_eq_gammaLift (solution)
