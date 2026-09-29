-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_monoidHom_gamma0_algEquiv_slash_floor_enum_ker_xH_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/f1601528-e2ef-546e-adcd-6098c928b6bb

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
import Theorems.Thm_ModularCurve_exists_intSeriesC_mul_ne_of_gamma0Units_not_mem
import Theorems.Thm_ModularCurve_relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero
import Theorems.Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_monoidHom_gamma0_algEquiv_slash_floor_enum_ker_xH_of_eq_three
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

namespace W1Aux

open IntermediateField

theorem relfinrank_lift_eq_finrank {K E : Type*} [Field K] [Field E] [Algebra K E]
    (F : IntermediateField K E) (L : IntermediateField K F) :
    (IntermediateField.lift L).relfinrank F = Module.finrank L F := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le (IntermediateField.lift_le L)]
  let i : L ≃+* (IntermediateField.lift L) := (IntermediateField.liftAlgEquiv L).toRingEquiv
  let j : F ≃+* (IntermediateField.extendScalars (IntermediateField.lift_le L)) := RingEquiv.refl _
  refine (Algebra.finrank_eq_of_equiv_equiv i j ?_).symm
  ext a
  rfl

open scoped MatrixGroups in
theorem gamma0Units_surjective' (M : ℕ) [NeZero M] : Function.Surjective (CohCarrier.gamma0Units M) := by
  intro u
  have hAD : (((((u⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ) * ((u : ZMod M).val : ℤ) - 1 : ℤ) : ZMod M) = 0 := by
    simp
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hAD
  let γ : SL(2, ℤ) := ⟨!![(((u⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ), k; (M : ℤ), ((u : ZMod M).val : ℤ)], by
    rw [Matrix.det_fin_two_of]
    linarith⟩
  have hγ0 : γ ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [γ]
  refine ⟨⟨γ, hγ0⟩, Units.ext ?_⟩
  simp only [CohCarrier.gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, CongruenceSubgroup.Gamma0Map]
  simp [γ]

theorem mem_or_neg_mem_of_mem_sup_zpowers_neg_one {M : ℕ} (H : Subgroup (ZMod M)ˣ)
    {d : (ZMod M)ˣ} (hd : d ∈ H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)) : d ∈ H ∨ -d ∈ H := by
  let S : Subgroup (ZMod M)ˣ :=
    { carrier := {x | x = 1 ∨ x = -1}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (rfl | rfl) (rfl | rfl) <;> simp
      inv_mem' := by
        rintro a (rfl | rfl) <;> simp }
  have hS : Subgroup.zpowers (-1 : (ZMod M)ˣ) ≤ S := by
    rw [Subgroup.zpowers_le]
    exact Or.inr rfl
  obtain ⟨h, hh, z, hz, rfl⟩ := Subgroup.mem_sup.mp hd
  rcases hS hz with hz1 | hz1
  · left; rw [hz1, mul_one]; exact hh
  · right; rw [hz1]; simpa using hh

open scoped MatrixGroups ModularForm in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem core (L : Type) [Field L] [CharZero L] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (E E₂ : IntermediateField L (LaurentSeries L))
    (hE : E = ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H)) (hE₂ : E₂ = ModularCurve.qExpFunctionFieldC L (CongruenceSubgroup.Gamma0 M)) :
    ∃ ρ : CongruenceSubgroup.Gamma0 M →* (↥E ≃ₐ[L] ↥E),
      (∀ (γ : CongruenceSubgroup.Gamma0 M) {k : ℤ}
          (f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
          {pf pg pf₁ pg₁ : PowerSeries ℤ} (c : ℂ), c ≠ 0 →
          ModularCurve.IsIntegralQExp f pf → ModularCurve.IsIntegralQExp g pg →
          ModularCurve.IsIntegralQExp f₁ pf₁ → ModularCurve.IsIntegralQExp g₁ pg₁ →
          (⇑f₁ : UpperHalfPlane → ℂ) = c • ((⇑f : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) →
          (⇑g₁ : UpperHalfPlane → ℂ) = c • ((⇑g : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) →
          ModularCurve.intSeriesC L pg ≠ 0 → ModularCurve.intSeriesC L pg₁ ≠ 0 →
          ∀ x : ↥E, (x : LaurentSeries L) = ModularCurve.intSeriesC L pf / ModularCurve.intSeriesC L pg →
            ((ρ γ x : ↥E) : LaurentSeries L) = ModularCurve.intSeriesC L pf₁ / ModularCurve.intSeriesC L pg₁) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 M) (x : ↥E), (x : LaurentSeries L) ∈ E₂ → ρ γ x = x) ∧
      (∀ σ : ↥E ≃ₐ[L] ↥E, (∀ x : ↥E, (x : LaurentSeries L) ∈ E₂ → σ x = x) →
          ∃ γ : CongruenceSubgroup.Gamma0 M, σ = ρ γ) ∧
      (∀ γ : CongruenceSubgroup.Gamma0 M, ρ γ = 1 ↔
          CohCarrier.gamma0Units M γ ∈ H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)) := by
  classical
  subst hE hE₂
  have hMk : (M : L) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hΓ : CohCarrier.GammaH M H ≤ CongruenceSubgroup.Gamma0 M := CohCarrier.GammaH_le_Gamma0 H
  have hb0H : (ModularCurve.qExpFunctionFieldC L (CongruenceSubgroup.Gamma0 M)) ≤ (ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H)) := ModularCurve.qExpFunctionFieldC_mono L hΓ
  obtain ⟨ρ, hρH, hρneg, hρfix, hρslash⟩ :=
    ModularCurve.exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero L M H

  have hker_iff : ∀ γ : CongruenceSubgroup.Gamma0 M, ρ γ = 1 ↔
      CohCarrier.gamma0Units M γ ∈ H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ) := by
    intro γ
    constructor
    · intro hγ
      by_contra hd
      obtain ⟨k, f, g, f₁, g₁, pf, pg, pf₁, pg₁, c, hc, hf, hg, hf₁, hg₁, ef, eg, hg0, hg₁0, hne⟩ :=
        ModularCurve.exists_intSeriesC_mul_ne_of_gamma0Units_not_mem L M hMk H γ.1 γ.2 hd
      have key := hρslash γ f g f₁ g₁ c hc hf hg hf₁ hg₁ ef eg hg0 hg₁0
      rw [hγ, AlgEquiv.one_apply] at key
      change ModularCurve.intSeriesC L pf / ModularCurve.intSeriesC L pg =
        ModularCurve.intSeriesC L pf₁ / ModularCurve.intSeriesC L pg₁ at key
      rw [div_eq_div_iff hg0 hg₁0] at key
      exact hne (key.trans (mul_comm _ _))
    · intro hd
      rcases mem_or_neg_mem_of_mem_sup_zpowers_neg_one H hd with h | h
      · exact hρH γ (CohCarrier.mem_GammaH_iff.mpr ⟨γ.2, h⟩)
      · have hneg0 : (-(γ : SL(2, ℤ))) ∈ CongruenceSubgroup.Gamma0 M := by
          have := CongruenceSubgroup.Gamma0_mem.mp γ.2
          rw [CongruenceSubgroup.Gamma0_mem]
          simp [Matrix.SpecialLinearGroup.coe_neg, this]
        have hunits : CohCarrier.gamma0Units M ⟨-(γ : SL(2, ℤ)), hneg0⟩ =
            -CohCarrier.gamma0Units M γ := by
          ext
          simp [CohCarrier.gamma0Units, CongruenceSubgroup.Gamma0Map, Matrix.SpecialLinearGroup.coe_neg]
        have hnegH : (-(γ : SL(2, ℤ))) ∈ CohCarrier.GammaH M H :=
          CohCarrier.mem_GammaH_iff.mpr ⟨hneg0, by rw [hunits]; exact h⟩
        have hm1 : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma0 M := by
          rw [CongruenceSubgroup.Gamma0_mem]; simp [Matrix.SpecialLinearGroup.coe_neg]
        have e1 : γ = ⟨-1, hm1⟩ * ⟨-(γ : SL(2, ℤ)), hneg0⟩ := by
          ext1; simp
        rw [e1, map_mul, hρneg ⟨-1, hm1⟩ rfl, hρH ⟨-(γ : SL(2, ℤ)), hneg0⟩ hnegH, mul_one]

  have hker : ρ.ker = (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).comap (CohCarrier.gamma0Units M) := by
    ext γ; rw [MonoidHom.mem_ker, Subgroup.mem_comap]; exact hker_iff γ
  have hidx : ρ.ker.index = (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index := by
    rw [hker]; exact Subgroup.index_comap_of_surjective _ (gamma0Units_surjective' M)
  haveI : (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).FiniteIndex := inferInstance
  haveI : ρ.ker.FiniteIndex := ⟨by rw [hidx]; exact Subgroup.FiniteIndex.index_ne_zero⟩
  haveI : Finite (↥(CongruenceSubgroup.Gamma0 M) ⧸ ρ.ker) := Subgroup.finite_quotient_of_finiteIndex
  haveI hfinr : Finite ρ.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ρ).toEquiv
  haveI : Fintype ρ.range := Fintype.ofFinite _
  have hcard : Fintype.card ρ.range = (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index := by
    rw [Fintype.card_eq_nat_card, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv,
      ← Subgroup.index_eq_card, hidx]

  have hartin : Module.finrank (IntermediateField.fixedField ρ.range) (ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H)) = Fintype.card ρ.range :=
    FixedPoints.finrank_eq_card _ _
  have hL : IntermediateField.lift (IntermediateField.fixedField ρ.range) ≤ (ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H)) := IntermediateField.lift_le _
  have h0L : (ModularCurve.qExpFunctionFieldC L (CongruenceSubgroup.Gamma0 M)) ≤ IntermediateField.lift (IntermediateField.fixedField ρ.range) := by
    intro x hx
    have hxH : x ∈ (ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H)) := hb0H hx
    have hfx : (⟨x, hxH⟩ : (ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H))) ∈ IntermediateField.fixedField ρ.range := by
      rw [IntermediateField.mem_fixedField_iff]
      rintro _ ⟨γ, rfl⟩
      exact hρfix γ ⟨x, hxH⟩ hx
    exact (IntermediateField.mem_lift ⟨x, hxH⟩).mpr hfx
  have eP : (IntermediateField.lift (IntermediateField.fixedField ρ.range)).relfinrank (ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H)) =
      (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index :=
    (relfinrank_lift_eq_finrank _ _).trans (hartin.trans hcard)
  have eQ : (ModularCurve.qExpFunctionFieldC L (CongruenceSubgroup.Gamma0 M)).relfinrank (ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H)) = (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index :=
    ModularCurve.relfinrank_qExpFunctionFieldC_gamma0_gammaH_eq_index_of_charZero L M H
  have hmul := IntermediateField.relfinrank_mul_relfinrank h0L hL
  rw [eP, eQ] at hmul
  have hone : (ModularCurve.qExpFunctionFieldC L (CongruenceSubgroup.Gamma0 M)).relfinrank (IntermediateField.lift (IntermediateField.fixedField ρ.range)) = 1 := by
    have hne : (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    have := hmul
    nth_rewrite 2 [← one_mul ((H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index)] at this
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) this
  have hLe : IntermediateField.lift (IntermediateField.fixedField ρ.range) ≤ (ModularCurve.qExpFunctionFieldC L (CongruenceSubgroup.Gamma0 M)) :=
    IntermediateField.relfinrank_eq_one_iff.mp hone
  have hinv : ∀ x : ↥(ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H)), (∀ γ : CongruenceSubgroup.Gamma0 M, ρ γ x = x) →
      (x : LaurentSeries L) ∈ ModularCurve.qExpFunctionFieldC L (CongruenceSubgroup.Gamma0 M) := by
    intro x hx
    have hmem : x ∈ IntermediateField.fixedField ρ.range := by
      rw [IntermediateField.mem_fixedField_iff]
      rintro _ ⟨γ, rfl⟩
      exact hx γ
    exact hLe ((IntermediateField.mem_lift x).mpr hmem)
  refine ⟨ρ, ?_, hρfix, ?_, hker_iff⟩
  ·
    intro γ k f g f₁ g₁ pf pg pf₁ pg₁ c hc hf hg hf₁ hg₁ ef eg hg0 hg₁0 x hx
    have hxe : x = ⟨ModularCurve.intSeriesC L pf / ModularCurve.intSeriesC L pg,
        ModularCurve.div_mem_qExpFunctionFieldC f g hf hg hg0⟩ := Subtype.ext hx
    rw [hxe]
    exact hρslash γ f g f₁ g₁ c hc hf hg hf₁ hg₁ ef eg hg0 hg₁0
  ·
    intro σ hσ
    letI act : MulSemiringAction ↥ρ.range ↥(ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H)) := MulSemiringAction.compHom _ ρ.range.subtype
    have hsmul : ∀ (g : ↥ρ.range) (x : ↥(ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H))), g • x = (g : _ ≃ₐ[L] _) x := fun _ _ => rfl

    have hfixσ : ∀ x : ↥(ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H)), x ∈ FixedPoints.subfield ↥ρ.range ↥(ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H)) → σ x = x := by
      intro x hx
      apply hσ x
      apply hinv x
      intro γ
      have := hx ⟨ρ γ, ⟨γ, rfl⟩⟩
      exact this
    let σ' : ↥(ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H)) ≃ₐ[FixedPoints.subfield ↥ρ.range ↥(ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H))] ↥(ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H)) :=
      AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun x => hfixσ x.1 x.2)
    obtain ⟨g, hg⟩ := FixedPoints.toAlgAut_surjective ↥ρ.range ↥(ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH M H)) σ'
    obtain ⟨g₁, γ, hγ⟩ := g
    refine ⟨γ, ?_⟩
    apply AlgEquiv.ext
    intro x
    have h1 := congrArg (fun e => e x) hg
    simp only [MulSemiringAction.toAlgAut_apply, MulSemiringAction.toAlgEquiv_apply] at h1

    rw [hγ]
    change g₁ x = σ x at h1
    exact h1.symm

end W1Aux

open scoped MatrixGroups ModularForm in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) :
    ∃ ρ : CongruenceSubgroup.Gamma0 (q ^ 2 * M') →* (↥K ≃ₐ[L] ↥K),

      (∀ (γ : CongruenceSubgroup.Gamma0 (q ^ 2 * M')) {k : ℤ}
          (f g f₁ g₁ : ModularForm (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') : Subgroup (GL (Fin 2) ℝ)) k)
          {pf pg pf₁ pg₁ : PowerSeries ℤ} (c : ℂ), c ≠ 0 →
          ModularCurve.IsIntegralQExp f pf → ModularCurve.IsIntegralQExp g pg →
          ModularCurve.IsIntegralQExp f₁ pf₁ → ModularCurve.IsIntegralQExp g₁ pg₁ →
          (⇑f₁ : UpperHalfPlane → ℂ) = c • ((⇑f : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) →
          (⇑g₁ : UpperHalfPlane → ℂ) = c • ((⇑g : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) →
          ModularCurve.intSeriesC L pg ≠ 0 → ModularCurve.intSeriesC L pg₁ ≠ 0 →
          ∀ x : ↥K, (x : LaurentSeries L) = ModularCurve.intSeriesC L pf / ModularCurve.intSeriesC L pg →
            ((ρ γ x : ↥K) : LaurentSeries L) = ModularCurve.intSeriesC L pf₁ / ModularCurve.intSeriesC L pg₁) ∧

      (∀ (γ : CongruenceSubgroup.Gamma0 (q ^ 2 * M')) (x : ↥K),
          (x : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (q ^ 2 * M')) → ρ γ x = x) ∧

      (∀ σ : ↥K ≃ₐ[L] ↥K,
          (∀ x : ↥K, (x : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (q ^ 2 * M')) → σ x = x) →
          ∃ γ : CongruenceSubgroup.Gamma0 (q ^ 2 * M'), σ = ρ γ) ∧

      (∀ γ : CongruenceSubgroup.Gamma0 (q ^ 2 * M'), ρ γ = 1 ↔
          CohCarrier.gamma0Units (q ^ 2 * M') γ ∈
            ModularCurve.FullLevel.levelH q M' ⊔ Subgroup.zpowers (-1 : (ZMod (q ^ 2 * M'))ˣ)) := by
  have eK : ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) =
      ModularCurve.qExpFunctionFieldC L (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) :=
    ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq L _
  have eK₂ : ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (q ^ 2 * M')) =
      ModularCurve.qExpFunctionFieldC L (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) := by
    rw [← ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull,
      ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq]
  subst hK
  exact W1Aux.core L (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') _ _ eK eK₂

end S_ModularCurve_FullLevel_exists_monoidHom_gamma0_algEquiv_slash_floor_enum_ker_xH_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_monoidHom_gamma0_algEquiv_slash_floor_enum_ker_xH_of_eq_three (solution)
