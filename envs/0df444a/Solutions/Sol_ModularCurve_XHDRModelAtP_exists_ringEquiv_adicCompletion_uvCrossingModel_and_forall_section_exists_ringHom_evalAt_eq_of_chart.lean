-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_ringEquiv_adicCompletion_uvCrossingModel_and_forall_section_exists_ringHom_evalAt_eq_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/97a7d8c2-d05b-51ed-b878-6f9d6ed0ada5

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_UVCrossingModel

import Theorems.Thm_ModularCurve_XHDRModelAtP_isNoetherianRing_stalk_and_exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_of_chart
import Theorems.Thm_ModularCurve_XHDRModelAtP_injective_stalkRead_and_stalkRead_germ_eq_read_chart_and_forall_section_evalAt_stalkRead_eq_of_chart
import Theorems.Thm_ValuationSubring_exists_ringHom_forall_eq_mul_units_and_forall_exists_ringHom_adicCompletion_comp_eq_of_liesOverPrime
import Theorems.Thm_IsLocalRing_exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringEquiv_adicCompletion_uvCrossingModel
import Theorems.Thm_AlgebraicCurve_Place_mk_mem_maximalIdeal_iff
import Theorems.Thm_AlgebraicCurve_Place_evalAt_eq_zero_iff_one_le_ord
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_isRational_section_forall_mem_iff_stalkClosedPointTo_eq_zero_of_isPrime_of_not_mem
import Theorems.Thm_ModularCurve_XHDRModelAtP_forall_exists_isDiscreteValuationRing_specializes_and_mul_stalkRead_eq_stalkRead
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_ringEquiv_adicCompletion_uvCrossingModel_and_forall_section_exists_ringHom_evalAt_eq_of_chart
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial

open scoped MatrixGroups

set_option maxHeartbeats 1600000 in

theorem ntcore
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)

    (jO : O →+* AlgebraicClosure ℚ) (hjO : jO.comp ρO = algebraMap (R p) (AlgebraicClosure ℚ))
    (ιA : O →+* ↥A) (hιA : A.subtype.comp ιA = jO) (hιAκ : (IsLocalRing.residue ↥A).comp ιA = toκ)

    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (e : ℕ) (he : 1 ≤ e) (U : (XO (ΓM M H) hj ρO).Opens) (hxU : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n ∈ U)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e))
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e)))) = U.ι ≫ pullback.snd _ _)
    (hfib : ∀ y : ↥(U : Scheme.{0}),
      (CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∧ CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ↔ U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n)
    (hpt : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
      (f.stalkMap y).hom.Flat ∧ Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧ IsIso (f.residueFieldMap y))
    (het : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n → ∃ V : (U : Scheme.{0}).Opens, y ∈ V ∧ Etale (V.ι ≫ f))
    (hor₁ : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal → U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (hor₂ : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal → U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (hor₃ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal)
    (hor₄ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal)

    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    (σ : O →+* O') (ιA' : O' →+* ↥A) (hσ : ιA'.comp σ = ιA) (hιA'inj : Function.Injective ιA') (hιA'loc : IsLocalHom ιA')
    (jO' : O' →+* AlgebraicClosure ℚ) (hjO' : jO'.comp (σ.comp ρO) = algebraMap (R p) (AlgebraicClosure ℚ)) (hιA'j : A.subtype.comp ιA' = jO')
    (htoκ' : ((IsLocalRing.residue ↥A).comp ιA').comp (σ.comp ρO) = (IsLocalRing.residue ↥A).comp ρ)
    (ϖ' : O') (hϖ' : IsLocalRing.maximalIdeal O' = Ideal.span {ϖ'}) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prJ : XQ ⟶ XO (ΓM M H) hj ρO :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
    letI VM : (𝔛.Meta).C.Opens := 𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ U)
    letI Q := CrossingQuotient O (((p : ℕ) : O) ^ e)
    letI φ : Q →+* Γ(CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
    letI gv : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.V (((p : ℕ) : O) ^ e))))
    letI gu : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.U (((p : ℕ) : O) ^ e))))
    ∀ hgen : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤)),
    letI read : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) →+* ↥(xHFunctionFieldBar M H) :=
      (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
          ((𝔛.eeta.app (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp (prJ.app (U.ι ''ᵁ ⊤)).hom))
    letI param : ↥(xHFunctionFieldBar M H) := read gv
    letI param' : ↥(xHFunctionFieldBar M H) := read gu
    letI bc' := bcMap (ΓM M H) hj (σ.comp ρO) ((IsLocalRing.residue ↥A).comp ιA') htoκ'
    letI xn' : ↥(XO (ΓM M H) hj (σ.comp ρO)) := (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc').base n
    letI prJ' : XQ ⟶ XO (ΓM M H) hj (σ.comp ρO) :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
    letI prσ : XO (ΓM M H) hj (σ.comp ρO) ⟶ XO (ΓM M H) hj ρO :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom σ)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
    letI B := (XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalk xn'
    letI σB : O' →+* ↥B := ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ ⊤ xn' trivial).hom.comp
      (((XO.toBase (ΓM M H) hj (σ.comp ρO)).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)
    ∀ (hsp : prJ'.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ xn'),
    letI emb : ↥B →+* ↥(xHFunctionFieldBar M H) := (𝔛.Meta).ffEquiv.symm.toRingHom.comp
      ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
        ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
          ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes hsp).hom))
    ∀ g : ↥(xHFunctionFieldBar M H), (∃ r s₀ : ↥B, s₀ ≠ 0 ∧ g * emb s₀ = emb r) →
      ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsNoetherianRing B) (_ : IsLocalRing B)
        (σB : O' →+* B) (_ : IsLocalHom σB)
        (emb : B →+* ↥(xHFunctionFieldBar M H)) (_ : Function.Injective emb)
        (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W')
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal W') W')
        (π' : W') (_ : Irreducible π') (E' : ℕ) (_ : 1 ≤ E')
        (ι' : AdicCompletion (IsLocalRing.maximalIdeal B) B ≃+* UVCrossingModel W' (π' ^ E'))
        (w₀ : (UVCrossingModel W' (π' ^ E'))ˣ)
        (_ : ι' (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) (σB ϖ')) = (w₀ : UVCrossingModel W' (π' ^ E')) * UVCrossingModel.const (π' ^ E') π')
        (bu bv : B) (wu : (UVCrossingModel W' (π' ^ E'))ˣ)
        (_ : ι' (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) bu) = UVCrossingModel.U (π' ^ E') * (wu : UVCrossingModel W' (π' ^ E')))
        (_ : ι' (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) bv) = UVCrossingModel.V (π' ^ E'))
        (_ : emb bv = param) (_ : emb bu = param')
        (_ : ∃ r s : B, s ≠ 0 ∧ g * emb s = emb r)

        (S : Type) (_ : CommRing S) (jA : ↥A →+* S)
        (_ : ∀ (α β : ↥A) (u : Sˣ), jA α = jA β * (u : S) → ∃ v : (↥A)ˣ, α = β * (v : ↥A)),

        (∀ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), W.IsRational →
          ∀ (s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})),
            s ≫ U.ι ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA) →
            barPt A ≫ s ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ →
            U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
          ∃ (χ : B →+* ↥A) (ψ : AdicCompletion (IsLocalRing.maximalIdeal B) B →+* S),
          IsLocalHom χ ∧ χ.comp σB = ιA' ∧ ψ.comp (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)) = jA.comp χ ∧
          (∀ b : B, emb b ∈ W.toValuationSubring ∧ W.evalAt (emb b) = ((χ b : ↥A) : AlgebraicClosure ℚ)) ∧
          (∀ (x : ↥(xHFunctionFieldBar M H)), x ∈ W.toValuationSubring → (∃ r s₀ : B, s₀ ≠ 0 ∧ x * emb s₀ = emb r) →
            ∃ r s₀ : B, χ s₀ ≠ 0 ∧ x * emb s₀ = emb r)) ∧

        (∀ P : Ideal B, P.IsPrime → P ≠ ⊥ → σB ϖ' ∉ P →
          ∃ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (_ : W.IsRational)
            (s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0}))
            (_ : s ≫ U.ι ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA))
            (_ : barPt A ≫ s ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ)
            (_ : U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n)
            (χ : B →+* ↥A),
            (IsLocalHom χ ∧ χ.comp σB = ιA' ∧
              (∀ b : B, emb b ∈ W.toValuationSubring ∧ W.evalAt (emb b) = ((χ b : ↥A) : AlgebraicClosure ℚ)) ∧
              (∀ (x : ↥(xHFunctionFieldBar M H)), x ∈ W.toValuationSubring → (∃ r s₀ : B, s₀ ≠ 0 ∧ x * emb s₀ = emb r) →
                ∃ r s₀ : B, χ s₀ ≠ 0 ∧ x * emb s₀ = emb r)) ∧
            ∀ b : B, b ∈ P ↔ χ b = 0) := by
  intro hgen hsp g hgfrac
  have h2 := ModularCurve.XHDRModelAtP.isNoetherianRing_stalk_and_exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_of_chart p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ jO hjO ιA hιA hιAκ n e he U hxU f hover hfib hpt het hor₁ hor₂ hor₃ hor₄ O' σ ιA' hσ hιA'inj hιA'loc jO' hjO' hιA'j htoκ' ϖ' hϖ'
  obtain ⟨hnoeth, hdom, E', hE', W', i1, i2, i3, i4, σ', hmW', hresW', ι', hconst, hmem2, ⟨wu, hbu⟩, hbv⟩ := h2
  have h3 := ModularCurve.XHDRModelAtP.injective_stalkRead_and_stalkRead_germ_eq_read_chart_and_forall_section_evalAt_stalkRead_eq_of_chart p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ jO hjO ιA hιA hιAκ n e he U hxU f hover hfib hpt het hor₁ hor₂ hor₃ hor₄ O' σ ιA' hσ hιA'inj hιA'loc jO' hjO' hιA'j htoκ' hgen hsp
  obtain ⟨⟨hσBloc, hembinj, hconst3⟩, ⟨hmem3, hembv, hembu⟩, hsec⟩ := h3
  have h6 := ModularCurve.XHDRModelAtP.exists_isRational_section_forall_mem_iff_stalkClosedPointTo_eq_zero_of_isPrime_of_not_mem p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ jO hjO ιA hιA hιAκ n U hxU O' σ ιA' hσ hιA'inj hιA'loc jO' hjO' hιA'j htoκ' ϖ' hϖ'
  obtain ⟨S, i5, jA, hdesc, hψall⟩ :=
    ValuationSubring.exists_ringHom_forall_eq_mul_units_and_forall_exists_ringHom_adicCompletion_comp_eq_of_liesOverPrime p A hA
  let XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  let prJ : XQ ⟶ XO (ΓM M H) hj ρO :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
  let VM : (𝔛.Meta).C.Opens := 𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ U)
  let Q := CrossingQuotient O (((p : ℕ) : O) ^ e)
  let φ : Q →+* Γ(CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
  let gv : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.V (((p : ℕ) : O) ^ e))))
  let gu : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.U (((p : ℕ) : O) ^ e))))
  let read : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) →+* ↥(xHFunctionFieldBar M H) :=
    (𝔛.Meta).ffEquiv.symm.toRingHom.comp
      (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
        ((𝔛.eeta.app (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp (prJ.app (U.ι ''ᵁ ⊤)).hom))
  let param : ↥(xHFunctionFieldBar M H) := read gv
  let param' : ↥(xHFunctionFieldBar M H) := read gu
  let bc' := bcMap (ΓM M H) hj (σ.comp ρO) ((IsLocalRing.residue ↥A).comp ιA') htoκ'
  let xn' : ↥(XO (ΓM M H) hj (σ.comp ρO)) := (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc').base n
  let prJ' : XQ ⟶ XO (ΓM M H) hj (σ.comp ρO) :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
  let prσ : XO (ΓM M H) hj (σ.comp ρO) ⟶ XO (ΓM M H) hj ρO :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom σ)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
  let B := (XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalk xn'
  let σB : O' →+* ↥B := ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ ⊤ xn' trivial).hom.comp
    (((XO.toBase (ΓM M H) hj (σ.comp ρO)).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)
  let emb : ↥B →+* ↥(xHFunctionFieldBar M H) := (𝔛.Meta).ffEquiv.symm.toRingHom.comp
    ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
      ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
        ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes hsp).hom))
  haveI : IsNoetherianRing ↥B := hnoeth
  haveI : IsDomain ↥B := hdom
  haveI : IsLocalHom σB := hσBloc
  have hirr : Irreducible (σ' ϖ') := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmW'
  have hϖB : ι' (algebraMap ↥B (AdicCompletion (IsLocalRing.maximalIdeal ↥B) ↥B) (σB ϖ')) =
      ((1 : (UVCrossingModel W' ((σ' ϖ') ^ E'))ˣ) : UVCrossingModel W' ((σ' ϖ') ^ E')) * UVCrossingModel.const ((σ' ϖ') ^ E') (σ' ϖ') := by
    rw [Units.val_one, one_mul]; exact hconst ϖ'
  have hϖ0 : ϖ' ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field O'
    rw [hϖ', h0, Ideal.span_singleton_eq_bot]

  have hlocal : ∀ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), W.IsRational →
      ∀ (s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})),
        s ≫ U.ι ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA) →
        barPt A ≫ s ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ →
        U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
      ∀ (s' : Spec (CommRingCat.of ↥A) ⟶ XO (ΓM M H) hj (σ.comp ρO)),
        s' ≫ pullback.fst _ _ = s ≫ U.ι ≫ pullback.fst _ _ → s' ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA') →
        ∀ (hx : s'.base (IsLocalRing.closedPoint ↥A) = xn'),
        letI χ : ↥B →+* ↥A :=
          (Scheme.stalkClosedPointTo s').hom.comp ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes (specializes_of_eq hx)).hom
        (IsLocalHom χ ∧ χ.comp σB = ιA' ∧
          (∀ b : ↥B, emb b ∈ W.toValuationSubring ∧ W.evalAt (emb b) = ((χ b : ↥A) : AlgebraicClosure ℚ))) →
        ∀ (x : ↥(xHFunctionFieldBar M H)), x ∈ W.toValuationSubring → (∃ r s₀ : ↥B, s₀ ≠ 0 ∧ x * emb s₀ = emb r) →
          ∃ r s₀ : ↥B, χ s₀ ≠ 0 ∧ x * emb s₀ = emb r := by
    intro W hrat s hs1 hs2 hs3 s' hs'1 hs'2 hx hχ x hxW hxfrac
    let χ : ↥B →+* ↥A := (Scheme.stalkClosedPointTo s').hom.comp ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes (specializes_of_eq hx)).hom
    obtain ⟨hχloc, hχcomp, hχev⟩ := hχ
    have hPm : RingHom.ker χ ≠ IsLocalRing.maximalIdeal ↥B := by
      intro hk
      have h1 : σB ϖ' ∈ IsLocalRing.maximalIdeal ↥B := map_nonunit σB ϖ' (by rw [hϖ']; exact Ideal.subset_span rfl)
      rw [← hk, RingHom.mem_ker] at h1
      have h2 : χ (σB ϖ') = ιA' ϖ' := RingHom.congr_fun hχcomp ϖ'
      rw [h1] at h2
      exact hϖ0 (hιA'inj (by rw [map_zero]; exact h2.symm))
    have hP : ∀ b : ↥B, b ∈ RingHom.ker χ ↔ emb b ∈ (W.toValuationSubring).nonunits := by
      intro b
      rw [RingHom.mem_ker, ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
      constructor
      · intro hb
        refine ⟨(hχev b).1, ?_⟩
        rw [AlgebraicCurve.Place.mk_mem_maximalIdeal_iff]
        by_cases h0 : emb b = 0
        · exact Or.inl h0
        · right
          have h1 := (AlgebraicCurve.Place.evalAt_eq_zero_iff_one_le_ord W hrat h0 (hχev b).1).mp (by rw [(hχev b).2, hb]; rfl)
          omega
      · rintro ⟨hm, hmax⟩
        rw [AlgebraicCurve.Place.mk_mem_maximalIdeal_iff] at hmax
        rcases hmax with h0 | hpos
        · have hb0 : b = 0 := hembinj (by rw [h0, map_zero])
          rw [hb0, map_zero]
        · have h0 : emb b ≠ 0 := fun h => by rw [h, AlgebraicCurve.Place.ord_zero] at hpos; exact lt_irrefl _ hpos
          have h1 := (AlgebraicCurve.Place.evalAt_eq_zero_iff_one_le_ord W hrat h0 (hχev b).1).mpr (by omega)
          rw [(hχev b).2] at h1
          exact_mod_cast h1
    obtain ⟨r, s₀, hs₀, hxr⟩ :=
      IsLocalRing.exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringEquiv_adicCompletion_uvCrossingModel
        (σ' ϖ') hirr E' hE' ι' emb hembinj W.toValuationSubring (fun b => (hχev b).1) (RingHom.ker χ) hP hPm x hxW hxfrac
    exact ⟨r, s₀, fun h => hs₀ (RingHom.mem_ker.mpr h), hxr⟩
  refine ⟨↥B, inferInstance, hdom, hnoeth, inferInstance, σB, hσBloc, emb, hembinj, W', i1, i2, i3, i4, σ' ϖ', hirr, E', hE', ι', 1, hϖB,
    ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ (prσ ⁻¹ᵁ (U.ι ''ᵁ ⊤)) xn' hmem2).hom ((prσ.app (U.ι ''ᵁ ⊤)).hom gu),
    ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ (prσ ⁻¹ᵁ (U.ι ''ᵁ ⊤)) xn' hmem2).hom ((prσ.app (U.ι ''ᵁ ⊤)).hom gv),
    wu, hbu, hbv, hembv, hembu, hgfrac, S, i5, jA, hdesc, ?_, ?_⟩
  ·
    intro W hrat s hs1 hs2 hs3
    have hw : (s ≫ U.ι ≫ pullback.fst _ _) ≫ toBase p (ΓM M H) hj =
        Spec.map (CommRingCat.ofHom ιA') ≫ Spec.map (CommRingCat.ofHom (σ.comp ρO)) := by
      simp only [Category.assoc]
      rw [pullback.condition, reassoc_of% hs1, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hσ]
    let s' : Spec (CommRingCat.of ↥A) ⟶ XO (ΓM M H) hj (σ.comp ρO) := pullback.lift (s ≫ U.ι ≫ pullback.fst _ _) (Spec.map (CommRingCat.ofHom ιA')) hw
    have hs'1 : s' ≫ pullback.fst _ _ = s ≫ U.ι ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
    have hs'2 : s' ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA') := pullback.lift_snd _ _ _
    obtain ⟨hx, hχ⟩ := hsec W hrat s hs1 hs2 hs3 s' hs'1 hs'2
    obtain ⟨hχloc, hχcomp, hχev⟩ := hχ
    obtain ⟨ψ, hψ⟩ := hψall ↥B _ hχloc
    exact ⟨_, ψ, hχloc, hχcomp, hψ, hχev, hlocal W hrat s hs1 hs2 hs3 s' hs'1 hs'2 hx ⟨hχloc, hχcomp, hχev⟩⟩
  ·
    intro P hP hP0 hϖP
    specialize h6 P hP hP0 hϖP
    obtain ⟨W, hrat, s, hs1, hs2, hs3, hker⟩ := h6
    have hw : (s ≫ U.ι ≫ pullback.fst _ _) ≫ toBase p (ΓM M H) hj =
        Spec.map (CommRingCat.ofHom ιA') ≫ Spec.map (CommRingCat.ofHom (σ.comp ρO)) := by
      simp only [Category.assoc]
      rw [pullback.condition, reassoc_of% hs1, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hσ]
    let s' : Spec (CommRingCat.of ↥A) ⟶ XO (ΓM M H) hj (σ.comp ρO) := pullback.lift (s ≫ U.ι ≫ pullback.fst _ _) (Spec.map (CommRingCat.ofHom ιA')) hw
    have hs'1 : s' ≫ pullback.fst _ _ = s ≫ U.ι ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
    have hs'2 : s' ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA') := pullback.lift_snd _ _ _
    obtain ⟨hx, hχ⟩ := hsec W hrat s hs1 hs2 hs3 s' hs'1 hs'2
    obtain ⟨hχloc, hχcomp, hχev⟩ := hχ
    exact ⟨W, hrat, s, hs1, hs2, hs3, _, ⟨hχloc, hχcomp, hχev, hlocal W hrat s hs1 hs2 hs3 s' hs'1 hs'2 hx ⟨hχloc, hχcomp, hχev⟩⟩,
      hker s' hs'1 hs'2 hx⟩

set_option maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)

    (jO : O →+* AlgebraicClosure ℚ) (hjO : jO.comp ρO = algebraMap (R p) (AlgebraicClosure ℚ))
    (ιA : O →+* ↥A) (hιA : A.subtype.comp ιA = jO) (hιAκ : (IsLocalRing.residue ↥A).comp ιA = toκ)

    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (e : ℕ) (he : 1 ≤ e) (U : (XO (ΓM M H) hj ρO).Opens) (hxU : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n ∈ U)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e))
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e)))) = U.ι ≫ pullback.snd _ _)
    (hfib : ∀ y : ↥(U : Scheme.{0}),
      (CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∧ CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ↔ U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n)
    (hpt : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
      (f.stalkMap y).hom.Flat ∧ Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧ IsIso (f.residueFieldMap y))
    (het : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n → ∃ V : (U : Scheme.{0}).Opens, y ∈ V ∧ Etale (V.ι ≫ f))
    (hor₁ : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal → U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (hor₂ : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal → U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (hor₃ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal)
    (hor₄ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prJ : XQ ⟶ XO (ΓM M H) hj ρO :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
    letI VM : (𝔛.Meta).C.Opens := 𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ U)
    letI Q := CrossingQuotient O (((p : ℕ) : O) ^ e)
    letI φ : Q →+* Γ(CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
    letI gv : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.V (((p : ℕ) : O) ^ e))))
    letI gu : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.U (((p : ℕ) : O) ^ e))))
    ∀ hgen : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤)),
    letI read : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) →+* ↥(xHFunctionFieldBar M H) :=
      (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
          ((𝔛.eeta.app (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp (prJ.app (U.ι ''ᵁ ⊤)).hom))
    letI param : ↥(xHFunctionFieldBar M H) := read gv
    letI param' : ↥(xHFunctionFieldBar M H) := read gu
    ∀ g : ↥(xHFunctionFieldBar M H),
      ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
        (ϖ' : O') (_ : IsLocalRing.maximalIdeal O' = Ideal.span {ϖ'})
        (ιA' : O' →+* ↥A) (_ : Function.Injective ιA') (_ : IsLocalHom ιA')
        (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsNoetherianRing B) (_ : IsLocalRing B)
        (σB : O' →+* B) (_ : IsLocalHom σB)
        (emb : B →+* ↥(xHFunctionFieldBar M H)) (_ : Function.Injective emb)
        (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W')
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal W') W')
        (π' : W') (_ : Irreducible π') (E' : ℕ) (_ : 1 ≤ E')
        (ι' : AdicCompletion (IsLocalRing.maximalIdeal B) B ≃+* UVCrossingModel W' (π' ^ E'))
        (w₀ : (UVCrossingModel W' (π' ^ E'))ˣ)
        (_ : ι' (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) (σB ϖ')) = (w₀ : UVCrossingModel W' (π' ^ E')) * UVCrossingModel.const (π' ^ E') π')
        (bu bv : B) (wu : (UVCrossingModel W' (π' ^ E'))ˣ)
        (_ : ι' (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) bu) = UVCrossingModel.U (π' ^ E') * (wu : UVCrossingModel W' (π' ^ E')))
        (_ : ι' (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) bv) = UVCrossingModel.V (π' ^ E'))
        (_ : emb bv = param) (_ : emb bu = param')
        (_ : ∃ r s : B, s ≠ 0 ∧ g * emb s = emb r)

        (S : Type) (_ : CommRing S) (jA : ↥A →+* S)
        (_ : ∀ (α β : ↥A) (u : Sˣ), jA α = jA β * (u : S) → ∃ v : (↥A)ˣ, α = β * (v : ↥A)),

        (∀ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), W.IsRational →
          ∀ (s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})),
            s ≫ U.ι ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA) →
            barPt A ≫ s ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ →
            U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
          ∃ (χ : B →+* ↥A) (ψ : AdicCompletion (IsLocalRing.maximalIdeal B) B →+* S),
          IsLocalHom χ ∧ χ.comp σB = ιA' ∧ ψ.comp (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)) = jA.comp χ ∧
          (∀ b : B, emb b ∈ W.toValuationSubring ∧ W.evalAt (emb b) = ((χ b : ↥A) : AlgebraicClosure ℚ)) ∧
          (∀ (x : ↥(xHFunctionFieldBar M H)), x ∈ W.toValuationSubring → (∃ r s₀ : B, s₀ ≠ 0 ∧ x * emb s₀ = emb r) →
            ∃ r s₀ : B, χ s₀ ≠ 0 ∧ x * emb s₀ = emb r)) ∧

        (∀ P : Ideal B, P.IsPrime → P ≠ ⊥ → σB ϖ' ∉ P →
          ∃ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (_ : W.IsRational)
            (s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0}))
            (_ : s ≫ U.ι ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA))
            (_ : barPt A ≫ s ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ)
            (_ : U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n)
            (χ : B →+* ↥A),
            (IsLocalHom χ ∧ χ.comp σB = ιA' ∧
              (∀ b : B, emb b ∈ W.toValuationSubring ∧ W.evalAt (emb b) = ((χ b : ↥A) : AlgebraicClosure ℚ)) ∧
              (∀ (x : ↥(xHFunctionFieldBar M H)), x ∈ W.toValuationSubring → (∃ r s₀ : B, s₀ ≠ 0 ∧ x * emb s₀ = emb r) →
                ∃ r s₀ : B, χ s₀ ≠ 0 ∧ x * emb s₀ = emb r)) ∧
            ∀ b : B, b ∈ P ↔ χ b = 0) := by
  intro hgen g
  obtain ⟨O', i1, i2, i3, σ, ιA', hσ, hinj, hloc, jO', hjO', hιA'j, htoκ', hsp, r, s₀, hs₀, hg⟩ :=
    ModularCurve.XHDRModelAtP.forall_exists_isDiscreteValuationRing_specializes_and_mul_stalkRead_eq_stalkRead p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ jO hjO ιA hιA hιAκ n g
  obtain ⟨ϖ', hϖ'irr⟩ := IsDiscreteValuationRing.exists_irreducible O'
  have hϖ' : IsLocalRing.maximalIdeal O' = Ideal.span {ϖ'} := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hϖ'irr
  exact ⟨O', i1, i2, i3, ϖ', hϖ', ιA', hinj, hloc,
    ntcore p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ jO hjO ιA hιA hιAκ n e he U hxU f hover hfib hpt het hor₁ hor₂ hor₃ hor₄ O' σ ιA' hσ hinj hloc jO' hjO' hιA'j htoκ' ϖ' hϖ' hgen hsp g ⟨r, s₀, hs₀, hg⟩⟩

end S_ModularCurve_XHDRModelAtP_exists_ringEquiv_adicCompletion_uvCrossingModel_and_forall_section_exists_ringHom_evalAt_eq_of_chart
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_ringEquiv_adicCompletion_uvCrossingModel_and_forall_section_exists_ringHom_evalAt_eq_of_chart (solution)
