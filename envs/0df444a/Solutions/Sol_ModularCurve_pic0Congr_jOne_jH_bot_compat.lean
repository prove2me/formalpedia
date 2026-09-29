-- Prove2me | solution 1 for ModularCurve.pic0Congr_jOne_jH_bot_compat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/252f461a-acee-547f-961d-b00d6915c2c8

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_pic0Congr_jOne_jH_bot_compat

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_pic0Congr_jOne_jH_bot_compat.ModularCurve HahnSeries IntermediateField CongruenceSubgroup UpperHalfPlane"

open scoped MatrixGroups ModularForm Pointwise

namespace ES1Sol

local notation "Qb" => AlgebraicClosure ℚ

abbrev FF (L : Type*) [Field L] [Algebra ℚ L] (Γ : Subgroup SL(2, ℤ)) :
    IntermediateField L (LaurentSeries L) :=
  laurentBaseChange L (qExpFunctionFieldC ℚ Γ)

abbrev JJ (Γ : Subgroup SL(2, ℤ)) : Type _ := Pic0 Qb (FF Qb Γ)

example (M : ℕ) : JOne M = JJ (Gamma1 M) := rfl
example (M : ℕ) (H : Subgroup (ZMod M)ˣ) : JH M H = JJ (CohCarrier.GammaH M H) := rfl

section Supply

variable (L : Type*) [Field L] [Algebra ℚ L]

theorem laurentBaseChange_mono {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)}
    (h : F₀ ≤ F₁) : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

theorem qExpand_mem_laurentBaseChange {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} (n : ℕ)
    [NeZero n] {F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (hF : ∀ y ∈ F₀, qExpand ℚ n y ∈ F₁)
    {x : LaurentSeries L} (hx : x ∈ laurentBaseChange L F₀) :
    qExpand L n x ∈ laurentBaseChange L F₁ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero,
          ← algebraMap_laurentSeries_eq_single]
        exact (laurentBaseChange L F₁).algebraMap_mem _
      · rw [coeffEmb, ← coeffMap_qExpand]
        exact coeffEmb_mem_laurentBaseChange L (hF z hz)
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

end Supply

section Hecke

variable (L : Type*) [Field L] [Algebra ℚ L]

def gAlpha (Γ : Subgroup SL(2, ℤ)) (t : ℕ) : FF L Γ →ₐ[L] FF L (Γ ⊓ Gamma0 t) :=
  IntermediateField.inclusion (laurentBaseChange_mono L (qExpFunctionFieldC_mono ℚ inf_le_left))

def gBeta (Γ : Subgroup SL(2, ℤ)) (t ℓ : ℕ) [NeZero ℓ]
    (h : ∀ y ∈ qExpFunctionFieldC ℚ Γ, qExpand ℚ ℓ y ∈ qExpFunctionFieldC ℚ (Γ ⊓ Gamma0 t)) :
    FF L Γ →ₐ[L] FF L (Γ ⊓ Gamma0 t) where
  toFun x := ⟨qExpand L ℓ (x : LaurentSeries L), qExpand_mem_laurentBaseChange L ℓ h x.2⟩
  map_one' := Subtype.ext (map_one (qExpand L ℓ))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand L ℓ) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand L ℓ))
  map_add' _ _ := Subtype.ext (map_add (qExpand L ℓ) _ _)
  commutes' a := Subtype.ext <| by
    show qExpand L ℓ (algebraMap L (LaurentSeries L) a) = algebraMap L (LaurentSeries L) a
    rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

theorem gAlpha_heq {Γ Γ' : Subgroup SL(2, ℤ)} (e : Γ = Γ') (t : ℕ) :
    HEq (gAlpha L Γ t) (gAlpha L Γ' t) := by
  subst e; rfl

theorem gBeta_heq {Γ Γ' : Subgroup SL(2, ℤ)} (e : Γ = Γ') (t ℓ : ℕ) [NeZero ℓ]
    (h : ∀ y ∈ qExpFunctionFieldC ℚ Γ, qExpand ℚ ℓ y ∈ qExpFunctionFieldC ℚ (Γ ⊓ Gamma0 t))
    (h' : ∀ y ∈ qExpFunctionFieldC ℚ Γ', qExpand ℚ ℓ y ∈ qExpFunctionFieldC ℚ (Γ' ⊓ Gamma0 t)) :
    HEq (gBeta L Γ t ℓ h) (gBeta L Γ' t ℓ h') := by
  subst e; rfl

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]

theorem heckeAlphaOneBar_eq : heckeAlphaOneBar L M ℓ = gAlpha L (Gamma1 M) (M * ℓ) := rfl

theorem heckeAlphaHBar_eq : heckeAlphaHBar L M H ℓ = gAlpha L (CohCarrier.GammaH M H) (M * ℓ) := rfl

theorem heckeBetaOneBar_eq' (h0 : HeckeBetaOneDefined M ℓ) :
    heckeBetaOneBar L M ℓ = gBeta L (Gamma1 M) (M * ℓ) ℓ h0 := by
  rw [heckeBetaOneBar_eq M ℓ h0]
  rfl

theorem heckeBetaHBar_eq' (h0 : HeckeBetaHDefined M H ℓ) :
    heckeBetaHBar L M H ℓ = gBeta L (CohCarrier.GammaH M H) (M * ℓ) ℓ h0 := by
  rw [heckeBetaHBar_eq M H ℓ h0]
  rfl

theorem correspondence_heq {Γ Γ' : Subgroup SL(2, ℤ)} (e : Γ = Γ') (t : ℕ)
    (α β : FF L Γ →ₐ[L] FF L (Γ ⊓ Gamma0 t)) (α' β' : FF L Γ' →ₐ[L] FF L (Γ' ⊓ Gamma0 t))
    (eα : HEq α α') (eβ : HEq β β')
    [i : HasPrincipalDivisors L (FF L (Γ ⊓ Gamma0 t))]
    [i' : HasPrincipalDivisors L (FF L (Γ' ⊓ Gamma0 t))]
    (hβ : β.toRingHom.IsIntegral) (hα : α.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong L β hβ) (hfin : FiniteAlong L α)
    (hN : NormFormulaAlong L α hfin)
    (hβ' : β'.toRingHom.IsIntegral) (hα' : α'.toRingHom.IsIntegral)
    (hFI' : FundamentalIdentityAlong L β' hβ') (hfin' : FiniteAlong L α')
    (hN' : NormFormulaAlong L α' hfin') :
    HEq (⇑(Pic0.correspondence β α hβ hα hFI hfin hN))
      (⇑(Pic0.correspondence β' α' hβ' hα' hFI' hfin' hN')) := by
  subst e
  cases eα
  cases eβ
  rfl

theorem heckeAlpha_heq : HEq (heckeAlphaHBar L M ⊥ ℓ) (heckeAlphaOneBar L M ℓ) := by
  rw [heckeAlphaHBar_eq, heckeAlphaOneBar_eq]
  exact gAlpha_heq L (GammaH_bot M) _

theorem heckeBeta_heq (h0 : HeckeBetaHDefined M ⊥ ℓ) (h0' : HeckeBetaOneDefined M ℓ) :
    HEq (heckeBetaHBar L M ⊥ ℓ) (heckeBetaOneBar L M ℓ) := by
  rw [heckeBetaHBar_eq' L M ⊥ ℓ h0, heckeBetaOneBar_eq' L M ℓ h0']
  exact gBeta_heq L (GammaH_bot M) _ _ _ _

theorem heckeOperator_heq (hinH : HeckeInputsHAlong L M ⊥ ℓ) (hin1 : HeckeInputsOneAlong L M ℓ) :
    HEq (⇑(heckeOperatorHAlong L M ⊥ ℓ)) (⇑(heckeOperatorOneAlong L M ℓ)) := by
  obtain ⟨h0, hα, hβ, hP, hfin, hFI, hN⟩ := hinH
  obtain ⟨h0', hα', hβ', hP', hfin', hFI', hN'⟩ := hin1
  rw [heckeOperatorHAlong_eq h0 hα hβ hFI hfin hN, heckeOperatorOneAlong_eq h0' hα' hβ' hFI' hfin' hN']
  exact correspondence_heq L (GammaH_bot M) (M * ℓ) (heckeAlphaHBar L M ⊥ ℓ) (heckeBetaHBar L M ⊥ ℓ)
    (heckeAlphaOneBar L M ℓ) (heckeBetaOneBar L M ℓ) (heckeAlpha_heq L M ℓ)
    (heckeBeta_heq L M ℓ h0 h0') (i := hP) (i' := hP') hβ hα hFI hfin hN hβ' hα' hFI' hfin' hN'

end Hecke

section Diamond

def IsDiaGen (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (d : (ZMod M)ˣ) (σ : FF Qb Γ ≃ₐ[Qb] FF Qb Γ) : Prop :=
  ∀ (k : ℤ) (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) (γ : SL(2, ℤ)), γ ∈ Gamma0 M → ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) →
      ∃ y : LaurentSeries ℚ, y ∈ qExpFunctionFieldC ℚ Γ ∧
        ((σ ⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : FF Qb Γ) :
            LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) y ∧
        coeffMap (algebraMap ℚ ℂ) y *
            HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ))) =
          HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] (γ : GL (Fin 2) ℝ)))

theorem isDiamondAutHBar_iff_isDiaGen (M : ℕ) (H : Subgroup (ZMod M)ˣ) (d : (ZMod M)ˣ)
    (σ : xHFunctionFieldBar M H ≃ₐ[Qb] xHFunctionFieldBar M H) :
    IsDiamondAutHBar M H d σ ↔ IsDiaGen M (CohCarrier.GammaH M H) d σ :=
  Iff.rfl

theorem exists_heq_isDiaGen (M : ℕ) (H : Subgroup (ZMod M)ˣ) (hinH : HeckeDiamondInputsHAll M H)
    {Γ' : Subgroup SL(2, ℤ)} (e : CohCarrier.GammaH M H = Γ') (d : (ZMod M)ˣ) :
    ∃ σ' : FF Qb Γ' ≃ₐ[Qb] FF Qb Γ', HEq (diamondAutHBar M H d) σ' ∧ IsDiaGen M Γ' d σ' := by
  subst e
  exact ⟨_, HEq.rfl, hinH.isDiamondAutHBar d⟩

variable {M : ℕ}

abbrev Γ1 (M : ℕ) : Subgroup (GL (Fin 2) ℝ) := ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 M := by
  rw [← GammaH_bot M]
  exact translation_mem_GammaH M ⊥

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ1 M).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 (M := M))]
  exact AddSubgroup.mem_zmultiples _

theorem conj_mem_Gamma1 {γ δ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hδ : δ ∈ Gamma1 M) :
    γ * δ * γ⁻¹ ∈ Gamma1 M := by
  rw [← GammaH_bot M] at hδ ⊢
  exact CohCarrier.conj_mem_GammaH M ⊥ ⟨γ, hγ⟩ ⟨δ, hδ⟩

theorem le_conj {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    Γ1 M ≤ ConjAct.toConjAct ((γ : GL (Fin 2) ℝ))⁻¹ • Γ1 M := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  exact ⟨γ * δ * γ⁻¹, conj_mem_Gamma1 hγ hδ, by simp; rfl⟩

def slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (Γ1 M) k) :
    ModularForm (Γ1 M) k :=
  restrictForm (le_conj hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))

@[scoped simp]
theorem coe_slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (Γ1 M) k) :
    ⇑(slashForm γ hγ f) = ⇑f ∣[k] (γ : GL (Fin 2) ℝ) := rfl

theorem slashForm_slashForm {k : ℤ} (γ δ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hδ : δ ∈ Gamma0 M)
    (f : ModularForm (Γ1 M) k) :
    slashForm δ hδ (slashForm γ hγ f) = slashForm (γ * δ) (mul_mem hγ hδ) f := by
  ext τ
  simp only [coe_slashForm, map_mul, SlashAction.slash_mul]

theorem slashForm_of_mem {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγ1 : γ ∈ Gamma1 M)
    (f : ModularForm (Γ1 M) k) : slashForm γ hγ f = f := by
  ext τ
  exact congrFun (SlashInvariantForm.slash_action_eqn f _
    (Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) hγ1)) τ

theorem slashForm_one {k : ℤ} (f : ModularForm (Γ1 M) k) : slashForm 1 (one_mem _) f = f :=
  slashForm_of_mem 1 _ (one_mem _) f

theorem slashForm_congr {k : ℤ} {γ γ' : SL(2, ℤ)} (h : γ = γ') (hγ : γ ∈ Gamma0 M) (hγ' : γ' ∈ Gamma0 M)
    (f : ModularForm (Γ1 M) k) : slashForm γ hγ f = slashForm γ' hγ' f := by
  subst h; rfl

theorem slashForm_inv_slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (Γ1 M) k) :
    slashForm γ⁻¹ (inv_mem hγ) (slashForm γ hγ f) = f := by
  rw [slashForm_slashForm, slashForm_congr (mul_inv_cancel γ) _ (one_mem _), slashForm_one]

theorem slashForm_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {f : ModularForm (Γ1 M) k}
    (hf : f ≠ 0) : slashForm γ hγ f ≠ 0 := by
  intro h
  apply hf
  rw [← slashForm_inv_slashForm γ hγ f, h]
  ext τ
  simp [coe_slashForm]

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem qC_eq_zero_iff {k : ℤ} (f : ModularForm (Γ1 M) k) : qC f = 0 ↔ f = 0 := by
  rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

abbrev ιC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

theorem ιC_injective : Function.Injective ιC :=
  RingHom.injective _

theorem ιC_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    ιC (intSeriesC ℚ p) = qC F := by
  rw [qC, ← h]
  ext n
  simp only [intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

theorem qC_ιC_ne_zero {k : ℤ} {g : ModularForm (Γ1 M) k} {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) : qC g ≠ 0 := by
  rw [← ιC_intSeriesC hg]
  exact (map_ne_zero_iff _ ιC_injective).mpr hg0

theorem ne_zero_of_intSeriesC_ne_zero {k : ℤ} {g : ModularForm (Γ1 M) k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : g ≠ 0 :=
  fun h => qC_ιC_ne_zero hg hg0 ((qC_eq_zero_iff g).mpr h)

theorem qC_slashForm_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {g : ModularForm (Γ1 M) k}
    {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    qC (slashForm γ hγ g) ≠ 0 := fun h =>
  slashForm_ne_zero γ hγ (ne_zero_of_intSeriesC_ne_zero hg hg0) ((qC_eq_zero_iff _).mp h)

def iota (Γ : Subgroup SL(2, ℤ)) : qExpFunctionFieldC ℚ Γ →+* FF Qb Γ where
  toFun y := ⟨coeffEmb Qb (y : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb y.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem coeffEmb_algebraMap (c : ℚ) :
    coeffEmb Qb (algebraMap ℚ (LaurentSeries ℚ) c) = algebraMap Qb (LaurentSeries Qb) (algebraMap ℚ Qb c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single]

variable [NeZero M]

theorem eq_diamondAutBar (hin : HeckeDiamondInputsAll M) {d : ℕ} (hd : d.Coprime M)
    (σ' : FF Qb (Gamma1 M) ≃ₐ[Qb] FF Qb (Gamma1 M))
    (hσ' : IsDiaGen M (Gamma1 M) (ZMod.unitOfCoprime d hd) σ') : σ' = diamondAutBar M d := by
  obtain ⟨hex, hexb⟩ := hin.2 d hd
  have hda : IsDiamondAut M d (diamondAut M d) := isDiamondAut_diamondAut hex
  have hbc : IsBaseChangeAutOf Qb (diamondAut M d) (diamondAutBar M d) :=
    isBaseChangeAutOf_baseChangeAut hexb

  obtain ⟨γd, hγd⟩ := CohCarrier.gamma0Units_surjective M (ZMod.unitOfCoprime d hd)⁻¹
  have hγ : (γd : SL(2, ℤ)) ∈ Gamma0 M := γd.2
  have hγ00 : (((γd : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
    have h1 : (CohCarrier.gamma0Units M γd)⁻¹ = ZMod.unitOfCoprime d hd := by rw [hγd, inv_inv]
    have h2 : ((CohCarrier.gamma0Units M γd)⁻¹ : (ZMod M)ˣ).val = ((d : ℕ) : ZMod M) := by
      rw [h1, ZMod.coe_unitOfCoprime]
    exact h2
  have hγ00' : (((γd : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = ((ZMod.unitOfCoprime d hd : (ZMod M)ˣ) : ZMod M) := by
    rw [hγ00, ZMod.coe_unitOfCoprime]

  set F₀ := qExpFunctionFieldC ℚ (Gamma1 M) with hF₀
  set σ₀ : F₀ ≃ₐ[ℚ] F₀ := diamondAut M d with hσ₀
  let φ₁ : F₀ →+* LaurentSeries Qb :=
    (SubringClass.subtype (FF Qb (Gamma1 M))).comp
      (σ'.toRingEquiv.toRingHom.comp (iota (Gamma1 M)))
  let φ₂ : F₀ →+* LaurentSeries Qb :=
    (coeffEmb Qb).comp ((SubringClass.subtype F₀).comp σ₀.toRingEquiv.toRingHom)
  have φ₁def : ∀ y : F₀, φ₁ y = ((σ' (iota (Gamma1 M) y) : FF Qb (Gamma1 M)) : LaurentSeries Qb) :=
    fun _ => rfl
  have φ₂def : ∀ y : F₀, φ₂ y = coeffEmb Qb ((σ₀ y : F₀) : LaurentSeries ℚ) := fun _ => rfl
  have hφ : ∀ (x : LaurentSeries ℚ) (hx : x ∈ F₀), φ₁ ⟨x, hx⟩ = φ₂ ⟨x, hx⟩ := by
    intro x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
        rw [φ₁def, φ₂def]
        obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
        obtain ⟨w, hw, hσw, hwslash⟩ := hσ' k f g pf pg hf hg hg0 γd hγ hγ00'
        have hda' := hda.2 k f g pf pg hf hg hg0 γd hγ hγ00
        have hQ : qC (⇑(slashForm (γd : SL(2, ℤ)) hγ g)) ≠ 0 := qC_slashForm_ne_zero _ hγ hg hg0
        have hcancel : ιC w = ιC ((σ₀ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg,
            div_mem_qExpFunctionFieldC f g hf hg hg0⟩ : F₀) : LaurentSeries ℚ) := by
          apply mul_right_cancel₀ hQ
          exact hwslash.trans hda'.symm
        have hw' : w = ((σ₀ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg,
            div_mem_qExpFunctionFieldC f g hf hg hg0⟩ : F₀) : LaurentSeries ℚ) := ιC_injective hcancel
        rw [← hw']
        exact hσw
    | algebraMap c =>
        have key : ∀ y : F₀, (y : LaurentSeries ℚ) = (c : LaurentSeries ℚ) → φ₁ y = φ₂ y := by
          intro y hy
          have : y = (c : F₀) := Subtype.ext (hy.trans (SubfieldClass.coe_ratCast F₀ c).symm)
          rw [this, map_ratCast, map_ratCast]
        exact key _ (eq_ratCast _ c)
    | add x y hx hy ihx ihy =>
        show φ₁ (⟨x, hx⟩ + ⟨y, hy⟩) = φ₂ (⟨x, hx⟩ + ⟨y, hy⟩)
        rw [map_add, map_add, ihx, ihy]
    | inv x hx ih =>
        show φ₁ (⟨x, hx⟩⁻¹) = φ₂ (⟨x, hx⟩⁻¹)
        rw [map_inv₀, map_inv₀, ih]
    | mul x y hx hy ihx ihy =>
        show φ₁ (⟨x, hx⟩ * ⟨y, hy⟩) = φ₂ (⟨x, hx⟩ * ⟨y, hy⟩)
        rw [map_mul, map_mul, ihx, ihy]
  have hσ'bc : IsBaseChangeAutOf Qb σ₀ σ' := fun y => by
    have := hφ y.1 y.2
    rw [φ₁def, φ₂def] at this
    exact this

  apply AlgEquiv.ext
  intro z
  obtain ⟨z, hz⟩ := z
  induction hz using IntermediateField.adjoin_induction with
  | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact Subtype.ext ((hσ'bc ⟨y, hy⟩).trans (hbc ⟨y, hy⟩).symm)
  | algebraMap c =>
      have : (⟨algebraMap Qb (LaurentSeries Qb) c, IntermediateField.algebraMap_mem _ c⟩ :
          FF Qb (Gamma1 M)) = algebraMap Qb (FF Qb (Gamma1 M)) c := rfl
      rw [this, AlgEquiv.commutes]
      exact ((diamondAutBar M d).commutes c).symm
  | add x y hx hy ihx ihy =>
      show σ' (⟨x, hx⟩ + ⟨y, hy⟩) = diamondAutBar M d (⟨x, hx⟩ + ⟨y, hy⟩)
      rw [map_add, map_add, ihx, ihy]
      rfl
  | inv x hx ih =>
      show σ' (⟨x, hx⟩⁻¹) = diamondAutBar M d (⟨x, hx⟩⁻¹)
      rw [map_inv₀, map_inv₀, ih]
      rfl
  | mul x y hx hy ihx ihy =>
      show σ' (⟨x, hx⟩ * ⟨y, hy⟩) = diamondAutBar M d (⟨x, hx⟩ * ⟨y, hy⟩)
      rw [map_mul, map_mul, ihx, ihy]
      rfl

theorem diamondAut_heq (hin : HeckeDiamondInputsAll M) (hinH : HeckeDiamondInputsHAll M ⊥)
    {d : ℕ} (hd : d.Coprime M) :
    HEq (diamondAutHBar M ⊥ (ZMod.unitOfCoprime d hd)) (diamondAutBar M d) := by
  obtain ⟨σ', hσ', hgen⟩ := exists_heq_isDiaGen M ⊥ hinH (GammaH_bot M) (ZMod.unitOfCoprime d hd)
  exact hσ'.trans (heq_of_eq (eq_diamondAutBar hin hd σ' hgen))

end Diamond

section Smul

theorem smul_heq {Γ Γ' : Subgroup SL(2, ℤ)} (e : Γ = Γ') (σ : FF Qb Γ ≃ₐ[Qb] FF Qb Γ)
    (σ' : FF Qb Γ' ≃ₐ[Qb] FF Qb Γ') (h : HEq σ σ') :
    HEq (fun z : JJ Γ => SemilinearAut.ofAlgAut σ • z)
      (fun z : JJ Γ' => SemilinearAut.ofAlgAut σ' • z) := by
  subst e
  cases h
  rfl

end Smul

section Congr

theorem congrRingEquiv_refl {K F : Type*} [Field K] [Field F] [Algebra K F]
    (he : ∀ a : K, (RingEquiv.refl F) (algebraMap K F a) = algebraMap K F a) (v : Place K F) :
    Place.congrRingEquiv (RingEquiv.refl F) he v = v := by
  ext1
  exact SetLike.ext fun x => Iff.rfl

theorem Divisor.congr_refl {K F : Type*} [Field K] [Field F] [Algebra K F]
    (he : ∀ a : K, (RingEquiv.refl F) (algebraMap K F a) = algebraMap K F a) (D : Divisor K F) :
    Divisor.congr (RingEquiv.refl F) he D = D := by
  induction D using Finsupp.induction with
  | zero => exact map_zero _
  | single_add v n D _ _ ih =>
      rw [map_add, ih, Divisor.congr_single, congrRingEquiv_refl]

theorem Pic0.congr_refl_apply {K F : Type*} [Field K] [Field F] [Algebra K F]
    (he : ∀ a : K, (RingEquiv.refl F) (algebraMap K F a) = algebraMap K F a) (z : Pic0 K F) :
    Pic0.congr (RingEquiv.refl F) he z = z := by
  induction z using QuotientAddGroup.induction_on with
  | H D =>
      change (QuotientAddGroup.mk (Pic0.degZeroCongr (RingEquiv.refl F) he D) : Pic0 K F) =
        QuotientAddGroup.mk D
      exact congrArg _ (Subtype.ext (Divisor.congr_refl he (D : Divisor K F)))

theorem Pic0.congr_equivOfEq_heq {K E : Type*} [Field K] [Field E] [Algebra K E]
    {F₀ F₁ : IntermediateField K E} (h : F₀ = F₁)
    (he : ∀ a : K, (IntermediateField.equivOfEq h).toRingEquiv (algebraMap K F₀ a) = algebraMap K F₁ a)
    (z : Pic0 K F₀) :
    HEq (Pic0.congr (IntermediateField.equivOfEq h).toRingEquiv he z) z := by
  subst h
  have hr : (IntermediateField.equivOfEq (rfl : F₀ = F₀)).toRingEquiv = RingEquiv.refl F₀ := by
    ext x; rfl
  apply heq_of_eq
  revert he
  rw [hr]
  intro he
  exact Pic0.congr_refl_apply he z

theorem congr_apply_eq_of_heq {K E : Type*} [Field K] [Field E] [Algebra K E]
    {F₀ F₁ : IntermediateField K E} (h : F₀ = F₁) (e : Pic0 K F₀ ≃+ Pic0 K F₁)
    (he : ∀ z, HEq (e z) z) (T₀ : Pic0 K F₀ → Pic0 K F₀) (T₁ : Pic0 K F₁ → Pic0 K F₁)
    (hT : HEq T₀ T₁) (x : Pic0 K F₀) : e (T₀ x) = T₁ (e x) := by
  subst h
  cases hT
  have he' : ∀ z, e z = z := fun z => eq_of_heq (he z)
  rw [he', he']

end Congr

end ES1Sol
p2m_reactivate "P2MW.S_ModularCurve_pic0Congr_jOne_jH_bot_compat.ES1Sol"

namespace ModularCurve p2m_export "ModularCurve" "heckeOperatorOneBar HeckeDiamondInputsAll heckeAlphaOneBar HeckeBetaOneDefined heckeBetaOneBar heckeBetaOneBar_eq HeckeInputsOneAlong heckeOperatorOneAlong heckeOperatorOneAlong_eq restrictForm IsIntegralQExp intSeriesC qExpFunctionFieldC div_mem_qExpFunctionFieldC qExpFunctionFieldC_mono x1FunctionField x1FunctionFieldBar JOne qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff IsBaseChangeAutOf isBaseChangeAutOf_baseChangeAut IsDiamondAut diamondAut isDiamondAut_diamondAut diamondAutBar diamondOneBar IsDiamondAutHBar diamondAutHBar diamondHBar HeckeDiamondInputsHAll heckeAlphaHBar HeckeBetaHDefined heckeBetaHBar heckeBetaHBar_eq HeckeInputsHAlong heckeOperatorHAlong heckeOperatorHAlong_eq translation_mem_GammaH GammaH_bot xHFunctionField xHFunctionFieldC_bot xHFunctionFieldBar JH" end ModularCurve
p2m_open_scoped "ModularCurve" in
open ES1Sol in

theorem ModularCurve.pic0Congr_diamondOneBar_eq_diamondHBar (M : ℕ) [NeZero M]
    (hin : ModularCurve.HeckeDiamondInputsAll M) (hinH : ModularCurve.HeckeDiamondInputsHAll M ⊥)
    (h : ModularCurve.x1FunctionFieldBar M = ModularCurve.xHFunctionFieldBar M ⊥)
    (d : ℕ) (hd : d.Coprime M) (x : ModularCurve.JOne M) :
    (AlgebraicCurve.Pic0.congr (IntermediateField.equivOfEq h).toRingEquiv
        (IntermediateField.equivOfEq h).commutes) (ModularCurve.diamondOneBar M d x) =
      ModularCurve.diamondHBar M ⊥ (ZMod.unitOfCoprime d hd)
        (AlgebraicCurve.Pic0.congr (IntermediateField.equivOfEq h).toRingEquiv
          (IntermediateField.equivOfEq h).commutes x) :=
  congr_apply_eq_of_heq h _ (Pic0.congr_equivOfEq_heq h _)
    (fun z : JOne M => SemilinearAut.ofAlgAut (diamondAutBar M d) • z)
    (fun w : JH M ⊥ => SemilinearAut.ofAlgAut (diamondAutHBar M ⊥ (ZMod.unitOfCoprime d hd)) • w)
    (smul_heq (GammaH_bot M) _ _ (diamondAut_heq hin hinH hd)).symm x

p2m_open_scoped "ModularCurve" in
open ES1Sol in

theorem ModularCurve.pic0Congr_heckeOperatorOneBar_eq_heckeOperatorHAlong (M : ℕ) [NeZero M]
    (hin : ModularCurve.HeckeDiamondInputsAll M) (hinH : ModularCurve.HeckeDiamondInputsHAll M ⊥)
    (h : ModularCurve.x1FunctionFieldBar M = ModularCurve.xHFunctionFieldBar M ⊥)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (x : ModularCurve.JOne M) :
    (AlgebraicCurve.Pic0.congr (IntermediateField.equivOfEq h).toRingEquiv
        (IntermediateField.equivOfEq h).commutes) (ModularCurve.heckeOperatorOneBar M ⟨ℓ, hℓ⟩ x) =
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
        ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M ⊥ ℓ)
        (AlgebraicCurve.Pic0.congr (IntermediateField.equivOfEq h).toRingEquiv
          (IntermediateField.equivOfEq h).commutes x) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  exact congr_apply_eq_of_heq h _ (Pic0.congr_equivOfEq_heq h _)
    (fun z : JOne M => heckeOperatorOneAlong (AlgebraicClosure ℚ) M ℓ z)
    (fun w : JH M ⊥ => heckeOperatorHAlong (AlgebraicClosure ℚ) M ⊥ ℓ w)
    (heckeOperator_heq (AlgebraicClosure ℚ) M ℓ (hinH.heckeInputsHAlong ℓ hℓ) (hin.1 ⟨ℓ, hℓ⟩)).symm x

namespace ES1Sol

theorem galois_smul_heq {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (hF : F₀ = F₁)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    HEq (fun z : Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀) => σ • z)
      (fun z : Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₁) => σ • z) := by
  subst hF
  rfl

end ES1Sol
p2m_reactivate "P2MW.S_ModularCurve_pic0Congr_jOne_jH_bot_compat.ES1Sol"

p2m_open_scoped "ModularCurve" in
set_option synthInstance.maxHeartbeats 1600000 in
open ES1Sol in

theorem ModularCurve.pic0Congr_galois_smul (M : ℕ) [NeZero M]
    (h : ModularCurve.x1FunctionFieldBar M = ModularCurve.xHFunctionFieldBar M ⊥) :
    let e : ModularCurve.JOne M ≃+ ModularCurve.JH M ⊥ :=
      AlgebraicCurve.Pic0.congr (IntermediateField.equivOfEq h).toRingEquiv
        (IntermediateField.equivOfEq h).commutes
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ModularCurve.JOne M), e (σ • x) = σ • e x := by
  intro e σ x
  exact congr_apply_eq_of_heq h e (Pic0.congr_equivOfEq_heq h _)
    (fun z : JOne M => σ • z) (fun w : JH M ⊥ => σ • w)
    (galois_smul_heq (F₀ := ModularCurve.x1FunctionField M) (F₁ := ModularCurve.xHFunctionField M ⊥)
      (ModularCurve.xHFunctionFieldC_bot ℚ M).symm σ) x

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution (M : ℕ) [NeZero M]
    (hin : ModularCurve.HeckeDiamondInputsAll M) (hinH : ModularCurve.HeckeDiamondInputsHAll M ⊥)
    (h : ModularCurve.x1FunctionFieldBar M = ModularCurve.xHFunctionFieldBar M ⊥) :
    let e : ModularCurve.JOne M ≃+ ModularCurve.JH M ⊥ :=
      AlgebraicCurve.Pic0.congr (IntermediateField.equivOfEq h).toRingEquiv
        (IntermediateField.equivOfEq h).commutes
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (x : ModularCurve.JOne M),
        e (ModularCurve.heckeOperatorOneBar M ⟨ℓ, hℓ⟩ x) =
          (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M ⊥ ℓ) (e x)) ∧
    (∀ (d : ℕ) (hd : d.Coprime M) (x : ModularCurve.JOne M),
        e (ModularCurve.diamondOneBar M d x) = ModularCurve.diamondHBar M ⊥ (ZMod.unitOfCoprime d hd) (e x)) ∧
    (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ModularCurve.JOne M),
        e (σ • x) = σ • e x) :=
  ⟨fun ℓ hℓ x => ModularCurve.pic0Congr_heckeOperatorOneBar_eq_heckeOperatorHAlong M hin hinH h ℓ hℓ x,
    fun d hd x => ModularCurve.pic0Congr_diamondOneBar_eq_diamondHBar M hin hinH h d hd x,
    fun σ x => ModularCurve.pic0Congr_galois_smul M h σ x⟩

end
end S_ModularCurve_pic0Congr_jOne_jH_bot_compat
end P2MW
export P2MW.S_ModularCurve_pic0Congr_jOne_jH_bot_compat (solution)
