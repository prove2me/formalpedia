-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.forall_exists_isDiscreteValuationRing_specializes_and_mul_stalkRead_eq_stalkRead
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/23132c30-5345-5d1e-af0b-f014b695e37d

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableCharts

import Theorems.Thm_ModularCurve_exists_sum_smul_coeffEmb_mul_eq_of_mem_laurentBaseChange
import Theorems.Thm_IsDiscreteValuationRing_exists_isDiscreteValuationRing_ringHom_valuationSubring_of_finiteDimensional
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_coeffEmb_mul_stalkRead_eq_stalkRead
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_forall_exists_isDiscreteValuationRing_specializes_and_mul_stalkRead_eq_stalkRead
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial

open scoped MatrixGroups

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

    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prJ : XQ ⟶ XO (ΓM M H) hj ρO :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
    ∀ g : ↥(xHFunctionFieldBar M H),

      ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
        (σ : O →+* O') (ιA' : O' →+* ↥A) (hσ : ιA'.comp σ = ιA) (hιA'inj : Function.Injective ιA') (hιA'loc : IsLocalHom ιA')
        (jO' : O' →+* AlgebraicClosure ℚ) (hjO' : jO'.comp (σ.comp ρO) = algebraMap (R p) (AlgebraicClosure ℚ)) (hιA'j : A.subtype.comp ιA' = jO')
        (htoκ' : ((IsLocalRing.residue ↥A).comp ιA').comp (σ.comp ρO) = (IsLocalRing.residue ↥A).comp ρ),
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
      ∃ (hsp : prJ'.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ xn'),
      letI emb : ↥B →+* ↥(xHFunctionFieldBar M H) := (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes hsp).hom))
      ∃ r s₀ : ↥B, s₀ ≠ 0 ∧ g * emb s₀ = emb r := by
  intro g

  have hcf := ModularCurve.exists_sum_smul_coeffEmb_mul_eq_of_mem_laurentBaseChange (AlgebraicClosure ℚ) (xHFunctionField M H) (g : LaurentSeries (AlgebraicClosure ℚ)) g.2
  obtain ⟨ι, _, c, gg, κ, _, d, hh, hD, hgD⟩ := hcf

  have hjinj : Function.Injective jO := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hne
    obtain ⟨P, -, huniq⟩ := ((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime O).mp inferInstance).2
    have h1 : RingHom.ker jO = P := huniq _ ⟨hne, RingHom.ker_isPrime jO⟩
    have hm : IsLocalRing.maximalIdeal O ≠ ⊥ := fun h0 =>
      IsDiscreteValuationRing.not_isField O (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h0)
    have h2 : IsLocalRing.maximalIdeal O = P := huniq _ ⟨hm, inferInstance⟩
    have hp : ((p : ℕ) : O) ∈ RingHom.ker jO := by
      rw [h1, ← h2, hϖ]; exact Ideal.subset_span rfl
    rw [RingHom.mem_ker, map_natCast] at hp
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)

  haveI hιAloc : IsLocalHom ιA := by
    refine ⟨fun x hx => ?_⟩
    by_contra hnu
    have hxm : x ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [hϖ, Ideal.mem_span_singleton] at hxm
    obtain ⟨y, rfl⟩ := hxm
    have hpA : ((p : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
      rw [← ValuationSubring.coe_mem_nonunits_iff]
      simpa using (show ((p : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits from hA)
    have : ιA (((p : ℕ) : O) * y) ∈ IsLocalRing.maximalIdeal ↥A := by
      rw [map_mul, map_natCast]; exact Ideal.mul_mem_right _ _ hpA
    exact (IsLocalRing.mem_maximalIdeal _).mp this hx

  let F := FractionRing O
  let jF : F →+* AlgebraicClosure ℚ := IsFractionRing.lift hjinj
  letI algF : Algebra F (AlgebraicClosure ℚ) := jF.toAlgebra
  haveI : CharZero O := jO.charZero
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective O F)
  haveI : IsScalarTower ℚ F (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq (fun q => by rw [eq_ratCast (algebraMap ℚ (AlgebraicClosure ℚ)) q, eq_ratCast (algebraMap ℚ F) q, map_ratCast])
  let S : Set (AlgebraicClosure ℚ) := Set.range c ∪ Set.range d
  let K' : IntermediateField F (AlgebraicClosure ℚ) := IntermediateField.adjoin F S
  have hSint : ∀ x ∈ S, IsIntegral F x := fun x _ =>
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral.tower_top
  haveI : FiniteDimensional F ↥K' := IntermediateField.finiteDimensional_adjoin hSint

  let Ks : Subfield (AlgebraicClosure ℚ) := K'.toSubfield
  have hjFmem : ∀ x : F, jF x ∈ Ks := fun x => K'.algebraMap_mem x
  letI algFK : Algebra F ↥Ks := (jF.codRestrict Ks hjFmem).toAlgebra
  letI algOK : Algebra O ↥Ks := ((jF.codRestrict Ks hjFmem).comp (algebraMap O F)).toAlgebra
  haveI : IsScalarTower O F ↥Ks := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : FiniteDimensional F ↥Ks := (inferInstance : FiniteDimensional F ↥K')
  haveI : Algebra.IsSeparable F ↥Ks := Algebra.IsSeparable.of_integral F ↥Ks
  have hιAK : ∀ x : O, ((ιA x : ↥A) : AlgebraicClosure ℚ) = ((algebraMap O ↥Ks x : ↥Ks) : AlgebraicClosure ℚ) := by
    intro x
    show A.subtype (ιA x) = jF (algebraMap O F x)
    rw [IsFractionRing.lift_algebraMap]
    exact RingHom.congr_fun hιA x
  have hdvr := IsDiscreteValuationRing.exists_isDiscreteValuationRing_ringHom_valuationSubring_of_finiteDimensional O F A Ks ιA hιAK
  obtain ⟨O', i1, i2, i3, σ, ι', j', hinj, hloc, hcomp, hιj, hjσ, hKfrac⟩ := hdvr
  let jO' : O' →+* AlgebraicClosure ℚ := Ks.subtype.comp j'
  have hjO' : jO'.comp (σ.comp ρO) = algebraMap (R p) (AlgebraicClosure ℚ) := by
    ext r
    show ((j' (σ (ρO r)) : ↥Ks) : AlgebraicClosure ℚ) = algebraMap (R p) _ r
    rw [← RingHom.comp_apply j' σ, hjσ]
    show jF (algebraMap O F (ρO r)) = _
    rw [IsFractionRing.lift_algebraMap]
    exact RingHom.congr_fun hjO r
  have hιA'j : A.subtype.comp ι' = jO' := by ext x; exact hιj x
  have htoκ' : ((IsLocalRing.residue ↥A).comp ι').comp (σ.comp ρO) = (IsLocalRing.residue ↥A).comp ρ := by
    ext r
    show IsLocalRing.residue ↥A (ι' (σ (ρO r))) = IsLocalRing.residue ↥A (ρ r)
    rw [← RingHom.comp_apply ι' σ, hcomp]
    have h1 := RingHom.congr_fun htoκ r
    have h2 := RingHom.congr_fun hιAκ (ρO r)
    simp only [RingHom.comp_apply] at h1 h2
    rw [h2, h1]
  refine ⟨O', i1, i2, i3, σ, ι', hcomp, hinj, hloc, jO', hjO', hιA'j, htoκ', ?_⟩

  let XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  let prJ : XQ ⟶ XO (ΓM M H) hj ρO :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
  let bc' := bcMap (ΓM M H) hj (σ.comp ρO) ((IsLocalRing.residue ↥A).comp ι') htoκ'
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

  haveI := 𝔛.eeta_iso
  haveI := 𝔛.flat
  have hjinj' : Function.Injective jO' := fun x y hxy => hinj (Subtype.ext (by
    have h1 := hιj x; have h2 := hιj y
    show ((ι' x : ↥A) : AlgebraicClosure ℚ) = ((ι' y : ↥A) : AlgebraicClosure ℚ)
    rw [h1, h2]; exact hxy))
  have hprJ₁ : prJ' ≫ pullback.fst _ _ = pullback.fst _ _ := by
    simp only [prJ', pullback.lift_fst, Category.comp_id]
  have hprJ₂ : prJ' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom jO') := by
    simp only [prJ', pullback.lift_snd]
  have hprPB : IsPullback prJ' (pullback.snd (toBase p (ΓM M H) hj) _) (XO.toBase (ΓM M H) hj (σ.comp ρO)) (Spec.map (CommRingCat.ofHom jO')) := by
    have key : IsPullback (prJ' ≫ pullback.fst (toBase p (ΓM M H) hj) _)
        (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) (toBase p (ΓM M H) hj)
        (Spec.map (CommRingCat.ofHom jO') ≫ Spec.map (CommRingCat.ofHom (σ.comp ρO))) := by
      rw [hprJ₁, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO']; exact IsPullback.of_hasPullback _ _
    exact IsPullback.of_right key hprJ₂ (IsPullback.of_hasPullback _ _)
  have hsp : prJ'.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ xn' := by
    have hflat : GeneralizingMap (XO.toBase (ΓM M H) hj (σ.comp ρO)).base := Flat.generalizingMap _
    have hsp0 : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O') ⤳ (XO.toBase (ΓM M H) hj (σ.comp ρO)).base xn' :=
      (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
    obtain ⟨x', hx', hx'b⟩ := hflat hsp0
    obtain ⟨ζ, hζ, -⟩ := Scheme.exists_preimage_of_isPullback hprPB x' (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) (by
      rw [hx'b]
      apply PrimeSpectrum.ext
      show (⊥ : Ideal O') = Ideal.comap jO' (IsLocalRing.closedPoint (AlgebraicClosure ℚ)).asIdeal
      rw [show (IsLocalRing.closedPoint (AlgebraicClosure ℚ)).asIdeal = ⊥ from Ideal.eq_bot_of_prime _, ← RingHom.ker_eq_comap_bot,
        (RingHom.injective_iff_ker_eq_bot jO').mp hjinj'])
    have h1 : genericPoint (𝔛.Meta).C ⤳ (inv 𝔛.eeta).base ζ := genericPoint_specializes _
    have h2 := h1.map (𝔛.eeta ≫ prJ').base.hom.continuous
    have h3 : (𝔛.eeta ≫ prJ').base ((inv 𝔛.eeta).base ζ) = x' := by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id_assoc, hζ]
    rw [h3] at h2
    rw [← Scheme.Hom.comp_apply]
    exact h2.trans hx'
  refine ⟨hsp, ?_⟩
  let emb : ↥B →+* ↥(xHFunctionFieldBar M H) := (𝔛.Meta).ffEquiv.symm.toRingHom.comp
    ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
      ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
        ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes hsp).hom))
  have hCR := ModularCurve.XHDRModelAtP.exists_coeffEmb_mul_stalkRead_eq_stalkRead p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ jO hjO ιA hιA hιAκ n O' σ ι' hcomp hinj hloc jO' hjO' hιA'j htoκ' hsp
  obtain ⟨hembinj, hconst, hfracF⟩ := hCR

  let P : ↥(xHFunctionFieldBar M H) → Prop := fun x => ∃ r s : ↥B, emb s ≠ 0 ∧ x * emb s = emb r
  have hP0 : P 0 := ⟨0, 1, by rw [map_one]; exact one_ne_zero, by rw [map_zero, zero_mul]⟩
  have hPmul : ∀ x y, P x → P y → P (x * y) := by
    rintro x y ⟨r, s, hs, hx⟩ ⟨r', s', hs', hy⟩
    refine ⟨r * r', s * s', by rw [map_mul]; exact mul_ne_zero hs hs', ?_⟩
    rw [map_mul, map_mul]
    linear_combination (y * emb s') * hx + (emb r) * hy
  have hPadd : ∀ x y, P x → P y → P (x + y) := by
    rintro x y ⟨r, s, hs, hx⟩ ⟨r', s', hs', hy⟩
    refine ⟨r * s' + r' * s, s * s', by rw [map_mul]; exact mul_ne_zero hs hs', ?_⟩
    rw [map_mul, map_add, map_mul, map_mul]
    linear_combination (emb s') * hx + (emb s) * hy
  have hPsum : ∀ {α : Type} [Fintype α] (f : α → ↥(xHFunctionFieldBar M H)), (∀ a, P (f a)) → P (∑ a, f a) := by
    intro α _ f hf
    classical
    have key : ∀ t : Finset α, P (∑ a ∈ t, f a) := by
      intro t
      induction t using Finset.induction_on with
      | empty => simpa using hP0
      | insert a t ha ih => rw [Finset.sum_insert ha]; exact hPadd _ _ (hf a) ih
    exact key _
  have hPconst : ∀ cc : AlgebraicClosure ℚ, cc ∈ Ks → P (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) cc) := by
    intro cc hcc
    obtain ⟨a, b, hb, hcab⟩ := hKfrac ⟨cc, hcc⟩
    have hea : emb (σB a) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (jO' a) := RingHom.congr_fun hconst a
    have heb : emb (σB b) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (jO' b) := RingHom.congr_fun hconst b
    refine ⟨σB a, σB b, ?_, ?_⟩
    · rw [heb, map_ne_zero_iff _ (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).injective]
      show ((j' b : ↥Ks) : AlgebraicClosure ℚ) ≠ 0
      exact fun h0 => hb (Subtype.ext h0)
    · rw [heb, hea, ← map_mul]
      congr 1
      exact congrArg Subtype.val hcab
  have hPemb : ∀ a : ↥(qExpFunctionFieldC ℚ (ΓM M H)),
      P ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (a : LaurentSeries ℚ), ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) a.2⟩ := by
    intro a
    obtain ⟨r, s, hs, h⟩ := hfracF a
    exact ⟨r, s, (map_ne_zero_iff emb hembinj).mpr hs, h⟩

  let q : ↥(xHFunctionField M H) → ↥(xHFunctionFieldBar M H) := fun a =>
    ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (a : LaurentSeries ℚ), ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) a.2⟩
  let Df : ↥(xHFunctionFieldBar M H) := ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (d j) * q (hh j)
  let Nf : ↥(xHFunctionFieldBar M H) := ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c i) * q (gg i)
  have hval : ∀ x : ↥(xHFunctionFieldBar M H), (x : LaurentSeries (AlgebraicClosure ℚ)) = (xHFunctionFieldBar M H).val x := fun x => rfl
  have hDf : (Df : LaurentSeries (AlgebraicClosure ℚ)) = ∑ j, algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (d j) * ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((hh j : ↥(xHFunctionField M H)) : LaurentSeries ℚ) := by
    rw [hval]; simp only [Df, q, map_sum, map_mul, AlgHom.commutes]; rfl
  have hNf : (Nf : LaurentSeries (AlgebraicClosure ℚ)) = ∑ i, algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c i) * ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((gg i : ↥(xHFunctionField M H)) : LaurentSeries ℚ) := by
    rw [hval]; simp only [Nf, q, map_sum, map_mul, AlgHom.commutes]; rfl
  have hDne : Df ≠ 0 := fun h => hD (by rw [← hDf, h]; rfl)
  have hgDf : g * Df = Nf := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, hDf, hNf]
    exact hgD
  have hcmem : ∀ i, c i ∈ Ks := fun i => IntermediateField.subset_adjoin F S (Or.inl ⟨i, rfl⟩)
  have hdmem : ∀ j, d j ∈ Ks := fun j => IntermediateField.subset_adjoin F S (Or.inr ⟨j, rfl⟩)
  have hPD : P Df := hPsum _ (fun j => hPmul _ _ (hPconst _ (hdmem j)) (hPemb _))
  have hPN : P Nf := hPsum _ (fun i => hPmul _ _ (hPconst _ (hcmem i)) (hPemb _))
  obtain ⟨rD, sD, hsD, hxD⟩ := hPD
  obtain ⟨rN, sN, hsN, hxN⟩ := hPN
  have hrD : emb rD ≠ 0 := by rw [← hxD]; exact mul_ne_zero hDne hsD
  refine ⟨rN * sD, rD * sN, ?_, ?_⟩
  · intro h0; apply mul_ne_zero hrD hsN; rw [← map_mul, h0, map_zero]
  · rw [map_mul, map_mul]
    linear_combination (emb sD * emb sN) * hgDf - (g * emb sN) * hxD + (emb sD) * hxN

end S_ModularCurve_XHDRModelAtP_forall_exists_isDiscreteValuationRing_specializes_and_mul_stalkRead_eq_stalkRead
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_forall_exists_isDiscreteValuationRing_specializes_and_mul_stalkRead_eq_stalkRead (solution)
