-- Prove2me | solution 1 for N25.cusp_pole_lift_bijection
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:44:21.749986+00:00
-- url     : https://prove2.me/submissions/14fda953-62e6-48df-a7f5-763f8638ccc9

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_N25_cusp_coefficient_embedding
import Theorems.Thm_N25_cusp_constant_place_lift
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_N25_level25_T_doubleCosets
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups

namespace N25

private theorem jq_mem_baseChange (L : Type*) [Field L] [Algebra ℚ L] :
    jqModC L ∈ laurentBaseChange L (xHFunctionField 25 H25) := by
  have hj : jqModC ℚ ∈ xHFunctionField 25 H25 :=
    intFormRatiosC_subset ℚ (CohCarrier.GammaH 25 H25)
      (jqModC_mem_intFormRatiosC ℚ (CohCarrier.GammaH 25 H25))
  have hm : coeffEmb L (jqModC ℚ) = jqModC L := map_jqModC _
  rw [←hm]
  exact coeffEmb_mem_laurentBaseChange L hj

private theorem complex_pole_bound
    {F Fℂ : Type*} [Field F] [Field Fℂ]
    [Algebra (AlgebraicClosure ℚ) F] [Algebra ℂ Fℂ]
    [IsCurveOver (AlgebraicClosure ℚ) F]
    (ι : AlgebraicClosure ℚ →+* ℂ)
    (κ : F →+* Fℂ)
    (hconst : ∀ a : AlgebraicClosure ℚ, κ (algebraMap (AlgebraicClosure ℚ) _ a) = algebraMap ℂ _ (ι a))
    (hgen : IntermediateField.adjoin ℂ (Set.range κ)=⊤)
    (j : F)
    (jℂ : Fℂ)
    (hjT : Transcendental (AlgebraicClosure ℚ) j)
    (hjfin : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({j} : Set (F)))
      (F))
    (hjℂT : Transcendental ℂ jℂ)
    (hjℂfin : FiniteDimensional (IntermediateField.adjoin ℂ ({jℂ} : Set (Fℂ)))
      (Fℂ))
    (hκj : κ j=jℂ) :
    Finite {P : Place ℂ (Fℂ) // P.ord jℂ<0} ∧
      Nat.card {P : Place ℂ (Fℂ) // P.ord jℂ<0} ≤
        Nat.card {P : Place (AlgebraicClosure ℚ) (F) // P.ord j<0} := by
  classical
  let K := AlgebraicClosure ℚ
  letI := hjfin
  letI := hjℂfin
  letI : Algebra ℂ Fℂ := inferInstance
  let A := IntermediateField.adjoin ℂ ({jℂ} : Set Fℂ)
  let E := (⊤ : IntermediateField A Fℂ)
  letI : Algebra ℂ E := E.algebra'
  let e : E ≃ₐ[ℂ] Fℂ :=
    { toFun := fun x => x.val
      invFun := fun x => ⟨x,IntermediateField.mem_top⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  let κE : F →+* E :=
    { toFun := fun x => ⟨κ x,IntermediateField.mem_top⟩
      map_zero' := Subtype.ext (map_zero κ)
      map_one' := Subtype.ext (map_one κ)
      map_add' := fun x y => Subtype.ext (map_add κ x y)
      map_mul' := fun x y => Subtype.ext (map_mul κ x y) }
  letI : Algebra K ℂ := ι.toAlgebra
  letI : Algebra F E := κE.toAlgebra
  letI : Algebra K E := ((algebraMap ℂ E).comp ι).toAlgebra
  letI : IsScalarTower K ℂ E := by
    constructor
    intro a b c
    simp only [Algebra.smul_def]
    change algebraMap ℂ E (ι a*b)*c = algebraMap ℂ E (ι a)*(algebraMap ℂ E b*c)
    rw [map_mul]
    ring
  letI : IsScalarTower K F E := by
    constructor
    intro a b c
    simp only [Algebra.smul_def]
    change κE (algebraMap K F a*b)*c = algebraMap ℂ E (ι a)*(κE b*c)
    rw [map_mul]
    have hc : κE (algebraMap K F a)=algebraMap ℂ E (ι a) := Subtype.ext (hconst a)
    rw [hc]
    ring
  letI : FiniteDimensional A E := IntermediateField.finiteDimensional_left E
  have hgenE : IntermediateField.adjoin ℂ (Set.range κE)=⊤ := by
    have hm : (IntermediateField.adjoin ℂ (Set.range κ)).map e.symm.toAlgHom =
        IntermediateField.adjoin ℂ (Set.range κE) := by
      rw [IntermediateField.adjoin_map]
      congr 1
      ext x
      constructor
      · rintro ⟨_,⟨y,rfl⟩,rfl⟩
        exact ⟨y,rfl⟩
      · rintro ⟨y,rfl⟩
        exact ⟨κ y,⟨y,rfl⟩,rfl⟩
    have ht : (⊤ : IntermediateField ℂ Fℂ).map e.symm.toAlgHom=⊤ := by
      apply top_unique
      intro x _
      exact ⟨e x,IntermediateField.mem_top,e.symm_apply_apply x⟩
    rw [hgen,ht] at hm
    exact hm.symm
  have hj0 : j≠0 := fun h => hjT (h.symm ▸ isAlgebraic_zero)
  have hyt : (algebraMap F E j : Fℂ)=jℂ := hκj
  have hb := finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin
    j hjT jℂ hjℂT E hyt hgenE
  let QE := {P : Place ℂ E // P.ord (algebraMap F E j)<0}
  let QC := {P : Place ℂ Fℂ // P.ord jℂ<0}
  have hbound := ((hb.2 j hj0).2).2
  letI : Finite QE := ((hb.2 j hj0).2).1
  let ep := Place.congrEquiv e.toRingEquiv (fun a => e.commutes a)
  have heord (P : Place ℂ E) : (ep P).ord jℂ=P.ord (algebraMap F E j) := by
    have ho := Place.ord_congrRingEquiv e.toRingEquiv (fun a => e.commutes a) P (algebraMap F E j)
    change (ep P).ord (e (algebraMap F E j))=P.ord (algebraMap F E j) at ho
    simpa only [show e (algebraMap F E j)=jℂ from hyt] using ho
  let epole : QE ≃ QC := ep.subtypeEquiv (fun P => by rw [heord])
  letI : Finite QC := Finite.of_surjective epole epole.surjective
  refine ⟨inferInstance,?_⟩
  rw [←Nat.card_congr epole]
  exact hbound

/-- The fourteen geometric j-poles correspond to all complex j-poles without changing orders. -/
theorem _root_.solution
    (ι : AlgebraicClosure ℚ →+* ℂ) :
    let K := AlgebraicClosure ℚ
    let F₀ := xHFunctionField 25 N25.H25
    let F := xHFunctionFieldBar 25 N25.H25
    let Fℂ := laurentBaseChange ℂ F₀
    ∃ κ : F →+* Fℂ, ∃ j : F, ∃ jℂ : Fℂ,
      (∀ x : F, (κ x : LaurentSeries ℂ) = coeffMap ι (x : LaurentSeries K)) ∧
      (j : LaurentSeries K) = jqModC K ∧
      (jℂ : LaurentSeries ℂ) = jqModC ℂ ∧ κ j = jℂ ∧
      Finite {P : Place K F // P.ord j < 0} ∧
      Finite {P : Place ℂ Fℂ // P.ord jℂ < 0} ∧
      Nat.card {P : Place K F // P.ord j < 0} = 14 ∧
      Nat.card {P : Place ℂ Fℂ // P.ord jℂ < 0} = 14 ∧
      ∃ lift : {P : Place K F // P.ord j < 0} ≃
          {P : Place ℂ Fℂ // P.ord jℂ < 0},
        ∀ P, (lift P).val.toValuationSubring.comap κ = P.val.toValuationSubring ∧
          ∀ x : F, (lift P).val.ord (κ x) = P.val.ord x := by
  classical
  let K := AlgebraicClosure ℚ
  let Γ := CohCarrier.GammaH 25 H25
  let F₀ := xHFunctionField 25 H25
  let F := xHFunctionFieldBar 25 H25
  let Fℂ := laurentBaseChange ℂ F₀
  let j : F := ⟨jqModC K,jq_mem_baseChange K⟩
  let jℂ : Fℂ := ⟨jqModC ℂ,jq_mem_baseChange ℂ⟩
  obtain ⟨κ,hκ,hconst,htower⟩ := cusp_coefficient_embedding ι
  have hκj : κ j=jℂ := by
    apply Subtype.ext
    rw [hκ]
    exact map_jqModC ι
  letI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH 25 H25)
  have hT : ModularGroup.T∈Γ := translation_mem_GammaH 25 H25
  obtain ⟨hjT,hjfin⟩ :=
    transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
      K Γ hT j rfl
  obtain ⟨hjℂT,hjℂfin⟩ :=
    transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
      ℂ Γ hT jℂ rfl
  letI := hjfin
  letI := hjℂfin
  have hfull := finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index K 25 H25 j rfl
  have hcardQ : Nat.card {P : Place K F // P.ord j<0}=14 :=
    (natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
      25 Γ (Gamma1_le_GammaH 25 H25) j rfl hfull).2.2.trans level25_T_doubleCosets
  letI : Finite {P : Place K F // P.ord j<0} :=
    Nat.finite_of_card_ne_zero (by rw [hcardQ]; decide)
  letI : IsCurveOver K F :=
    (isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField K 25 H25).1
  have hbound := complex_pole_bound ι κ hconst htower.2.2 j jℂ hjT hjfin hjℂT hjℂfin hκj
  let QC := {P : Place ℂ Fℂ // P.ord jℂ<0}
  letI : Finite QC := hbound.1
  have hboundC : Nat.card QC≤14 := hbound.2.trans_eq hcardQ
  obtain ⟨κ',hκ',hlift⟩ := cusp_constant_place_lift ι
  have heκ : κ'=κ := by
    exact RingHom.ext (fun x => Subtype.ext ((hκ' x).trans (hκ x).symm))
  subst κ'
  choose lift hcomap hord huniq using hlift
  have hinj : Function.Injective lift := by
    intro P Q h
    apply Place.ext
    rw [←hcomap P,←hcomap Q,h]
  let Q := {P : Place K F // P.ord j<0}
  let f : Q → QC := fun P => ⟨lift P.val,by rw [←hκj,hord]; exact P.property⟩
  have hfinj : Function.Injective f := fun P Q h =>
    Subtype.ext (hinj (congrArg Subtype.val h))
  have hcardC : Nat.card QC=14 := by
    have hl := Nat.card_le_card_of_injective f hfinj
    change Nat.card Q≤Nat.card QC at hl
    change Nat.card Q=14 at hcardQ
    omega
  letI : Fintype Q := Fintype.ofFinite Q
  letI : Fintype QC := Fintype.ofFinite QC
  have hcards : Fintype.card Q=Fintype.card QC := by
    simpa only [Nat.card_eq_fintype_card] using hcardQ.trans hcardC.symm
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj,hcards⟩
  refine ⟨κ,j,jℂ,hκ,rfl,rfl,hκj,inferInstance,inferInstance,hcardQ,hcardC,
    Equiv.ofBijective f hbij,?_⟩
  intro P
  exact ⟨hcomap P.val,hord P.val⟩

end N25
