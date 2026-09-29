-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/a30ceea6-f3a0-5914-aa33-a6ddff0e56e2

import Mathlib
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_exists_levelField_coeff_mem_sup_eq_top_levelAutBar_stable_linearDisjoint_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_exists_ringEquiv_laurentBaseChange_levelField_coe_eq_coeffMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.ModularCurve ModularCurve.FullLevel"

namespace ModularCurve
p2m_export "ModularCurve" "FullLevel.IsLevelAutAt FullLevel.levelH xHFunctionField modularFunctionFieldBar qExpand modularFunctionFieldFull coeffMap coeffMap_single coeffMap_coeffMap coeffMap_id coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff FullLevel.AuxLevelOne.forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd FullLevel.exists_levelField_coeff_mem_sup_eq_top_levelAutBar_stable_linearDisjoint_of_eq_two FullLevel.exists_ringEquiv_laurentBaseChange_levelField_coe_eq_coeffMap"
namespace FieldDescentAux
p2m_open "ModularCurve"
section CoeffTransport

variable {L L' : Type} [Field L] [CharZero L] [Field L'] [CharZero L']

theorem coeffMap_mem_laurentBaseChange_of_mem (σ : L →+* L') (F : IntermediateField ℚ (LaurentSeries ℚ))
    {f : LaurentSeries L} (hf : f ∈ laurentBaseChange L F) :
    coeffMap σ f ∈ laurentBaseChange L' F := by

  have hL : (laurentBaseChange L F).toSubfield =
      Subfield.closure (Set.range (algebraMap L (LaurentSeries L)) ∪ (⇑(coeffEmb L) '' (F : Set (LaurentSeries ℚ)))) :=
    IntermediateField.adjoin_toSubfield _ _
  have hL' : (laurentBaseChange L' F).toSubfield =
      Subfield.closure (Set.range (algebraMap L' (LaurentSeries L')) ∪ (⇑(coeffEmb L') '' (F : Set (LaurentSeries ℚ)))) :=
    IntermediateField.adjoin_toSubfield _ _
  have hf' : f ∈ (laurentBaseChange L F).toSubfield := hf
  rw [hL] at hf'
  have himg : coeffMap σ f ∈ (Subfield.closure (Set.range (algebraMap L (LaurentSeries L)) ∪
      (⇑(coeffEmb L) '' (F : Set (LaurentSeries ℚ))))).map (coeffMap σ) := Subfield.mem_map.mpr ⟨f, hf', rfl⟩
  rw [RingHom.map_field_closure] at himg
  change coeffMap σ f ∈ (laurentBaseChange L' F).toSubfield
  rw [hL']
  refine Subfield.closure_mono ?_ himg
  rintro _ ⟨y, hy, rfl⟩
  rcases hy with ⟨c, rfl⟩ | ⟨x, hx, rfl⟩
  · left
    refine ⟨σ c, ?_⟩
    rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]
  · right
    refine ⟨x, hx, ?_⟩
    rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
    exact coeffMap_congr (Subsingleton.elim _ _) x

def laurentBaseChangeCongr (σ : L ≃+* L') (F : IntermediateField ℚ (LaurentSeries ℚ)) :
    ↥(laurentBaseChange L F) ≃+* ↥(laurentBaseChange L' F) :=
  RingEquiv.ofBijective
    (((coeffMap (σ : L →+* L')).comp (laurentBaseChange L F).toSubfield.subtype).codRestrict
      (laurentBaseChange L' F).toSubfield
      (fun f => coeffMap_mem_laurentBaseChange_of_mem (σ : L →+* L') F f.2))
    (by
      constructor
      · intro f g h
        apply Subtype.ext
        have h1 := congrArg (fun x : ↥(laurentBaseChange L' F) => coeffMap (σ.symm : L' →+* L) (x : LaurentSeries L')) h
        simp only [RingHom.codRestrict_apply, RingHom.coe_comp, Function.comp_apply, coeffMap_coeffMap] at h1
        have hid : (σ.symm : L' →+* L).comp (σ : L →+* L') = RingHom.id L := by
          ext x; simp
        rw [hid, coeffMap_id, coeffMap_id] at h1
        exact h1
      · intro g
        refine ⟨⟨coeffMap (σ.symm : L' →+* L) (g : LaurentSeries L'),
          coeffMap_mem_laurentBaseChange_of_mem (σ.symm : L' →+* L) F g.2⟩, ?_⟩
        apply Subtype.ext
        simp only [RingHom.codRestrict_apply, RingHom.coe_comp, Function.comp_apply]
        change coeffMap (σ : L →+* L') (coeffMap (σ.symm : L' →+* L) (g : LaurentSeries L')) = _
        rw [coeffMap_coeffMap]
        have hid : (σ : L →+* L').comp (σ.symm : L' →+* L) = RingHom.id L' := by
          ext x; simp
        rw [hid, coeffMap_id])

@[scoped simp] theorem coe_laurentBaseChangeCongr (σ : L ≃+* L') (F : IntermediateField ℚ (LaurentSeries ℚ))
    (f : ↥(laurentBaseChange L F)) :
    ((laurentBaseChangeCongr σ F f : ↥(laurentBaseChange L' F)) : LaurentSeries L') =
      coeffMap (σ : L →+* L') (f : LaurentSeries L) := rfl

end CoeffTransport

section FieldDescent

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (K₀ : Subfield (AlgebraicClosure ℚ))

def K₀' : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  K₀.toIntermediateField (fun x => by rw [eq_ratCast]; exact SubfieldClass.ratCast_mem K₀ x)

theorem mem_K₀' (x : AlgebraicClosure ℚ) : x ∈ K₀' K₀ ↔ x ∈ K₀ := Iff.rfl

def botCongr : ↥K₀ ≃+* ↥(⊥ : IntermediateField ↥(K₀' K₀) (AlgebraicClosure ℚ)) :=
  (RingEquiv.ofBijective
      ({ toFun := fun x => ⟨x.1, x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
         map_zero' := rfl, map_add' := fun _ _ => rfl } : ↥K₀ →+* ↥(K₀' K₀))
      ⟨fun _ _ h => Subtype.ext (congrArg Subtype.val h), fun y => ⟨⟨y.1, y.2⟩, rfl⟩⟩).trans
    (IntermediateField.botEquiv ↥(K₀' K₀) (AlgebraicClosure ℚ)).symm.toRingEquiv

theorem algebraMap_botCongr (x : ↥K₀) :
    algebraMap ↥(⊥ : IntermediateField ↥(K₀' K₀) (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ) (botCongr K₀ x) =
      (x : AlgebraicClosure ℚ) := by
  change algebraMap ↥(⊥ : IntermediateField ↥(K₀' K₀) (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ)
      ((IntermediateField.botEquiv ↥(K₀' K₀) (AlgebraicClosure ℚ)).symm ⟨x.1, x.2⟩) = _
  rw [IntermediateField.botEquiv_symm,
    ← IsScalarTower.algebraMap_apply ↥(K₀' K₀) ↥(⊥ : IntermediateField ↥(K₀' K₀) (AlgebraicClosure ℚ))
      (AlgebraicClosure ℚ)]
  rfl

end FieldDescent

end ModularCurve.FieldDescentAux
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.ModularCurve.FieldDescentAux"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.ModularCurve.FieldDescentAux"

p2m_open "ModularCurve P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.ModularCurve.FieldDescentAux"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem W1ISO_ringEquiv_smallq
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (K₀ : Subfield (AlgebraicClosure ℚ)) (ζ : ↥K₀) (hζ : IsPrimitiveRoot ζ q)
    (F₀ : Subfield ↥(fieldBar q M'))
    (hF₀ : ∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔
      ∀ n : ℤ, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ K₀) :
    ∃ e : ↥(laurentBaseChange ↥K₀ (xHFunctionField (q ^ 2 * M') (levelH q M'))) ≃+* ↥F₀,
      ∀ f : ↥(laurentBaseChange ↥K₀ (xHFunctionField (q ^ 2 * M') (levelH q M'))),
        (((e f : ↥F₀) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffMap K₀.subtype (f : LaurentSeries ↥K₀) := by
  classical
  letI : Algebra ↥(K₀' K₀) ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp
      (algebraMap ↥(K₀' K₀) (AlgebraicClosure ℚ))).toAlgebra

  let ζ' : ↥(K₀' K₀) := ⟨ζ.1, ζ.2⟩
  have hζ' : IsPrimitiveRoot ((ζ' : ↥(K₀' K₀)) : AlgebraicClosure ℚ) q := by
    change IsPrimitiveRoot (K₀.subtype ζ) q
    exact hζ.map_of_injective K₀.subtype_injective

  obtain ⟨F₀', hCHAR, hK1, -, hLD⟩ :=
    ModularCurve.FullLevel.exists_levelField_coeff_mem_sup_eq_top_levelAutBar_stable_linearDisjoint_of_eq_two
      q hq2 M' hqM' (K₀' K₀) ζ' hζ'

  let Kb : IntermediateField ↥(K₀' K₀) (AlgebraicClosure ℚ) := ⊥
  haveI hfd : FiniteDimensional ↥(K₀' K₀) ↥Kb :=
    Module.finite_of_finrank_eq_succ (IntermediateField.finrank_bot (F := ↥(K₀' K₀)) (E := AlgebraicClosure ℚ))

  have hRAT : ∀ f : ↥(fieldBar q M'),
      (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀' := by
    rintro f ⟨x, hx⟩
    rw [hCHAR]
    intro n
    refine ⟨⟨algebraMap ℚ (AlgebraicClosure ℚ) (x.coeff n), ?_⟩, ?_⟩
    · rw [mem_K₀', eq_ratCast]
      exact SubfieldClass.ratCast_mem K₀ _
    · rw [← hx, coeffEmb_coeff]

  obtain ⟨e', he'⟩ :=
    ModularCurve.FullLevel.exists_ringEquiv_laurentBaseChange_levelField_coe_eq_coeffMap
      q M' (K₀' K₀) Kb hfd F₀' hK1 (hLD Kb hfd) hRAT

  have habs : IntermediateField.adjoin ↥(K₀' K₀)
      (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀' = F₀' := by
    refine sup_eq_right.mpr (IntermediateField.adjoin_le_iff.mpr ?_)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.mp hx
    exact F₀'.algebraMap_mem c

  have hcar : ∀ g : ↥(fieldBar q M'), g ∈ F₀' ↔ g ∈ F₀ := by
    intro g
    rw [hCHAR, hF₀]
    constructor
    · intro h n
      obtain ⟨c, hc⟩ := h n
      rw [hc]; exact c.2
    · intro h n
      exact ⟨⟨_, h n⟩, rfl⟩
  let eCar : ↥F₀' ≃+* ↥F₀ :=
    RingEquiv.ofBijective
      ({ toFun := fun g => ⟨g.1, (hcar _).mp g.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
         map_zero' := rfl, map_add' := fun _ _ => rfl } : ↥F₀' →+* ↥F₀)
      ⟨fun a b h => Subtype.ext (by exact congrArg (fun y : ↥F₀ => (y : ↥(fieldBar q M'))) h),
        fun y => ⟨⟨y.1, (hcar _).mpr y.2⟩, rfl⟩⟩

  let e₀ := laurentBaseChangeCongr (botCongr K₀) (xHFunctionField (q ^ 2 * M') (levelH q M'))
  refine ⟨((e₀.trans e').trans (IntermediateField.equivOfEq habs).toRingEquiv).trans eCar, fun f => ?_⟩
  change ((((e' (e₀ f)) : ↥(IntermediateField.adjoin ↥(K₀' K₀)
      (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀')) :
        ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = _
  rw [he', coe_laurentBaseChangeCongr, coeffMap_coeffMap]
  refine coeffMap_congr ?_ _
  ext x
  exact algebraMap_botCongr K₀ x

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 12800000

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.ModularCurve ModularCurve.FullLevel CongruenceSubgroup IntermediateField HahnSeries"
open scoped MatrixGroups

namespace W1ISO

abbrev en (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

theorem exists_emb_bar {n : ℕ} (hn : 0 < n) {z : AlgebraicClosure ℚ} (hz : IsPrimitiveRoot z n) :
    ∃ ι₀ : AlgebraicClosure ℚ →+* ℂ, ι₀ z = en n := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  haveI : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr hn0⟩
  have hmin : minpoly ℚ z = Polynomial.cyclotomic n ℚ :=
    (Polynomial.cyclotomic_eq_minpoly_rat hz hn).symm
  have hroot : en n ∈ (minpoly ℚ z).rootSet ℂ := by
    rw [hmin, Polynomial.mem_rootSet]
    refine ⟨Polynomial.cyclotomic_ne_zero n ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff.mpr (Complex.isPrimitiveRoot_exp n hn0)).eq_zero
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ z] at hroot
  obtain ⟨ψ, hψ⟩ := hroot
  exact ⟨ψ.toRingHom, hψ⟩

theorem exists_emb_sub (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) {n : ℕ} (hn : 0 < n) {ξ : ↥k₀}
    (hξ : IsPrimitiveRoot ξ n) : ∃ ι : ↥k₀ →+* ℂ, ι ξ = en n := by
  have hξ' : IsPrimitiveRoot (ξ : AlgebraicClosure ℚ) n :=
    hξ.map_of_injective (f := algebraMap ↥k₀ (AlgebraicClosure ℚ)) Subtype.val_injective
  obtain ⟨ι₀, hι₀⟩ := exists_emb_bar hn hξ'
  exact ⟨ι₀.comp (algebraMap ↥k₀ (AlgebraicClosure ℚ)), hι₀⟩

theorem coeffMap_algebraMap_coeffEmb (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (x : LaurentSeries ℚ) :
    coeffMap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) (coeffEmb ↥k₀ x) = coeffEmb (AlgebraicClosure ℚ) x := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) x

theorem mem_fixedField_closure_iff {F E : Type*} [Field F] [Field E] [Algebra F E] (S : Set (E ≃ₐ[F] E)) (w : E) :
    w ∈ fixedField (Subgroup.closure S) ↔ ∀ τ ∈ S, τ w = w := by
  rw [mem_fixedField_iff]
  constructor
  · intro h τ hτ
    exact h τ (Subgroup.subset_closure hτ)
  · intro h τ hτ
    induction hτ using Subgroup.closure_induction with
    | mem σ hσ => exact h σ hσ
    | one => rfl
    | mul σ σ' _ _ h1 h2 => rw [AlgEquiv.mul_apply, h2, h1]
    | inv σ _ h1 =>
        rw [AlgEquiv.aut_inv]
        conv_lhs => rw [← h1]
        exact σ.symm_apply_apply w

section Transport

variable {L L' : Type} [Field L] [CharZero L] [Field L'] [CharZero L']

theorem coeffMap_mem_laurentBaseChange_of_mem (σ : L →+* L') (F : IntermediateField ℚ (LaurentSeries ℚ))
    {f : LaurentSeries L} (hf : f ∈ laurentBaseChange L F) :
    coeffMap σ f ∈ laurentBaseChange L' F := by
  rw [mem_laurentBaseChange_iff] at hf
  induction hf using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | ⟨x, hx, rfl⟩
      · rw [algebraMap_laurentSeries_eq_single, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
        exact IntermediateField.algebraMap_mem _ _
      · have : coeffMap σ (coeffEmb L x) = coeffEmb L' x := by
          rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
          exact coeffMap_congr (Subsingleton.elim _ _) x
        rw [this]
        exact coeffEmb_mem_laurentBaseChange L' hx
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

def transport (σ : L ≃+* L') (F : IntermediateField ℚ (LaurentSeries ℚ)) :
    ↥(laurentBaseChange L F) ≃+* ↥(laurentBaseChange L' F) where
  toFun f := ⟨coeffMap (σ : L →+* L') (f : LaurentSeries L),
    coeffMap_mem_laurentBaseChange_of_mem (σ : L →+* L') F f.2⟩
  invFun g := ⟨coeffMap (σ.symm : L' →+* L) (g : LaurentSeries L'),
    coeffMap_mem_laurentBaseChange_of_mem (σ.symm : L' →+* L) F g.2⟩
  left_inv f := by
    apply Subtype.ext
    change coeffMap (σ.symm : L' →+* L) (coeffMap (σ : L →+* L') (f : LaurentSeries L)) = _
    rw [coeffMap_coeffMap]
    have hid : (σ.symm : L' →+* L).comp (σ : L →+* L') = RingHom.id L := by ext x; simp
    rw [hid, coeffMap_id]
  right_inv g := by
    apply Subtype.ext
    change coeffMap (σ : L →+* L') (coeffMap (σ.symm : L' →+* L) (g : LaurentSeries L')) = _
    rw [coeffMap_coeffMap]
    have hid : (σ : L →+* L').comp (σ.symm : L' →+* L) = RingHom.id L' := by ext x; simp
    rw [hid, coeffMap_id]
  map_mul' f g := Subtype.ext (by simp)
  map_add' f g := Subtype.ext (by simp)

@[scoped simp] theorem coe_transport (σ : L ≃+* L') (F : IntermediateField ℚ (LaurentSeries ℚ))
    (f : ↥(laurentBaseChange L F)) :
    ((transport σ F f : ↥(laurentBaseChange L' F)) : LaurentSeries L') = coeffMap (σ : L →+* L') (f : LaurentSeries L) :=
  rfl

end Transport
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.ModularCurve.FieldDescentAux"

section Constants

variable (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))

def subCongr : ↥k₀ ≃+* ↥k₀.toSubfield where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem subtype_comp_subCongr :
    k₀.toSubfield.subtype.comp (subCongr k₀ : ↥k₀ →+* ↥k₀.toSubfield) = algebraMap ↥k₀ (AlgebraicClosure ℚ) := by
  ext x; rfl

end Constants
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.ModularCurve.FieldDescentAux"

section Rho

variable {k : Type} [Field k]
  (B K : IntermediateField k (LaurentSeries k)) (K₀ : IntermediateField k ↥K)
  (hBK : ∀ x : LaurentSeries k, x ∈ B → x ∈ K)
  (hK₀ : ∀ w : ↥K, w ∈ K₀ ↔ ∃ x : LaurentSeries k, x ∈ B ∧ ((w : ↥K) : LaurentSeries k) = x)

def rho : ↥B →ₐ[k] ↥K₀ where
  toFun x := ⟨⟨(x : LaurentSeries k), hBK x x.2⟩, (hK₀ _).mpr ⟨x, x.2, rfl⟩⟩
  map_one' := Subtype.ext (Subtype.ext rfl)
  map_mul' x y := Subtype.ext (Subtype.ext rfl)
  map_zero' := Subtype.ext (Subtype.ext rfl)
  map_add' x y := Subtype.ext (Subtype.ext rfl)
  commutes' c := Subtype.ext (Subtype.ext rfl)

theorem coe_rho (x : ↥B) : (((rho B K K₀ hBK hK₀ x : ↥K₀) : ↥K) : LaurentSeries k) = x := rfl

theorem rho_bijective : Function.Bijective (rho B K K₀ hBK hK₀) := by
  constructor
  · intro x y h
    have h' := congrArg (fun z : ↥K₀ => ((z : ↥K) : LaurentSeries k)) h
    simp only [coe_rho] at h'
    exact Subtype.ext h'
  · intro w
    obtain ⟨x, hx, hw⟩ := (hK₀ (w : ↥K)).mp w.2
    exact ⟨⟨x, hx⟩, Subtype.ext (Subtype.ext hw.symm)⟩

def rhoE : ↥B ≃ₐ[k] ↥K₀ := AlgEquiv.ofBijective _ (rho_bijective B K K₀ hBK hK₀)

theorem coe_rhoE_symm (w : ↥K₀) :
    (((rhoE B K K₀ hBK hK₀).symm w : ↥B) : LaurentSeries k) = ((w : ↥K) : LaurentSeries k) := by
  have h := (rhoE B K K₀ hBK hK₀).apply_symm_apply w
  have h' := congrArg (fun z : ↥K₀ => ((z : ↥K) : LaurentSeries k)) h
  simpa only [rhoE, AlgEquiv.ofBijective_apply, coe_rho] using h'

end Rho
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.ModularCurve.FieldDescentAux"

end W1ISO
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.ModularCurve.FieldDescentAux P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.W1ISO"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.ModularCurve.FieldDescentAux P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.W1ISO"

p2m_open "ModularCurve P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.ModularCurve ModularCurve.FullLevel CongruenceSubgroup IntermediateField HahnSeries P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd.W1ISO"
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 3200000 in
set_option maxHeartbeats 12800000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ q)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK : K = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (G : Subgroup (↥K ≃ₐ[↥k₀] ↥K))
    (hG : G = Subgroup.closure {τ : ↥K ≃ₐ[↥k₀] ↥K | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧
      γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ K τ})
    (K₀ : IntermediateField ↥k₀ ↥K) (hK₀ : K₀ = IntermediateField.fixedField G) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),

      (∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ∃ c : ↥k₀,
        ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n = ((c : ↥k₀) : AlgebraicClosure ℚ)) →
    ∃ φ : ↥K₀ ≃ₐ[↥k₀] ↥F₀,

      (∀ f : ↥K₀, coeffMap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) (((f : ↥K)) : LaurentSeries ↥k₀) =
        ( ((φ f : ↥F₀) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))) ∧

      (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
        (hgK : (coeffEmb ↥k₀ g) ∈ K) (hgK₀ : (⟨_, hgK⟩ : ↥K) ∈ K₀),
        ((φ ⟨⟨_, hgK⟩, hgK₀⟩ : ↥F₀) : ↥(fieldBar q M')) =
          IntermediateField.inclusion hle
            ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩) := by
  letI instk₀ : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  intro F₀ hF₀
  haveI : Fact ℓg.Prime := ⟨hℓg⟩

  let incl : ↥k₀ →+* AlgebraicClosure ℚ := algebraMap ↥k₀ (AlgebraicClosure ℚ)
  let B : IntermediateField ↥k₀ (LaurentSeries ↥k₀) :=
    laurentBaseChange ↥k₀ (xHFunctionField (q ^ 2 * M') (levelH q M'))
  have hqpos : 0 < q := (Fact.out : q.Prime).pos

  have hι : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / q) := by
    obtain ⟨ι, hι⟩ := exists_emb_sub k₀ hqpos hξ
    exact ⟨ι, by rw [hι, en]⟩

  obtain ⟨hBK, hfix⟩ :=
    ModularCurve.FullLevel.AuxLevelOne.forall_isLevelAutAt_apply_eq_iff_exists_of_exists_ringHom_of_dvd
      q M' hqM' ℓg hℓg12 hℓgM' ↥k₀ ξ hξ hι H₁ hH₁ K hK
  have hK₀' : ∀ w : ↥K, w ∈ K₀ ↔ ∃ x : LaurentSeries ↥k₀, x ∈ B ∧ ((w : ↥K) : LaurentSeries ↥k₀) = x := by
    intro w
    rw [hK₀, hG, mem_fixedField_closure_iff, ← hfix w]
    constructor
    · intro h γ hγ hγ0 τ hτ
      exact h τ ⟨γ, hγ, hγ0, hτ⟩
    · rintro h τ ⟨γ, hγ, hγ0, hτ⟩
      exact h γ hγ hγ0 τ hτ

  let ρ : ↥B ≃ₐ[↥k₀] ↥K₀ := rhoE B K K₀ hBK hK₀'

  let k₀' : Subfield (AlgebraicClosure ℚ) := k₀.toSubfield
  let σ : ↥k₀ ≃+* ↥k₀' := subCongr k₀
  have hζ : IsPrimitiveRoot (σ ξ) q := hξ.map_of_injective σ.injective
  let F₀' : Subfield ↥(fieldBar q M') := F₀.toSubfield
  have hF₀' : ∀ f : ↥(fieldBar q M'), f ∈ F₀' ↔
      ∀ n : ℤ, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ k₀' := by
    intro f
    change f ∈ F₀.toSubfield ↔ _
    rw [IntermediateField.mem_toSubfield, hF₀ f]
    refine forall_congr' fun n => ?_
    constructor
    · rintro ⟨c, hc⟩
      rw [hc]
      exact c.2
    · intro h
      exact ⟨⟨_, h⟩, rfl⟩
  obtain ⟨e, he⟩ := W1ISO_ringEquiv_smallq q hq2 M' hqM' k₀' (σ ξ) hζ F₀' hF₀'

  let castF : ↥F₀' ≃+* ↥F₀ :=
    { toFun := fun y => ⟨y.1, y.2⟩
      invFun := fun y => ⟨y.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }

  let Φ : ↥K₀ ≃+* ↥F₀ :=
    ρ.symm.toRingEquiv.trans
      (((transport σ (xHFunctionField (q ^ 2 * M') (levelH q M'))).trans e).trans castF)

  have hΦ : ∀ w : ↥K₀, (((Φ w : ↥F₀) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap incl (((ρ.symm w : ↥B)) : LaurentSeries ↥k₀) := by
    intro w
    change (((e (transport σ _ (ρ.symm w)) : ↥F₀') : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = _
    rw [he, coe_transport, coeffMap_coeffMap, subtype_comp_subCongr]
  have hΦ1 : ∀ w : ↥K₀, coeffMap incl (((w : ↥K)) : LaurentSeries ↥k₀) =
      (((Φ w : ↥F₀) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) := by
    intro w
    rw [hΦ, coe_rhoE_symm]

  have hΦc : ∀ c : ↥k₀, Φ (algebraMap ↥k₀ ↥K₀ c) = algebraMap ↥k₀ ↥F₀ c := by
    intro c
    apply Subtype.ext; apply Subtype.ext
    have e1 : ((((algebraMap ↥k₀ ↥K₀ c : ↥K₀) : ↥K)) : LaurentSeries ↥k₀) = algebraMap ↥k₀ (LaurentSeries ↥k₀) c :=
      rfl
    have e2 : ((((algebraMap ↥k₀ ↥F₀ c : ↥F₀) : ↥(fieldBar q M'))) : LaurentSeries (AlgebraicClosure ℚ)) =
        algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (incl c) := rfl
    have h1 := hΦ1 (algebraMap ↥k₀ ↥K₀ c)
    rw [e1, algebraMap_laurentSeries_eq_single, coeffMap_single] at h1
    rw [e2, ← h1, algebraMap_laurentSeries_eq_single]
  refine ⟨AlgEquiv.ofRingEquiv (f := Φ) hΦc, ?_, ?_⟩
  · intro w
    exact hΦ1 w
  · intro g hg hgK hgK₀
    apply Subtype.ext
    have h1 := hΦ1 ⟨⟨_, hgK⟩, hgK₀⟩
    change coeffMap incl (coeffEmb ↥k₀ g) = _ at h1
    rw [coeffMap_algebraMap_coeffEmb] at h1
    rw [IntermediateField.coe_inclusion]
    exact h1.symm

end S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_exists_algEquiv_fixedField_coeffMap_eq_of_forall_mem_iff_coeff_of_eq_two_of_dvd (solution)
