-- Prove2me | solution 1 for ModularCurve.natCard_ssPlacesQExp_eq_natCard_ssPlacesQExp_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/15251e47-d758-5c61-9db3-b067a3180152

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_of_ne_top
import Theorems.Thm_ModularCurve_comap_ne_top_and_mem_ssPlacesQExp_of_mem_and_mem_ssPlacesQExp_of_comap_eq
import Theorems.Thm_ModularCurve_ssJSet_eq_image_algebraMap_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_natCard_ssPlacesQExp_eq_natCard_ssPlacesQExp_of_isAlgClosed
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open scoped MatrixGroups

theorem solution
    (p : ℕ) [Fact p.Prime]
    (κ K : Type*) [Field κ] [Field K] [IsAlgClosed κ] [IsAlgClosed K] [CharP κ p] [CharP K p] [Algebra κ K]
    (Γ : Subgroup SL(2, ℤ))
    [AlgebraicCurve.IsCurveOver κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)]
    [AlgebraicCurve.IsCurveOver K ↥(ModularCurve.qExpFunctionFieldC K Γ)]
    (hfgκ : ∃ x : ↥(ModularCurve.qExpFunctionFieldC κ Γ), Transcendental κ x ∧
      FiniteDimensional ↥(IntermediateField.adjoin κ ({x} : Set ↥(ModularCurve.qExpFunctionFieldC κ Γ)))
        ↥(ModularCurve.qExpFunctionFieldC κ Γ))
    (hfgK : ∃ x : ↥(ModularCurve.qExpFunctionFieldC K Γ), Transcendental K x ∧
      FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set ↥(ModularCurve.qExpFunctionFieldC K Γ)))
        ↥(ModularCurve.qExpFunctionFieldC K Γ)) :
    Nat.card ↥(ModularCurve.ssPlacesQExp K Γ p) = Nat.card ↥(ModularCurve.ssPlacesQExp κ Γ p) := by
  classical

  have hBC : ModularCurve.qExpFunctionFieldC K Γ =
      IntermediateField.adjoin K (⇑(ModularCurve.coeffMap (algebraMap κ K)) ''
        (ModularCurve.qExpFunctionFieldC κ Γ : Set (LaurentSeries κ))) :=
    ModularCurve.qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC κ K Γ
  have hmem : ∀ x : ↥(ModularCurve.qExpFunctionFieldC κ Γ),
      ModularCurve.coeffMap (algebraMap κ K) (x : LaurentSeries κ) ∈ ModularCurve.qExpFunctionFieldC K Γ := by
    intro x
    rw [hBC]
    exact IntermediateField.subset_adjoin K _ ⟨x, x.2, rfl⟩
  let φ : ↥(ModularCurve.qExpFunctionFieldC κ Γ) →+* ↥(ModularCurve.qExpFunctionFieldC K Γ) :=
    { toFun := fun x => ⟨ModularCurve.coeffMap (algebraMap κ K) (x : LaurentSeries κ), hmem x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have hφ : ∀ x : ↥(ModularCurve.qExpFunctionFieldC κ Γ),
      ((φ x : ↥(ModularCurve.qExpFunctionFieldC K Γ)) : LaurentSeries K) = ModularCurve.coeffMap (algebraMap κ K) (x : LaurentSeries κ) :=
    fun x => rfl
  letI instA : Algebra ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ) := φ.toAlgebra
  letI instB : Algebra κ ↥(ModularCurve.qExpFunctionFieldC K Γ) :=
    ((algebraMap K ↥(ModularCurve.qExpFunctionFieldC K Γ)).comp (algebraMap κ K)).toAlgebra
  haveI : IsScalarTower κ K ↥(ModularCurve.qExpFunctionFieldC K Γ) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have hcmC : ∀ a : κ, ModularCurve.coeffMap (algebraMap κ K) (algebraMap κ (LaurentSeries κ) a) =
      algebraMap K (LaurentSeries K) (algebraMap κ K a) := by
    intro a
    ext n
    rw [ModularCurve.coeffMap_coeff]
    by_cases h : n = 0
    · subst h; simp [HahnSeries.algebraMap_apply']
    · simp [HahnSeries.algebraMap_apply', h]
  haveI : IsScalarTower κ ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => Subtype.ext ?_)
    exact (hcmC a).symm
  have halgφ : algebraMap ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ) = φ := rfl

  have hgen : IntermediateField.adjoin K
      (Set.range (algebraMap ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ))) = ⊤ := by
    apply IntermediateField.lift_injective
    erw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
    have hset : Subtype.val '' Set.range (algebraMap ↥(ModularCurve.qExpFunctionFieldC κ Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ)) =
        ⇑(ModularCurve.coeffMap (algebraMap κ K)) '' (ModularCurve.qExpFunctionFieldC κ Γ : Set (LaurentSeries κ)) := by
      ext y
      constructor
      · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨φ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
    rw [hset, ← hBC]

  have hext := fun P : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ) =>
    AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
      κ ↥(ModularCurve.qExpFunctionFieldC κ Γ) K ↥(ModularCurve.qExpFunctionFieldC K Γ) hfgκ hfgK hgen P
  choose ext hext_comap _hext_ord hext_uniq using hext

  have hss := ModularCurve.ssJSet_eq_image_algebraMap_of_isAlgClosed p κ K
  have hc := fun w : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ) =>
    ModularCurve.comap_ne_top_and_mem_ssPlacesQExp_of_mem_and_mem_ssPlacesQExp_of_comap_eq p κ K Γ φ hφ hss w
  have hmaps : ∀ P ∈ ModularCurve.ssPlacesQExp κ Γ p, ext P ∈ ModularCurve.ssPlacesQExp K Γ p :=
    fun P hP => (hc (ext P)).2 P hP (by rw [← halgφ]; exact hext_comap P)

  let f : ↥(ModularCurve.ssPlacesQExp κ Γ p) → ↥(ModularCurve.ssPlacesQExp K Γ p) :=
    fun P => ⟨ext P.1, hmaps P.1 P.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨P, hP⟩ ⟨Q, hQ⟩ h
      have h' : ext P = ext Q := congrArg Subtype.val h
      apply Subtype.ext
      apply AlgebraicCurve.Place.ext
      rw [← hext_comap P, ← hext_comap Q, h']
    · rintro ⟨w, hw⟩
      obtain ⟨hne, hbelow⟩ := (hc w).1 hw
      have hK : ∀ a : κ, φ (algebraMap κ ↥(ModularCurve.qExpFunctionFieldC κ Γ) a) ∈ w.toValuationSubring := by
        intro a
        have ha : φ (algebraMap κ ↥(ModularCurve.qExpFunctionFieldC κ Γ) a) =
            algebraMap K ↥(ModularCurve.qExpFunctionFieldC K Γ) (algebraMap κ K a) := Subtype.ext (hcmC a)
        rw [ha]
        exact w.algebraMap_mem' _

      obtain ⟨v, hv⟩ :=
        AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_of_ne_top (K := κ) φ w hK hne
      have hvss : v ∈ ModularCurve.ssPlacesQExp κ Γ p := hbelow v hv.symm
      refine ⟨⟨v, hvss⟩, Subtype.ext ?_⟩
      exact (hext_uniq v w (by rw [halgφ]; exact hv.symm)).symm
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

end S_ModularCurve_natCard_ssPlacesQExp_eq_natCard_ssPlacesQExp_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_natCard_ssPlacesQExp_eq_natCard_ssPlacesQExp_of_isAlgClosed (solution)
