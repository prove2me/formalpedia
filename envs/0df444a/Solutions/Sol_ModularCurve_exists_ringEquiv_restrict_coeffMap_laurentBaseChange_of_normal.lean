-- Prove2me | solution 1 for ModularCurve.exists_ringEquiv_restrict_coeffMap_laurentBaseChange_of_normal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/d2e0aac6-5a74-563f-8c37-dfc0d6226e57

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ringEquiv_restrict_coeffMap_laurentBaseChange_of_normal

set_option autoImplicit false

open IsLocalRing

namespace K2Sol

noncomputable def coeffEquiv {R : Type*} [CommRing R] (e : R ≃+* R) : LaurentSeries R ≃+* LaurentSeries R :=
  RingEquiv.ofRingHom (ModularCurve.coeffMap e.toRingHom) (ModularCurve.coeffMap e.symm.toRingHom)
    (by
      ext x : 1
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, ModularCurve.coeffMap_coeffMap]
      rw [show e.toRingHom.comp e.symm.toRingHom = RingHom.id R from RingHom.ext fun r => e.apply_symm_apply r,
        ModularCurve.coeffMap_id])
    (by
      ext x : 1
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, ModularCurve.coeffMap_coeffMap]
      rw [show e.symm.toRingHom.comp e.toRingHom = RingHom.id R from RingHom.ext fun r => e.symm_apply_apply r,
        ModularCurve.coeffMap_id])

theorem coeffEquiv_apply {R : Type*} [CommRing R] (e : R ≃+* R) (x : LaurentSeries R) :
    coeffEquiv e x = ModularCurve.coeffMap e.toRingHom x := rfl

end K2Sol

open K2Sol in
theorem solution
    (L₀ : Type) [Field L₀] [CharZero L₀] [Normal ℚ L₀]
    (L : Type) [Field L] [CharZero L] (i : L₀ →+* L)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [Algebra A₀ L₀] [IsFractionRing A₀ L₀]
    [Algebra A₀ A] [IsLocalHom (algebraMap A₀ A)] (hinj : Function.Injective (algebraMap A₀ A))
    (hA₀A : ∀ a : A₀, algebraMap A L (algebraMap A₀ A a) = i (algebraMap A₀ L₀ a))
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (K₀ : IntermediateField L₀ (LaurentSeries L₀)) (hK₀ : K₀ = ModularCurve.laurentBaseChange L₀ F₀)
    (K : IntermediateField L (LaurentSeries L)) (hK : K = ModularCurve.laurentBaseChange L F₀)
    (cK : ↥K₀ →+* ↥K)
    (hcK : ∀ x : ↥K₀, ((cK x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap i ((x : ↥K₀) : LaurentSeries L₀))
    (σL : L ≃+* L) (σA : A ≃+* A)
    (hσ : ∀ a : A, algebraMap A L (σA a) = σL (algebraMap A L a))
    (hσm : ∀ a : A, σA a - a ∈ maximalIdeal A)
    (τ : ↥K ≃+* ↥K)
    (hτ : ∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.toRingHom ((x : ↥K) : LaurentSeries L)) :
    ∃ (σL₀ : L₀ ≃+* L₀) (σA₀ : A₀ ≃+* A₀) (τ₀ : ↥K₀ ≃+* ↥K₀),
      (∀ x : L₀, i (σL₀ x) = σL (i x)) ∧
      (∀ a : A₀, algebraMap A₀ A (σA₀ a) = σA (algebraMap A₀ A a)) ∧
      (∀ a : A₀, algebraMap A₀ L₀ (σA₀ a) = σL₀ (algebraMap A₀ L₀ a)) ∧
      (∀ a : A₀, σA₀ a - a ∈ maximalIdeal A₀) ∧
      (∀ x : ↥K₀, ((τ₀ x : ↥K₀) : LaurentSeries L₀) =
        ModularCurve.coeffMap σL₀.toRingHom ((x : ↥K₀) : LaurentSeries L₀)) ∧
      (∀ x : ↥K₀, cK (τ₀ x) = τ (cK x)) := by
  classical
  subst hK₀

  letI : Algebra L₀ L := i.toAlgebra
  haveI : IsScalarTower ℚ L₀ L :=
    IsScalarTower.of_algebraMap_eq (fun q => by
      rw [RingHom.algebraMap_toAlgebra]
      simp)
  let σLℚ : L ≃ₐ[ℚ] L := AlgEquiv.ofRingEquiv (f := σL) (fun q => by simp)
  let σ₀ : L₀ ≃ₐ[ℚ] L₀ := σLℚ.restrictNormal L₀
  let σL₀ : L₀ ≃+* L₀ := σ₀.toRingEquiv
  have h1 : ∀ x : L₀, i (σL₀ x) = σL (i x) := fun x => AlgEquiv.restrictNormal_commutes σLℚ L₀ x
  have h1' : ∀ x : L₀, i (σL₀.symm x) = σL.symm (i x) := fun x => by
    apply σL.injective
    rw [← h1, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

  have hj₀ : Function.Injective (algebraMap A₀ L₀) := IsFractionRing.injective A₀ L₀
  have hjA : Function.Injective (algebraMap A L) := IsFractionRing.injective A L

  have key : ∀ x : L₀, i x ∈ Set.range (algebraMap A L) → x ∈ Set.range (algebraMap A₀ L₀) := by
    rintro x ⟨a, ha⟩
    rcases ValuationRing.isInteger_or_isInteger A₀ x with hm | hm
    · rw [IsLocalization.IsInteger, RingHom.mem_rangeS] at hm
      exact hm
    · rw [IsLocalization.IsInteger, RingHom.mem_rangeS] at hm
      obtain ⟨m, hm⟩ := hm
      by_cases hx : x = 0
      · exact ⟨0, by simp [hx]⟩
      · have hu : IsUnit (algebraMap A₀ A m) := by
          refine isUnit_iff_exists_inv.mpr ⟨a, ?_⟩
          apply hjA
          rw [map_mul, map_one, hA₀A, hm, map_inv₀, ha]
          exact inv_mul_cancel₀ ((map_ne_zero i).mpr hx)
        have hmu : IsUnit m := IsUnit.of_map (algebraMap A₀ A) m hu
        obtain ⟨v, rfl⟩ := hmu
        refine ⟨((v⁻¹ : A₀ˣ) : A₀), ?_⟩
        have hvv : algebraMap A₀ L₀ (v : A₀) * algebraMap A₀ L₀ ((v⁻¹ : A₀ˣ) : A₀) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        rw [← inv_inv x, ← hm]
        exact (inv_eq_of_mul_eq_one_right hvv).symm

  have stab : ∀ (ρ₀ : L₀ ≃+* L₀) (ρ : L ≃+* L) (ρA : A ≃+* A),
      (∀ x : L₀, i (ρ₀ x) = ρ (i x)) → (∀ a : A, algebraMap A L (ρA a) = ρ (algebraMap A L a)) →
      ∀ y : L₀, y ∈ Set.range (algebraMap A₀ L₀) → ρ₀ y ∈ Set.range (algebraMap A₀ L₀) := by
    intro ρ₀ ρ ρA hρ₀ hρA y ⟨a, ha⟩
    apply key
    refine ⟨ρA (algebraMap A₀ A a), ?_⟩
    rw [hρA, hA₀A, ha, hρ₀]
  have hσ' : ∀ a : A, algebraMap A L (σA.symm a) = σL.symm (algebraMap A L a) := fun a => by
    apply σL.injective
    rw [← hσ, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  let S₀ : Subring L₀ := (algebraMap A₀ L₀).range
  have hS₀ : ∀ y : L₀, y ∈ S₀ ↔ σL₀ y ∈ S₀ := fun y => by
    constructor
    · intro hy
      exact RingHom.mem_range.mpr (stab σL₀ σL σA h1 hσ y (RingHom.mem_range.mp hy))
    · intro hy
      have := stab σL₀.symm σL.symm σA.symm h1' hσ' (σL₀ y) (RingHom.mem_range.mp hy)
      rw [RingEquiv.symm_apply_apply] at this
      exact RingHom.mem_range.mpr this
  let σS : ↥S₀ ≃+* ↥S₀ := σL₀.restrict S₀ S₀ hS₀
  let e₀ : A₀ ≃+* ↥S₀ := RingEquiv.ofBijective (algebraMap A₀ L₀).rangeRestrict
    ⟨fun a b hab => hj₀ (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
  let σA₀ : A₀ ≃+* A₀ := e₀.trans (σS.trans e₀.symm)
  have e₀val : ∀ a : A₀, ((e₀ a : ↥S₀) : L₀) = algebraMap A₀ L₀ a := fun a => rfl
  have e₀symm : ∀ s : ↥S₀, algebraMap A₀ L₀ (e₀.symm s) = (s : L₀) := fun s => by
    rw [← e₀val, RingEquiv.apply_symm_apply]
  have σSval : ∀ s : ↥S₀, ((σS s : ↥S₀) : L₀) = σL₀ (s : L₀) := fun s => rfl
  have h3 : ∀ a : A₀, algebraMap A₀ L₀ (σA₀ a) = σL₀ (algebraMap A₀ L₀ a) := fun a => by
    show algebraMap A₀ L₀ (e₀.symm (σS (e₀ a))) = _
    rw [e₀symm, σSval, e₀val]
  have h2 : ∀ a : A₀, algebraMap A₀ A (σA₀ a) = σA (algebraMap A₀ A a) := fun a => by
    apply hjA
    rw [hA₀A, h3, h1, ← hA₀A, hσ]
  have h4 : ∀ a : A₀, σA₀ a - a ∈ maximalIdeal A₀ := fun a => by
    by_contra hn
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hn
    have hu := hn.map (algebraMap A₀ A)
    rw [map_sub, h2] at hu
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp (hσm (algebraMap A₀ A a))) hu

  let E : LaurentSeries L₀ ≃+* LaurentSeries L₀ := coeffEquiv σL₀
  have hE : ∀ x, E x = ModularCurve.coeffMap (σ₀ : L₀ →+* L₀) x := fun x => by
    rw [coeffEquiv_apply]
    exact ModularCurve.coeffMap_congr (RingHom.ext fun _ => rfl) x
  have hE' : ∀ x, E.symm x = ModularCurve.coeffMap (σ₀.symm : L₀ →+* L₀) x := fun x => by
    show ModularCurve.coeffMap σL₀.symm.toRingHom x = _
    exact ModularCurve.coeffMap_congr (RingHom.ext fun _ => rfl) x
  have hmem : ∀ x : LaurentSeries L₀,
      x ∈ ModularCurve.laurentBaseChange L₀ F₀ ↔ E x ∈ ModularCurve.laurentBaseChange L₀ F₀ := fun x => by
    constructor
    · intro hx
      rw [hE]
      exact ModularCurve.coeffMap_mem_laurentBaseChange σ₀ hx
    · intro hx
      have := ModularCurve.coeffMap_mem_laurentBaseChange σ₀.symm hx
      rw [← hE', RingEquiv.symm_apply_apply] at this
      exact this
  let τ₀ : ↥(ModularCurve.laurentBaseChange L₀ F₀) ≃+* ↥(ModularCurve.laurentBaseChange L₀ F₀) :=
    E.restrict _ _ hmem
  have τ₀val : ∀ x : ↥(ModularCurve.laurentBaseChange L₀ F₀),
      ((τ₀ x : ↥(ModularCurve.laurentBaseChange L₀ F₀)) : LaurentSeries L₀) = E (x : LaurentSeries L₀) := fun x => rfl
  have h5 : ∀ x : ↥(ModularCurve.laurentBaseChange L₀ F₀),
      ((τ₀ x : ↥(ModularCurve.laurentBaseChange L₀ F₀)) : LaurentSeries L₀) =
        ModularCurve.coeffMap σL₀.toRingHom ((x : ↥(ModularCurve.laurentBaseChange L₀ F₀)) : LaurentSeries L₀) :=
    fun x => by rw [τ₀val, coeffEquiv_apply]
  have hcomp : i.comp σL₀.toRingHom = σL.toRingHom.comp i := RingHom.ext fun x => h1 x
  have h6 : ∀ x : ↥(ModularCurve.laurentBaseChange L₀ F₀), cK (τ₀ x) = τ (cK x) := fun x => by
    apply Subtype.ext
    rw [hcK, hτ, hcK, h5, ModularCurve.coeffMap_coeffMap, ModularCurve.coeffMap_coeffMap, hcomp]
  exact ⟨σL₀, σA₀, τ₀, h1, h2, h3, h4, h5, h6⟩

end S_ModularCurve_exists_ringEquiv_restrict_coeffMap_laurentBaseChange_of_normal
end P2MW
export P2MW.S_ModularCurve_exists_ringEquiv_restrict_coeffMap_laurentBaseChange_of_normal (solution)
