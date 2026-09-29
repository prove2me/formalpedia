-- Prove2me | solution 1 for ModularCurve.deg_eq_one_of_trace_qExpFunctionFieldC_galoisField_of_deg_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/cbbb304e-68b6-55d5-ac95-065fb5de9fa1

import Mathlib
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_Place_residueField_eq_compositum_of_isConstantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_deg_eq_one_of_trace_qExpFunctionFieldC_galoisField_of_deg_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

open AlgebraicCurve ModularCurve
open scoped MatrixGroups

namespace ResfieldTrace

variable {K : Type} [Field K]

noncomputable def formEmb {k : Type*} [Field k] (ι₀ : k →+* K) (Γ : Subgroup SL(2, ℤ)) :
    ↥(qExpFunctionFieldC k Γ) →+* ↥(qExpFunctionFieldC K Γ) :=
  letI := ι₀.toAlgebra
  have hmem : ∀ x : ↥(qExpFunctionFieldC k Γ), coeffMap (algebraMap k K) (x : LaurentSeries k) ∈ qExpFunctionFieldC K Γ := by
    intro x
    rw [ModularCurve.qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC k K Γ]
    exact IntermediateField.subset_adjoin K _ ⟨x, x.2, rfl⟩
  { toFun := fun x => ⟨coeffMap (algebraMap k K) (x : LaurentSeries k), hmem x⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := fun x y => Subtype.ext (by simp)
    map_zero' := Subtype.ext (by simp)
    map_add' := fun x y => Subtype.ext (by simp) }

theorem coe_formEmb {k : Type*} [Field k] (ι₀ : k →+* K) (Γ : Subgroup SL(2, ℤ)) (x : ↥(qExpFunctionFieldC k Γ)) :
    (formEmb ι₀ Γ x : LaurentSeries K) = coeffMap ι₀ (x : LaurentSeries k) := rfl

theorem formEmb_algebraMap {k : Type*} [Field k] (ι₀ : k →+* K) (Γ : Subgroup SL(2, ℤ)) (a : k) :
    formEmb ι₀ Γ (algebraMap k ↥(qExpFunctionFieldC k Γ) a) = algebraMap K ↥(qExpFunctionFieldC K Γ) (ι₀ a) := by
  apply Subtype.ext
  change coeffMap ι₀ (algebraMap k (LaurentSeries k) a) = algebraMap K (LaurentSeries K) (ι₀ a)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem adjoin_range_formEmb_eq_top {k : Type*} [Field k] (ι₀ : k →+* K) (Γ : Subgroup SL(2, ℤ)) :
    IntermediateField.adjoin K (Set.range (formEmb ι₀ Γ)) = ⊤ := by
  letI := ι₀.toAlgebra
  apply IntermediateField.lift_injective (qExpFunctionFieldC K Γ)
  have e1 := IntermediateField.lift_adjoin K (qExpFunctionFieldC K Γ) (Set.range (formEmb ι₀ Γ))
  have e2 := IntermediateField.lift_top K (qExpFunctionFieldC K Γ)
  refine e1.trans (Eq.trans ?_ e2.symm)
  conv_rhs => rw [ModularCurve.qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC k K Γ]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, z.2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨formEmb ι₀ Γ ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩, rfl⟩

theorem isAlgebraic_and_adjoin_eq_top_of_adjoin_range_eq_top {k K' F F' : Type*} [Field k] [Field K'] [Field F] [Field F']
    [Algebra k K'] [Algebra K' F'] [Algebra F F'] [Algebra k F] [Algebra.IsAlgebraic k K']
    (hcomp : ∀ a : k, algebraMap F F' (algebraMap k F a) = algebraMap K' F' (algebraMap k K' a))
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤) :
    Algebra.IsAlgebraic F F' ∧ IntermediateField.adjoin F (Set.range (algebraMap K' F')) = ⊤ ∧
      Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤ := by
  letI : Algebra k F' := ((algebraMap K' F').comp (algebraMap k K')).toAlgebra
  haveI : IsScalarTower k K' F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower k F F' := IsScalarTower.of_algebraMap_eq (fun a => (hcomp a).symm)
  set S : IntermediateField F F' := IntermediateField.adjoin F (Set.range (algebraMap K' F')) with hS
  have halgS : ∀ x ∈ Set.range (algebraMap K' F'), IsAlgebraic F x := by
    rintro _ ⟨a, rfl⟩
    have ha : IsIntegral k a := (Algebra.IsAlgebraic.isAlgebraic (R := k) a).isIntegral
    exact ((ha.map (IsScalarTower.toAlgHom k K' F')).tower_top (A := F)).isAlgebraic
  have hSalg : Algebra.IsAlgebraic F S := by
    apply IntermediateField.isAlgebraic_adjoin
    intro x hx
    exact (halgS x hx).isIntegral
  have hStop : S = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ (⊤ : IntermediateField K' F') := IntermediateField.mem_top
    rw [← hgen] at hy
    have h1 : (IntermediateField.adjoin K' (Set.range (algebraMap F F'))).toSubfield =
        Subfield.closure (Set.range (algebraMap K' F') ∪ Set.range (algebraMap F F')) :=
      IntermediateField.adjoin_toSubfield _ _
    have h2 : S.toSubfield = Subfield.closure (Set.range (algebraMap F F') ∪ Set.range (algebraMap K' F')) :=
      IntermediateField.adjoin_toSubfield _ _
    change y ∈ S.toSubfield
    rw [h2, Set.union_comm, ← h1]
    exact hy
  refine ⟨⟨fun y => ?_⟩, hStop, ?_⟩
  · have hy : y ∈ S := hStop ▸ IntermediateField.mem_top
    exact IntermediateField.isAlgebraic_iff.mp (hSalg.isAlgebraic ⟨y, hy⟩)
  · rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halgS]
    change S.toSubalgebra = ⊤
    rw [hStop, IntermediateField.top_toSubalgebra]

theorem mem_range_algebraMap_of_pow_card_eq {K' E : Type*} [Field K'] [Fintype K'] [Field E] [Algebra K' E]
    {y : E} (hy : y ^ Fintype.card K' = y) : y ∈ Set.range (algebraMap K' E) := by
  classical
  have hq : 1 < Fintype.card K' := Fintype.one_lt_card
  set P : Polynomial E := Polynomial.X ^ Fintype.card K' - Polynomial.X with hPdef
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero E hq
  have hdeg : P.natDegree = Fintype.card K' := FiniteField.X_pow_card_sub_X_natDegree_eq E hq
  set T : Finset E := Finset.univ.image (algebraMap K' E) with hT
  have hTcard : T.card = Fintype.card K' := by
    rw [hT, Finset.card_image_of_injective _ (algebraMap K' E).injective, Finset.card_univ]
  have hmem : ∀ z : E, z ∈ P.roots.toFinset ↔ z ^ Fintype.card K' = z := by
    intro z
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def, hPdef, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, sub_eq_zero]
  have hTroots : T ⊆ P.roots.toFinset := by
    intro z hz
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz
    rw [hmem, ← map_pow, FiniteField.pow_card]
  have hroots_card : P.roots.toFinset.card ≤ Fintype.card K' :=
    (Multiset.toFinset_card_le _).trans (hdeg ▸ Polynomial.card_roots' P)
  have hTeq : T = P.roots.toFinset := Finset.eq_of_subset_of_card_le hTroots (by rw [hTcard]; exact hroots_card)
  have hyroot : y ∈ P.roots.toFinset := (hmem y).mpr hy
  rw [← hTeq] at hyroot
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hyroot
  exact ⟨a, ha⟩

end ResfieldTrace

open ResfieldTrace in
theorem solution
    (K : Type) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a)
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (w : Place K ↥(qExpFunctionFieldC K Γ))
    (ι₁ : ↥(qExpFunctionFieldC (ZMod p) Γ) →+* ↥(qExpFunctionFieldC K Γ))
    (hι₁ : ∀ x : ↥(qExpFunctionFieldC (ZMod p) Γ),
      (ι₁ x : LaurentSeries K) = coeffMap (ZMod.castHom (dvd_refl p) K) (x : LaurentSeries (ZMod p)))
    (P₁ : Place (ZMod p) ↥(qExpFunctionFieldC (ZMod p) Γ))
    (hP₁ : P₁.toValuationSubring = w.toValuationSubring.comap ι₁)
    (m : ℕ) (hm : 0 < m) (ι₀ : GaloisField p m →+* K)
    (ι : ↥(qExpFunctionFieldC (GaloisField p m) Γ) →+* ↥(qExpFunctionFieldC K Γ))
    (hι : ∀ x : ↥(qExpFunctionFieldC (GaloisField p m) Γ),
      (ι x : LaurentSeries K) = coeffMap ι₀ (x : LaurentSeries (GaloisField p m)))
    (P : Place (GaloisField p m) ↥(qExpFunctionFieldC (GaloisField p m) Γ))
    (hP : P.toValuationSubring = w.toValuationSubring.comap ι)
    (hdvd : P₁.deg ∣ m) :
    P.deg = 1 := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Fintype (GaloisField p m) := Fintype.ofFinite _

  letI algKF : Algebra (ZMod p) ↥(qExpFunctionFieldC (ZMod p) Γ) := SubalgebraClass.toAlgebra (qExpFunctionFieldC (ZMod p) Γ)
  letI algK'F' : Algebra (GaloisField p m) ↥(qExpFunctionFieldC (GaloisField p m) Γ) := SubalgebraClass.toAlgebra (qExpFunctionFieldC (GaloisField p m) Γ)
  letI smulKF : SMul (ZMod p) ↥(qExpFunctionFieldC (ZMod p) Γ) := Algebra.toSMul
  letI smulK'F' : SMul (GaloisField p m) ↥(qExpFunctionFieldC (GaloisField p m) Γ) := Algebra.toSMul

  set j₀ : ZMod p →+* GaloisField p m := algebraMap (ZMod p) (GaloisField p m) with hj₀
  letI instFF' : Algebra ↥(qExpFunctionFieldC (ZMod p) Γ) ↥(qExpFunctionFieldC (GaloisField p m) Γ) := (formEmb j₀ Γ).toAlgebra
  letI smulFF' : SMul ↥(qExpFunctionFieldC (ZMod p) Γ) ↥(qExpFunctionFieldC (GaloisField p m) Γ) := Algebra.toSMul
  letI instKF' : Algebra (ZMod p) ↥(qExpFunctionFieldC (GaloisField p m) Γ) :=
    ((algebraMap (GaloisField p m) ↥(qExpFunctionFieldC (GaloisField p m) Γ)).comp j₀).toAlgebra
  letI smulKF' : SMul (ZMod p) ↥(qExpFunctionFieldC (GaloisField p m) Γ) := Algebra.toSMul
  haveI : IsScalarTower (ZMod p) (GaloisField p m) ↥(qExpFunctionFieldC (GaloisField p m) Γ) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower (ZMod p) ↥(qExpFunctionFieldC (ZMod p) Γ) ↥(qExpFunctionFieldC (GaloisField p m) Γ) :=
    IsScalarTower.of_algebraMap_eq (fun a => (formEmb_algebraMap j₀ Γ a).symm)
  haveI : Algebra.IsAlgebraic (ZMod p) (GaloisField p m) := Algebra.IsAlgebraic.of_finite (ZMod p) (GaloisField p m)
  haveI : Algebra.IsSeparable (ZMod p) (GaloisField p m) := inferInstance
  obtain ⟨hIA, -, hgen⟩ := isAlgebraic_and_adjoin_eq_top_of_adjoin_range_eq_top (k := ZMod p) (K' := GaloisField p m)
    (F := ↥(qExpFunctionFieldC (ZMod p) Γ)) (F' := ↥(qExpFunctionFieldC (GaloisField p m) Γ))
    (fun a => formEmb_algebraMap j₀ Γ a) (adjoin_range_formEmb_eq_top j₀ Γ)
  haveI : Algebra.IsIntegral ↥(qExpFunctionFieldC (ZMod p) Γ) ↥(qExpFunctionFieldC (GaloisField p m) Γ) :=
    Algebra.isAlgebraic_iff_isIntegral.mp hIA

  have hcomp := AlgebraicCurve.Place.residueField_eq_compositum_of_isConstantFieldExtension (K := ZMod p) hgen P

  have hιj : ∀ x : ↥(qExpFunctionFieldC (ZMod p) Γ), ι (formEmb j₀ Γ x) = ι₁ x := by
    intro x
    apply Subtype.ext
    rw [hι, coe_formEmb, hι₁, coeffMap_coeffMap]
    exact congrArg (fun f : ZMod p →+* K => coeffMap f (x : LaurentSeries (ZMod p))) (Subsingleton.elim _ _)
  have hP₀P₁ : (P.forgetConstants (K := ZMod p)).restrict ↥(qExpFunctionFieldC (ZMod p) Γ) = P₁ := by
    apply Place.ext
    change P.toValuationSubring.comap (formEmb j₀ Γ) = P₁.toValuationSubring
    rw [hP, hP₁, ValuationSubring.comap_comap]
    exact congrArg w.toValuationSubring.comap (RingHom.ext hιj)
  rw [← hP₀P₁] at hdvd

  have hd0 : 0 < ((P.forgetConstants (K := ZMod p)).restrict ↥(qExpFunctionFieldC (ZMod p) Γ)).deg := Nat.pos_of_dvd_of_pos hdvd hm
  haveI : Module.Finite (ZMod p) ((P.forgetConstants (K := ZMod p)).restrict ↥(qExpFunctionFieldC (ZMod p) Γ)).ResidueField := Module.finite_of_finrank_pos hd0
  haveI : Finite ((P.forgetConstants (K := ZMod p)).restrict ↥(qExpFunctionFieldC (ZMod p) Γ)).ResidueField := Module.finite_of_finite (ZMod p)
  letI : Fintype ((P.forgetConstants (K := ZMod p)).restrict ↥(qExpFunctionFieldC (ZMod p) Γ)).ResidueField := Fintype.ofFinite _
  have hcard0 : Fintype.card ((P.forgetConstants (K := ZMod p)).restrict ↥(qExpFunctionFieldC (ZMod p) Γ)).ResidueField = p ^ ((P.forgetConstants (K := ZMod p)).restrict ↥(qExpFunctionFieldC (ZMod p) Γ)).deg := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
    rfl
  have hcardK' : Fintype.card (GaloisField p m) = p ^ m := by
    rw [Fintype.card_eq_nat_card]; exact GaloisField.card p m hm.ne'

  have key : ∀ y : P.ResidueField, y ∈ Set.range ((P.forgetConstants (K := ZMod p)).restrictResidueMap (F := ↥(qExpFunctionFieldC (ZMod p) Γ))) →
      y ∈ Set.range (algebraMap (GaloisField p m) P.ResidueField) := by
    rintro _ ⟨x, rfl⟩
    apply mem_range_algebraMap_of_pow_card_eq
    have hx : x ^ Fintype.card (GaloisField p m) = x := by
      obtain ⟨t, ht⟩ := hdvd
      have hpm : p ^ m = Fintype.card ((P.forgetConstants (K := ZMod p)).restrict ↥(qExpFunctionFieldC (ZMod p) Γ)).ResidueField ^ t := by
        rw [hcard0, ← pow_mul, ← ht]
      rw [hcardK', hpm]
      exact FiniteField.pow_card_pow t x
    exact (map_pow ((P.forgetConstants (K := ZMod p)).restrictResidueMap (F := ↥(qExpFunctionFieldC (ZMod p) Γ))) x _).symm.trans
      (congrArg ((P.forgetConstants (K := ZMod p)).restrictResidueMap (F := ↥(qExpFunctionFieldC (ZMod p) Γ))) hx)

  have htop : (⊤ : IntermediateField (GaloisField p m) P.ResidueField) ≤ ⊥ := by
    rw [← hcomp, IntermediateField.adjoin_le_iff]
    intro y hy
    obtain ⟨a, ha⟩ := key y hy
    rw [← ha]
    exact (⊥ : IntermediateField (GaloisField p m) P.ResidueField).algebraMap_mem a
  rw [AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField]
  intro e
  have he : e ∈ (⊥ : IntermediateField (GaloisField p m) P.ResidueField) := htop IntermediateField.mem_top
  rwa [IntermediateField.mem_bot] at he

end S_ModularCurve_deg_eq_one_of_trace_qExpFunctionFieldC_galoisField_of_deg_dvd
end P2MW
export P2MW.S_ModularCurve_deg_eq_one_of_trace_qExpFunctionFieldC_galoisField_of_deg_dvd (solution)
