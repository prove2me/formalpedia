-- Prove2me | solution 1 for GlobalTheory.HermTuple.witt_tuples
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:47:22.714228+00:00
-- url     : https://prove2.me/submissions/768a796f-f3d7-469f-bde4-05f606e05cd7

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralValIntegerIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEquivOfRetractions
import Theorems.Thm_GlobalTheory_HermTuple_exists_matrix_split
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HermWitt_exists_gl_isometry_mul_eq_of_det_ne_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HermTuple
open Matrix Module
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
open Matrix Module in
private theorem transpose_mul_mul_map_apply_eq_sum {R p q q' : Type*} [CommRing R] [Fintype p]
    (c : R →+* R) (G : Matrix p p R) (U : Matrix p q R) (V : Matrix p q' R) (i : q) (j : q') :
    (Uᵀ * G * V.map c) i j = ∑ a, ∑ b, U a i * G a b * c (V b j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
open Matrix Module in
private theorem isField_or_exists_swap_ringEquiv {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) : IsField E ∨ ∃ e : E ≃+* F × F, ∀ x, e (L.cj x) = (e x).swap := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ L.rank
  haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ L.rank
  haveI := L.reduced
  by_cases hfield : IsField E
  · exact Or.inl hfield
  right
  obtain ⟨u, hu0, hu⟩ : ∃ u : E, u ≠ 0 ∧ ∀ w, u * w ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hfield ⟨exists_pair_ne E, mul_comm, fun ha => hcon _ ha⟩
  obtain ⟨t, ht⟩ := (L.cj_fix (u + L.cj u)).1 (by rw [map_add, L.cj_cj, add_comm])
  obtain ⟨s, hs⟩ := (L.cj_fix (u * L.cj u)).1 (by rw [map_mul, L.cj_cj, mul_comm])
  have hs0 : s = 0 := by
    by_contra hs0
    apply hu (L.cj u * algebraMap F E s⁻¹)
    rw [← mul_assoc, ← hs, ← map_mul, mul_inv_cancel₀ hs0, map_one]
  have huu : u * L.cj u = 0 := by rw [← hs, hs0, map_zero]
  have hsq : u * u = algebraMap F E t * u := by
    rw [ht]
    linear_combination (-1 : E) * huu
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hu0
    apply IsReduced.eq_zero
    exact ⟨2, by rw [pow_two, hsq, map_zero, zero_mul]⟩
  have hcu0 : L.cj u ≠ 0 := by
    intro h
    apply hu0
    rw [← L.cj_cj u, h, map_zero]
  set p := algebraMap F E t⁻¹ * u with hp
  set q := algebraMap F E t⁻¹ * L.cj u with hq
  have h1 : p + q = 1 := by
    rw [hp, hq, ← mul_add, ← ht, ← map_mul, inv_mul_cancel₀ ht0, map_one]
  have h0 : p * q = 0 := by
    rw [hp, hq]
    linear_combination (algebraMap F E t⁻¹ * algebraMap F E t⁻¹) * huu
  have hp0 : p ≠ 0 := by
    intro h
    apply hu0
    have hpu : algebraMap F E t * p = u := by
      rw [hp, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ht0, map_one, one_mul]
    rw [← hpu, h, mul_zero]
  have hq0 : q ≠ 0 := by
    intro h
    apply hcu0
    have hqu : algebraMap F E t * q = L.cj u := by
      rw [hq, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ht0, map_one, one_mul]
    rw [← hqu, h, mul_zero]
  have hpp : p * p = p := by linear_combination p * h1 - h0
  have hqq : q * q = q := by linear_combination q * h1 - h0
  have hcp : L.cj p = q := by rw [hp, hq, map_mul, AlgEquiv.commutes]
  have hcq : L.cj q = p := by rw [hp, hq, map_mul, AlgEquiv.commutes, L.cj_cj]
  clear_value p q
  let φ : F × F →ₐ[F] E := _root_.GlobalTheory.SgLoc.idemPairHom p q h1 h0
  have hφ : ∀ a b : F, φ (a, b) = algebraMap F E a * p + algebraMap F E b * q := by
    intro a b
    simp [φ, _root_.GlobalTheory.SgLoc.idemPairHom, Algebra.smul_def]
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hab
    rw [hφ] at hab
    have ha : algebraMap F E a * p = 0 := by
      linear_combination p * hab - algebraMap F E a * hpp - algebraMap F E b * h0
    have hb : algebraMap F E b * q = 0 := by
      linear_combination q * hab - algebraMap F E a * h0 - algebraMap F E b * hqq
    rw [← Algebra.smul_def, smul_eq_zero] at ha hb
    exact Prod.ext (ha.resolve_right hp0) (hb.resolve_right hq0)
  have hdim : Module.finrank F (F × F) = Module.finrank F E := by
    rw [L.rank, Module.finrank_prod, Module.finrank_self]
  have hbij : Function.Bijective φ :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := φ.toLinearMap)).1 hinj⟩
  have hcj : ∀ w : F × F, L.cj (φ w) = φ w.swap := by
    rintro ⟨a, b⟩
    rw [hφ, Prod.swap_prod_mk, hφ]
    simp only [map_add, map_mul, AlgEquiv.commutes, hcp, hcq]
    ring
  let eφ := AlgEquiv.ofBijective φ hbij
  have hsymm : ∀ w, eφ.symm (φ w) = w := fun w => eφ.symm_apply_apply w
  refine ⟨eφ.symm.toRingEquiv, fun x => ?_⟩
  obtain ⟨w, rfl⟩ := hbij.2 x
  change eφ.symm (L.cj (φ w)) = (eφ.symm (φ w)).swap
  rw [hcj, hsymm, hsymm]
end GlobalTheory.HermTuple
end

set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HermTuple
open Matrix Module
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical
open Matrix Module
namespace GlobalTheory.HermTuple
namespace _root_.GlobalTheory.HermTuple
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), _root_.GlobalTheory.HL.IsHermND L Hm → ∀ (m : ℕ) (x y : Fin m → Fin n → E), (∀ i j, _root_.GlobalTheory.HL.hf L Hm (x i) (x j) = _root_.GlobalTheory.HL.hf L Hm (y i) (y j)) → IsUnit (Matrix.of fun i j => _root_.GlobalTheory.HL.hf L Hm (x i) (x j)).det → ∃ g ∈ _root_.GlobalTheory.HL.isomG L Hm, ∀ i, g (x i) = y i := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hHm m x y hxy hunit
  haveI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ L.rank
  have hHm' := hHm
  unfold _root_.GlobalTheory.HL.IsHermND _root_.GlobalTheory.HL.IsHerm _root_.GlobalTheory.HL.cT at hHm'
  obtain ⟨hherm, hdet⟩ := hHm'
  have hG : ∀ a b, L.cj (Hm a b) = Hm b a := fun a b => by
    simpa using congrFun (congrFun hherm b) a
  let c : E →+* E := L.cj.toRingEquiv.toRingHom
  have hform : ∀ u v : Fin n → E,
      _root_.GlobalTheory.HL.hf L Hm u v = ∑ a, ∑ b, u a * Hm a b * c (v b) := by
    intro u v
    unfold _root_.GlobalTheory.HL.hf
    rfl
  let X : Matrix (Fin n) (Fin m) E := Matrix.of fun k i => x i k
  let Y : Matrix (Fin n) (Fin m) E := Matrix.of fun k i => y i k
  have hXY : Yᵀ * Hm * Y.map c = Xᵀ * Hm * X.map c := by
    ext i j
    rw [transpose_mul_mul_map_apply_eq_sum, transpose_mul_mul_map_apply_eq_sum, ← hform,
      ← hform]
    exact (hxy i j).symm
  have hXu : IsUnit (Xᵀ * Hm * X.map c).det := by
    convert hunit using 2
    ext i j
    rw [transpose_mul_mul_map_apply_eq_sum, ← hform]
    rfl
  have h2 : (2 : E) ≠ 0 := by
    intro h2
    apply (two_ne_zero : (2 : F) ≠ 0)
    apply (algebraMap F E).injective
    rw [map_ofNat, map_zero]
    exact h2
  obtain ⟨P, hPG, hPX⟩ : ∃ P : Matrix (Fin n) (Fin n) E, Pᵀ * Hm * P.map c = Hm ∧ P * X = Y := by
    rcases isField_or_exists_swap_ringEquiv L with hfield | ⟨e, he⟩
    · letI : Field E := hfield.toField
      obtain ⟨γ, hγG, hγX⟩ := _root_.GlobalTheory.HermWitt.exists_gl_isometry_mul_eq_of_det_ne_zero h2 (c := c)
        (fun t => L.cj_cj t) hG hXu.ne_zero hXY
      exact ⟨γ, hγG, hγX⟩
    · exact _root_.GlobalTheory.HermTuple.exists_matrix_split c e he Hm hG hdet X Y hXu hXY
  have hPdet : IsUnit P.det := by
    have hd := congrArg Matrix.det hPG
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
    have h' : IsUnit (P.det * Hm.det * (P.map c).det) := by
      rw [hd]
      exact hdet
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h')
  letI := P.invertibleOfIsUnitDet hPdet
  have hcol : ∀ u : Fin n → E,
      (Matrix.of fun k (_ : Unit) => (P *ᵥ u) k) = P * Matrix.of fun k (_ : Unit) => u k := by
    intro u
    ext k l
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hform' : ∀ u v : Fin n → E, _root_.GlobalTheory.HL.hf L Hm u v =
      ((Matrix.of fun k (_ : Unit) => u k)ᵀ * Hm *
        (Matrix.of fun k (_ : Unit) => v k).map c) () () := by
    intro u v
    rw [transpose_mul_mul_map_apply_eq_sum, hform]
    rfl
  refine ⟨Matrix.toLinearEquiv' P ‹_›, ?_, fun i => ?_⟩
  · change ∀ u v, _root_.GlobalTheory.HL.hf L Hm (P *ᵥ u) (P *ᵥ v) =
      _root_.GlobalTheory.HL.hf L Hm u v
    intro u v
    rw [hform', hform', hcol, hcol, Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Hm, ← Matrix.mul_assoc Pᵀ, ← Matrix.mul_assoc Pᵀ Hm, hPG]
  · change P *ᵥ x i = y i
    ext k
    have := congrFun (congrFun hPX k) i
    simpa [X, Y, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
end _root_.GlobalTheory.HermTuple
end GlobalTheory.HermTuple
