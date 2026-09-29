-- Prove2me | solution 1 for M4aHerbrand.IdeleGaloisDescent.apply_unitsAct_eq_of_forall_mem_normOneIdeles
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/040e054d-cfcc-5bf2-9f38-364b085738de

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_IdeleGaloisDescent_apply_unitsAct_eq_of_forall_mem_normOneIdeles
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

noncomputable section

namespace R1UnitsActNormOne

open NumberField MeasureTheory
open scoped Pointwise ENNReal NNReal

section Modulus

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

def actEquiv (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    AdeleRing (𝓞 L) L ≃ₜ+ AdeleRing (𝓞 L) L :=
  { ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv with
    continuous_toFun := D.continuous_act σ
    continuous_invFun := by
      have h : Continuous (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := D.continuous_act σ⁻¹
      have heq : (((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv.symm :
          AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) = (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := by
        funext a
        rw [map_inv]
        rfl
      show Continuous ((((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv.symm))
      rw [heq]; exact h }

theorem actEquiv_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (a : AdeleRing (𝓞 L) L) :
    actEquiv K L D σ a = (D.act σ : RingAut (AdeleRing (𝓞 L) L)) a := rfl

theorem distribHaarChar_unitsMap_act (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    distribHaarChar (AdeleRing (𝓞 L) L)
        (Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z) =
      distribHaarChar (AdeleRing (𝓞 L) L) z := by
  classical
  letI : MeasurableSpace (AdeleRing (𝓞 L) L) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := ⟨rfl⟩
  set θ := actEquiv K L D σ with hθ
  set μ : Measure (AdeleRing (𝓞 L) L) := Measure.addHaar with hμ
  haveI : μ.IsAddHaarMeasure := by rw [hμ]; infer_instance

  set ν : Measure (AdeleRing (𝓞 L) L) := Measure.map θ.symm μ with hν
  haveI hνH : ν.IsAddHaarMeasure := θ.symm.isAddHaarMeasure_map μ
  haveI : μ.Regular := by rw [hμ]; infer_instance
  haveI : ν.Regular := Measure.Regular.map θ.symm.toHomeomorph

  obtain ⟨s, hs_compact, hs_mem⟩ := exists_compact_mem_nhds (0 : AdeleRing (𝓞 L) L)
  have hs0 : μ s ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hs_mem).ne'
  have hstop : μ s ≠ ⊤ := hs_compact.measure_lt_top.ne

  set w : (AdeleRing (𝓞 L) L)ˣ := Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
    AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z with hw
  have hθsymm : ∀ b, (D.act σ : RingAut (AdeleRing (𝓞 L) L)) (θ.symm b) = b := fun b => θ.apply_symm_apply b

  have hset : (w • s : Set (AdeleRing (𝓞 L) L)) = θ '' (z • (θ.symm '' s)) := by
    ext a
    simp only [Set.mem_smul_set, Set.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨(z : AdeleRing (𝓞 L) L) * θ.symm b, ⟨θ.symm b, ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
      rw [actEquiv_apply, map_mul, hθsymm, Units.smul_def, smul_eq_mul]
      rfl
    · rintro ⟨_, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩
      refine ⟨b, hb, ?_⟩
      rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, actEquiv_apply, map_mul, hθsymm]
      rfl

  have himg : ∀ B : Set (AdeleRing (𝓞 L) L), μ (θ '' B) = ν B := by
    intro B
    have hmap : ν B = μ (θ.symm ⁻¹' B) := (θ.symm.toHomeomorph.measurableEmbedding).map_apply μ B
    rw [hmap]
    congr 1
    ext a
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rwa [θ.symm_apply_apply]
    · intro ha
      exact ⟨θ.symm a, ha, θ.apply_symm_apply a⟩
  have himg' : θ '' (θ.symm '' s) = s := by
    rw [← Set.image_comp]
    convert Set.image_id s
    first | (funext a; exact θ.apply_symm_apply a) | exact θ.apply_symm_apply _

  have h1 := distribHaarChar_mul μ w s
  have h2 := distribHaarChar_mul ν z (θ.symm '' s)
  rw [hset, himg, ← h2, ← himg, himg'] at h1

  have := congrArg (fun t => t / μ s) h1
  rwa [ENNReal.mul_div_cancel_right hs0 hstop, ENNReal.mul_div_cancel_right hs0 hstop, ENNReal.coe_inj] at this

theorem unitsAct_eq_unitsMap (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    D.unitsAct σ z =
      Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z := by
  ext; rfl

theorem distribHaarChar_unitsAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    distribHaarChar (AdeleRing (𝓞 L) L) (D.unitsAct σ z) = distribHaarChar (AdeleRing (𝓞 L) L) z := by
  rw [unitsAct_eq_unitsMap]
  exact distribHaarChar_unitsMap_act K L D σ z

end Modulus

section Coboundary

variable (L : Type) [Field L] [NumberField L]
variable {M : Type*} [CommGroup M]

def cobd (θ : MulAut (AdeleRing (𝓞 L) L)ˣ) (ξ : (AdeleRing (𝓞 L) L)ˣ →* M)
    (z : (AdeleRing (𝓞 L) L)ˣ) : M :=
  ξ (θ z) * (ξ z)⁻¹

theorem cobd_mul (θ : MulAut (AdeleRing (𝓞 L) L)ˣ) (ξ : (AdeleRing (𝓞 L) L)ˣ →* M)
    (a b : (AdeleRing (𝓞 L) L)ˣ) :
    cobd L θ ξ (a * b) = cobd L θ ξ a * cobd L θ ξ b := by
  unfold cobd
  rw [map_mul, map_mul, map_mul, mul_inv]
  simp only [mul_assoc, mul_left_comm, mul_comm]

theorem cobd_pow (θ : MulAut (AdeleRing (𝓞 L) L)ˣ) (ξ : (AdeleRing (𝓞 L) L)ˣ →* M)
    (a : (AdeleRing (𝓞 L) L)ˣ) (k : ℕ) :
    cobd L θ ξ (a ^ k) = cobd L θ ξ a ^ k := by
  induction k with
  | zero =>
      simp only [pow_zero]
      unfold cobd
      rw [map_one, map_one, mul_inv_cancel]
  | succ k ih => rw [pow_succ, cobd_mul, ih, pow_succ]

theorem prod_range_cobd (θ : MulAut (AdeleRing (𝓞 L) L)ˣ) (ξ : (AdeleRing (𝓞 L) L)ˣ →* M)
    (z : (AdeleRing (𝓞 L) L)ˣ) (k : ℕ) :
    ∏ i ∈ Finset.range k, cobd L θ ξ ((θ ^ i) z) = ξ ((θ ^ k) z) * (ξ z)⁻¹ := by
  induction k with
  | zero => simp only [Finset.range_zero, Finset.prod_empty, pow_zero, MulAut.one_apply, mul_inv_cancel]
  | succ k ih =>
      rw [Finset.prod_range_succ, ih, pow_succ', MulAut.mul_apply]
      unfold cobd

      have : ξ ((θ ^ k) z) * (ξ z)⁻¹ * (ξ (θ ((θ ^ k) z)) * (ξ ((θ ^ k) z))⁻¹) =
          ξ (θ ((θ ^ k) z)) * (ξ z)⁻¹ * (ξ ((θ ^ k) z) * (ξ ((θ ^ k) z))⁻¹) := by
        simp only [mul_assoc, mul_left_comm, mul_comm]
      rw [this, mul_inv_cancel, mul_one]

variable (K : Type) [Field K] [NumberField K] [Algebra K L]

omit [NumberField K] in

theorem cobd_eq_of_distribHaarChar_eq (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξ : (AdeleRing (𝓞 L) L)ˣ →* M)
    (h : ∀ z ∈ NumberField.TateGlobal.normOneIdeles L, ξ (D.unitsAct σ z) = ξ z)
    {z z' : (AdeleRing (𝓞 L) L)ˣ}
    (hzz' : distribHaarChar (AdeleRing (𝓞 L) L) z = distribHaarChar (AdeleRing (𝓞 L) L) z') :
    cobd L (D.unitsAct σ) ξ z = cobd L (D.unitsAct σ) ξ z' := by

  have hmem : z' * z⁻¹ ∈ NumberField.TateGlobal.normOneIdeles L := by
    show z' * z⁻¹ ∈ (distribHaarChar (AdeleRing (𝓞 L) L)).ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hzz', mul_inv_cancel₀ (distribHaarChar_pos).ne']
  have hone : cobd L (D.unitsAct σ) ξ (z' * z⁻¹) = 1 := by
    unfold cobd
    rw [h _ hmem, mul_inv_cancel]
  have : z' = (z' * z⁻¹) * z := by rw [inv_mul_cancel_right]
  rw [this, cobd_mul, hone, one_mul]

theorem main (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξ : (AdeleRing (𝓞 L) L)ˣ →* M)
    (h : ∀ z ∈ NumberField.TateGlobal.normOneIdeles L, ξ (D.unitsAct σ z) = ξ z)
    (z : (AdeleRing (𝓞 L) L)ˣ) : ξ (D.unitsAct σ z) = ξ z := by
  classical
  set θ : MulAut (AdeleRing (𝓞 L) L)ˣ := D.unitsAct σ with hθ

  have hinv : ∀ w, cobd L θ ξ (θ w) = cobd L θ ξ w := fun w =>
    cobd_eq_of_distribHaarChar_eq L K D σ ξ h (distribHaarChar_unitsAct K L D σ w)
  have hinv_pow : ∀ (i : ℕ) (w), cobd L θ ξ ((θ ^ i) w) = cobd L θ ξ w := by
    intro i
    induction i with
    | zero => intro w; rw [pow_zero, MulAut.one_apply]
    | succ i ih => intro w; rw [pow_succ', MulAut.mul_apply, hinv, ih]

  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have hfin : IsOfFinOrder σ := isOfFinOrder_of_finite σ
  set n : ℕ := orderOf σ with hn
  have hn0 : 0 < n := hfin.orderOf_pos
  have hθn : θ ^ n = 1 := by
    rw [hθ, ← map_pow, hn, pow_orderOf_eq_one, map_one]

  have htors : ∀ w, cobd L θ ξ w ^ n = 1 := by
    intro w
    have htel := prod_range_cobd L θ ξ w n
    rw [hθn, MulAut.one_apply, mul_inv_cancel] at htel
    rw [← htel]
    rw [Finset.prod_congr rfl (fun i _ => hinv_pow i w), Finset.prod_const, Finset.card_range]

  obtain ⟨s, -, hs, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq L
  have hs' : ∀ r : ℝ≥0ˣ, distribHaarChar (AdeleRing (𝓞 L) L) (s r) = (r : ℝ≥0) := by
    intro r
    have := hs r
    unfold NumberField.TateGlobal.ideleNorm at this
    exact_mod_cast this

  have hzpos : (distribHaarChar (AdeleRing (𝓞 L) L) z : ℝ≥0) ≠ 0 := (distribHaarChar_pos).ne'
  set r : ℝ≥0ˣ := Units.mk0 (distribHaarChar (AdeleRing (𝓞 L) L) z) hzpos with hr
  have hρ0 : ((r : ℝ≥0) ^ ((1 : ℝ) / n)) ≠ 0 :=
    (NNReal.rpow_pos (pos_iff_ne_zero.mpr r.ne_zero)).ne'
  set ρ : ℝ≥0ˣ := Units.mk0 ((r : ℝ≥0) ^ ((1 : ℝ) / n)) hρ0 with hρ
  have hρn : ρ ^ n = r := by
    ext
    rw [Units.val_pow_eq_pow_val, hρ, Units.val_mk0, ← NNReal.rpow_natCast, ← NNReal.rpow_mul,
      one_div_mul_cancel (Nat.cast_ne_zero.mpr hn0.ne'), NNReal.rpow_one]

  have hzr : cobd L θ ξ z = cobd L θ ξ (s r) := by
    refine cobd_eq_of_distribHaarChar_eq L K D σ ξ h ?_
    rw [hs' r, hr, Units.val_mk0]
  have hone : cobd L θ ξ z = 1 := by
    rw [hzr, ← hρn, map_pow, cobd_pow, htors]
  unfold cobd at hone
  rwa [mul_inv_eq_one] at hone

end Coboundary

end R1UnitsActNormOne

end

open NumberField in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    {M : Type*} [CommGroup M] (ξ : (AdeleRing (𝓞 L) L)ˣ →* M)
    (h : ∀ z ∈ NumberField.TateGlobal.normOneIdeles L, ξ (D.unitsAct σ z) = ξ z)
    (z : (AdeleRing (𝓞 L) L)ˣ) : ξ (D.unitsAct σ z) = ξ z :=
  R1UnitsActNormOne.main L K D σ ξ h z

end S_M4aHerbrand_IdeleGaloisDescent_apply_unitsAct_eq_of_forall_mem_normOneIdeles
end P2MW
export P2MW.S_M4aHerbrand_IdeleGaloisDescent_apply_unitsAct_eq_of_forall_mem_normOneIdeles (solution)
