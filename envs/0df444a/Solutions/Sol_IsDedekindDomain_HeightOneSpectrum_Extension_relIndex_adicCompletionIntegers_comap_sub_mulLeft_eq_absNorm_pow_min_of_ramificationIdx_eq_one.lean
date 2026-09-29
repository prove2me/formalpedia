-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.Extension.relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ad21804a-8470-5062-86c8-092ddef04b26

import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_LinearMap_relIndex_pow_smul_top_comap_eq_card_pow_min_of_finrank_ker_baseChange_le_one
import Theorems.Thm_AlgEquiv_algebraMap_det_toLinearMap_sub_smul_id_eq_of_orderOf_eq_finrank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace P2mLocalIndex

section NormVal

variable (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

theorem one_lt_q : (1 : ℝ) < (Ideal.absNorm u.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm u

theorem q_pos : (0 : ℝ) < (Ideal.absNorm u.asIdeal : ℝ) := lt_trans zero_lt_one (one_lt_q F u)

theorem exists_norm_eq_zpow_and_v_eq {x : u.adicCompletion F} (hx : x ≠ 0) :
    ∃ k : ℤ, ‖x‖ = (Ideal.absNorm u.asIdeal : ℝ) ^ k ∧
      (Valued.v x : WithZero (Multiplicative ℤ)) = WithZero.exp k := by
  have hv0 : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  refine ⟨Multiplicative.toAdd (WithZero.unzero hv0), ?_, ?_⟩
  · rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv0]
    push_cast
    rfl
  · conv_lhs => rw [← WithZero.coe_unzero hv0]
    rfl

theorem v_eq_exp_of_norm_eq_zpow {x : u.adicCompletion F} {k : ℤ}
    (h : ‖x‖ = (Ideal.absNorm u.asIdeal : ℝ) ^ k) :
    (Valued.v x : WithZero (Multiplicative ℤ)) = WithZero.exp k := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, norm_zero] at h
    exact (zpow_pos (q_pos F u) k).ne h
  obtain ⟨k', hk', hv⟩ := exists_norm_eq_zpow_and_v_eq F u hx
  rw [hk'] at h
  have hk : k' = k := zpow_right_injective₀ (q_pos F u) (one_lt_q F u).ne' h
  rw [hv, hk]

theorem v_eq_one_of_norm_eq_one {x : u.adicCompletion F} (h : ‖x‖ = 1) :
    (Valued.v x : WithZero (Multiplicative ℤ)) = 1 := by
  have := v_eq_exp_of_norm_eq_zpow F u (k := 0) (by rw [h, zpow_zero])
  rwa [WithZero.exp_zero] at this

theorem v_le_one_of_norm_le_one {x : u.adicCompletion F} (h : ‖x‖ ≤ 1) :
    (Valued.v x : WithZero (Multiplicative ℤ)) ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.1 h

theorem mem_integers_iff_v (x : u.adicCompletion F) :
    x ∈ u.adicCompletionIntegers F ↔ (Valued.v x : WithZero (Multiplicative ℤ)) ≤ 1 :=
  HeightOneSpectrum.mem_adicCompletionIntegers _ _ _

end NormVal

section Unramified

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

scoped instance isScalarTower_int : IsScalarTower (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
    (w.1.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem algebraMap_int_coe (x : v.adicCompletionIntegers K) :
    ((algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) x :
        w.1.adicCompletionIntegers L) : w.1.adicCompletion L) =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (x : v.adicCompletion K) := rfl

theorem algebraMap_int_field (x : v.adicCompletionIntegers K) :
    algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletion L) x =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (x : v.adicCompletion K) := rfl

variable (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
include hw

theorem v_algebraMap (x : v.adicCompletion K) :
    (Valued.v (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) x) : WithZero (Multiplicative ℤ)) =
      Valued.v x := by
  change Valued.v (w.adicCompletionSemialgHom K L x) = _
  rw [HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom K L w x, hw, pow_one]

theorem algebraMap_mem_integers_iff (x : v.adicCompletion K) :
    algebraMap (v.adicCompletion K) (w.1.adicCompletion L) x ∈ w.1.adicCompletionIntegers L ↔
      x ∈ v.adicCompletionIntegers K := by
  rw [mem_integers_iff_v, mem_integers_iff_v, v_algebraMap K L v w hw]

theorem exists_eq_algebraMap_mul_unit {y : w.1.adicCompletion L} (hy : y ≠ 0) :
    ∃ x : v.adicCompletion K, x ≠ 0 ∧
      (Valued.v (y * (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) x)⁻¹) :
        WithZero (Multiplicative ℤ)) = 1 := by
  obtain ⟨x, hx⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v
    (Valued.v y : WithZero (Multiplicative ℤ))
  have hy0 : (Valued.v y : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact hy0 hx.symm
  refine ⟨x, hx0, ?_⟩
  rw [map_mul, map_inv₀, v_algebraMap K L v w hw, hx, mul_inv_cancel₀ hy0]

end Unramified

section Theta

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
  (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)

theorem isIntegral_of_mem {y : w.1.adicCompletion L} (hy : y ∈ w.1.adicCompletionIntegers L) :
    IsIntegral (v.adicCompletionIntegers K) y := by
  haveI : Algebra.IsIntegral (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) :=
    Algebra.IsIntegral.of_finite _ _
  have h : IsIntegral (v.adicCompletionIntegers K) (⟨y, hy⟩ : w.1.adicCompletionIntegers L) :=
    Algebra.IsIntegral.isIntegral _
  exact h.map (IsScalarTower.toAlgHom (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
    (w.1.adicCompletion L))

theorem mem_of_isIntegral {y : w.1.adicCompletion L} (hy : IsIntegral (v.adicCompletionIntegers K) y) :
    y ∈ w.1.adicCompletionIntegers L := by
  have h2 : IsIntegral (w.1.adicCompletionIntegers L) y := hy.tower_top
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := w.1.adicCompletionIntegers L)
    (K := w.1.adicCompletion L)).1 h2
  rw [← hz]
  exact z.2

theorem theta_mem {y : w.1.adicCompletion L} (hy : y ∈ w.1.adicCompletionIntegers L) :
    θ y ∈ w.1.adicCompletionIntegers L := by
  apply mem_of_isIntegral K L v w
  have h := isIntegral_of_mem K L v w hy
  exact h.map (θ.restrictScalars (v.adicCompletionIntegers K)).toAlgHom

theorem theta_pow_mem (i : ℕ) {y : w.1.adicCompletion L} (hy : y ∈ w.1.adicCompletionIntegers L) :
    (θ ^ i) y ∈ w.1.adicCompletionIntegers L := by
  induction i with
  | zero => simpa using hy
  | succ i ih => rw [pow_succ', AlgEquiv.mul_apply]; exact theta_mem K L v w θ ih

theorem v_theta_eq_one {y : w.1.adicCompletion L} (hy : (Valued.v y : WithZero (Multiplicative ℤ)) = 1) (i : ℕ) :
    (Valued.v ((θ ^ i) y) : WithZero (Multiplicative ℤ)) = 1 := by
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hy; exact zero_ne_one hy
  have h1 : (θ ^ i) y ∈ w.1.adicCompletionIntegers L :=
    theta_pow_mem K L v w θ i ((mem_integers_iff_v L w.1 y).2 hy.le)
  have h2 : (θ ^ i) y⁻¹ ∈ w.1.adicCompletionIntegers L :=
    theta_pow_mem K L v w θ i ((mem_integers_iff_v L w.1 y⁻¹).2 (by rw [map_inv₀, hy, inv_one]))
  rw [map_inv₀] at h2
  rw [mem_integers_iff_v] at h1 h2
  rw [map_inv₀] at h2
  have h3 : (Valued.v ((θ ^ i) y) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ (θ ^ i).injective).2 hy0)
  exact le_antisymm h1 (by rwa [inv_le_one₀ (zero_lt_iff.2 h3)] at h2)

variable (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
include hw

theorem v_c_eq_one {f : ℕ} (hf : 0 < f) (c : w.1.adicCompletion L) (n : v.adicCompletion K)
    (hn : (Valued.v n : WithZero (Multiplicative ℤ)) = 1)
    (hc : ∏ i ∈ Finset.range f, (θ ^ i) c = algebraMap (v.adicCompletion K) (w.1.adicCompletion L) n) :
    (Valued.v c : WithZero (Multiplicative ℤ)) = 1 := by
  have hn0 : n ≠ 0 := by intro h; rw [h, map_zero] at hn; exact zero_ne_one hn
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hc
    have : (∏ i ∈ Finset.range f, (θ ^ i) (0 : w.1.adicCompletion L)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.2 hf) (map_zero _)
    rw [this, eq_comm, map_eq_zero] at hc
    exact hn0 hc
  obtain ⟨x, hx0, hu⟩ := exists_eq_algebraMap_mul_unit K L v w hw hc0
  set a := algebraMap (v.adicCompletion K) (w.1.adicCompletion L) x with ha
  have ha0 : a ≠ 0 := (map_ne_zero _).2 hx0
  set uu := c * a⁻¹ with huu
  have hcu : c = a * uu := by rw [huu, mul_left_comm, mul_inv_cancel₀ ha0, mul_one]

  have hprod : ∏ i ∈ Finset.range f, (θ ^ i) c = a ^ f * ∏ i ∈ Finset.range f, (θ ^ i) uu := by
    rw [← Finset.card_range f, ← Finset.prod_const, Finset.card_range, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hcu, map_mul, ha, AlgEquiv.commutes]
  have hval := congrArg (fun z => (Valued.v z : WithZero (Multiplicative ℤ))) hc
  rw [hprod, map_mul, map_pow, map_prod, v_algebraMap K L v w hw, v_algebraMap K L v w hw, hn,
    Finset.prod_eq_one (fun i _ => v_theta_eq_one K L v w θ hu i), mul_one] at hval
  have hx1 : (Valued.v x : WithZero (Multiplicative ℤ)) = 1 :=
    le_antisymm ((pow_le_one_iff hf.ne').1 hval.le) ((one_le_pow_iff hf.ne').1 hval.ge)
  rw [hcu, map_mul, v_algebraMap K L v w hw, hx1, one_mul, hu]

end Theta

section ModuleSetup

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

theorem algebraMap_int_injective :
    Function.Injective (algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)) := by
  intro x y hxy
  have h := congrArg (fun z : w.1.adicCompletionIntegers L => (z : w.1.adicCompletion L)) hxy
  simp only [algebraMap_int_coe] at h
  exact Subtype.ext ((algebraMap (v.adicCompletion K) (w.1.adicCompletion L)).injective h)

scoped instance isTorsionFree_int : Module.IsTorsionFree (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) :=
  Module.isTorsionFree_iff_algebraMap_injective.2 (algebraMap_int_injective K L v w)

scoped instance free_int : Module.Free (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) :=
  Module.free_of_finite_type_torsion_free'

scoped instance isIntegralClosure_int :
    IsIntegralClosure (w.1.adicCompletionIntegers L) (v.adicCompletionIntegers K) (w.1.adicCompletion L) where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff := fun {y} =>
    ⟨fun h => ⟨⟨y, mem_of_isIntegral K L v w h⟩, rfl⟩, fun ⟨z, hz⟩ => hz ▸ isIntegral_of_mem K L v w z.2⟩

theorem isLocalization_int :
    IsLocalization (Algebra.algebraMapSubmonoid (w.1.adicCompletionIntegers L)
      (nonZeroDivisors (v.adicCompletionIntegers K))) (w.1.adicCompletion L) :=
  IsIntegralClosure.isLocalization (v.adicCompletionIntegers K) (v.adicCompletion K)
    (w.1.adicCompletion L) (w.1.adicCompletionIntegers L)

end ModuleSetup

section TheMap

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
  (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
  (c : w.1.adicCompletion L) (hcO : c ∈ w.1.adicCompletionIntegers L)

abbrev phi : w.1.adicCompletion L →ₗ[v.adicCompletion K] w.1.adicCompletion L :=
  (θ : w.1.adicCompletion L →ₐ[v.adicCompletion K] w.1.adicCompletion L).toLinearMap -
    c • (LinearMap.id : w.1.adicCompletion L →ₗ[v.adicCompletion K] w.1.adicCompletion L)

theorem phi_apply (y : w.1.adicCompletion L) : phi K L v w θ c y = θ y - c * y := rfl

def fO : w.1.adicCompletionIntegers L →ₗ[v.adicCompletionIntegers K] w.1.adicCompletionIntegers L where
  toFun y := ⟨θ y - c * y, sub_mem (theta_mem K L v w θ y.2) (mul_mem hcO y.2)⟩
  map_add' y z := by
    apply Subtype.ext
    change θ ((y : w.1.adicCompletion L) + z) - c * ((y : w.1.adicCompletion L) + z) =
      (θ y - c * y) + (θ z - c * z)
    rw [map_add]; ring
  map_smul' r y := by
    apply Subtype.ext
    change θ (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (r : v.adicCompletion K) * y) -
        c * (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (r : v.adicCompletion K) * y) =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (r : v.adicCompletion K) * (θ y - c * y)
    rw [map_mul, AlgEquiv.commutes]; ring

theorem fO_coe (y : w.1.adicCompletionIntegers L) :
    ((fO K L v w θ c hcO y : w.1.adicCompletionIntegers L) : w.1.adicCompletion L) = θ y - c * y := rfl

theorem fO_coe' (y : w.1.adicCompletionIntegers L) :
    ((fO K L v w θ c hcO y : w.1.adicCompletionIntegers L) : w.1.adicCompletion L) =
      phi K L v w θ c (y : w.1.adicCompletion L) := rfl

theorem phi_algebraMap (y : w.1.adicCompletionIntegers L) :
    phi K L v w θ c (algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) y) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) (fO K L v w θ c hcO y) := rfl

theorem toMatrix_phi {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L))
    [IsLocalization (Algebra.algebraMapSubmonoid (w.1.adicCompletionIntegers L)
      (nonZeroDivisors (v.adicCompletionIntegers K))) (w.1.adicCompletion L)] :
    LinearMap.toMatrix
        (b.localizationLocalization (v.adicCompletion K) (nonZeroDivisors (v.adicCompletionIntegers K))
          (w.1.adicCompletion L))
        (b.localizationLocalization (v.adicCompletion K) (nonZeroDivisors (v.adicCompletionIntegers K))
          (w.1.adicCompletion L)) (phi K L v w θ c) =
      (LinearMap.toMatrix b b (fO K L v w θ c hcO)).map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) := by
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    Module.Basis.localizationLocalization_apply, phi_algebraMap,
    Module.Basis.localizationLocalization_repr_algebraMap]

theorem algebraMap_det_fO :
    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (LinearMap.det (fO K L v w θ c hcO)) =
      LinearMap.det (phi K L v w θ c) := by
  classical
  haveI := isLocalization_int K L v w
  let b := Module.Free.chooseBasis (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
  rw [← LinearMap.det_toMatrix (b.localizationLocalization (v.adicCompletion K)
    (nonZeroDivisors (v.adicCompletionIntegers K)) (w.1.adicCompletion L)), toMatrix_phi K L v w θ c hcO b,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, LinearMap.det_toMatrix]

variable (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
  (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
  (n : v.adicCompletion K)
  (hc : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)), (θ ^ i) c =
    algebraMap (v.adicCompletion K) (w.1.adicCompletion L) n)
include hθ hc

theorem det_phi : LinearMap.det (phi K L v w θ c) =
    (-1) ^ (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) - 1) * (1 - n) := by
  have h := AlgEquiv.algebraMap_det_toLinearMap_sub_smul_id_eq_of_orderOf_eq_finrank
    (v.adicCompletion K) (w.1.adicCompletion L) θ hθ c
  rw [hc, ← map_one (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)), ← map_sub, ← map_neg,
    ← map_pow, ← map_mul] at h
  exact (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)).injective h

theorem algebraMap_det_fO_eq :
    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (LinearMap.det (fO K L v w θ c hcO)) =
      (-1) ^ (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) - 1) * (1 - n) := by
  rw [algebraMap_det_fO, det_phi K L v w θ c hθ n hc]

variable (m : ℕ) (hm : ‖1 - n‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(m : ℤ)))
include hm

theorem v_det_fO : (Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
    (LinearMap.det (fO K L v w θ c hcO))) : WithZero (Multiplicative ℤ)) = WithZero.exp (-(m : ℤ)) := by
  rw [algebraMap_det_fO_eq K L v w θ c hcO hθ n hc, map_mul, map_pow, Valuation.map_neg, map_one, one_pow,
    one_mul]
  exact v_eq_exp_of_norm_eq_zpow K v hm

theorem fO_injective : Function.Injective (fO K L v w θ c hcO) := by
  intro y z hyz
  have h := congrArg (fun t : w.1.adicCompletionIntegers L => (t : w.1.adicCompletion L)) hyz
  simp only [fO_coe'] at h
  have hdet : LinearMap.det (phi K L v w θ c) ≠ 0 := by
    rw [det_phi K L v w θ c hθ n hc]
    refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) ?_
    intro h0
    have := v_eq_exp_of_norm_eq_zpow K v hm
    rw [h0, map_zero] at this
    exact WithZero.coe_ne_zero this.symm
  have hunit : IsUnit (phi K L v w θ c) := (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  have hker := (LinearMap.isUnit_iff_ker_eq_bot _).1 hunit
  have hinj : Function.Injective (phi K L v w θ c) := LinearMap.ker_eq_bot.1 hker
  exact Subtype.ext (hinj h)

end TheMap

section Uniformizer

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

theorem exp_neg_one_pow (m : ℕ) : (WithZero.exp (-1 : ℤ)) ^ m = WithZero.exp (-(m : ℤ)) := by
  rw [← WithZero.exp_nsmul, smul_neg, nsmul_one]

theorem isUnit_int_iff (x : v.adicCompletionIntegers K) :
    IsUnit x ↔ (Valued.v (x : v.adicCompletion K) : WithZero (Multiplicative ℤ)) = 1 :=
  Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers _)

theorem associated_of_v_eq {x y : v.adicCompletionIntegers K} (hy : y ≠ 0)
    (h : (Valued.v (x : v.adicCompletion K) : WithZero (Multiplicative ℤ)) = Valued.v (y : v.adicCompletion K)) :
    Associated x y := by
  have hy' : (y : v.adicCompletion K) ≠ 0 := fun h' => hy (Subtype.ext h')
  have hvy : (Valued.v (y : v.adicCompletion K) : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).2 hy'
  have hx' : (x : v.adicCompletion K) ≠ 0 := by
    intro h'
    rw [h', map_zero] at h
    exact hvy h.symm
  set t : v.adicCompletion K := (y : v.adicCompletion K) * (x : v.adicCompletion K)⁻¹ with ht
  have hvt : (Valued.v t : WithZero (Multiplicative ℤ)) = 1 := by
    rw [ht, map_mul, map_inv₀, h, mul_inv_cancel₀ hvy]
  have htO : t ∈ v.adicCompletionIntegers K := (mem_integers_iff_v K v t).2 hvt.le
  obtain ⟨u, hu⟩ := (isUnit_int_iff K v ⟨t, htO⟩).2 hvt
  refine ⟨u, Subtype.ext ?_⟩
  change (x : v.adicCompletion K) * ((u : v.adicCompletionIntegers K) : v.adicCompletion K) = y
  rw [hu]
  change (x : v.adicCompletion K) * t = y
  rw [ht, mul_comm, inv_mul_cancel_right₀ hx']

variable (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹)
include hϖ

theorem v_pi : (Valued.v ϖ : WithZero (Multiplicative ℤ)) = WithZero.exp (-1) :=
  v_eq_exp_of_norm_eq_zpow K v (k := -1) (by rw [hϖ, zpow_neg_one])

theorem pi_ne_zero : ϖ ≠ 0 := by
  intro h
  have := v_pi K v ϖ hϖ
  rw [h, map_zero] at this
  exact WithZero.coe_ne_zero this.symm

theorem pi_mem : ϖ ∈ v.adicCompletionIntegers K := by
  rw [mem_integers_iff_v, v_pi K v ϖ hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

def piO : v.adicCompletionIntegers K := ⟨ϖ, pi_mem K v ϖ hϖ⟩

theorem coe_piO : ((piO K v ϖ hϖ : v.adicCompletionIntegers K) : v.adicCompletion K) = ϖ := rfl

theorem irreducible_piO : Irreducible (piO K v ϖ hϖ) := by
  refine ⟨?_, fun a b hab => ?_⟩
  · rw [isUnit_int_iff, coe_piO, v_pi K v ϖ hϖ, ← WithZero.exp_zero]
    intro h
    have := WithZero.exp_injective h
    omega
  · have hv : (Valued.v (a : v.adicCompletion K) : WithZero (Multiplicative ℤ)) * Valued.v (b : v.adicCompletion K) =
        WithZero.exp (-1) := by
      rw [← map_mul, ← v_pi K v ϖ hϖ, ← coe_piO K v ϖ hϖ, hab]; rfl
    by_cases ha : IsUnit a
    · exact Or.inl ha
    · right
      have ha' : (Valued.v (a : v.adicCompletion K) : WithZero (Multiplicative ℤ)) < 1 :=
        (Valuation.Integer.not_isUnit_iff_valuation_lt_one (x := a)).1 ha
      have ha'' := le_exp_neg_one_of_lt_one ha'
      have hb1 : (Valued.v (b : v.adicCompletion K) : WithZero (Multiplicative ℤ)) ≤ 1 := b.2
      rw [isUnit_int_iff]
      refine le_antisymm hb1 ?_
      by_contra hlt
      push Not at hlt
      have hlt' : (Valued.v (a : v.adicCompletion K) : WithZero (Multiplicative ℤ)) * Valued.v (b : v.adicCompletion K) <
          WithZero.exp (-1) * 1 := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos ha'' hlt zero_le' WithZero.exp_pos
      rw [mul_one, hv] at hlt'
      exact lt_irrefl _ hlt'

theorem v_piO_pow (m : ℕ) :
    (Valued.v (((piO K v ϖ hϖ) ^ m : v.adicCompletionIntegers K) : v.adicCompletion K) : WithZero (Multiplicative ℤ)) =
      WithZero.exp (-(m : ℤ)) := by
  rw [SubmonoidClass.coe_pow, map_pow, coe_piO, v_pi K v ϖ hϖ, exp_neg_one_pow]

end Uniformizer

section DetAssociated

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
  (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
  (c : w.1.adicCompletion L) (hcO : c ∈ w.1.adicCompletionIntegers L)
  (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
  (n : v.adicCompletion K)
  (hc : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)), (θ ^ i) c =
    algebraMap (v.adicCompletion K) (w.1.adicCompletion L) n)
  (m : ℕ) (hm : ‖1 - n‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(m : ℤ)))
  (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹)
include hθ hc hm hϖ

theorem associated_det_fO : Associated (LinearMap.det (fO K L v w θ c hcO)) ((piO K v ϖ hϖ) ^ m) := by
  apply associated_of_v_eq K v
  · exact pow_ne_zero _ (irreducible_piO K v ϖ hϖ).ne_zero
  · rw [v_piO_pow]
    exact v_det_fO K L v w θ c hcO hθ n hc m hm

end DetAssociated

section Residue

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
  (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)

def thetaO : w.1.adicCompletionIntegers L ≃ₐ[v.adicCompletionIntegers K] w.1.adicCompletionIntegers L where
  toFun y := ⟨θ y, theta_mem K L v w θ y.2⟩
  invFun y := ⟨θ.symm y, theta_mem K L v w θ.symm y.2⟩
  left_inv y := Subtype.ext (θ.symm_apply_apply (y : w.1.adicCompletion L))
  right_inv y := Subtype.ext (θ.apply_symm_apply (y : w.1.adicCompletion L))
  map_mul' y z := Subtype.ext (map_mul θ (y : w.1.adicCompletion L) (z : w.1.adicCompletion L))
  map_add' y z := Subtype.ext (map_add θ (y : w.1.adicCompletion L) (z : w.1.adicCompletion L))
  commutes' r := Subtype.ext (θ.commutes (r : v.adicCompletion K))

theorem coe_thetaO (y : w.1.adicCompletionIntegers L) :
    ((thetaO K L v w θ y : w.1.adicCompletionIntegers L) : w.1.adicCompletion L) = θ y := rfl

theorem coe_thetaO_pow (i : ℕ) (y : w.1.adicCompletionIntegers L) :
    (((thetaO K L v w θ ^ i) y : w.1.adicCompletionIntegers L) : w.1.adicCompletion L) = (θ ^ i) y := by
  induction i generalizing y with
  | zero => rfl
  | succ i ih => rw [pow_succ, AlgEquiv.mul_apply, ih, pow_succ, AlgEquiv.mul_apply]; rfl

variable (c : w.1.adicCompletion L) (hcO : c ∈ w.1.adicCompletionIntegers L)

theorem fO_eq : fO K L v w θ c hcO =
    (thetaO K L v w θ : w.1.adicCompletionIntegers L →ₐ[v.adicCompletionIntegers K] w.1.adicCompletionIntegers L).toLinearMap -
      (⟨c, hcO⟩ : w.1.adicCompletionIntegers L) • LinearMap.id := by
  ext y
  rfl

abbrev kv : Type := IsLocalRing.ResidueField (v.adicCompletionIntegers K)

def sigmaV : (kv K v ⊗[v.adicCompletionIntegers K] w.1.adicCompletionIntegers L) ≃ₐ[kv K v]
    (kv K v ⊗[v.adicCompletionIntegers K] w.1.adicCompletionIntegers L) :=
  Algebra.TensorProduct.congr AlgEquiv.refl (thetaO K L v w θ)

theorem sigmaV_tmul (a : kv K v) (y : w.1.adicCompletionIntegers L) :
    sigmaV K L v w θ (a ⊗ₜ y) = a ⊗ₜ thetaO K L v w θ y := by
  simp [sigmaV, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]

theorem sigmaV_pow_tmul (i : ℕ) (a : kv K v) (y : w.1.adicCompletionIntegers L) :
    (sigmaV K L v w θ ^ i) (a ⊗ₜ y) = a ⊗ₜ (thetaO K L v w θ ^ i) y := by
  induction i generalizing y with
  | zero => rfl
  | succ i ih => rw [pow_succ, AlgEquiv.mul_apply, sigmaV_tmul, ih, pow_succ, AlgEquiv.mul_apply]

def cV : kv K v ⊗[v.adicCompletionIntegers K] w.1.adicCompletionIntegers L :=
  (1 : kv K v) ⊗ₜ (⟨c, hcO⟩ : w.1.adicCompletionIntegers L)

theorem fO_apply_eq (y : w.1.adicCompletionIntegers L) :
    fO K L v w θ c hcO y = thetaO K L v w θ y - (⟨c, hcO⟩ : w.1.adicCompletionIntegers L) * y :=
  Subtype.ext rfl

theorem cV_mul_tmul (a : kv K v) (y : w.1.adicCompletionIntegers L) :
    cV K L v w c hcO * (a ⊗ₜ y) = a ⊗ₜ ((⟨c, hcO⟩ : w.1.adicCompletionIntegers L) * y) := by
  rw [cV, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

set_option maxHeartbeats 3200000 in

theorem baseChange_fO_apply (z : kv K v ⊗[v.adicCompletionIntegers K] w.1.adicCompletionIntegers L) :
    (fO K L v w θ c hcO).baseChange (kv K v) z = sigmaV K L v w θ z - cV K L v w c hcO * z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
      rw [LinearMap.baseChange_tmul, fO_apply_eq, TensorProduct.tmul_sub, sigmaV_tmul, cV_mul_tmul]
  | add x y hx hy => rw [map_add, hx, hy, map_add, mul_add]; abel

end Residue

section ResidueField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
  (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
  (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹)
include hw hϖ

theorem map_maximalIdeal :
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).map
        (algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)) =
      IsLocalRing.maximalIdeal (w.1.adicCompletionIntegers L) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_int_iff, algebraMap_int_coe,
      v_algebraMap K L v w hw]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_int_iff] at hx
    exact hx
  · intro y hy
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy
    have hy' : (Valued.v (y : w.1.adicCompletion L) : WithZero (Multiplicative ℤ)) < 1 :=
      (Valuation.Integer.not_isUnit_iff_valuation_lt_one (x := y)).1 hy
    have hyle := le_exp_neg_one_of_lt_one hy'

    set πL : w.1.adicCompletion L := algebraMap (v.adicCompletion K) (w.1.adicCompletion L) ϖ with hπL
    have hvπ : (Valued.v πL : WithZero (Multiplicative ℤ)) = WithZero.exp (-1) := by
      rw [hπL, v_algebraMap K L v w hw, v_pi K v ϖ hϖ]
    have hπ0 : πL ≠ 0 := by
      intro h; rw [h, map_zero] at hvπ; exact WithZero.coe_ne_zero hvπ.symm
    have hq : (y : w.1.adicCompletion L) * πL⁻¹ ∈ w.1.adicCompletionIntegers L := by
      rw [mem_integers_iff_v, map_mul, map_inv₀, hvπ]
      calc (Valued.v (y : w.1.adicCompletion L) : WithZero (Multiplicative ℤ)) * (WithZero.exp (-1))⁻¹
          ≤ WithZero.exp (-1) * (WithZero.exp (-1))⁻¹ := mul_le_mul_left hyle _
        _ = 1 := mul_inv_cancel₀ WithZero.coe_ne_zero
    have hfac : y = algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) (piO K v ϖ hϖ) *
        ⟨(y : w.1.adicCompletion L) * πL⁻¹, hq⟩ := by
      apply Subtype.ext
      change (y : w.1.adicCompletion L) = algebraMap (v.adicCompletion K) (w.1.adicCompletion L) ϖ * ((y : w.1.adicCompletion L) * πL⁻¹)
      rw [← hπL, mul_left_comm, mul_inv_cancel₀ hπ0, mul_one]
    rw [hfac]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ((irreducible_piO K v ϖ hϖ).not_isUnit |>
      (IsLocalRing.mem_maximalIdeal _).2))

theorem isField_V : IsField (kv K v ⊗[v.adicCompletionIntegers K] w.1.adicCompletionIntegers L) := by
  have hmax : ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).map
      (algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L))).IsMaximal := by
    rw [map_maximalIdeal K L v w hw ϖ hϖ]; infer_instance
  have hF := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  exact MulEquiv.isField hF
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (w.1.adicCompletionIntegers L)
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))).symm.toMulEquiv

theorem tmul_eq_zero_iff (y : w.1.adicCompletionIntegers L) :
    ((1 : kv K v) ⊗ₜ[v.adicCompletionIntegers K] y :
        kv K v ⊗[v.adicCompletionIntegers K] w.1.adicCompletionIntegers L) = 0 ↔
      y ∈ IsLocalRing.maximalIdeal (w.1.adicCompletionIntegers L) := by
  have key : ((1 : kv K v) ⊗ₜ[v.adicCompletionIntegers K] y :
        kv K v ⊗[v.adicCompletionIntegers K] w.1.adicCompletionIntegers L) =
      Algebra.TensorProduct.quotIdealMapEquivQuotTensor (w.1.adicCompletionIntegers L)
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) (Ideal.Quotient.mk _ y) :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk _ _ y).symm
  have h1 := map_eq_zero_iff _ (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (w.1.adicCompletionIntegers L)
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))).injective (x := Ideal.Quotient.mk _ y)
  rw [Ideal.Quotient.eq_zero_iff_mem] at h1
  have h2 : y ∈ (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).map
        (algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)) ↔
      y ∈ IsLocalRing.maximalIdeal (w.1.adicCompletionIntegers L) := by
    rw [map_maximalIdeal K L v w hw ϖ hϖ]
  rw [key]
  exact h1.trans h2

end ResidueField

section CorankBound

p2m_attr_erase "instance" "IsLocalRing.ResidueField.algebraOfIsIntegral IsLocalRing.ResidueField.isScalarTowerOfIsIntegral"

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
  (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
  (c : w.1.adicCompletion L) (hcO : c ∈ w.1.adicCompletionIntegers L)

theorem finrank_int : Module.finrank (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) =
    Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := by
  classical
  haveI := isLocalization_int K L v w
  let b := Module.Free.chooseBasis (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis
    (b.localizationLocalization (v.adicCompletion K) (nonZeroDivisors (v.adicCompletionIntegers K))
      (w.1.adicCompletion L))]

theorem finrank_V : Module.finrank (kv K v) (kv K v ⊗[v.adicCompletionIntegers K] w.1.adicCompletionIntegers L) =
    Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := by
  rw [Module.finrank_baseChange, finrank_int]

variable (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
include hθ

set_option maxHeartbeats 3200000 in
theorem sigmaV_pow_finrank :
    sigmaV K L v w θ ^ Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1 := by
  refine AlgEquiv.ext fun z => ?_
  rw [AlgEquiv.one_apply]
  induction z using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul a y =>
      rw [sigmaV_pow_tmul]
      congr 1
      apply Subtype.ext
      rw [coe_thetaO_pow, ← hθ, pow_orderOf_eq_one, AlgEquiv.one_apply]
  | add x y hx hy => rw [map_add, hx, hy]

variable (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
  (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹)
  (hres : ∃ y : w.1.adicCompletion L, ‖y‖ ≤ 1 ∧ ‖θ y - y‖ = 1)
include hw hϖ hres

theorem sigmaV_ne_one : sigmaV K L v w θ ≠ 1 := by
  obtain ⟨y, hy1, hy2⟩ := hres
  have hyO : y ∈ w.1.adicCompletionIntegers L := (mem_integers_iff_v L w.1 y).2 (v_le_one_of_norm_le_one L w.1 hy1)
  intro h
  have h1 : sigmaV K L v w θ ((1 : kv K v) ⊗ₜ (⟨y, hyO⟩ : w.1.adicCompletionIntegers L)) =
      (1 : kv K v) ⊗ₜ (⟨y, hyO⟩ : w.1.adicCompletionIntegers L) := by rw [h, AlgEquiv.one_apply]
  rw [sigmaV_tmul, ← sub_eq_zero, ← TensorProduct.tmul_sub, tmul_eq_zero_iff K L v w hw ϖ hϖ,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1
  have h2 := (Valuation.Integer.not_isUnit_iff_valuation_lt_one
    (x := thetaO K L v w θ ⟨y, hyO⟩ - ⟨y, hyO⟩)).1 h1
  have h3 : (Valued.v (θ y - y) : WithZero (Multiplicative ℤ)) = 1 := v_eq_one_of_norm_eq_one L w.1 hy2
  change (Valued.v (θ y - y) : WithZero (Multiplicative ℤ)) < 1 at h2
  rw [h3] at h2
  exact lt_irrefl _ h2

variable (hprime : (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)).Prime)
include hprime

theorem orderOf_sigmaV : orderOf (sigmaV K L v w θ) = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := by
  haveI : Fact (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)).Prime := ⟨hprime⟩
  exact orderOf_eq_prime (sigmaV_pow_finrank K L v w θ hθ) (sigmaV_ne_one K L v w θ hθ hw ϖ hϖ hres)

variable (hcunit : (Valued.v c : WithZero (Multiplicative ℤ)) = 1)
include hcunit

abbrev VV : Type := kv K v ⊗[v.adicCompletionIntegers K] w.1.adicCompletionIntegers L

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem finrank_ker_le_one :
    Module.finrank (kv K v) (LinearMap.ker ((fO K L v w θ c hcO).baseChange (kv K v))) ≤ 1 := by
  classical

  letI hF : Field (VV K L v w) := (isField_V K L v w hw ϖ hϖ).toField
  haveI hnt : Nontrivial (VV K L v w) := inferInstance
  set σ : VV K L v w ≃ₐ[kv K v] VV K L v w := sigmaV K L v w θ with hσ
  set d := Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) with hd
  have hd0 : 0 < d := hprime.pos

  have hfix : IntermediateField.fixedField (Subgroup.zpowers σ) = (⊥ : IntermediateField (kv K v) (VV K L v w)) := by
    have h1 := IntermediateField.finrank_fixedField_eq_card (F := kv K v) (E := VV K L v w) (Subgroup.zpowers σ)
    rw [Nat.card_zpowers, hσ, orderOf_sigmaV K L v w θ hθ hw ϖ hϖ hres hprime] at h1
    have h2 := Module.finrank_mul_finrank (kv K v) (IntermediateField.fixedField (Subgroup.zpowers σ)) (VV K L v w)
    rw [h1, finrank_V, ← hd] at h2
    have h3 : Module.finrank (kv K v) (IntermediateField.fixedField (Subgroup.zpowers σ)) = 1 := by
      have : Module.finrank (kv K v) (IntermediateField.fixedField (Subgroup.zpowers σ)) * d = 1 * d := by
        rw [one_mul]; exact h2
      exact Nat.eq_of_mul_eq_mul_right hd0 this
    exact IntermediateField.finrank_eq_one_iff.1 h3

  have hcV : cV K L v w c hcO ≠ 0 := by
    have hu : IsUnit (⟨c, hcO⟩ : w.1.adicCompletionIntegers L) := (isUnit_int_iff L w.1 _).2 hcunit
    have hu' : IsUnit (cV K L v w c hcO) :=
      hu.map (Algebra.TensorProduct.includeRight :
        w.1.adicCompletionIntegers L →ₐ[v.adicCompletionIntegers K] VV K L v w)
    exact hu'.ne_zero

  set W := LinearMap.ker ((fO K L v w θ c hcO).baseChange (kv K v)) with hW
  by_cases hbot : W = ⊥
  · rw [hbot, finrank_bot]; exact zero_le_one
  obtain ⟨y₀, hy₀W, hy₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hker : ∀ y ∈ W, σ y = cV K L v w c hcO * y := by
    intro y hy
    rw [hW, LinearMap.mem_ker, baseChange_fO_apply, sub_eq_zero] at hy
    exact hy
  have hle : W ≤ Submodule.span (kv K v) {y₀} := by
    intro y hy
    set t : VV K L v w := y * y₀⁻¹ with ht
    have hσt : σ t = t := by
      rw [ht, map_mul, map_inv₀, hker y hy, hker y₀ hy₀W, mul_inv_rev]
      calc cV K L v w c hcO * y * (y₀⁻¹ * (cV K L v w c hcO)⁻¹)
          = y * y₀⁻¹ * (cV K L v w c hcO * (cV K L v w c hcO)⁻¹) := by ring
        _ = y * y₀⁻¹ := by rw [mul_inv_cancel₀ hcV, mul_one]
    have hstab : Subgroup.zpowers σ ≤ MulAction.stabilizer (VV K L v w ≃ₐ[kv K v] VV K L v w) t :=
      Subgroup.zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff]; exact hσt)
    have htfix : t ∈ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.mem_fixedField_iff]
      intro g hg
      exact hstab hg
    rw [hfix, IntermediateField.mem_bot] at htfix
    obtain ⟨a, ha⟩ := htfix
    rw [Submodule.mem_span_singleton]
    refine ⟨a, ?_⟩
    rw [Algebra.smul_def, ha, ht, inv_mul_cancel_right₀ hy₀]
  calc Module.finrank (kv K v) W ≤ Module.finrank (kv K v) (Submodule.span (kv K v) {y₀}) :=
        Submodule.finrank_mono hle
    _ = 1 := finrank_span_singleton hy₀
    _ ≤ 1 := le_rfl

end CorankBound

section Transport

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
  (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
  (c : w.1.adicCompletion L) (hcO : c ∈ w.1.adicCompletionIntegers L)
  (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) (s : ℕ)

theorem finite_residueField : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  exact Finite.of_equiv _ (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField K v).toEquiv

theorem card_residueField : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) = Ideal.absNorm v.asIdeal := by
  rw [← Nat.card_congr (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField K v).toEquiv,
    Ideal.absNorm_apply, Submodule.cardQuot_apply]

abbrev pis : w.1.adicCompletion L := algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ s)

theorem pis_eq : pis K L v w ϖ s =
    ((algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) ((piO K v ϖ hϖ) ^ s) :
      w.1.adicCompletionIntegers L) : w.1.adicCompletion L) := by
  rw [algebraMap_int_coe, SubmonoidClass.coe_pow, coe_piO]

include hϖ in
theorem pis_ne_zero : pis K L v w ϖ s ≠ 0 :=
  (map_ne_zero _).2 (pow_ne_zero _ (pi_ne_zero K v ϖ hϖ))

theorem theta_pis : θ (pis K L v w ϖ s) = pis K L v w ϖ s := θ.commutes _

include hϖ in
theorem mulLeft_pis_injective : Function.Injective (AddMonoidHom.mulLeft (pis K L v w ϖ s)) := by
  intro x y hxy
  exact mul_left_cancel₀ (pis_ne_zero K L v w ϖ hϖ s) hxy

abbrev iota : w.1.adicCompletionIntegers L →+ w.1.adicCompletion L :=
  (w.1.adicCompletionIntegers L).subtype.toAddMonoidHom

theorem iota_apply (y : w.1.adicCompletionIntegers L) : iota K L v w y = (y : w.1.adicCompletion L) := rfl

theorem iota_injective : Function.Injective (iota K L v w) := fun _ _ h => Subtype.ext h

theorem map_iota_smul_top :
    ((Ideal.span {(piO K v ϖ hϖ) ^ s} • ⊤ :
        Submodule (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)).toAddSubgroup).map (iota K L v w) =
    (w.1.adicCompletionIntegers L).toAddSubgroup.map (AddMonoidHom.mulLeft (pis K L v w ϖ s)) := by
  ext x
  rw [AddSubgroup.mem_map, AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Submodule.mem_toAddSubgroup, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨z, -, rfl⟩ := hy
    refine ⟨(z : w.1.adicCompletion L), z.2, ?_⟩
    rw [AddMonoidHom.coe_mulLeft, iota_apply, pis_eq K L v w ϖ hϖ s]
    rfl
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(piO K v ϖ hϖ ^ s) • (⟨t, ht⟩ : w.1.adicCompletionIntegers L), ?_, ?_⟩
    · rw [Submodule.mem_toAddSubgroup, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨⟨t, ht⟩, Submodule.mem_top, rfl⟩
    · rw [AddMonoidHom.coe_mulLeft, iota_apply, pis_eq K L v w ϖ hϖ s]
      rfl

theorem map_iota_comap :
    (((Ideal.span {(piO K v ϖ hϖ) ^ s} • ⊤ :
        Submodule (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)).comap
          (fO K L v w θ c hcO)).toAddSubgroup).map (iota K L v w) =
    (((w.1.adicCompletionIntegers L).toAddSubgroup.comap
        (θ.toAlgHom.toRingHom.toAddMonoidHom - AddMonoidHom.mulLeft c)) ⊓
      ((w.1.adicCompletionIntegers L).toAddSubgroup.comap
        (AddMonoidHom.mulLeft (pis K L v w ϖ s)))).map (AddMonoidHom.mulLeft (pis K L v w ϖ s)) := by
  have hπ0 := pis_ne_zero K L v w ϖ hϖ s
  ext x
  rw [AddSubgroup.mem_map, AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Submodule.mem_toAddSubgroup, Submodule.mem_comap, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨z, -, hz⟩ := hy
    have hz' : θ y - c * y = pis K L v w ϖ s * z := by
      have h1 := congrArg (fun t : w.1.adicCompletionIntegers L => (t : w.1.adicCompletion L)) hz
      simp only [fO_coe] at h1
      rw [← h1, pis_eq K L v w ϖ hϖ s]
      rfl
    refine ⟨(y : w.1.adicCompletion L) * (pis K L v w ϖ s)⁻¹, ⟨?_, ?_⟩, ?_⟩
    · change θ ((y : w.1.adicCompletion L) * (pis K L v w ϖ s)⁻¹) -
        c * ((y : w.1.adicCompletion L) * (pis K L v w ϖ s)⁻¹) ∈ w.1.adicCompletionIntegers L
      rw [map_mul, map_inv₀, theta_pis, ← mul_assoc, ← sub_mul, hz', mul_comm, inv_mul_cancel_left₀ hπ0]
      exact z.2
    · change pis K L v w ϖ s * ((y : w.1.adicCompletion L) * (pis K L v w ϖ s)⁻¹) ∈ w.1.adicCompletionIntegers L
      rw [mul_comm, inv_mul_cancel_right₀ hπ0]
      exact y.2
    · rw [AddMonoidHom.coe_mulLeft, iota_apply, mul_comm, inv_mul_cancel_right₀ hπ0]
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    change θ t - c * t ∈ w.1.adicCompletionIntegers L at h1
    change pis K L v w ϖ s * t ∈ w.1.adicCompletionIntegers L at h2
    refine ⟨⟨pis K L v w ϖ s * t, h2⟩, ?_, rfl⟩
    rw [Submodule.mem_toAddSubgroup, Submodule.mem_comap, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨⟨θ t - c * t, h1⟩, Submodule.mem_top, Subtype.ext ?_⟩
    rw [fO_coe]
    change ((algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) ((piO K v ϖ hϖ) ^ s) :
        w.1.adicCompletionIntegers L) : w.1.adicCompletion L) * (θ t - c * t) =
      θ (pis K L v w ϖ s * t) - c * (pis K L v w ϖ s * t)
    rw [← pis_eq K L v w ϖ hϖ s, map_mul, theta_pis]
    ring

end Transport

theorem main
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (hprime : (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)).Prime)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
    (hres : ∃ y : w.1.adicCompletion L, ‖y‖ ≤ 1 ∧ ‖θ y - y‖ = 1)
    (c : w.1.adicCompletion L) (n : v.adicCompletion K) (hn : ‖n‖ = 1) (m : ℕ)
    (hm : ‖1 - n‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(m : ℤ)))
    (hc : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)), (θ ^ i) c =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) n)
    (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) (s : ℕ) :
    (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex
        (((w.1.adicCompletionIntegers L).toAddSubgroup.comap
            (θ.toAlgHom.toRingHom.toAddMonoidHom - AddMonoidHom.mulLeft c)) ⊓
          ((w.1.adicCompletionIntegers L).toAddSubgroup.comap
            (AddMonoidHom.mulLeft
              (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ s))))) =
      Ideal.absNorm v.asIdeal ^ min s m := by
  have hn1 : (Valued.v n : WithZero (Multiplicative ℤ)) = 1 := v_eq_one_of_norm_eq_one K v hn
  have hcunit := v_c_eq_one K L v w θ hw hprime.pos c n hn1 hc
  have hcO : c ∈ w.1.adicCompletionIntegers L := (mem_integers_iff_v L w.1 c).2 hcunit.le
  haveI := finite_residueField K v
  have hI := LinearMap.relIndex_pow_smul_top_comap_eq_card_pow_min_of_finrank_ker_baseChange_le_one
    (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) (fO K L v w θ c hcO)
    (fO_injective K L v w θ c hcO hθ n hc m hm)
    (finrank_ker_le_one K L v w θ c hcO hθ hw ϖ hϖ hres hprime hcunit)
    (piO K v ϖ hϖ) (irreducible_piO K v ϖ hϖ) m
    (associated_det_fO K L v w θ c hcO hθ n hc m hm ϖ hϖ) s
  rw [card_residueField] at hI
  rw [← hI, ← AddSubgroup.relIndex_map_map_of_injective _ _ (iota_injective K L v w),
    map_iota_smul_top K L v w ϖ hϖ s, map_iota_comap K L v w θ c hcO ϖ hϖ s,
    AddSubgroup.relIndex_map_map_of_injective _ _ (mulLeft_pis_injective K L v w ϖ hϖ s)]

end P2mLocalIndex
p2m_reactivate "P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one.P2mLocalIndex"

end
p2m_reactivate "P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one.P2mLocalIndex"

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (hprime : (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)).Prime)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
    (hres : ∃ y : w.1.adicCompletion L, ‖y‖ ≤ 1 ∧ ‖θ y - y‖ = 1)
    (c : w.1.adicCompletion L) (n : v.adicCompletion K) (hn : ‖n‖ = 1) (m : ℕ)
    (hm : ‖1 - n‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(m : ℤ)))
    (hc : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)), (θ ^ i) c =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) n)
    (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) (s : ℕ) :
    (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex
        (((w.1.adicCompletionIntegers L).toAddSubgroup.comap
            (θ.toAlgHom.toRingHom.toAddMonoidHom - AddMonoidHom.mulLeft c)) ⊓
          ((w.1.adicCompletionIntegers L).toAddSubgroup.comap
            (AddMonoidHom.mulLeft
              (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ s))))) =
      Ideal.absNorm v.asIdeal ^ min s m :=
  P2mLocalIndex.main K L v w hw hprime θ hθ hres c n hn m hm hc ϖ hϖ s

end S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one (solution)
