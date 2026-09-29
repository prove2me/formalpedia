-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ad66017c-2bab-5be9-b47c-155673794fe7

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_RatIdele_Normalizer
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_valued_eq_exp_of_coe_eq_diagonal_of_not_valued_lt
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isHeckeCosetSystem_heckeGen1_cosetSum_twoRowPointLocal
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isHeckeCosetSystem_heckeGen2_cosetSum_twoRowPointLocal
import Theorems.Thm_LanglandsTunnell_CubicInduction_cosetSum_isRightInvariant_and_isGL3PsiWhittakerFn
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn
import Theorems.Thm_LanglandsTunnell_CubicInduction_finsum_primeFibre_inertiaDeg_eq_three_of_not_isRamifiedIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

set_option autoImplicit false

open IsDedekindDomain NumberField
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace.LanglandsTunnell.CubicInduction"

noncomputable section

section MatrixValuations

open Matrix

namespace IwasawaUniqueness

section Unipotent

variable {A : Type*} [CommRing A]

private theorem unip_mul (x y z x' y' z' : A) :
    upperUnipotent3 x y z * upperUnipotent3 x' y' z' = upperUnipotent3 (x + x') (y + y') (z + z' + x * y') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent3, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

private theorem unip_inv (x y z : A) : (upperUnipotent3 x y z)⁻¹ = upperUnipotent3 (-x) (-y) (x * y - z) :=
  Units.ext rfl

private theorem unip_det (x y z : A) : (upperUnipotent3 x y z : Matrix (Fin 3) (Fin 3) A).det = 1 := by
  rw [upperUnipotent3_coe, Matrix.det_fin_three]; simp

end Unipotent

section Integral

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem exists_mapMatrix_eq' (M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
    (hM : ∀ i j, Valued.v (M i j) ≤ 1) :
    ∃ N : Matrix (Fin 3) (Fin 3) (v.adicCompletionIntegers ℚ),
      (v.adicCompletionIntegers ℚ).subtype.mapMatrix N = M :=
  ⟨Matrix.of fun i j => ⟨M i j, (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 (hM i j)⟩,
    by ext i j; rfl⟩

private theorem valued_det_le_one' (M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
    (hM : ∀ i j, Valued.v (M i j) ≤ 1) : Valued.v M.det ≤ 1 := by
  obtain ⟨N, rfl⟩ := exists_mapMatrix_eq' M hM
  rw [← RingHom.map_det]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 N.det.2

private theorem eq_one_and_eq_one_of_mul_eq_one' {a b : WithZero (Multiplicative ℤ)} (h : a * b = 1) (ha : a ≤ 1)
    (hb : b ≤ 1) : a = 1 ∧ b = 1 := by
  refine ⟨le_antisymm ha ?_, le_antisymm hb ?_⟩
  · calc (1 : WithZero (Multiplicative ℤ)) = a * b := h.symm
      _ ≤ a * 1 := mul_le_mul' le_rfl hb
      _ = a := mul_one a
  · calc (1 : WithZero (Multiplicative ℤ)) = a * b := h.symm
      _ ≤ 1 * b := mul_le_mul' ha le_rfl
      _ = b := one_mul b

private theorem valued_det_eq_one_of_mem' {k : LocalGL3 v} (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) = 1 := by
  have h₁ := valued_det_le_one' _ hk.1
  have h₂ := valued_det_le_one' _ hk.2
  have hprod : Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) *
      Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) = 1 := by
    rw [← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one]
  exact (eq_one_and_eq_one_of_mul_eq_one' hprod h₁ h₂).1

end Integral

section Invariants

variable {v : HeightOneSpectrum (𝓞 ℚ)}

private theorem inv_mul_diagonal {t : LocalGL3 v} {d : Fin 3 → v.adicCompletion ℚ}
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) :
    ((t⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) * Matrix.diagonal d = 1 := by
  rw [← ht]
  exact Units.inv_mul t

private theorem inv_apply_mul_diag {t : LocalGL3 v} {d : Fin 3 → v.adicCompletion ℚ}
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) (i j : Fin 3) :
    ((t⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j * d j =
      (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j := by
  rw [← inv_mul_diagonal ht, Matrix.mul_diagonal]

private theorem inv_apply_mul_self {t : LocalGL3 v} {d : Fin 3 → v.adicCompletion ℚ}
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) (i : Fin 3) :
    ((t⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i i * d i = 1 := by
  have h := inv_apply_mul_diag ht i i
  rwa [Matrix.one_apply_eq] at h

private theorem ne_zero_of_coe_eq_diagonal {t : LocalGL3 v} {d : Fin 3 → v.adicCompletion ℚ}
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) (i : Fin 3) : d i ≠ 0 :=
  right_ne_zero_of_mul_eq_one (inv_apply_mul_self ht i)

private theorem valued_row_two_le (x y z : v.adicCompletion ℚ) {t : LocalGL3 v} {d : Fin 3 → v.adicCompletion ℚ}
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) (l : Fin 3) :
    Valued.v (((upperUnipotent3 x y z * t : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 l) ≤
      Valued.v (d 2) := by
  rw [Units.val_mul, ht, upperUnipotent3_coe, Matrix.mul_diagonal]
  fin_cases l <;> simp

private theorem row_two_two (x y z : v.adicCompletion ℚ) {t : LocalGL3 v} {d : Fin 3 → v.adicCompletion ℚ}
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) :
    ((upperUnipotent3 x y z * t : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 = d 2 := by
  rw [Units.val_mul, ht, upperUnipotent3_coe, Matrix.mul_diagonal]
  simp

private theorem valued_bottom_le (x y z : v.adicCompletion ℚ) {t : LocalGL3 v} {d : Fin 3 → v.adicCompletion ℚ}
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) {k : LocalGL3 v}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) (j : Fin 3) :
    Valued.v (((upperUnipotent3 x y z * t * k : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 j) ≤
      Valued.v (d 2) := by
  rw [Units.val_mul]
  exact valued_mul_apply_le3 (𝓞 ℚ) ℚ v (fun l => valued_row_two_le x y z ht l) (fun l => hk.1 l j)

private theorem le_of_bottom (x y z : v.adicCompletion ℚ) {t : LocalGL3 v} {d : Fin 3 → v.adicCompletion ℚ}
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) {k : LocalGL3 v}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) {C : WithZero (Multiplicative ℤ)}
    (hC : ∀ j, Valued.v
      (((upperUnipotent3 x y z * t * k : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 j) ≤ C) :
    Valued.v (d 2) ≤ C := by
  rw [← row_two_two x y z ht, (mul_inv_cancel_right (upperUnipotent3 x y z * t) k).symm, Units.val_mul]
  exact valued_mul_apply_le3 (𝓞 ℚ) ℚ v hC (fun l => hk.2 l 2)

private theorem inv_col_zero (x y z : v.adicCompletion ℚ) (t : LocalGL3 v) (m : Fin 3) :
    ((t⁻¹ * (upperUnipotent3 x y z)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) m 0 =
      ((t⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) m 0 := by
  rw [Units.val_mul, unip_inv, upperUnipotent3_coe, Matrix.mul_apply, Fin.sum_univ_three]
  simp

private theorem inv_apply_mul_le (x y z : v.adicCompletion ℚ) {t : LocalGL3 v} {d : Fin 3 → v.adicCompletion ℚ}
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) {k : LocalGL3 v}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) (l : Fin 3) :
    Valued.v ((((upperUnipotent3 x y z * t * k)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) l 0 *
      d 0) ≤ 1 := by
  have hX : ∀ m : Fin 3,
      (((t⁻¹ * (upperUnipotent3 x y z)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
        Matrix.diagonal d) m 0 = (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) m 0 := fun m => by
    rw [Matrix.mul_diagonal, inv_col_zero]
    exact inv_apply_mul_diag ht m 0
  have hentry :
      (((upperUnipotent3 x y z * t * k)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) l 0 * d 0 =
        ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) l 0 := by
    calc (((upperUnipotent3 x y z * t * k)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) l 0 * d 0
        = ((((upperUnipotent3 x y z * t * k)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
            Matrix.diagonal d) l 0 := (Matrix.mul_diagonal d _ l 0).symm
      _ = (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
            ((((t⁻¹ * (upperUnipotent3 x y z)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) *
              Matrix.diagonal d)) l 0 := by
          rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
      _ = (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
            (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) l 0 := by
          rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_three, hX 0, hX 1, hX 2]
      _ = ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) l 0 := by rw [Matrix.mul_one]
  rw [hentry]
  exact hk.2 l 0

private theorem mul_inv_apply_mul_eq_one (x y z : v.adicCompletion ℚ) {t : LocalGL3 v}
    {d : Fin 3 → v.adicCompletion ℚ} (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d)
    (k : LocalGL3 v) :
    ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
        (((upperUnipotent3 x y z * t * k)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) 0 0 *
      d 0 = 1 := by
  have h1 : (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
      (((upperUnipotent3 x y z * t * k)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
        ((t⁻¹ * (upperUnipotent3 x y z)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) := by
    rw [← Units.val_mul, _root_.mul_inv_rev, _root_.mul_inv_rev, mul_inv_cancel_left]
  rw [h1, inv_col_zero]
  exact inv_apply_mul_self ht 0

private theorem le_of_integral_column {Q K' : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {e e' : v.adicCompletion ℚ}
    (hK' : ∀ l, Valued.v (K' 0 l) ≤ 1) (hF : ∀ l, Valued.v (Q l 0 * e) ≤ 1) (hR : (K' * Q) 0 0 * e' = 1) :
    Valued.v e ≤ Valued.v e' := by
  have hb : ∀ l, Valued.v ((Q * Matrix.diagonal (fun _ : Fin 3 => e)) l 0) ≤ 1 := fun l => by
    rw [Matrix.mul_diagonal]
    exact hF l
  have hint : Valued.v ((K' * Q) 0 0 * e) ≤ 1 := by
    have h := valued_mul_apply_le3 (𝓞 ℚ) ℚ v hK' hb
    rwa [← Matrix.mul_assoc, Matrix.mul_diagonal] at h
  have he : e = (K' * Q) 0 0 * e * e' := by
    calc e = e * ((K' * Q) 0 0 * e') := by rw [hR, mul_one]
      _ = (K' * Q) 0 0 * e * e' := by ring
  calc Valued.v e = Valued.v ((K' * Q) 0 0 * e * e') := congrArg (fun a => Valued.v a) he
    _ = Valued.v ((K' * Q) 0 0 * e) * Valued.v e' := by rw [map_mul]
    _ ≤ 1 * Valued.v e' := mul_le_mul' hint le_rfl
    _ = Valued.v e' := one_mul _

private theorem valued_det_eq (x y z : v.adicCompletion ℚ) {t : LocalGL3 v} {d : Fin 3 → v.adicCompletion ℚ}
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d) {k : LocalGL3 v}
    (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    Valued.v (((upperUnipotent3 x y z * t * k : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det) =
      Valued.v (d 0) * Valued.v (d 1) * Valued.v (d 2) := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, unip_det, ht, Matrix.det_diagonal,
    Fin.prod_univ_three, one_mul, map_mul, valued_det_eq_one_of_mem' hk, mul_one, map_mul, map_mul]

private theorem quot_apply_zero_one (x y z x' y' z' : v.adicCompletion ℚ) :
    (((upperUnipotent3 x' y' z')⁻¹ * upperUnipotent3 x y z : LocalGL3 v) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1 = x - x' := by
  rw [unip_inv, unip_mul, upperUnipotent3_coe]
  simp
  ring

private theorem quot_apply_one_two (x y z x' y' z' : v.adicCompletion ℚ) :
    (((upperUnipotent3 x' y' z')⁻¹ * upperUnipotent3 x y z : LocalGL3 v) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 2 = y - y' := by
  rw [unip_inv, unip_mul, upperUnipotent3_coe]
  simp
  ring

private theorem conj_apply_mul {t t' : LocalGL3 v} {d d' : Fin 3 → v.adicCompletion ℚ}
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d)
    (ht' : (t' : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d') (M : LocalGL3 v) (p q : Fin 3) :
    ((t' * M * t⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) p q * d q =
      d' p * (M : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) p q := by
  rw [Units.val_mul, ← Matrix.mul_diagonal d, Matrix.mul_assoc, inv_mul_diagonal ht, Matrix.mul_one, Units.val_mul,
    ht', Matrix.diagonal_mul]

private theorem le_one_of_mul_le {a c u : WithZero (Multiplicative ℤ)} (hcu : c * u = 1) (hac : a * c ≤ c) : a ≤ 1 :=
  calc a = a * (c * u) := by rw [hcu, mul_one]
    _ = a * c * u := (mul_assoc a c u).symm
    _ ≤ c * u := mul_le_mul' hac le_rfl
    _ = 1 := hcu

private theorem valued_le_one_of_mul_eq {a e e₁ m u : v.adicCompletion ℚ} (hae : a * e₁ = e * m) (hu : u * e₁ = 1)
    (hm : Valued.v m ≤ 1) (he : Valued.v e ≤ Valued.v e₁) : Valued.v a ≤ 1 := by
  have hcu : Valued.v e₁ * Valued.v u = 1 := by
    rw [← map_mul, mul_comm, hu, map_one]
  have hac : Valued.v a * Valued.v e₁ ≤ Valued.v e₁ := by
    rw [← map_mul, hae, map_mul]
    calc Valued.v e * Valued.v m ≤ Valued.v e₁ * 1 := mul_le_mul' he hm
      _ = Valued.v e₁ := mul_one _
  exact le_one_of_mul_le hcu hac

end Invariants

end IwasawaUniqueness

open IwasawaUniqueness

namespace LanglandsTunnell p2m_export "LanglandsTunnell" "RankinSelberg.primeFibre RankinSelberg.mem_primeFibre RankinSelberg.inducedFactor RankinSelberg.inducedEulerPoly RankinSelberg.inducedE1 RankinSelberg.inducedE2 RankinSelberg.inducedE3" namespace CubicInduction p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn inducedCoeff psiLoc upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero coe_iotaGL valued_mul_apply_le3 localMaximalCompact3 LocalGL3 varpi varpi_ne_zero heckeGen1 heckeGen2 centralGen cNormQ cosetSum IsCosetEigenfunction IsRightInvariant IsInducedSphericalAt IsBadPlace ratPrimeAt ratPrimeUnit iotaTorusLocal iotaTorusLocal_zero sphericalTorusValue coe_diagUnits2 twoRowPointLocal twoRowPointLocal_zero_right HasSphericalTorusValuesAt exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3 exists_valued_eq_exp_of_coe_eq_diagonal_of_not_valued_lt eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant exists_isHeckeCosetSystem_heckeGen1_cosetSum_twoRowPointLocal exists_isHeckeCosetSystem_heckeGen2_cosetSum_twoRowPointLocal cosetSum_isRightInvariant_and_isGL3PsiWhittakerFn eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn finsum_primeFibre_inertiaDeg_eq_three_of_not_isRamifiedIn" end LanglandsTunnell.CubicInduction
p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.valued_eq_of_upperUnipotent3_mul_mul_eq_of_coe_eq_diagonal
    (v : HeightOneSpectrum (𝓞 ℚ)) (x y z x' y' z' : v.adicCompletion ℚ) (t t' : LocalGL3 v)
    (d d' : Fin 3 → v.adicCompletion ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d)
    (ht' : (t' : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d')
    (k k' : LocalGL3 v) (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) (hk' : k' ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (h : upperUnipotent3 x y z * t * k = upperUnipotent3 x' y' z' * t' * k') :
    ∀ i : Fin 3, Valued.v (d i) = Valued.v (d' i) := by
  have h2 : Valued.v (d 2) = Valued.v (d' 2) := by
    refine le_antisymm ?_ ?_
    · refine le_of_bottom x y z ht hk fun j => ?_
      rw [h]
      exact valued_bottom_le x' y' z' ht' hk' j
    · refine le_of_bottom x' y' z' ht' hk' fun j => ?_
      rw [← h]
      exact valued_bottom_le x y z ht hk j
  have h0 : Valued.v (d 0) = Valued.v (d' 0) := by
    refine le_antisymm ?_ ?_
    · refine le_of_integral_column (fun l => hk'.1 0 l) (inv_apply_mul_le x y z ht hk) ?_
      rw [h]
      exact mul_inv_apply_mul_eq_one x' y' z' ht' k'
    · refine le_of_integral_column (fun l => hk.1 0 l) (inv_apply_mul_le x' y' z' ht' hk') ?_
      rw [← h]
      exact mul_inv_apply_mul_eq_one x y z ht k
  have hdet : Valued.v (d 0) * Valued.v (d 1) * Valued.v (d 2) =
      Valued.v (d' 0) * Valued.v (d' 1) * Valued.v (d' 2) := by
    rw [← valued_det_eq x y z ht hk, ← valued_det_eq x' y' z' ht' hk', h]
  have h1 : Valued.v (d 1) = Valued.v (d' 1) := by
    rw [h0, h2] at hdet
    have hne0 : Valued.v (d' 0) ≠ 0 := (Valuation.ne_zero_iff Valued.v).2 (ne_zero_of_coe_eq_diagonal ht' 0)
    have hne2 : Valued.v (d' 2) ≠ 0 := (Valuation.ne_zero_iff Valued.v).2 (ne_zero_of_coe_eq_diagonal ht' 2)
    exact mul_left_cancel₀ hne0 (mul_right_cancel₀ hne2 hdet)
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in

private theorem LanglandsTunnell.CubicInduction.valued_sub_le_one_of_upperUnipotent3_mul_mul_eq_of_not_valued_lt
    (v : HeightOneSpectrum (𝓞 ℚ)) (x y z x' y' z' : v.adicCompletion ℚ) (t t' : LocalGL3 v)
    (d d' : Fin 3 → v.adicCompletion ℚ)
    (ht : (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d)
    (ht' : (t' : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d')
    (hd : ¬ (Valued.v (d 1) < Valued.v (d 0) ∨ Valued.v (d 2) < Valued.v (d 1)))
    (k k' : LocalGL3 v) (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) (hk' : k' ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (h : upperUnipotent3 x y z * t * k = upperUnipotent3 x' y' z' * t' * k') :
    Valued.v (x - x') ≤ 1 ∧ Valued.v (y - y') ≤ 1 := by
  have hR2 :=
    valued_eq_of_upperUnipotent3_mul_mul_eq_of_coe_eq_diagonal v x y z x' y' z' t t' d d' ht ht' k k' hk hk' h
  have hd01 : Valued.v (d 0) ≤ Valued.v (d 1) := not_lt.1 fun hlt => hd (Or.inl hlt)
  have hd12 : Valued.v (d 1) ≤ Valued.v (d 2) := not_lt.1 fun hlt => hd (Or.inr hlt)
  have hM : k' * k⁻¹ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v :=
    (localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem hk' ((localMaximalCompact3 (𝓞 ℚ) ℚ v).inv_mem hk)
  have hrel : (upperUnipotent3 x' y' z')⁻¹ * upperUnipotent3 x y z = t' * (k' * k⁻¹) * t⁻¹ := by
    have h' : upperUnipotent3 x y z = upperUnipotent3 x' y' z' * t' * k' * k⁻¹ * t⁻¹ := by
      rw [← h, mul_inv_cancel_right, mul_inv_cancel_right]
    rw [h']
    simp only [mul_assoc, inv_mul_cancel_left]
  have hmat : (((upperUnipotent3 x' y' z')⁻¹ * upperUnipotent3 x y z : LocalGL3 v) :
      Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
        ((t' * (k' * k⁻¹) * t⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) :=
    congrArg Units.val hrel
  constructor
  · have hae : (x - x') * d 1 =
        d' 0 * ((k' * k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 0 1 := by
      rw [← quot_apply_zero_one x y z x' y' z', hmat, conj_apply_mul ht ht' (k' * k⁻¹) 0 1]
    have he : Valued.v (d' 0) ≤ Valued.v (d 1) := by
      rw [← hR2 0]
      exact hd01
    exact valued_le_one_of_mul_eq hae (inv_apply_mul_self ht 1) (hM.1 0 1) he
  · have hae : (y - y') * d 2 =
        d' 1 * ((k' * k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 2 := by
      rw [← quot_apply_one_two x y z x' y' z', hmat, conj_apply_mul ht ht' (k' * k⁻¹) 1 2]
    have he : Valued.v (d' 1) ≤ Valued.v (d 2) := by
      rw [← hR2 1]
      exact hd12
    exact valued_le_one_of_mul_eq hae (inv_apply_mul_self ht 2) (hM.1 1 2) he

end MatrixValuations

section TorusPoints

open NumberField.AdelicLevel

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RankinSelberg.primeFibre RankinSelberg.mem_primeFibre RankinSelberg.inducedFactor RankinSelberg.inducedEulerPoly RankinSelberg.inducedE1 RankinSelberg.inducedE2 RankinSelberg.inducedE3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn inducedCoeff psiLoc upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero coe_iotaGL valued_mul_apply_le3 localMaximalCompact3 LocalGL3 varpi varpi_ne_zero heckeGen1 heckeGen2 centralGen cNormQ cosetSum IsCosetEigenfunction IsRightInvariant IsInducedSphericalAt IsBadPlace ratPrimeAt ratPrimeUnit iotaTorusLocal iotaTorusLocal_zero sphericalTorusValue coe_diagUnits2 twoRowPointLocal twoRowPointLocal_zero_right HasSphericalTorusValuesAt exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3 exists_valued_eq_exp_of_coe_eq_diagonal_of_not_valued_lt eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant exists_isHeckeCosetSystem_heckeGen1_cosetSum_twoRowPointLocal exists_isHeckeCosetSystem_heckeGen2_cosetSum_twoRowPointLocal cosetSum_isRightInvariant_and_isGL3PsiWhittakerFn eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn finsum_primeFibre_inertiaDeg_eq_three_of_not_isRamifiedIn"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section PlaceArithmetic

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem absNorm_asIdeal_eq_natGenerator : Ideal.absNorm v.asIdeal = Rat.HeightOneSpectrum.natGenerator v := by
  rw [RatIdele.asIdeal_eq_span_natGenerator v, Ideal.absNorm_span_singleton,
    ← map_natCast (algebraMap ℤ (𝓞 ℚ)) (Rat.HeightOneSpectrum.natGenerator v), Algebra.norm_algebraMap,
    RingOfIntegers.rank, Module.finrank_self, pow_one, Int.natAbs_natCast]

private theorem ratPrimeAt_eq_algebraMap :
    ratPrimeAt v = algebraMap ℚ (v.adicCompletion ℚ) ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) := by
  simp only [ratPrimeAt, map_natCast]

private theorem valued_ratPrimeAt : Valued.v (ratPrimeAt v) = WithZero.exp (-1 : ℤ) := by
  rw [ratPrimeAt_eq_algebraMap, RatIdele.valued_algebraMap_rat, absNorm_asIdeal_eq_natGenerator]
  exact RatIdele.valuation_natGenerator v

private def scalarGL3 : (v.adicCompletion ℚ)ˣ →* LocalGL3 v :=
  Matrix.GeneralLinearGroup.scalar (Fin 3)

private theorem coe_scalarGL3 (u : (v.adicCompletion ℚ)ˣ) :
    ((scalarGL3 v u : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal fun _ => (u : v.adicCompletion ℚ) := by
  show Matrix.scalar (Fin 3) (u : v.adicCompletion ℚ) = _
  rw [Matrix.scalar_apply]

private theorem scalarGL3_mul_comm (u : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    scalarGL3 v u * g = g * scalarGL3 v u := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_scalarGL3]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact mul_comm _ _

private theorem coe_centralGen :
    ((centralGen v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![varpi v, varpi v, varpi v] :=
  rfl

private theorem centralGen_eq_scalarGL3 : centralGen v = scalarGL3 v (uniformizerUnit ℚ v) := by
  apply Units.ext
  rw [coe_centralGen, coe_scalarGL3]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem coe_twoRowPointLocal (k₁ k₂ : ℕ) :
    ((twoRowPointLocal v k₁ k₂ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![ratPrimeAt v ^ k₁, 0, 0; 0, ratPrimeAt v ^ k₂, 0; 0, 0, 1] := by
  rw [twoRowPointLocal, coe_iotaGL, coe_diagUnits2, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    ratPrimeUnit, Units.val_mk0]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end PlaceArithmetic

end LanglandsTunnell.CubicInduction

end TorusPoints

namespace SphericalWhittakerConstruction

open IwasawaUniqueness

section Table

variable (v : HeightOneSpectrum (𝓞 ℚ)) (e₁ e₂ e₃ : ℂ)

private def torusTable : ℕ → ℕ → ℂ
  | n, 0 => (cNormQ v)⁻¹ ^ n * sphericalTorusValue e₁ e₂ e₃ n
  | k₁, j + 1 =>
    (cNormQ v)⁻¹ ^ k₁ *
      (sphericalTorusValue e₁ e₂ e₃ k₁ *
          sphericalTorusValue e₁ e₂ e₃ (j + 1) -
        sphericalTorusValue e₁ e₂ e₃ (k₁ + 1) *
          sphericalTorusValue e₁ e₂ e₃ j)

private theorem torusTable_zero (n : ℕ) :
    torusTable v e₁ e₂ e₃ n 0 = (cNormQ v)⁻¹ ^ n * sphericalTorusValue e₁ e₂ e₃ n :=
  rfl

private theorem torusTable_succ (k₁ j : ℕ) :
    torusTable v e₁ e₂ e₃ k₁ (j + 1) =
      (cNormQ v)⁻¹ ^ k₁ *
        (sphericalTorusValue e₁ e₂ e₃ k₁ *
            sphericalTorusValue e₁ e₂ e₃ (j + 1) -
          sphericalTorusValue e₁ e₂ e₃ (k₁ + 1) *
            sphericalTorusValue e₁ e₂ e₃ j) :=
  rfl

private def torusValue (a b c : ℤ) : ℂ :=
  if c ≤ b ∧ b ≤ a then e₃ ^ c * torusTable v e₁ e₂ e₃ (a - c).toNat (b - c).toNat else 0

private theorem torusValue_of_not {a b c : ℤ} (h : ¬ (c ≤ b ∧ b ≤ a)) : torusValue v e₁ e₂ e₃ a b c = 0 := by
  rw [torusValue, if_neg h]

private theorem torusValue_add (he₃ : e₃ ≠ 0) (a b c m : ℤ) :
    torusValue v e₁ e₂ e₃ (a + m) (b + m) (c + m) = e₃ ^ m * torusValue v e₁ e₂ e₃ a b c := by
  by_cases h : c ≤ b ∧ b ≤ a
  · have h' : c + m ≤ b + m ∧ b + m ≤ a + m := by omega
    rw [torusValue, if_pos h', torusValue, if_pos h, zpow_add₀ he₃, show a + m - (c + m) = a - c by omega,
      show b + m - (c + m) = b - c by omega]
    ring
  · have h' : ¬ (c + m ≤ b + m ∧ b + m ≤ a + m) := fun h' => h (by omega)
    rw [torusValue_of_not v e₁ e₂ e₃ h', torusValue_of_not v e₁ e₂ e₃ h, mul_zero]

private theorem torusValue_natCast (k₁ k₂ : ℕ) (hk : k₂ ≤ k₁) :
    torusValue v e₁ e₂ e₃ k₁ k₂ 0 = torusTable v e₁ e₂ e₃ k₁ k₂ := by
  have h : (0 : ℤ) ≤ k₂ ∧ (k₂ : ℤ) ≤ k₁ := by omega
  rw [torusValue, if_pos h]
  simp

end Table

section Orders

open NumberField.AdelicLevel

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def ord (x : v.adicCompletion ℚ) : ℤ := - WithZero.log (Valued.v x)

private theorem ord_of_valued_eq {x : v.adicCompletion ℚ} {n : ℤ} (h : Valued.v x = WithZero.exp n) :
    ord v x = -n := by
  rw [ord, h, WithZero.log_exp]

private theorem ord_one : ord v 1 = 0 := by
  rw [ord, map_one, WithZero.log_one, neg_zero]

private theorem ord_ratPrimeAt_pow (k : ℕ) : ord v (ratPrimeAt v ^ k) = k := by
  have h : Valued.v (ratPrimeAt v ^ k) = WithZero.exp (-(k : ℤ)) := by
    rw [map_pow, valued_ratPrimeAt v, ← WithZero.exp_nsmul, WithZero.exp_inj]
    simp
  rw [ord_of_valued_eq v h, neg_neg]

private theorem ord_uniformizerUnit : ord v (uniformizerUnit ℚ v : v.adicCompletion ℚ) = 1 := by
  rw [ord_of_valued_eq v (valued_uniformizerUnit ℚ v), neg_neg]

private theorem ord_unit_mul (w : (v.adicCompletion ℚ)ˣ) {x : v.adicCompletion ℚ} (hx : x ≠ 0) :
    ord v ((w : v.adicCompletion ℚ) * x) = ord v x + ord v (w : v.adicCompletion ℚ) := by
  have hw : Valued.v (w : v.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff Valued.v).2 w.ne_zero
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff Valued.v).2 hx
  simp only [ord]
  rw [map_mul, WithZero.log_mul hw hx']
  ring

private theorem ord_lt_ord_of_valued_lt {a b : v.adicCompletion ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Valued.v b < Valued.v a) : ord v a < ord v b := by
  have ha' : Valued.v a ≠ 0 := (Valuation.ne_zero_iff Valued.v).2 ha
  have hb' : Valued.v b ≠ 0 := (Valuation.ne_zero_iff Valued.v).2 hb
  rw [← WithZero.exp_log ha', ← WithZero.exp_log hb', WithZero.exp_lt_exp] at h
  simp only [ord]
  omega

end Orders

section Definition

variable (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (e₁ e₂ e₃ : ℂ)

private def IsValue (g : LocalGL3 v) (c : ℂ) : Prop :=
  ∃ (x y z : v.adicCompletion ℚ) (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ) (k : LocalGL3 v),
    (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d ∧
      k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧ g = upperUnipotent3 x y z * t * k ∧
        c = ψv (x + y) * torusValue v e₁ e₂ e₃ (ord v (d 0)) (ord v (d 1)) (ord v (d 2))

open scoped Classical in

private def whittakerFn (g : LocalGL3 v) : ℂ :=
  if h : ∃ c : ℂ, IsValue v ψv e₁ e₂ e₃ g c then h.choose else 0

end Definition

section Laws

variable {v : HeightOneSpectrum (𝓞 ℚ)} {ψv : AddChar (v.adicCompletion ℚ) ℂ} {e₁ e₂ e₃ : ℂ}

private theorem isValue_unique (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1) {g : LocalGL3 v}
    {c c' : ℂ} (h : IsValue v ψv e₁ e₂ e₃ g c) (h' : IsValue v ψv e₁ e₂ e₃ g c') : c = c' := by
  obtain ⟨x, y, z, t, d, k, ht, hk, rfl, rfl⟩ := h
  obtain ⟨x', y', z', t', d', k', ht', hk', hg', rfl⟩ := h'
  have hval := LanglandsTunnell.CubicInduction.valued_eq_of_upperUnipotent3_mul_mul_eq_of_coe_eq_diagonal v x y z
    x' y' z' t t' d d' ht ht' k k' hk hk' hg'
  have hord : ∀ i, ord v (d i) = ord v (d' i) := fun i => by simp only [ord, hval i]
  rw [hord 0, hord 1, hord 2]
  by_cases hd : Valued.v (d 1) < Valued.v (d 0) ∨ Valued.v (d 2) < Valued.v (d 1)
  · have h0 : torusValue v e₁ e₂ e₃ (ord v (d' 0)) (ord v (d' 1)) (ord v (d' 2)) = 0 := by
      rw [← hord 0, ← hord 1, ← hord 2]
      refine torusValue_of_not v e₁ e₂ e₃ ?_
      rcases hd with hd | hd
      · have := ord_lt_ord_of_valued_lt v (ne_zero_of_coe_eq_diagonal ht 0) (ne_zero_of_coe_eq_diagonal ht 1) hd
        omega
      · have := ord_lt_ord_of_valued_lt v (ne_zero_of_coe_eq_diagonal ht 1) (ne_zero_of_coe_eq_diagonal ht 2) hd
        omega
    rw [h0, mul_zero, mul_zero]
  · obtain ⟨hx, hy⟩ :=
      LanglandsTunnell.CubicInduction.valued_sub_le_one_of_upperUnipotent3_mul_mul_eq_of_not_valued_lt v x y z
        x' y' z' t t' d d' ht ht' hd k k' hk hk' hg'
    have hxy : x + y = x' + y' + ((x - x') + (y - y')) := by ring
    rw [hxy, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul ψv (x - x'), hψ0 _ hx, hψ0 _ hy, mul_one, mul_one]

private theorem whittakerFn_eq (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1) {g : LocalGL3 v}
    {c : ℂ} (h : IsValue v ψv e₁ e₂ e₃ g c) : whittakerFn v ψv e₁ e₂ e₃ g = c := by
  have hex : ∃ c : ℂ, IsValue v ψv e₁ e₂ e₃ g c := ⟨c, h⟩
  rw [whittakerFn, dif_pos hex]
  exact isValue_unique hψ0 hex.choose_spec h

private theorem whittakerFn_eq_zero {g : LocalGL3 v} (h : ¬ ∃ c : ℂ, IsValue v ψv e₁ e₂ e₃ g c) :
    whittakerFn v ψv e₁ e₂ e₃ g = 0 := by
  rw [whittakerFn, dif_neg h]

private theorem isValue_unipotent_mul (a b e : v.adicCompletion ℚ) {g : LocalGL3 v} {c : ℂ}
    (h : IsValue v ψv e₁ e₂ e₃ g c) :
    IsValue v ψv e₁ e₂ e₃ (upperUnipotent3 a b e * g) (ψv (a + b) * c) := by
  obtain ⟨x, y, z, t, d, k, ht, hk, rfl, rfl⟩ := h
  refine ⟨a + x, b + y, e + z + a * y, t, d, k, ht, hk, ?_, ?_⟩
  · rw [← mul_assoc, ← mul_assoc, unip_mul]
  · rw [show a + x + (b + y) = a + b + (x + y) by ring, AddChar.map_add_eq_mul ψv (a + b) (x + y)]
    ring

private theorem isValue_mul_mem {u : LocalGL3 v} (hu : u ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) {g : LocalGL3 v}
    {c : ℂ} (h : IsValue v ψv e₁ e₂ e₃ g c) : IsValue v ψv e₁ e₂ e₃ (g * u) c := by
  obtain ⟨x, y, z, t, d, k, ht, hk, rfl, rfl⟩ := h
  exact ⟨x, y, z, t, d, k * u, ht, (localMaximalCompact3 (𝓞 ℚ) ℚ v).mul_mem hk hu, mul_assoc _ _ _, rfl⟩

private theorem isValue_scalar_mul (he₃ : e₃ ≠ 0) (w : (v.adicCompletion ℚ)ˣ) {g : LocalGL3 v} {c : ℂ}
    (h : IsValue v ψv e₁ e₂ e₃ g c) :
    IsValue v ψv e₁ e₂ e₃ (scalarGL3 v w * g) (e₃ ^ ord v (w : v.adicCompletion ℚ) * c) := by
  obtain ⟨x, y, z, t, d, k, ht, hk, rfl, rfl⟩ := h
  refine ⟨x, y, z, scalarGL3 v w * t, fun i => (w : v.adicCompletion ℚ) * d i, k, ?_, hk, ?_, ?_⟩
  · rw [Units.val_mul, coe_scalarGL3, ht, Matrix.diagonal_mul_diagonal]
  · rw [← mul_assoc, ← mul_assoc, scalarGL3_mul_comm v w (upperUnipotent3 x y z),
      mul_assoc (upperUnipotent3 x y z) (scalarGL3 v w) t]
  · rw [ord_unit_mul v w (ne_zero_of_coe_eq_diagonal ht 0), ord_unit_mul v w (ne_zero_of_coe_eq_diagonal ht 1),
      ord_unit_mul v w (ne_zero_of_coe_eq_diagonal ht 2), torusValue_add v e₁ e₂ e₃ he₃]
    ring

private theorem whittakerFn_unipotent_mul (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1)
    (a b e : v.adicCompletion ℚ) (g : LocalGL3 v) :
    whittakerFn v ψv e₁ e₂ e₃ (upperUnipotent3 a b e * g) = ψv (a + b) * whittakerFn v ψv e₁ e₂ e₃ g := by
  by_cases hg : ∃ c : ℂ, IsValue v ψv e₁ e₂ e₃ g c
  · obtain ⟨c, hc⟩ := hg
    rw [whittakerFn_eq hψ0 hc, whittakerFn_eq hψ0 (isValue_unipotent_mul a b e hc)]
  · rw [whittakerFn_eq_zero hg, whittakerFn_eq_zero, mul_zero]
    rintro ⟨c, hc⟩
    have h' := isValue_unipotent_mul (-a) (-b) (a * b - e) hc
    rw [← unip_inv, inv_mul_cancel_left] at h'
    exact hg ⟨_, h'⟩

private theorem whittakerFn_mul_mem (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1) (g : LocalGL3 v)
    {u : LocalGL3 v} (hu : u ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    whittakerFn v ψv e₁ e₂ e₃ (g * u) = whittakerFn v ψv e₁ e₂ e₃ g := by
  by_cases hg : ∃ c : ℂ, IsValue v ψv e₁ e₂ e₃ g c
  · obtain ⟨c, hc⟩ := hg
    rw [whittakerFn_eq hψ0 hc, whittakerFn_eq hψ0 (isValue_mul_mem hu hc)]
  · rw [whittakerFn_eq_zero hg, whittakerFn_eq_zero]
    rintro ⟨c, hc⟩
    have h' := isValue_mul_mem ((localMaximalCompact3 (𝓞 ℚ) ℚ v).inv_mem hu) hc
    rw [mul_inv_cancel_right] at h'
    exact hg ⟨_, h'⟩

private theorem whittakerFn_scalar_mul (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1)
    (he₃ : e₃ ≠ 0) (w : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    whittakerFn v ψv e₁ e₂ e₃ (scalarGL3 v w * g) =
      e₃ ^ ord v (w : v.adicCompletion ℚ) * whittakerFn v ψv e₁ e₂ e₃ g := by
  by_cases hg : ∃ c : ℂ, IsValue v ψv e₁ e₂ e₃ g c
  · obtain ⟨c, hc⟩ := hg
    rw [whittakerFn_eq hψ0 hc, whittakerFn_eq hψ0 (isValue_scalar_mul he₃ w hc)]
  · rw [whittakerFn_eq_zero hg, whittakerFn_eq_zero, mul_zero]
    rintro ⟨c, hc⟩
    have h' := isValue_scalar_mul he₃ w⁻¹ hc
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] at h'
    exact hg ⟨_, h'⟩

private theorem whittakerFn_centralGen_mul (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1)
    (he₃ : e₃ ≠ 0) (g : LocalGL3 v) :
    whittakerFn v ψv e₁ e₂ e₃ (centralGen v * g) = e₃ * whittakerFn v ψv e₁ e₂ e₃ g := by
  rw [centralGen_eq_scalarGL3, whittakerFn_scalar_mul hψ0 he₃, ord_uniformizerUnit, zpow_one]

private theorem isValue_twoRowPointLocal (k₁ k₂ : ℕ) :
    IsValue v ψv e₁ e₂ e₃ (twoRowPointLocal v k₁ k₂) (torusValue v e₁ e₂ e₃ k₁ k₂ 0) := by
  refine ⟨0, 0, 0, twoRowPointLocal v k₁ k₂, ![ratPrimeAt v ^ k₁, ratPrimeAt v ^ k₂, 1], 1, ?_,
    (localMaximalCompact3 (𝓞 ℚ) ℚ v).one_mem, ?_, ?_⟩
  · rw [coe_twoRowPointLocal]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · rw [upperUnipotent3_zero, one_mul, mul_one]
  · have h0 : ord v (![ratPrimeAt v ^ k₁, ratPrimeAt v ^ k₂, (1 : v.adicCompletion ℚ)] 0) = k₁ :=
      ord_ratPrimeAt_pow v k₁
    have h1 : ord v (![ratPrimeAt v ^ k₁, ratPrimeAt v ^ k₂, (1 : v.adicCompletion ℚ)] 1) = k₂ :=
      ord_ratPrimeAt_pow v k₂
    have h2 : ord v (![ratPrimeAt v ^ k₁, ratPrimeAt v ^ k₂, (1 : v.adicCompletion ℚ)] 2) = 0 := ord_one v
    simp only [h0, h1, h2, add_zero, AddChar.map_zero_eq_one, one_mul]

private theorem whittakerFn_twoRowPointLocal (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1)
    (k₁ k₂ : ℕ) (hk : k₂ ≤ k₁) :
    whittakerFn v ψv e₁ e₂ e₃ (twoRowPointLocal v k₁ k₂) = torusTable v e₁ e₂ e₃ k₁ k₂ := by
  rw [whittakerFn_eq hψ0 (isValue_twoRowPointLocal k₁ k₂), torusValue_natCast v e₁ e₂ e₃ k₁ k₂ hk]

end Laws

end SphericalWhittakerConstruction

p2m_open_scoped "LanglandsTunnell LanglandsTunnell.CubicInduction" in
open SphericalWhittakerConstruction in

private theorem LanglandsTunnell.CubicInduction.exists_sphericalWhittakerFn_of_forall_valued_le_one
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1) (e₁ e₂ e₃ : ℂ) (he₃ : e₃ ≠ 0) :
    ∃ W : LocalGL3 v → ℂ,
      IsGL3PsiWhittakerFn ψv W ∧ IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      (∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) ∧ W 1 = 1 ∧
      (∀ n : ℕ, W (iotaTorusLocal v n) =
        (cNormQ v)⁻¹ ^ n * sphericalTorusValue e₁ e₂ e₃ n) ∧
      (∀ k₁ k₂ : ℕ, k₂ + 1 ≤ k₁ → W (twoRowPointLocal v k₁ (k₂ + 1)) =
        (cNormQ v)⁻¹ ^ k₁ *
          (sphericalTorusValue e₁ e₂ e₃ k₁ *
              sphericalTorusValue e₁ e₂ e₃ (k₂ + 1) -
            sphericalTorusValue e₁ e₂ e₃ (k₁ + 1) *
              sphericalTorusValue e₁ e₂ e₃ k₂)) := by
  refine ⟨whittakerFn v ψv e₁ e₂ e₃, fun x y z g => whittakerFn_unipotent_mul hψ0 x y z g,
    fun g u hu => whittakerFn_mul_mem hψ0 g hu, fun g => whittakerFn_centralGen_mul hψ0 he₃ g, ?_, ?_, ?_⟩
  · rw [← iotaTorusLocal_zero v, ← twoRowPointLocal_zero_right v 0, whittakerFn_twoRowPointLocal hψ0 0 0 le_rfl]
    simp [torusTable_zero, sphericalTorusValue]
  · intro n
    rw [← twoRowPointLocal_zero_right v n, whittakerFn_twoRowPointLocal hψ0 n 0 (Nat.zero_le n), torusTable_zero]
  · intro k₁ k₂ hk
    rw [whittakerFn_twoRowPointLocal hψ0 k₁ (k₂ + 1) hk, torusTable_succ]

end

set_option autoImplicit false

open IsDedekindDomain NumberField
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace.LanglandsTunnell.CubicInduction"

noncomputable section

namespace SphericalWhittakerEigen

section Table

variable (N e₁ e₂ e₃ : ℂ)

private def torusTable : ℕ → ℕ → ℂ
  | n, 0 => N⁻¹ ^ n * sphericalTorusValue e₁ e₂ e₃ n
  | k₁, j + 1 =>
    N⁻¹ ^ k₁ *
      (sphericalTorusValue e₁ e₂ e₃ k₁ * sphericalTorusValue e₁ e₂ e₃ (j + 1) -
        sphericalTorusValue e₁ e₂ e₃ (k₁ + 1) * sphericalTorusValue e₁ e₂ e₃ j)

private theorem torusTable_zero (n : ℕ) :
    torusTable N e₁ e₂ e₃ n 0 = N⁻¹ ^ n * sphericalTorusValue e₁ e₂ e₃ n :=
  rfl

private theorem torusTable_succ (k₁ j : ℕ) :
    torusTable N e₁ e₂ e₃ k₁ (j + 1) =
      N⁻¹ ^ k₁ *
        (sphericalTorusValue e₁ e₂ e₃ k₁ * sphericalTorusValue e₁ e₂ e₃ (j + 1) -
          sphericalTorusValue e₁ e₂ e₃ (k₁ + 1) * sphericalTorusValue e₁ e₂ e₃ j) :=
  rfl

private def torusValue (a b c : ℤ) : ℂ :=
  if c ≤ b ∧ b ≤ a then e₃ ^ c * torusTable N e₁ e₂ e₃ (a - c).toNat (b - c).toNat else 0

private theorem torusValue_natCast (a b : ℕ) (h : b ≤ a) :
    torusValue N e₁ e₂ e₃ a b 0 = torusTable N e₁ e₂ e₃ a b := by
  rw [torusValue, if_pos (by omega)]
  simp

private theorem torusValue_natCast_of_lt (a b : ℕ) (h : a < b) : torusValue N e₁ e₂ e₃ a b 0 = 0 := by
  rw [torusValue, if_neg (by omega)]

private theorem torusValue_succ_succ_one (a b : ℕ) (h : b ≤ a) :
    torusValue N e₁ e₂ e₃ ((a + 1 : ℕ) : ℤ) ((b + 1 : ℕ) : ℤ) 1 = e₃ * torusTable N e₁ e₂ e₃ a b := by
  rw [torusValue, if_pos (by omega)]
  simp

private theorem torusValue_one_of_lt (a b : ℕ) (h : a < b) : torusValue N e₁ e₂ e₃ a b 1 = 0 := by
  rw [torusValue, if_neg (by omega)]

private theorem torusValue_one_of_nonpos {b : ℤ} (a : ℕ) (hb : b ≤ 0) : torusValue N e₁ e₂ e₃ a b 1 = 0 := by
  rw [torusValue, if_neg (by omega)]

end Table

section Identities

variable {N : ℂ} (e₁ e₂ e₃ : ℂ)

private theorem torusValue_heckeGen1 (hN : N ≠ 0) (k₁ k₂ : ℕ) (hk : k₂ ≤ k₁) :
    N ^ 2 * torusValue N e₁ e₂ e₃ ((k₁ + 1 : ℕ) : ℤ) k₂ 0 + N * torusValue N e₁ e₂ e₃ k₁ ((k₂ + 1 : ℕ) : ℤ) 0 +
        torusValue N e₁ e₂ e₃ k₁ k₂ 1 =
      N * e₁ * torusValue N e₁ e₂ e₃ k₁ k₂ 0 := by
  match k₂, hk with
  | 0, _ =>
    rcases k₁ with _ | m
    · simp (disch := omega) only [torusValue_natCast, torusValue_natCast_of_lt, torusValue_one_of_nonpos,
        torusTable_zero, sphericalTorusValue]
      linear_combination (N * e₁) * mul_inv_cancel₀ hN
    · simp (disch := omega) only [torusValue_natCast, torusValue_one_of_nonpos, torusTable_zero, torusTable_succ,
        sphericalTorusValue]
      set h := sphericalTorusValue e₁ e₂ e₃
      linear_combination (N * N⁻¹ * (N⁻¹ ^ m) * (h (m + 2))) * mul_inv_cancel₀ hN
  | 1, hk =>
    rcases Nat.lt_or_ge 1 k₁ with hlt | hge
    · obtain ⟨m, rfl⟩ : ∃ m, k₁ = m + 1 := ⟨k₁ - 1, by omega⟩
      simp (disch := omega) only [torusValue_natCast, torusValue_succ_succ_one, torusTable_zero, torusTable_succ,
        sphericalTorusValue]
      set h := sphericalTorusValue e₁ e₂ e₃
      linear_combination (-(N⁻¹ ^ m) * e₃ * (h m)
          + N * N⁻¹ * (N⁻¹ ^ m) * e₂ * (h (m + 1))
          - N * N⁻¹ * (N⁻¹ ^ m) * e₃ * (h m)) * mul_inv_cancel₀ hN
    · obtain rfl : k₁ = 1 := le_antisymm hge hk
      simp (disch := omega) only [torusValue_natCast, torusValue_natCast_of_lt, torusValue_succ_succ_one,
        torusTable_zero, torusTable_succ, sphericalTorusValue]
      linear_combination (-e₃
          - N * N⁻¹ * e₃
          + N * N⁻¹ * e₁ * e₂) * mul_inv_cancel₀ hN
  | i + 2, hk =>
    rcases Nat.lt_or_ge (i + 2) k₁ with hlt | hge
    · obtain ⟨m, rfl⟩ : ∃ m, k₁ = m + 1 := ⟨k₁ - 1, by omega⟩
      simp (disch := omega) only [torusValue_natCast, torusValue_succ_succ_one, torusTable_succ, sphericalTorusValue]
      set h := sphericalTorusValue e₁ e₂ e₃
      linear_combination ((N⁻¹ ^ m) * e₃ * (h i) * (h (m + 1))
          - (N⁻¹ ^ m) * e₃ * (h (i + 1)) * (h m)
          + N * N⁻¹ * (N⁻¹ ^ m) * (h (i + 2)) * (h (m + 2))
          + N * N⁻¹ * (N⁻¹ ^ m) * e₂ * (h (i + 1)) * (h (m + 1))
          - N * N⁻¹ * (N⁻¹ ^ m) * e₁ * (h (i + 1)) * (h (m + 2))
          - N * N⁻¹ * (N⁻¹ ^ m) * e₃ * (h (i + 1)) * (h m)) * mul_inv_cancel₀ hN
    · obtain rfl : k₁ = i + 2 := le_antisymm hge hk
      simp (disch := omega) only [torusValue_natCast, torusValue_natCast_of_lt, torusValue_succ_succ_one,
        torusTable_succ, sphericalTorusValue]
      set h := sphericalTorusValue e₁ e₂ e₃
      linear_combination (-N⁻¹ * (N⁻¹ ^ i) * e₃ * (h (i + 1)) ^ 2
          + N * N⁻¹ ^ 2 * (N⁻¹ ^ i) * e₁ * (h (i + 2)) ^ 2
          + N⁻¹ * (N⁻¹ ^ i) * e₃ * (h i) * (h (i + 2))
          - N * N⁻¹ ^ 2 * (N⁻¹ ^ i) * e₃ * (h (i + 1)) ^ 2
          + N * N⁻¹ ^ 2 * (N⁻¹ ^ i) * e₁ * e₂ * (h (i + 1)) ^ 2
          + N * N⁻¹ ^ 2 * (N⁻¹ ^ i) * e₃ * (h i) * (h (i + 2))
          - N * N⁻¹ ^ 2 * (N⁻¹ ^ i) * e₁ ^ 2 * (h (i + 1)) * (h (i + 2))
          - N * N⁻¹ ^ 2 * (N⁻¹ ^ i) * e₁ * e₃ * (h i) * (h (i + 1))) * mul_inv_cancel₀ hN

private theorem torusValue_heckeGen2 (hN : N ≠ 0) (k₁ k₂ : ℕ) (hk : k₂ ≤ k₁) :
    N ^ 2 * torusValue N e₁ e₂ e₃ ((k₁ + 1 : ℕ) : ℤ) ((k₂ + 1 : ℕ) : ℤ) 0 +
          N * torusValue N e₁ e₂ e₃ ((k₁ + 1 : ℕ) : ℤ) k₂ 1 +
        torusValue N e₁ e₂ e₃ k₁ ((k₂ + 1 : ℕ) : ℤ) 1 =
      N * e₂ * torusValue N e₁ e₂ e₃ k₁ k₂ 0 := by
  match k₂, hk with
  | 0, _ =>
    rcases k₁ with _ | m
    · simp (disch := omega) only [torusValue_natCast, torusValue_one_of_nonpos, torusValue_one_of_lt, torusTable_zero,
        torusTable_succ, sphericalTorusValue]
      linear_combination (N * e₂) * mul_inv_cancel₀ hN
    · simp (disch := omega) only [torusValue_natCast, torusValue_one_of_nonpos, torusValue_succ_succ_one,
        torusTable_zero, torusTable_succ, sphericalTorusValue]
      set h := sphericalTorusValue e₁ e₂ e₃
      linear_combination (-(N⁻¹ ^ m) * e₃ * (h m)
          + N * N⁻¹ * (N⁻¹ ^ m) * e₂ * (h (m + 1))
          - N * N⁻¹ * (N⁻¹ ^ m) * e₃ * (h m)) * mul_inv_cancel₀ hN
  | 1, hk =>
    rcases Nat.lt_or_ge 1 k₁ with hlt | hge
    · obtain ⟨m, rfl⟩ : ∃ m, k₁ = m + 1 := ⟨k₁ - 1, by omega⟩
      simp (disch := omega) only [torusValue_natCast, torusValue_succ_succ_one, torusTable_zero, torusTable_succ,
        sphericalTorusValue]
      set h := sphericalTorusValue e₁ e₂ e₃
      linear_combination ((N⁻¹ ^ m) * e₃ * (h (m + 1))
          - (N⁻¹ ^ m) * e₁ * e₃ * (h m)
          - N * N⁻¹ * (N⁻¹ ^ m) * e₂ * (h (m + 2))
          + N * N⁻¹ * (N⁻¹ ^ m) * e₁ * e₂ * (h (m + 1))
          - N * N⁻¹ * (N⁻¹ ^ m) * e₁ * e₃ * (h m)) * mul_inv_cancel₀ hN
    · obtain rfl : k₁ = 1 := le_antisymm hge hk
      simp (disch := omega) only [torusValue_natCast, torusValue_succ_succ_one, torusValue_one_of_lt, torusTable_zero,
        torusTable_succ, sphericalTorusValue]
      linear_combination (N * N⁻¹ * e₂ ^ 2
          - N * N⁻¹ * e₁ * e₃) * mul_inv_cancel₀ hN
  | i + 2, hk =>
    rcases Nat.lt_or_ge (i + 2) k₁ with hlt | hge
    · obtain ⟨m, rfl⟩ : ∃ m, k₁ = m + 1 := ⟨k₁ - 1, by omega⟩
      simp (disch := omega) only [torusValue_natCast, torusValue_succ_succ_one, torusTable_succ, sphericalTorusValue]
      set h := sphericalTorusValue e₁ e₂ e₃
      linear_combination ((N⁻¹ ^ m) * e₃ * (h (i + 1)) * (h (m + 1))
          - (N⁻¹ ^ m) * e₃ * (h (i + 2)) * (h m)
          + N * N⁻¹ * (N⁻¹ ^ m) * e₂ * (h (i + 2)) * (h (m + 1))
          + N * N⁻¹ * (N⁻¹ ^ m) * e₃ * (h i) * (h (m + 2))
          - N * N⁻¹ * (N⁻¹ ^ m) * e₂ * (h (i + 1)) * (h (m + 2))
          - N * N⁻¹ * (N⁻¹ ^ m) * e₃ * (h (i + 2)) * (h m)) * mul_inv_cancel₀ hN
    · obtain rfl : k₁ = i + 2 := le_antisymm hge hk
      simp (disch := omega) only [torusValue_natCast, torusValue_succ_succ_one, torusValue_one_of_lt, torusTable_succ,
        sphericalTorusValue]
      set h := sphericalTorusValue e₁ e₂ e₃
      linear_combination (N * N⁻¹ ^ 2 * (N⁻¹ ^ i) * e₂ * (h (i + 2)) ^ 2
          + N * N⁻¹ ^ 2 * (N⁻¹ ^ i) * e₂ ^ 2 * (h (i + 1)) ^ 2
          + N * N⁻¹ ^ 2 * (N⁻¹ ^ i) * e₃ ^ 2 * (h i) ^ 2
          - N * N⁻¹ ^ 2 * (N⁻¹ ^ i) * e₃ * (h (i + 1)) * (h (i + 2))
          + N * N⁻¹ ^ 2 * (N⁻¹ ^ i) * e₁ * e₃ * (h i) * (h (i + 2))
          - N * N⁻¹ ^ 2 * (N⁻¹ ^ i) * e₁ * e₂ * (h (i + 1)) * (h (i + 2))
          - 2 * N * N⁻¹ ^ 2 * (N⁻¹ ^ i) * e₂ * e₃ * (h i) * (h (i + 1))) * mul_inv_cancel₀ hN

end Identities

section CosetSums

variable {G : Type*} [Group G]

private theorem cosetSum_eq_cosetSum {U : Subgroup G} {gen : G} {ι ι' : Type} [Fintype ι] [Fintype ι']
    {reps : ι → G} {reps' : ι' → G} (h : HeckeIntegralSeam.IsHeckeCosetSystem U gen reps)
    (h' : HeckeIntegralSeam.IsHeckeCosetSystem U gen reps') {W : G → ℂ} (hW : IsRightInvariant U W) (g : G) :
    cosetSum reps W g = cosetSum reps' W g := by
  have hWU : ∀ x : G, ∀ u ∈ U, W (x * u) = W x := hW
  choose σ hσ using fun i => h'.covers (reps i) (h.mem_doubleCoset i)
  have hinj : Function.Injective σ := by
    intro i j hij
    apply h.mk_injective
    show (QuotientGroup.mk (reps i) : G ⧸ U) = QuotientGroup.mk (reps j)
    rw [hσ i, hσ j, hij]
  have hsurj : Function.Surjective σ := by
    intro i'
    obtain ⟨i, hi⟩ := h.covers (reps' i') (h'.mem_doubleCoset i')
    refine ⟨i, h'.mk_injective ?_⟩
    show (QuotientGroup.mk (reps' (σ i)) : G ⧸ U) = QuotientGroup.mk (reps' i')
    rw [← hσ i, hi]
  simp only [cosetSum]
  refine Fintype.sum_equiv (Equiv.ofBijective σ ⟨hinj, hsurj⟩) _ _ fun i => ?_
  show W (g * reps i) = W (g * reps' (σ i))
  have hu : (reps i)⁻¹ * reps' (σ i) ∈ U := QuotientGroup.eq.1 (hσ i)
  rw [← mul_inv_cancel_left (reps i) (reps' (σ i)), ← mul_assoc g (reps i), hWU _ _ hu]

private theorem cosetSum_central_mul {ι : Type} [Fintype ι] (reps : ι → G) {W : G → ℂ} {z : G} {e : ℂ}
    (hZ : ∀ x : G, W (z * x) = e * W x) (g : G) : cosetSum reps W (z * g) = e * cosetSum reps W g := by
  simp only [cosetSum, mul_assoc, hZ, Finset.mul_sum]

end CosetSums

section Points

open NumberField.AdelicLevel

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem cNormQ_ne_zero : cNormQ v ≠ 0 := by
  rw [cNormQ, absNorm_asIdeal_eq_natGenerator]
  exact_mod_cast (Rat.HeightOneSpectrum.prime_natGenerator v).ne_zero

private theorem valued_ratPrimeAt_pow (k : ℕ) : Valued.v (ratPrimeAt v ^ k) = WithZero.exp (-(k : ℤ)) := by
  rw [map_pow, valued_ratPrimeAt v, ← WithZero.exp_nsmul, WithZero.exp_inj]
  simp

private theorem valued_ratPrimeAt_pow_succ (k : ℕ) :
    Valued.v (ratPrimeAt v ^ (k + 1)) = WithZero.exp (-((k : ℤ) + 1)) := by
  simp [valued_ratPrimeAt_pow]

private theorem coe_twoRowPointLocal_eq_diagonal (k₁ k₂ : ℕ) :
    ((twoRowPointLocal v k₁ k₂ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![ratPrimeAt v ^ k₁, ratPrimeAt v ^ k₂, 1] := by
  rw [coe_twoRowPointLocal]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private def lastGen : LocalGL3 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![1, 1, varpi v]) (by
    simp [Matrix.det_diagonal, Fin.prod_univ_three, varpi_ne_zero v])

private theorem coe_lastGen :
    ((lastGen v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal ![1, 1, varpi v] :=
  rfl

private theorem centralGen_eq_lastGen_mul : centralGen v = lastGen v * heckeGen2 v := by
  apply Units.ext
  rw [Units.val_mul, coe_centralGen, coe_lastGen]
  show _ = Matrix.diagonal ![1, 1, varpi v] * Matrix.diagonal ![varpi v, varpi v, 1]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp

private theorem twoRowPointLocal_mul_central (k₁ k₂ : ℕ) :
    twoRowPointLocal v k₁ k₂ * (centralGen v * (heckeGen2 v)⁻¹) = twoRowPointLocal v k₁ k₂ * lastGen v := by
  rw [centralGen_eq_lastGen_mul, mul_inv_cancel_right]

private theorem coe_twoRowPointLocal_mul_lastGen (k₁ k₂ : ℕ) :
    ((twoRowPointLocal v k₁ k₂ * lastGen v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![ratPrimeAt v ^ k₁, ratPrimeAt v ^ k₂, varpi v] := by
  rw [Units.val_mul, coe_twoRowPointLocal_eq_diagonal, coe_lastGen, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp

private theorem valued_varpi : Valued.v (varpi v) = WithZero.exp (-1 : ℤ) :=
  valued_uniformizerUnit ℚ v

end Points

section Values

variable {v : HeightOneSpectrum (𝓞 ℚ)} {ψv : AddChar (v.adicCompletion ℚ) ℂ} {W : LocalGL3 v → ℂ} {e₁ e₂ e₃ : ℂ}

private theorem apply_twoRowPointLocal
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W) (hψ : IsGL3PsiWhittakerFn ψv W)
    (h₁ : ∀ n : ℕ, W (iotaTorusLocal v n) = (cNormQ v)⁻¹ ^ n * sphericalTorusValue e₁ e₂ e₃ n)
    (h₂ : ∀ k₁ k₂ : ℕ, k₂ + 1 ≤ k₁ → W (twoRowPointLocal v k₁ (k₂ + 1)) =
      (cNormQ v)⁻¹ ^ k₁ *
        (sphericalTorusValue e₁ e₂ e₃ k₁ * sphericalTorusValue e₁ e₂ e₃ (k₂ + 1) -
          sphericalTorusValue e₁ e₂ e₃ (k₁ + 1) * sphericalTorusValue e₁ e₂ e₃ k₂))
    (a b : ℕ) : W (twoRowPointLocal v a b) = torusValue (cNormQ v) e₁ e₂ e₃ a b 0 := by
  rcases Nat.lt_or_ge a b with hab | hab
  · rw [torusValue_natCast_of_lt (cNormQ v) e₁ e₂ e₃ a b hab]
    have h0 : Valued.v ((![ratPrimeAt v ^ a, ratPrimeAt v ^ b, 1] : Fin 3 → v.adicCompletion ℚ) 0) =
        WithZero.exp (-(a : ℤ)) := valued_ratPrimeAt_pow v a
    have h1 : Valued.v ((![ratPrimeAt v ^ a, ratPrimeAt v ^ b, 1] : Fin 3 → v.adicCompletion ℚ) 1) =
        WithZero.exp (-(b : ℤ)) := valued_ratPrimeAt_pow v b
    exact eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn v ψv W hW hψ hψ1 _ _
      (coe_twoRowPointLocal_eq_diagonal v a b) (Or.inl (by rw [h1, h0]; exact WithZero.exp_lt_exp.2 (by omega)))
  · rw [torusValue_natCast (cNormQ v) e₁ e₂ e₃ a b hab]
    cases b with
    | zero => rw [twoRowPointLocal_zero_right, h₁, torusTable_zero]
    | succ j => rw [h₂ a j hab, torusTable_succ]

private theorem apply_twoRowPointLocal_mul
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W) (hψ : IsGL3PsiWhittakerFn ψv W)
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (h₁ : ∀ n : ℕ, W (iotaTorusLocal v n) = (cNormQ v)⁻¹ ^ n * sphericalTorusValue e₁ e₂ e₃ n)
    (h₂ : ∀ k₁ k₂ : ℕ, k₂ + 1 ≤ k₁ → W (twoRowPointLocal v k₁ (k₂ + 1)) =
      (cNormQ v)⁻¹ ^ k₁ *
        (sphericalTorusValue e₁ e₂ e₃ k₁ * sphericalTorusValue e₁ e₂ e₃ (k₂ + 1) -
          sphericalTorusValue e₁ e₂ e₃ (k₁ + 1) * sphericalTorusValue e₁ e₂ e₃ k₂))
    (a b : ℕ) :
    W (twoRowPointLocal v a b * (centralGen v * (heckeGen2 v)⁻¹)) = torusValue (cNormQ v) e₁ e₂ e₃ a b 1 := by
  rw [twoRowPointLocal_mul_central]
  cases b with
  | zero =>
    rw [torusValue_one_of_nonpos (b := ((0 : ℕ) : ℤ)) (cNormQ v) e₁ e₂ e₃ a (by simp)]
    have h1 : Valued.v ((![ratPrimeAt v ^ a, ratPrimeAt v ^ 0, varpi v] : Fin 3 → v.adicCompletion ℚ) 1) =
        WithZero.exp (-((0 : ℕ) : ℤ)) := valued_ratPrimeAt_pow v 0
    have h2 : Valued.v ((![ratPrimeAt v ^ a, ratPrimeAt v ^ 0, varpi v] : Fin 3 → v.adicCompletion ℚ) 2) =
        WithZero.exp (-1 : ℤ) := valued_varpi v
    exact eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn v ψv W hW hψ hψ1 _ _
      (coe_twoRowPointLocal_mul_lastGen v a 0) (Or.inr (by rw [h2, h1]; exact WithZero.exp_lt_exp.2 (by omega)))
  | succ j =>
    rcases Nat.lt_or_ge a (j + 1) with hab | hab
    · rw [torusValue_one_of_lt (cNormQ v) e₁ e₂ e₃ a (j + 1) hab]
      have h0 : Valued.v ((![ratPrimeAt v ^ a, ratPrimeAt v ^ (j + 1), varpi v] : Fin 3 → v.adicCompletion ℚ) 0) =
          WithZero.exp (-(a : ℤ)) := valued_ratPrimeAt_pow v a
      have h1 : Valued.v ((![ratPrimeAt v ^ a, ratPrimeAt v ^ (j + 1), varpi v] : Fin 3 → v.adicCompletion ℚ) 1) =
          WithZero.exp (-((j + 1 : ℕ) : ℤ)) := valued_ratPrimeAt_pow v (j + 1)
      exact eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn v ψv W hW hψ hψ1 _ _
        (coe_twoRowPointLocal_mul_lastGen v a (j + 1))
        (Or.inl (by rw [h1, h0]; exact WithZero.exp_lt_exp.2 (by omega)))
    · obtain ⟨i, rfl⟩ : ∃ i, a = i + 1 := ⟨a - 1, by omega⟩
      rw [torusValue_succ_succ_one (cNormQ v) e₁ e₂ e₃ i j (by omega),
        eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant v W e₃ hW hZ _ _
          (coe_twoRowPointLocal_mul_lastGen v (i + 1) (j + 1)) i j 1 (valued_ratPrimeAt_pow_succ v i)
          (valued_ratPrimeAt_pow_succ v j) (valued_varpi v),
        zpow_one, apply_twoRowPointLocal hψ1 hW hψ h₁ h₂ i j, torusValue_natCast (cNormQ v) e₁ e₂ e₃ i j (by omega)]

private theorem isCosetEigenfunction_of_forall_twoRowPointLocal
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W) (hψ : IsGL3PsiWhittakerFn ψv W)
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g) {gen : LocalGL3 v} {lam : ℂ} {ι : Type} [Fintype ι]
    {reps : ι → LocalGL3 v} (hsys : HeckeIntegralSeam.IsHeckeCosetSystem (localMaximalCompact3 (𝓞 ℚ) ℚ v) gen reps)
    (htorus : ∀ k₁ k₂ : ℕ, k₂ ≤ k₁ →
      cosetSum reps W (twoRowPointLocal v k₁ k₂) = lam * W (twoRowPointLocal v k₁ k₂)) :
    IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) gen W lam := by
  have hW' : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) (cosetSum reps W) :=
    (cosetSum_isRightInvariant_and_isGL3PsiWhittakerFn v ψv (localMaximalCompact3 (𝓞 ℚ) ℚ v) gen reps W).1 hsys hW
  have hψ' : IsGL3PsiWhittakerFn ψv (cosetSum reps W) :=
    (cosetSum_isRightInvariant_and_isGL3PsiWhittakerFn v ψv (localMaximalCompact3 (𝓞 ℚ) ℚ v) gen reps W).2 hψ
  have hZ' : ∀ g : LocalGL3 v, cosetSum reps W (centralGen v * g) = e₃ * cosetSum reps W g :=
    cosetSum_central_mul reps hZ
  have key : ∀ (t : LocalGL3 v) (d : Fin 3 → v.adicCompletion ℚ),
      (t : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) = Matrix.diagonal d → cosetSum reps W t = lam * W t := by
    intro t d ht
    by_cases hdrop : Valued.v (d 1) < Valued.v (d 0) ∨ Valued.v (d 2) < Valued.v (d 1)
    · rw [eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn v ψv _ hW' hψ' hψ1 t d ht hdrop,
        eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn v ψv W hW hψ hψ1 t d ht hdrop, mul_zero]
    · obtain ⟨k₁, k₂, c, h0, h1, h2⟩ := exists_valued_eq_exp_of_coe_eq_diagonal_of_not_valued_lt v t d ht hdrop
      have hk : k₂ ≤ k₁ := by
        by_contra hlt
        exact hdrop (Or.inl (by rw [h1, h0]; exact WithZero.exp_lt_exp.2 (by omega)))
      rw [eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant v _ e₃ hW' hZ' t d ht k₁ k₂ c h0 h1 h2,
        eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant v W e₃ hW hZ t d ht k₁ k₂ c h0 h1 h2,
        htorus k₁ k₂ hk]
      ring
  have hWU : ∀ x : LocalGL3 v, ∀ u ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, W (x * u) = W x := hW
  have hWU' : ∀ x : LocalGL3 v, ∀ u ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
      cosetSum reps W (x * u) = cosetSum reps W x := hW'
  have hψN : ∀ (x y z : v.adicCompletion ℚ) (g : LocalGL3 v),
      W (upperUnipotent3 x y z * g) = ψv (x + y) * W g := hψ
  have hψN' : ∀ (x y z : v.adicCompletion ℚ) (g : LocalGL3 v),
      cosetSum reps W (upperUnipotent3 x y z * g) = ψv (x + y) * cosetSum reps W g := hψ'
  intro ι' _ reps' hsys' g
  rw [cosetSum_eq_cosetSum hsys' hsys hW g]
  obtain ⟨x, y, z, t, d, k, hk, ht, rfl⟩ := exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3 v g
  rw [hWU' _ k hk, hWU _ k hk, hψN' x y z t, hψN x y z t, key t d ht]
  ring

end Values

section HeckeEigenvalues

private theorem isCosetEigenfunction_heckeGen1_and_heckeGen2 (v : HeightOneSpectrum (𝓞 ℚ))
    (ψv : AddChar (v.adicCompletion ℚ) ℂ) (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1) (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
    (hψ : IsGL3PsiWhittakerFn ψv W) (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (h₁ : ∀ n : ℕ, W (iotaTorusLocal v n) = (cNormQ v)⁻¹ ^ n * sphericalTorusValue e₁ e₂ e₃ n)
    (h₂ : ∀ k₁ k₂ : ℕ, k₂ + 1 ≤ k₁ → W (twoRowPointLocal v k₁ (k₂ + 1)) =
      (cNormQ v)⁻¹ ^ k₁ *
        (sphericalTorusValue e₁ e₂ e₃ k₁ * sphericalTorusValue e₁ e₂ e₃ (k₂ + 1) -
          sphericalTorusValue e₁ e₂ e₃ (k₁ + 1) * sphericalTorusValue e₁ e₂ e₃ k₂)) :
    IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) := by
  have hN : cNormQ v ≠ 0 := cNormQ_ne_zero v
  constructor
  · obtain ⟨reps, hsys, hformula⟩ := exists_isHeckeCosetSystem_heckeGen1_cosetSum_twoRowPointLocal v
    refine isCosetEigenfunction_of_forall_twoRowPointLocal hψ1 hW hψ hZ hsys fun k₁ k₂ hk => ?_
    rw [hformula ψv hψ0 W hψ k₁ k₂ hk]
    simp only [apply_twoRowPointLocal hψ1 hW hψ h₁ h₂, apply_twoRowPointLocal_mul hψ1 hW hψ hZ h₁ h₂]
    exact torusValue_heckeGen1 e₁ e₂ e₃ hN k₁ k₂ hk
  · obtain ⟨reps, hsys, hformula⟩ := exists_isHeckeCosetSystem_heckeGen2_cosetSum_twoRowPointLocal v
    refine isCosetEigenfunction_of_forall_twoRowPointLocal hψ1 hW hψ hZ hsys fun k₁ k₂ hk => ?_
    rw [hformula ψv hψ0 W hψ k₁ k₂ hk]
    simp only [apply_twoRowPointLocal hψ1 hW hψ h₁ h₂, apply_twoRowPointLocal_mul hψ1 hW hψ hZ h₁ h₂]
    exact torusValue_heckeGen2 e₁ e₂ e₃ hN k₁ k₂ hk

end HeckeEigenvalues

end SphericalWhittakerEigen

end

set_option autoImplicit false

open IsDedekindDomain NumberField Polynomial

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RankinSelberg.primeFibre RankinSelberg.mem_primeFibre RankinSelberg.inducedFactor RankinSelberg.inducedEulerPoly RankinSelberg.inducedE1 RankinSelberg.inducedE2 RankinSelberg.inducedE3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn inducedCoeff psiLoc upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero coe_iotaGL valued_mul_apply_le3 localMaximalCompact3 LocalGL3 varpi varpi_ne_zero heckeGen1 heckeGen2 centralGen cNormQ cosetSum IsCosetEigenfunction IsRightInvariant IsInducedSphericalAt IsBadPlace ratPrimeAt ratPrimeUnit iotaTorusLocal iotaTorusLocal_zero sphericalTorusValue coe_diagUnits2 twoRowPointLocal twoRowPointLocal_zero_right HasSphericalTorusValuesAt exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3 exists_valued_eq_exp_of_coe_eq_diagonal_of_not_valued_lt eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant exists_isHeckeCosetSystem_heckeGen1_cosetSum_twoRowPointLocal exists_isHeckeCosetSystem_heckeGen2_cosetSum_twoRowPointLocal cosetSum_isRightInvariant_and_isGL3PsiWhittakerFn eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn finsum_primeFibre_inertiaDeg_eq_three_of_not_isRamifiedIn"
namespace InducedTriple
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Uniqueness

private theorem ringHom_ringOfIntegers_rat_ext {S : Type*} [NonAssocSemiring S] (f g : 𝓞 ℚ →+* S) : f = g := by
  have h : f.comp (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) =
      g.comp (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) :=
    RingHom.ext_int _ _
  refine RingHom.ext fun x => ?_
  obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
  exact RingHom.congr_fun h n

private theorem algebra_ringOfIntegers_eq (K : Type*) [Field K] [NumberField K] (inst : Algebra (𝓞 ℚ) (𝓞 K)) :
    inst = NumberField.inst_ringOfIntegersAlgebra ℚ K :=
  Algebra.algebra_ext _ _ fun r => RingHom.congr_fun (ringHom_ringOfIntegers_rat_ext _ _) r

end Uniqueness

section Fibre

variable (K : Type) [Field K] [NumberField K]

private theorem finite_primeFibre (v : HeightOneSpectrum (𝓞 ℚ)) : (RankinSelberg.primeFibre ℚ K v).Finite := by
  have hpre : (HeightOneSpectrum.asIdeal ⁻¹' Ideal.primesOver v.asIdeal (𝓞 K) :
      Set (HeightOneSpectrum (𝓞 K))).Finite :=
    (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)).preimage fun a _ b _ h => HeightOneSpectrum.ext h
  refine hpre.subset fun 𝔓 h𝔓 => ?_
  show 𝔓.asIdeal ∈ Ideal.primesOver v.asIdeal (𝓞 K)
  exact ⟨𝔓.isPrime, ⟨by rw [← (RankinSelberg.mem_primeFibre ℚ v 𝔓).mp h𝔓]; rfl⟩⟩

end Fibre

section E3

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

private theorem exists_finset_inducedEulerPoly_eq_prod (hdeg : Module.finrank ℚ K = 3) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ IsBadPlace K μ v) :
    ∃ s : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ 𝔓 ∈ s, 𝔓 ∈ RankinSelberg.primeFibre ℚ K v) ∧ (∀ 𝔓 ∈ s, inducedCoeff K μ 𝔓 ≠ 0) ∧
      (∀ 𝔓 ∈ s, 0 < (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) ∧
      (∑ 𝔓 ∈ s, (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) = 3 ∧ s.card ≤ 3 ∧
      RankinSelberg.inducedEulerPoly ℚ (inducedCoeff K μ) v =
        ∏ 𝔓 ∈ s, RankinSelberg.inducedFactor ℚ (inducedCoeff K μ) 𝔓 ∧
      (RankinSelberg.inducedEulerPoly ℚ (inducedCoeff K μ) v).natDegree = 3 ∧
      RankinSelberg.inducedE3 ℚ (inducedCoeff K μ) v = -∏ 𝔓 ∈ s, (-inducedCoeff K μ 𝔓) := by
  obtain rfl : ‹Algebra (𝓞 ℚ) (𝓞 K)› = NumberField.inst_ringOfIntegersAlgebra ℚ K :=
    algebra_ringOfIntegers_eq K _
  classical
  haveI : Module.Finite (𝓞 ℚ) (𝓞 K) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 ℚ) (𝓞 K)
  have hfin := finite_primeFibre K v

  have hc : ∀ 𝔓 ∈ hfin.toFinset, inducedCoeff K μ 𝔓 ≠ 0 := by
    intro 𝔓 h
    unfold inducedCoeff
    split_ifs with hunr
    · exact Units.ne_zero _
    · exact (hv (Or.inr ⟨𝔓, hfin.mem_toFinset.mp h, hunr⟩)).elim
  have hmem : ∀ 𝔓 ∈ hfin.toFinset, 𝔓.under (𝓞 ℚ) = v := fun 𝔓 h =>
    (RankinSelberg.mem_primeFibre ℚ v 𝔓).mp (hfin.mem_toFinset.mp h)

  have hf : ∀ 𝔓 ∈ hfin.toFinset, 0 < (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal := by
    intro 𝔓 _
    haveI : 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩
    exact Ideal.inertiaDeg_pos' _ _

  have hfac : ∀ 𝔓 ∈ hfin.toFinset,
      (RankinSelberg.inducedFactor ℚ (inducedCoeff K μ) 𝔓).natDegree =
          (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal ∧
        (RankinSelberg.inducedFactor ℚ (inducedCoeff K μ) 𝔓).leadingCoeff = -inducedCoeff K μ 𝔓 := by
    intro 𝔓 h
    have hc0 := hc 𝔓 h
    have hlt : (C (1 : ℂ)).degree <
        (C (inducedCoeff K μ 𝔓) * X ^ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal).degree := by
      rw [degree_C one_ne_zero, degree_C_mul_X_pow _ hc0]
      exact_mod_cast hf 𝔓 h
    have hltn : (C (1 : ℂ)).natDegree <
        (C (inducedCoeff K μ 𝔓) * X ^ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal).natDegree := by
      rw [natDegree_C, natDegree_C_mul_X_pow _ _ hc0]
      exact hf 𝔓 h
    unfold RankinSelberg.inducedFactor
    exact ⟨by rw [natDegree_sub_eq_right_of_natDegree_lt hltn, natDegree_C_mul_X_pow _ _ hc0],
      by rw [leadingCoeff_sub_of_degree_lt' hlt, leadingCoeff_C_mul_X_pow]⟩

  have hsumf : ∑ 𝔓 ∈ hfin.toFinset, (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal = 3 := by
    rw [← finsum_primeFibre_inertiaDeg_eq_three_of_not_isRamifiedIn K hdeg v fun h => hv (Or.inl h),
      finsum_mem_eq_finite_toFinset_sum _ hfin]
    exact Finset.sum_congr rfl fun 𝔓 h => by rw [hmem 𝔓 h]

  have hcard : hfin.toFinset.card ≤ 3 := by
    rw [Finset.card_eq_sum_ones, ← hsumf]
    exact Finset.sum_le_sum fun 𝔓 h => hf 𝔓 h

  have hlead : ∏ 𝔓 ∈ hfin.toFinset, (RankinSelberg.inducedFactor ℚ (inducedCoeff K μ) 𝔓).leadingCoeff ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro 𝔓 h
    rw [(hfac 𝔓 h).2, neg_ne_zero]
    exact hc 𝔓 h
  have hprod : RankinSelberg.inducedEulerPoly ℚ (inducedCoeff K μ) v =
      ∏ 𝔓 ∈ hfin.toFinset, RankinSelberg.inducedFactor ℚ (inducedCoeff K μ) 𝔓 := by
    unfold RankinSelberg.inducedEulerPoly
    exact finprod_mem_eq_finite_toFinset_prod _ hfin
  have hnat : (RankinSelberg.inducedEulerPoly ℚ (inducedCoeff K μ) v).natDegree = 3 := by
    rw [hprod, natDegree_prod' _ _ hlead, ← hsumf]
    exact Finset.sum_congr rfl fun 𝔓 h => (hfac 𝔓 h).1
  have he3 : RankinSelberg.inducedE3 ℚ (inducedCoeff K μ) v = -∏ 𝔓 ∈ hfin.toFinset, (-inducedCoeff K μ 𝔓) := by
    unfold RankinSelberg.inducedE3
    rw [← hnat, coeff_natDegree, hprod, leadingCoeff_prod' _ _ hlead]
    exact congrArg Neg.neg (Finset.prod_congr rfl fun 𝔓 h => (hfac 𝔓 h).2)
  exact ⟨hfin.toFinset, fun 𝔓 h => hfin.mem_toFinset.mp h, hc, hf, hsumf, hcard, hprod, hnat, he3⟩

private theorem inducedE3_inducedCoeff_ne_zero (hdeg : Module.finrank ℚ K = 3) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ IsBadPlace K μ v) :
    RankinSelberg.inducedE3 ℚ (inducedCoeff K μ) v ≠ 0 := by
  obtain ⟨s, -, hc, -, -, -, -, -, he⟩ := exists_finset_inducedEulerPoly_eq_prod K hdeg μ v hv
  rw [he, neg_ne_zero, Finset.prod_ne_zero_iff]
  exact fun 𝔓 h => neg_ne_zero.mpr (hc 𝔓 h)

end E3

end LanglandsTunnell.CubicInduction.InducedTriple

set_option autoImplicit false

open IsDedekindDomain NumberField
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RankinSelberg.primeFibre RankinSelberg.mem_primeFibre RankinSelberg.inducedFactor RankinSelberg.inducedEulerPoly RankinSelberg.inducedE1 RankinSelberg.inducedE2 RankinSelberg.inducedE3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn inducedCoeff psiLoc upperUnipotent3 upperUnipotent3_coe upperUnipotent3_zero coe_iotaGL valued_mul_apply_le3 localMaximalCompact3 LocalGL3 varpi varpi_ne_zero heckeGen1 heckeGen2 centralGen cNormQ cosetSum IsCosetEigenfunction IsRightInvariant IsInducedSphericalAt IsBadPlace ratPrimeAt ratPrimeUnit iotaTorusLocal iotaTorusLocal_zero sphericalTorusValue coe_diagUnits2 twoRowPointLocal twoRowPointLocal_zero_right HasSphericalTorusValuesAt exists_eq_upperUnipotent3_mul_diagonal_mul_mem_localMaximalCompact3 exists_valued_eq_exp_of_coe_eq_diagonal_of_not_valued_lt eq_zpow_mul_twoRowPointLocal_of_coe_eq_diagonal_of_isRightInvariant exists_isHeckeCosetSystem_heckeGen1_cosetSum_twoRowPointLocal exists_isHeckeCosetSystem_heckeGen2_cosetSum_twoRowPointLocal cosetSum_isRightInvariant_and_isGL3PsiWhittakerFn eq_zero_of_coe_eq_diagonal_of_valued_lt_of_isGL3PsiWhittakerFn finsum_primeFibre_inertiaDeg_eq_three_of_not_isRamifiedIn"
namespace SphericalNormalization
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem exists_of_level_zero {K : Type} [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (c : HeightOneSpectrum (𝓞 K) → ℂ) (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1)
    (he₃ : RankinSelberg.inducedE3 ℚ c v ≠ 0) :
    ∃ W : LocalGL3 v → ℂ, IsGL3PsiWhittakerFn ψv W ∧
      IsInducedSphericalAt c v (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧ W 1 = 1 ∧ HasSphericalTorusValuesAt c v W := by
  obtain ⟨W, hW, hinv, hZ, h1, ht, h2⟩ := exists_sphericalWhittakerFn_of_forall_valued_le_one v ψv hψ0
    (RankinSelberg.inducedE1 ℚ c v) (RankinSelberg.inducedE2 ℚ c v) (RankinSelberg.inducedE3 ℚ c v) he₃
  have heig := SphericalWhittakerEigen.isCosetEigenfunction_heckeGen1_and_heckeGen2 v ψv hψ0 hψ1 W
    (RankinSelberg.inducedE1 ℚ c v) (RankinSelberg.inducedE2 ℚ c v) (RankinSelberg.inducedE3 ℚ c v) hW hinv hZ ht h2
  exact ⟨W, hW, ⟨hinv, heig.1, heig.2, hZ⟩, h1, ht, h2⟩

end LanglandsTunnell.CubicInduction.SphericalNormalization

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace.LanglandsTunnell.CubicInduction"

theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ IsBadPlace K μ v)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → psiLoc ψ v x = 1)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ psiLoc ψ v ((varpi v)⁻¹ * x) ≠ 1) :
    ∃ W : LocalGL3 v → ℂ,
      IsGL3PsiWhittakerFn (psiLoc ψ v) W ∧
      IsInducedSphericalAt (inducedCoeff K μ) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      W 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v W := by
  exact LanglandsTunnell.CubicInduction.SphericalNormalization.exists_of_level_zero
    (inducedCoeff K μ) v (psiLoc ψ v) hψ0 hψ1
    (LanglandsTunnell.CubicInduction.InducedTriple.inducedE3_inducedCoeff_ne_zero K hdeg μ v hv)

end S_LanglandsTunnell_CubicInduction_exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace (solution)
