-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/d6c05f28-1967-5732-be82-abf30b3cd680

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level
import Theorems.Thm_LanglandsTunnell_CubicInduction_apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.principalSeries3 CubicInduction.upperUnipotent3 CubicInduction.radicalP21 CubicInduction.iotaGL CubicInduction.LocalGL3 TateLocal.higherUnitsAt CubicInduction.diagUnitGL2 CubicInduction.lowerUnipotent21 CubicInduction.longWeyl3 CubicInduction.weylPrime3 CubicInduction.eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level CubicInduction.apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 apply_upperUnipotent3_mul_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP21_coe radicalP21_add embedMat2 iotaGL coe_iotaGL iotaGL_unipotentGL2 LocalGL3 diagUnitGL2 coe_diagUnitGL2 diagUnits2 coe_diagUnits2 lowerUnipotent21 longWeyl3 longWeyl3_coe weylPrime3 weylPrime3_coe eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level"
namespace OpenCell
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

p2m_open "Matrix LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level.LanglandsTunnell.CubicInduction"

section MatrixIdentities

variable {A : Type*} [CommRing A]

def lowerU (s : A) : GL (Fin 2) A where
  val := !![1, 0; s, 1]
  inv := !![1, 0; -s, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem coe_lowerU (s : A) : ((lowerU s : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![1, 0; s, 1] := rfl

def weyl : GL (Fin 2) A where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem coe_weyl : ((weyl : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![0, 1; 1, 0] := rfl

theorem weyl_mul_weyl : (weyl : GL (Fin 2) A) * weyl = 1 := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_weyl, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem weyl_inv : (weyl : GL (Fin 2) A)⁻¹ = weyl := inv_eq_of_mul_eq_one_right weyl_mul_weyl

theorem iotaGL_lowerU (s : A) : iotaGL (lowerU s) = lowerUnipotent21 s := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, lowerU]

theorem iotaGL_mul_radicalP21 (h : GL (Fin 2) A) (Y : Fin 2 → A) :
    iotaGL h * radicalP21 Y = radicalP21 ((h : Matrix (Fin 2) (Fin 2) A) *ᵥ Y) * iotaGL h := by
  refine Units.ext ?_
  ext i j
  simp only [Units.val_mul, coe_iotaGL, radicalP21_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

theorem vec2_add (a b c d : A) : (![a, b] : Fin 2 → A) + ![c, d] = ![a + c, b + d] := by
  ext i
  fin_cases i <;> simp

theorem diagUnitGL2_mulVec (u : Aˣ) (z y : A) :
    ((diagUnitGL2 u : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) *ᵥ ![z, y] = ![(u : A) * z, y] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem unipotentGL2_mulVec (t z y : A) :
    ((AutomorphicForm.unipotentGL2 t : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) *ᵥ ![z, y] = ![z + t * y, y] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem lowerU_mulVec (t z y : A) :
    ((lowerU t : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) *ᵥ ![z, y] = ![z, t * z + y] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem longWeyl3_mul_iotaGL_lowerU (x : A) :
    (longWeyl3 : GL (Fin 3) A) * iotaGL (lowerU x) = upperUnipotent3 0 x 0 * longWeyl3 := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, longWeyl3_coe, coe_iotaGL, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, lowerU, Matrix.mul_apply, Fin.sum_univ_three]

theorem weyl_mul_unipotent (x : A) : (weyl : GL (Fin 2) A) * AutomorphicForm.unipotentGL2 x = lowerU x * weyl := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_weyl, coe_lowerU, AutomorphicForm.unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem weyl_mul_diagUnits2 (a d : Aˣ) : (weyl : GL (Fin 2) A) * diagUnits2 a d = diagUnits2 d a * weyl := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_weyl, coe_diagUnits2, coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end MatrixIdentities

section Local

variable {v : HeightOneSpectrum (𝓞 ℚ)}

theorem longWeyl3_mul_iotaGL_diagUnits2 (a d : (v.adicCompletion ℚ)ˣ) :
    (longWeyl3 : LocalGL3 v) * iotaGL (diagUnits2 a d) = diagonal3 v ![1, d, a] * longWeyl3 := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, longWeyl3_coe, coe_iotaGL, diagonal3_coe, coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal]

theorem iotaGL_diagUnitGL2_mul_radicalP21 (u : (v.adicCompletion ℚ)ˣ) (z y : v.adicCompletion ℚ) :
    (iotaGL (diagUnitGL2 u) : LocalGL3 v) * radicalP21 ![z, y] =
      radicalP21 ![(u : v.adicCompletion ℚ) * z, y] * iotaGL (diagUnitGL2 u) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, radicalP21_coe, radicalP21_coe, coe_iotaGL, coe_diagUnitGL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

theorem iotaGL_unipotent_mul_radicalP21 (t z y : v.adicCompletion ℚ) :
    (iotaGL (AutomorphicForm.unipotentGL2 t) : LocalGL3 v) * radicalP21 ![z, y] =
      radicalP21 ![t * y + z, y] * iotaGL (AutomorphicForm.unipotentGL2 t) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, radicalP21_coe, radicalP21_coe, coe_iotaGL, AutomorphicForm.unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem iotaGL_lowerU_mul_radicalP21 (t z y : v.adicCompletion ℚ) :
    (iotaGL (lowerU t) : LocalGL3 v) * radicalP21 ![z, y] =
      radicalP21 ![z, t * z + y] * iotaGL (lowerU t) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, radicalP21_coe, radicalP21_coe, coe_iotaGL, coe_lowerU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

noncomputable def kappa (ε r₀ r₁ : v.adicCompletion ℚ) : LocalGL3 v where
  val := !![1, 0, 0; 0, 1, 0; ε * r₀, ε * r₁, 1]
  inv := !![1, 0, 0; 0, 1, 0; -(ε * r₀), -(ε * r₁), 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem support_identity_z {z : v.adicCompletion ℚ} (hz : z ≠ 0) (y : v.adicCompletion ℚ)
    (k : GL (Fin 2) (v.adicCompletion ℚ)) :
    (longWeyl3 : LocalGL3 v) * radicalP21 ![z, y] * iotaGL k =
      diagonal3 v ![Units.mk0 (-z⁻¹) (neg_ne_zero.mpr (inv_ne_zero hz)), 1, Units.mk0 z hz] *
        upperUnipotent3 0 y (-z) *
        (iotaGL (lowerU (-(y / z)) * k) *
          kappa z⁻¹ ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0) ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1)) := by
  refine Units.ext ?_
  simp only [Units.val_mul, longWeyl3_coe, radicalP21_coe, coe_iotaGL, diagonal3_coe, upperUnipotent3_coe, coe_lowerU]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, kappa, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.diagonal] <;>
    field_simp <;> ring

theorem support_identity_y {y : v.adicCompletion ℚ} (hy : y ≠ 0) (z : v.adicCompletion ℚ)
    (k : GL (Fin 2) (v.adicCompletion ℚ)) :
    (longWeyl3 : LocalGL3 v) * radicalP21 ![z, y] * iotaGL k =
      diagonal3 v ![Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy)), Units.mk0 y hy, 1] *
        upperUnipotent3 (-y) 0 0 *
        (weylPrime3 * radicalP21 ![0, z] * iotaGL (weyl * AutomorphicForm.unipotentGL2 (-(z / y)) * k) *
          kappa y⁻¹ ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0) ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1)) := by
  refine Units.ext ?_
  simp only [Units.val_mul, longWeyl3_coe, weylPrime3_coe, radicalP21_coe, coe_iotaGL, diagonal3_coe,
    upperUnipotent3_coe, coe_weyl, AutomorphicForm.unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, kappa, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.diagonal] <;>
    field_simp <;> ring

end Local

section Integral

variable {v : HeightOneSpectrum (𝓞 ℚ)}

def IsInt (k : GL (Fin 2) (v.adicCompletion ℚ)) : Prop :=
  (∀ i j, Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) ∧
    ∀ i j, Valued.v ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1

theorem valued_mul_apply_le_one {a b : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)}
    (ha : ∀ i j, Valued.v (a i j) ≤ 1) (hb : ∀ i j, Valued.v (b i j) ≤ 1) (i j : Fin 2) :
    Valued.v ((a * b) i j) ≤ 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_) <;> rw [map_mul] <;> exact mul_le_one' (ha _ _) (hb _ _)

theorem isInt_mul {k₁ k₂ : GL (Fin 2) (v.adicCompletion ℚ)} (h₁ : IsInt k₁) (h₂ : IsInt k₂) : IsInt (k₁ * k₂) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul]
    exact valued_mul_apply_le_one h₁.1 h₂.1 i j
  · rw [_root_.mul_inv_rev, Units.val_mul]
    exact valued_mul_apply_le_one h₂.2 h₁.2 i j

theorem isInt_unipotent {x : v.adicCompletion ℚ} (hx : Valued.v x ≤ 1) : IsInt (AutomorphicForm.unipotentGL2 x) := by
  have hinv : (((AutomorphicForm.unipotentGL2 x)⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![1, -x; 0, 1] := rfl
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [AutomorphicForm.unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp [hx]
  · rw [hinv]
    fin_cases i <;> fin_cases j <;> simp [hx]

theorem isInt_weyl : IsInt (weyl : GL (Fin 2) (v.adicCompletion ℚ)) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_weyl]
    fin_cases i <;> fin_cases j <;> simp
  · rw [weyl_inv, coe_weyl]
    fin_cases i <;> fin_cases j <;> simp

theorem valued_mulVec_le_max {a : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)} (ha : ∀ i j, Valued.v (a i j) ≤ 1)
    (Y : Fin 2 → v.adicCompletion ℚ) (i : Fin 2) :
    Valued.v ((a *ᵥ Y) i) ≤ max (Valued.v (Y 0)) (Valued.v (Y 1)) := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · rw [map_mul]
    exact ((mul_le_mul' (ha i 0) le_rfl).trans_eq (one_mul _)).trans (le_max_left _ _)
  · rw [map_mul]
    exact ((mul_le_mul' (ha i 1) le_rfl).trans_eq (one_mul _)).trans (le_max_right _ _)

theorem norm_eq_one_of_valued_eq_one {u : v.adicCompletion ℚ} (hu : Valued.v u = 1) : ‖u‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def, hu, map_one, NNReal.coe_one]

end Integral

section Residue

variable {v : HeightOneSpectrum (𝓞 ℚ)}

def IsPer (lo : ℤ) (f : v.adicCompletion ℚ → ℂ) : Prop :=
  ∀ y h : v.adicCompletion ℚ, Valued.v h ≤ WithZero.exp lo → f (y + h) = f y

theorem sum_comp_eq {S : Finset (v.adicCompletion ℚ)} {c lo : ℤ}
    (hS : ∀ s ∈ S, Valued.v s ≤ WithZero.exp c)
    (hS' : ∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp c → ∃! s, s ∈ S ∧ Valued.v (y - s) ≤ WithZero.exp lo)
    {f : v.adicCompletion ℚ → ℂ} (hf : IsPer lo f) (φ : v.adicCompletion ℚ → v.adicCompletion ℚ)
    (hφc : ∀ y, Valued.v y ≤ WithZero.exp c → Valued.v (φ y) ≤ WithZero.exp c)
    (hφiso : ∀ y y', Valued.v (φ y - φ y') = Valued.v (y - y')) :
    ∑ s ∈ S, f (φ s) = ∑ s ∈ S, f s := by
  classical

  have hex : ∀ s ∈ S, ∃ s', s' ∈ S ∧ Valued.v (φ s - s') ≤ WithZero.exp lo := fun s hs =>
    (hS' (φ s) (hφc s (hS s hs))).exists
  choose! σ hσS hσclose using hex
  have hval : ∀ s ∈ S, f (φ s) = f (σ s) := fun s hs => by
    have h := hf (σ s) (φ s - σ s) (hσclose s hs)
    rwa [add_sub_cancel] at h
  have hinj : Set.InjOn σ S := by
    intro s₁ h₁ s₂ h₂ heq
    have hd : Valued.v (s₁ - s₂) ≤ WithZero.exp lo := by
      rw [← hφiso]
      have hrew : φ s₁ - φ s₂ = (φ s₁ - σ s₁) + (φ s₂ - σ s₂) * (-1) := by rw [heq]; ring
      rw [hrew]
      refine (Valuation.map_add _ _ _).trans (max_le (hσclose s₁ h₁) ?_)
      rw [map_mul, Valuation.map_neg, map_one, mul_one]
      exact hσclose s₂ h₂
    obtain ⟨s, -, huniq⟩ := hS' s₁ (hS s₁ h₁)
    have e1 : s₁ = s := huniq s₁ ⟨h₁, by simp⟩
    have e2 : s₂ = s := huniq s₂ ⟨h₂, hd⟩
    rw [e1, e2]
  have hsurj : Set.SurjOn σ S S := by
    intro s' hs'
    obtain ⟨s, hs, hEq⟩ := Finset.surj_on_of_inj_on_of_card_le (fun s _ => σ s) (fun s hs => hσS s hs)
      (fun a₁ a₂ h₁ h₂ heq => hinj h₁ h₂ heq) le_rfl s' hs'
    exact ⟨s, hs, hEq.symm⟩
  rw [Finset.sum_nbij σ hσS hinj hsurj hval]

theorem sum_add_left_eq {S : Finset (v.adicCompletion ℚ)} {c lo : ℤ}
    (hS : ∀ s ∈ S, Valued.v s ≤ WithZero.exp c)
    (hS' : ∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp c → ∃! s, s ∈ S ∧ Valued.v (y - s) ≤ WithZero.exp lo)
    {f : v.adicCompletion ℚ → ℂ} (hf : IsPer lo f) {a : v.adicCompletion ℚ} (ha : Valued.v a ≤ WithZero.exp c) :
    ∑ s ∈ S, f (a + s) = ∑ s ∈ S, f s :=
  sum_comp_eq hS hS' hf (fun y => a + y) (fun y hy => (Valuation.map_add _ _ _).trans (max_le ha hy))
    (fun y y' => by rw [add_sub_add_left_eq_sub])

theorem sum_mul_left_eq {S : Finset (v.adicCompletion ℚ)} {c lo : ℤ}
    (hS : ∀ s ∈ S, Valued.v s ≤ WithZero.exp c)
    (hS' : ∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp c → ∃! s, s ∈ S ∧ Valued.v (y - s) ≤ WithZero.exp lo)
    {f : v.adicCompletion ℚ → ℂ} (hf : IsPer lo f) {u : v.adicCompletion ℚ} (hu : Valued.v u = 1) :
    ∑ s ∈ S, f (u * s) = ∑ s ∈ S, f s :=
  sum_comp_eq hS hS' hf (fun y => u * y) (fun y hy => by rw [map_mul, hu, one_mul]; exact hy)
    (fun y y' => by rw [← mul_sub, map_mul, hu, one_mul])

theorem apply_eq_apply_of_close {lo : ℤ} {f : v.adicCompletion ℚ → ℂ} (hf : IsPer lo f) {y s : v.adicCompletion ℚ}
    (h : Valued.v (y - s) ≤ WithZero.exp lo) : f y = f s := by
  have h' := hf s (y - s) h
  rwa [add_sub_cancel] at h'

end Residue

section Terms

variable {v : HeightOneSpectrum (𝓞 ℚ)} {Ψ : LocalGL3 v → ℂ}

theorem term_diag
    (hdiag : ∀ (g : LocalGL3 v) (u : (v.adicCompletion ℚ)ˣ), Valued.v (u : v.adicCompletion ℚ) = 1 →
      Ψ (g * iotaGL (diagUnitGL2 u)) = Ψ g)
    (k' : GL (Fin 2) (v.adicCompletion ℚ)) {u : (v.adicCompletion ℚ)ˣ} (hu : Valued.v (u : v.adicCompletion ℚ) = 1)
    (s s' : v.adicCompletion ℚ) :
    Ψ (longWeyl3 * iotaGL (k' * diagUnitGL2 u) * radicalP21 ![s, s']) =
      Ψ (longWeyl3 * iotaGL k' * radicalP21 ![(u : v.adicCompletion ℚ) * s, s']) := by
  rw [map_mul, mul_assoc, mul_assoc, iotaGL_diagUnitGL2_mul_radicalP21, ← mul_assoc, ← mul_assoc]
  exact hdiag _ u hu

theorem term_unipotent {b : ℕ}
    (hupper : ∀ (g : LocalGL3 v) (s : v.adicCompletion ℚ), Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Ψ (g * upperUnipotent3 s 0 0) = Ψ g)
    (k' : GL (Fin 2) (v.adicCompletion ℚ)) {t : v.adicCompletion ℚ} (ht : Valued.v t ≤ WithZero.exp (-(b : ℤ)))
    (s s' : v.adicCompletion ℚ) :
    Ψ (longWeyl3 * iotaGL (k' * AutomorphicForm.unipotentGL2 t) * radicalP21 ![s, s']) =
      Ψ (longWeyl3 * iotaGL k' * radicalP21 ![t * s' + s, s']) := by
  rw [map_mul, mul_assoc, mul_assoc, iotaGL_unipotent_mul_radicalP21, ← mul_assoc, ← mul_assoc, iotaGL_unipotentGL2]
  exact hupper _ t ht

theorem term_lower {b : ℕ}
    (hlower : ∀ (g : LocalGL3 v) (s : v.adicCompletion ℚ), Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Ψ (g * lowerUnipotent21 s) = Ψ g)
    (k' : GL (Fin 2) (v.adicCompletion ℚ)) {t : v.adicCompletion ℚ} (ht : Valued.v t ≤ WithZero.exp (-(b : ℤ)))
    (s s' : v.adicCompletion ℚ) :
    Ψ (longWeyl3 * iotaGL (k' * lowerU t) * radicalP21 ![s, s']) =
      Ψ (longWeyl3 * iotaGL k' * radicalP21 ![s, t * s + s']) := by
  rw [map_mul, mul_assoc, mul_assoc, iotaGL_lowerU_mul_radicalP21, ← mul_assoc, ← mul_assoc, iotaGL_lowerU]
  exact hlower _ t ht

noncomputable def orbSum (Ψ : LocalGL3 v → ℂ) (S : Finset (v.adicCompletion ℚ)) (k' : GL (Fin 2) (v.adicCompletion ℚ)) : ℂ :=
  ∑ s ∈ S, ∑ s' ∈ S, Ψ (longWeyl3 * iotaGL k' * radicalP21 ![s, s'])

theorem orbSum_apply (Ψ : LocalGL3 v → ℂ) (S : Finset (v.adicCompletion ℚ)) (k' : GL (Fin 2) (v.adicCompletion ℚ)) :
    orbSum Ψ S k' = ∑ s ∈ S, ∑ s' ∈ S, Ψ (longWeyl3 * iotaGL k' * radicalP21 ![s, s']) := rfl

end Terms

end LanglandsTunnell.CubicInduction.OpenCell
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level.LanglandsTunnell.CubicInduction.OpenCell"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level.LanglandsTunnell"

set_option maxHeartbeats 4000000 in
open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.OpenCell in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (b : ℕ)
    (hχ : ∀ i, ∃ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v b, χ i u ≠ 1)
    (Ψ : LanglandsTunnell.CubicInduction.LocalGL3 v → ℂ)
    (hΨ : Ψ ∈ LanglandsTunnell.CubicInduction.principalSeries3 v χ)
    (hdiag : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v (u : v.adicCompletion ℚ) = 1 →
      Ψ (g * LanglandsTunnell.CubicInduction.iotaGL (LanglandsTunnell.CubicInduction.diagUnitGL2 u)) = Ψ g)
    (hupper : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Ψ (g * LanglandsTunnell.CubicInduction.upperUnipotent3 s 0 0) = Ψ g)
    (hlower : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Ψ (g * LanglandsTunnell.CubicInduction.lowerUnipotent21 s) = Ψ g)
    (m : ℕ)
    (hm : ∀ κ : LanglandsTunnell.CubicInduction.LocalGL3 v,
      (∀ i j, Valued.v ((κ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))) →
      ∀ g : LanglandsTunnell.CubicInduction.LocalGL3 v, Ψ (g * κ) = Ψ g)
    (hmid : ∀ k' : GL (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, Valued.v ((k' : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) →
      (∀ i j, Valued.v ((k'⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) →
      ∀ y : v.adicCompletion ℚ,
        Ψ (LanglandsTunnell.CubicInduction.weylPrime3 * LanglandsTunnell.CubicInduction.radicalP21 ![0, y] *
          LanglandsTunnell.CubicInduction.iotaGL k') = 0)
    (k : GL (Fin 2) (v.adicCompletion ℚ))
    (hk : ∀ i j, Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1)
    (hkinv : ∀ i j, Valued.v ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) :
    (∀ Y : Fin 2 → v.adicCompletion ℚ, WithZero.exp (m : ℤ) ≤ max (Valued.v (Y 0)) (Valued.v (Y 1)) →
      Ψ (LanglandsTunnell.CubicInduction.longWeyl3 * LanglandsTunnell.CubicInduction.iotaGL k *
        LanglandsTunnell.CubicInduction.radicalP21 Y) = 0) ∧
    ∀ (c : ℕ) (S : Finset (v.adicCompletion ℚ)), m ≤ c →
      (∀ s ∈ S, Valued.v s ≤ WithZero.exp (c : ℤ)) →
      (∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp (c : ℤ) →
        ∃! s, s ∈ S ∧ Valued.v (y - s) ≤ WithZero.exp (-(m : ℤ))) →
      ∑ s ∈ S, ∑ s' ∈ S, Ψ (LanglandsTunnell.CubicInduction.longWeyl3 * LanglandsTunnell.CubicInduction.iotaGL k *
        LanglandsTunnell.CubicInduction.radicalP21 ![s, s']) = 0 := by
  classical

  have hP : ∀ x : LocalGL3 v, (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 →
      (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 → Ψ x = 0 := fun x h20 h21 =>
    LanglandsTunnell.CubicInduction.apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level v χ b
      (hχ 0) (hχ 1) Ψ hΨ hdiag hupper hlower x h20 h21

  have hsuppZ : ∀ k' : GL (Fin 2) (v.adicCompletion ℚ), IsInt k' →
      ∀ Z : Fin 2 → v.adicCompletion ℚ, WithZero.exp (m : ℤ) ≤ max (Valued.v (Z 0)) (Valued.v (Z 1)) →
      Ψ (longWeyl3 * radicalP21 Z * iotaGL k') = 0 := by
    intro k' hk' Z hZ
    have hZeq : Z = ![Z 0, Z 1] := by
      ext i
      fin_cases i <;> rfl
    rcases le_or_gt (Valued.v (Z 1)) (Valued.v (Z 0)) with hle | hlt
    ·
      have hz : WithZero.exp (m : ℤ) ≤ Valued.v (Z 0) := hZ.trans (max_le le_rfl hle)
      have hz0 : Z 0 ≠ 0 := by
        intro h
        rw [h, map_zero] at hz
        exact (lt_of_lt_of_le WithZero.exp_pos hz).false.elim
      have hzinv : Valued.v (Z 0)⁻¹ ≤ WithZero.exp (-(m : ℤ)) := by
        rw [map_inv₀, WithZero.exp_neg]
        exact inv_anti₀ WithZero.exp_pos hz
      have hκ : ∀ i j, Valued.v ((kappa (Z 0)⁻¹ ((k' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 0)
          ((k' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 1) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
          (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ)) := by
        intro i j
        fin_cases i <;> fin_cases j <;> simp [kappa]
        · simpa using (mul_le_mul' hzinv (hk'.1 0 0)).trans_eq (mul_one _)
        · simpa using (mul_le_mul' hzinv (hk'.1 0 1)).trans_eq (mul_one _)
      rw [hZeq, support_identity_z hz0 (Z 1) k', mul_assoc (diagonal3 v _),
        apply_diagonal3_mul_of_mem_principalSeries3 hΨ, apply_upperUnipotent3_mul_of_mem_principalSeries3 hΨ,
        hm _ hκ _, hP _ (by simp [embedMat2]) (by simp [embedMat2]), mul_zero]
    ·
      have hy : WithZero.exp (m : ℤ) ≤ Valued.v (Z 1) := hZ.trans (max_le hlt.le le_rfl)
      have hy0 : Z 1 ≠ 0 := by
        intro h
        rw [h, map_zero] at hy
        exact (lt_of_lt_of_le WithZero.exp_pos hy).false.elim
      have hyinv : Valued.v (Z 1)⁻¹ ≤ WithZero.exp (-(m : ℤ)) := by
        rw [map_inv₀, WithZero.exp_neg]
        exact inv_anti₀ WithZero.exp_pos hy
      have hκ : ∀ i j, Valued.v ((kappa (Z 1)⁻¹ ((k' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0)
          ((k' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
          (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ)) := by
        intro i j
        fin_cases i <;> fin_cases j <;> simp [kappa]
        · simpa using (mul_le_mul' hyinv (hk'.1 1 0)).trans_eq (mul_one _)
        · simpa using (mul_le_mul' hyinv (hk'.1 1 1)).trans_eq (mul_one _)
      have hI : IsInt (weyl * AutomorphicForm.unipotentGL2 (-(Z 0 / Z 1)) * k') := by
        refine isInt_mul (isInt_mul isInt_weyl (isInt_unipotent ?_)) hk'
        rw [Valuation.map_neg, map_div₀]
        exact div_le_one_of_le₀ hlt.le zero_le'
      rw [hZeq, support_identity_y hy0 (Z 0) k', mul_assoc (diagonal3 v _),
        apply_diagonal3_mul_of_mem_principalSeries3 hΨ, apply_upperUnipotent3_mul_of_mem_principalSeries3 hΨ,
        hm _ hκ _, hmid _ hI.1 hI.2 (Z 0), mul_zero]

  have hsupp : ∀ Y : Fin 2 → v.adicCompletion ℚ, WithZero.exp (m : ℤ) ≤ max (Valued.v (Y 0)) (Valued.v (Y 1)) →
      Ψ (longWeyl3 * iotaGL k * radicalP21 Y) = 0 := by
    intro Y hY
    rw [mul_assoc, iotaGL_mul_radicalP21, ← mul_assoc]
    refine hsuppZ k ⟨hk, hkinv⟩ _ (hY.trans ?_)
    have hback : Y = Matrix.mulVec (((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
        (Matrix.mulVec (((k : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) Y) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    refine max_le ?_ ?_
    · conv_lhs => rw [hback]
      exact valued_mulVec_le_max hkinv _ 0
    · conv_lhs => rw [hback]
      exact valued_mulVec_le_max hkinv _ 1
  refine ⟨hsupp, fun c S hmc hS hS' => ?_⟩

  have hperz : ∀ (k' : GL (Fin 2) (v.adicCompletion ℚ)) (y : v.adicCompletion ℚ),
      IsPer (-(m : ℤ)) fun z => Ψ (longWeyl3 * iotaGL k' * radicalP21 ![z, y]) := by
    intro k' y z h hh
    dsimp only
    rw [show (![z + h, y] : Fin 2 → v.adicCompletion ℚ) = ![z, y] + ![h, 0] by rw [vec2_add, add_zero],
      radicalP21_add, ← mul_assoc, hm _ ?_ _]
    intro i j
    rw [radicalP21_coe]
    fin_cases i <;> fin_cases j <;> simp
    simpa using hh
  have hpery : ∀ (k' : GL (Fin 2) (v.adicCompletion ℚ)) (z : v.adicCompletion ℚ),
      IsPer (-(m : ℤ)) fun y => Ψ (longWeyl3 * iotaGL k' * radicalP21 ![z, y]) := by
    intro k' z y h hh
    dsimp only
    rw [show (![z, y + h] : Fin 2 → v.adicCompletion ℚ) = ![z, y] + ![0, h] by rw [vec2_add, add_zero],
      radicalP21_add, ← mul_assoc, hm _ ?_ _]
    intro i j
    rw [radicalP21_coe]
    fin_cases i <;> fin_cases j <;> simp
    simpa using hh

  have hR1 : ∀ (k' : GL (Fin 2) (v.adicCompletion ℚ)) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v (u : v.adicCompletion ℚ) = 1 → orbSum Ψ S (k' * diagUnitGL2 u) = orbSum Ψ S k' := by
    intro k' u hu
    simp only [orbSum_apply, term_diag hdiag k' hu]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s' _ => sum_mul_left_eq hS hS' (hperz k' s') hu
  have hR2 : ∀ (k' : GL (Fin 2) (v.adicCompletion ℚ)) (t : v.adicCompletion ℚ),
      Valued.v t ≤ WithZero.exp (-(b : ℤ)) → orbSum Ψ S (k' * AutomorphicForm.unipotentGL2 t) = orbSum Ψ S k' := by
    intro k' t ht
    have ht1 : Valued.v t ≤ 1 := ht.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
    simp only [orbSum_apply, term_unipotent hupper k' ht]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' hs' => ?_
    have hshift : Valued.v (t * s') ≤ WithZero.exp (c : ℤ) := by
      rw [map_mul]
      exact (mul_le_mul' ht1 (hS s' hs')).trans_eq (one_mul _)
    exact sum_add_left_eq hS hS' (hperz k' s') hshift
  have hR3 : ∀ (k' : GL (Fin 2) (v.adicCompletion ℚ)) (t : v.adicCompletion ℚ),
      Valued.v t ≤ WithZero.exp (-(b : ℤ)) → orbSum Ψ S (k' * lowerU t) = orbSum Ψ S k' := by
    intro k' t ht
    have ht1 : Valued.v t ≤ 1 := ht.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
    simp only [orbSum_apply, term_lower hlower k' ht]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hshift : Valued.v (t * s) ≤ WithZero.exp (c : ℤ) := by
      rw [map_mul]
      exact (mul_le_mul' ht1 (hS s hs)).trans_eq (one_mul _)
    exact sum_add_left_eq hS hS' (hpery k' s) hshift

  have hL1 : ∀ (a d : (v.adicCompletion ℚ)ˣ) (k' : GL (Fin 2) (v.adicCompletion ℚ)),
      Valued.v (a : v.adicCompletion ℚ) = 1 → Valued.v (d : v.adicCompletion ℚ) = 1 →
      orbSum Ψ S (diagUnits2 a d * k') = ((χ 2 a : ℂˣ) : ℂ) * ((χ 1 d : ℂˣ) : ℂ) * orbSum Ψ S k' := by
    intro a d k' ha hd
    simp only [orbSum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    rw [map_mul, ← mul_assoc, longWeyl3_mul_iotaGL_diagUnits2, mul_assoc (diagonal3 v _), mul_assoc (diagonal3 v _),
      apply_diagonal3_mul_of_mem_principalSeries3 hΨ]
    simp only [torusChar3, halfModulus3, Fin.prod_univ_three]
    simp [norm_eq_one_of_valued_eq_one ha, mul_comm, mul_assoc]
  have hL2 : ∀ (x : v.adicCompletion ℚ) (k' : GL (Fin 2) (v.adicCompletion ℚ)), orbSum Ψ S (lowerU x * k') = orbSum Ψ S k' := by
    intro x k'
    simp only [orbSum_apply]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    rw [map_mul, ← mul_assoc, longWeyl3_mul_iotaGL_lowerU, mul_assoc (upperUnipotent3 _ _ _),
      mul_assoc (upperUnipotent3 _ _ _), apply_upperUnipotent3_mul_of_mem_principalSeries3 hΨ]

  have hF₁ : ∀ k' : GL (Fin 2) (v.adicCompletion ℚ), IsInt k' → orbSum Ψ S (weyl * k') = 0 := by
    intro k' hk'
    refine LanglandsTunnell.CubicInduction.eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level v b (χ 1) (χ 2)
      (hχ 1) (hχ 2) (fun k'' => orbSum Ψ S (weyl * k'')) ?_ ?_ ?_ ?_ ?_ k' hk'.1 hk'.2
    · intro u₁ u₂ k'' _ _ hu₁ hu₂
      show orbSum Ψ S (weyl * (diagUnits2 u₁ u₂ * k'')) = _ * orbSum Ψ S (weyl * k'')
      rw [← mul_assoc, weyl_mul_diagUnits2, mul_assoc, hL1 u₂ u₁ _ hu₂ hu₁, mul_comm ((χ 2 u₂ : ℂˣ) : ℂ)]
    · intro x k'' _ _ _
      show orbSum Ψ S (weyl * (AutomorphicForm.unipotentGL2 x * k'')) = orbSum Ψ S (weyl * k'')
      rw [← mul_assoc, weyl_mul_unipotent, mul_assoc, hL2]
    · intro k'' u hu
      show orbSum Ψ S (weyl * (k'' * diagUnitGL2 u)) = orbSum Ψ S (weyl * k'')
      rw [← mul_assoc, hR1 _ u hu]
    · intro k'' t ht
      show orbSum Ψ S (weyl * (k'' * AutomorphicForm.unipotentGL2 t)) = orbSum Ψ S (weyl * k'')
      rw [← mul_assoc, hR2 _ t ht]
    · intro k'' t ht
      show orbSum Ψ S (weyl * (k'' * Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : v.adicCompletion ℚ), 0; t, 1]
        (by simp [Matrix.det_fin_two_of]))) = orbSum Ψ S (weyl * k'')
      rw [show Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : v.adicCompletion ℚ), 0; t, 1]
          (by simp [Matrix.det_fin_two_of]) = lowerU t from Units.ext rfl, ← mul_assoc, hR3 _ t ht]
  have hfin : orbSum Ψ S k = orbSum Ψ S (weyl * (weyl * k)) := by
    rw [← mul_assoc, weyl_mul_weyl, one_mul]
  change orbSum Ψ S k = 0
  rw [hfin]
  exact hF₁ _ (isInt_mul isInt_weyl ⟨hk, hkinv⟩)

end S_LanglandsTunnell_CubicInduction_sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level (solution)
