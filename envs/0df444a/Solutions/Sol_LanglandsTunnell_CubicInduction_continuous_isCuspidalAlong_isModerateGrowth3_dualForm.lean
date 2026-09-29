-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.continuous_isCuspidalAlong_isModerateGrowth3_dualForm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/c9ff89d6-ad46-5c8d-926b-3be30dc538d4

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_continuous_isCuspidalAlong_isModerateGrowth3_dualForm

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "transposeInv3 IsCuspidalAlongP21 IsCuspidalAlongP12 dualForm AdelicGL globalPointsGL centralScalarGL radicalP21 radicalP12 radicalP21_coe radicalP12_coe archComponentN componentAt3 archComponent3 archPlaceComponent3 matrixSize matrixSupSize archGauge3 finGauge3 gauge3 IsModerateGrowth3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section TransposeInverse

open Matrix

variable {A : Type*} [CommRing A]

private theorem transposeInv3_apply (k : GL (Fin 3) A) (i j : Fin 3) :
    ((transposeInv3 k : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) i j =
      ((k⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) j i :=
  rfl

private theorem transposeInv3_inv_apply (k : GL (Fin 3) A) (i j : Fin 3) :
    (((transposeInv3 k)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) i j = (k : Matrix (Fin 3) (Fin 3) A) j i :=
  rfl

private theorem transposeInv3_mul (a b : GL (Fin 3) A) :
    transposeInv3 (a * b) = transposeInv3 a * transposeInv3 b := by
  refine Units.ext ?_
  change (((a * b)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ =
    ((a⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ * ((b⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem map_transposeInv3 {B : Type*} [CommRing B] (f : A →+* B) (g : GL (Fin 3) A) :
    Matrix.GeneralLinearGroup.map f (transposeInv3 g) = transposeInv3 (Matrix.GeneralLinearGroup.map f g) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change f (((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) j i) =
    (((Matrix.GeneralLinearGroup.map f g)⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) j i
  rw [← Matrix.GeneralLinearGroup.map_inv]
  exact (Matrix.GeneralLinearGroup.map_apply f j i g⁻¹).symm

private theorem transposeInv3_scalar (z : Aˣ) :
    transposeInv3 (Matrix.GeneralLinearGroup.scalar (Fin 3) z) = Matrix.GeneralLinearGroup.scalar (Fin 3) z⁻¹ := by
  refine Units.ext ?_
  change (((Matrix.GeneralLinearGroup.scalar (Fin 3) z)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  rw [← _root_.map_inv]
  change (Matrix.scalar (Fin 3) ((z⁻¹ : Aˣ) : A))ᵀ = Matrix.scalar (Fin 3) ((z⁻¹ : Aˣ) : A)
  rw [Matrix.scalar_apply, Matrix.diagonal_transpose]

private def radicalSwap : GL (Fin 3) A where
  val := !![0, 0, -1; 1, 0, 0; 0, 1, 0]
  inv := !![0, 1, 0; 0, 0, 1; -1, 0, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem radicalSwap_coe :
    ((radicalSwap : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = !![0, 0, -1; 1, 0, 0; 0, 1, 0] :=
  rfl

private theorem radicalSwap_inv_coe :
    (((radicalSwap : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = !![0, 1, 0; 0, 0, 1; -1, 0, 0] :=
  rfl

private theorem map_radicalSwap {B : Type*} [CommRing B] (f : A →+* B) :
    Matrix.GeneralLinearGroup.map f (radicalSwap : GL (Fin 3) A) = (radicalSwap : GL (Fin 3) B) := by
  refine Units.ext ?_
  rw [radicalSwap_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [radicalSwap_coe]

private theorem transposeInv3_radicalP21_coe (v : Fin 2 → A) :
    ((transposeInv3 (radicalP21 v) : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1, 0, 0; 0, 1, 0; -(v 0), -(v 1), 1] := by
  have hinv : (((radicalP21 v : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1, 0, -(v 0); 0, 1, -(v 1); 0, 0, 1] := by
    rw [Matrix.coe_units_inv, radicalP21_coe]
    refine Matrix.inv_eq_left_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  change (((radicalP21 v : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

private theorem transposeInv3_radicalP12_coe (v : Fin 2 → A) :
    ((transposeInv3 (radicalP12 v) : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1, 0, 0; -(v 0), 1, 0; -(v 1), 0, 1] := by
  have hinv : (((radicalP12 v : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1, -(v 0), -(v 1); 0, 1, 0; 0, 0, 1] := by
    rw [Matrix.coe_units_inv, radicalP12_coe]
    refine Matrix.inv_eq_left_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  change (((radicalP12 v : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

private theorem radicalSwap_mul_transposeInv3_radicalP21 (v : Fin 2 → A) :
    (radicalSwap : GL (Fin 3) A) * transposeInv3 (radicalP21 v) = radicalP12 v * radicalSwap := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, transposeInv3_radicalP21_coe, radicalSwap_coe, radicalP12_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem radicalSwap_inv_mul_transposeInv3_radicalP12 (v : Fin 2 → A) :
    (radicalSwap : GL (Fin 3) A)⁻¹ * transposeInv3 (radicalP12 v) = radicalP21 v * radicalSwap⁻¹ := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, transposeInv3_radicalP12_coe, radicalSwap_inv_coe, radicalP21_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem matrixSize_transposeInv3 {L : Type*} [NormedField L] (k : GL (Fin 3) L) :
    matrixSize (transposeInv3 k) = matrixSize k := by
  unfold matrixSize
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [transposeInv3_apply, transposeInv3_inv_apply]
  exact add_comm _ _

private theorem sup_swap_eq {G : Fin 3 × Fin 3 → NNReal} :
    (Finset.univ.sup fun ij : Fin 3 × Fin 3 => G (ij.2, ij.1)) = Finset.univ.sup G :=
  le_antisymm (Finset.sup_le fun ij _ => Finset.le_sup (f := G) (Finset.mem_univ (ij.2, ij.1)))
    (Finset.sup_le fun ij _ =>
      Finset.le_sup (f := fun ij : Fin 3 × Fin 3 => G (ij.2, ij.1)) (Finset.mem_univ (ij.2, ij.1)))

private theorem matrixSupSize_transposeInv3 {L : Type*} [NormedField L] (k : GL (Fin 3) L) :
    matrixSupSize (transposeInv3 k) = matrixSupSize k := by
  unfold matrixSupSize
  rw [← sup_swap_eq (G := fun ij : Fin 3 × Fin 3 => max ‖(k : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊
    ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊)]
  refine Finset.sup_congr rfl fun ij _ => ?_
  rw [transposeInv3_apply, transposeInv3_inv_apply]
  exact max_comm _ _

end TransposeInverse

section Adelic

private theorem globalPointsGL_transposeInv3 (γ : GL (Fin 3) ℚ) :
    globalPointsGL 3 (𝓞 ℚ) ℚ (transposeInv3 γ) = transposeInv3 (globalPointsGL 3 (𝓞 ℚ) ℚ γ) :=
  map_transposeInv3 _ γ

private theorem globalPointsGL_radicalSwap :
    globalPointsGL 3 (𝓞 ℚ) ℚ (radicalSwap : GL (Fin 3) ℚ) = (radicalSwap : AdelicGL 3 (𝓞 ℚ) ℚ) :=
  map_radicalSwap _

private theorem globalPointsGL_radicalSwap_inv :
    globalPointsGL 3 (𝓞 ℚ) ℚ (radicalSwap : GL (Fin 3) ℚ)⁻¹ = (radicalSwap : AdelicGL 3 (𝓞 ℚ) ℚ)⁻¹ := by
  rw [map_inv, globalPointsGL_radicalSwap]

private theorem transposeInv3_centralScalarGL (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    transposeInv3 (centralScalarGL 3 (𝓞 ℚ) ℚ z) = centralScalarGL 3 (𝓞 ℚ) ℚ z⁻¹ :=
  transposeInv3_scalar z

private theorem archPlaceComponent3_transposeInv3 (w : InfinitePlace ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archPlaceComponent3 ℚ w (transposeInv3 g) = transposeInv3 (archPlaceComponent3 ℚ w g) := by
  simp only [archPlaceComponent3, MonoidHom.comp_apply, archComponent3, archComponentN, map_transposeInv3]

private theorem componentAt3_transposeInv3 (v : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    componentAt3 (𝓞 ℚ) ℚ v (transposeInv3 g) = transposeInv3 (componentAt3 (𝓞 ℚ) ℚ v g) :=
  map_transposeInv3 _ g

private theorem gauge3_transposeInv3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) : gauge3 ℚ (transposeInv3 g) = gauge3 ℚ g := by
  unfold gauge3 archGauge3 finGauge3
  simp only [archPlaceComponent3_transposeInv3, componentAt3_transposeInv3, matrixSize_transposeInv3,
    matrixSupSize_transposeInv3]

private theorem isCuspidalAlongP21_dualForm (pins : CarrierPins ℚ) {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), Φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = Φ g)
    (hP12 : IsCuspidalAlongP12 pins Φ) : IsCuspidalAlongP21 pins (dualForm Φ) := by
  intro g
  have hpt : ∀ x y : AdeleRing (𝓞 ℚ) ℚ, dualForm Φ (radicalP21 ![x, y] * g) =
      Φ (radicalP12 ![x, y] * (radicalSwap * transposeInv3 g)) := by
    intro x y
    simp only [dualForm]
    rw [transposeInv3_mul, ← haut radicalSwap (transposeInv3 (radicalP21 ![x, y]) * transposeInv3 g),
      globalPointsGL_radicalSwap, ← mul_assoc, radicalSwap_mul_transposeInv3_radicalP21, mul_assoc]
  simp only [hpt]
  exact hP12 (radicalSwap * transposeInv3 g)

private theorem isCuspidalAlongP12_dualForm (pins : CarrierPins ℚ) {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), Φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = Φ g)
    (hP21 : IsCuspidalAlongP21 pins Φ) : IsCuspidalAlongP12 pins (dualForm Φ) := by
  intro g
  have hpt : ∀ x y : AdeleRing (𝓞 ℚ) ℚ, dualForm Φ (radicalP12 ![x, y] * g) =
      Φ (radicalP21 ![x, y] * (radicalSwap⁻¹ * transposeInv3 g)) := by
    intro x y
    simp only [dualForm]
    rw [transposeInv3_mul, ← haut radicalSwap⁻¹ (transposeInv3 (radicalP12 ![x, y]) * transposeInv3 g),
      globalPointsGL_radicalSwap_inv, ← mul_assoc, radicalSwap_inv_mul_transposeInv3_radicalP12, mul_assoc]
  simp only [hpt]
  exact hP21 (radicalSwap⁻¹ * transposeInv3 g)

private theorem continuous_transposeInv3 :
    Continuous (transposeInv3 : AdelicGL 3 (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_coe_inv.matrix_transpose
  · exact Units.continuous_val.matrix_transpose

end Adelic

end LanglandsTunnell.CubicInduction

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_continuous_isCuspidalAlong_isModerateGrowth3_dualForm.LanglandsTunnell.CubicInduction in
theorem solution
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hc : Continuous Φ)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), Φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = Φ g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      Φ (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * Φ g)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) Φ)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) Φ)
    (hmg : IsModerateGrowth3 ℚ Φ) :
    Continuous (dualForm Φ) ∧
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), dualForm Φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = dualForm Φ g) ∧
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        dualForm Φ (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ)⁻¹ * dualForm Φ g) ∧
      IsCuspidalAlongP21 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) (dualForm Φ) ∧
      IsCuspidalAlongP12 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) (dualForm Φ) ∧
      IsModerateGrowth3 ℚ (dualForm Φ) := by
  refine ⟨hc.comp continuous_transposeInv3, ?_, ?_, isCuspidalAlongP21_dualForm _ haut hP12,
    isCuspidalAlongP12_dualForm _ haut hP21, ?_⟩
  · intro γ g
    simp only [dualForm]
    rw [transposeInv3_mul, ← globalPointsGL_transposeInv3, haut]
  · intro z g
    simp only [dualForm]
    rw [transposeInv3_mul, transposeInv3_centralScalarGL, hcen, map_inv, Units.val_inv_eq_inv_val]
  · unfold IsModerateGrowth3 at hmg ⊢
    obtain ⟨C, N, h⟩ := hmg
    refine ⟨C, N, fun g _ => ?_⟩
    calc ‖dualForm Φ g‖ = ‖Φ (transposeInv3 g)‖ := rfl
      _ ≤ C * gauge3 ℚ (transposeInv3 g) ^ N := h _ (Set.mem_univ _)
      _ = C * gauge3 ℚ g ^ N := by rw [gauge3_transposeInv3]

end S_LanglandsTunnell_CubicInduction_continuous_isCuspidalAlong_isModerateGrowth3_dualForm
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_continuous_isCuspidalAlong_isModerateGrowth3_dualForm (solution)
