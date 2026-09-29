-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_linearMap_apply_eq_zero_of_transposeInv3_radicalP21_of_mem_principalSeries3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e128af57-51a1-5bb6-983b-64295bedc446

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_transposeInv3_radicalP21_of_mem_principalSeries3
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.principalSeries3 CubicInduction.rightTranslate_mem_principalSeries3 CubicInduction.gl3AmbientRightTranslate CubicInduction.transposeInv3 CubicInduction.upperUnipotent3 CubicInduction.radicalP21 CubicInduction.iotaGL CubicInduction.LocalGL3 TateLocal.higherUnitsAt CubicInduction.diagUnitGL2 CubicInduction.lowerUnipotent21 CubicInduction.transposeInv3_lowerUnipotent21 CubicInduction.exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_coe halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff rightTranslate_mem_principalSeries3 gl3AmbientRightTranslate gl3AmbientRightTranslate_apply transposeInv3 upperUnipotent3 upperUnipotent3_coe radicalP21 embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply transposeInv3_lowerUnipotent21 exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3"
namespace OppositeRadical
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

p2m_open "Matrix LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_transposeInv3_radicalP21_of_mem_principalSeries3.LanglandsTunnell.CubicInduction"

section MatrixIdentities

variable {A : Type*} [CommRing A]

theorem transposeInv3_mul (g h : GL (Fin 3) A) : transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  change (((g * h)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ =
    ((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ * ((h⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem transposeInv3_transposeInv3 (g : GL (Fin 3) A) : transposeInv3 (transposeInv3 g) = g := by
  refine Units.ext ?_
  change ((((transposeInv3 g)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ = _
  change (((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ)ᵀ = _
  rw [Matrix.transpose_transpose]

theorem transposeInv3_longWeyl3 : transposeInv3 (longWeyl3 : GL (Fin 3) A) = longWeyl3 := by
  refine Units.ext ?_
  change (((longWeyl3 : GL (Fin 3) A)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  change ((longWeyl3 : GL (Fin 3) A).inv)ᵀ = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [longWeyl3]

theorem longWeyl3_mul_longWeyl3 : (longWeyl3 : GL (Fin 3) A) * longWeyl3 = 1 := by
  refine Units.ext ?_
  rw [Units.val_mul, longWeyl3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem longWeyl3_mul_transposeInv3_upperUnipotent3 (x y z : A) :
    (longWeyl3 : GL (Fin 3) A) * transposeInv3 (upperUnipotent3 x y z) =
      upperUnipotent3 (-y) (-x) (x * y - z) * longWeyl3 := by
  refine Units.ext ?_
  have hinv : (((upperUnipotent3 x y z)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] := rfl
  change (longWeyl3 : GL (Fin 3) A).val * (((upperUnipotent3 x y z)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  rw [hinv, Units.val_mul, longWeyl3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem transposeInv3_upperUnipotent3_zero_zero (s : A) :
    transposeInv3 (upperUnipotent3 s 0 0) = lowerUnipotent21 (-s) := by
  have h := congrArg transposeInv3 (transposeInv3_lowerUnipotent21 (-s))
  rw [transposeInv3_transposeInv3, neg_neg] at h
  exact h.symm

theorem transposeInv3_iotaGL_diagUnitGL2 (u : Aˣ) :
    transposeInv3 (iotaGL (diagUnitGL2 u)) = iotaGL (diagUnitGL2 u⁻¹) := by
  refine Units.ext ?_
  change (((iotaGL (diagUnitGL2 u))⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  rw [← map_inv, coe_iotaGL, coe_iotaGL]
  have hinv : (((diagUnitGL2 u)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![((u⁻¹ : Aˣ) : A), 0; 0, 1] := rfl
  rw [hinv, coe_diagUnitGL2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2]

end MatrixIdentities

section Involution

variable {v : HeightOneSpectrum (𝓞 ℚ)}

noncomputable def revInv (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ) :=
  fun i => (χ (Fin.rev i))⁻¹

theorem revInv_apply (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (i : Fin 3) (u : (v.adicCompletion ℚ)ˣ) :
    revInv χ i u = (χ (Fin.rev i) u)⁻¹ := rfl

theorem revInv_revInv (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) : revInv (revInv χ) = χ := by
  funext i
  refine MonoidHom.ext fun u => ?_
  rw [revInv_apply, revInv_apply, Fin.rev_rev, inv_inv]

theorem continuous_transposeInv3 : Continuous (transposeInv3 : LocalGL3 v → LocalGL3 v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · change Continuous fun g : LocalGL3 v => (((g⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))ᵀ
    exact Units.continuous_coe_inv.matrix_transpose
  · change Continuous fun g : LocalGL3 v => (((g : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))ᵀ
    exact Units.continuous_val.matrix_transpose

theorem longWeyl3_mul_transposeInv3_diagonal3 (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    (longWeyl3 : LocalGL3 v) * transposeInv3 (diagonal3 v a) =
      diagonal3 v (fun i => (a (Fin.rev i))⁻¹) * longWeyl3 := by
  refine Units.ext ?_
  have hinv : (((diagonal3 v a)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal fun i => (((a i)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) := rfl
  change (longWeyl3 : LocalGL3 v).val * (((diagonal3 v a)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ᵀ = _
  rw [hinv, Matrix.diagonal_transpose, Units.val_mul, diagonal3_coe, longWeyl3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal]

theorem torusChar3_revInv (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    torusChar3 v χ (fun i => (a (Fin.rev i))⁻¹) = torusChar3 v (revInv χ) a := by
  simp only [torusChar3, Fin.prod_univ_three, revInv_apply, map_inv]
  simp only [Fin.rev, Units.val_inv_eq_inv_val]
  simp only [show ((3 : ℕ) - (↑(0 : Fin 3) + 1) : ℕ) = 2 from rfl, show ((3 : ℕ) - (↑(2 : Fin 3) + 1) : ℕ) = 0 from rfl,
    show ((3 : ℕ) - (↑(1 : Fin 3) + 1) : ℕ) = 1 from rfl]
  change ((χ 0 (a 2) : ℂˣ) : ℂ)⁻¹ * ((χ 1 (a 1) : ℂˣ) : ℂ)⁻¹ * ((χ 2 (a 0) : ℂˣ) : ℂ)⁻¹ =
    ((χ 2 (a 0) : ℂˣ) : ℂ)⁻¹ * ((χ 1 (a 1) : ℂˣ) : ℂ)⁻¹ * ((χ 0 (a 2) : ℂˣ) : ℂ)⁻¹
  ring

theorem halfModulus3_revInv (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    halfModulus3 v (fun i => (a (Fin.rev i))⁻¹) = halfModulus3 v a := by
  have h0 : ‖((a 0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖ ≠ 0 := norm_ne_zero_iff.mpr (a 0).ne_zero
  have h2 : ‖((a 2 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖ ≠ 0 := norm_ne_zero_iff.mpr (a 2).ne_zero
  simp only [halfModulus3]
  congr 1
  simp only [Fin.rev, Units.val_inv_eq_inv_val, norm_inv]
  simp only [show ((3 : ℕ) - (↑(0 : Fin 3) + 1) : ℕ) = 2 from rfl, show ((3 : ℕ) - (↑(2 : Fin 3) + 1) : ℕ) = 0 from rfl]
  change ‖((a 2 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖⁻¹ / ‖((a 0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖⁻¹ = _
  field_simp

theorem dualWhittakerFn3_mem_principalSeries3 {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    {Φ : LocalGL3 v → ℂ} (hΦ : Φ ∈ principalSeries3 v χ) :
    dualWhittakerFn3 Φ ∈ principalSeries3 v (revInv χ) := by
  obtain ⟨hlc, hn, ht⟩ := mem_principalSeries3_iff.mp hΦ
  refine mem_principalSeries3_iff.mpr ⟨?_, fun x y z g => ?_, fun a g => ?_⟩
  · exact hlc.comp_continuous (continuous_const.mul continuous_transposeInv3)
  · show Φ (longWeyl3 * transposeInv3 (upperUnipotent3 x y z * g)) = Φ (longWeyl3 * transposeInv3 g)
    rw [transposeInv3_mul, ← mul_assoc, longWeyl3_mul_transposeInv3_upperUnipotent3, mul_assoc, hn]
  · show Φ (longWeyl3 * transposeInv3 (diagonal3 v a * g)) = _ * Φ (longWeyl3 * transposeInv3 g)
    rw [transposeInv3_mul, ← mul_assoc, longWeyl3_mul_transposeInv3_diagonal3, mul_assoc, ht,
      torusChar3_revInv, halfModulus3_revInv]

theorem dualWhittakerFn3_dualWhittakerFn3 (Φ : LocalGL3 v → ℂ) : dualWhittakerFn3 (dualWhittakerFn3 Φ) = Φ := by
  funext g
  simp only [dualWhittakerFn3_apply, transposeInv3_mul, transposeInv3_longWeyl3, transposeInv3_transposeInv3,
    ← mul_assoc, longWeyl3_mul_longWeyl3, one_mul]

theorem dualWhittakerFn3_gl3AmbientRightTranslate (g : LocalGL3 v) (Φ : LocalGL3 v → ℂ) :
    dualWhittakerFn3 (gl3AmbientRightTranslate (R := ℂ) g Φ) =
      gl3AmbientRightTranslate (R := ℂ) (transposeInv3 g) (dualWhittakerFn3 Φ) := by
  funext x
  simp only [dualWhittakerFn3_apply, gl3AmbientRightTranslate_apply, transposeInv3_mul,
    transposeInv3_transposeInv3, mul_assoc]

noncomputable def toOrig (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    ↥(principalSeries3 v (revInv χ)) →ₗ[ℂ] ↥(principalSeries3 v χ) where
  toFun G := ⟨dualWhittakerFn3 (G : LocalGL3 v → ℂ), by
    have h := dualWhittakerFn3_mem_principalSeries3 G.2
    rwa [revInv_revInv] at h⟩
  map_add' G G' := by
    refine Subtype.ext (funext fun x => ?_)
    rfl
  map_smul' c G := by
    refine Subtype.ext (funext fun x => ?_)
    rfl

@[scoped simp] theorem coe_toOrig (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (G : ↥(principalSeries3 v (revInv χ))) :
    (toOrig χ G : LocalGL3 v → ℂ) = dualWhittakerFn3 (G : LocalGL3 v → ℂ) := rfl

end Involution

end LanglandsTunnell.CubicInduction.OppositeRadical
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_transposeInv3_radicalP21_of_mem_principalSeries3.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_transposeInv3_radicalP21_of_mem_principalSeries3.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_transposeInv3_radicalP21_of_mem_principalSeries3.LanglandsTunnell.CubicInduction.OppositeRadical"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_transposeInv3_radicalP21_of_mem_principalSeries3.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_transposeInv3_radicalP21_of_mem_principalSeries3.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_transposeInv3_radicalP21_of_mem_principalSeries3.LanglandsTunnell"

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_transposeInv3_radicalP21_of_mem_principalSeries3.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.OppositeRadical in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (b : ℕ)
    (hχ : ∀ i, ∃ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v b, χ i u ≠ 1)
    (Φ : LanglandsTunnell.CubicInduction.LocalGL3 v → ℂ)
    (hΦ : Φ ∈ LanglandsTunnell.CubicInduction.principalSeries3 v χ)
    (hdiag : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v (u : v.adicCompletion ℚ) = 1 →
      Φ (g * LanglandsTunnell.CubicInduction.iotaGL (LanglandsTunnell.CubicInduction.diagUnitGL2 u)) = Φ g)
    (hupper : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Φ (g * LanglandsTunnell.CubicInduction.upperUnipotent3 s 0 0) = Φ g)
    (hlower : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Φ (g * LanglandsTunnell.CubicInduction.lowerUnipotent21 s) = Φ g) :
    ∃ c : ℕ, ∀ Λ : ↥(LanglandsTunnell.CubicInduction.principalSeries3 v χ) →ₗ[ℂ] ℂ,
      (∀ (F : ↥(LanglandsTunnell.CubicInduction.principalSeries3 v χ)) (Y : Fin 2 → v.adicCompletion ℚ),
        (∀ i, Valued.v (Y i) ≤ WithZero.exp (c : ℤ)) →
        Λ ⟨LanglandsTunnell.CubicInduction.gl3AmbientRightTranslate (R := ℂ)
              (LanglandsTunnell.CubicInduction.transposeInv3
                (LanglandsTunnell.CubicInduction.radicalP21 Y)) F,
            LanglandsTunnell.CubicInduction.rightTranslate_mem_principalSeries3 F.2 _⟩ = Λ F) →
      Λ ⟨Φ, hΦ⟩ = 0 := by

  set Ψ : LocalGL3 v → ℂ := dualWhittakerFn3 Φ with hΨdef
  have hΨ : Ψ ∈ principalSeries3 v (revInv χ) := dualWhittakerFn3_mem_principalSeries3 hΦ
  have hΨapply : ∀ g : LocalGL3 v, Ψ g = Φ (longWeyl3 * transposeInv3 g) := fun g => rfl

  have hχ' : ∀ i, ∃ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v b, revInv χ i u ≠ 1 := fun i => by
    obtain ⟨u, hu, hne⟩ := hχ (Fin.rev i)
    exact ⟨u, hu, by rwa [revInv_apply, Ne, inv_eq_one]⟩
  have hdiag' : ∀ (g : LocalGL3 v) (u : (v.adicCompletion ℚ)ˣ), Valued.v (u : v.adicCompletion ℚ) = 1 →
      Ψ (g * iotaGL (diagUnitGL2 u)) = Ψ g := fun g u hu => by
    have hu' : Valued.v ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
    rw [hΨapply, hΨapply, transposeInv3_mul, transposeInv3_iotaGL_diagUnitGL2, ← mul_assoc, hdiag _ _ hu']
  have hupper' : ∀ (g : LocalGL3 v) (s : v.adicCompletion ℚ), Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Ψ (g * upperUnipotent3 s 0 0) = Ψ g := fun g s hs => by
    have hs' : Valued.v (-s) ≤ WithZero.exp (-(b : ℤ)) := by rwa [Valuation.map_neg]
    rw [hΨapply, hΨapply, transposeInv3_mul, transposeInv3_upperUnipotent3_zero_zero, ← mul_assoc, hlower _ _ hs']
  have hlower' : ∀ (g : LocalGL3 v) (s : v.adicCompletion ℚ), Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Ψ (g * lowerUnipotent21 s) = Ψ g := fun g s hs => by
    have hs' : Valued.v (-s) ≤ WithZero.exp (-(b : ℤ)) := by rwa [Valuation.map_neg]
    rw [hΨapply, hΨapply, transposeInv3_mul, LanglandsTunnell.CubicInduction.transposeInv3_lowerUnipotent21,
      ← mul_assoc, hupper _ _ hs']
  obtain ⟨c, hc⟩ :=
    LanglandsTunnell.CubicInduction.exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3
      v (revInv χ) b hχ' Ψ hΨ hdiag' hupper' hlower'
  refine ⟨c, fun Λ hΛ => ?_⟩

  have h := hc (Λ ∘ₗ toOrig χ) ?_
  ·
    have hback : toOrig χ ⟨Ψ, hΨ⟩ = ⟨Φ, hΦ⟩ :=
      Subtype.ext (by rw [coe_toOrig]; exact dualWhittakerFn3_dualWhittakerFn3 Φ)
    rw [LinearMap.comp_apply, hback] at h
    exact h
  · intro G Y hY
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    have hG : toOrig χ ⟨gl3AmbientRightTranslate (R := ℂ) (radicalP21 Y) G, rightTranslate_mem_principalSeries3 G.2 _⟩
        = ⟨gl3AmbientRightTranslate (R := ℂ) (transposeInv3 (radicalP21 Y)) (toOrig χ G),
            rightTranslate_mem_principalSeries3 (toOrig χ G).2 _⟩ :=
      Subtype.ext (by
        rw [coe_toOrig]
        exact dualWhittakerFn3_gl3AmbientRightTranslate (radicalP21 Y) G)
    rw [hG]
    exact hΛ (toOrig χ G) Y hY

end S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_transposeInv3_radicalP21_of_mem_principalSeries3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_transposeInv3_radicalP21_of_mem_principalSeries3 (solution)
