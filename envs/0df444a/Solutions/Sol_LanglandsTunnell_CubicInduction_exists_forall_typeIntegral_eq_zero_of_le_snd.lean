-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_typeIntegral_eq_zero_of_le_snd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/87eea6a5-7bcc-5f14-970f-213737573f37

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_linearMap_apply_eq_zero_of_transposeInv3_radicalP21_of_mem_principalSeries3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_snd
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.HasConductorExponentAt CubicInduction.exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 TateLocal.psiLocal_eq_one_of_mem_integers CubicInduction.exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3 CubicInduction.exists_forall_linearMap_apply_eq_zero_of_transposeInv3_radicalP21_of_mem_principalSeries3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "principalSeries3 rightTranslate_mem_principalSeries3 coefficientFn IsWhittakerFunctional3 gl3Entry continuous_gl3Entry gl3AmbientRightTranslate transposeInv3 upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP21_coe embedMat2 iotaGL coe_iotaGL iotaGL_unipotentGL2 LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3 exists_forall_linearMap_apply_eq_zero_of_transposeInv3_radicalP21_of_mem_principalSeries3"
namespace TypeIntegralSnd
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_le_exp LanglandsTunnell"

open Matrix

section MatrixIdentities

variable {A : Type*} [CommRing A]

theorem iotaGL_mul_radicalP21 (h : GL (Fin 2) A) (Y : Fin 2 → A) :
    iotaGL h * radicalP21 Y = radicalP21 ((h : Matrix (Fin 2) (Fin 2) A) *ᵥ Y) * iotaGL h := by
  refine Units.ext ?_
  ext i j
  simp only [Units.val_mul, coe_iotaGL, radicalP21_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

theorem radicalP21_eq (Y : Fin 2 → A) : radicalP21 Y = upperUnipotent3 0 (Y 1) (Y 0) := rfl

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

theorem transposeInv3_iotaGL (h : GL (Fin 2) A) :
    transposeInv3 (iotaGL h) = iotaGL (AutomorphicForm.transposeInvN (Fin 2) h) := by
  refine Units.ext ?_
  change (((iotaGL h)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  rw [← map_inv, coe_iotaGL, coe_iotaGL, AutomorphicForm.coe_transposeInvN]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2]

theorem longWeyl3_mul_transposeInv3_radicalP21 (Y : Fin 2 → A) :
    (longWeyl3 : GL (Fin 3) A) * transposeInv3 (radicalP21 Y) =
      upperUnipotent3 (-Y 1) 0 (-Y 0) * longWeyl3 := by
  refine Units.ext ?_
  have hinv : (((radicalP21 Y)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) = !![1, 0, -Y 0; 0, 1, -Y 1; 0, 0, 1] := by
    change ((upperUnipotent3 (0 : A) (Y 1) (Y 0))⁻¹ : GL (Fin 3) A).val = _
    change (upperUnipotent3 (0 : A) (Y 1) (Y 0)).inv = _
    simp [upperUnipotent3]
  change (longWeyl3 : GL (Fin 3) A).val * (((radicalP21 Y)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ = _
  rw [hinv, Units.val_mul, longWeyl3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem mul_apply_one_of_apply_one_zero (t k : Matrix (Fin 2) (Fin 2) A) (h : t 1 0 = 0) (j : Fin 2) :
    (t * k) 1 j = t 1 1 * k 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, h]

end MatrixIdentities

section Torus

variable {K : Type*} [Field K]

theorem scalarPi_eq_scalar (π : K) (hπ : π ≠ 0) :
    UnramifiedWhittaker.scalarPi π hπ = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 π hπ) := by
  refine Units.ext ?_
  ext i j
  change (!![π, 0; 0, π] : Matrix (Fin 2) (Fin 2) K) i j = _
  rw [Matrix.GeneralLinearGroup.scalar, Units.coe_map]
  change _ = (Matrix.scalar (Fin 2) ((Units.mk0 π hπ : Kˣ) : K)) i j
  rw [Matrix.scalar_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem coe_scalarPi_zpow (π : K) (hπ : π ≠ 0) (n : ℤ) :
    ((UnramifiedWhittaker.scalarPi π hπ ^ n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal fun _ => π ^ n := by
  rw [scalarPi_eq_scalar, ← map_zpow, Matrix.GeneralLinearGroup.scalar, Units.coe_map]
  change Matrix.scalar (Fin 2) (((Units.mk0 π hπ ^ n : Kˣ)) : K) = _
  rw [Matrix.scalar_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0]

theorem torus_apply_one (π : K) (hπ : π ≠ 0) (n₂ : ℤ) (x : Kˣ) (j : Fin 2) :
    ((UnramifiedWhittaker.scalarPi π hπ ^ n₂ * diagUnitGL2 x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 j =
      if j = 1 then π ^ n₂ else 0 := by
  rw [Units.val_mul, coe_scalarPi_zpow, coe_diagUnitGL2, Matrix.diagonal_mul]
  fin_cases j <;> simp

end Torus

end LanglandsTunnell.CubicInduction.TypeIntegralSnd

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.HasConductorExponentAt CubicInduction.exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 TateLocal.psiLocal_eq_one_of_mem_integers CubicInduction.exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3 CubicInduction.exists_forall_linearMap_apply_eq_zero_of_transposeInv3_radicalP21_of_mem_principalSeries3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "principalSeries3 rightTranslate_mem_principalSeries3 coefficientFn IsWhittakerFunctional3 gl3Entry continuous_gl3Entry gl3AmbientRightTranslate transposeInv3 upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP21_coe embedMat2 iotaGL coe_iotaGL iotaGL_unipotentGL2 LocalGL3 diagUnitGL2 coe_diagUnitGL2 lowerUnipotent21 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3 exists_forall_linearMap_apply_eq_zero_of_transposeInv3_radicalP21_of_mem_principalSeries3"
namespace TypeIntegralSnd
p2m_open "LanglandsTunnell.CubicInduction~exists_valued_le_exp LanglandsTunnell"

open Matrix

section PS

variable {v : HeightOneSpectrum (𝓞 ℚ)} {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}

noncomputable def Rsub (g : LocalGL3 v) : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ) :=
  (gl3AmbientRightTranslate (R := ℂ) g).restrict fun _ hF => rightTranslate_mem_principalSeries3 hF g

theorem Rsub_apply (g : LocalGL3 v) (F : ↥(principalSeries3 v χ)) :
    Rsub g F = ⟨gl3AmbientRightTranslate (R := ℂ) g F, rightTranslate_mem_principalSeries3 F.2 g⟩ := rfl

@[scoped simp] theorem coe_Rsub_apply (g : LocalGL3 v) (F : ↥(principalSeries3 v χ)) (x : LocalGL3 v) :
    (Rsub g F : LocalGL3 v → ℂ) x = (F : LocalGL3 v → ℂ) (x * g) := rfl

theorem Rsub_mul (g h : LocalGL3 v) (F : ↥(principalSeries3 v χ)) : Rsub (g * h) F = Rsub g (Rsub h F) :=
  Subtype.ext (funext fun x => by simp [mul_assoc])

theorem Rsub_one (F : ↥(principalSeries3 v χ)) : Rsub 1 F = F :=
  Subtype.ext (funext fun x => by simp)

theorem Rsub_injective (g : LocalGL3 v) : Function.Injective (Rsub (χ := χ) g) := by
  intro F G h
  have h' := congrArg (Rsub g⁻¹) h
  rwa [← Rsub_mul, ← Rsub_mul, inv_mul_cancel, Rsub_one, Rsub_one] at h'

theorem coefficientFn_eq (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 v χ)) (g : LocalGL3 v) :
    coefficientFn Λ f g = Λ (Rsub g f) := rfl

theorem whittaker_Rsub {ψ : AddChar (v.adicCompletion ℚ) ℂ} {Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ}
    (hΛ : IsWhittakerFunctional3 ψ Λ) (x y z : v.adicCompletion ℚ) (F : ↥(principalSeries3 v χ)) :
    Λ (Rsub (upperUnipotent3 x y z) F) = ψ (x + y) * Λ F :=
  hΛ x y z F

theorem apply_Rsub_iotaGL_Rsub_radicalP21 {ψ : AddChar (v.adicCompletion ℚ) ℂ}
    {Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ} (hΛ : IsWhittakerFunctional3 ψ Λ)
    (h : GL (Fin 2) (v.adicCompletion ℚ)) (Y : Fin 2 → v.adicCompletion ℚ) (F : ↥(principalSeries3 v χ)) :
    Λ (Rsub (iotaGL h) (Rsub (radicalP21 Y) F)) =
      ψ (((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *ᵥ Y) 1) * Λ (Rsub (iotaGL h) F) := by
  rw [← Rsub_mul, iotaGL_mul_radicalP21, Rsub_mul, radicalP21_eq, whittaker_Rsub hΛ, zero_add]

theorem apply_Rsub_longWeyl3_iotaGL_Rsub_transposeInv3_radicalP21 {ψ : AddChar (v.adicCompletion ℚ) ℂ}
    {Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ} (hΛ : IsWhittakerFunctional3 ψ Λ)
    (h : GL (Fin 2) (v.adicCompletion ℚ)) (Y : Fin 2 → v.adicCompletion ℚ) (F : ↥(principalSeries3 v χ)) :
    Λ (Rsub (longWeyl3 * iotaGL h) (Rsub (transposeInv3 (radicalP21 Y)) F)) =
      ψ (-(((AutomorphicForm.transposeInvN (Fin 2) h : GL (Fin 2) (v.adicCompletion ℚ)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *ᵥ Y) 1) * Λ (Rsub (longWeyl3 * iotaGL h) F) := by
  have hι : iotaGL h = transposeInv3 (iotaGL (AutomorphicForm.transposeInvN (Fin 2) h)) := by
    rw [transposeInv3_iotaGL, AutomorphicForm.transposeInvN_transposeInvN]
  have hcomm : iotaGL h * transposeInv3 (radicalP21 Y) =
      transposeInv3 (radicalP21 (((AutomorphicForm.transposeInvN (Fin 2) h : GL (Fin 2) (v.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *ᵥ Y)) * iotaGL h := by
    conv_lhs => rw [hι, ← transposeInv3_mul, iotaGL_mul_radicalP21, transposeInv3_mul, ← hι]
  rw [← Rsub_mul, mul_assoc, hcomm, ← mul_assoc, longWeyl3_mul_transposeInv3_radicalP21, mul_assoc, Rsub_mul,
    whittaker_Rsub hΛ, add_zero]

def congr3 (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) : Set (LocalGL3 v) :=
  {k | ∀ i j : Fin 3, Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
    ≤ WithZero.exp (-(n : ℤ))}

theorem congr3_mem_nhds_one (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) : congr3 v n ∈ nhds (1 : LocalGL3 v) := by
  have hopen : IsOpen (congr3 v n) := by
    have : congr3 v n = ⋂ i : Fin 3, ⋂ j : Fin 3,
        (fun k : LocalGL3 v => gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ⁻¹'
          {y | Valued.v y ≤ WithZero.exp (-(n : ℤ))} := by
      ext k
      simp [congr3]
    rw [this]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    obtain ⟨t, ht, hvt⟩ := NumberField.AdelicLevel.exists_valued_eq_exp_neg (K := ℚ) v n
    rw [← hvt]
    exact (NumberField.AdelicLevel.isOpen_setOf_valued_le v t ht).preimage
      ((continuous_gl3Entry v i j).sub continuous_const)
  refine hopen.mem_nhds ?_
  intro i j
  simp [gl3Entry]

def stab {G : Type*} [Group G] {Z : Type*} (f : G → Z) : Subgroup G where
  carrier := {u | ∀ g : G, f (g * u) = f g}
  one_mem' g := by rw [mul_one]
  mul_mem' {a b} ha hb g := by rw [← mul_assoc, hb, ha]
  inv_mem' {a} ha g := by
    have h := ha (g * a⁻¹)
    rw [inv_mul_cancel_right] at h
    exact h.symm

theorem mem_stab_iff {G : Type*} [Group G] {Z : Type*} {f : G → Z} {u : G} :
    u ∈ stab f ↔ ∀ g : G, f (g * u) = f g :=
  Iff.rfl

theorem Rsub_eq_self_of_mem_stab {u : LocalGL3 v} {F : ↥(principalSeries3 v χ)}
    (hu : u ∈ stab (F : LocalGL3 v → ℂ)) : Rsub u F = F :=
  Subtype.ext (funext fun x => hu x)

end PS

section Stab

variable {v : HeightOneSpectrum (𝓞 ℚ)} {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}

theorem isOpen_stab (F : ↥(principalSeries3 v χ)) : IsOpen (stab (F : LocalGL3 v → ℂ) : Set (LocalGL3 v)) := by
  obtain ⟨n, hn⟩ :=
    LanglandsTunnell.CubicInduction.exists_forall_gl3AmbientRightTranslate_eq_of_mem_principalSeries3 v χ F F.2
  refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (congr3_mem_nhds_one v n) fun k hk g => ?_)
  have h := hn k hk
  exact congrFun h g

theorem isOpen_comap_iotaGL_stab (F : ↥(principalSeries3 v χ)) :
    IsOpen ((stab (F : LocalGL3 v → ℂ)).comap
      (iotaGL : GL (Fin 2) (v.adicCompletion ℚ) →* LocalGL3 v) : Set (GL (Fin 2) (v.adicCompletion ℚ))) :=
  (isOpen_stab F).preimage continuous_iotaGL
where

  continuous_iotaGL : Continuous (iotaGL : GL (Fin 2) (v.adicCompletion ℚ) → LocalGL3 v) := by
    have hc : ∀ a b : Fin 2, Continuous fun h : GL (Fin 2) (v.adicCompletion ℚ) =>
        ((h : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) a b :=
      fun a b => Units.continuous_val.matrix_elem a b
    have hc' : ∀ a b : Fin 2, Continuous fun h : GL (Fin 2) (v.adicCompletion ℚ) =>
        ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) a b :=
      fun a b => Units.continuous_coe_inv.matrix_elem a b
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · refine continuous_matrix fun i j => ?_
      show Continuous fun h : GL (Fin 2) (v.adicCompletion ℚ) =>
        embedMat2 ((h : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j
      fin_cases i <;> fin_cases j <;> simp [embedMat2, hc, continuous_const]
    · refine continuous_matrix fun i j => ?_
      show Continuous fun h : GL (Fin 2) (v.adicCompletion ℚ) =>
        embedMat2 ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j
      fin_cases i <;> fin_cases j <;> simp [embedMat2, hc', continuous_const, -Matrix.coe_units_inv]

end Stab

section Level

variable (v : HeightOneSpectrum (𝓞 ℚ)) (b : ℕ)

theorem idealBound_pow :
    NumberField.AdelicLevel.idealBound (𝓞 ℚ) (v.asIdeal ^ b) v = WithZero.exp (-(b : ℤ)) := by
  rw [NumberField.AdelicLevel.idealBound_of_ne_bot (pow_ne_zero _ v.ne_bot), Associates.mk_pow,
    Associates.count_pow (Associates.mk_ne_zero.mpr v.ne_bot) (Associates.irreducible_mk.mpr v.irreducible),
    Associates.count_self (Associates.irreducible_mk.mpr v.irreducible), mul_one]

def lowerUnipotentGL2 {A : Type*} [CommRing A] (s : A) : GL (Fin 2) A where
  val := !![1, 0; s, 1]
  inv := !![1, 0; -s, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem iotaGL_lowerUnipotentGL2 {A : Type*} [CommRing A] (s : A) :
    iotaGL (lowerUnipotentGL2 s) = lowerUnipotent21 s := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, lowerUnipotentGL2]

variable {v b}

private theorem isLocalLevelOne_of (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hint : ∀ i j, Valued.v (m i j) ≤ 1) (h10 : Valued.v (m 1 0) ≤ WithZero.exp (-(b : ℤ)))
    (h11 : Valued.v (m 1 1 - 1) ≤ WithZero.exp (-(b : ℤ))) :
    AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) m := by
  refine ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr (hint i j), ?_, ?_⟩
  · rw [idealBound_pow]; exact h10
  · rw [idealBound_pow]; exact h11

theorem diagUnitGL2_mem_localLevelOne (u : (v.adicCompletion ℚ)ˣ) (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    diagUnitGL2 u ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) := by
  have hu' : (Valued.v (u : v.adicCompletion ℚ))⁻¹ ≤ 1 := by
    rw [hu, inv_one]
  rw [AdelicDock.mem_localLevelOne_iff]
  refine ⟨isLocalLevelOne_of _ ?_ ?_ ?_, isLocalLevelOne_of _ ?_ ?_ ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [hu.le]
  · simp
  · simp
  · intro i j
    change Valued.v ((diagUnitGL2 u).inv i j) ≤ 1
    fin_cases i <;> fin_cases j <;> simp [diagUnitGL2, hu']
  · change Valued.v ((diagUnitGL2 u).inv 1 0) ≤ _
    simp [diagUnitGL2]
  · change Valued.v ((diagUnitGL2 u).inv 1 1 - 1) ≤ _
    simp [diagUnitGL2]

theorem unipotentGL2_mem_localLevelOne (s : v.adicCompletion ℚ) (hs : Valued.v s ≤ 1) :
    AutomorphicForm.unipotentGL2 s ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) := by
  have hs' : Valued.v (-s) ≤ 1 := by rwa [Valuation.map_neg]
  have hval : ((AutomorphicForm.unipotentGL2 s : GL (Fin 2) (v.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![1, s; 0, 1] := rfl
  have hinv : (((AutomorphicForm.unipotentGL2 s)⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![1, -s; 0, 1] := rfl
  rw [AdelicDock.mem_localLevelOne_iff, hinv, hval]
  refine ⟨isLocalLevelOne_of _ ?_ ?_ ?_, isLocalLevelOne_of _ ?_ ?_ ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [hs]
  · simp
  · simp
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [hs]
  · simp
  · simp

theorem lowerUnipotentGL2_mem_localLevelOne (s : v.adicCompletion ℚ) (hs : Valued.v s ≤ WithZero.exp (-(b : ℤ))) :
    lowerUnipotentGL2 s ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) := by
  have hs1 : Valued.v s ≤ 1 := hs.trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have hs' : Valued.v (-s) ≤ WithZero.exp (-(b : ℤ)) := by rwa [Valuation.map_neg]
  have hs1' : Valued.v (-s) ≤ 1 := by rwa [Valuation.map_neg]
  rw [AdelicDock.mem_localLevelOne_iff]
  refine ⟨isLocalLevelOne_of _ ?_ ?_ ?_, isLocalLevelOne_of _ ?_ ?_ ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [lowerUnipotentGL2, hs1]
  · simpa [lowerUnipotentGL2] using hs
  · simp [lowerUnipotentGL2]
  · intro i j
    change Valued.v ((lowerUnipotentGL2 s).inv i j) ≤ 1
    fin_cases i <;> fin_cases j <;> simp [lowerUnipotentGL2, hs1]
  · change Valued.v ((lowerUnipotentGL2 s).inv 1 0) ≤ _
    simpa [lowerUnipotentGL2] using hs'
  · change Valued.v ((lowerUnipotentGL2 s).inv 1 1 - 1) ≤ _
    simp [lowerUnipotentGL2]

end Level

section Average

open MeasureTheory

theorem setIntegral_apply_eq_apply_sum {X : Type*} [MeasurableSpace X] {V : Type*} [AddCommGroup V]
    [Module ℂ V] (μ : Measure X) {S : Set X} (F : X → V) (T : Finset V) (hT : ∀ x ∈ S, F x ∈ T)
    (hmeas : ∀ w ∈ T, MeasurableSet (S ∩ F ⁻¹' {w})) (hfin : ∀ w ∈ T, μ (S ∩ F ⁻¹' {w}) ≠ ⊤)
    (L : V →ₗ[ℂ] ℂ) :
    ∫ x in S, L (F x) ∂μ = L (∑ w ∈ T, ((μ (S ∩ F ⁻¹' {w})).toReal : ℂ) • w) := by
  have hS : (⋃ w ∈ T, (S ∩ F ⁻¹' {w})) = S := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, exists_prop]
    constructor
    · rintro ⟨w, -, hx, -⟩
      exact hx
    · intro hx
      exact ⟨F x, hT x hx, hx, rfl⟩
  have hdisj : Set.Pairwise (↑T) (Function.onFun Disjoint fun w => S ∩ F ⁻¹' {w}) := by
    intro w _ w' _ hne
    refine Set.disjoint_left.mpr ?_
    rintro x ⟨-, hx⟩ ⟨-, hx'⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx hx'
    exact hne (hx.symm.trans hx')
  have hint : ∀ w ∈ T, IntegrableOn (fun x => L (F x)) (S ∩ F ⁻¹' {w}) μ := by
    intro w hw
    refine (integrableOn_const (C := L w) (hfin w hw)).congr_fun ?_ (hmeas w hw)
    rintro x ⟨-, hx⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp [hx]
  conv_lhs => rw [← hS]
  rw [integral_biUnion_finset T hmeas hdisj hint, map_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  have heq : Set.EqOn (fun x => L (F x)) (fun _ => L w) (S ∩ F ⁻¹' {w}) := by
    rintro x ⟨-, hx⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp [hx]
  rw [map_smul, setIntegral_congr_fun (hmeas w hw) heq, setIntegral_const, smul_eq_mul,
    Measure.real, RCLike.real_smul_eq_coe_mul]
  rfl

variable {v : HeightOneSpectrum (𝓞 ℚ)} {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}

theorem isLocallyConstant_Rsub_iotaGL (f₀ : ↥(principalSeries3 v χ)) :
    IsLocallyConstant fun k : GL (Fin 2) (v.adicCompletion ℚ) => Rsub (iotaGL k) f₀ := by
  rw [IsLocallyConstant.iff_exists_open]
  intro k
  refine ⟨(fun κ => k * κ) '' ((stab (f₀ : LocalGL3 v → ℂ)).comap
      (iotaGL : GL (Fin 2) (v.adicCompletion ℚ) →* LocalGL3 v) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
    (isOpenMap_mul_left k) _ (isOpen_comap_iotaGL_stab f₀), ⟨1, one_mem _, mul_one k⟩, ?_⟩
  rintro _ ⟨κ, hκ, rfl⟩
  rw [map_mul, Rsub_mul, Rsub_eq_self_of_mem_stab (Subgroup.mem_comap.mp hκ)]

variable [MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ))] [BorelSpace (GL (Fin 2) (v.adicCompletion ℚ))]

theorem exists_average (f₀ : ↥(principalSeries3 v χ)) (K₁ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)))
    (hKc : IsCompact (K₁ : Set (GL (Fin 2) (v.adicCompletion ℚ))))
    (hKo : IsOpen (K₁ : Set (GL (Fin 2) (v.adicCompletion ℚ))))
    (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure] :
    ∃ Φ' : ↥(principalSeries3 v χ),
      (∀ L : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ,
        ∫ k in (K₁ : Set (GL (Fin 2) (v.adicCompletion ℚ))), L (Rsub (iotaGL k) f₀) ∂μ₂ = L Φ') ∧
      ∀ k₁ ∈ K₁, Rsub (iotaGL k₁) Φ' = Φ' := by
  classical
  set F : GL (Fin 2) (v.adicCompletion ℚ) → ↥(principalSeries3 v χ) := fun k => Rsub (iotaGL k) f₀ with hFdef
  have hloc : IsLocallyConstant F := isLocallyConstant_Rsub_iotaGL f₀
  have hfinite : (F '' (K₁ : Set (GL (Fin 2) (v.adicCompletion ℚ)))).Finite := by
    haveI : CompactSpace (K₁ : Set (GL (Fin 2) (v.adicCompletion ℚ))) := isCompact_iff_compactSpace.mp hKc
    rw [Set.image_eq_range]
    exact (hloc.comp_continuous continuous_subtype_val).range_finite
  set T : Finset ↥(principalSeries3 v χ) := hfinite.toFinset with hTdef
  have hT : ∀ k ∈ (K₁ : Set (GL (Fin 2) (v.adicCompletion ℚ))), F k ∈ T := fun k hk =>
    hfinite.mem_toFinset.mpr (Set.mem_image_of_mem F hk)
  have hTiff : ∀ w, w ∈ T ↔ ∃ k ∈ K₁, F k = w := fun w => by
    rw [hTdef, Set.Finite.mem_toFinset, Set.mem_image]
    rfl
  set A : ↥(principalSeries3 v χ) → Set (GL (Fin 2) (v.adicCompletion ℚ)) :=
    fun w => (K₁ : Set (GL (Fin 2) (v.adicCompletion ℚ))) ∩ F ⁻¹' {w} with hAdef
  have hmeas : ∀ w, MeasurableSet (A w) := fun w =>
    hKo.measurableSet.inter (hloc.isOpen_fiber w).measurableSet
  have hfin : ∀ w, μ₂ (A w) ≠ ⊤ := fun w =>
    (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hKc.measure_lt_top).ne
  refine ⟨∑ w ∈ T, ((μ₂ (A w)).toReal : ℂ) • w, fun L => ?_, fun k₁ hk₁ => ?_⟩
  · exact setIntegral_apply_eq_apply_sum μ₂ F T hT (fun w _ => hmeas w) (fun w _ => hfin w) L
  ·
    set σ := Rsub (χ := χ) (iotaGL k₁) with hσ
    have hσF : ∀ k, σ (F k) = F (k₁ * k) := fun k => by
      simp only [hσ, hFdef, map_mul, Rsub_mul]
    have hσT : ∀ w ∈ T, σ w ∈ T := fun w hw => by
      obtain ⟨k, hk, rfl⟩ := (hTiff w).mp hw
      exact (hTiff _).mpr ⟨k₁ * k, K₁.mul_mem hk₁ hk, (hσF k).symm⟩
    have hA : ∀ w, A (σ w) = (fun k => k₁⁻¹ * k) ⁻¹' A w := fun w => by
      ext k
      simp only [hAdef, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
      have hk : F k = σ (F (k₁⁻¹ * k)) := by rw [hσF, mul_inv_cancel_left]
      rw [hk, (Rsub_injective (iotaGL k₁)).eq_iff]
      constructor
      · rintro ⟨hkK, hFk⟩
        exact ⟨by simpa using K₁.mul_mem (K₁.inv_mem hk₁) hkK, hFk⟩
      · rintro ⟨hkK, hFk⟩
        exact ⟨by simpa using K₁.mul_mem hk₁ hkK, hFk⟩
    have hμA : ∀ w, μ₂ (A (σ w)) = μ₂ (A w) := fun w => by
      rw [hA, measure_preimage_mul]
    rw [map_sum]
    simp_rw [map_smul]
    refine Finset.sum_bij (fun w _ => σ w) hσT (fun w _ w' _ h => Rsub_injective _ h) ?_ ?_
    · intro w' hw'
      obtain ⟨k', hk', rfl⟩ := (hTiff w').mp hw'
      refine ⟨F (k₁⁻¹ * k'), (hTiff _).mpr ⟨k₁⁻¹ * k', K₁.mul_mem (K₁.inv_mem hk₁) hk', rfl⟩, ?_⟩
      rw [hσF, mul_inv_cancel_left]
    · intro w _
      rw [hμA]

end Average

section Bounds

variable {v : HeightOneSpectrum (𝓞 ℚ)}

theorem exists_valued_le_exp (x : v.adicCompletion ℚ) : ∃ m : ℤ, Valued.v x ≤ WithZero.exp m := by
  by_cases hx : Valued.v x = 0
  · exact ⟨0, by rw [hx]; exact zero_le'⟩
  · exact ⟨WithZero.log (Valued.v x), by rw [WithZero.exp_log hx]⟩

theorem exists_row_one_le_exp (k₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    ∃ M : ℤ, ∀ j : Fin 2, Valued.v (k₀ 1 j) ≤ WithZero.exp M := by
  obtain ⟨m₀, h₀⟩ := exists_valued_le_exp (k₀ 1 0)
  obtain ⟨m₁, h₁⟩ := exists_valued_le_exp (k₀ 1 1)
  refine ⟨max m₀ m₁, fun j => ?_⟩
  fin_cases j
  · exact h₀.trans (WithZero.exp_le_exp.mpr (le_max_left _ _))
  · exact h₁.trans (WithZero.exp_le_exp.mpr (le_max_right _ _))

theorem valued_mulVec_one_le_one {t k₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)}
    {Y : Fin 2 → v.adicCompletion ℚ} {n₂ M c : ℤ}
    (ht10 : t 1 0 = 0) (ht11 : Valued.v (t 1 1) ≤ WithZero.exp (-n₂))
    (hk : ∀ j : Fin 2, Valued.v (k₀ 1 j) ≤ WithZero.exp M) (hY : ∀ i, Valued.v (Y i) ≤ WithZero.exp c)
    (hn : M + c ≤ n₂) : Valued.v (((t * k₀) *ᵥ Y) 1) ≤ 1 := by
  have hterm : ∀ j : Fin 2, Valued.v (t 1 1 * k₀ 1 j * Y j) ≤ 1 := fun j => by
    rw [map_mul, map_mul]
    calc Valued.v (t 1 1) * Valued.v (k₀ 1 j) * Valued.v (Y j)
        ≤ WithZero.exp (-n₂) * WithZero.exp M * WithZero.exp c := mul_le_mul' (mul_le_mul' ht11 (hk j)) (hY j)
      _ = WithZero.exp (-n₂ + M + c) := by rw [WithZero.exp_add, WithZero.exp_add]
      _ ≤ WithZero.exp 0 := WithZero.exp_le_exp.mpr (by omega)
      _ = 1 := WithZero.exp_zero
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_apply_one_of_apply_one_zero t k₀ ht10]
  exact (Valuation.map_add _ _ _).trans (max_le (hterm 0) (hterm 1))

theorem valued_zpow_of_valued_eq {π : v.adicCompletion ℚ} (hϖ : Valued.v π = WithZero.exp (-1 : ℤ)) (n : ℤ) :
    Valued.v (π ^ n) = WithZero.exp (-n) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul, smul_neg, zsmul_one, Int.cast_id]

end Bounds

end LanglandsTunnell.CubicInduction.TypeIntegralSnd
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_snd.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_snd.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_snd.LanglandsTunnell.CubicInduction.TypeIntegralSnd"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_snd.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_snd.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_snd.LanglandsTunnell"

open AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse

open scoped nonZeroDivisors

p2m_open "LanglandsTunnell.CubicInduction~exists_valued_le_exp" in open _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_snd.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.TypeIntegralSnd in
open scoped Classical in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : Fin 3 → ℕ)
    (ha : ∀ i, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (χ i) (a i))
    (W : LocalGL3 v → ℂ)
    (hmem : ∃ (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 v χ)),
      IsWhittakerFunctional3 ψv Λ ∧ W = coefficientFn Λ f)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (b : ℕ)
    (hfloorb : ∀ i, 2 * b + 1 ≤ a i) :
    ∀ (g₃ : LocalGL3 v) (k₀ : GL (Fin 2) (v.adicCompletion ℚ)) (η : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (c : ℕ),
    LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v η c → c ≤ b →
    letI := localBorel ℚ v
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∃ N : ℤ, ∀ n : ℤ × ℤ, N ≤ n.2 →
        (∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
            (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) :
                  Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                W (iotaGL (UnramifiedWhittaker.scalarPi
                      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
                      ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) = 0 ∧
        (∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
            (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) :
                  Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                dualWhittakerFn3 (fun x => W (x * g₃)) (iotaGL (UnramifiedWhittaker.scalarPi
                      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
                      ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) = 0 := by
  intro g₃ k₀ η c hη hcb μ₂ hμ₂
  classical
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) := localGLBorel ℚ v
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ v
  obtain ⟨Λ, f, hΛ, rfl⟩ := hmem
  set K₁ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)) := AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b)
    with hK₁def
  have hK := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ v (v.asIdeal ^ b) (pow_ne_zero _ v.ne_bot)

  obtain ⟨Φ', hint, hinv⟩ := exists_average (Rsub g₃ f) K₁ hK.1 hK.2 μ₂

  have hfix : ∀ k₁ ∈ K₁, ∀ g : LocalGL3 v,
      (Φ' : LocalGL3 v → ℂ) (g * iotaGL k₁) = (Φ' : LocalGL3 v → ℂ) g := fun k₁ hk₁ g => by
    have h := congrArg (fun G : ↥(principalSeries3 v χ) => (G : LocalGL3 v → ℂ) g) (hinv k₁ hk₁)
    simpa using h
  have hdiag : ∀ (g : LocalGL3 v) (u : (v.adicCompletion ℚ)ˣ), Valued.v (u : v.adicCompletion ℚ) = 1 →
      (Φ' : LocalGL3 v → ℂ) (g * iotaGL (diagUnitGL2 u)) = (Φ' : LocalGL3 v → ℂ) g :=
    fun g u hu => hfix _ (diagUnitGL2_mem_localLevelOne u hu) g
  have hb1 : WithZero.exp (-(b : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  have hupper : ∀ (g : LocalGL3 v) (s : v.adicCompletion ℚ), Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      (Φ' : LocalGL3 v → ℂ) (g * upperUnipotent3 s 0 0) = (Φ' : LocalGL3 v → ℂ) g := fun g s hs => by
    rw [← iotaGL_unipotentGL2]
    exact hfix _ (unipotentGL2_mem_localLevelOne s (hs.trans hb1)) g
  have hlower : ∀ (g : LocalGL3 v) (s : v.adicCompletion ℚ), Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      (Φ' : LocalGL3 v → ℂ) (g * lowerUnipotent21 s) = (Φ' : LocalGL3 v → ℂ) g := fun g s hs => by
    rw [← iotaGL_lowerUnipotentGL2]
    exact hfix _ (lowerUnipotentGL2_mem_localLevelOne s hs) g

  have hχ' : ∀ i, ∃ u ∈ higherUnitsAt ℚ v b, χ i u ≠ 1 := fun i =>
    (ha i).2 b (by have := hfloorb i; omega)

  obtain ⟨cA, hA⟩ := LanglandsTunnell.CubicInduction.exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3 v χ b hχ' Φ' Φ'.2 hdiag hupper hlower
  obtain ⟨cA', hA'⟩ := LanglandsTunnell.CubicInduction.exists_forall_linearMap_apply_eq_zero_of_transposeInv3_radicalP21_of_mem_principalSeries3
      v χ b hχ' Φ' Φ'.2 hdiag hupper hlower

  obtain ⟨M, hM⟩ := exists_row_one_le_exp ((k₀ : GL (Fin 2) (v.adicCompletion ℚ)) :
    Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))

  have hψ : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1 := fun x hx => by
    rw [hψinv, AddChar.inv_apply]
    refine LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ v (-x) ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_neg]
    exact hx
  refine ⟨M + max (cA : ℤ) (cA' : ℤ), fun n hn => ?_⟩

  have ht10 : ∀ x : (v.adicCompletion ℚ)ˣ,
      ((scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 * diagUnitGL2 x : GL (Fin 2) (v.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 0 = 0 := fun x => by
    rw [torus_apply_one]; simp
  have ht11 : ∀ x : (v.adicCompletion ℚ)ˣ,
      Valued.v (((scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 * diagUnitGL2 x : GL (Fin 2) (v.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 1) ≤ WithZero.exp (-n.2) := fun x => by
    rw [torus_apply_one, if_pos rfl, valued_zpow_of_valued_eq hϖ]
  have hbox : ∀ (d : ℕ) (Y : Fin 2 → v.adicCompletion ℚ), (d : ℤ) ≤ max (cA : ℤ) (cA' : ℤ) →
      (∀ i, Valued.v (Y i) ≤ WithZero.exp (d : ℤ)) → ∀ x : (v.adicCompletion ℚ)ˣ,
      Valued.v (Matrix.mulVec ((scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 * diagUnitGL2 x * k₀ : GL (Fin 2) (v.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) Y 1) ≤ 1 := fun d Y hd hY x => by
    rw [Units.val_mul]
    exact valued_mulVec_one_le_one (ht10 x) (ht11 x) hM hY (by omega)

  have h1 : ∀ u : (v.adicCompletion ℚ)ˣ,
      ∫ k in (K₁ : Set (GL (Fin 2) (v.adicCompletion ℚ))),
        coefficientFn Λ f (iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1 * u) * (k₀ * k)) * g₃)
          ∂μ₂ = 0 := by
    intro u
    set t : GL (Fin 2) (v.adicCompletion ℚ) := scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1 * u)
      with htdef
    set L : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ := Λ ∘ₗ Rsub (iotaGL (t * k₀)) with hLdef
    have hrw : ∀ k : GL (Fin 2) (v.adicCompletion ℚ),
        coefficientFn Λ f (iotaGL (t * (k₀ * k)) * g₃) = L (Rsub (iotaGL k) (Rsub g₃ f)) := fun k => by
      simp only [coefficientFn_eq, hLdef, LinearMap.comp_apply, ← Rsub_mul, map_mul, mul_assoc]
    simp_rw [hrw]
    rw [hint L]
    have h := hA L ?_
    · simpa using h
    · intro G Y hY
      change L (Rsub (radicalP21 Y) G) = L G
      rw [hLdef, LinearMap.comp_apply, LinearMap.comp_apply, apply_Rsub_iotaGL_Rsub_radicalP21 hΛ,
        hψ _ (hbox cA Y (le_max_left _ _) hY _), one_mul]

  have h2 : ∀ u : (v.adicCompletion ℚ)ˣ,
      ∫ k in (K₁ : Set (GL (Fin 2) (v.adicCompletion ℚ))),
        dualWhittakerFn3 (fun x => coefficientFn Λ f (x * g₃))
          (iotaGL (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1 * u) *
            (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂ = 0 := by
    intro u
    set t : GL (Fin 2) (v.adicCompletion ℚ) := scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 * diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1 * u)
      with htdef
    set L' : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ :=
      Λ ∘ₗ Rsub (longWeyl3 * iotaGL (AutomorphicForm.transposeInvN (Fin 2) (t * k₀))) with hL'def
    have hrw : ∀ k : GL (Fin 2) (v.adicCompletion ℚ),
        dualWhittakerFn3 (fun x => coefficientFn Λ f (x * g₃))
          (iotaGL (t * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) = L' (Rsub (iotaGL k) (Rsub g₃ f)) := fun k => by
      rw [dualWhittakerFn3_apply, transposeInv3_iotaGL, ← mul_assoc, AutomorphicForm.transposeInvN_mul,
        AutomorphicForm.transposeInvN_transposeInvN, coefficientFn_eq, hL'def, LinearMap.comp_apply, ← Rsub_mul,
        ← Rsub_mul, map_mul]
      simp only [mul_assoc]
    simp_rw [hrw]
    rw [hint L']
    have h := hA' L' ?_
    · simpa using h
    · intro G Y hY
      change L' (Rsub (transposeInv3 (radicalP21 Y)) G) = L' G
      rw [hL'def, LinearMap.comp_apply, LinearMap.comp_apply,
        apply_Rsub_longWeyl3_iotaGL_Rsub_transposeInv3_radicalP21 hΛ, AutomorphicForm.transposeInvN_transposeInvN,
        hψ _ ?_, one_mul]
      rw [Valuation.map_neg]
      exact hbox cA' Y (le_max_right _ _) hY _
  refine ⟨?_, ?_⟩
  · simp_rw [h1]
    simp
  · simp_rw [h2]
    simp

end S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_snd
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_snd (solution)
