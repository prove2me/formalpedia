-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_eq_coefficientFn_principalSeries3_of_isCosetEigenfunction_of_norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/5285cb2d-3344-5e3c-9bcf-f045180770f5

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_spherical_mem_principalSeries3_isCosetEigenfunction
import Theorems.Thm_LanglandsTunnell_CubicInduction_whittakerFunctional3_spherical_ne_zero_of_norm_eq_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_ne_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_eq_zero_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn_of_apply_one_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_coefficientFn_principalSeries3_of_isCosetEigenfunction_of_norm_eq_one
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel LanglandsTunnell.CubicInduction

namespace SphidGlue

variable {v : HeightOneSpectrum (𝓞 ℚ)}

noncomputable def ord (x : (v.adicCompletion ℚ)ˣ) : ℤ := WithZero.log (Valued.v (x : v.adicCompletion ℚ))

theorem valued_ne_zero (x : (v.adicCompletion ℚ)ˣ) : Valued.v (x : v.adicCompletion ℚ) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr x.ne_zero

theorem exp_ord (x : (v.adicCompletion ℚ)ˣ) : WithZero.exp (ord x) = Valued.v (x : v.adicCompletion ℚ) := by
  rw [ord, WithZero.exp_log (valued_ne_zero x)]

theorem ord_mul (x y : (v.adicCompletion ℚ)ˣ) : ord (x * y) = ord x + ord y := by
  apply WithZero.exp_injective
  rw [WithZero.exp_add, exp_ord, exp_ord, exp_ord, Units.val_mul, map_mul]

theorem ord_one : ord (1 : (v.adicCompletion ℚ)ˣ) = 0 := by
  apply WithZero.exp_injective
  rw [exp_ord, Units.val_one, map_one, WithZero.exp_zero]

theorem ord_uniformizerUnit : ord (uniformizerUnit ℚ v) = -1 := by
  apply WithZero.exp_injective
  rw [exp_ord, valued_uniformizerUnit]

theorem ord_eq_zero_of_norm_eq_one {x : (v.adicCompletion ℚ)ˣ} (hx : ‖(x : v.adicCompletion ℚ)‖ = 1) : ord x = 0 := by
  apply WithZero.exp_injective
  rw [exp_ord, WithZero.exp_zero]
  refine le_antisymm ?_ ?_
  · exact Valued.toNormedField.norm_le_one_iff.mp hx.le
  · exact Valued.toNormedField.one_le_norm_iff.mp hx.ge

noncomputable def unrChar (α : ℂ) (hα : α ≠ 0) : (v.adicCompletion ℚ)ˣ →* ℂˣ where
  toFun x := (Units.mk0 α hα) ^ (-(ord x))
  map_one' := by rw [ord_one, neg_zero, zpow_zero]
  map_mul' x y := by rw [ord_mul, neg_add, zpow_add]

theorem unrChar_apply (α : ℂ) (hα : α ≠ 0) (x : (v.adicCompletion ℚ)ˣ) :
    ((unrChar (v := v) α hα x : ℂˣ) : ℂ) = α ^ (-(ord x)) := by
  simp [unrChar]

theorem unrChar_uniformizerUnit (α : ℂ) (hα : α ≠ 0) :
    ((unrChar (v := v) α hα (uniformizerUnit ℚ v) : ℂˣ) : ℂ) = α := by
  rw [unrChar_apply, ord_uniformizerUnit, neg_neg, zpow_one]

theorem unrChar_eq_one_of_norm_eq_one (α : ℂ) (hα : α ≠ 0) {x : (v.adicCompletion ℚ)ˣ}
    (hx : ‖(x : v.adicCompletion ℚ)‖ = 1) : unrChar (v := v) α hα x = 1 := by
  apply Units.ext
  rw [unrChar_apply, ord_eq_zero_of_norm_eq_one hx, neg_zero, zpow_zero, Units.val_one]

theorem norm_unrChar (α : ℂ) (hα : ‖α‖ = 1) (x : (v.adicCompletion ℚ)ˣ) :
    ‖((unrChar (v := v) α (by rintro rfl; simp at hα) x : ℂˣ) : ℂ)‖ = 1 := by
  rw [unrChar_apply, norm_zpow, hα, one_zpow]

theorem isLocallyConstant_unrChar (α : ℂ) (hα : α ≠ 0) : IsLocallyConstant (unrChar (v := v) α hα) := by
  refine IsLocallyConstant.iff_eventually_eq _ |>.mpr fun u₀ => ?_
  have h0 : ((u₀ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≠ 0 := u₀.ne_zero
  have hev : ∀ᶠ u in nhds u₀, Valued.v ((u : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
      Valued.v ((u₀ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) :=
    (Units.continuous_val.tendsto u₀).eventually (eventually_valued_eq v h0)
  filter_upwards [hev] with u hu
  apply Units.ext
  rw [unrChar_apply, unrChar_apply, ord, ord, hu]

variable {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}

theorem gl3AmbientRightTranslate_mul_apply (a b : LocalGL3 v) (f : LocalGL3 v → ℂ) :
    gl3AmbientRightTranslate (R := ℂ) (a * b) f =
      gl3AmbientRightTranslate (R := ℂ) a (gl3AmbientRightTranslate (R := ℂ) b f) := by
  funext x
  simp [gl3AmbientRightTranslate_apply, mul_assoc]

noncomputable def Rsub (a : LocalGL3 v) (f : ↥(principalSeries3 v χ)) : ↥(principalSeries3 v χ) :=
  ⟨gl3AmbientRightTranslate (R := ℂ) a f, rightTranslate_mem_principalSeries3 f.2 a⟩

@[scoped simp] theorem coe_Rsub (a : LocalGL3 v) (f : ↥(principalSeries3 v χ)) :
    ((Rsub a f : ↥(principalSeries3 v χ)) : LocalGL3 v → ℂ) = gl3AmbientRightTranslate (R := ℂ) a f := rfl

theorem coefficientFn_apply (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 v χ)) (g : LocalGL3 v) :
    coefficientFn Λ f g = Λ (Rsub g f) := rfl

theorem Rsub_one (f : ↥(principalSeries3 v χ)) : Rsub 1 f = f := by
  apply Subtype.ext; funext x; simp [gl3AmbientRightTranslate_apply]

theorem Rsub_mul (a b : LocalGL3 v) (f : ↥(principalSeries3 v χ)) : Rsub (a * b) f = Rsub a (Rsub b f) := by
  apply Subtype.ext; exact gl3AmbientRightTranslate_mul_apply a b f

noncomputable def coeffL (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) : ↥(principalSeries3 v χ) →ₗ[ℂ] (LocalGL3 v → ℂ) where
  toFun f := coefficientFn Λ f
  map_add' f g := by
    funext x
    show Λ _ = Λ _ + Λ _
    rw [← map_add]
    congr 1
  map_smul' c f := by
    funext x
    show Λ _ = c * Λ _
    rw [← smul_eq_mul, ← map_smul]
    congr 1

theorem coeffL_apply (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 v χ)) :
    coeffL Λ f = coefficientFn Λ f := rfl

theorem coefficientFn_one (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 v χ)) :
    coefficientFn Λ f 1 = Λ f := by
  rw [coefficientFn_apply, Rsub_one]

theorem isRightInvariant_coefficientFn (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 v χ))
    (hf : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) (f : LocalGL3 v → ℂ)) :
    IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) (coefficientFn Λ f) := by
  intro g u hu
  rw [coefficientFn_apply, coefficientFn_apply, Rsub_mul]
  congr 1
  apply Subtype.ext
  funext x
  simp only [coe_Rsub, gl3AmbientRightTranslate_apply]
  exact hf _ u hu

theorem isCosetEigenfunction_coefficientFn (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 v χ))
    (gen : LocalGL3 v) (lam : ℂ)
    (hf : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) gen (f : LocalGL3 v → ℂ) lam) :
    IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) gen (coefficientFn Λ f) lam := by
  intro ι _ reps hreps g
  classical
  have hsum : (∑ i, Rsub (g * reps i) f : ↥(principalSeries3 v χ)) = lam • Rsub g f := by
    apply Subtype.ext
    rw [Submodule.coe_sum, Submodule.coe_smul]
    funext x
    simp only [Finset.sum_apply, coe_Rsub, gl3AmbientRightTranslate_apply, Pi.smul_apply, smul_eq_mul]
    have := hf ι reps hreps (x * g)
    simp only [cosetSum, mul_assoc] at this ⊢
    exact this
  show cosetSum reps (coefficientFn Λ f) g = lam * coefficientFn Λ f g
  simp only [cosetSum, coefficientFn_apply]
  rw [← smul_eq_mul, ← map_smul, ← hsum, map_sum]

theorem centralGen_mul_comm (x : LocalGL3 v) : centralGen v * x = x * centralGen v := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  have hc : ((centralGen v : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      Matrix.diagonal ![varpi v, varpi v, varpi v] := rfl
  have hd : (Matrix.diagonal ![varpi v, varpi v, varpi v] : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      varpi v • (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  rw [hc, hd, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

theorem central_coefficientFn (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 v χ)) (e : ℂ)
    (hf : ∀ g : LocalGL3 v, (f : LocalGL3 v → ℂ) (centralGen v * g) = e * (f : LocalGL3 v → ℂ) g) :
    ∀ g : LocalGL3 v, coefficientFn Λ f (centralGen v * g) = e * coefficientFn Λ f g := by
  intro g
  rw [coefficientFn_apply, coefficientFn_apply]
  have hR : Rsub (centralGen v * g) f = e • Rsub g f := by
    apply Subtype.ext
    rw [Submodule.coe_smul, coe_Rsub, coe_Rsub]
    funext x
    simp only [gl3AmbientRightTranslate_apply, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← centralGen_mul_comm, mul_assoc, hf]
  rw [hR, map_smul, smul_eq_mul]

section Closure
variable (ψv : AddChar (v.adicCompletion ℚ) ℂ) (W W' : LocalGL3 v → ℂ) (c : ℂ)

theorem isRightInvariant_sub_smul (h : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (h' : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W') :
    IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) (W - c • W') := by
  intro g u hu
  simp only [Pi.sub_apply, Pi.smul_apply, h g u hu, h' g u hu]

theorem isCosetEigenfunction_sub_smul (gen : LocalGL3 v) (lam : ℂ)
    (h : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) gen W lam)
    (h' : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) gen W' lam) :
    IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) gen (W - c • W') lam := by
  intro ι _ reps hreps g
  have h1 := h ι reps hreps g
  have h2 := h' ι reps hreps g
  simp only [cosetSum, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib, ← Finset.mul_sum] at h1 h2 ⊢
  rw [h1, h2]
  ring

theorem central_sub_smul (e : ℂ) (h : ∀ g : LocalGL3 v, W (centralGen v * g) = e * W g)
    (h' : ∀ g : LocalGL3 v, W' (centralGen v * g) = e * W' g) :
    ∀ g : LocalGL3 v, (W - c • W') (centralGen v * g) = e * (W - c • W') g := by
  intro g
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h g, h' g]
  ring

theorem isGL3PsiWhittakerFn_sub_smul (h : IsGL3PsiWhittakerFn ψv W) (h' : IsGL3PsiWhittakerFn ψv W') :
    IsGL3PsiWhittakerFn ψv (W - c • W') := by
  intro x y z g
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h x y z g, h' x y z g]
  ring

end Closure

theorem exists_valued_le_exp_one_ne_one (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hlev : LanglandsTunnell.TateLocal.addCharLevel ψv = 0) (hne : ψv ≠ 1)
    (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1) :
    ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ ψv x ≠ 1 := by
  by_contra hcon
  push Not at hcon

  set S : Set ℤ := {n : ℤ | ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp n → ψv x = 1} with hS
  have h1S : (1 : ℤ) ∈ S := fun x hx => by
    by_contra h; exact absurd (hcon x hx) h
  have hbdd : BddAbove S := by
    by_contra hnb
    apply hne
    ext x
    rw [AddChar.one_apply]
    by_cases hx0 : Valued.v x = 0
    · exact hψ0 x (by rw [hx0]; exact zero_le_one)
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m := ⟨_, (WithZero.exp_log hx0).symm⟩
    rw [not_bddAbove_iff] at hnb
    obtain ⟨n, hnS, hmn⟩ := hnb m
    exact hnS x (by rw [hm]; exact WithZero.exp_le_exp.mpr hmn.le)
  have hle : (1 : ℤ) ≤ sSup S := le_csSup hbdd h1S
  rw [LanglandsTunnell.TateLocal.addCharLevel_def] at hlev
  change sSup S = 0 at hlev
  omega

end SphidGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_coefficientFn_principalSeries3_of_isCosetEigenfunction_of_norm_eq_one.SphidGlue"

open SphidGlue in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (α : Fin 3 → ℂ) (hα : ∀ i, ‖α i‖ = 1) (W : LocalGL3 v → ℂ)
    (hU : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W)
    (hT₁ : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W
      (cNormQ v * (α 0 + α 1 + α 2)))
    (hT₂ : IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W
      (cNormQ v * (α 0 * α 1 + α 0 * α 2 + α 1 * α 2)))
    (hZ : ∀ g : LocalGL3 v, W (centralGen v * g) = α 0 * α 1 * α 2 * W g)
    (hψ : IsGL3PsiWhittakerFn ψv W) (hlev : LanglandsTunnell.TateLocal.addCharLevel ψv = 0) (hne : ψv ≠ 1) :
    ∃ χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ),
      (∀ i, IsLocallyConstant (χ i)) ∧
      (∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖((χ i x : ℂˣ) : ℂ)‖ = 1) ∧
      (∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖(x : v.adicCompletion ℚ)‖ = 1 → χ i x = 1) ∧
      ∃ Λ : ↥(LanglandsTunnell.CubicInduction.principalSeries3 v χ) →ₗ[ℂ] ℂ,
        LanglandsTunnell.CubicInduction.IsWhittakerFunctional3 ψv Λ ∧
        ∃ f : ↥(LanglandsTunnell.CubicInduction.principalSeries3 v χ),
          W = LanglandsTunnell.CubicInduction.coefficientFn Λ f := by
  classical
  have hα0 : ∀ i, α i ≠ 0 := fun i h => by simpa [h] using hα i
  let χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ) := fun i => unrChar (α i) (hα0 i)
  have hχunr : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖(x : v.adicCompletion ℚ)‖ = 1 → χ i x = 1 :=
    fun i x hx => unrChar_eq_one_of_norm_eq_one _ _ hx
  have hχu : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖((χ i x : ℂˣ) : ℂ)‖ = 1 :=
    fun i x => norm_unrChar (α i) (hα i) x
  have hχlc : ∀ i, IsLocallyConstant (χ i) := fun i => isLocallyConstant_unrChar _ _
  have hχϖ : ∀ i, ((χ i (uniformizerUnit ℚ v) : ℂˣ) : ℂ) = α i := fun i => unrChar_uniformizerUnit _ _
  by_cases hW1 : W 1 = 0
  ·
    have hW : W = 0 := LanglandsTunnell.CubicInduction.eq_zero_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn_of_apply_one_eq_zero v ψv _ _ _ W hU hT₁ hT₂ hZ hψ hlev hne hW1
    refine ⟨χ, hχlc, hχu, hχunr, 0, isWhittakerFunctional3_zero ψv, 0, ?_⟩
    rw [hW]
    funext g
    simp [coefficientFn]
  ·
    have hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1 := by
      intro x hx
      have h := hψ x 0 0 1
      rw [mul_one, add_zero] at h
      have hmem : (upperUnipotent3 x 0 0 : LocalGL3 v) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by
        rw [mem_localMaximalCompact3_iff]
        have hinv : (((upperUnipotent3 x 0 0 : LocalGL3 v)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
            !![1, -x, x * 0 - 0; 0, 1, -0; 0, 0, 1] := rfl
        refine ⟨fun i j => ?_, fun i j => ?_⟩
        · rw [upperUnipotent3_coe]
          fin_cases i <;> fin_cases j <;> simp [hx]
        · rw [hinv]
          fin_cases i <;> fin_cases j <;> simp [hx, Valuation.map_neg]
      have h2 := hU 1 _ hmem
      rw [one_mul] at h2
      rw [h2] at h
      exact (mul_left_eq_self₀.mp h.symm).resolve_right hW1
    have hψ1 := exists_valued_le_exp_one_ne_one ψv hlev hne hψ0

    obtain ⟨f, hf1, hfK, hfT₁, hfT₂, hfZ⟩ := LanglandsTunnell.CubicInduction.exists_spherical_mem_principalSeries3_isCosetEigenfunction v χ hχunr
    simp only [hχϖ] at hfT₁ hfT₂ hfZ
    obtain ⟨Λ, hΛne, hΛ⟩ := LanglandsTunnell.CubicInduction.exists_isWhittakerFunctional3_ne_zero v χ hχlc ψv
      ⟨0, fun x hx => hψ0 x (by simpa using hx)⟩
    have hΛf : Λ f ≠ 0 := LanglandsTunnell.CubicInduction.whittakerFunctional3_spherical_ne_zero_of_norm_eq_one v χ hχunr hχu f hf1 hfK ψv hψ0 hψ1 Λ hΛ hΛne

    set W' : LocalGL3 v → ℂ := coefficientFn Λ f with hW'
    have hW'1 : W' 1 = Λ f := coefficientFn_one Λ f
    have hU' := isRightInvariant_coefficientFn Λ f hfK
    have hT₁' := isCosetEigenfunction_coefficientFn Λ f _ _ hfT₁
    have hT₂' := isCosetEigenfunction_coefficientFn Λ f _ _ hfT₂
    have hZ' := central_coefficientFn Λ f _ hfZ
    have hψ' : IsGL3PsiWhittakerFn ψv W' := isGL3PsiWhittakerFn_coefficientFn hΛ f

    set c : ℂ := W 1 / Λ f with hc
    have hD : W - c • W' = 0 :=
      LanglandsTunnell.CubicInduction.eq_zero_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn_of_apply_one_eq_zero v ψv _ _ _ (W - c • W')
        (isRightInvariant_sub_smul W W' c hU hU') (isCosetEigenfunction_sub_smul W W' c _ _ hT₁ hT₁')
        (isCosetEigenfunction_sub_smul W W' c _ _ hT₂ hT₂') (central_sub_smul W W' c _ hZ hZ')
        (isGL3PsiWhittakerFn_sub_smul ψv W W' c hψ hψ') hlev hne
        (by simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hW'1, hc, div_mul_cancel₀ _ hΛf, sub_self])
    refine ⟨χ, hχlc, hχu, hχunr, Λ, hΛ, c • f, ?_⟩
    rw [← coeffL_apply, map_smul, coeffL_apply]
    exact (sub_eq_zero.mp hD)

end S_LanglandsTunnell_CubicInduction_exists_eq_coefficientFn_principalSeries3_of_isCosetEigenfunction_of_norm_eq_one
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_coefficientFn_principalSeries3_of_isCosetEigenfunction_of_norm_eq_one (solution)
