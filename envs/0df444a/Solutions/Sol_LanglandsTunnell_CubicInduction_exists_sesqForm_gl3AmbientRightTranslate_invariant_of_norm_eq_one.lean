-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_sesqForm_gl3AmbientRightTranslate_invariant_of_norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d6f4992b-eef2-525e-82a0-247bf2ff4f72

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_invariant_pos_linearMap_of_torusChar3_eq_halfModulus3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_sesqForm_gl3AmbientRightTranslate_invariant_of_norm_eq_one
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField
open scoped ComplexConjugate

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff rightTranslate_mem_principalSeries3 gl3AmbientRightTranslate LocalGL3 exists_invariant_pos_linearMap_of_torusChar3_eq_halfModulus3"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def normChar : (v.adicCompletion ℚ)ˣ →* ℂˣ where
  toFun x := Units.mk0 (((‖(x : v.adicCompletion ℚ)‖ : ℝ) : ℂ))
    (Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr x.ne_zero).ne')
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp [norm_mul]

private theorem normChar_apply (x : (v.adicCompletion ℚ)ˣ) :
    ((normChar v x : ℂˣ) : ℂ) = ((‖(x : v.adicCompletion ℚ)‖ : ℝ) : ℂ) := rfl

private def deltaTriple : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ) := ![normChar v, 1, (normChar v)⁻¹]

private theorem torusChar3_deltaTriple (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    torusChar3 v (deltaTriple v) a = halfModulus3 v a := by
  simp only [torusChar3, halfModulus3, deltaTriple, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, MonoidHom.one_apply, MonoidHom.inv_apply, Units.val_one,
    Units.val_inv_eq_inv_val, normChar_apply, one_mul]
  push_cast
  ring

private theorem conj_halfModulus3 (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    conj (halfModulus3 v a) = halfModulus3 v a := by
  simp [halfModulus3]

private theorem torusChar3_mul_conj {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (hunit : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖((χ i x : ℂˣ) : ℂ)‖ = 1) (a : Fin 3 → (v.adicCompletion ℚ)ˣ) :
    torusChar3 v χ a * conj (torusChar3 v χ a) = 1 := by
  have h : ‖torusChar3 v χ a‖ = 1 := by
    simp only [torusChar3, norm_prod, hunit, Finset.prod_const_one]
  rw [Complex.mul_conj', h]
  simp

private def prodFun (f f' : LocalGL3 v → ℂ) : LocalGL3 v → ℂ := fun g => f g * conj (f' g)

private theorem prodFun_mem {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (hunit : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖((χ i x : ℂˣ) : ℂ)‖ = 1) {f f' : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) (hf' : f' ∈ principalSeries3 v χ) :
    prodFun v f f' ∈ principalSeries3 v (deltaTriple v) := by
  obtain ⟨hlc, hn, ht⟩ := mem_principalSeries3_iff.mp hf
  obtain ⟨hlc', hn', ht'⟩ := mem_principalSeries3_iff.mp hf'
  refine mem_principalSeries3_iff.mpr ⟨hlc.comp₂ hlc' (fun z w => z * conj w), fun x y z g => ?_, fun a g => ?_⟩
  · show f _ * conj (f' _) = f g * conj (f' g)
    rw [hn, hn']
  · show f _ * conj (f' _) = torusChar3 v (deltaTriple v) a * halfModulus3 v a * (f g * conj (f' g))
    rw [ht, ht', torusChar3_deltaTriple, map_mul, map_mul, conj_halfModulus3]
    linear_combination (halfModulus3 v a * halfModulus3 v a * f g * conj (f' g)) * torusChar3_mul_conj v hunit a

private def prodSec {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (hunit : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖((χ i x : ℂˣ) : ℂ)‖ = 1)
    (f f' : ↥(principalSeries3 v χ)) : ↥(principalSeries3 v (deltaTriple v)) :=
  ⟨prodFun v f f', prodFun_mem v hunit f.2 f'.2⟩

private theorem prodSec_apply {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (hunit : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖((χ i x : ℂˣ) : ℂ)‖ = 1)
    (f f' : ↥(principalSeries3 v χ)) (g : LocalGL3 v) :
    (prodSec v hunit f f' : LocalGL3 v → ℂ) g = (f : LocalGL3 v → ℂ) g * conj ((f' : LocalGL3 v → ℂ) g) := rfl

private theorem prodSec_add_left {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (hunit : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖((χ i x : ℂˣ) : ℂ)‖ = 1)
    (f₁ f₂ f' : ↥(principalSeries3 v χ)) :
    prodSec v hunit (f₁ + f₂) f' = prodSec v hunit f₁ f' + prodSec v hunit f₂ f' := by
  apply Subtype.ext
  funext g
  simp only [prodSec_apply, Submodule.coe_add, Pi.add_apply]
  ring

private theorem prodSec_smul_left {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (hunit : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖((χ i x : ℂˣ) : ℂ)‖ = 1)
    (c : ℂ) (f f' : ↥(principalSeries3 v χ)) :
    prodSec v hunit (c • f) f' = c • prodSec v hunit f f' := by
  apply Subtype.ext
  funext g
  simp only [prodSec_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

private theorem prodSec_add_right {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (hunit : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖((χ i x : ℂˣ) : ℂ)‖ = 1)
    (f f₁ f₂ : ↥(principalSeries3 v χ)) :
    prodSec v hunit f (f₁ + f₂) = prodSec v hunit f f₁ + prodSec v hunit f f₂ := by
  apply Subtype.ext
  funext g
  simp only [prodSec_apply, Submodule.coe_add, Pi.add_apply, map_add]
  ring

private theorem prodSec_smul_right {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (hunit : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖((χ i x : ℂˣ) : ℂ)‖ = 1)
    (c : ℂ) (f f' : ↥(principalSeries3 v χ)) :
    prodSec v hunit f (c • f') = conj c • prodSec v hunit f f' := by
  apply Subtype.ext
  funext g
  simp only [prodSec_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

private theorem conj_comp_mem {φ : LocalGL3 v → ℂ} (hφ : φ ∈ principalSeries3 v (deltaTriple v)) :
    (fun g => conj (φ g)) ∈ principalSeries3 v (deltaTriple v) := by
  obtain ⟨hlc, hn, ht⟩ := mem_principalSeries3_iff.mp hφ
  refine mem_principalSeries3_iff.mpr ⟨hlc.comp conj, fun x y z g => ?_, fun a g => ?_⟩
  · show conj (φ _) = conj (φ g)
    rw [hn]
  · show conj (φ _) = torusChar3 v (deltaTriple v) a * halfModulus3 v a * conj (φ g)
    rw [ht, torusChar3_deltaTriple, map_mul, map_mul, conj_halfModulus3]

private theorem re_comp_mem {φ : LocalGL3 v → ℂ} (hφ : φ ∈ principalSeries3 v (deltaTriple v)) :
    (fun g => ((φ g).re : ℂ)) ∈ principalSeries3 v (deltaTriple v) := by
  obtain ⟨hlc, hn, ht⟩ := mem_principalSeries3_iff.mp hφ
  refine mem_principalSeries3_iff.mpr ⟨hlc.comp (fun z : ℂ => ((z.re : ℝ) : ℂ)), fun x y z g => ?_, fun a g => ?_⟩
  · show (((φ _).re : ℝ) : ℂ) = (((φ g).re : ℝ) : ℂ)
    rw [hn]
  · show (((φ _).re : ℝ) : ℂ) = torusChar3 v (deltaTriple v) a * halfModulus3 v a * (((φ g).re : ℝ) : ℂ)
    rw [ht, torusChar3_deltaTriple]
    simp only [halfModulus3]
    rw [← Complex.ofReal_mul, Complex.re_ofReal_mul]
    exact Complex.ofReal_mul _ _

private theorem im_comp_mem {φ : LocalGL3 v → ℂ} (hφ : φ ∈ principalSeries3 v (deltaTriple v)) :
    (fun g => ((φ g).im : ℂ)) ∈ principalSeries3 v (deltaTriple v) := by
  obtain ⟨hlc, hn, ht⟩ := mem_principalSeries3_iff.mp hφ
  refine mem_principalSeries3_iff.mpr ⟨hlc.comp (fun z : ℂ => ((z.im : ℝ) : ℂ)), fun x y z g => ?_, fun a g => ?_⟩
  · show (((φ _).im : ℝ) : ℂ) = (((φ g).im : ℝ) : ℂ)
    rw [hn]
  · show (((φ _).im : ℝ) : ℂ) = torusChar3 v (deltaTriple v) a * halfModulus3 v a * (((φ g).im : ℝ) : ℂ)
    rw [ht, torusChar3_deltaTriple]
    simp only [halfModulus3]
    rw [← Complex.ofReal_mul, Complex.im_ofReal_mul]
    exact Complex.ofReal_mul _ _

private theorem conj_apply_eq (I : ↥(principalSeries3 v (deltaTriple v)) →ₗ[ℂ] ℂ)
    (hreal : ∀ φ : ↥(principalSeries3 v (deltaTriple v)),
      (∀ g : LocalGL3 v, ((φ : LocalGL3 v → ℂ) g).im = 0) → (I φ).im = 0)
    (φ : ↥(principalSeries3 v (deltaTriple v))) :
    conj (I φ) = I ⟨fun g => conj ((φ : LocalGL3 v → ℂ) g), conj_comp_mem v φ.2⟩ := by
  obtain ⟨φr, hφr⟩ : ∃ φr : ↥(principalSeries3 v (deltaTriple v)),
      (φr : LocalGL3 v → ℂ) = fun g => ((((φ : LocalGL3 v → ℂ) g).re : ℝ) : ℂ) := ⟨⟨_, re_comp_mem v φ.2⟩, rfl⟩
  obtain ⟨φi, hφi⟩ : ∃ φi : ↥(principalSeries3 v (deltaTriple v)),
      (φi : LocalGL3 v → ℂ) = fun g => ((((φ : LocalGL3 v → ℂ) g).im : ℝ) : ℂ) := ⟨⟨_, im_comp_mem v φ.2⟩, rfl⟩
  have hr : (I φr).im = 0 := hreal φr (fun g => by simp [hφr])
  have hi : (I φi).im = 0 := hreal φi (fun g => by simp [hφi])
  have hφ : φ = φr + Complex.I • φi := by
    apply Subtype.ext
    funext g
    simp only [Submodule.coe_add, Submodule.coe_smul, hφr, hφi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact (Complex.re_add_im _).symm.trans (by ring)
  have hc : (⟨fun g => conj ((φ : LocalGL3 v → ℂ) g), conj_comp_mem v φ.2⟩ :
      ↥(principalSeries3 v (deltaTriple v))) = φr - Complex.I • φi := by
    apply Subtype.ext
    funext g
    simp only [Submodule.coe_sub, Submodule.coe_smul, hφr, hφi, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    apply Complex.ext <;> simp
  rw [hc, map_sub, map_smul, smul_eq_mul]
  conv_lhs => rw [hφ, map_add, map_smul, smul_eq_mul]
  rw [map_add, map_mul, Complex.conj_I, Complex.conj_eq_iff_im.mpr hr, Complex.conj_eq_iff_im.mpr hi]
  ring

private theorem prodSec_self_re_nonneg {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (hunit : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖((χ i x : ℂˣ) : ℂ)‖ = 1) (f : ↥(principalSeries3 v χ))
    (g : LocalGL3 v) :
    0 ≤ ((prodSec v hunit f f : LocalGL3 v → ℂ) g).re ∧ ((prodSec v hunit f f : LocalGL3 v → ℂ) g).im = 0 := by
  rw [prodSec_apply, Complex.mul_conj]
  exact ⟨by simpa using Complex.normSq_nonneg _, Complex.ofReal_im _⟩

private theorem prodSec_self_ne_zero {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (hunit : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖((χ i x : ℂˣ) : ℂ)‖ = 1) {f : ↥(principalSeries3 v χ)}
    (hf : f ≠ 0) : prodSec v hunit f f ≠ 0 := by
  intro h
  apply hf
  apply Subtype.ext
  funext g
  have h1 : (prodSec v hunit f f : LocalGL3 v → ℂ) g = 0 := by
    rw [h]
    rfl
  rw [prodSec_apply, Complex.mul_conj, Complex.ofReal_eq_zero, Complex.normSq_eq_zero] at h1
  exact h1

private theorem prodSec_translate {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (hunit : ∀ (i : Fin 3) (x : (v.adicCompletion ℚ)ˣ), ‖((χ i x : ℂˣ) : ℂ)‖ = 1) (g : LocalGL3 v)
    (f f' : ↥(principalSeries3 v χ)) :
    prodSec v hunit ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩
        ⟨gl3AmbientRightTranslate (R := ℂ) g f', rightTranslate_mem_principalSeries3 f'.2 g⟩ =
      ⟨gl3AmbientRightTranslate (R := ℂ) g (prodSec v hunit f f'),
        rightTranslate_mem_principalSeries3 (prodSec v hunit f f').2 g⟩ :=
  Subtype.ext (funext fun _ => rfl)

end LanglandsTunnell.CubicInduction

end

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_sesqForm_gl3AmbientRightTranslate_invariant_of_norm_eq_one.LanglandsTunnell.CubicInduction in
open IsDedekindDomain NumberField in
open scoped ComplexConjugate in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hunit : ∀ i, ∀ x : (v.adicCompletion ℚ)ˣ, ‖((χ i x : ℂˣ) : ℂ)‖ = 1) :
    ∃ B : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ) →ₗ⋆[ℂ] ℂ,
      (∀ f f' : ↥(principalSeries3 v χ), B f f' = (starRingEnd ℂ) (B f' f)) ∧
      (∀ f : ↥(principalSeries3 v χ), f ≠ 0 → 0 < (B f f).re) ∧
      ∀ (g : LocalGL3 v) (f f' : ↥(principalSeries3 v χ)),
        B ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩
            ⟨gl3AmbientRightTranslate (R := ℂ) g f', rightTranslate_mem_principalSeries3 f'.2 g⟩ = B f f' := by
  obtain ⟨I, hinv, hreal, hpos⟩ :=
    exists_invariant_pos_linearMap_of_torusChar3_eq_halfModulus3 v (deltaTriple v) (torusChar3_deltaTriple v)
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun f f' => I (prodSec v hunit f f'))
    (fun f₁ f₂ f' => by simp only [prodSec_add_left, map_add])
    (fun c f f' => by simp only [prodSec_smul_left, map_smul, RingHom.id_apply, smul_eq_mul])
    (fun f f₁ f₂ => by simp only [prodSec_add_right, map_add])
    (fun c f f' => by simp only [prodSec_smul_right, map_smul, smul_eq_mul]), ?_, ?_, ?_⟩
  · intro f f'
    simp only [LinearMap.mk₂'ₛₗ_apply]
    rw [conj_apply_eq v I hreal]
    congr 1
    apply Subtype.ext
    funext g
    dsimp only
    simp only [prodSec_apply, map_mul, starRingEnd_self_apply]
    ring
  · intro f hf
    simp only [LinearMap.mk₂'ₛₗ_apply]
    exact hpos _ (prodSec_self_re_nonneg v hunit f) (prodSec_self_ne_zero v hunit hf)
  · intro g f f'
    simp only [LinearMap.mk₂'ₛₗ_apply]
    rw [prodSec_translate]
    exact hinv g _

end S_LanglandsTunnell_CubicInduction_exists_sesqForm_gl3AmbientRightTranslate_invariant_of_norm_eq_one
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_sesqForm_gl3AmbientRightTranslate_invariant_of_norm_eq_one (solution)
