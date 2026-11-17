-- Prove2me | solution 1 for N25.unitRelation25_sturm_realization
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:48.272723+00:00
-- url     : https://prove2.me/submissions/caf4cc61-1e9c-48f6-b1e2-49b88acd5321

import Mathlib
import Definitions.Def_N25_UnitRelation
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_unitDenominatorForm25
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_N25_unitNumeratorForm25

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularCurve

open scoped MatrixGroups

namespace N25

private theorem period_one : (1 : ℝ) ∈ GammaH25GL.strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH 25 N25.H25)]
  exact AddSubgroup.mem_zmultiples 1

private theorem integral_mul {k l : ℤ}
    (f : ModularForm GammaH25GL k) (g : ModularForm GammaH25GL l)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    IsIntegralQExp (f.mul g) (pf * pg) := by
  unfold IsIntegralQExp at *
  rw [map_mul, hf, hg, ModularForm.qExpansion_mul one_pos period_one]

private theorem integral_pow {k : ℤ}
    (f : ModularForm GammaH25GL k) (n : ℕ)
    {p : PowerSeries ℤ} (hf : IsIntegralQExp f p) :
    IsIntegralQExp (f.pow n) (p ^ n) := by
  unfold IsIntegralQExp at *
  rw [map_pow, hf, ModularForm.qExpansion_pow one_pos period_one]

private theorem integral_add {k : ℤ}
    (f g : ModularForm GammaH25GL k)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    IsIntegralQExp (f + g) (pf + pg) := by
  unfold IsIntegralQExp at *
  rw [map_add, hf, hg, ModularForm.qExpansion_add one_pos period_one]

private theorem integral_sub {k : ℤ}
    (f g : ModularForm GammaH25GL k)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    IsIntegralQExp (f - g) (pf - pg) := by
  unfold IsIntegralQExp at *
  rw [map_sub, hf, hg, ModularForm.qExpansion_sub one_pos period_one]

private theorem cleared_relation_form
    (G F₀ F₁ : ModularForm GammaH25GL 36)
    (g f₀ f₁ : PowerSeries ℤ)
    (hg : IsIntegralQExp G g) (hf₀ : IsIntegralQExp F₀ f₀) (hf₁ : IsIntegralQExp F₁ f₁) :
    ∃ H : ModularForm GammaH25GL 396,
      IsIntegralQExp H (clearedUnitRelation25 g f₀ f₁) ∧
        ∀ τ : UpperHalfPlane, H τ = clearedUnitRelation25 (G τ) (F₀ τ) (F₁ τ) := by
  let T₀ : ModularForm GammaH25GL 396 := (F₀.pow 4).mul (G.pow 7)
  let T₁ : ModularForm GammaH25GL 396 := ((F₀.pow 6).mul (G.pow 4)).mul F₁
  let T₂ : ModularForm GammaH25GL 396 := ((F₀.pow 3).mul (G.pow 6)).mul (F₁.pow 2)
  let T₃ : ModularForm GammaH25GL 396 := ((F₀.pow 5).mul (G.pow 4)).mul (F₁.pow 2)
  let T₄ : ModularForm GammaH25GL 396 := ((F₀.pow 6).mul (G.pow 3)).mul (F₁.pow 2)
  let T₅ : ModularForm GammaH25GL 396 := ((F₀.pow 4).mul (G.pow 4)).mul (F₁.pow 3)
  let T₆ : ModularForm GammaH25GL 396 := ((F₀.pow 5).mul (G.pow 3)).mul (F₁.pow 3)
  let T₇ : ModularForm GammaH25GL 396 := ((F₀.pow 6).mul (G.pow 2)).mul (F₁.pow 3)
  let T₈ : ModularForm GammaH25GL 396 := (F₀.pow 7).mul (F₁.pow 4)
  let H : ModularForm GammaH25GL 396 :=
    T₀-T₁+T₂-T₃-(T₄+T₄)-T₅-T₆-(T₇+T₇)+T₈
  have ht₀ := integral_mul (F₀.pow 4) (G.pow 7)
    (integral_pow F₀ 4 hf₀) (integral_pow G 7 hg)
  have ht₁ := integral_mul ((F₀.pow 6).mul (G.pow 4)) F₁
    (integral_mul (F₀.pow 6) (G.pow 4)
      (integral_pow F₀ 6 hf₀) (integral_pow G 4 hg)) hf₁
  have ht₂ := integral_mul ((F₀.pow 3).mul (G.pow 6)) (F₁.pow 2)
    (integral_mul (F₀.pow 3) (G.pow 6)
      (integral_pow F₀ 3 hf₀) (integral_pow G 6 hg)) (integral_pow F₁ 2 hf₁)
  have ht₃ := integral_mul ((F₀.pow 5).mul (G.pow 4)) (F₁.pow 2)
    (integral_mul (F₀.pow 5) (G.pow 4)
      (integral_pow F₀ 5 hf₀) (integral_pow G 4 hg)) (integral_pow F₁ 2 hf₁)
  have ht₄ := integral_mul ((F₀.pow 6).mul (G.pow 3)) (F₁.pow 2)
    (integral_mul (F₀.pow 6) (G.pow 3)
      (integral_pow F₀ 6 hf₀) (integral_pow G 3 hg)) (integral_pow F₁ 2 hf₁)
  have ht₅ := integral_mul ((F₀.pow 4).mul (G.pow 4)) (F₁.pow 3)
    (integral_mul (F₀.pow 4) (G.pow 4)
      (integral_pow F₀ 4 hf₀) (integral_pow G 4 hg)) (integral_pow F₁ 3 hf₁)
  have ht₆ := integral_mul ((F₀.pow 5).mul (G.pow 3)) (F₁.pow 3)
    (integral_mul (F₀.pow 5) (G.pow 3)
      (integral_pow F₀ 5 hf₀) (integral_pow G 3 hg)) (integral_pow F₁ 3 hf₁)
  have ht₇ := integral_mul ((F₀.pow 6).mul (G.pow 2)) (F₁.pow 3)
    (integral_mul (F₀.pow 6) (G.pow 2)
      (integral_pow F₀ 6 hf₀) (integral_pow G 2 hg)) (integral_pow F₁ 3 hf₁)
  have ht₈ := integral_mul (F₀.pow 7) (F₁.pow 4)
    (integral_pow F₀ 7 hf₀) (integral_pow F₁ 4 hf₁)
  have h44 := integral_add T₄ T₄ ht₄ ht₄
  have h77 := integral_add T₇ T₇ ht₇ ht₇
  have ha := integral_sub T₀ T₁ ht₀ ht₁
  have hb := integral_add (T₀-T₁) T₂ ha ht₂
  have hc := integral_sub (T₀-T₁+T₂) T₃ hb ht₃
  have hd := integral_sub (T₀-T₁+T₂-T₃) (T₄+T₄) hc h44
  have he := integral_sub (T₀-T₁+T₂-T₃-(T₄+T₄)) T₅ hd ht₅
  have hf := integral_sub (T₀-T₁+T₂-T₃-(T₄+T₄)-T₅) T₆ he ht₆
  have hi := integral_sub (T₀-T₁+T₂-T₃-(T₄+T₄)-T₅-T₆) (T₇+T₇) hf h77
  have hraw := integral_add (T₀-T₁+T₂-T₃-(T₄+T₄)-T₅-T₆-(T₇+T₇)) T₈ hi ht₈
  refine ⟨H, ?_, ?_⟩
  · convert hraw using 1
    · rfl
    · unfold clearedUnitRelation25
      ring
  · intro τ
    change (F₀ τ)^4*(G τ)^7-(F₀ τ)^6*(G τ)^4*(F₁ τ)+
      (F₀ τ)^3*(G τ)^6*(F₁ τ)^2-(F₀ τ)^5*(G τ)^4*(F₁ τ)^2-
      ((F₀ τ)^6*(G τ)^3*(F₁ τ)^2+(F₀ τ)^6*(G τ)^3*(F₁ τ)^2)-
      (F₀ τ)^4*(G τ)^4*(F₁ τ)^3-(F₀ τ)^5*(G τ)^3*(F₁ τ)^3-
      ((F₀ τ)^6*(G τ)^2*(F₁ τ)^3+(F₀ τ)^6*(G τ)^2*(F₁ τ)^3)+
      (F₀ τ)^7*(F₁ τ)^4 = _
    unfold clearedUnitRelation25
    ring

/-- The homogeneous cleared relation is the integral expansion of a weight-396 modular form. -/
theorem _root_.solution :
    ∃ H : ModularForm GammaH25GL 396,
      ModularCurve.IsIntegralQExp H unitRelationClearedSeries25 ∧
      ∀ τ : UpperHalfPlane,
        H τ = clearedUnitRelation25
          (ModularForm.discriminant τ ^ 3)
          (ModularForm.discriminant τ ^ 3 * unitAnalytic25 0 τ)
          (ModularForm.discriminant τ ^ 3 * unitAnalytic25 1 τ) := by
  obtain ⟨G, hG, hg⟩ := unitDenominatorForm25
  obtain ⟨F₀, hF₀, hf₀⟩ := unitNumeratorForm25 0
  obtain ⟨F₁, hF₁, hf₁⟩ := unitNumeratorForm25 1
  obtain ⟨H, hH, hval⟩ := cleared_relation_form G F₀ F₁
    unitDenominatorSeries25 (unitNumeratorSeries25 0) (unitNumeratorSeries25 1) hg hf₀ hf₁
  refine ⟨H, hH, ?_⟩
  intro τ
  rw [hval, hG, hF₀, hF₁]

end N25
