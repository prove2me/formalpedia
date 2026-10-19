-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Auxiliary.spread_trunc_eventual_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:34:24.829328+00:00
-- url     : https://prove2.me/submissions/3332a967-444c-4f3b-b24c-c2c557907063

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Spreading.lean:L386-L446
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Auxiliary.spread_trunc_eventual_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Auxiliary_binary_abs_le
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_finite_product_error
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_rowTrunc_error

-- ---- from OAI.Analysis.Littlewood.QuadraticTail ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
namespace OAI

universe uI uZ

namespace AsymptoticallyMinimalLittlewood
namespace QuadraticTail
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff

lemma phase_norm (t u x : ℝ) : ‖phase t u x‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Real.exp_zero]

lemma circleChirp_norm {g : ℝ → ℂ} (hg : ∀ x, ‖g x‖ ≤ 1)
    (t : ℝ) (z : UnitAddCircle) : ‖circleChirp g t z‖ ≤ 1 := by
  dsimp [circleChirp, AddCircle.liftIoc, Function.comp_def, Set.domRestrict]
  rw [norm_mul, phase_norm, mul_one]
  exact hg _

end
end QuadraticTail
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- from OAI.Analysis.Littlewood.Spreading ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
private abbrev Finset.prod_le_one₀ := @Finset.prod_le_one

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

universe uI uE uJ uK

namespace AsymptoticallyMinimalLittlewood
namespace Spreading
noncomputable section
open QuadraticTail MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff FourierTransform SchwartzMap

variable {I : Type uI} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma tensor_uniform_error {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1) {α : ℝ}
    (hα0 : 0≤α) (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α)
    {β : I → ℝ} (hβ : ∀ i, β i≠0) :
    ∃ C : ℝ, 0≤C ∧ ∀ B : ℝ, 1≤B → ∀ z : I → UnitAddCircle,
      ‖(∏ i, rowTrunc g B (β i) (z i))-
        (∏ i, circleChirp g (B*β i) (z i))‖ ≤ C/B := by
  apply finite_product_error (I := I) (Z := I → UnitAddCircle) Finset.univ
    (fun (i : I) (B : ℝ) (z : I → UnitAddCircle) ↦ rowTrunc g B (β i) (z i))
    (fun (i : I) (B : ℝ) (z : I → UnitAddCircle) ↦ circleChirp g (B*β i) (z i))
  · intro i _ B z
    exact circleChirp_norm hg1 _ _
  · intro i _
    obtain ⟨C,hC,h⟩ := rowTrunc_error hg hgs hα0 hα hs (hβ i)
    exact ⟨C,hC,fun B hB z ↦ h B hB (z i)⟩

end
end Spreading
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood
namespace Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex

lemma rowForm_apply {n : ℕ} (s : Fin n → ℤ) (x : Fin n → ℝ) :
    rowForm s x = ∑ k, (s k : ℝ)*x k := by simp [rowForm]

end
end Auxiliary
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

lemma mFourier_norm_apply {J : Type uJ} [Fintype J] (s : J → ℤ)
    (x : J → UnitAddCircle) : ‖mFourier s x‖=1 := by
  simp only [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one]

lemma mFourier_add_point {J : Type uJ} [Fintype J] (s : J → ℤ)
    (x y : J → UnitAddCircle) : mFourier s (x+y)=mFourier s x*mFourier s y := by
  simp only [mFourier, ContinuousMap.coe_mk,Pi.add_apply,fourier_apply,
    zsmul_add,AddCircle.toCircle_add,Circle.coe_mul,Finset.prod_mul_distrib]

lemma mFourier_real {J : Type uJ} [Fintype J] (s : J → ℤ) (x : J → ℝ) :
    mFourier s (fun j ↦ (x j : UnitAddCircle)) =
      Complex.exp (Complex.I*(2*Real.pi*(∑ j, (s j : ℝ)*x j) : ℝ)) := by
  simp only [mFourier,ContinuousMap.coe_mk,fourier_coe_apply,Complex.ofReal_one,div_one]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_mul,Complex.ofReal_sum,Complex.ofReal_intCast,Complex.ofReal_ofNat,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma phase_tensor_character {n : ℕ} {J : Type uJ} [Fintype J]
    (s : Fin n → ℤ) (b : J → Fin n → ℝ) (B : ℝ) (z : J → ℝ) :
    (∏ j, phase (B*rowForm s (b j)) 0 (z j)) =
      mFourier s (fun k ↦ ((B/2*∑ j, b j k*z j^2 : ℝ) : UnitAddCircle)) := by
  rw [mFourier_real]
  simp only [phase,sub_zero,zero_mul,← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_mul,Complex.ofReal_sum,Complex.ofReal_div,
    Complex.ofReal_ofNat,Complex.ofReal_pow,rowForm_apply]
  push_cast
  simp only [Finset.mul_sum,Finset.sum_mul,Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma spread_half_bound {n : ℕ} {J : Type uJ} [Fintype J]
    (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ)
    (hc : ∀ y : Fin n → UnitAddCircle,
      (binary n y : ℂ) = (∑ s ∈ S, c s*mFourier s y)+
        conj (∑ s ∈ S, c s*mFourier s y))
    (g : ℝ → ℝ) (hg : ∀ x, 0≤g x ∧ g x≤1)
    (b : J → Fin n → ℝ) (B : ℝ) (y : Fin n → UnitAddCircle)
    (z : J → UnitAddCircle) :
    ‖(∑ s∈S, c s*mFourier s y*∏ j, circleChirp (fun x ↦ (g x : ℂ))
      (B*rowForm s (b j)) (z j)) +
      conj (∑ s∈S, c s*mFourier s y*∏ j, circleChirp (fun x ↦ (g x : ℂ))
      (B*rowForm s (b j)) (z j))‖ ≤ 1 := by
  let x : J → ℝ := fun j ↦ AddCircle.equivIoc 1 (-1/2) (z j)
  let u : Fin n → UnitAddCircle := fun k ↦ ((B/2*∑ j, b j k*x j^2 : ℝ) : UnitAddCircle)
  let A : ℝ := ∏ j, g (x j)
  have hA0 : 0≤A := Finset.prod_nonneg (fun j _ ↦ (hg _).1)
  have hA1 : A≤1 := Finset.prod_le_one₀ (fun j _ ↦ (hg _).1) (fun j _ ↦ (hg _).2)
  have he : (∑ s∈S, c s*mFourier s y*∏ j, circleChirp (fun x ↦ (g x : ℂ))
      (B*rowForm s (b j)) (z j)) = (A : ℂ)*∑ s∈S, c s*mFourier s (y+u) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    have hp : (∏ j, circleChirp (fun x ↦ (g x : ℂ)) (B*rowForm s (b j)) (z j)) =
        (A : ℂ)*mFourier s u := by
      change (∏ j, (g (x j) : ℂ)*phase (B*rowForm s (b j)) 0 (x j)) = _
      rw [Finset.prod_mul_distrib,phase_tensor_character]
      simp only [A,Complex.ofReal_prod,u]
    rw [hp,mFourier_add_point]
    ring
  rw [he,map_mul,conj_ofReal,← mul_add,← hc]
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hA0,
    Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (binary_abs_le n _) hA0).trans (by simpa using hA1)

end
end AsymptoticallyMinimalLittlewood.Auxiliary

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

lemma spread_trunc_eventual_bound {n : ℕ} {J : Type uJ} [Fintype J] [DecidableEq J]
    (S : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ)
    (hc : ∀ y : Fin n → UnitAddCircle,
      (binary n y : ℂ) = (∑ s∈S, c s*mFourier s y)+conj (∑ s∈S, c s*mFourier s y))
    {g : ℝ → ℝ} (hgs : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hg : ∀ x, 0≤g x ∧ g x≤1) {α : ℝ} (hα0 : 0≤α) (hα : α<1/2)
    (hga : tsupport g ⊆ Set.Icc (-α) α)
    (b : J → Fin n → ℝ) (hb : ∀ s∈S, ∀ j, rowForm s (b j)≠0)
    {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ B : ℝ in atTop, ∀ y : Fin n → UnitAddCircle, ∀ z : J → UnitAddCircle,
      ‖(∑ s∈S, c s*mFourier s y*∏ j, rowTrunc (fun x ↦ (g x : ℂ)) B (rowForm s (b j)) (z j))+
        conj (∑ s∈S, c s*mFourier s y*∏ j, rowTrunc (fun x ↦ (g x : ℂ)) B (rowForm s (b j)) (z j))‖ ≤ 1+δ := by
  classical
  have hsupp : tsupport (fun x ↦ (g x : ℂ)) = tsupport g := by
    unfold tsupport
    apply congrArg closure
    ext x
    change ((g x : ℂ)≠0) ↔ g x≠0
    exact Complex.ofReal_ne_zero
  have hgc' : HasCompactSupport (fun x ↦ (g x : ℂ)) := by simpa only [HasCompactSupport,hsupp] using hgc
  have hgs' : ContDiff ℝ ∞ (fun x ↦ (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hgs
  have hg' : ∀ x, ‖(g x : ℂ)‖≤1 := by intro x; simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hg x).1] using (hg x).2
  have hga' : tsupport (fun x ↦ (g x : ℂ)) ⊆ Set.Icc (-α) α := by
    simpa only [hsupp] using hga
  have hh (s : S) : ∃ C : ℝ, 0≤C ∧ ∀ B : ℝ, 1≤B → ∀ z : J → UnitAddCircle,
      ‖(∏ j, rowTrunc (fun x ↦ (g x : ℂ)) B (rowForm s.val (b j)) (z j))-
        (∏ j, circleChirp (fun x ↦ (g x : ℂ)) (B*rowForm s.val (b j)) (z j))‖≤C/B :=
    tensor_uniform_error hgc' hgs' hg' hα0 hα hga' (hb s.val s.property)
  choose C hC hE using hh
  let A : ℝ := ∑ s : S, ‖c s.val‖*C s
  have hlim : Tendsto (fun B : ℝ ↦ 2*A/B) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  filter_upwards [hlim.eventually (eventually_lt_nhds hδ),eventually_ge_atTop (1:ℝ)] with B hBδ hB
  intro y z
  let T : ℂ := ∑ s∈S, c s*mFourier s y*∏ j, rowTrunc (fun x ↦ (g x : ℂ)) B (rowForm s (b j)) (z j)
  let G : ℂ := ∑ s∈S, c s*mFourier s y*∏ j, circleChirp (fun x ↦ (g x : ℂ)) (B*rowForm s (b j)) (z j)
  have hTG : ‖T-G‖≤A/B := by
    dsimp [T,G]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ s∈S, ‖c s*mFourier s y*((∏ j, rowTrunc (fun x ↦ (g x : ℂ)) B (rowForm s (b j)) (z j))-
        (∏ j, circleChirp (fun x ↦ (g x : ℂ)) (B*rowForm s (b j)) (z j)))‖ := by
          simp only [mul_sub]; exact norm_sum_le _ _
      _ = ∑ s : S, ‖c s.val‖*‖(∏ j, rowTrunc (fun x ↦ (g x : ℂ)) B (rowForm s.val (b j)) (z j))-
        (∏ j, circleChirp (fun x ↦ (g x : ℂ)) (B*rowForm s.val (b j)) (z j))‖ := by
          simp only [norm_mul,mFourier_norm_apply,mul_one]
          exact (Finset.sum_attach _ _).symm
      _ ≤ ∑ s : S, ‖c s.val‖*(C s/B) := Finset.sum_le_sum (fun s _ ↦ mul_le_mul_of_nonneg_left (hE s B hB z) (norm_nonneg _))
      _ = A/B := by simp only [A,mul_div_assoc,Finset.sum_div]
  have hm := spread_half_bound S c hc g hg b B y z
  change ‖G+conj G‖≤1 at hm
  change ‖T+conj T‖≤1+δ
  have hd : ‖(T+conj T)-(G+conj G)‖≤2*(A/B) := by
    calc
      _ = ‖(T-G)+conj (T-G)‖ := by congr 1; simp only [map_sub]; ring
      _ ≤ ‖T-G‖+‖conj (T-G)‖ := norm_add_le _ _
      _ ≤ 2*(A/B) := by rw [norm_conj]; linarith
  have ht := norm_add_le ((T+conj T)-(G+conj G)) (G+conj G)
  rw [sub_add_cancel] at ht
  have he : 2*(A/B)=2*A/B := by ring
  rw [he] at hd
  linarith

end
end AsymptoticallyMinimalLittlewood.Auxiliary

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

attribute [instance] FinitePacket.fintypeI FinitePacket.fintypeJ FinitePacket.nonemptyI

end
end AsymptoticallyMinimalLittlewood.Auxiliary

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

end
end AsymptoticallyMinimalLittlewood.Auxiliary

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Auxiliary
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading


theorem solution.{uJ} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Auxiliary.spread_trunc_eventual_bound.{uJ} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Auxiliary.spread_trunc_eventual_bound.{uJ}
