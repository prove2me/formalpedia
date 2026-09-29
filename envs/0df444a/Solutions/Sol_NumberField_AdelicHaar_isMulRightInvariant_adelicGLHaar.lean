-- Prove2me | solution 1 for NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/db7da04c-5c09-529d-9b93-0d68cbf73389

import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Group.ModularCharacter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar

set_option autoImplicit false

open MeasureTheory IsDedekindDomain
open scoped NumberField NNReal

local notation "Δ" => MeasureTheory.Measure.modularCharacter

section DeltaAlgebra

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]

private theorem unimodGL2_delta_conj (a h : G) : Δ (a * h * a⁻¹) = Δ h := by
  have h1 : Δ a * Δ a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  calc Δ (a * h * a⁻¹) = Δ a * Δ h * Δ a⁻¹ := by rw [map_mul, map_mul]
    _ = Δ h * (Δ a * Δ a⁻¹) := by ring
    _ = Δ h := by rw [h1, mul_one]

private theorem unimodGL2_delta_eq_one_of_sq (h : G) (hh : Δ h * Δ h = 1) : Δ h = 1 := by
  have h2 : Δ h ^ 2 = 1 := by rw [sq]; exact hh
  exact (pow_eq_one_iff_of_nonneg (by simp) two_ne_zero).1 h2

private theorem unimodGL2_delta_eq_one_of_conj_inv (a h : G) (hc : a * h * a⁻¹ = h⁻¹) :
    Δ h = 1 := by
  apply unimodGL2_delta_eq_one_of_sq
  calc Δ h * Δ h = Δ h * Δ (a * h * a⁻¹) := by rw [unimodGL2_delta_conj]
    _ = Δ h * Δ h⁻¹ := by rw [hc]
    _ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]

private theorem unimodGL2_delta_eq_one_of_mul (h h' z : G) (hz : Δ z = 1) (hh' : Δ h' = Δ h)
    (hm : h * h' = z) : Δ h = 1 := by
  apply unimodGL2_delta_eq_one_of_sq
  calc Δ h * Δ h = Δ h * Δ h' := by rw [hh']
    _ = Δ (h * h') := (map_mul _ _ _).symm
    _ = 1 := by rw [hm, hz]

private theorem unimodGL2_delta_central (z : G) (hz : ∀ g : G, g * z = z * g) : Δ z = 1 := by
  show Measure.modularCharacterFun z = 1
  borelize G
  rw [Measure.modularCharacterFun_eq_haarScalarFactor (Measure.haar (G := G)) z]
  have hfun : (fun g : G => g * z) = fun g : G => z * g := funext hz
  have hmap : Measure.map (· * z) (Measure.haar (G := G)) = Measure.haar := by
    rw [hfun]
    exact map_mul_left_eq_self _ z
  simp only [hmap, Measure.haarScalarFactor_self]

private theorem unimodGL2_isMulRightInvariant_of_modularCharacterFun [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (hΔ : ∀ g : G, Measure.modularCharacterFun g = 1) : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  haveI : (Measure.map (· * g) μ).Regular := Measure.Regular.map (Homeomorph.mulRight g)
  calc Measure.map (· * g) μ
      = Measure.haarScalarFactor (Measure.map (· * g) μ) μ • μ :=
        Measure.isMulLeftInvariant_eq_smul_of_regular _ _
    _ = Measure.modularCharacterFun g • μ := by
        rw [Measure.modularCharacterFun_eq_haarScalarFactor μ g]
    _ = μ := by rw [hΔ g]; exact one_smul ℝ≥0 μ

end DeltaAlgebra

section Matrices

variable {A : Type*} [CommRing A]

local notation "GL₂" => Matrix.GeneralLinearGroup (Fin 2) A

private def unimodGL2_E (x : A) : GL₂ :=
  ⟨!![1, x; 0, 1], !![1, -x; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

private def unimodGL2_L (y : A) : GL₂ :=
  ⟨!![1, 0; y, 1], !![1, 0; -y, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

private def unimodGL2_D (u e : Aˣ) : GL₂ :=
  ⟨!![(u : A), 0; 0, (e : A)], !![((u⁻¹ : Aˣ) : A), 0; 0, ((e⁻¹ : Aˣ) : A)],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

private def unimodGL2_w : GL₂ :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

private def unimodGL2_s : GL₂ :=
  ⟨!![-1, 0; 0, 1], !![-1, 0; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

private theorem unimodGL2_s_E_s (x : A) :
    unimodGL2_s * unimodGL2_E x * unimodGL2_s⁻¹ = (unimodGL2_E x)⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unimodGL2_s, unimodGL2_E, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem unimodGL2_s_L_s (y : A) :
    unimodGL2_s * unimodGL2_L y * unimodGL2_s⁻¹ = (unimodGL2_L y)⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unimodGL2_s, unimodGL2_L, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem unimodGL2_w_D_w (u : Aˣ) :
    unimodGL2_w * unimodGL2_D u 1 * unimodGL2_w⁻¹ = unimodGL2_D 1 u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unimodGL2_w, unimodGL2_D, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem unimodGL2_D_mul_D (u : Aˣ) :
    unimodGL2_D u 1 * unimodGL2_D 1 u = unimodGL2_D u u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unimodGL2_D, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem unimodGL2_D_eq_mul (u e : Aˣ) :
    unimodGL2_D u e = unimodGL2_D u 1 * unimodGL2_D 1 e := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unimodGL2_D, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem unimodGL2_D_central (u : Aˣ) (g : GL₂) :
    g * unimodGL2_D u u = unimodGL2_D u u * g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unimodGL2_D, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem unimodGL2_E_mul_entry (x : A) (g : GL₂) :
    (unimodGL2_E x * g).val 0 0 = g.val 0 0 + x * g.val 1 0 := by
  simp [unimodGL2_E, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem unimodGL2_ldu (h : GL₂) (a : Aˣ) (ha : h.val 0 0 = a) :
    h = unimodGL2_L (h.val 1 0 * ((a⁻¹ : Aˣ) : A)) *
      unimodGL2_D a (a⁻¹ * Matrix.GeneralLinearGroup.det h) *
      unimodGL2_E (((a⁻¹ : Aˣ) : A) * h.val 0 1) := by
  have hdet : ((Matrix.GeneralLinearGroup.det h : Aˣ) : A) =
      h.val 0 0 * h.val 1 1 - h.val 0 1 * h.val 1 0 := Matrix.det_fin_two _
  have hinv : ((a⁻¹ : Aˣ) : A) * (a : A) = 1 := Units.inv_mul a
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unimodGL2_L, unimodGL2_D, unimodGL2_E, Units.val_mul, Matrix.mul_apply,
      Fin.sum_univ_two, hdet, ha]
  · linear_combination (-(h.val 1 1)) * hinv

end Matrices

section DeltaGL2

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace (Matrix.GeneralLinearGroup (Fin 2) A)]

private theorem unimodGL2_delta_E (x : A) : Δ (unimodGL2_E x) = 1 :=
  unimodGL2_delta_eq_one_of_conj_inv unimodGL2_s _ (unimodGL2_s_E_s x)

private theorem unimodGL2_delta_L (y : A) : Δ (unimodGL2_L y) = 1 :=
  unimodGL2_delta_eq_one_of_conj_inv unimodGL2_s _ (unimodGL2_s_L_s y)

private theorem unimodGL2_delta_D_one (u : Aˣ) : Δ (unimodGL2_D u 1) = 1 := by
  refine unimodGL2_delta_eq_one_of_mul _ (unimodGL2_D 1 u) (unimodGL2_D u u)
    (unimodGL2_delta_central _ (unimodGL2_D_central u)) ?_ (unimodGL2_D_mul_D u)
  rw [← unimodGL2_w_D_w u, unimodGL2_delta_conj]

private theorem unimodGL2_delta_D (u e : Aˣ) : Δ (unimodGL2_D u e) = 1 := by
  have h1 : Δ (unimodGL2_D 1 e) = 1 := by
    rw [← unimodGL2_w_D_w e, unimodGL2_delta_conj, unimodGL2_delta_D_one]
  rw [unimodGL2_D_eq_mul, map_mul, unimodGL2_delta_D_one, h1, mul_one]

private theorem unimodGL2_delta_of_entry (h : Matrix.GeneralLinearGroup (Fin 2) A) (a : Aˣ)
    (ha : h.val 0 0 = a) : Δ h = 1 := by
  calc Δ h = Δ (unimodGL2_L (h.val 1 0 * ((a⁻¹ : Aˣ) : A)) *
        unimodGL2_D a (a⁻¹ * Matrix.GeneralLinearGroup.det h) *
        unimodGL2_E (((a⁻¹ : Aˣ) : A) * h.val 0 1)) := congrArg _ (unimodGL2_ldu h a ha)
    _ = 1 := by
      rw [map_mul, map_mul, unimodGL2_delta_L, unimodGL2_delta_D, unimodGL2_delta_E, mul_one,
        mul_one]

private theorem unimodGL2_delta_of_stable (g : Matrix.GeneralLinearGroup (Fin 2) A) (x : A)
    (hx : IsUnit (g.val 0 0 + x * g.val 1 0)) : Δ g = 1 := by
  obtain ⟨a, ha⟩ := hx
  have h1 : Δ (unimodGL2_E x * g) = 1 :=
    unimodGL2_delta_of_entry _ a (by rw [unimodGL2_E_mul_entry]; exact ha.symm)
  rwa [map_mul, unimodGL2_delta_E, one_mul] at h1

end DeltaGL2

section StableRange

variable {F : Type} [Field F]

set_option backward.isDefEq.respectTransparency false in

private theorem unimodGL2_stable_fin [NumberField F] (a b c d : FiniteAdeleRing (𝓞 F) F)
    (hdet : IsUnit (a * d - b * c)) : ∃ x : FiniteAdeleRing (𝓞 F) F, IsUnit (a + x * c) := by
  classical
  obtain ⟨h0, hev⟩ := FiniteAdeleRing.isUnit_iff.1 hdet
  have hdv : ∀ v, (a * d - b * c) v = a v * d v - b v * c v := fun v => rfl
  let xv : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F := fun v =>
    if Valued.v (a v) = 1 then 0 else if a v + c v ≠ 0 then 1 else 0
  have hxv : ∀ v, xv v ∈ v.adicCompletionIntegers F := by
    intro v
    simp only [xv]
    split_ifs <;> simp
  let x : FiniteAdeleRing (𝓞 F) F := ⟨xv, Filter.Eventually.of_forall hxv⟩
  have hx : ∀ v, (a + x * c) v = a v + xv v * c v := fun v => rfl
  refine ⟨x, FiniteAdeleRing.isUnit_iff.2 ⟨fun v => ?_, ?_⟩⟩
  · rw [hx]
    have hv := h0 v
    rw [hdv] at hv
    simp only [xv]
    by_cases h1 : Valued.v (a v) = 1
    · rw [if_pos h1, zero_mul, add_zero]
      intro ha0
      rw [ha0, Valuation.map_zero] at h1
      exact zero_ne_one h1
    · by_cases h2 : a v + c v ≠ 0
      · rw [if_neg h1, if_pos h2, one_mul]
        exact h2
      · rw [if_neg h1, if_neg h2, zero_mul, add_zero]
        intro ha0
        apply hv
        have hc0 : c v = 0 := by simpa [ha0] using h2
        simp [ha0, hc0]
  · filter_upwards [hev, a.2, b.2, c.2, d.2] with v hvdet ha hb hc hd
    rw [hx]
    rw [hdv] at hvdet
    have ha1 : Valued.v (a v) ≤ 1 := ha
    have hb1 : Valued.v (b v) ≤ 1 := hb
    have hc1 : Valued.v (c v) ≤ 1 := hc
    have hd1 : Valued.v (d v) ≤ 1 := hd
    simp only [xv]
    by_cases h1 : Valued.v (a v) = 1
    · rw [if_pos h1, zero_mul, add_zero]
      exact h1
    · have ha' : Valued.v (a v) < 1 := lt_of_le_of_ne ha1 h1
      have hcu : Valued.v (c v) = 1 := by
        by_contra hcu
        have hc' : Valued.v (c v) < 1 := lt_of_le_of_ne hc1 hcu
        have h3 : Valued.v (a v * d v - b v * c v) < 1 := by
          refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
          · rw [Valuation.map_mul]
            calc Valued.v (a v) * Valued.v (d v) ≤ Valued.v (a v) * 1 := mul_le_mul_right hd1 _
              _ = Valued.v (a v) := mul_one _
              _ < 1 := ha'
          · rw [Valuation.map_mul]
            calc Valued.v (b v) * Valued.v (c v) ≤ 1 * Valued.v (c v) := mul_le_mul_left hb1 _
              _ = Valued.v (c v) := one_mul _
              _ < 1 := hc'
        rw [hvdet] at h3
        exact lt_irrefl _ h3
      have hlt : Valued.v (a v) < Valued.v (c v) := by rw [hcu]; exact ha'
      have hsum : Valued.v (a v + c v) = 1 := by
        rw [Valuation.map_add_eq_of_lt_right _ hlt, hcu]
      have h2 : a v + c v ≠ 0 := by
        intro h0'
        rw [h0', Valuation.map_zero] at hsum
        exact zero_ne_one hsum
      rw [if_neg h1, if_pos h2, one_mul]
      exact hsum

set_option backward.isDefEq.respectTransparency false in

private theorem unimodGL2_stable_inf (a b c d : NumberField.InfiniteAdeleRing F)
    (hdet : IsUnit (a * d - b * c)) : ∃ x : NumberField.InfiniteAdeleRing F, IsUnit (a + x * c) := by
  classical
  rw [Pi.isUnit_iff] at hdet
  let x : NumberField.InfiniteAdeleRing F :=
    show ∀ v : NumberField.InfinitePlace F, v.Completion from fun v => if a v ≠ 0 then 0 else 1
  refine ⟨x, Pi.isUnit_iff.2 fun v => ?_⟩
  have hv : a v * d v - b v * c v ≠ 0 := isUnit_iff_ne_zero.1 (hdet v)
  rw [isUnit_iff_ne_zero]
  show a v + (if a v ≠ 0 then 0 else 1) * c v ≠ 0
  by_cases ha : a v = 0
  · rw [if_neg (not_not.2 ha), one_mul, ha, zero_add]
    intro hc
    apply hv
    rw [ha, hc]
    ring
  · rw [if_pos ha, zero_mul, add_zero]
    exact ha

set_option backward.isDefEq.respectTransparency false in

private theorem unimodGL2_stable_adele [NumberField F] (a b c d : NumberField.AdeleRing (𝓞 F) F)
    (hdet : IsUnit (a * d - b * c)) : ∃ x : NumberField.AdeleRing (𝓞 F) F, IsUnit (a + x * c) := by
  have h : IsUnit ((a.1 * d.1 - b.1 * c.1, a.2 * d.2 - b.2 * c.2) :
      NumberField.InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) := hdet
  rw [Prod.isUnit_iff] at h
  obtain ⟨x1, hx1⟩ := unimodGL2_stable_inf a.1 b.1 c.1 d.1 h.1
  obtain ⟨x2, hx2⟩ := unimodGL2_stable_fin a.2 b.2 c.2 d.2 h.2
  refine ⟨(x1, x2), ?_⟩
  show IsUnit ((a.1 + x1 * c.1, a.2 + x2 * c.2) :
    NumberField.InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  exact Prod.isUnit_iff.2 ⟨hx1, hx2⟩

end StableRange

section Adelic

variable (F : Type) [Field F] [NumberField F]

private theorem unimodGL2_modularCharacterFun_adelic
    (g : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (𝓞 F) F)) :
    Measure.modularCharacterFun g = 1 := by
  have hdet : IsUnit (g.val.det) := (Matrix.GeneralLinearGroup.det g).isUnit
  rw [Matrix.det_fin_two] at hdet
  obtain ⟨x, hx⟩ := unimodGL2_stable_adele _ _ _ _ hdet
  exact unimodGL2_delta_of_stable g x hx

end Adelic

attribute [local instance] NumberField.AdelicHaar.glBorel

open NumberField.AdelicHaar in
theorem solution (F : Type) [Field F] [NumberField F] :
    (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).Regular := by
    unfold adelicGLHaar
    infer_instance
  exact unimodGL2_isMulRightInvariant_of_modularCharacterFun _
    (unimodGL2_modularCharacterFun_adelic F)

end S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
end P2MW
export P2MW.S_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar (solution)
