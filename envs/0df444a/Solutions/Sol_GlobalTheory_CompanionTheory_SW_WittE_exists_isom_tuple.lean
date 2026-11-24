-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.WittE.exists_isom_tuple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:20:57.794657+00:00
-- url     : https://prove2.me/submissions/26a5a82e-2224-4897-be52-2d22ad9d4f0a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WittExtensionGlobal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_IsIsom_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_exists_isom_of_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_form_lin_left
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_form_lin_right
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_lin_single
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_lin_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_lin_sub
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_lin_mem_span
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_exists_norm_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.WittE
variable {E V : Type} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  {σ : E →+* E}
namespace GlobalTheory.CompanionTheory.SW.WittE
theorem _root_.solution (B : V →ₛₗ[σ] V →ₗ[E] E) (hσ : ∀ x, σ (σ x) = x)
    (hB : ∀ x y, σ (B x y) = B y x) (h2 : (2 : E) ≠ 0) {n : ℕ} (k : ℕ) :
    ∀ X Y : Fin n → V, Module.finrank E (Submodule.span E (Set.range X)) = k →
      (∀ a b, B (X a) (X b) = B (Y a) (Y b)) →
      (∀ c : Fin n → E, (∀ a, B (X a) (lin X c) = 0) → lin X c = 0 ∧ lin Y c = 0) →
      ∃ γ : V →ₗ[E] V, IsIsom B γ ∧ ∀ a, γ (X a) = Y a := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro X Y hk hG hN
  by_cases hX : ∀ a b, B (X a) (X b) = 0
  · refine ⟨LinearMap.id, fun _ _ => rfl, fun a => ?_⟩
    have h := hN (Pi.single a (1 : E)) (fun b => by rw [lin_single]; exact hX b a)
    rw [lin_single, lin_single] at h
    simp [h.1, h.2]
  obtain ⟨c, hc⟩ := exists_norm_ne_zero B hB h2 X hX
  set x := lin X c with hx
  set y := lin Y c with hy
  have hXY : ∀ a, B x (X a) = B y (Y a) := by
    intro a
    rw [hx, hy, form_lin_left, form_lin_left]
    simp only [hG]
  have hxy : B x x = B y y := by
    calc B x x = ∑ a, c a * B x (X a) := form_lin_right B X c x
      _ = ∑ a, c a * B y (Y a) := by simp only [hXY]
      _ = B y y := (form_lin_right B Y c y).symm
  have hXY' : ∀ a, B (X a) x = B (Y a) y := by
    intro a
    rw [← hB x, ← hB y, hXY]
  set q := B x x with hq
  set t : Fin n → E := fun a => B x (X a) with ht
  set X' : Fin n → V := fun a => X a - (t a / q) • x with hX'
  set Y' : Fin n → V := fun a => Y a - (t a / q) • y with hY'
  have hty : ∀ a, B y (Y a) = t a := fun a => (hXY a).symm
  have hyy : B y y = q := hxy.symm
  have hx0 : ∀ a, B x (X' a) = 0 := by
    intro a
    have e : B x (X a) = t a := rfl
    simp only [hX', map_sub, map_smul, smul_eq_mul, e, ← hq]
    rw [div_mul_cancel₀ _ hc, sub_self]
  have hy0 : ∀ a, B y (Y' a) = 0 := by
    intro a
    simp only [hY', map_sub, map_smul, smul_eq_mul, hty, hyy]
    rw [div_mul_cancel₀ _ hc, sub_self]
  have hG' : ∀ a b, B (X' a) (X' b) = B (Y' a) (Y' b) := by
    intro a b
    simp only [hX', hY', map_sub, map_smul, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hG a b, hXY' a, hty, hyy]
    rw [← hq, show B x (X b) = t b from rfl]
  have hspan : Submodule.span E (Set.range X') < Submodule.span E (Set.range X) := by
    have hxm : x ∈ Submodule.span E (Set.range X) := lin_mem_span X c
    refine lt_of_le_of_ne ?_ ?_
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨a, rfl⟩) (Submodule.smul_mem _ _ hxm)
    · intro he
      rw [← he] at hxm
      have hz : ∀ w ∈ Submodule.span E (Set.range X'), B x w = 0 := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem w hw => obtain ⟨a, rfl⟩ := hw; exact hx0 a
        | zero => simp
        | add u v _ _ hu hv => simp [hu, hv]
        | smul s u _ hu => simp [hu]
      exact hc (hz x hxm)
  have hlt : Module.finrank E (Submodule.span E (Set.range X')) < k := by
    rw [← hk]
    exact Submodule.finrank_lt_finrank_of_lt hspan
  have hlinX : ∀ d : Fin n → E, lin X' d = lin X (d - ((∑ a, d a * t a) / q) • c) := by
    intro d
    rw [lin_sub, lin_smul, ← hx]
    simp only [lin, hX', smul_sub, Finset.sum_sub_distrib, smul_smul, ← Finset.sum_smul]
    congr 2
    simp only [Finset.sum_div, mul_div_assoc]
  have hlinY : ∀ d : Fin n → E, lin Y' d = lin Y (d - ((∑ a, d a * t a) / q) • c) := by
    intro d
    rw [lin_sub, lin_smul, ← hy]
    simp only [lin, hY', smul_sub, Finset.sum_sub_distrib, smul_smul, ← Finset.sum_smul]
    congr 2
    simp only [Finset.sum_div, mul_div_assoc]
  have hN' : ∀ d : Fin n → E, (∀ a, B (X' a) (lin X' d) = 0) → lin X' d = 0 ∧ lin Y' d = 0 := by
    intro d hd
    rw [hlinX, hlinY]
    apply hN
    intro a
    have h0 : B x (lin X' d) = 0 := by
      rw [form_lin_right]
      simp [hx0]
    have h1 := hd a
    have e : X' a = X a - (t a / q) • x := rfl
    rw [e] at h1
    simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [← hlinX]
    rw [h0, mul_zero, sub_zero] at h1
    exact h1
  obtain ⟨γ₁, i1, e1⟩ := ih _ hlt X' Y' rfl hG' hN'
  have hx1 : B (γ₁ x) (γ₁ x) = B y y := by rw [i1]; exact hxy
  obtain ⟨γ₂, i2, e2, f2⟩ := exists_isom_of_eq B hσ hB h2 (γ₁ x) y hx1
    (by rw [i1]; exact hc)
  refine ⟨γ₂ ∘ₗ γ₁, i2.comp i1, fun a => ?_⟩
  have hXa : X a = X' a + (t a / q) • x := by simp [hX']
  have hYa : Y a = Y' a + (t a / q) • y := by simp [hY']
  have hf : γ₂ (Y' a) = Y' a := f2 _ (by rw [← e1 a, i1]; exact hx0 a) (hy0 a)
  rw [LinearMap.comp_apply, hXa, map_add, map_smul, e1, map_add, map_smul, hf, e2, ← hYa]
end GlobalTheory.CompanionTheory.SW.WittE
