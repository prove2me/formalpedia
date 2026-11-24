-- Prove2me | solution 1 for GlobalTheory.AdLat.trivial_level_of_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:40:30.186801+00:00
-- url     : https://prove2.me/submissions/231cefad-3611-4b6f-a778-44011fccc517

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionSelfDualOfSelfDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralTmulOneMulMemAdelicCompletion
import Theorems.Thm_GlobalTheory_AdLat_Half_herm_sub_left
import Theorems.Thm_GlobalTheory_AdLat_Half_herm_sub_right
import Theorems.Thm_GlobalTheory_AdLat_Half_herm_smul_left
import Theorems.Thm_GlobalTheory_AdLat_Half_herm_smul_right
import Theorems.Thm_GlobalTheory_AdLat_Half_herm_mem_of_fv
import Theorems.Thm_P2M_GlobalTheory_AdLat_Half_fv_mem_hat__c076b46fc3eb
import Theorems.Thm_GlobalTheory_AdLat_hat_selfDual
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
open Half
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
namespace GlobalTheory.AdLat
namespace _root_.GlobalTheory.AdLat
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (c : E ≃ₐ[F] E)
    (G : Matrix (Fin n) (Fin n) E) (J : FractionalIdeal (𝓞 E)⁰ E)
    (g : GL (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) (M : ℕ) (I I' : Ideal (𝓞 E)), L.FG →
    Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ x, c (c x) = x) → (∀ a b, c (G a b) = G b a) →
    G.det ≠ 0 → J ≠ 0 → (∀ v : Fin n → E, (∀ y ∈ L, (∑ a, ∑ b, v a * G a b * c (y b)) ∈ J) ↔ v ∈ L) →
    (∀ x y, _root_.GlobalTheory.AdLat.hermA c G ((g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) *ᵥ x)
      ((g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) *ᵥ y) = _root_.GlobalTheory.AdLat.hermA c G x y) →
    0 < M → I ⊔ I' = ⊤ → I * I' = Ideal.span {(M : 𝓞 E)} →
    (∀ b ∈ I', ∃ b' ∈ I, ((b' : 𝓞 E) : E) = c (b : E)) →
    (∀ b ∈ I, ∀ z ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
      ∃ y ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
        (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) *ᵥ
          (fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) * z i) -
          (fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) * z i) = M • y) →
    ∀ z ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
      ∃ y ∈ (_root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))),
        (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) *ᵥ z - z = M • y := by
  intro F E _ _ _ _ _ n L c G J g M I I' hFG hspan hc hG hdet hJ hdual hg hM hsup hprod hcI hhalf
  set Lh := _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) with hLh
  generalize (g : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E)) = gm at hg hhalf ⊢
  let e : 𝓞 E → _root_.GlobalTheory.AdLat.RA F E :=
    fun b => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)
  have hh : ∀ b ∈ I, ∀ z ∈ Lh, ∃ y ∈ Lh, gm *ᵥ (e b • z) - e b • z = M • y := hhalf
  have hu : ∀ (r : _root_.GlobalTheory.AdLat.RA F E) (z : Fin n → _root_.GlobalTheory.AdLat.RA F E),
      gm *ᵥ (r • z) - r • z = r • (gm *ᵥ z - z) := fun r z => by
    rw [Matrix.mulVec_smul, smul_sub]
  have hM0 : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hnat : ∀ (m : ℕ) (v : Fin n → _root_.GlobalTheory.AdLat.RA F E),
      m • v = (algebraMap F (_root_.GlobalTheory.AdLat.RA F E) m) • v := fun m v => by
    rw [map_natCast, Nat.cast_smul_eq_nsmul]
  have hMcancel : ∀ x y : Fin n → _root_.GlobalTheory.AdLat.RA F E, M • x = M • y → x = y := by
    intro x y hxy
    rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at hxy
    exact smul_right_injective _ hM0 hxy
  have heM : e (M : 𝓞 E) = algebraMap F (_root_.GlobalTheory.AdLat.RA F E) M := by
    simp only [e, map_natCast]
    push_cast
    rw [← Algebra.TensorProduct.includeRight_apply, map_natCast]
  have hMI : (M : 𝓞 E) ∈ I := by
    have h1 : (M : 𝓞 E) ∈ Ideal.span {(M : 𝓞 E)} := Ideal.mem_span_singleton_self _
    rw [← hprod] at h1
    have h2 : I * I' ≤ I := Ideal.mul_le_left
    exact h2 h1

  have hstab : ∀ z ∈ Lh, gm *ᵥ z - z ∈ Lh := fun z hz => by
    obtain ⟨y, hy, hyz⟩ := hh _ hMI z hz
    rw [hu, heM, ← hnat] at hyz
    rw [hMcancel _ _ hyz]
    exact hy
  have hgL : ∀ z ∈ Lh, gm *ᵥ z ∈ Lh := fun z hz => by
    rw [← sub_add_cancel (gm *ᵥ z) z]
    exact add_mem (hstab z hz) hz
  have hpair : ∀ z ∈ Lh, ∀ w ∈ Lh,
      _root_.GlobalTheory.AdLat.hermA c G z w ∈ _root_.GlobalTheory.AdLat.hat1 F (J : Set E) :=
    fun z hz w hw => _root_.GlobalTheory.AdLat.Half.herm_mem_of_fv c G J L z
      ((_root_.GlobalTheory.AdLat.hat_selfDual F E n L c G J hFG hspan hc hG hdet hJ hdual z).2
        hz) w hw
  intro z hz
  obtain ⟨i, hi, i', hi', hii'⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ I ⊔ I')
  obtain ⟨b, hb, hbc⟩ := hcI i' hi'
  have he1 : e i + e i' = 1 := by
    have h1 : (i : E) + (i' : E) = 1 := by exact_mod_cast congrArg (fun x : 𝓞 E => (x : E)) hii'
    simp only [e, ← TensorProduct.tmul_add]
    rw [h1]
    rfl
  set w := gm *ᵥ z - z with hw
  obtain ⟨y₁, hy₁, hwy₁⟩ := hh i hi z hz
  rw [hu] at hwy₁
  set v : Fin n → _root_.GlobalTheory.AdLat.RA F E := ((M : F)⁻¹) • (e i' • w) with hv
  have hMv : M • v = e i' • w := by
    rw [hv, ← Nat.cast_smul_eq_nsmul F, smul_smul, mul_inv_cancel₀ hM0, one_smul]
  have hsg : _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (e b) = e i' := by
    simp only [e, _root_.GlobalTheory.AdLat.sg, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [AlgEquiv.coe_algHom, hbc, hc]
  have hvL : v ∈ Lh := by
    refine (_root_.GlobalTheory.AdLat.hat_selfDual F E n L c G J hFG hspan hc hG hdet hJ hdual v).1
      fun y hy => ?_
    set Y := _root_.GlobalTheory.AdLat.fv F y
    have hY : Y ∈ Lh := _root_.GlobalTheory.AdLat.Half.fv_mem_hat' (L : Set (Fin n → E)) y hy
    obtain ⟨y₂, hy₂, hY₂⟩ := hh b hb Y hY
    rw [hu] at hY₂
    have key : _root_.GlobalTheory.AdLat.hermA c G w Y =
        -_root_.GlobalTheory.AdLat.hermA c G (gm *ᵥ z) (gm *ᵥ Y - Y) := by
      rw [hw, _root_.GlobalTheory.AdLat.Half.herm_sub_left, _root_.GlobalTheory.AdLat.Half.herm_sub_right, ← hg z Y]
      ring
    have h2 : e i' * _root_.GlobalTheory.AdLat.hermA c G (gm *ᵥ z) (gm *ᵥ Y - Y) =
        algebraMap F (_root_.GlobalTheory.AdLat.RA F E) M * _root_.GlobalTheory.AdLat.hermA c G (gm *ᵥ z) y₂ := by
      rw [← hsg, ← _root_.GlobalTheory.AdLat.Half.herm_smul_right, hY₂, hnat,
        _root_.GlobalTheory.AdLat.Half.herm_smul_right, AlgHom.commutes]
    have h3 : _root_.GlobalTheory.AdLat.hermA c G v Y = -_root_.GlobalTheory.AdLat.hermA c G (gm *ᵥ z) y₂ := by
      rw [hv, algebra_compatible_smul (_root_.GlobalTheory.AdLat.RA F E),
        _root_.GlobalTheory.AdLat.Half.herm_smul_left, _root_.GlobalTheory.AdLat.Half.herm_smul_left, key, mul_neg,
        h2, mul_neg, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hM0, map_one, one_mul]
    rw [h3]
    exact neg_mem (hpair _ (hgL z hz) y₂ hy₂)
  refine ⟨y₁ + v, add_mem hy₁ hvL, ?_⟩
  calc w = e i • w + e i' • w := by rw [← add_smul, he1, one_smul]
    _ = M • (y₁ + v) := by rw [hwy₁, ← hMv, smul_add]
end _root_.GlobalTheory.AdLat
end GlobalTheory.AdLat
