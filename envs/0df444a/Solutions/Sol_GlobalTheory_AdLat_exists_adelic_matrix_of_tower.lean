-- Prove2me | solution 1 for GlobalTheory.AdLat.exists_adelic_matrix_of_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:47.034016+00:00
-- url     : https://prove2.me/submissions/f97e7e80-331c-468d-a466-b0ba11e0bf07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionLatticeSeparatedCompleteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealDivisibleEqZero
import Theorems.Thm_GlobalTheory_AdLat_lim_hat_induction
import Theorems.Thm_GlobalTheory_AdLat_lim_adele_smul_mem
import Theorems.Thm_GlobalTheory_AdLat_lim_fv_smul
import Theorems.Thm_GlobalTheory_AdLat_lim_int_smul_mem
import Theorems.Thm_GlobalTheory_AdLat_lim_nsmul_cancel
import Theorems.Thm_GlobalTheory_AdLat_lim_herm_fv
import Theorems.Thm_GlobalTheory_AdLat_lim_herm_mem
import Theorems.Thm_GlobalTheory_AdLat_adelicCompletionFractionalIdeal_divisible_eq_zero
import Theorems.Thm_GlobalTheory_AdLat_lim_eq_of_congr
import Theorems.Thm_GlobalTheory_AdLat_lim_exists_matrix
import Theorems.Thm_GlobalTheory_AdLat_cap_fv_add
import Theorems.Thm_GlobalTheory_AdLat_cap_fv_mem
import Theorems.Thm_GlobalTheory_AdLat_cap_fv_nsmul
import Theorems.Thm_GlobalTheory_AdLat_one_tmul_mem_adelicCompletionOfElementSet
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_T_adelicCompletion_lattice_separated_complete
import Theorems.Thm_GlobalTheory_T_adelicCompletion_rational_points_and_approximation
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
namespace GlobalTheory.AdLat
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L Λ : Submodule (𝓞 E) (Fin n → E)) (f : ℕ → (L →ₗ[𝓞 E] Λ)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → Λ.FG → Submodule.span E (Λ : Set (Fin n → E)) = ⊤ → (∀ N m : ℕ, 0 < N → 0 < m → ∀ a, ∃ v, f (N * m) a = f N a + N • v) → (∀ N : ℕ, 0 < N → (∀ a, (∃ v, f N a = N • v) ↔ ∃ v, a = N • v) ∧ ∀ a', ∃ a v, a' = f N a + N • v) → ∃ g : GL (Fin n) (RA F E), (g : Matrix (Fin n) (Fin n) (RA F E)).mulVec '' (hat F (L : Set (Fin n → E))) = (hat F (Λ : Set (Fin n → E))) ∧ (∀ N : ℕ, 0 < N → ∀ a : L, ∃ w ∈ (hat F (Λ : Set (Fin n → E))), (g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ fv F (a : Fin n → E) = fv F (f N a : Fin n → E) + N • w) ∧ ∀ (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (J : FractionalIdeal (𝓞 E)⁰ E), (∀ x ∈ Λ, ∀ y ∈ Λ, (∑ a, ∑ b, x a * G a b * c (y b)) ∈ J) → (∀ N : ℕ, 0 < N → ∀ x y : L, ∃ z ∈ J, (∑ a, ∑ b, (f N x : Fin n → E) a * G a b * c ((f N y : Fin n → E) b)) = (∑ a, ∑ b, (x : Fin n → E) a * G a b * c ((y : Fin n → E) b)) + N • z) → ∀ x y, hermA c G ((g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ x) ((g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ y) = hermA c G x y := by
  intro F E _ _ _ _ _ n L Λ f hL hLsp hΛ hΛsp hcomp hiso
  have hfv : ∀ (M : Submodule (𝓞 E) (Fin n → E)) (x : M), fv F (x : Fin n → E) ∈ hat F (M : Set (Fin n → E)) :=
    fun M x => cap_fv_mem F _ _ x.2

  have hlim : ∀ a : L, ∃ z ∈ hat F (Λ : Set (Fin n → E)), ∀ N : ℕ, 0 < N →
      ∃ w ∈ hat F (Λ : Set (Fin n → E)), z = fv F (f N a : Fin n → E) + N • w := by
    intro a
    refine (GlobalTheory.T.adelicCompletion_lattice_separated_complete F E n Λ hΛ).2 (fun N => fv F (f N a : Fin n → E)) (fun N => hfv Λ _) ?_
    intro N m hN hm
    obtain ⟨v, hv⟩ := hcomp N m hN hm a
    refine ⟨_, hfv Λ v, ?_⟩
    rw [hv, Submodule.coe_add, cap_fv_add, AddSubmonoidClass.coe_nsmul, cap_fv_nsmul]
  choose φ hφm hφ using hlim
  have hφadd : ∀ a b, φ (a + b) = φ a + φ b := by
    intro a b
    refine lim_eq_of_congr F Λ hΛ _ _ fun N hN => ?_
    obtain ⟨w, hw, e⟩ := hφ (a + b) N hN
    obtain ⟨w₁, hw₁, e₁⟩ := hφ a N hN
    obtain ⟨w₂, hw₂, e₂⟩ := hφ b N hN
    refine ⟨w - w₁ - w₂, sub_mem (sub_mem hw hw₁) hw₂, ?_⟩
    rw [e, e₁, e₂, map_add, Submodule.coe_add, cap_fv_add, smul_sub, smul_sub]
    abel
  have hφsmul : ∀ (r : 𝓞 E) (a : L),
      φ (r • a) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (r : E) : RA F E) • φ a := by
    intro r a
    refine lim_eq_of_congr F Λ hΛ _ _ fun N hN => ?_
    obtain ⟨w, hw, e⟩ := hφ (r • a) N hN
    obtain ⟨w₁, hw₁, e₁⟩ := hφ a N hN
    refine ⟨_, sub_mem hw (lim_int_smul_mem F Λ r hw₁), ?_⟩
    have : ((r • f N a : Λ) : Fin n → E) = (r : E) • (f N a : Fin n → E) := rfl
    rw [e, e₁, map_smul, this, lim_fv_smul, smul_sub, smul_add, smul_comm _ N]
    abel
  obtain ⟨g, hg⟩ := lim_exists_matrix F L hLsp (AddMonoidHom.mk' φ hφadd) hφsmul
  simp only [AddMonoidHom.mk'_apply] at hg
  have hgmem : ∀ z ∈ hat F (L : Set (Fin n → E)), g *ᵥ z ∈ hat F (Λ : Set (Fin n → E)) := by
    intro z hz
    refine lim_hat_induction F (fun z => g *ᵥ z ∈ hat F (Λ : Set (Fin n → E))) ?_ ?_ ?_ ?_ hz
    · simp
    · intro x y hx hy; rw [Matrix.mulVec_add]; exact add_mem hx hy
    · intro x hx; rw [Matrix.mulVec_neg]; exact neg_mem hx
    · intro a ha x hx
      rw [Matrix.mulVec_smul, hg ⟨x, hx⟩]
      exact lim_adele_smul_mem F a ha (hφm _)

  have hsurj0 : ∀ b : Λ, ∃ z ∈ hat F (L : Set (Fin n → E)), g *ᵥ z = fv F (b : Fin n → E) := by
    intro b
    have hex : ∀ N : ℕ, ∃ a : L, 0 < N → ∃ v, b = f N a + N • v := by
      intro N
      by_cases hN : 0 < N
      · obtain ⟨a, v, h⟩ := (hiso N hN).2 b
        exact ⟨a, fun _ => ⟨v, h⟩⟩
      · exact ⟨0, fun h => absurd h hN⟩
    choose h hh using hex
    obtain ⟨z, hz, hzN⟩ := (GlobalTheory.T.adelicCompletion_lattice_separated_complete F E n L hL).2 (fun N => fv F (h N : Fin n → E))
      (fun N => hfv L _) (by
        intro N m hN hm
        obtain ⟨v₁, e₁⟩ := hh N hN
        obtain ⟨v₂, e₂⟩ := hh (N * m) (Nat.mul_pos hN hm)
        obtain ⟨v₃, e₃⟩ := hcomp N m hN hm (h (N * m))
        obtain ⟨u, hu⟩ := ((hiso N hN).1 (h (N * m) - h N)).1 ⟨v₁ - m • v₂ - v₃, by
          have e₄ : f N (h (N * m)) = b - (N * m) • v₂ - N • v₃ := by
            rw [e₂, e₃]; abel
          have e₅ : f N (h N) = b - N • v₁ := by rw [e₁]; abel
          rw [map_sub, e₄, e₅, mul_smul, smul_sub, smul_sub]; abel⟩
        refine ⟨_, hfv L u, ?_⟩
        have : h (N * m) = h N + N • u := by rw [← hu]; abel
        rw [this, Submodule.coe_add, cap_fv_add, AddSubmonoidClass.coe_nsmul, cap_fv_nsmul])
    refine ⟨z, hz, lim_eq_of_congr F Λ hΛ _ _ fun N hN => ?_⟩
    obtain ⟨w, hw, e⟩ := hzN N hN
    obtain ⟨v, ev⟩ := hh N hN
    obtain ⟨w', hw', e'⟩ := hφ (h N) N hN
    refine ⟨w' + g *ᵥ w - fv F (v : Fin n → E), sub_mem (add_mem hw' (hgmem w hw)) (hfv Λ v), ?_⟩
    have eb : fv F (b : Fin n → E) = fv F (f N (h N) : Fin n → E) + N • fv F (v : Fin n → E) := by
      conv_lhs => rw [ev]
      rw [Submodule.coe_add, cap_fv_add, AddSubmonoidClass.coe_nsmul, cap_fv_nsmul]
    rw [e, eb, Matrix.mulVec_add, Matrix.mulVec_smul, hg, e', smul_sub, smul_add]
    abel
  have hsurj : ∀ y ∈ hat F (Λ : Set (Fin n → E)), ∃ z ∈ hat F (L : Set (Fin n → E)), g *ᵥ z = y := by
    intro y hy
    refine lim_hat_induction F (fun y => ∃ z ∈ hat F (L : Set (Fin n → E)), g *ᵥ z = y) ?_ ?_ ?_ ?_ hy
    · exact ⟨0, zero_mem _, by simp⟩
    · rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      exact ⟨x + y, add_mem hx hy, Matrix.mulVec_add _ _ _⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨-x, neg_mem hx, Matrix.mulVec_neg _ _⟩
    · intro a ha x hx
      obtain ⟨z, hz, e⟩ := hsurj0 ⟨x, hx⟩
      exact ⟨a • z, lim_adele_smul_mem F a ha hz, by rw [Matrix.mulVec_smul, e]⟩
  have hunit : IsUnit g := by
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    intro y
    obtain ⟨d, hd, hy⟩ := (GlobalTheory.T.adelicCompletion_rational_points_and_approximation F E n Λ hΛ hΛsp).2.2.2 y
    obtain ⟨z, -, e⟩ := hsurj _ hy
    refine ⟨(d : F)⁻¹ • z, ?_⟩
    rw [Matrix.mulVec_smul, e, ← Nat.cast_smul_eq_nsmul F, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hd.ne'), one_smul]
  obtain ⟨g, rfl⟩ := hunit
  refine ⟨g, ?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hgmem z hz
    · intro hy
      exact hsurj y hy
  · intro N hN a
    rw [hg]
    exact hφ a N hN
  intro c G J hJ hf
  let T : (Fin n → RA F E) →ₗ[FiniteAdeleRing (𝓞 F) F] (Fin n → RA F E) :=
    { toFun := (g : Matrix (Fin n) (Fin n) (RA F E)).mulVec
      map_add' := Matrix.mulVec_add _
      map_smul' := fun a x => Matrix.mulVec_smul _ a x }
  let B := (hermBil F c G).compl₁₂ T T - hermBil F c G
  have hB0 : ∀ x y : L, B (fv F (x : Fin n → E)) (fv F (y : Fin n → E)) = 0 := by
    intro x y
    refine adelicCompletionFractionalIdeal_divisible_eq_zero F J _ fun N hN => ?_
    obtain ⟨z, hz, e⟩ := hf N hN x y
    obtain ⟨w₁, hw₁, e₁⟩ := hφ x N hN
    obtain ⟨w₂, hw₂, e₂⟩ := hφ y N hN
    refine ⟨(1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] z + hermBil F c G (fv F (f N x : Fin n → E)) w₂ +
      hermBil F c G w₁ (φ y), add_mem (add_mem (one_tmul_mem_adelicCompletionOfElementSet F hz)
        (lim_herm_mem F c G hJ (hfv Λ _) hw₂)) (lim_herm_mem F c G hJ hw₁ (hφm y)), ?_⟩
    have : B (fv F (x : Fin n → E)) (fv F (y : Fin n → E)) = hermBil F c G (φ x) (φ y) -
        hermBil F c G (fv F (x : Fin n → E)) (fv F (y : Fin n → E)) := by
      rw [← hg, ← hg]; rfl
    rw [this, e₁, map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply]
    have e₃ : hermBil F c G (fv F (f N x : Fin n → E)) (φ y) =
        hermBil F c G (fv F (x : Fin n → E)) (fv F (y : Fin n → E)) +
          N • (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] z +
          N • hermBil F c G (fv F (f N x : Fin n → E)) w₂ := by
      rw [e₂, map_add, map_nsmul, lim_herm_fv, lim_herm_fv, e, TensorProduct.tmul_add,
        TensorProduct.tmul_smul]
    rw [e₃, smul_add, smul_add]
    abel
  have hB1 : ∀ x ∈ hat F (L : Set (Fin n → E)), ∀ y ∈ hat F (L : Set (Fin n → E)), B x y = 0 := by
    intro x hx y hy
    refine lim_hat_induction F (fun x => B x y = 0) ?_ ?_ ?_ ?_ hx
    · simp only [map_zero, LinearMap.zero_apply]
    · intro x y hx hy; rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    · intro x hx; rw [map_neg, LinearMap.neg_apply, hx, neg_zero]
    intro a ha x hx
    refine lim_hat_induction F (fun y => B (a • fv F x) y = 0) ?_ ?_ ?_ ?_ hy
    · simp only [map_zero]
    · intro x y hx hy; rw [map_add, hx, hy, add_zero]
    · intro x hx; rw [map_neg, hx, neg_zero]
    intro b hb y hy
    rw [map_smul, map_smul, LinearMap.smul_apply, hB0 ⟨x, hx⟩ ⟨y, hy⟩, smul_zero, smul_zero]
  intro x y
  obtain ⟨d, hd, hx⟩ := (GlobalTheory.T.adelicCompletion_rational_points_and_approximation F E n L hL hLsp).2.2.2 x
  obtain ⟨e, he, hy⟩ := (GlobalTheory.T.adelicCompletion_rational_points_and_approximation F E n L hL hLsp).2.2.2 y
  have h1 := hB1 _ hx _ hy
  rw [map_nsmul, map_nsmul, LinearMap.smul_apply, smul_smul, ← smul_zero (e * d)] at h1
  have h2 := lim_nsmul_cancel F (Nat.mul_pos he hd) h1
  exact sub_eq_zero.mp h2
end GlobalTheory.AdLat
