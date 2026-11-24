-- Prove2me | solution 1 for GlobalTheory.exists_finite_unitary_classes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:59:54.759573+00:00
-- url     : https://prove2.me/submissions/ae343906-5948-44b4-ae4f-2bb2e2233dd9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteRepresentatives_c0b95eec68dc9003
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteUnitaryClassesOfDualEqSmul_87ddafdad67ddc06
import Theorems.Thm_GlobalTheory_exists_sesquilinear_eq_herm
import Theorems.Thm_GlobalTheory_HermClass_exists_finite_classes


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.MultiplicativeHeights
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory
theorem _root_.solution (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (hdet : G.det ≠ 0) {N : ℤ} (hN : N ≠ 0)
    {𝔪 : Ideal (𝓞 E)} (h𝔪 : 𝔪 ≠ ⊥) {α : Type*} {ι : Type*} [Finite ι]
    (Λ : α → Submodule (𝓞 E) (Fin r → E)) (t : α → ι → Fin r → E)
    (hΛ : ∀ a, IsLattice (Λ a))
    (hint : ∀ a, ∀ x ∈ Λ a, ∀ y ∈ Λ a, IsIntegral ℤ ((N : E) * herm G x y))
    (hdual : ∀ a x, (∀ y ∈ Λ a, IsIntegral ℤ (herm G x y)) → (N : E) • x ∈ Λ a)
    (ht : ∀ a i, t a i ∈ Λ a) :
    ∃ S : Set α, S.Finite ∧ ∀ a, ∃ s ∈ S, ∃ γ : GL (Fin r) E,
      (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) =
        herm G x y) ∧
      (∀ x, x ∈ Λ a ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ Λ s) ∧
      ∀ i, (γ : Matrix (Fin r) (Fin r) E) *ᵥ t a i - t s i ∈ 𝔪 • Λ s := by
  classical
  have hc : ∀ x : E, cc x = star x := fun _ => rfl
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN
  obtain ⟨h, hh⟩ := exists_sesquilinear_eq_herm G
  have hs : ∀ x y, h y x = star (h x y) := fun x y => by
    simp only [hh, herm, star_sum, star_mul', ← hc (G _ _), hG, hc, star_star]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hnd : ∀ y, (∀ x, h y x = 0) → y = 0 := fun y hy => by
    refine Matrix.eq_zero_of_vecMul_eq_zero hdet (funext fun b => ?_)
    have := hy (Pi.single b 1)
    rw [hh, herm, Finset.sum_comm, Finset.sum_eq_single b] at this
    · simpa [hc, Matrix.vecMul, dotProduct] using this
    · intro b' _ hb; simp [hc, hb]
    · simp
  have hm : (Ideal.absNorm 𝔪 : ℤ) ≠ 0 := by
    exact_mod_cast fun h0 => h𝔪 (Ideal.absNorm_eq_zero_iff.1 h0)
  obtain ⟨S, hS, H⟩ := HermClass.exists_finite_classes ((N : E) • h)
    (fun x y => by simp [hs x y]) (fun y hy => hnd y fun x => by simpa [hN'] using hy x)
    (mul_ne_zero hN hN) hm (fun a => (Λ a).restrictScalars ℤ) t
    (fun a => by
      have : Module.Finite (𝓞 E) (Λ a) := Module.Finite.iff_fg.2 (hΛ a).1
      exact Module.Finite.iff_fg.1 (Module.Finite.trans (R := ℤ) (𝓞 E) (Λ a)))
    (fun a => (hΛ a).2) (fun a c hc x hx => (Λ a).smul_mem (⟨c, hc⟩ : 𝓞 E) hx)
    (fun a x hx y hy => by simpa [hh] using hint a x hx y hy)
    (fun a x hx => by
      rw [Int.cast_mul, mul_smul]
      exact hdual a _ fun y hy => by simpa [← hh] using hx y hy) ht
  refine ⟨S, hS, fun a => ?_⟩
  obtain ⟨s, hsS, γ, h1, h2, h3⟩ := H a
  let g : GL (Fin r) E := ⟨LinearMap.toMatrix' γ.toLinearMap, LinearMap.toMatrix' γ.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  have hg : ∀ x, (g : Matrix (Fin r) (Fin r) E) *ᵥ x = γ x := fun x =>
    LinearMap.toMatrix'_mulVec γ.toLinearMap x
  refine ⟨s, hsS, g, fun x y => ?_, fun x => ?_, fun i => ?_⟩
  · simpa [hg, hh, hN'] using h1 x y
  · rw [hg]; exact h2 x
  · obtain ⟨y, hy, he⟩ := h3 i
    rw [hg, he, natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul (Ideal.absNorm_mem 𝔪) hy
end GlobalTheory
