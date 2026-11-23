-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.exists_basis_of_image
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:22.366684+00:00
-- url     : https://prove2.me/submissions/4998e4b2-3a7a-4c9d-a4c1-91c821de2b65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal
open scoped nonZeroDivisors UpperHalfPlane ComplexConjugate
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
variable (h2 : finrank ℚ K = 2) (hD : discr K = -d) (σ : K →+* ℂ)
include h2 hD
omit h2 hD
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {ω : ℂ} {τ : ℍ} (hω : ω ≠ 0)
    (h : ∀ z, z ∈ σ '' 𝔞 ↔ ∃ m n : ℤ, ω * (m * (τ : ℂ) + n) = z) :
    ∃ b : Basis (Fin 2) ℤ (𝔞 : Submodule (𝓞 K) K), σ (b 0) = ω * τ ∧ σ (b 1) = ω := by
  obtain ⟨α, hα, eα⟩ := (h (ω * τ)).2 ⟨1, 0, by simp⟩
  obtain ⟨β, hβ, eβ⟩ := (h ω).2 ⟨0, 1, by simp⟩
  let v : Fin 2 → (𝔞 : Submodule (𝓞 K) K) := ![⟨α, hα⟩, ⟨β, hβ⟩]
  have hi : LinearIndependent ℤ v := by
    rw [LinearIndependent.pair_iff]
    intro m n e
    have e1 := congrArg (fun x : (𝔞 : Submodule (𝓞 K) K) => σ x) e
    simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, zsmul_eq_mul, map_add, map_mul,
      map_intCast, eα, eβ, Submodule.coe_zero, map_zero] at e1
    have e2 : (m * τ + n : ℂ) = 0 := mul_left_cancel₀ hω (by linear_combination e1)
    have e3 : m = 0 := by simpa [τ.im_ne_zero] using congrArg Complex.im e2
    exact ⟨e3, by simpa [e3] using e2⟩
  have hs : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨m, n, e⟩ := (h (σ x)).1 ⟨x, hx, rfl⟩
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![m, n], Subtype.ext (σ.injective ?_)⟩
    simp [v, eα, eβ, ← e]
    ring
  exact ⟨Basis.mk hi hs, by simp [v, eα], by simp [v, eβ]⟩
end GlobalTheory.QuadraticZeta
