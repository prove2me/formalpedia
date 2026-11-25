-- Prove2me | solution 1 for GlobalTheory.TorsionZero.ringKrullDim_cone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:04:55.565338+00:00
-- url     : https://prove2.me/submissions/f52e3ea8-6bc8-4add-93af-aad3a09636bf

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_NonemptyGradedAlgebraSubGrading
import Theorems.Thm_GlobalTheory_TorsionZero_aeval_mul_of_isHomogeneous
import Theorems.Thm_GlobalTheory_TorsionZero_exists_homogenisation
import Theorems.Thm_GlobalTheory_TorsionZero_aeval_eq_zero_iff_components
import Theorems.Thm_GlobalTheory_TorsionZero_aeval_cone_eq_zero_iff
import Theorems.Thm_GlobalTheory_TorsionZero_trdeg_eq_of_isAlgebraic
import Theorems.Thm_ReciprocityTheory_CA_exists_dim_trdeg_field
import Theorems.Thm_ReciprocityTheory_CA_ringKrullDim_eq_of_trdeg_eq_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TorsionZero
open MvPolynomial
variable {K σ : Type} [Field K]
namespace GlobalTheory.TorsionZero
theorem _root_.solution {T C : Type} [CommRing T] [IsDomain T] [Algebra K T]
    [Algebra.FiniteType K T] (𝒜 : ℕ → Submodule K T) [GradedAlgebra 𝒜] [Finite σ] {x : σ → T}
    (hx : ∀ j, x j ∈ 𝒜 1) [Algebra.IsIntegral (Algebra.adjoin K (Set.range x)) T]
    [CommRing C] [IsDomain C] [Algebra K C] (r : σ → C) (i : σ) (hi : r i = 1)
    (hr : Function.Surjective (aeval r : MvPolynomial σ K →ₐ[K] C))
    (hrel : ∀ n (G : MvPolynomial σ K), G.IsHomogeneous n → (aeval x G = 0 ↔ aeval r G = 0))
    (g : ℕ) (hg : ringKrullDim C = g) : ringKrullDim T = (g + 1 : ℕ) := by
  haveI : Algebra.FiniteType K C := Algebra.FiniteType.of_surjective _ hr
  obtain ⟨s, hs, hs'⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := K) (A := C)
  obtain rfl : s = g := by
    rw [hs] at hg
    exact_mod_cast hg
  refine ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field (K := K) _ ?_
  set cone : MvPolynomial σ K →ₐ[K] Polynomial C :=
    aeval (fun j => Polynomial.C (r j) * Polynomial.X) with hcone
  have hker : RingHom.ker (aeval x : MvPolynomial σ K →ₐ[K] T) = RingHom.ker cone := by
    ext G
    rw [RingHom.mem_ker, RingHom.mem_ker, aeval_eq_zero_iff_components 𝒜 hx, hcone,
      aeval_cone_eq_zero_iff]
    exact forall_congr' fun n => hrel n _ (homogeneousComponent_isHomogeneous n G)
  have e : (aeval x : MvPolynomial σ K →ₐ[K] T).range ≃ₐ[K] cone.range :=
    (Ideal.quotientKerEquivRange _).symm.trans
      ((Ideal.quotientEquivAlgOfEq K hker).trans (Ideal.quotientKerEquivRange _))
  have hX : Polynomial.X ∈ cone.range := ⟨X i, by simp [hcone, hi]⟩
  have key : ∀ p : Polynomial C, ∃ n : ℕ, Polynomial.X ^ n * p ∈ cone.range := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      refine ⟨a + b, ?_⟩
      have : Polynomial.X ^ (a + b) * (p + q) =
          Polynomial.X ^ b * (Polynomial.X ^ a * p) + Polynomial.X ^ a * (Polynomial.X ^ b * q) := by
        ring
      rw [this]
      exact add_mem (mul_mem (pow_mem hX _) ha) (mul_mem (pow_mem hX _) hb)
    | monomial d c =>
      obtain ⟨F, rfl⟩ := hr c
      obtain ⟨n, G, hG, hF⟩ := exists_homogenisation F i
      refine ⟨n, ?_⟩
      have h1 : cone G = Polynomial.C (aeval r F) * Polynomial.X ^ n := by
        rw [hcone, aeval_mul_of_isHomogeneous _ _ hG, ← hF C r hi]
        congr 1
        exact (comp_aeval_apply r (Polynomial.CAlgHom (R := K) (A := C)) _).symm
      have : Polynomial.X ^ n * Polynomial.monomial d (aeval r F) = cone G * Polynomial.X ^ d := by
        rw [h1, ← Polynomial.C_mul_X_pow_eq_monomial]; ring
      rw [this]
      exact mul_mem ⟨G, rfl⟩ (pow_mem hX _)
  haveI : Algebra.IsAlgebraic cone.range (Polynomial C) := ⟨fun p => by
    obtain ⟨n, hn⟩ := key p
    refine IsAlgebraic.of_smul (y := (⟨Polynomial.X ^ n, pow_mem hX n⟩ : cone.range))
      (mem_nonZeroDivisors_of_ne_zero fun h => ?_) ?_
    · exact pow_ne_zero n Polynomial.X_ne_zero (congrArg Subtype.val h)
    · exact isAlgebraic_algebraMap (⟨_, hn⟩ : cone.range)⟩
  rw [trdeg_eq_of_isAlgebraic (Algebra.adjoin K (Set.range x)), Algebra.adjoin_range_eq_range_aeval,
    e.trdeg_eq, ← trdeg_eq_of_isAlgebraic cone.range, ← trdeg_add_eq K C (A := Polynomial C), hs',
    Polynomial.trdeg_of_isDomain]
  simp
end GlobalTheory.TorsionZero
