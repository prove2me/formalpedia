-- Prove2me | solution 1 for GlobalTheory.CongruenceDet.isIntegral_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:59.446888+00:00
-- url     : https://prove2.me/submissions/9364be16-4d32-44cf-8575-cba579ad9ae0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralDetSubOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CongruenceDet
open NumberField Matrix
open scoped nonZeroDivisors
namespace GlobalTheory.CongruenceDet
namespace _root_.GlobalTheory.CongruenceDet
theorem _root_.solution {R E K : Type} [CommRing R] [Field E]
    [Field K] [CharZero K]
    [Algebra R E] [Algebra R K] [Algebra E K] [IsScalarTower R E K] {r M : ℕ} (hM : M ≠ 0)
    (Λ : Submodule R (Fin r → E)) (g : Matrix (Fin r) (Fin r) E) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hg : ∀ v ∈ Λ, ∃ w ∈ Λ, g *ᵥ v = v + M • w) (μ : K)
    (hμ : (g.map (algebraMap E K)).charpoly.IsRoot μ) :
    IsIntegral R ((μ - 1) / M) := by
  classical
  have hdet : (scalar (Fin r) μ - g.map (algebraMap E K)).det = 0 := by
    rw [← Matrix.eval_charpoly]
    exact hμ
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  have hug : u ᵥ* g.map (algebraMap E K) = μ • u := by
    rw [Matrix.vecMul_sub, sub_eq_zero] at hu
    rw [← hu]
    ext i
    simp [Matrix.scalar_apply, Matrix.vecMul_diagonal, mul_comm]
  let ℓE : (Fin r → E) →ₗ[E] K :=
    ∑ i, u i • ((Algebra.linearMap E K).comp (LinearMap.proj i))
  have hℓE : ∀ v, ℓE v = u ⬝ᵥ (algebraMap E K ∘ v) := by
    intro v
    simp [ℓE, dotProduct]
  let ℓ : (Fin r → E) →ₗ[R] K := ℓE.restrictScalars R
  have hℓ : ∀ v, ℓ v = u ⬝ᵥ (algebraMap E K ∘ v) := hℓE
  have hMK : (M : K) ≠ 0 := by exact_mod_cast hM
  have hstep : ∀ v ∈ Λ, ∃ w ∈ Λ, ((μ - 1) / M) * ℓ v = ℓ w := by
    intro v hv
    obtain ⟨w, hw, hgv⟩ := hg v hv
    refine ⟨w, hw, ?_⟩
    have hmap : algebraMap E K ∘ (g *ᵥ v) = g.map (algebraMap E K) *ᵥ (algebraMap E K ∘ v) := by
      funext k
      exact RingHom.map_mulVec _ _ _ k
    have h1 : ℓ (g *ᵥ v) = μ * ℓ v := by
      rw [hℓ, hℓ, hmap, Matrix.dotProduct_mulVec, hug, smul_dotProduct, smul_eq_mul]
    have h2 : ℓ (g *ᵥ v) = ℓ v + M * ℓ w := by
      rw [hgv, map_add, map_nsmul, nsmul_eq_mul]
    field_simp
    linear_combination h1.symm.trans h2
  let N : Submodule R K := Λ.map ℓ
  have hN : N ≠ ⊥ := by
    intro hbot
    have hker : Submodule.span E (Λ : Set (Fin r → E)) ≤ LinearMap.ker ℓE := by
      rw [Submodule.span_le]
      intro v hv
      have : ℓ v ∈ N := Submodule.mem_map_of_mem hv
      rw [hbot, Submodule.mem_bot] at this
      exact this
    rw [hspan] at hker
    apply hu0
    funext j
    have := hker (Submodule.mem_top (x := Pi.single j 1))
    rw [LinearMap.mem_ker, hℓE] at this
    simpa [dotProduct, Pi.single_apply] using this
  refine isIntegral_of_smul_mem_submodule N hN (hfg.map ℓ) _ ?_
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨w, hw, hvw⟩ := hstep v hv
  rw [smul_eq_mul, hvw]
  exact Submodule.mem_map_of_mem hw
end _root_.GlobalTheory.CongruenceDet
end GlobalTheory.CongruenceDet
