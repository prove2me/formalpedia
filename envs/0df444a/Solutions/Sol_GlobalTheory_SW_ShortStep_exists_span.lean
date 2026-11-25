-- Prove2me | solution 1 for GlobalTheory.SW.ShortStep.exists_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:39:43.327401+00:00
-- url     : https://prove2.me/submissions/2d0e92d7-9e44-4445-92d8-b56b50dfe61d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSte
import Theorems.Thm_P2M_GlobalTheory_SW_ShortStep_li_of_mul__9c3b39fbd582
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ShortStep
open MinkowskiProductBounds
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
omit [IsCMField E]
namespace GlobalTheory.SW.ShortStep
theorem _root_.solution {n m : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
    (hn : n = m + Fintype.card κ) (R : Matrix κ (Fin n) E) (F : Matrix (Fin n) κ E)
    (h : R * F = 1) : ∃ (B : Matrix (Fin m) (Fin n) E) (S : Matrix (Fin n) (Fin m) E), IntM B ∧
      LinearIndependent E (fun i => B i) ∧ B * F = 0 ∧ S * B = 1 - F * R := by
  classical
  have hsurj : LinearMap.range F.vecMulLinear = ⊤ :=
    LinearMap.range_eq_top.2 fun y => ⟨y ᵥ* R, by simp [vecMul_vecMul, h]⟩
  have hr : Module.finrank E (LinearMap.ker F.vecMulLinear) = m := by
    have h1 := LinearMap.finrank_range_add_finrank_ker F.vecMulLinear
    rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card] at h1
    omega
  have hP : (1 - F * R) * F = 0 := by rw [Matrix.sub_mul, Matrix.mul_assoc, h]; simp
  generalize 1 - F * R = P at hP
  have hmem : ∀ i, P i ∈ LinearMap.ker F.vecMulLinear := fun i =>
    LinearMap.mem_ker.2 (congrFun hP i)
  have hker : ∀ x ∈ LinearMap.ker F.vecMulLinear, x ᵥ* F = 0 := fun x hx => LinearMap.mem_ker.1 hx
  generalize LinearMap.ker F.vecMulLinear = K at hr hmem hker
  let b := Module.finBasisOfFinrankEq E K hr
  let B : Matrix (Fin m) (Fin n) E := Matrix.of fun i => (b i).1
  have hBi : LinearIndependent E (fun i => B i) := by
    have := b.linearIndependent.map' K.subtype K.ker_subtype
    exact this
  have hBF : B * F = 0 := by ext i j; exact congrFun (hker _ (b i).2) j
  have hSB : (Matrix.of fun i j => b.repr ⟨_, hmem i⟩ j) * B = P := by
    ext i j
    have := congrFun (congrArg Subtype.val (b.sum_repr ⟨_, hmem i⟩)) j
    rw [Submodule.coe_sum, Finset.sum_apply] at this
    exact this
  generalize (Matrix.of fun i j => b.repr ⟨_, hmem i⟩ j) = S at hSB
  clear_value B
  obtain ⟨k, hk, hint⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : Fin m × Fin n => B p.1 p.2)
  have hk' : (k : E) ≠ 0 := by exact_mod_cast hk
  refine ⟨(k : E) • B, (k : E)⁻¹ • S, fun i j => ?_, ?_,
    by rw [Matrix.smul_mul, hBF, smul_zero], ?_⟩
  · simpa using hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
  · refine li_of_mul' hBi hk'
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hk', one_smul, hSB]
end GlobalTheory.SW.ShortStep
