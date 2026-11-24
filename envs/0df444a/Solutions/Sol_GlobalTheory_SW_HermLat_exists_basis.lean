-- Prove2me | solution 1 for GlobalTheory.SW.HermLat.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:40:11.685412+00:00
-- url     : https://prove2.me/submissions/6052693e-d1d4-4043-a517-3464b5260bc6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsIntegralBasisHermitianMatricesDual
import Theorems.Thm_GlobalTheory_SW_HermLat_form_eq
import Theorems.Thm_GlobalTheory_SW_HermLat_form_nondeg
import Theorems.Thm_GlobalTheory_SW_HermLat_exists_den
import Theorems.Thm_GlobalTheory_SW_HermLat_functional_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HermLat
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.HermLat
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ N R : ℕ, 0 < R → ∃ (m : ℕ) (β T : Fin m → Matrix (Fin N) (Fin N) E) (c : ℕ), 0 < c ∧ (∀ i, ccT (β i) = β i ∧ ccT (T i) = T i ∧ Den c (T i) ∧ ∃ y : Matrix (Fin N) (Fin N) E, IntM y ∧ ccT y = y ∧ β i = (R : E) • y) ∧ (∀ i j, ∑ τ : Ψ, τ.1 (T i * β j).trace = if i = j then 1 else 0) ∧ ∀ Z : CM Ψ N N, Z = fun τ => ∑ j, (∑ σ : Ψ, ((T j).map σ.1 * Z σ).trace) • (β j).map τ.1 := by
  intro E _ _ _ Ψ hΨ N R hR
  let b₀ := Module.finBasis ℚ (HermSub E N)
  obtain ⟨d, hd, hdi⟩ := exists_den (fun i => (b₀ i).1)
  have hu : ((R : ℚ) * d) ≠ 0 := by positivity
  let b := b₀.unitsSMul (fun _ => Units.mk0 _ hu)
  have hb : ∀ i, (b i).1 = (R : E) • ((d : E) • (b₀ i).1) := fun i => by
    simp only [b, Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0, Submodule.coe_smul]
    ext k l
    simp [Rat.smul_def, mul_assoc]
  let t := (form E N).dualBasis (form_nondeg hΨ N) b
  have ht : ∀ i j, form E N (t i) (b j) = if i = j then 1 else 0 := fun i j => by
    rw [LinearMap.BilinForm.apply_dualBasis_left]
    simp only [eq_comm]
  obtain ⟨c, hc, hci⟩ := exists_den (fun i => (t i).1)
  refine ⟨_, fun i => (b i).1, fun i => (t i).1, c, hc, fun i => ⟨(b i).2, (t i).2, hci i,
    _, hdi i, ?_, hb i⟩, fun i j => ?_, fun Z => ?_⟩
  · have : (d : E) • (b₀ i).1 = ((d : ℚ) • b₀ i).1 := by
      ext k l
      simp [Rat.smul_def]
    rw [this]
    exact ((d : ℚ) • b₀ i).2
  · rw [← form_eq hΨ, ht]
    split_ifs <;> simp
  · have hrep : ∀ (X : HermSub E N) j, b.repr X j = form E N (t j) X := fun X j => by
      conv_rhs => rw [← b.sum_repr X]
      simp only [map_sum, map_smul, ht, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
    funext τ
    ext k l
    let L : CM Ψ N N →ₗ[ℂ] ℂ :=
      { toFun := fun Z => Z τ k l -
          (∑ j, (∑ σ : Ψ, (((t j).1).map σ.1 * Z σ).trace) • ((b j).1).map τ.1) k l
        map_add' := fun Z W => by
          simp only [Pi.add_apply, Matrix.mul_add, trace_add, Finset.sum_add_distrib, add_smul,
            Matrix.add_apply]
          ring
        map_smul' := fun s Z => by
          simp only [Pi.smul_apply, Matrix.mul_smul, trace_smul, ← Finset.smul_sum, smul_assoc,
            Matrix.smul_apply, RingHom.id_apply, smul_sub] }
    have hL : L = 0 := functional_eq_zero hΨ L fun X => by
      have h1 : ∀ j, (∑ σ : Ψ, (((t j).1).map σ.1 * X.1.map σ.1).trace) =
          ((b.repr X j : ℚ) : ℂ) := fun j => by
        rw [hrep, form_eq hΨ]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← Matrix.map_mul, AddMonoidHom.map_trace]
      show τ.1 (X.1 k l) - (∑ j, (∑ σ : Ψ, (((t j).1).map σ.1 * X.1.map σ.1).trace) •
        ((b j).1).map τ.1) k l = 0
      simp only [h1]
      have h2 : X.1 = ∑ j, b.repr X j • (b j).1 := by
        conv_lhs => rw [← b.sum_repr X]
        simp only [Submodule.coe_sum, Submodule.coe_smul]
      rw [sub_eq_zero]
      conv_lhs => rw [h2]
      simp [Matrix.sum_apply, Rat.smul_def]
    exact sub_eq_zero.1 (LinearMap.congr_fun hL Z)
end GlobalTheory.SW.HermLat
