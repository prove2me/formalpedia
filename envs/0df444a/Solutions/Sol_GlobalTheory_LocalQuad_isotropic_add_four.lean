-- Prove2me | solution 1 for GlobalTheory.LocalQuad.isotropic_add_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:38:57.098146+00:00
-- url     : https://prove2.me/submissions/1cb4e8ac-c5e1-4e41-aabd-22d77559203c

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuaternaryOfCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitValuedTernaryLtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroFiveOfValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsForallAbvSubLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRingHomAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometricCm
import Theorems.Thm_GlobalTheory_LocalQuad_isotropic_ternary_of_units
import Theorems.Thm_GlobalTheory_LocalQuad_isotropic_four
import Theorems.Thm_GlobalTheory_LocalQuad_exists_value_isSquare_div
import Theorems.Thm_GlobalTheory_LocalQuad_finite_setOf_valued_ne_one
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_LocalQuad_exists_value_isotropic
import Theorems.Thm_GlobalTheory_LocalQuad_isotropic_of_injective
import Theorems.Thm_GlobalTheory_LocalQuad_isotropic_succ_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.Inertia.negIndex_neg
attribute [local simp] GlobalTheory.Inertia.posIndex_neg



set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
namespace GlobalTheory.LocalQuad
theorem _root_.solution (H : GlobalTheory.Published.HasseNormSt) (F : Type) [Field F] [NumberField F] (n : ℕ)
    (a : Fin (n + 4) → F) (ha : ∀ i, a i ≠ 0)
    (hr : ∀ σ : F →+* ℝ, ∃ x : Fin (n + 4) → ℝ, x ≠ 0 ∧ ∑ i, σ (a i) * x i ^ 2 = 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : Fin (n + 4) → v.adicCompletion F, x ≠ 0 ∧
      ∑ i, algebraMap F (v.adicCompletion F) (a i) * x i ^ 2 = 0) :
    ∃ x : Fin (n + 4) → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  induction n with
  | zero => exact isotropic_four H F a ha hr hf
  | succ n ih =>
    classical
    have split : ∀ (k : Type) [Field k] (φ : F →+* k),
        (∃ x : Fin (n + 1 + 4) → k, x ≠ 0 ∧ ∑ i, φ (a i) * x i ^ 2 = 0) →
        ∃ x y : k, φ (a 0) * x ^ 2 + φ (a 1) * y ^ 2 ≠ 0 ∧
          ∀ μ : F, IsSquare (φ μ / (φ (a 0) * x ^ 2 + φ (a 1) * y ^ 2)) →
          ∃ x : Fin (n + 4) → k, x ≠ 0 ∧
            ∑ i, φ ((Fin.cons μ fun j : Fin (n + 3) => a j.succ.succ : Fin (n + 4) → F) i) * x i ^ 2
              = 0 := by
      rintro k _ φ ⟨x, hx, h⟩
      haveI : CharZero k := (RingHom.charZero_iff φ.injective).1 inferInstance
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at h
      obtain ⟨X, Y, hXY, H⟩ := exists_value_isotropic (a := φ (a 0)) (a' := φ (a 1))
        (b := fun j : Fin (n + 2 + 1) => φ (a j.succ.succ)) (by simpa using ha 0)
        (by simpa using ha 1) (by simpa using ha _) (x := x 0) (y := x 1)
        (z := fun j => x j.succ.succ) (by
          by_contra hc
          push Not at hc
          apply hx
          funext i
          refine Fin.cases hc.1 (fun j => Fin.cases hc.2.1 (fun l => congrFun hc.2.2 l) j) i) h
      refine ⟨X, Y, hXY, fun μ hμ => ?_⟩
      refine (isotropic_succ_iff (n := n + 3)).2 ?_
      simpa using H _ hμ
    let e : Fin 3 → Fin (n + 3) := Fin.natAdd n
    have hT := (finite_setOf_valued_ne_one F (two_ne_zero (α := F))).union
      (Set.finite_iUnion fun i : Fin 3 => finite_setOf_valued_ne_one F (ha (e i).succ.succ))
    choose p q hpq hp using fun v : hT.toFinset => split _ _ (hf v.1)
    choose p' q' hpq' hp' using fun σ : F →+* ℝ => split _ _ (hr σ)
    obtain ⟨x, y, h0, h1, h2⟩ := exists_value_isSquare_div F (a' := a 1) (ha 0) _ p q hpq p' q' hpq'
    obtain ⟨t, z, hz0, hz⟩ := (isotropic_succ_iff (n := n + 3)).1 (ih
      (Fin.cons (a 0 * x ^ 2 + a 1 * y ^ 2) fun j : Fin (n + 3) => a j.succ.succ)
      (fun i => Fin.cases h0 (fun j => ha _) i) (fun σ => hp' σ _ (h2 σ)) (fun v => by
        by_cases hv : v ∈ hT.toFinset
        · exact hp ⟨v, hv⟩ _ (h1 ⟨v, hv⟩)
        · simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion,
            not_or, not_exists, not_not] at hv
          refine isotropic_of_injective (fun i => (e i).succ)
            ((Fin.succ_injective _).comp (Fin.natAdd_injective _ _)) ?_
          exact isotropic_ternary_of_units F v (by simpa only [map_ofNat] using hv.1) _ hv.2))
    simp only [Fin.cons_zero, Fin.cons_succ] at hz
    refine (isotropic_succ_iff (n := n + 4)).2 ⟨x * t, Fin.cons (y * t) z, ?_, ?_⟩
    · by_contra hc
      push Not at hc
      obtain ⟨hx, hy⟩ := hc
      have hy0 : y * t = 0 := by simpa using congrFun hy 0
      rcases hz0 with ht | hz0
      · rw [mul_eq_zero_iff_right ht] at hx hy0
        simp [hx, hy0] at h0
      · exact hz0 (funext fun i => by simpa using congrFun hy i.succ)
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_zero_eq_one]
      linear_combination hz
end GlobalTheory.LocalQuad
