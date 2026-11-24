-- Prove2me | solution 1 for GlobalTheory.exists_finset_boundedBasis_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:42:42.286892+00:00
-- url     : https://prove2.me/submissions/054218bc-3180-491c-b601-fcc2058fbaf0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases
import Theorems.Thm_GlobalTheory_BoundedBasis_exists_generators_mod_smul
import Theorems.Thm_GlobalTheory_BoundedBasis_exists_finset_representatives
import Theorems.Thm_GlobalTheory_BoundedBasis_card_quotient_range_vecMulLinear
import Theorems.Thm_GlobalTheory_BoundedBasis_natAbs_norm_le_pow
import Theorems.Thm_GlobalTheory_BoundedBasis_norm_det_le_pow
import Theorems.Thm_GlobalTheory_BoundedBasis_finrank_eq_two_mul_fdeg
import Theorems.Thm_GlobalTheory_BoundedBasis_det_gramOf_ne_zero
import Theorems.Thm_GlobalTheory_BoundedBasis_pairing_injective
import Theorems.Thm_GlobalTheory_BoundedBasis_exists_mem_of_pairing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
open BoundedBasis
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory
theorem _root_.solution (X : DataX E r) {B : ℝ} (hB : 0 ≤ B)
    (A : Matrix (Fin r) (Fin r) (𝓞 E)) :
    ∃ V : Finset (Fin r → Fin r → E), (∀ v ∈ V, IsBoundedBasis X B v) ∧
      (∀ v, IsBoundedBasis X B v → gramOf X.Gm v = A.map (algebraMap (𝓞 E) E) →
        ∃ γ ∈ X.Γ, ∃ w ∈ V, ∀ i, v i = (γ : Matrix (Fin r) (Fin r) E) *ᵥ w i) ∧
      (V.card : ℝ) ≤ ((X.NA : ℝ) * X.NC * X.g * r * B) ^ (2 * fdeg E * r ^ 2) := by
  classical
  let S : Set (Fin r → Fin r → E) :=
    {v | IsBoundedBasis X B v ∧ gramOf X.Gm v = A.map (algebraMap (𝓞 E) E)}
  rcases S.eq_empty_or_nonempty with hS | ⟨u, hu, huA⟩
  · refine ⟨∅, by simp, fun v hv hA => ?_, by simp; positivity⟩
    exact absurd (show v ∈ S from ⟨hv, hA⟩) (by simp [hS])
  set n : ℕ := X.NA * X.NC * X.g with hn
  have hn0 : n ≠ 0 := (Nat.mul_pos (Nat.mul_pos X.NA_pos X.NC_pos) X.g_pos).ne'
  set N : Matrix (Fin r) (Fin r) (𝓞 E) := (n : 𝓞 E) • A with hN
  have hA : A.det ≠ 0 := by
    intro h0
    apply det_gramOf_ne_zero X.Gm_det hu.2.1
    rw [huA, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have hN0 : N.det ≠ 0 := by
    rw [hN, det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hn0)) hA
  have hcard := card_quotient_range_vecMulLinear N hN0
  have hbound : ((Algebra.norm ℤ N.det).natAbs : ℝ) ≤ ((r * (n * B)) ^ r) ^ finrank ℚ E := by
    refine natAbs_norm_le_pow fun σ => ?_
    have h1 : σ ((N.det : 𝓞 E) : E) = (N.map (σ.comp (algebraMap (𝓞 E) E))).det :=
      RingHom.map_det (σ.comp (algebraMap (𝓞 E) E)) N
    rw [h1]
    refine norm_det_le_pow _ (by positivity) fun i k => ?_
    have h2 : algebraMap (𝓞 E) E (A i k) = herm X.Gm (u i) (u k) :=
      (congrFun (congrFun huA i) k).symm
    simp only [hN, map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast,
      RingHom.comp_apply, h2, norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hu.2.2 σ i k) (by positivity)
  have : Finite ((Fin r → 𝓞 E) ⧸ LinearMap.range N.vecMulLinear) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard, Int.natAbs_ne_zero, Algebra.norm_ne_zero_iff]
    exact hN0
  obtain ⟨x, hx⟩ := exists_generators_mod_smul hN0 r X.Λ _ (pairing_injective X hu.1 hu.2.1)
  obtain ⟨V, hV, hV'⟩ := exists_finset_representatives S fun v j =>
    (LinearMap.range N.vecMulLinear).mkQ (pairing X v.1 v.2.1.1 (x j))
  refine ⟨V.image Subtype.val, ?_, fun v hv hvA => ?_, ?_⟩
  · intro v hv
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hv
    exact w.2.1
  · obtain ⟨w, hwV, hw⟩ := hV' ⟨v, hv, hvA⟩
    obtain ⟨γ, hγ, h⟩ := exists_mem_of_pairing X hv.1 w.2.1.1 hv.2.1 w.2.1.2.1 A hvA w.2.2
      fun m => by
        obtain ⟨c, m', rfl⟩ := hx m
        rw [map_add, map_add, add_sub_add_comm, map_sum, map_sum, ← Finset.sum_sub_distrib,
          map_smul, map_smul, ← smul_sub]
        refine add_mem (Submodule.sum_mem _ fun j _ => ?_) ⟨(pairing X w.1 w.2.1.1 m' -
          pairing X v hv.1 m') ᵥ* N.adjugate, ?_⟩
        · rw [map_smul, map_smul, ← smul_sub]
          exact Submodule.smul_mem _ _ ((Submodule.Quotient.eq _).1 (congrFun hw j))
        · rw [vecMulLinear_apply, vecMul_vecMul, adjugate_mul, vecMul_smul, vecMul_one]
    exact ⟨γ, hγ, w.1, Finset.mem_image_of_mem _ hwV, h⟩
  · rw [Nat.card_fun, hcard, Nat.card_eq_fintype_card, Fintype.card_fin] at hV
    calc ((V.image Subtype.val).card : ℝ) ≤ ((Algebra.norm ℤ N.det).natAbs : ℝ) ^ r := by
          exact_mod_cast Finset.card_image_le.trans hV
      _ ≤ (((r * (n * B)) ^ r) ^ finrank ℚ E) ^ r := by gcongr
      _ = _ := by
          rw [← pow_mul, ← pow_mul, finrank_eq_two_mul_fdeg, hn]
          push_cast
          congr 1 <;> ring
end GlobalTheory
