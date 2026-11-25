-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.conj_mem_integralGL_of_conj_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:04:17.31306+00:00
-- url     : https://prove2.me/submissions/2b92ed0e-d26f-42de-b36d-66293590aa70

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_transvectionGL_mem
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_mem_integralMatrices


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Topology Filter Set
open scoped Pointwise Matrix
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution {g : GL (Fin n) F}
    (hg : ∀ k ∈ integralGL F n, g⁻¹ * k * g ∈ integralGL F n) {k : GL (Fin n) F}
    (hk : k ∈ integralGL F n) : g * k * g⁻¹ ∈ integralGL F n := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · exact (mem_integralGL_iff F n).mpr ⟨fun i => isEmptyElim i, fun i => isEmptyElim i⟩
  set A : Matrix (Fin n) (Fin n) F := (g : Matrix (Fin n) (Fin n) F) with hAdef
  set B : Matrix (Fin n) (Fin n) F := ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    with hBdef
  have hAB : A * B = 1 := Units.mul_inv g
  have hBA : B * A = 1 := Units.inv_mul g
  obtain ⟨⟨j₀, k₀⟩, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun p : Fin n × Fin n => valuation F (A p.1 p.2)) Finset.univ_nonempty
  set a := A j₀ k₀ with ha_def
  have hmax' : ∀ i j, valuation F (A i j) ≤ valuation F a := fun i j =>
    hmax (i, j) (Finset.mem_univ _)
  have ha : a ≠ 0 := by
    intro h0
    have hA0 : A = 0 := Matrix.ext fun i j => by
      have := hmax' i j
      rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
      exact this
    have := congrFun (congrFun hAB j₀) j₀
    rw [hA0, zero_mul, Matrix.zero_apply, Matrix.one_apply_eq] at this
    exact zero_ne_one this
  have hva : 0 < valuation F a := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr ha)

  have hconj : ∀ k ∈ integralGL F n, B * (k : Matrix (Fin n) (Fin n) F) * A ∈ integralMatrices F n :=
    fun k hk => (mem_integralMatrices F n).mpr ((mem_integralGL_iff F n).mp (hg k hk)).1
  have hsingle_ne : ∀ i t : Fin n, i ≠ t →
      B * Matrix.single i t (1 : F) * A ∈ integralMatrices F n := by
    intro i t hit
    have h := hconj _ (transvectionGL_mem F n hit)
    have : B * Matrix.single i t (1 : F) * A =
        B * ((transvectionGL F n hit : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * A - 1 := by
      change _ = B * Matrix.transvection i t 1 * A - 1
      rw [Matrix.transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hBA,
        add_sub_cancel_left]
    rw [this]
    exact Subring.sub_mem _ h (Subring.one_mem _)
  have hsingle : ∀ i, B * Matrix.single i j₀ (1 : F) * A ∈ integralMatrices F n := by
    intro i
    by_cases hi : i = j₀
    · subst hi
      by_cases ht : ∃ t, t ≠ i
      · obtain ⟨t, ht⟩ := ht
        have : B * Matrix.single i i (1 : F) * A =
            (B * Matrix.single i t (1 : F) * A) * (B * Matrix.single t i (1 : F) * A) := by
          have hs : Matrix.single i i (1 : F) = Matrix.single i t 1 * Matrix.single t i 1 := by
            rw [Matrix.single_mul_single_same, mul_one]
          rw [hs]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc A B, hAB, Matrix.one_mul]
        rw [this]
        exact Subring.mul_mem _ (hsingle_ne i t (Ne.symm ht)) (hsingle_ne t i ht)
      · push Not at ht
        have h1 : Matrix.single i i (1 : F) = 1 := Matrix.ext fun x y => by
          rw [ht x, ht y, Matrix.single_apply, Matrix.one_apply_eq]
          simp
        rw [h1, Matrix.mul_one, hBA]
        exact Subring.one_mem _
    · exact hsingle_ne i j₀ hi

  have hB' : a • B ∈ integralMatrices F n := by
    refine (mem_integralMatrices F n).mpr fun l i => ?_
    have h := (mem_integralMatrices F n).mp (hsingle i) l k₀
    have : (B * Matrix.single i j₀ (1 : F) * A) l k₀ = B l i * a := by
      rw [Matrix.mul_apply, Finset.sum_eq_single j₀]
      · rw [Matrix.mul_single_apply_same, mul_one]
      · intro x _ hx
        rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hx, zero_mul]
      · simp
    rw [this] at h
    rw [Matrix.smul_apply, smul_eq_mul, mul_comm]
    exact h
  have hA' : a⁻¹ • A ∈ integralMatrices F n := by
    refine (mem_integralMatrices F n).mpr fun i j => ?_
    rw [Matrix.smul_apply, smul_eq_mul, Valuation.mem_integer_iff, map_mul, map_inv₀,
      inv_mul_le_iff₀ hva, mul_one]
    exact hmax' i j

  have hmain : ∀ k' ∈ integralGL F n,
      ((g * k' * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ∈ integralMatrices F n := by
    intro k' hk'
    have hk'' : (k' : Matrix (Fin n) (Fin n) F) ∈ integralMatrices F n :=
      (mem_integralMatrices F n).mpr ((mem_integralGL_iff F n).mp hk').1
    have : ((g * k' * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        a⁻¹ • A * (k' : Matrix (Fin n) (Fin n) F) * (a • B) := by
      rw [Units.val_mul, Units.val_mul]
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ ha, one_smul]
      rfl
    rw [this]
    exact Subring.mul_mem _ (Subring.mul_mem _ hA' hk'') hB'
  refine (mem_integralGL_iff F n).mpr ⟨(mem_integralMatrices F n).mp (hmain k hk), ?_⟩
  have : (g * k * g⁻¹)⁻¹ = g * k⁻¹ * g⁻¹ := by group
  rw [this]
  exact (mem_integralMatrices F n).mp (hmain _ (inv_mem hk))
end GroundTheory.Automorphic.GLnLocal
