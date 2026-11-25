-- Prove2me | solution 1 for GlobalTheory.JR.EtInv.invK_regular_iff_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:37:09.011958+00:00
-- url     : https://prove2.me/submissions/f4ea02ac-3bfc-4753-91b5-5d597457326c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit
import Theorems.Thm_GlobalTheory_JR_EtInv_eq_zero_of_trace_mul
import Theorems.Thm_GlobalTheory_JR_EtInv_trace_mul_eq_sum
import Theorems.Thm_GlobalTheory_JR_EtInv_companion_pow_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtInv
namespace GlobalTheory.JR.EtInv
theorem _root_.solution :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p →
      Function.Bijective (fun (a : A.K) (i : Fin r) => Algebra.trace F A.K (τ ^ (i : ℕ) * a)) ∧
      ∀ a : A.K, (∀ i : ℕ, mom (sec (A.invK τ p lam a)) i = Algebra.trace F A.K (τ ^ i * a)) ∧
        (Delta (A.invK τ p lam a) ≠ 0 ↔ IsUnit a) := by
  intro F E _ _ _ _ hU A r τ p lam hg
  classical
  haveI : CharZero F := hU.charZero
  obtain ⟨hli, hfr, hr⟩ := hg
  let bb : Module.Basis (Fin r) F A.K :=
    basisOfLinearIndependentOfCardEqFinrank' _ hli (by rw [hfr, Fintype.card_fin])
  have hb : ∀ i, bb i = τ ^ (i : ℕ) := fun i => by
    simp [bb]
  let Ψ : A.K →ₗ[F] (Fin r → F) :=
    { toFun := fun a i => Algebra.trace F A.K (τ ^ (i : ℕ) * a)
      map_add' := fun a a' => by funext i; simp [mul_add]
      map_smul' := fun c a => by funext i; simp [mul_smul_comm] }
  have hΨ : ∀ a, Ψ a = fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * a) := fun _ => rfl
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    apply eq_zero_of_trace_mul (F := F) a
    intro x
    rw [trace_mul_eq_sum bb hb x a]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := congrFun ha j
    simp only [hΨ, Pi.zero_apply] at this
    rw [this, mul_zero]
  have hbij : Function.Bijective Ψ := by
    refine ⟨hinj, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hfr])).1 hinj
  have hmom : ∀ a : A.K, ∀ i : ℕ, mom (sec (A.invK τ p lam a)) i = Algebra.trace F A.K (τ ^ i * a) := by
    intro a i
    simp only [mom, sec, Et.invK]
    rw [companion_pow_mulVec bb hb hr i, trace_mul_eq_sum bb hb (τ ^ i) a, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine ⟨hbij, fun a => ⟨hmom a, ?_⟩⟩

  have hH : ∀ v : Fin r → F, hankel (A.invK τ p lam a) *ᵥ v = Ψ (a * bb.equivFun.symm v) := by
    intro v
    funext i
    simp only [hankel, Matrix.mulVec, dotProduct, Matrix.of_apply, hmom, hΨ,
      Module.Basis.equivFun_symm_apply, hb, Finset.mul_sum, map_sum, mul_smul_comm, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]; ring_nf
  have hcomp : Function.Injective (hankel (A.invK τ p lam a)).mulVec ↔ Function.Injective (fun y : A.K => a * y) := by
    constructor
    · intro h y y' hyy
      have := h (a₁ := bb.equivFun y) (a₂ := bb.equivFun y') (by rw [hH, hH]; simp [hyy])
      exact bb.equivFun.injective this
    · intro h v v' hvv
      rw [hH, hH] at hvv
      exact bb.equivFun.symm.injective (h (hinj hvv))
  rw [Delta, ← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit, hcomp]
  constructor
  · intro h
    have hs : Function.Surjective (Algebra.lmul F A.K a) :=
      LinearMap.injective_iff_surjective.1 h
    obtain ⟨y, hy⟩ := hs 1
    exact ⟨⟨a, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩
  · intro h
    exact h.mul_right_injective
end GlobalTheory.JR.EtInv
