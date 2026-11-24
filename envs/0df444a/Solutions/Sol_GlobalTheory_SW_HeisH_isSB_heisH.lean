-- Prove2me | solution 1 for GlobalTheory.SW.HeisH.isSB_heisH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:27:14.402306+00:00
-- url     : https://prove2.me/submissions/12b86a95-f867-4994-9a2d-7c3fbb69bdaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
import Theorems.Thm_GlobalTheory_SW_HeisH_pairT_add
import Theorems.Thm_GlobalTheory_SW_HeisH_heisH_apply
import Theorems.Thm_GlobalTheory_SW_Base_isIntegral_cc
import Theorems.Thm_GlobalTheory_SW_Dict_exists_den
import Theorems.Thm_GlobalTheory_SW_FourierJ_exists_den
import Theorems.Thm_GlobalTheory_SW_LinChange_exists_den


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
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeisH
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.HeisH
theorem _root_.solution (d b : Matrix (Fin n) (Fin N) E) {φ : Matrix (Fin n) (Fin N) E → ℂ}
    (hφ : IsSB φ) : IsSB (heisH d b φ) := by
  obtain ⟨R, hR, hs, hp⟩ := hφ
  obtain ⟨M, hM, h⟩ := Dict.exists_den (fun p : Bool × Fin n × Fin N =>
    if p.1 then d p.2.1 p.2.2 else b p.2.1 p.2.2)
  have hd : ∀ k a, IsIntegral ℤ ((M : E) * d k a) := fun k a => by
    simpa using h (true, k, a)
  have hb : ∀ k a, IsIntegral ℤ ((M : E) * b k a) := fun k a => by
    simpa using h (false, k, a)
  have c : ∀ k : ℕ, IsIntegral ℤ (k : E) := fun k => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ))
  refine ⟨R * M, by positivity, fun x hx k a => ?_, fun x y hy => ?_⟩
  · rw [heisH_apply] at hx
    have h1 := hs _ (left_ne_zero_of_mul hx) k a
    have := ((c M).mul h1).add ((c R).mul (hd k a))
    have e : (((R * M : ℕ) : E) • x) k a = M * ((R : E) • (x - d)) k a + R * (M * d k a) := by
      simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Nat.cast_mul]; ring
    rw [e]; exact this
  · rw [heisH_apply, heisH_apply, pairT_add]
    have e : x + ((R * M : ℕ) : E) • y - d = x - d + (R : E) • ((M : E) • y) := by
      rw [smul_smul, Nat.cast_mul]; abel
    rw [e, hp _ ((M : E) • y) (fun k a => (c M).mul (hy k a))]
    congr 1
    have hi : IsIntegral ℤ (pairT b (((R * M : ℕ) : E) • y)) := by
      refine Algebra.isIntegral_trace (IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun a _ => ?_)
      have := (c R).mul ((hb k a).mul (Base.isIntegral_cc (hy k a)))
      convert this using 1
      simp only [Matrix.smul_apply, smul_eq_mul, Nat.cast_mul, cc, map_mul, map_natCast]; ring
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    rw [← hm, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨m, ?_⟩
    simp only [eq_intCast]
    push_cast
    ring
end GlobalTheory.SW.HeisH
