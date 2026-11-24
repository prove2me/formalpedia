-- Prove2me | solution 1 for GlobalTheory.PerMove.rmul_mem_GG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:21:19.504501+00:00
-- url     : https://prove2.me/submissions/cef47589-efba-4231-addb-d2f02a2bd048

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
import Theorems.Thm_GlobalTheory_PerMove_bor_tri
import Theorems.Thm_GlobalTheory_PerMove_bor_diag_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_gram_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_lminor_conj


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
open GlobalTheory GlobalTheory.PerMove
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField Matrix
open scoped nonZeroDivisors
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.PerMove
namespace _root_.GlobalTheory.PerMove
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {q : ℕ}
    {x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r} (hx : x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.GG Ψ G q) (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.GG Ψ G q := by
  intro τ
  have hmat : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ := rfl
  refine ⟨?_, fun i => ?_⟩
  · rw [hmat, Matrix.det_mul]
    exact mul_ne_zero (hx τ).1 (hb τ).1
  · have h := (hx τ).2 i
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin at h ⊢
    rw [hmat, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_conj (_root_.GlobalTheory.PerMove.bor_tri hb τ)]
    set z := ∏ j, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
    have hz : z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => _root_.GlobalTheory.PerMove.bor_diag_ne hb τ _
    have hre : ∀ m : ℂ, (z * m * (starRingEnd ℂ) z).re = Complex.normSq z * m.re := by
      intro m
      rw [mul_right_comm, Complex.mul_conj, Complex.re_ofReal_mul]
    rw [hre, mul_left_comm]
    exact mul_pos (Complex.normSq_pos.mpr hz) h
end _root_.GlobalTheory.PerMove
end GlobalTheory.PerMove
