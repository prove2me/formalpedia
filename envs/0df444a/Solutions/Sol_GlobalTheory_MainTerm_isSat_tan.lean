-- Prove2me | solution 1 for GlobalTheory.MainTerm.isSat_tan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:09:12.143178+00:00
-- url     : https://prove2.me/submissions/bd847117-2441-4e9a-9ad2-345a9bebb4b4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Theorems.Thm_GlobalTheory_MainTerm_tan_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_inv_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
open Formalism.BaseCaseIdentities (Data Kn s0)
open Classical
noncomputable section
open GlobalTheory GlobalTheory.MainTerm
variable {C : Type} [Field C]
variable {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
variable {G : Cart V d I J} {S : Sys G} {Z : Type} {D : Data C Z I} {a : ZMod d} {i : ℕ}
open Classical
variable {C : Type} [Field C]
variable {V : _root_.Formalism.L2.FormalSeriesBounds.VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
variable {G : _root_.Formalism.L2.FormalSeriesBounds.Cart V d I J} {S : _root_.Formalism.L2.FormalSeriesBounds.Sys G} {Z : Type} {D : _root_.Formalism.BaseCaseIdentities.Data C Z I} {a : ZMod d}
  {i : ℕ}
namespace GlobalTheory.MainTerm
namespace _root_.GlobalTheory.MainTerm
theorem _root_.solution (S : _root_.Formalism.L2.FormalSeriesBounds.Sys G) {N : ℕ} (em : Fin N ↪ I) :
    _root_.Formalism.L2.FormalSeriesBounds.IsSat V (fun δ => S.tan (em δ)) := by
  have hu : V.v (Matrix.of S.tan).det = 0 := S.unimod
  have hdet : (Matrix.of S.tan).det ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hu
    simp at hu
  have hint : ∀ x y, V.Ge 0 (Matrix.of S.tan x y) :=
    fun x y => _root_.GlobalTheory.MainTerm.tan_int S x y
  unfold _root_.Formalism.L2.FormalSeriesBounds.IsSat
  refine ⟨fun c x => _root_.GlobalTheory.MainTerm.tan_int S _ _,
    fun x c' => (Matrix.of S.tan)⁻¹ x (em c'),
    fun x c' => _root_.Formalism.L2.FormalSeriesBounds.inv_int (Matrix.of S.tan) hint hu x (em c'), fun c c' => ?_⟩
  have h1 := congrFun (congrFun
    (Matrix.mul_nonsing_inv (Matrix.of S.tan) (isUnit_iff_ne_zero.2 hdet)) (em c)) (em c')
  rw [Matrix.mul_apply, Matrix.one_apply] at h1
  simpa [em.injective.eq_iff] using h1
end _root_.GlobalTheory.MainTerm
end GlobalTheory.MainTerm
