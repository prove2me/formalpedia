-- Prove2me | solution 1 for GlobalTheory.AdLat.Half.herm_mem_of_fv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:01:59.208231+00:00
-- url     : https://prove2.me/submissions/16a28a3c-b202-4b2b-94f2-70f5f7ad6045

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionSelfDualOfSelfDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralTmulOneMulMemAdelicCompletion
import Theorems.Thm_GlobalTheory_AdLat_Half_herm_add_right
import Theorems.Thm_GlobalTheory_AdLat_Half_herm_neg_right
import Theorems.Thm_GlobalTheory_AdLat_Half_herm_smul_right
import Theorems.Thm_GlobalTheory_AdLat_mul_mem_adelicCompletionOfElementSet_of_mul_mem
import Theorems.Thm_GlobalTheory_AdLat_tmul_mem_adelicCompletion_of_integral
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Half
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.AdLat.Half
namespace _root_.GlobalTheory.AdLat.Half
theorem _root_.solution (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (J : Set E) (L : Set (Fin n → E)) (z : Fin n → _root_.GlobalTheory.AdLat.RA F E)
    (hz : ∀ y ∈ L, _root_.GlobalTheory.AdLat.hermA c G z (_root_.GlobalTheory.AdLat.fv F y) ∈
      _root_.GlobalTheory.AdLat.hat1 F J)
    (w : Fin n → _root_.GlobalTheory.AdLat.RA F E) (hw : w ∈ _root_.GlobalTheory.AdLat.hat F L) :
    _root_.GlobalTheory.AdLat.hermA c G z w ∈ _root_.GlobalTheory.AdLat.hat1 F J := by
  unfold _root_.GlobalTheory.AdLat.hat at hw
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, y, hy, rfl⟩ := hw
    have hw' : (fun i => a ⊗ₜ[F] y i) =
        (a ⊗ₜ[F] (1 : E) : _root_.GlobalTheory.AdLat.RA F E) • _root_.GlobalTheory.AdLat.fv F y := by
      funext i
      simp [_root_.GlobalTheory.AdLat.fv, Algebra.TensorProduct.tmul_mul_tmul]
    rw [hw', _root_.GlobalTheory.AdLat.Half.herm_smul_right]
    have hsg : _root_.GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (a ⊗ₜ[F] (1 : E)) =
        a ⊗ₜ[F] (1 : E) := by
      simp [_root_.GlobalTheory.AdLat.sg]
    rw [hsg]
    refine _root_.GlobalTheory.AdLat.mul_mem_adelicCompletionOfElementSet_of_mul_mem F (I := {1}) (fun x hx y hy => ?_)
      (_root_.GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral F ha rfl) (hz y hy)
    rw [Set.mem_singleton_iff.1 hx, one_mul]
    exact hy
  | zero =>
    have h0 : _root_.GlobalTheory.AdLat.hermA c G z 0 = 0 := by
      simp [_root_.GlobalTheory.AdLat.hermA]
    rw [h0]
    exact zero_mem _
  | add w w' _ _ hw hw' =>
    rw [_root_.GlobalTheory.AdLat.Half.herm_add_right]
    exact add_mem hw hw'
  | neg w _ hw =>
    rw [_root_.GlobalTheory.AdLat.Half.herm_neg_right]
    exact neg_mem hw
end _root_.GlobalTheory.AdLat.Half
end GlobalTheory.AdLat.Half
