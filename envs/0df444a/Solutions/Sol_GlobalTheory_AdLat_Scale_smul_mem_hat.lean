-- Prove2me | solution 1 for GlobalTheory.AdLat.Scale.smul_mem_hat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:54:10.889643+00:00
-- url     : https://prove2.me/submissions/b0040c69-d076-4ce2-b3c9-ce01b16efbf8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ZeroMemLatOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Scale
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.AdLat.Scale
namespace _root_.GlobalTheory.AdLat.Scale
theorem _root_.solution {L L' : Set (Fin n → E)} {a : E}
    (h : ∀ x ∈ L, a • x ∈ L')
    {z : Fin n → _root_.GlobalTheory.AdLat.RA F E} (hz : z ∈ _root_.GlobalTheory.AdLat.hat F L) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a : _root_.GlobalTheory.AdLat.RA F E) • z ∈
      _root_.GlobalTheory.AdLat.hat F L' := by
  unfold _root_.GlobalTheory.AdLat.hat at hz ⊢
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨b, hb, a • x, h x hx, ?_⟩
    funext i
    change ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a) * (b ⊗ₜ[F] x i) = b ⊗ₜ[F] (a * x i)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx
end _root_.GlobalTheory.AdLat.Scale
end GlobalTheory.AdLat.Scale
