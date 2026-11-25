-- Prove2me | solution 1 for GlobalTheory.Sandwich.HodgeTateBound.smul_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:09:12.240824+00:00
-- url     : https://prove2.me/submissions/3ac67d18-33e9-4532-a97f-591fa172ac38

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FontaineAinfLocalDomainXiAdicOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulMemRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.Sandwich.HodgeTateBound
variable {A O : Type} [CommRing A] [CommRing O] {h : ℕ}
namespace GlobalTheory.Sandwich.HodgeTateBound
theorem _root_.solution [IsDomain A] (θ : A →+* O) (hs : Function.Surjective θ) {ξ ν μ : A}
    (hker : RingHom.ker θ = Ideal.span {ξ}) (hξ : ξ ≠ 0) (hμ : ξ * ν = μ)
    {F G : Matrix (Fin h) (Fin h) A} (hFG : F * G = μ • (1 : Matrix (Fin h) (Fin h) A))
    (f : Fin h → O) (hf : f ∈ LinearMap.ker (Matrix.toLin' (G.map θ))) :
    θ ν • f ∈ LinearMap.range (Matrix.toLin' (F.map θ)) := by
  choose m hm using fun i => hs (f i)
  have hf' : f = θ ∘ m := by
    funext i
    exact (hm i).symm
  rw [LinearMap.mem_ker, Matrix.toLin'_apply, hf'] at hf
  have h1 : ∀ i, ∃ x, x * ξ = (G *ᵥ m) i := by
    intro i
    rw [← Ideal.mem_span_singleton', ← hker, RingHom.mem_ker, RingHom.map_mulVec, hf]
    rfl
  choose x hx using h1
  have h2 : G *ᵥ m = ξ • x := by
    funext i
    rw [← hx i, Pi.smul_apply, smul_eq_mul, mul_comm]
  have h3 : F *ᵥ (G *ᵥ m) = μ • m := by
    rw [Matrix.mulVec_mulVec, hFG, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [h2, Matrix.mulVec_smul, ← hμ] at h3
  refine ⟨θ ∘ x, ?_⟩
  funext i
  have h4 := congrFun h3 i
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc] at h4
  have h5 := mul_left_cancel₀ hξ h4
  rw [Matrix.toLin'_apply, ← RingHom.map_mulVec, h5, map_mul, hm]
  rfl
end GlobalTheory.Sandwich.HodgeTateBound
