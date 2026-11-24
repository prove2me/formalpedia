-- Prove2me | solution 1 for GlobalTheory.Phase.ShapeOps.quad_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:40:07.339669+00:00
-- url     : https://prove2.me/submissions/b5508adb-6959-4bb9-91b1-8d80c31e09ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsCosetQuadraticPhaseTestFunctionConjCharacterMu
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_mu_mul
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_mu_inv
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_mu_ne
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_quad_mul
import Theorems.Thm_GlobalTheory_Phase_ShapeOps_quad_affine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.ShapeOps
variable {M : Type} [AddCommGroup M]
namespace GlobalTheory.Phase.ShapeOps
theorem _root_.solution {S : AddSubgroup M} {f : M → ℂ} (hf : Quad S f) {d : M} (hd : d ∈ S) :
    Quad S (fun x => f (x + d)) := by
  have hq : Quad S (fun x => f (x + d) * (f x)⁻¹) := by
    refine quad_affine (fun x hx => mu_mul (hf.1 _ (S.add_mem hx hd)) (mu_inv (hf.1 x hx)))
      fun x hx y hy => ?_
    have h := hf.2 x hx y hy d hd
    have n0 := mu_ne (hf.1 0 S.zero_mem)
    have nx := mu_ne (hf.1 x hx)
    have ny := mu_ne (hf.1 y hy)
    have nxy := mu_ne (hf.1 _ (S.add_mem hx hy))
    simp only [zero_add]
    field_simp
    linear_combination h
  have hm := quad_mul hf hq
  have key : ∀ x ∈ S, f (x + d) = f x * (f (x + d) * (f x)⁻¹) := fun x hx => by
    have nx := mu_ne (hf.1 x hx)
    field_simp
  refine ⟨fun x hx => hf.1 _ (S.add_mem hx hd), fun x hx y hy z hz => ?_⟩
  have := hm.2 x hx y hy z hz
  simp only at this ⊢
  rw [← key _ hx, ← key _ hy, ← key _ hz, ← key _ S.zero_mem, ← key _ (S.add_mem hx hy),
    ← key _ (S.add_mem hy hz), ← key _ (S.add_mem hx hz),
    ← key _ (S.add_mem (S.add_mem hx hy) hz)] at this
  exact this
end GlobalTheory.Phase.ShapeOps
