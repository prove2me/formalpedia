-- Prove2me | solution 1 for GlobalTheory.FibrePowerProper.isProper_fan_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:13:56.909904+00:00
-- url     : https://prove2.me/submissions/9a77ae97-d91e-43a6-9433-2b510ae6eb7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsProperEighthFibrePowerOver
import Theorems.Thm_GlobalTheory_FibrePowerProper_isProper_hom_of_iso
import Theorems.Thm_GlobalTheory_FibrePowerProper_isProper_prod_hom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.FibrePowerProper
namespace GlobalTheory.FibrePowerProper
theorem _root_.solution {T : Scheme.{0}} : ∀ (n : ℕ) (f : Fin n → Over T),
    (∀ i, IsProper (f i).hom) → ∀ (c : Fan f), IsLimit c → IsProper c.pt.hom
  | 0, f, _, c, hc => by
      have h0 : IsLimit (Fan.mk (Over.mk (𝟙 T)) (fun i => i.elim0 : ∀ i, Over.mk (𝟙 T) ⟶ f i)) :=
        Fan.IsLimit.mk _ (fun _ => Over.mkIdTerminal.from _) (fun _ k => k.elim0)
          (fun _ _ _ => Over.mkIdTerminal.hom_ext _ _)
      exact isProper_hom_of_iso (hc.conePointUniqueUpToIso h0) (by dsimp; infer_instance)
  | n + 1, f, hf, c, hc => by
      let c₁ : Fan (fun i : Fin n => f i.succ) := limit.cone (Discrete.functor fun i : Fin n => f i.succ)
      have h1 : IsProper c₁.pt.hom :=
        solution n (fun i => f i.succ) (fun i => hf _) c₁ (limit.isLimit _)
      have hl := extendFanIsLimit f (limit.isLimit (Discrete.functor fun i : Fin n => f i.succ))
        (prodIsProd (f 0) c₁.pt)
      exact isProper_hom_of_iso (hc.conePointUniqueUpToIso hl) (isProper_prod_hom _ _ (hf 0) h1)
end GlobalTheory.FibrePowerProper
