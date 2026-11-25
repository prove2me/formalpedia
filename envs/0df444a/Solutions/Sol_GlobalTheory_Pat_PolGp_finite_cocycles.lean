-- Prove2me | solution 1 for GlobalTheory.Pat.PolGp.finite_cocycles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:08:07.862295+00:00
-- url     : https://prove2.me/submissions/cb93baf8-13ae-489c-85d7-dcc510fece38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles
import Theorems.Thm_GlobalTheory_Pat_PhiFin_finite_cocycles
import Theorems.Thm_GlobalTheory_Pat_Frame_l_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Polynomial IsLocalRing
noncomputable section
open IsLocalRing
open GlobalTheory GlobalTheory.Pat
attribute [instance] PG.grp PG.top PG.tgrp PG.cpt PG.t2 PG.td
attribute [instance] Frame.hl Frame.iO Frame.iOd Frame.iOv Frame.iVl Frame.iSt
namespace GlobalTheory.Pat
namespace PolGp
theorem _root_.solution {Φ : Frame} (G : PolGp Φ) (i i' : Fin Φ.n) :
    {b : G.Γ → Φ.k | IsLocallyConstant b ∧ ∀ g h, b (g * h) =
      ((G.chi i g : Φ.kˣ) : Φ.k) * b h + b g * ((G.chi i' h : Φ.kˣ) : Φ.k)}.Finite := by
  haveI := Φ.k_fin
  refine G.fg.finite_cocycles (fun m => by rw [nsmul_eq_mul, Φ.l_eq_zero, zero_mul])
    ((G.chi i).ker ⊓ (G.chi i').ker)
    ((G.chi_open i).inter (G.chi_open i')) (fun g m => ((G.chi i g : Φ.kˣ) : Φ.k) * m)
    (fun g m => m * ((G.chi i' g : Φ.kˣ) : Φ.k)) ?_ ?_
  · intro h hh m; rw [MonoidHom.mem_ker.1 hh.1]; simp
  · intro h hh m; rw [MonoidHom.mem_ker.1 hh.2]; simp
end PolGp
end GlobalTheory.Pat
