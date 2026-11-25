-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckMatHom.dsigW_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:04:55.417802+00:00
-- url     : https://prove2.me/submissions/0cfccc8f-83bb-4c33-b5c0-dee1083496b0

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MatrixHom
import Theorems.Thm_CompanionTheory_Zuck_URep_dsig_coe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckMatHom
namespace GlobalTheory.CompanionTheory.ZuckMatHom
theorem _root_.solution {k r : ℕ} (U : URep k r) :
    ∀ (W : List (Formalism.FourierDecayAlt.ThreeDimData.Mx k r)), LieWd k r W → ∀ v : U.R.smSub,
      PI.UpqRep.dsigW (k := k) (r := r) U.R.σ W (v : U.R.H) = ((W.map U.dsig).prod v : U.R.H)
  | [], _, _ => rfl
  | X :: W, hW, v => by
    have ih := solution U W (fun Y hY => hW Y (List.mem_cons_of_mem _ hY)) v
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply,
      URep.dsig_coe U (hW X List.mem_cons_self), ← ih]
    rfl
end GlobalTheory.CompanionTheory.ZuckMatHom
