-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases.IsExt.apply_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:50:17.645803+00:00
-- url     : https://prove2.me/submissions/fbf6fd1c-c920-4bd2-bc58-cf5b587c33f2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_GramCEqTranspose
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SemilinearExtensionBases

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open Module
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases
namespace GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases
namespace IsExt
theorem _root_.solution {Ks LL WL : Type} [Field Ks] [Field LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    {WK : Submodule Ks WL} {O K K'' : Type} [CommRing O] [Field K] [Algebra Ks K] [Field K''] [Algebra O K'']
    {Fm : Type} [AddCommGroup Fm] [Module K Fm] [Module O Fm]
    {emb : LL →+* K''} {eF : Fm ≃ₗ[K] K ⊗[Ks] WK} {e : WL →ₛₗ[emb] K'' ⊗[O] Fm} (h : IsExt O emb eF e) (f : WK) :
    e f = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] f) := by
  simpa using h Unit (fun _ => 1) (fun _ => f)
end IsExt
end GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases
