-- Prove2me | solution 1 for GlobalTheory.FontCmp.exists_liftAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:50:02.918657+00:00
-- url     : https://prove2.me/submissions/384475fe-1b46-4437-9203-d80c2cb87d6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_TensorMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FontaineFormalismTensorEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FontCmp
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct GlobalTheory.IndefiniteRowSideFullHecke
namespace GlobalTheory.FontCmp
theorem _root_.solution {R M N Z : Type} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [AddCommGroup Z] (f : M → N → Z)
    (h1 : ∀ m m' n, f (m + m') n = f m n + f m' n) (h2 : ∀ m n n', f m (n + n') = f m n + f m n')
    (h3 : ∀ (r : R) m n, f (r • m) n = f m (r • n)) :
    ∃ F : M ⊗[R] N →+ Z, ∀ m n, F (m ⊗ₜ n) = f m n :=
  ⟨liftAddHom (AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (f m) (h2 m))
    (fun m m' => by ext n; exact h1 m m' n)) h3, fun _ _ => rfl⟩
end GlobalTheory.FontCmp
