-- Prove2me | solution 1 for GroundTheory.Global.kerModRangePiEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:45:56.029658+00:00
-- url     : https://prove2.me/submissions/0242cc07-afc6-4267-9579-8dde4303c921

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
namespace GroundTheory.Global
theorem _root_.solution {ι : Type*} {A : ι → Type*} [∀ i, AddCommGroup (A i)]
    (F G : (∀ i, A i) →+ (∀ i, A i)) (f g : ∀ i, A i →+ A i) (hF : ∀ x i, F x i = f i (x i))
    (hG : ∀ x i, G x i = g i (x i)) (x : F.ker) (i : ι) :
    kerModRangePiEquiv F G f g hF hG (QuotientAddGroup.mk x : KerModRange F G) i =
      QuotientAddGroup.mk (⟨(x : ∀ i, A i) i, by
        rw [AddMonoidHom.mem_ker, ← hF, AddMonoidHom.mem_ker.1 x.2, Pi.zero_apply]⟩ : (f i).ker) :=
  rfl
end GroundTheory.Global
