-- Prove2me | solution 1 for GlobalTheory.AdLat.Model.fv_mem_hat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:46.256658+00:00
-- url     : https://prove2.me/submissions/e502651f-c050-4897-9bff-bad221053a25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_SmulBasisMemHatIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Model
open NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.AdLat.Model
theorem _root_.solution {n : ℕ} {L : Set (Fin n → E)} {x : Fin n → E} (hx : x ∈ L) : fv F x ∈ hat F L :=
  AddSubgroup.subset_closure ⟨1, fun _ => one_mem _, x, hx, rfl⟩
end GlobalTheory.AdLat.Model
