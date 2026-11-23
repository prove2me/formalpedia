-- Prove2me | solution 1 for GlobalTheory.CompleteBaseChange.isPrecomplete_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:24.555811+00:00
-- url     : https://prove2.me/submissions/f67397ed-08a9-4ffd-ba84-6ad50455cc5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsPolynomialSubMem
import Theorems.Thm_GlobalTheory_CompleteBaseChange_mem_smul_top_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries IsLocalRing
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompleteBaseChange
namespace GlobalTheory.CompleteBaseChange
theorem _root_.solution {R M : Type*} (ι : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    {J : Ideal R} (hJ : J.FG) [IsPrecomplete J M] : IsPrecomplete J (ι → M) := by
  refine ⟨fun u hu => ?_⟩
  have h1 : ∀ i, ∃ L : M, ∀ k, u k i ≡ L [SMOD (J ^ k • ⊤ : Submodule R M)] :=
    fun i => IsPrecomplete.prec' (fun k => u k i) fun {a b} hab =>
      SModEq.sub_mem.2 ((mem_smul_top_pi hJ.pow _).1 (SModEq.sub_mem.1 (hu hab)) i)
  choose L hL using h1
  exact ⟨L, fun k => SModEq.sub_mem.2
    ((mem_smul_top_pi hJ.pow _).2 fun i => SModEq.sub_mem.1 (hL i k))⟩
end GlobalTheory.CompleteBaseChange
