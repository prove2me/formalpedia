-- Prove2me | solution 1 for GlobalTheory.ProdSubProdBound.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:14:19.625971+00:00
-- url     : https://prove2.me/submissions/f5dec8ef-90ae-4152-9bd0-8c41a291d7a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ProdSubProdLe
import Theorems.Thm_GlobalTheory_ProdSubProdBound_prod_sub_prod_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ProdSubProdBound
namespace GlobalTheory.ProdSubProdBound
theorem _root_.solution : ∀ {K Γ : Type} [inst : Field K] [inst_1 : LinearOrderedCommGroupWithZero Γ] {v : Valuation K Γ} {ι : Type} (s : Finset ι) {c : Γ} {a b : ι → K}, (∀ (i : ι), (v : K → Γ) (a i) ≤ (1 : Γ)) → (∀ (i : ι), (v : K → Γ) (b i) ≤ (1 : Γ)) → (∀ (i : ι), (v : K → Γ) (a i - b i) ≤ c) → (v : K → Γ) (∏ i ∈ s, a i - ∏ i ∈ s, b i) ≤ c :=
  fun s => prod_sub_prod_le s
end GlobalTheory.ProdSubProdBound
