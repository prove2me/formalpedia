-- Prove2me | solution 1 for GlobalTheory.ActLimit.exists_tends
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:29:28.573989+00:00
-- url     : https://prove2.me/submissions/e7cbd36c-c0da-4866-913a-340e22b4c554

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupActionLimitsIntegralEndomorphisms
import Theorems.Thm_GlobalTheory_ActLimit_TendsS_sub
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mono
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sub
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mono
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.ActLimit
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.ActLimit
theorem _root_.solution (cpl : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n))
    {s : ℕ → C} (hs : ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (s (n + 1) - s n)) : ∃ x, Tends V s x := by
  choose k hk using hs
  have hd : ∀ N m n, k N ≤ m → m ≤ n → V.Ge N (s n - s m) := by
    intro N m n hm hn
    induction n, hn using Nat.le_induction with
    | base => simpa using VF.Ge.zero (V := V) N
    | succ n hn ih => simpa using (hk N n (hm.trans hn)).add ih
  let φ : ℕ → ℕ := fun N => (Finset.range (N + 1)).sup k
  have h1 : ∀ N, k N ≤ φ N := fun N => Finset.le_sup (f := k) (Finset.self_mem_range_succ N)
  have h2 : ∀ N, φ N ≤ φ (N + 1) := fun N => Finset.sup_mono (Finset.range_mono (by omega))
  obtain ⟨x, hx⟩ := cpl (fun N => s (φ N)) fun N => hd N _ _ (h1 N) (h2 N)
  refine ⟨x, fun w => ?_⟩
  filter_upwards [eventually_ge_atTop (φ ⌈w⌉₊)] with n hn
  have := (hx ⌈w⌉₊).sub (hd ⌈w⌉₊ _ _ (h1 _) hn)
  simpa using this.mono (Nat.le_ceil w)
end GlobalTheory.ActLimit
