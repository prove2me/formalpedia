-- Prove2me | solution 1 for GlobalTheory.SecAff.sec_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:53:38.391192+00:00
-- url     : https://prove2.me/submissions/e9781050-5bcb-4808-8a4d-f5b353359677

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
import Theorems.Thm_GlobalTheory_SecAff_rs_rs
import Theorems.Thm_GlobalTheory_SecAff_eq_of_cover
import Theorems.Thm_GlobalTheory_SecAff_fun_kill
import Theorems.Thm_GlobalTheory_SecAff_pow_mul_zero_mono
import Theorems.Thm_GlobalTheory_SecAff_exists_fin_cover
import Theorems.Thm_GlobalTheory_SecAff_sec_at
import Theorems.Thm_GlobalTheory_SecAff_le_iSup_inf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SecAff
variable {X X' X'' : Scheme.{0}}
namespace GlobalTheory.SecAff
theorem _root_.solution [CompactSpace X] (φ : X' ⟶ X) [IsOpenImmersion φ] (f : Γ(X, ⊤))
    (hφ : φ.opensRange = X.basicOpen f) (M : LB X) (hM : M.IsLB) (U' : M.ι → X'.Opens)
    (h : ∀ j, U' j ≤ φ ⁻¹ᵁ M.U j) (h' : ∀ j, φ ⁻¹ᵁ M.U j ≤ U' j) (s : LB.Sec M)
    (hs : ∀ j, pa φ (h j) (s.f j) = 0) :
    ∃ N : ℕ, ∀ j, rs (le_top : M.U j ≤ ⊤) f ^ N * s.f j = 0 := by
  obtain ⟨κ, _, W, c, hW, hWc, hc⟩ := exists_fin_cover M hM
  have : ∀ a, ∃ N : ℕ, rs (le_top : W a ≤ ⊤) f ^ N * rs (hWc a) (s.f (c a)) = 0 := by
    intro a
    refine fun_kill φ f hφ (hW a).isCompact le_rfl le_rfl _ ?_
    have := congrArg (rs ((φ.preimage_mono (hWc a)).trans (h' (c a)))) (hs (c a))
    rw [rs_pa, map_zero] at this
    rw [pa_rs]
    exact this
  choose n hn using this
  refine ⟨Finset.univ.sup n, fun j => ?_⟩
  refine eq_of_cover (fun a => M.U j ⊓ W a) (fun a => inf_le_left) (le_iSup_inf _ hc) _ _ fun a => ?_
  have := congrArg (rs (inf_le_right : M.U j ⊓ W a ≤ W a))
    (pow_mul_zero_mono (hn a) (Finset.le_sup (f := n) (Finset.mem_univ a)))
  rw [map_mul, map_pow, rs_rs, rs_rs, map_zero] at this
  rw [map_mul, map_pow, rs_rs, map_zero,
    sec_at s j (c a) inf_le_left (inf_le_right.trans (hWc a)), mul_left_comm, this, mul_zero]
end GlobalTheory.SecAff
