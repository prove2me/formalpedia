-- Prove2me | solution 1 for GroundTheory.GroupCoh.infRes_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:24.837201+00:00
-- url     : https://prove2.me/submissions/66d2fc22-6e95-46c0-bd8c-2c5b7feeacdb

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DeltaMap
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_InfRes
import Theorems.Thm_GroundTheory_GroupCoh_shiftSC_shortExact
import Theorems.Thm_GroundTheory_GroupCoh_shiftSCQ_shortExact
import Theorems.Thm_GroundTheory_GroupCoh_isZero_coindOne
import Theorems.Thm_GroundTheory_GroupCoh_isZero_quotientToInvariants_coindOne
import Theorems.Thm_GroundTheory_GroupCoh_isZero_res_coindOne
import Theorems.Thm_P2M_GroundTheory_GroupCoh___comp_map_002a70015e3d
import Theorems.Thm_P2M_GroundTheory_GroupCoh___comp_map_res_6a14414efe8b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits groupCohomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (A : Rep k G) (S : Subgroup G) [S.Normal]
namespace GroundTheory.GroupCoh
theorem _root_.solution (n : ℕ)
    (ih : ∀ B : Rep k G, (∀ i, 0 < i → i < n + 1 → IsZero (groupCohomology (res S.subtype B) i)) →
      Mono (infResShortComplex B S n).f ∧ (infResShortComplex B S n).Exact)
    (hA : ∀ i, 0 < i → i < n + 2 → IsZero (groupCohomology (res S.subtype A) i)) :
    Mono (infResShortComplex A S (n + 1)).f ∧ (infResShortComplex A S (n + 1)).Exact := by
  have hX := shiftSC_shortExact A
  have hS := (shortExact_res S.subtype).2 hX
  have hQ := shiftSCQ_shortExact A S (hA 1 one_pos (by omega))
  have hC : ∀ i, 0 < i → i < n + 1 →
      IsZero (groupCohomology (res S.subtype (shiftSC A).X₃) i) := by
    intro i hi hin
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    have hδ := isIso_δ_of_isZero hS (m + 1) (isZero_res_coindOne k A S m)
      (isZero_res_coindOne k A S (m + 1))
    exact (hA (m + 1 + 1) (by omega) (by omega)).of_iso (@asIso _ _ _ _ _ hδ)
  obtain ⟨ihm, ihe⟩ := ih (shiftSC A).X₃ hC
  have hδQ := isIso_δ_of_isZero hQ (n + 1) (isZero_quotientToInvariants_coindOne k A S n)
    (isZero_quotientToInvariants_coindOne k A S (n + 1))
  have hδX := isIso_δ_of_isZero hX (n + 1) (isZero_coindOne k G A n)
    (isZero_coindOne k G A (n + 1))
  have hδS := isIso_δ_of_isZero hS (n + 1) (isZero_res_coindOne k A S n)
    (isZero_res_coindOne k A S (n + 1))
  let F : (shiftSCQ A S).map (resFunctor (QuotientGroup.mk' S)) ⟶ shiftSC A :=
    { τ₁ := ofHom (A.ρ.quotientToInvariants_lift S)
      τ₂ := ofHom ((coindOne k G A).ρ.quotientToInvariants_lift S)
      τ₃ := ofHom ((shiftSC A).X₃.ρ.quotientToInvariants_lift S)
      comm₁₂ := by ext; rfl
      comm₂₃ := by ext; rfl }
  have h1 : δ hQ (n + 1) (n + 1 + 1) rfl ≫ inflation A S (n + 1 + 1) =
      inflation (shiftSC A).X₃ S (n + 1) ≫ δ hX (n + 1) (n + 1 + 1) rfl :=
    δ_comp_map (QuotientGroup.mk' S) hQ hX F (n + 1) (n + 1 + 1) rfl
  have h2 : δ hX (n + 1) (n + 1 + 1) rfl ≫ restriction A S (n + 1 + 1) =
      restriction (shiftSC A).X₃ S (n + 1) ≫ δ hS (n + 1) (n + 1 + 1) rfl :=
    δ_comp_map_res S.subtype hX (n + 1) (n + 1 + 1) rfl
  let e : infResShortComplex (shiftSC A).X₃ S n ≅ infResShortComplex A S (n + 1) :=
    ShortComplex.isoMk (@asIso _ _ _ _ _ hδQ) (@asIso _ _ _ _ _ hδX) (@asIso _ _ _ _ _ hδS) h1 h2
  refine ⟨?_, (ShortComplex.exact_iff_of_iso e).1 ihe⟩
  have hf : e.inv.τ₁ ≫ (infResShortComplex (shiftSC A).X₃ S n).f ≫ e.hom.τ₂ =
      (infResShortComplex A S (n + 1)).f := by
    rw [← Category.assoc, e.inv.comm₁₂, Category.assoc, ← ShortComplex.comp_τ₂, e.inv_hom_id,
      ShortComplex.id_τ₂, Category.comp_id]
  rw [← hf]
  infer_instance
end GroundTheory.GroupCoh
