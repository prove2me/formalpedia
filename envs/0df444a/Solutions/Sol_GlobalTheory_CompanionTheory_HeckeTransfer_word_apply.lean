-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeTransfer.word_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:33:34.311081+00:00
-- url     : https://prove2.me/submissions/9dd1e698-1af4-4d3b-a701-642ca6a22020

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithfulStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TransferStatementBis
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeTransfer_phi_single
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeTransfer_phi_fixed
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeTransfer_phi_phi
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.Fl
open CompanionTheory.D.gk.admitted (stdPoly word word_nil word_cons)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeTransfer
variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {K : Subgroup G} {σ : G →* (H →L[ℂ] H)} {v : H}
namespace GlobalTheory.CompanionTheory.HeckeTransfer
theorem _root_.solution {E : H →L[ℂ] H} (hA : IsAvg σ K E) (b : G → Hk K)
    (hb : ∀ (u : H), (∀ k ∈ K, σ k u = u) → ∀ g, E (σ g u) = phi K σ u ((b g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)))
    (hv : ∀ k ∈ K, σ k v = v) (l : List G) :
    word E (l.map fun g => σ g) v =
      phi K σ v ((((l.map b).reverse.prod : Hk K) : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)) := by
  induction l with
  | nil =>
    simp only [List.map_nil, word_nil, List.reverse_nil, List.prod_nil, OneMemClass.coe_one,
      Module.End.one_apply, dlt, phi_single hv, one_smul, map_one, ContinuousLinearMap.one_apply]
    exact hA.2.1 v hv
  | cons g l ih =>
    simp only [List.map_cons, word_cons, ContinuousLinearMap.mul_apply]
    rw [ih, hb _ (phi_fixed hv _) g, phi_phi hv]
    simp only [List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
      MulMemClass.coe_mul, Module.End.mul_apply]
end GlobalTheory.CompanionTheory.HeckeTransfer
