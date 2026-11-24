-- Prove2me | solution 1 for GlobalTheory.UnitVectorStabEq.stabLat_inf_stabVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:25:56.910961+00:00
-- url     : https://prove2.me/submissions/1aef7b30-e7db-4bd3-8654-af4009cc676e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_StabLatInfStabVec
import Theorems.Thm_GlobalTheory_UnitVectorStabEq_mem_stabVec
import Theorems.Thm_GlobalTheory_UnitVectorStabEq_mem_stabLat
import Theorems.Thm_GlobalTheory_UnitVectorStabEq_mem_perpLat
import Theorems.Thm_GlobalTheory_UnitVectorStabEq_hR_act
import Theorems.Thm_GlobalTheory_UnitVectorStabEq_act_sub_smul
import Theorems.Thm_GlobalTheory_UnitVectorStabEq_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
open GlobalTheory GlobalTheory.UnitVectorStabEq
namespace GlobalTheory.UnitVectorStabEq
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (OEv F E v) (Fin M → Ev F E v)), IsSDLat σ J v L → ∀ x ∈ L, (∃ b ∈ OEv F E v, hR (Fv F v) σ J x x * b = 1) → stabLat σ J v L ⊓ stabVec σ J v x = stabLat σ J v (perpLat σ J v L x) ⊓ stabVec σ J v x := by
  intro F E _ _ _ _ _ σ _ M J _ v L hL x hx ⟨b, hb, hb1⟩
  ext g
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  refine and_congr_left fun hg => ?_
  rw [mem_stabVec] at hg
  have hh : ∀ y, hR (Fv F v) σ J x (act σ J v g y) = hR (Fv F v) σ J x y := by
    intro y
    rw [← hR_act σ J v g x y, hg]
  rw [mem_stabLat, mem_stabLat]
  constructor
  · intro h y
    rw [mem_perpLat, mem_perpLat, hh, h y]
  · intro h y
    rw [mem_iff σ J v L hL x hx b hb hb1 y, mem_iff σ J v L hL x hx b hb hb1 (act σ J v g y), hh,
      h (y - _), act_sub_smul, hg]
end GlobalTheory.UnitVectorStabEq
