-- Prove2me | solution 1 for GlobalTheory.SelfDualLatticeCompare.conclusion_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:48:25.005779+00:00
-- url     : https://prove2.me/submissions/ca612f4a-291a-4449-84a9-6811f4c62fd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_UnitaryLatticeOrthogonal
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualLatticeActions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_hasONB_iff
import Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_unitVectors_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.SelfDualLatticeCompare
open GlobalTheory.IndefiniteRowSideFullHecke
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.SelfDualLatticeCompare
theorem _root_.solution (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) :
    (UnitaryLatticeOrthogonal.HasONB σ J v L ∧
      (∀ L₁ : Submodule (UnitaryLatticeOrthogonal.OEv F E v) (Fin M → UnitaryLatticeOrthogonal.Ev F E v), UnitaryLatticeOrthogonal.IsSDLat σ J v L₁ →
        ∃ g : HA (Fv F v) σ J, ∀ y, y ∈ L ↔ UnitaryLatticeOrthogonal.act σ J v g y ∈ L₁) ∧
      ∀ β : (v.adicCompletionIntegers F)ˣ,
        UnitaryLatticeOrthogonal.UnitVectors σ J v L ((β : v.adicCompletionIntegers F) : Fv F v)) ↔
    (SelfDualLatticeActions.HasOrthonormalBasis v σ J L ∧
      (∀ L' : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M), SelfDualLatticeActions.IsSelfDualLat v σ J L' →
        ∃ g : HA (Fv F v) σ J, ∀ y, y ∈ L ↔ SelfDualLatticeActions.act v σ J g y ∈ L') ∧
      ∀ β : (v.adicCompletionIntegers F)ˣ,
        SelfDualLatticeActions.UnitVectorClaims v σ J L ((β : v.adicCompletionIntegers F) : Fv F v)) :=
  and_congr (hasONB_iff σ J v L) (and_congr Iff.rfl (forall_congr' fun β =>
    unitVectors_iff σ J v h hJ L _ (β.isUnit.map (v.adicCompletionIntegers F).subtype)))
end GlobalTheory.SelfDualLatticeCompare
