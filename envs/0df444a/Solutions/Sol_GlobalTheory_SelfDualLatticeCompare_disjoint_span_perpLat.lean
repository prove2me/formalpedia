-- Prove2me | solution 1 for GlobalTheory.SelfDualLatticeCompare.disjoint_span_perpLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:23:27.227544+00:00
-- url     : https://prove2.me/submissions/afead4ae-3279-4517-8e91-4c9e090cff98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_UnitaryLatticeOrthogonal
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualLatticeActions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_hR_self
import Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_hR_smul_right

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
    (L : Submodule (SelfDualLatticeActions.OEv E v) (SelfDualLatticeActions.Wv E v M)) (x : SelfDualLatticeActions.Wv E v M)
    (hx : IsUnit (qR (Fv F v) σ J x)) :
    Disjoint (Submodule.span (SelfDualLatticeActions.OEv E v) {x}) (SelfDualLatticeActions.perpLat v σ J x L) := by
  rw [Submodule.disjoint_def]
  intro y hy hy'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have h0 : hR (Fv F v) σ J x ((c : SelfDualLatticeActions.Ev E v) • x) = 0 := hy'.1
  rw [hR_smul_right, hR_self _ h hJ, (hx.map _).mul_left_eq_zero] at h0
  show (c : SelfDualLatticeActions.Ev E v) • x = 0
  rw [h0, zero_smul]
end GlobalTheory.SelfDualLatticeCompare
