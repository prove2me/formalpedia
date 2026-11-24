-- Prove2me | solution 1 for GlobalTheory.JR.OrbitProper.isCompact_set
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:26:01.723811+00:00
-- url     : https://prove2.me/submissions/c81739af-7bc8-4b74-89e1-c1152df2a7b2

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitInvariantMapProper
import Theorems.Thm_GlobalTheory_JR_OrbitProper_cont_sec
import Theorems.Thm_GlobalTheory_JR_OrbitProper_cont_act
import Theorems.Thm_GlobalTheory_JR_OrbitProper_cont_Bm
import Theorems.Thm_GlobalTheory_JR_OrbitProper_cont_Cm
import Theorems.Thm_GlobalTheory_JR_OrbitProper_contAt_hankel_inv
import Theorems.Thm_GlobalTheory_JR_OrbitProper_coe_eq
import Theorems.Thm_GlobalTheory_JR_OrbitProper_coe_inv_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OrbitProper
variable {r : ℕ} {F : Type} [NontriviallyNormedField F]
namespace GlobalTheory.JR.OrbitProper
theorem _root_.solution (C : Set (Gl r F)) (Ω : Set (Inv r F)) (hC : IsCompact C) (hΩ : IsCompact Ω)
    (hD : ∀ a ∈ Ω, Delta a ≠ 0) :
    IsCompact {p : GL (Fin r) F × Inv r F | p.2 ∈ Ω ∧ act p.1 (sec p.2) ∈ C} := by
  set Φ : Gl r F × Inv r F → (Matrix (Fin r) (Fin r) F × (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ) × Inv r F :=
    fun q => ((Bm q.1, MulOpposite.op ((hankel q.2)⁻¹ * Cm q.1)), q.2) with hΦdef
  have hΦ : ContinuousOn Φ (C ×ˢ Ω) := by
    intro q hq
    apply ContinuousAt.continuousWithinAt
    have h3 : ContinuousAt (fun q : Gl r F × Inv r F => (hankel q.2)⁻¹) q :=
      (contAt_hankel_inv q.2 (hD q.2 hq.2)).comp continuous_snd.continuousAt
    exact (((cont_Bm.comp continuous_fst).continuousAt).prodMk
      (MulOpposite.continuous_op.continuousAt.comp (h3.mul (cont_Cm.comp continuous_fst).continuousAt))).prodMk
      continuous_snd.continuousAt
  set e : GL (Fin r) F × Inv r F → (Matrix (Fin r) (Fin r) F × (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ) × Inv r F :=
    Prod.map (Units.embedProduct (Matrix (Fin r) (Fin r) F)) id with hedef
  have he : Topology.IsClosedEmbedding e :=
    Units.isClosedEmbedding_embedProduct.prodMap Topology.IsClosedEmbedding.id
  have hK : IsCompact (e ⁻¹' (Φ '' (C ×ˢ Ω))) :=
    he.isCompact_preimage ((hC.prod hΩ).image_of_continuousOn hΦ)
  have hS : IsClosed {p : GL (Fin r) F × Inv r F | p.2 ∈ Ω ∧ act p.1 (sec p.2) ∈ C} := by
    have hc : Continuous (fun p : GL (Fin r) F × Inv r F => act p.1 (sec p.2)) :=
      cont_act.comp (continuous_fst.prodMk (cont_sec.comp continuous_snd))
    exact (hΩ.isClosed.preimage continuous_snd).inter (hC.isClosed.preimage hc)
  refine hK.of_isClosed_subset hS ?_
  rintro ⟨g, a⟩ ⟨ha, hY⟩
  refine ⟨(act g (sec a), a), ⟨hY, ha⟩, ?_⟩
  simp only [hΦdef, hedef, Prod.map, id, Units.embedProduct_apply]
  rw [← coe_eq g a, ← coe_inv_eq g a (hD a ha)]
end GlobalTheory.JR.OrbitProper
