-- Prove2me | solution 1 for GlobalTheory.UnramSelfDual.exists_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:58:30.391238+00:00
-- url     : https://prove2.me/submissions/ed88ab1f-c814-4e2a-819f-57490e7925f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsSubConjNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsReflection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SelfDualLatticeProjectionMemOfUnitLength
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_StabLatInfStabVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RestrHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsOfFixedInt
import Theorems.Thm_GlobalTheory_UnramSelfDual_exists_next
import Theorems.Thm_GlobalTheory_UnramSelfDual_exists_family
import Theorems.Thm_GlobalTheory_UnramSelfDual_exists_uniformiser
import Theorems.Thm_GlobalTheory_UnramSelfDual_exists_norm
import Theorems.Thm_GlobalTheory_UnramSelfDual_JR_herm
import Theorems.Thm_GlobalTheory_UnramSelfDual_sd_iff
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SelfDualLatticeActions_sigR_mem
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryLatticeOrthogonal_sigR_mem
import Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_sigR_sigR
import Theorems.Thm_GlobalTheory_UnramConjUnit_exists_sub_conj_unit


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
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal Formalism.UG
open GlobalTheory GlobalTheory.UnramSelfDual
open GlobalTheory.SelfDualLatticeCompare IsLocalRing
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} (v : HeightOneSpectrum (𝓞 F))
variable {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
namespace GlobalTheory.UnramSelfDual
theorem _root_.solution (h : IsCMExt F E σ) (hv : UnramAt F E v) {m : ℕ}
    {J : Matrix (Fin (m + 1)) (Fin (m + 1)) E} (hJ : IsHermND σ J)
    {L : Submodule (OEv F E v) (Fin (m + 1) → Ev F E v)} (hL : IsSDLat σ J v L) :
    (∃ x ∈ L, hR (Fv F v) σ J x x = 1) ∧ ∀ x ∈ L, hR (Fv F v) σ J x x = 1 →
      ∃ e : Fin (m + 1) → Fin (m + 1) → Ev F E v, (∀ i, e i ∈ L) ∧
        (∀ i j, hform (sigR (Fv F v) σ) (JR (Fv F v) J) (e i) (e j) = if i = j then 1 else 0) ∧
        e 0 = x := by
  obtain ⟨p, q, hp, hpc, hpq, hq, hloc⟩ := exists_uniformiser v h
  have hθ := GlobalTheory.UnramConjUnit.exists_sub_conj_unit F E σ h v hv
  have step := fun k (hk : k < m + 1) (e : Fin k → Fin (m + 1) → Ev F E v) heL he =>
    exists_next (sigR_sigR _ h) (JR_herm v hJ) (fun _ => sigR_mem σ v) hp hpc hpq hq hloc hθ
      (exists_norm v h hθ) hL.1 hL.2.1 (sd_iff v hL) hk (e := e) heL he
  refine ⟨?_, fun x hx hx1 =>
    exists_family (sigR_sigR _ h) (JR_herm v hJ) step hx hx1 m le_rfl⟩
  obtain ⟨y, hy, -, hy1⟩ := step 0 (Nat.succ_pos m) Fin.elim0 (fun i => i.elim0)
    (fun i => i.elim0)
  exact ⟨y, hy, hy1⟩
end GlobalTheory.UnramSelfDual
