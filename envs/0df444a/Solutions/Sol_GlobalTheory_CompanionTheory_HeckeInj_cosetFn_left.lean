-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeInj.cosetFn_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:37:01.48681+00:00
-- url     : https://prove2.me/submissions/8a01c1f5-6ea3-46e4-9fa8-a75725a68c66

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeInj
variable {G : Type} [Group G]
namespace GlobalTheory.CompanionTheory.HeckeInj
theorem _root_.solution (K L : Subgroup G) [Fintype (K ⧸ L.subgroupOf K)] (g : G)
    (hL : ∀ l ∈ L, g⁻¹ * l * g ∈ K) (x : G) {k : G} (hk : k ∈ K) :
    cosetFn K L g (k * x) = cosetFn K L g x := by
  classical
  unfold cosetFn
  let kk : K := ⟨k, hk⟩
  refine Fintype.sum_equiv (MulAction.toPerm kk⁻¹ : Equiv.Perm (K ⧸ L.subgroupOf K)) _ _ fun q => ?_
  have hq : (MulAction.toPerm kk⁻¹ : Equiv.Perm (K ⧸ L.subgroupOf K)) q =
      (QuotientGroup.mk (kk⁻¹ * q.out) : K ⧸ L.subgroupOf K) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (L.subgroupOf K) (kk⁻¹ * q.out)
  have hcL : ((c : K) : G) ∈ L := Subgroup.mem_subgroupOf.1 c.2
  have hmk : (QuotientGroup.mk (((((MulAction.toPerm kk⁻¹ : Equiv.Perm (K ⧸ L.subgroupOf K)) q).out : K) : G) * g) : G ⧸ K)
      = QuotientGroup.mk (k⁻¹ * (((q.out : K) : G) * g)) := by
    rw [hq, hc, QuotientGroup.eq]
    have := hL _ (L.inv_mem hcL)
    simpa [kk, mul_assoc] using this
  have hiff : ((QuotientGroup.mk (k * x) : G ⧸ K) = QuotientGroup.mk (((q.out : K) : G) * g)) ↔
      ((QuotientGroup.mk x : G ⧸ K) = QuotientGroup.mk (k⁻¹ * (((q.out : K) : G) * g))) := by
    rw [QuotientGroup.eq, QuotientGroup.eq]
    simp [mul_assoc]
  rw [hmk]
  simp only [hiff]
end GlobalTheory.CompanionTheory.HeckeInj
