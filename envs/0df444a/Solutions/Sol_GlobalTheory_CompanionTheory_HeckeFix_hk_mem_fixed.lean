-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeFix.hk_mem_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:58.501476+00:00
-- url     : https://prove2.me/submissions/89e3745b-39f6-481a-bbd3-2e0622bd8a1f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HkMemFixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeFix
namespace GlobalTheory.CompanionTheory.HeckeFix
theorem _root_.solution : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι] (K : Subgroup (GL ι F)) (e : GL ι F → ℂ), IsHk K e → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V), ∀ v ∈ fixed ρ K, hk ρ K e v ∈ fixed ρ K ∧ ∀ g : GL ι F, (∀ q : GL ι F ⧸ K, e (g * q.out) = e q.out) → True := by
  intro F _ _ _ _ ι _ _ K e hE V _ _ ρ v hv
  refine ⟨?_, fun _ _ => trivial⟩
  have hfix : ∀ c ∈ K, ρ c v = v := by
    intro c hc
    have := hv ⟨c, hc⟩
    simpa using this
  have hbi := hE.2.2.2
  intro h
  have hk' : (h : GL ι F) ∈ K := h.2
  set k : GL ι F := (h : GL ι F) with hkdef
  have hinj : Function.Injective (ρ k : V →ₗ[ℂ] V) := by
    intro x y hxy
    have h1 : ∀ z, ρ k⁻¹ (ρ k z) = z := by
      intro z
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← h1 x, ← h1 y, hxy]
  have hstep : ∀ q : GL ι F ⧸ K, ρ k (e q.out • ρ q.out v) =
      e (k • q).out • ρ (k • q).out v := by
    intro q
    have hq : k • q = QuotientGroup.mk (k * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K (k * q.out)
    rw [hq, hc, hbi k hk' c c.2 q.out, map_smul, map_mul, Module.End.mul_apply, map_mul,
      Module.End.mul_apply, hfix c c.2]
  have hsum : ρ k (hk ρ K e v) = hk ρ K e v := by
    unfold hk
    have h1 := AddMonoidHom.map_finsum_of_injective (ρ k : V →ₗ[ℂ] V).toAddMonoidHom hinj
      (fun q : GL ι F ⧸ K => e q.out • ρ q.out v)
    simp only [LinearMap.toAddMonoidHom_coe] at h1
    rw [h1]
    simp only [hstep]
    exact finsum_comp_equiv (f := fun q : GL ι F ⧸ K => e q.out • ρ q.out v) (MulAction.toPerm k)
  simpa using hsum
end GlobalTheory.CompanionTheory.HeckeFix
