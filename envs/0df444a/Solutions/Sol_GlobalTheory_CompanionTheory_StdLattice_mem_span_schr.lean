-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.StdLattice.mem_span_schr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:28:50.052069+00:00
-- url     : https://prove2.me/submissions/41f0f385-3c34-42be-bfdb-1f4847ab5ba5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SchrodingerModelSelfDualLatticeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsStd
import Theorems.Thm_GlobalTheory_CompanionTheory_StdLattice_exists_nhds_invariant
import Theorems.Thm_GlobalTheory_CompanionTheory_StdLattice_mem_span_cosets
import Theorems.Thm_GlobalTheory_T_indicator_in_schrodinger_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.StdLattice
variable {R : Type} [CommRing R] {κ : Type} [Fintype κ]
variable [TopologicalSpace R]
variable [IsTopologicalRing R] [Invertible (2 : R)]
namespace GlobalTheory.CompanionTheory.StdLattice
theorem _root_.solution [LocallyCompactSpace R] [T2Space R] {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ}
    (h : GoodChar ψ O u) {f : (κ → R) → ℂ} (hf : f ∈ SB (κ → R)) :
    f ∈ Submodule.span ℂ (Set.range fun w => schr ψ w (ind O κ)) := by
  classical
  set V := Submodule.span ℂ (Set.range fun w => schr ψ w (ind O κ)) with hV
  have htr : ∀ g ∈ Submodule.span ℂ {g : (κ → R) → ℂ | ∃ y, g = schr ψ (0, y) (ind O κ)},
      ∀ a : κ → R, (fun x => g (x + a)) ∈ V := by
    intro g hg a
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨y, rfl⟩ := hg
      have heq : (fun x => schr ψ (0, y) (ind O κ) (x + a)) =
          ψ (a ⬝ᵥ y - ⅟2 * (a ⬝ᵥ y)) • schr ψ (a, y) (ind O κ) := by
        funext x
        simp only [schr, Pi.smul_apply, smul_eq_mul, add_zero, zero_dotProduct, mul_zero]
        rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_dotProduct,
          show x ⬝ᵥ y + a ⬝ᵥ y = a ⬝ᵥ y - ⅟2 * (a ⬝ᵥ y) + (x ⬝ᵥ y + ⅟2 * (a ⬝ᵥ y)) by ring]
      rw [heq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, y), rfl⟩)
    | zero => exact V.zero_mem
    | add g1 g2 _ _ h1 h2 => exact V.add_mem h1 h2
    | smul c g _ h => exact V.smul_mem c h
  have hsb : IsLocallyConstant f ∧ HasCompactSupport f := hf
  have hA := exists_nhds_invariant hf
  rw [nhds_pi] at hA
  obtain ⟨I, t, ht, hIt⟩ := Filter.mem_pi'.1 hA
  have hU' : (⋂ i, t i) ∈ 𝓝 (0 : R) := Filter.iInter_mem.2 fun i => ht i
  obtain ⟨v, hv⟩ := h.basis _ (Filter.inter_mem hU' (h.isOpen.mem_nhds O.zero_mem))
  have hvO : ((v : Rˣ) : R) ∈ O := by
    have h1 := (hv 1 O.one_mem).2
    rwa [mul_one] at h1
  have hboxU : ∀ w ∈ box O v κ, ∀ y ∈ tsupport f, f (y + w) = f y := by
    intro w hw
    have hw' : ∀ i, ((v⁻¹ : Rˣ) : R) * w i ∈ O := hw
    have hwI : w ∈ (↑I : Set κ).pi t := fun i _ => by
      have h2 := (hv _ (hw' i)).1
      rw [Units.mul_inv_cancel_left] at h2
      exact Set.mem_iInter.1 h2 i
    exact hIt hwI
  have hbox_open : IsOpen ((box O v κ : AddSubgroup (κ → R)) : Set (κ → R)) := by
    show IsOpen {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O}
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i =>
      h.isOpen.preimage (continuous_const.mul (continuous_apply i))
  have hmem := mem_span_cosets hsb.2 (box O v κ) hbox_open (fun y hy w hw => hboxU w hw y hy)
  refine Submodule.span_le.2 ?_ hmem
  rintro _ ⟨a, rfl⟩
  exact htr _ (GlobalTheory.T.indicator_in_schrodinger_span ψ O u v h hvO) a
end GlobalTheory.CompanionTheory.StdLattice
