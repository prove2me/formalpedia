-- Prove2me | solution 1 for MassDataIdxLatFree.exists_gl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:29:31.862357+00:00
-- url     : https://prove2.me/submissions/191ab0da-55a6-42c5-a897-88296d12ec9e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_ExistsGl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxLatFree
open scoped Matrix
open Module
variable {K : Type} [Field K] (O : ValuationSubring K) [IsPrincipalIdealRing O]
  {n : Type} [Fintype n] [DecidableEq n]
namespace MassDataIdxLatFree
theorem _root_.solution (M : Submodule O (n → K)) (hfg : M.FG)
    (hsp : Submodule.span K (M : Set (n → K)) = ⊤) :
    ∃ P : GL n K, ∀ y, y ∈ M ↔ ∀ i, (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ y) i ∈ O := by
  classical
  haveI : Module.Finite O M := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free O M := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex O M
  let bM : Module.Basis ι O M := Module.Free.chooseBasis O M
  let v : ι → (n → K) := fun i => (bM i : n → K)
  have hliO : LinearIndependent O v := bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent K v := (LinearIndependent.iff_fractionRing O K).mp hliO
  have hsmul : ∀ (r : O) (w : n → K), r • w = (r : K) • w := fun r w => rfl
  have hMsp : (M : Set (n → K)) ⊆ Submodule.span K (Set.range v) := by
    intro y hy
    have h1 := bM.sum_repr ⟨y, hy⟩
    have h2 : y = ∑ i, (bM.repr ⟨y, hy⟩ i : K) • v i := by
      have h3 := congrArg (fun m : M => (m : n → K)) h1
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
      conv_lhs => rw [← h3]
      rfl
    rw [h2]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← hsp]
    exact Submodule.span_le.mpr hMsp
  let bK : Module.Basis ι K (n → K) := Module.Basis.mk hli hsp
  have hbK : ∀ i, bK i = v i := fun i => Module.Basis.mk_apply hli hsp i
  have hcard : Fintype.card ι = Fintype.card n := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fintype_fun_eq_card]
  let e : ι ≃ n := Fintype.equivOfCardEq hcard
  let Pm : Matrix n n K := fun i j => bK (e.symm j) i
  let Qm : Matrix n n K := fun i j => bK.repr (Pi.single j 1) (e.symm i)
  have hQ : ∀ y : n → K, Qm *ᵥ y = fun i => bK.repr y (e.symm i) := by
    intro y
    funext i
    have hy : y = ∑ j, y j • (Pi.single j (1 : K) : n → K) := by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hy]
    simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, Qm]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hQP : Qm * Pm = 1 := by
    ext i k
    have h1 := congrFun (hQ (fun j => Pm j k)) i
    rw [Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct] at h1
    rw [h1]
    have h2 : (fun j => Pm j k) = bK (e.symm k) := rfl
    rw [h2, Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
    simp [e.symm.injective.eq_iff, eq_comm]
  have hPQ : Pm * Qm = 1 := mul_eq_one_comm.mp hQP
  refine ⟨(⟨Pm, Qm, hPQ, hQP⟩ : GL n K), fun y => ?_⟩
  show y ∈ M ↔ ∀ i, (Qm *ᵥ y) i ∈ O
  rw [hQ]
  constructor
  · intro hy i
    have h2 : y = ∑ j, (bM.repr ⟨y, hy⟩ j : K) • bK j := by
      have h1 := bM.sum_repr ⟨y, hy⟩
      have h3 := congrArg (fun m : M => (m : n → K)) h1
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
      conv_lhs => rw [← h3]
      exact Finset.sum_congr rfl (fun j _ => by rw [hbK]; rfl)
    have h4 : bK.repr y (e.symm i) = (bM.repr ⟨y, hy⟩ (e.symm i) : K) := by
      conv_lhs => rw [h2]
      simp [Module.Basis.repr_self, Finsupp.single_apply]
    show bK.repr y (e.symm i) ∈ O
    rw [h4]
    exact (bM.repr ⟨y, hy⟩ (e.symm i)).2
  · intro hc
    have hc' : ∀ j, bK.repr y j ∈ O := by
      intro j
      have := hc (e j)
      simpa using this
    rw [← bK.sum_repr y]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    have h5 : bK.repr y j • bK j = (⟨bK.repr y j, hc' j⟩ : O) • (bM j : n → K) := by
      rw [hsmul, hbK]
    rw [h5]
    exact M.smul_mem _ (bM j).2
end MassDataIdxLatFree
