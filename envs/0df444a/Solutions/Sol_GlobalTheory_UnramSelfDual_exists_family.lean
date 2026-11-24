-- Prove2me | solution 1 for GlobalTheory.UnramSelfDual.exists_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:08:27.570805+00:00
-- url     : https://prove2.me/submissions/db36076f-2468-43a4-8fad-a583c7b526e6

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
import Theorems.Thm_GlobalTheory_UnramSelfDual_h_conj
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal Formalism.UG
open GlobalTheory GlobalTheory.UnramSelfDual
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {O : Subalgebra R A}
  {c : A →+* A} {M : ℕ} {J : Matrix (Fin M) (Fin M) A} {L : Submodule O (Fin M → A)}
namespace GlobalTheory.UnramSelfDual
theorem _root_.solution (hc : ∀ a, c (c a) = a) (hJ : ∀ i j, c (J j i) = J i j)
    (step : ∀ k < M, ∀ e : Fin k → Fin M → A, (∀ i, e i ∈ L) →
      (∀ i j, hform c J (e i) (e j) = if i = j then 1 else 0) →
      ∃ y ∈ L, (∀ i, hform c J (e i) y = 0) ∧ hform c J y y = 1)
    {x : Fin M → A} (hx : x ∈ L) (hx1 : hform c J x x = 1) (k : ℕ) (hk : k + 1 ≤ M) :
    ∃ e : Fin (k + 1) → Fin M → A, (∀ i, e i ∈ L) ∧
      (∀ i j, hform c J (e i) (e j) = if i = j then 1 else 0) ∧ e 0 = x := by
  induction k with
  | zero => exact ⟨fun _ => x, fun _ => hx, fun i j => by
      rw [hx1, if_pos (Subsingleton.elim (α := Fin 1) i j)], rfl⟩
  | succ k ih =>
    obtain ⟨e, heL, he, he0⟩ := ih (by omega)
    obtain ⟨y, hy, hy0, hy1⟩ := step (k + 1) (by omega) e heL he
    refine ⟨Fin.snoc (α := fun _ => Fin M → A) e y, fun i => ?_, fun i j => ?_, ?_⟩
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using hy
      · simpa using heL i
    · refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hy1
      · have := h_conj hc hJ (e j) y
        rw [hy0, map_zero] at this
        simp [← this, (Fin.castSucc_lt_last j).ne']
      · simp [hy0, (Fin.castSucc_lt_last i).ne]
      · simp [he]
    · rw [← he0, ← Fin.castSucc_zero, Fin.snoc_castSucc]
end GlobalTheory.UnramSelfDual
