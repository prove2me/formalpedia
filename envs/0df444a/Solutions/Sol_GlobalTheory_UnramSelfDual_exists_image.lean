-- Prove2me | solution 1 for GlobalTheory.UnramSelfDual.exists_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:31:54.471171+00:00
-- url     : https://prove2.me/submissions/5fb149f7-2266-4237-9daa-d41994333af9

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
import Theorems.Thm_GlobalTheory_UnramSelfDual_h_unitary
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
theorem _root_.solution (hfg : L.FG) (hsp : Submodule.span A (L : Set (Fin M → A)) = ⊤)
    (hL : ∀ y, y ∈ L ↔ ∀ z ∈ L, hform c J z y ∈ O) {g : GL (Fin M) A} (hg : g ∈ UJ c J) :
    ∃ L' : Submodule O (Fin M → A), L'.FG ∧ Submodule.span A (L' : Set (Fin M → A)) = ⊤ ∧
      (∀ y, y ∈ L' ↔ ∀ z ∈ L', hform c J z y ∈ O) ∧
      ∀ y ∈ L, (g : Matrix (Fin M) (Fin M) A) *ᵥ y ∈ L' := by
  let f : (Fin M → A) →ₗ[A] (Fin M → A) := Matrix.mulVecLin (g : Matrix (Fin M) (Fin M) A)
  have hs : Function.Surjective f := fun y =>
    ⟨((g⁻¹ : GL (Fin M) A) : Matrix (Fin M) (Fin M) A) *ᵥ y, by
      simp only [f, Matrix.mulVecLin_apply]
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
  refine ⟨L.map (f.restrictScalars O), hfg.map _, ?_, fun y => ?_, fun y hy => ⟨y, hy, rfl⟩⟩
  · show Submodule.span A (f '' (L : Set (Fin M → A))) = ⊤
    rw [← Submodule.map_span, hsp, Submodule.map_top, LinearMap.range_eq_top.2 hs]
  · obtain ⟨y, rfl⟩ := hs y
    constructor
    · rintro ⟨y', hy', hyy⟩ _ ⟨z, hz, rfl⟩
      rw [← hyy]
      exact (h_unitary hg z y').symm ▸ (hL y').1 hy' z hz
    · intro h
      refine ⟨y, (hL y).2 fun z hz => ?_, rfl⟩
      exact h_unitary hg z y ▸ h _ ⟨z, hz, rfl⟩
end GlobalTheory.UnramSelfDual
