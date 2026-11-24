-- Prove2me | solution 1 for GlobalTheory.SelfDualGenus.mem_locLattice_iff_of_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:28:42.5678+00:00
-- url     : https://prove2.me/submissions/4fcb4ddc-4802-4ab6-9d9a-ea3732587519

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_locEmb_mem_locOrder_iff
import Theorems.Thm_GlobalTheory_SelfDualGenus_one_notMem
import Theorems.Thm_GlobalTheory_SelfDualGenus_exists_smul_col_mem
import Theorems.Thm_GlobalTheory_SelfDualGenus_mem_locLattice_of_smul_mem
import Theorems.Thm_GlobalTheory_SelfDualGenus_smul_mem_locLattice
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
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
open scoped Matrix TensorProduct nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LocalLattice
noncomputable section
open GlobalTheory GlobalTheory.SelfDualGenus
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
variable {L : Submodule (𝓞 E) (Fin r → E)}
namespace GlobalTheory.SelfDualGenus
theorem _root_.solution {g : GL (Fin r) E}
    (hg : ∀ x, (∃ s ∉ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x ∈ L) ↔
      ∀ i, (((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x) i ∈ semiLoc v)
    (x : Fin r → LocAlg v) :
    x ∈ locLattice v L ↔ ∀ i,
      (((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map (locEmb v) *ᵥ x) i ∈ locOrder v := by
  constructor
  · intro hx i
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      have := (locEmb_mem_locOrder_iff v _).2 ((hg y).1 ⟨1, one_notMem v, by simpa using hy⟩ i)
      rwa [RingHom.map_mulVec] at this
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Subalgebra.smul_mem _ hx c
  · intro hx
    have h1 : x = (g : Matrix (Fin r) (Fin r) E).map (locEmb v) *ᵥ
        (((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map (locEmb v) *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Units.mul_inv,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    rw [h1, Matrix.mulVec_eq_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨s, hs, h⟩ := exists_smul_col_mem v hg j
    have := smul_mem_locLattice v (hx j) (mem_locLattice_of_smul_mem v hs h)
    convert this using 1
    funext k
    simp [mul_comm]
end GlobalTheory.SelfDualGenus
