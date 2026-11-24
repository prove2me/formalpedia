-- Prove2me | solution 1 for GlobalTheory.InertCompletion.exists_ringEquiv_completion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:21:02.975868+00:00
-- url     : https://prove2.me/submissions/ddf16b6d-ab8d-478d-96c4-c490133fc83f

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IsFieldAdicCompletionTensorOfInert
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsRingEquivTensorInertAdicCompletion
import Theorems.Thm_GlobalTheory_InertCompletion_exists_completion_map
import Theorems.Thm_GlobalTheory_InertCompletion_continuous_of_valued_eq
import Theorems.Thm_GlobalTheory_InertCompletion_surjective_of_continuous
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_InertField_isField_of_inert
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_SelfDualGenus_exists_of_locConj_eq
import Theorems.Thm_GlobalTheory_SelfDualGenus_exists_sub_conj_notMem
import Theorems.Thm_GlobalTheory_SelfDualGenus_locConj_locConj
import Theorems.Thm_GlobalTheory_SelfDualGenus_locConj_locEmb
import Theorems.Thm_GlobalTheory_SelfDualGenus_locConj_tmul
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
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
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
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.InertCompletion
namespace GlobalTheory.InertCompletion
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E)), IsInertAt (maximalRealSubfield E) E v P → ∀ σ : P.adicCompletion E →+* P.adicCompletion E, (∀ x : E, σ (algebraMap E (P.adicCompletion E) x) = algebraMap E (P.adicCompletion E) (ReciprocityTheory.ChartRestriction.G.FD.cc x)) → (∀ x, Valued.v (σ x) = Valued.v x) → ∃ ψ : LocAlg v ≃+* P.adicCompletion E, (∀ x : E, ψ (locEmb v x) = algebraMap E (P.adicCompletion E) x) ∧ (∀ z, ψ (locConj v z) = σ (ψ z)) ∧ ∀ z, z ∈ locOrder v ↔ Valued.v (ψ z) ≤ 1 := by
  intro E _ _ _ _ v P h σ hσ hσv
  obtain ⟨φ, hc, hφ, hv⟩ := exists_completion_map v P h
  obtain ⟨ψ, hψ⟩ : ∃ ψ : LocAlg v →+* P.adicCompletion E,
      ∀ a x, ψ (a ⊗ₜ x) = φ a * algebraMap E _ x := by
    letI : Algebra (maximalRealSubfield E) (P.adicCompletion E) :=
      ((algebraMap E (P.adicCompletion E)).comp (algebraMap (maximalRealSubfield E) E)).toAlgebra
    let f : E →ₐ[maximalRealSubfield E] P.adicCompletion E := ⟨algebraMap E _, fun _ => rfl⟩
    let g : v.adicCompletion (maximalRealSubfield E) →ₐ[maximalRealSubfield E] P.adicCompletion E :=
      ⟨φ, hφ⟩
    exact ⟨(Algebra.TensorProduct.productMap g f).toRingHom, fun a x => rfl⟩
  have hF : IsField (LocAlg v) := InertField.isField_of_inert _ E
    (Algebra.IsQuadraticExtension.finrank_eq_two _ E) v (by
      rw [show Ideal.map _ v.asIdeal = P.asIdeal from h]; exact P.isPrime)
  have hinj : Function.Injective ψ := by
    letI := hF.toField
    exact ψ.injective
  have hE : ∀ x : E, ψ (locEmb v x) = algebraMap E _ x := fun x =>
    (hψ 1 x).trans (by rw [map_one, one_mul])
  have hA : ∀ a, ψ (algebraMap _ (LocAlg v) a) = φ a := fun a =>
    (hψ a 1).trans (by rw [map_one, mul_one])
  have hσφ : ∀ a, σ (φ a) = φ a := fun a =>
    congrFun ((HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) v).equalizer
      ((continuous_of_valued_eq P σ hσv).comp hc) hc (funext fun x => by
        simp only [Function.comp_apply, hφ, hσ]
        exact congrArg _ ((IsCMField.complexConj E).commutes x))) a
  have hconj : ∀ z, ψ (locConj v z) = σ (ψ z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rw [locConj_tmul, hψ, hψ, map_mul, hσφ, hσ]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hint : ∀ s : 𝓞 E, Valued.v (algebraMap E (P.adicCompletion E) (s : E)) ≤ 1 := fun s =>
    (Idele.valued_algebraMap P (s : E)).trans_le (P.valuation_le_one s)
  refine ⟨RingEquiv.ofBijective ψ ⟨hinj, surjective_of_continuous v P φ hc ψ hψ⟩, hE, hconj,
    fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · change Valued.v (ψ z) ≤ 1
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact (congrArg Valued.v (hE a)).trans_le (hint a)
    | algebraMap a => exact ((congrArg Valued.v (hA a)).trans (hv a)).trans_le a.2
    | add x y _ _ hx hy => rw [map_add]; exact Valuation.map_add_le _ hx hy
    | mul x y _ _ hx hy => rw [map_mul, map_mul]; exact mul_le_one' hx hy
  · replace hz : Valued.v (ψ z) ≤ 1 := hz
    have fix : ∀ w : LocAlg v, locConj v w = w → Valued.v (ψ w) ≤ 1 → w ∈ locOrder v := by
      intro w hw hw1
      obtain ⟨a, rfl⟩ := exists_of_locConj_eq v hw
      rw [hA, hv] at hw1
      exact (locOrder v).algebraMap_mem ⟨a, hw1⟩
    obtain ⟨θ, hθ⟩ := exists_sub_conj_notMem P.asIdeal P.isPrime.ne_top
    have hδ1 : P.valuation E ((θ : E) - ReciprocityTheory.ChartRestriction.G.FD.cc (θ : E)) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) P).2 hθ
    set δ : E := (θ : E) - ReciprocityTheory.ChartRestriction.G.FD.cc (θ : E) with hδ
    have hδ0 : δ ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hδ1
      exact zero_ne_one hδ1
    have hcδ : ReciprocityTheory.ChartRestriction.G.FD.cc δ⁻¹ = -δ⁻¹ := by
      have : ReciprocityTheory.ChartRestriction.G.FD.cc δ = -δ := by simp [hδ, ReciprocityTheory.ChartRestriction.G.FD.cc]
      rw [← inv_neg, ← this]
      exact map_inv₀ (IsCMField.complexConj E) δ
    have hone : locEmb v δ⁻¹ * (locEmb v θ - locEmb v (ReciprocityTheory.ChartRestriction.G.FD.cc (θ : E))) = 1 := by
      rw [← map_sub, ← map_mul, inv_mul_cancel₀ hδ0, map_one]
    set b : LocAlg v := (z - locConj v z) * locEmb v δ⁻¹ with hb
    have hb1 : locConj v b = b := by
      rw [hb, map_mul, map_sub, locConj_locConj, locConj_locEmb, hcδ, map_neg]; ring
    have hb2 : Valued.v (ψ b) ≤ 1 := by
      rw [hb, map_mul, map_mul, hE, Idele.valued_algebraMap, map_inv₀, hδ1, inv_one, mul_one,
        map_sub, hconj]
      exact Valuation.map_sub_le _ hz ((hσv _).trans_le hz)
    have ha1 : locConj v (z - b * locEmb v θ) = z - b * locEmb v θ := by
      rw [map_sub, map_mul, hb1, locConj_locEmb, hb]
      linear_combination (z - locConj v z) * hone
    have ha2 : Valued.v (ψ (z - b * locEmb v θ)) ≤ 1 := by
      rw [map_sub, map_mul, hE]
      refine Valuation.map_sub_le _ hz ?_
      rw [map_mul]
      exact mul_le_one' hb2 (hint θ)
    rw [← sub_add_cancel z (b * locEmb v θ)]
    exact add_mem (fix _ ha1 ha2) (mul_mem (fix _ hb1 hb2) (locEmb_mem_locOrder v θ))
end GlobalTheory.InertCompletion
