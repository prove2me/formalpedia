-- Prove2me | solution 1 for GlobalTheory.LocalTraceSum.exists_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:43:01.394139+00:00
-- url     : https://prove2.me/submissions/cf6becdf-94fe-4ce7-b07e-e52a4c596986

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TraceEqSumLocalTracesAbovePrime
import Theorems.Thm_GlobalTheory_LocalTraceSum_t2
import Theorems.Thm_GlobalTheory_LocalTraceSum_isOpen_lt
import Theorems.Thm_GlobalTheory_LocalTraceSum_contSMul
import Theorems.Thm_GlobalTheory_LocalTraceSum_norm_l_lt
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.LocalTraceSum
open Filter Topology TensorProduct
variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime]
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra ℚ_[l] K] {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]
namespace GlobalTheory.LocalTraceSum
theorem _root_.solution (hc : Continuous (algebraMap ℚ_[l] K)) (ι : F →+* K) (hι : DenseRange ι)
    (σ : F →+* Ω) (h : ∀ a : F, valuation K (ι a) < 1 → ‖σ a‖ ≤ 1) :
    ∃ τ : K →ₐ[ℚ_[l]] Ω, ∀ a, τ (ι a) = σ a := by
  have := contSMul hc
  have : T2Space K := t2
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] _).injective
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ_[l] _).injective
  let φ : ℚ_[l] ⊗[ℚ] F →ₐ[ℚ_[l]] K :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) ι.toRatAlgHom (fun _ _ => .all _ _)
  let ψ : ℚ_[l] ⊗[ℚ] F →ₐ[ℚ_[l]] Ω :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) σ.toRatAlgHom (fun _ _ => .all _ _)
  have hφ : ∀ c a, φ (c ⊗ₜ a) = c • ι a := fun c a => by simp [φ, Algebra.smul_def]
  have hψ : ∀ c a, ψ (c ⊗ₜ a) = c • σ a := fun c a => by simp [ψ, Algebra.smul_def]
  have hsurj : Function.Surjective φ := by
    have hcl : IsClosed (LinearMap.range φ.toLinearMap : Set K) :=
      Submodule.closed_of_finiteDimensional _
    intro x
    have : x ∈ (LinearMap.range φ.toLinearMap : Set K) := by
      refine hι.induction_on x hcl fun a => ⟨1 ⊗ₜ a, ?_⟩
      simp [hφ]
    exact this
  let G : AddSubgroup (K × Ω) := ((ι.prod σ).toAddMonoidHom.range).topologicalClosure
  have hG : ∀ z, (φ z, ψ z) ∈ G := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; exact G.zero_mem
    | add x y hx hy => simpa using G.add_mem hx hy
    | tmul c a =>
      rw [hφ, hψ]
      refine (Padic.denseRange_ratCast l).induction_on c ?_ fun q => ?_
      · exact (AddSubgroup.isClosed_topologicalClosure _).preimage
          (f := fun c : ℚ_[l] => (c • ι a, c • σ a)) (by fun_prop)
      · refine AddSubgroup.le_topologicalClosure _ ⟨(q : F) * a, ?_⟩
        simp [Algebra.smul_def]
  have hl : (l : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hl' : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hker : ∀ z, φ z = 0 → ψ z = 0 := by
    intro z hz
    have hb : ∀ k : ℕ, ‖ψ z‖ ≤ ‖(l : Ω)‖ ^ k := by
      intro k
      have hcl : IsClosed ({w : K × Ω | valuation K w.1 < valuation K ((l : K) ^ k)}ᶜ ∪
          {w : K × Ω | ‖w.2‖ ≤ ‖(l : Ω)‖ ^ k}) :=
        (((isOpen_lt _).preimage continuous_fst).isClosed_compl).union
          (isClosed_le (by fun_prop) continuous_const)
      have hsub := closure_minimal (s := ((ι.prod σ).toAddMonoidHom.range : Set (K × Ω))) ?_ hcl
      · rcases hsub (hG z) with h1 | h1
        · exfalso
          apply h1
          simp only [Set.mem_setOf_eq, hz, map_zero]
          exact zero_lt_iff.2 (by simp [hl])
        · exact h1
      · rintro _ ⟨a, rfl⟩
        by_cases ha : valuation K (ι a) < valuation K ((l : K) ^ k)
        · right
          have h2 := h (a / (l : F) ^ k) (by
            rw [map_div₀, map_div₀, div_lt_one₀ (zero_lt_iff.2 (by simp [hl]))]
            simpa using ha)
          rw [map_div₀, norm_div, div_le_one (by simp [hl'])] at h2
          simpa using h2
        · left; exact ha
    have := ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
      (norm_l_lt (l := l) (Ω := Ω))) hb
    exact norm_le_zero_iff.1 this
  refine ⟨AlgHom.liftOfSurjective φ hsurj ψ (fun z hz => hker z hz), fun a => ?_⟩
  have h1 : ι a = φ (1 ⊗ₜ a) := by simp [hφ]
  rw [h1]
  exact (AlgHom.liftOfSurjective_apply φ hsurj ψ _ _).trans (by rw [hψ, one_smul])
end GlobalTheory.LocalTraceSum
