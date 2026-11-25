-- Prove2me | solution 1 for GlobalTheory.ResidueCharacterDense.exists_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:57:59.592811+00:00
-- url     : https://prove2.me/submissions/e81ea7ed-bd14-4fa1-8b8f-fa96a777660c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Theorems.Thm_GlobalTheory_ResidueCharacterDense_mem_smallIdeal
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
open ValuativeRel IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.ResidueCharacterDense
variable {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [NumberField F]
  (p : HeightOneSpectrum (𝓞 F)) {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [T2Space K] [CharZero K] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K] [ContinuousSMul ℚ_[l] K]
  (ι : F →+* K) (U : Set K)
namespace GlobalTheory.ResidueCharacterDense
theorem _root_.solution (hd : DenseRange ι) (hUo : IsOpen U)
    (hU : ∀ x, ι x ∈ U ↔ p.valuation F x < 1) (σ : F →+* PadicAlgCl l)
    (hσ : p.asIdeal = smallIdeal σ) :
    ∃ τ : K →ₐ[ℚ_[l]] PadicAlgCl l, ∀ x, τ (ι x) = σ x := by
  have hle : ∀ x : F, ι x ∈ U → ‖σ x‖ ≤ 1 := by
    intro x hx
    obtain ⟨n, d, hnd⟩ := p.exists_primeCompl_mul_eq_of_integer x ((hU x).mp hx).le
    have hd1 : 1 ≤ ‖σ (d : 𝓞 F)‖ := by
      have : (d : 𝓞 F) ∉ p.asIdeal := d.2
      exact not_lt.mp fun h => this (hσ.ge ((mem_smallIdeal σ _).mpr h))
    have hn : ‖σ n‖ ≤ 1 :=
      norm_le_one_of_isIntegral ((RingOfIntegers.isIntegral_coe n).map σ.toIntAlgHom)
    have h3 : ‖σ x‖ * ‖σ (d : 𝓞 F)‖ = ‖σ n‖ := by
      rw [← norm_mul, ← map_mul]; exact congrArg (fun t => ‖σ t‖) hnd
    nlinarith [norm_nonneg (σ x)]
  have h0 : (0 : K) ∈ U := by simpa using (hU 0).mpr (by simp)
  let b := Module.finBasis ℚ F
  let Φ : (Fin (Module.finrank ℚ F) → ℚ_[l]) →ₗ[ℚ_[l]] K :=
    Fintype.linearCombination ℚ_[l] fun i => ι (b i)
  let Ψ : (Fin (Module.finrank ℚ F) → ℚ_[l]) →ₗ[ℚ_[l]] PadicAlgCl l :=
    Fintype.linearCombination ℚ_[l] fun i => σ (b i)
  have hΦc : Continuous Φ := Φ.continuous_of_finiteDimensional
  have hΨc : Continuous Ψ := Ψ.continuous_of_finiteDimensional
  have hΦq : ∀ c : Fin (Module.finrank ℚ F) → ℚ,
      Φ (fun i => (c i : ℚ_[l])) = ι (∑ i, c i • b i) := by
    intro c
    simp [Φ, Fintype.linearCombination_apply, Algebra.smul_def]
  have hΨq : ∀ c : Fin (Module.finrank ℚ F) → ℚ,
      Ψ (fun i => (c i : ℚ_[l])) = σ (∑ i, c i • b i) := by
    intro c
    simp [Ψ, Fintype.linearCombination_apply, Algebra.smul_def]
  have hden : DenseRange (Pi.map fun (_ : Fin (Module.finrank ℚ F)) => (Rat.cast : ℚ → ℚ_[l])) :=
    DenseRange.piMap fun _ => Padic.denseRange_ratCast l
  have hcl : ∀ c, Φ c ∈ U → ‖Ψ c‖ ≤ 1 := by
    intro c hc
    have h1 := Dense.open_subset_closure_inter hden (hUo.preimage hΦc) hc
    have h2 : IsClosed {c | ‖Ψ c‖ ≤ 1} := isClosed_le hΨc.norm continuous_const
    refine h2.closure_subset_iff.mpr ?_ h1
    rintro _ ⟨hx, q, rfl⟩
    have e : (Pi.map (fun (_ : Fin (Module.finrank ℚ F)) => (Rat.cast : ℚ → ℚ_[l])) q) =
      fun i => (q i : ℚ_[l]) := rfl
    rw [e, Set.mem_preimage, hΦq] at hx
    rw [e, Set.mem_setOf_eq, hΨq]
    exact hle _ hx
  have hker : ∀ c, Φ c = 0 → Ψ c = 0 := by
    intro c hc
    by_contra hne
    have hpos : 0 < ‖Ψ c‖ := norm_pos_iff.mpr hne
    obtain ⟨a, ha⟩ := NormedField.exists_lt_norm ℚ_[l] (‖Ψ c‖⁻¹)
    have h1 := hcl (a • c) (by rw [map_smul, hc, smul_zero]; exact h0)
    rw [map_smul, norm_smul] at h1
    rw [inv_lt_iff_one_lt_mul₀ hpos] at ha
    linarith
  let φ : ℚ_[l] ⊗[ℚ] F →ₐ[ℚ_[l]] K :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) ι.toRatAlgHom fun _ _ => Commute.all _ _
  let ψ : ℚ_[l] ⊗[ℚ] F →ₐ[ℚ_[l]] PadicAlgCl l :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) σ.toRatAlgHom fun _ _ => Commute.all _ _
  have hφ : ∀ x, φ (1 ⊗ₜ x) = ι x := fun x => by simp [φ]
  have hψ : ∀ x, ψ (1 ⊗ₜ x) = σ x := fun x => by simp [ψ]
  have hsurj : Function.Surjective φ := by
    have h1 : IsClosed (LinearMap.range φ.toLinearMap : Set K) :=
      Submodule.closed_of_finiteDimensional _
    intro z
    have h2 : Set.range ι ⊆ (LinearMap.range φ.toLinearMap : Set K) := by
      rintro _ ⟨x, rfl⟩
      exact ⟨1 ⊗ₜ x, hφ x⟩
    exact h1.closure_subset_iff.mpr h2 (hd z)
  have hk : RingHom.ker φ.toRingHom ≤ RingHom.ker ψ.toRingHom := by
    intro t ht
    let B := Algebra.TensorProduct.basis ℚ_[l] b
    have e1 : φ t = Φ (B.repr t) := by
      conv_lhs => rw [← B.sum_repr t]
      simp [Φ, Fintype.linearCombination_apply, B, hφ]
    have e2 : ψ t = Ψ (B.repr t) := by
      conv_lhs => rw [← B.sum_repr t]
      simp [Ψ, Fintype.linearCombination_apply, B, hψ]
    have ht' : φ t = 0 := ht
    change ψ t = 0
    rw [e2]
    exact hker _ (e1 ▸ ht')
  refine ⟨AlgHom.liftOfSurjective φ hsurj ψ hk, fun x => ?_⟩
  rw [← hφ, ← hψ]
  simp
end GlobalTheory.ResidueCharacterDense
