-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LagFun.exists_invariant_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:25:55.077831+00:00
-- url     : https://prove2.me/submissions/888d31ef-605e-4f73-8e56-f8827d427a81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsInvariantForm
import Theorems.Thm_GlobalTheory_CompanionTheory_LagFun_exists_param

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LagFun
namespace GlobalTheory.CompanionTheory.LagFun
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (κ : Type) [Fintype κ] (ψ : AddChar k ℂ), Continuous ψ → ψ ≠ 1 → ∀ large₂ : Submodule k ((κ → k) × (κ → k)), (∀ w ∈ large₂, ∀ w' ∈ large₂, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) → ∃ l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ, (∃ φ ∈ SB (κ → k), l φ ≠ 0) ∧ ∀ w ∈ large₂, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ := by
  intro k _ _ _ _ _ κ _ ψ hψ _ large₂ hL
  obtain ⟨n, j, σ, p, hp, hσ, hj⟩ := exists_param large₂
  have hT2 : T2Space k := by
    let := IsTopologicalAddGroup.rightUniformSpace k
    have := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  have hlc : LocallyCompactSpace k := inferInstance
  have htd : TotallyDisconnectedSpace k := by
    let := IsTopologicalAddGroup.rightUniformSpace k
    have := isUniformAddGroup_of_addCommGroup (G := k)
    have : NonarchimedeanAddGroup k := ⟨fun U hU => by
      obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hU
      exact ⟨⟨(Valued.v (R := k)).restrict.ltAddSubgroup γ, by
        simpa [Valuation.ltAddSubgroup] using Valued.isOpen_ball k γ⟩, hγ⟩⟩
    infer_instance
  let : MeasurableSpace (Fin n → k) := borel _
  have : BorelSpace (Fin n → k) := ⟨rfl⟩
  set μ : Measure (Fin n → k) := Measure.addHaar
  have cj : Continuous j := j.continuous_on_pi
  have cσ : Continuous σ := σ.continuous_on_pi
  have cp : Continuous p := p.continuous_on_pi
  have hce : Topology.IsClosedEmbedding j := Function.LeftInverse.isClosedEmbedding hp cp cj
  set g : (Fin n → k) → ℂ := fun t => ψ (⅟(2 : k) * (j t ⬝ᵥ σ t)) with hg
  have cg : Continuous g := hψ.comp (continuous_const.mul (cj.dotProduct cσ))
  set S : Submodule ℂ ((κ → k) → ℂ) :=
    { carrier := {φ | Integrable (fun t => g t * φ (j t)) μ}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Pi.add_apply, mul_add]
        exact Integrable.add ha hb
      smul_mem' := fun c a ha => by
        simpa only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm] using Integrable.const_mul ha c }
  have memS : ∀ φ, φ ∈ S ↔ Integrable (fun t => g t * φ (j t)) μ := fun _ => Iff.rfl
  set l₀ : S →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∫ t, g t * φ.1 (j t) ∂μ
      map_add' := fun a b => by
        rw [← integral_add a.2 b.2]
        simp [mul_add]
      map_smul' := fun c a => by
        simp [← integral_const_mul, mul_left_comm] }
  obtain ⟨l, hl⟩ := l₀.exists_extend
  have hl' : ∀ φ ∈ S, l φ = ∫ t, g t * φ (j t) ∂μ := fun φ hφ => LinearMap.congr_fun hl ⟨φ, hφ⟩
  have cc : ∀ φ ∈ SB (κ → k), Continuous (fun t => g t * φ (j t)) ∧ HasCompactSupport (fun t => g t * φ (j t)) :=
    fun φ hφ => ⟨cg.mul (hφ.1.continuous.comp cj), (hφ.2.comp_isClosedEmbedding hce).mul_left⟩
  have hSB : ∀ φ ∈ SB (κ → k), φ ∈ S := fun φ hφ => (cc φ hφ).1.integrable_of_hasCompactSupport (cc φ hφ).2
  refine ⟨l, ?_, fun w hw φ hφ => ?_⟩
  · have ho : IsOpen {x : κ → k | 0 < (g (p x)).re} :=
      isOpen_lt continuous_const (Complex.continuous_re.comp (cg.comp cp))
    have h0 : (0 : κ → k) ∈ {x : κ → k | 0 < (g (p x)).re} := by simp [hg]
    obtain ⟨K, hK, hK0, hKs⟩ := exists_compact_subset ho h0
    obtain ⟨U, hU, hU0, hUs⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (H := κ → k)).exists_subset_of_mem_open hK0
      isOpen_interior
    have hU : IsClopen U := hU
    have hUK : U ⊆ K := hUs.trans interior_subset
    have hφ : U.indicator (fun _ => (1 : ℂ)) ∈ SB (κ → k) :=
      ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) hU).isLocallyConstant,
        HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem (fun h => hx (hUK h)) _⟩
    refine ⟨_, hφ, fun h => ?_⟩
    rw [hl' _ (hSB _ hφ)] at h
    have h2 := congrArg Complex.re h
    rw [← RCLike.re_to_complex, ← integral_re ((memS _).1 (hSB _ hφ))] at h2
    refine ne_of_gt ?_ h2
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
      (RCLike.continuous_re.comp (cc _ hφ).1) ((cc _ hφ).2.comp_left (g := RCLike.re) (map_zero _)) (fun t => ?_) ?_
    · by_cases ht : j t ∈ U
      · have := hKs (hUK ht)
        simp only [Set.mem_ofPred_eq, hp] at this
        simpa [ht] using this.le
      · simp [ht]
    · simp [hU0, hg]
  · obtain ⟨t₁, ht₁⟩ := hj w hw
    have key : (fun t => g t * schr ψ w φ (j t)) = fun t => g (t + t₁) * φ (j (t + t₁)) := by
      funext t
      have e1 := hL _ (hσ t) w hw
      have e2 := hL _ (hσ t₁) w hw
      have e3 := hL _ (hσ t) _ (hσ t₁)
      simp only [← ht₁] at e1 e2 e3
      simp only [hg, schr, ← ht₁, map_add, ← mul_assoc, ← AddChar.map_add_eq_mul, add_dotProduct, dotProduct_add]
      congr 2
      have h2 : ⅟(2 : k) * 2 = 1 := invOf_mul_self _
      linear_combination e1 + ⅟(2 : k) * e2 - ⅟(2 : k) * e3 - (j t₁ ⬝ᵥ σ t) * h2
    have hi := (memS _).1 (hSB _ hφ)
    rw [hl' _ (hSB _ hφ), hl' _ ((memS _).2 (key ▸ hi.comp_add_right t₁)), key]
    exact integral_add_right_eq_self (fun t => g t * φ (j t)) t₁
end GlobalTheory.CompanionTheory.LagFun
