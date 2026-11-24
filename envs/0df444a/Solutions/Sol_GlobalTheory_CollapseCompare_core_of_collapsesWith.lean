-- Prove2me | solution 1 for GlobalTheory.CollapseCompare.core_of_collapsesWith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:54:12.805246+00:00
-- url     : https://prove2.me/submissions/6811fb0e-3020-4b66-9122-7b902c9be2c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_FlatOmegaSeries
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemNormalizerOfTri
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmulFrameMulFrameInvApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CoreIffCollapsesWith
import Theorems.Thm_GlobalTheory_CollapseCompare_exists_equivariant
import Theorems.Thm_GlobalTheory_CollapseCompare_omRep_smooth
import Theorems.Thm_GlobalTheory_CollapseCompare_isQuotInt_zero_iff
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_continuous_embX
import Theorems.Thm_GlobalTheory_RootEx_opE_om_embX
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_smoothRep
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_mul
import Theorems.Thm_GlobalTheory_SplitWeil_Model_om_one
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_stabilizer_om
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_eq_one_of_valuation_eq_one
import Theorems.Thm_GlobalTheory_SplitWeil_om_mul
import Theorems.Thm_GlobalTheory_SplitWeil_om_one
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_StepData_valuation_det_of_mem_KO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CollapseCompare
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k]
variable {ν : Measure k} {μX : Measure (GL n k)} {μG : Measure (GL (n ⊕ Fin c) k)}
  {J : Subgroup (GL (n ⊕ Fin c) k)} {bas : GL (n ⊕ Fin c) k} {ψ : AddChar k Circle} {μ : kˣ →* ℂˣ}
  {lam : J →* ℂˣ} {κ : ℝ}
namespace GlobalTheory.CollapseCompare
theorem _root_.solution (hc : 1 ≤ c) [ν.IsAddHaarMeasure] (hμ : IsOpen (μ.ker : Set kˣ))
    (hJ : IsOpen (J : Set (GL (n ⊕ Fin c) k))) {Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)}
    (hΦ : HasTargetType μ J lam Φ.1) (H : CollapsesWith ν μX μG J bas ψ μ lam Φ κ) :
    Core ν μX μG J bas ψ μ lam Φ.1 κ := by
  intro V' V A _ _ _ _ _ _ π σ θ b hθ hb φ v hv f hf Ξ hΞ z
  obtain rfl : Ξ = xiOneS ψ ν μ Φ J bas := Subtype.ext hΞ
  obtain rfl : f = integrand ψ ν μ Φ σ b θ φ v := funext fun h => hf h _ rfl
  by_cases h0 : Φ = 0
  · have e : ∀ h, flatS ψ ν μ Φ h = 0 := fun h => Subtype.ext (funext fun x => by
      simp [flatS, flat, opE, om, h0])
    have e' : xiOneS ψ ν μ Φ J bas = 0 := Subtype.ext (funext fun x => by
      simp [xiOneS, xi, flat, opE, om, h0])
    rw [e', show integrand ψ ν μ Φ σ b θ φ v = fun _ => 0 from funext fun h => by simp [integrand, e]]
    simpa using isQuotInt_zero_iff H z
  have := t2Space k
  have hvs : v ∈ PRep.smoothPart σ := by
    refine SmGL.mem_smoothPart_of_nhds (Filter.mem_of_superset ((hJ.inter ((isOpen_stabilizer_om hμ Φ.2).preimage
      (Continuous.prodMk_right (1 : GL (n' ⊕ Fin (c + 1)) k)))).mem_nhds ⟨one_mem J, om_one μ _⟩) ?_)
    rintro g ⟨hg, hg'⟩
    have h1 : (((lam ⟨g, hg⟩)⁻¹ : ℂˣ) : ℂ) • Φ.1 = (1 : ℂ) • Φ.1 := by rw [← hΦ ⟨g, hg⟩, one_smul]; exact hg'
    have h2 := smul_left_injective ℂ (fun h => h0 (Subtype.ext h)) h1
    have h3 : lam ⟨g, hg⟩ = 1 := inv_eq_one.1 (Units.ext h2)
    show σ g v = v
    simpa [h3] using hv ⟨g, hg⟩
  let ρ' : Representation ℂ (GL n' k) (SB (Matrix n n' k)) := (omRep μ).comp (MonoidHom.inl _ _)
  let πS : Representation ℂ (GL n k) (SB (Matrix n n' k)) := (omRep μ).comp (MonoidHom.inr _ _)
  have hρ' : IsSmoothRep ρ' := fun Ψ => (omRep_smooth hμ Ψ).preimage (Continuous.prodMk_left 1)
  have hπS : IsSmoothRep πS := fun Ψ => (omRep_smooth hμ Ψ).preimage (Continuous.prodMk_right 1)
  have hcomm : ∀ g h Ψ, πS h (ρ' g Ψ) = ρ' g (πS h Ψ) := fun g h Ψ => Subtype.ext (by
    change om μ 1 h (om μ g 1 Ψ.1) = om μ g 1 (om μ 1 h Ψ.1)
    rw [← om_mul, ← om_mul]; simp)
  let K₀ : Subgroup (GL n' k) :=
    { carrier := {g | om μ (embX (c + 1) g) 1 Φ.1 = Φ.1}
      one_mem' := by simp [om_one]
      mul_mem' := fun {x y} hx hy => by
        have := om_mul μ (embX (c + 1) x) (embX (c + 1) y) 1 1 Φ.1
        rw [hy, hx, mul_one, ← map_mul] at this
        exact this
      inv_mem' := fun {x} hx => by
        have := om_mul μ (embX (c + 1) x⁻¹) (embX (c + 1) x) 1 1 Φ.1
        rw [hx, mul_one, ← map_mul, inv_mul_cancel, map_one, om_one] at this
        exact this.symm }
  have hK₀ : IsOpen (K₀ : Set (GL n' k)) :=
    (isOpen_stabilizer_om hμ Φ.2).preimage ((Continuous.prodMk_left 1).comp QuotStep.continuous_embX)
  have hKo : IsOpen ((KO k n' ⊓ K₀ : Subgroup _) : Set (GL n' k)) := SplitFlip.isOpen_KO.inter hK₀
  have hKc : IsCompact ((KO k n' ⊓ K₀ : Subgroup _) : Set (GL n' k)) :=
    SplitFlip.isCompact_KO.inter_right (K₀.isClosed_of_isOpen hK₀)
  obtain ⟨P', _, _, π', θ', e, hπ', he1, he2⟩ := exists_equivariant ρ' hρ' πS hcomm _ hKo hKc
  have hfl : ∀ h, θ' e (flatS ψ ν μ Φ h) = flatS ψ ν μ Φ h := fun h => he2 _ fun g hg => Subtype.ext (by
    have h1 := (opE_om_embX k n n' c 1 le_rfl hc ψ ν μ (om μ 1 h Φ.1)).2 g
    have h2 : om μ (embX (c + 1) g) 1 (om μ 1 h Φ.1) = om μ 1 h (om μ (embX (c + 1) g) 1 Φ.1) := by
      rw [← om_mul, ← om_mul]; simp
    rw [nabs_eq_one_of_valuation_eq_one (valuation_det_of_mem_KO hg.1), Real.one_rpow, Complex.ofReal_one, one_smul,
      h2, show om μ _ 1 Φ.1 = Φ.1 from hg.2] at h1
    exact h1.symm)
  have hxi : θ' e (xiOneS ψ ν μ Φ J bas) = xiOneS ψ ν μ Φ J bas := by
    rw [show xiOneS ψ ν μ Φ J bas = (((volNat ν bas (Cgrp J 1))⁻¹ : ℝ) : ℂ) • flatS ψ ν μ Φ 1 from rfl, map_smul, hfl]
  have key := H P' _ _ π' πS (PRep.smoothRep σ) hπ' hπS
    (SmGL.isSmooth_smoothRep _) ((b ∘ₗ θ φ).compl₂ (PRep.smoothPart σ).subtype)
    ⟨fun Ψ g hg a => hb.1 (θ φ Ψ) g hg a, fun g Ψ a => by
      have := hb.2 g (θ φ Ψ) a
      rw [← hθ g φ Ψ (πS g Ψ) rfl] at this
      exact this⟩
    θ' (fun g h T Ψ => by
      refine Eq.trans (congrArg (θ' (π' g T)) (Subtype.ext ?_)) (he1 g h T Ψ)
      change om μ g h Ψ.1 = om μ g 1 (om μ 1 h Ψ.1)
      rw [← om_mul]; simp)
    e ⟨v, hvs⟩ (fun j => Subtype.ext (hv j)) z
  rw [hxi, show integrand ψ ν μ Φ _ _ θ' e _ = integrand ψ ν μ Φ σ b θ φ v from funext fun h => by
    change b (θ φ (θ' e _)) (σ h v) = b (θ φ _) (σ h v)
    rw [hfl]] at key
  exact key
end GlobalTheory.CollapseCompare
