-- Prove2me | solution 1 for GlobalTheory.RootEx.exDown_exUp_and_exUp_exDown
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:11:52.776519+00:00
-- url     : https://prove2.me/submissions/a2ee3f44-7020-4189-9fbd-e9769d3c85fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExDownExUpAndExUpExDown
import Theorems.Thm_GlobalTheory_RootEx_rowE_zero_eq_one
import Theorems.Thm_GlobalTheory_RootEx_colE_zero_eq_one
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_fourier_transform_inversion_localFieldPi
import Theorems.Thm_GlobalTheory_T_rootExchange_support_and_fourier_relation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
namespace GlobalTheory.RootEx
private theorem sigmaCompactSpace_nonarchimedeanLocalField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SigmaCompactSpace k := by
  obtain ⟨γ, hγ0, hγ1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := k)
  have hδ : (1 : ValueGroupWithZero k) < γ⁻¹ := one_lt_inv_iff₀.mpr ⟨hγ0, hγ1⟩
  refine ⟨⟨fun m : ℕ => {x : k | valuation k x ≤ γ⁻¹ ^ m},
    fun m => IsNonarchimedeanLocalField.isCompact_closedBall k _, ?_⟩⟩
  ext x
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact MulArchimedean.arch (valuation k x) hδ
private theorem fourier_fourier_eq_neg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n]
    [DecidableEq n] (ψ : AddChar k Circle) (ν : Measure k) [SigmaFinite ν] [ν.IsAddHaarMeasure]
    (hF : ∀ f ∈ SB (n → k), ∫ y : n → k, (∫ x : n → k, f x * (ψ (x ⬝ᵥ y) : ℂ)
      ∂(Measure.pi fun _ => ν)) ∂(Measure.pi fun _ => ν) = f 0)
    (f : (n → k) → ℂ) (hf : f ∈ SB (n → k)) (z : n → k) :
    ∫ y : n → k, (∫ x : n → k, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) * (ψ (y ⬝ᵥ z) : ℂ)
      ∂(Measure.pi fun _ => ν) = f (-z) := by
  have hτ : (fun x : n → k => f (x - z)) ∈ SB (n → k) :=
    ⟨hf.1.comp_continuous (continuous_sub_right z), hf.2.comp_homeomorph (Homeomorph.subRight z)⟩
  have key : ∀ y : n → k, (∫ x : n → k, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν))
      * (ψ (y ⬝ᵥ z) : ℂ) = ∫ x : n → k, f (x - z) * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν) := by
    intro y
    rw [← integral_mul_const,
      ← integral_add_right_eq_self (fun x : n → k => f (x - z) * (ψ (x ⬝ᵥ y) : ℂ)) z]
    congr 1
    funext x
    simp only [add_sub_cancel_right, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul,
      dotProduct_comm z y]
    ring
  calc _ = ∫ y : n → k, (∫ x : n → k, f (x - z) * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν))
        ∂(Measure.pi fun _ => ν) := by
          congr 1
          funext y
          exact key y
    _ = f (0 - z) := hF _ hτ
    _ = f (-z) := by rw [zero_sub]
end GlobalTheory.RootEx
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx
namespace GlobalTheory.RootEx
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), (IsNEquiv ψ p σ l → exDown ν p σ (exUp ν p σ l) v = l v) ∧ (IsNEquiv ψ (p + 1) σ l → exUp ν p σ (exDown ν p σ l) v = l v) := by
  intro k _ _ _ _ _ _ n _ _ c p hp hpc ψ hψc hψ1 ν hsd A _ _ σ hσ l v
  have : ν.IsAddHaarMeasure := hsd.1
  have hT := GlobalTheory.T.rootExchange_support_and_fourier_relation k n c p hp hpc ψ hψc hψ1 ν A σ hσ l v
  have hF := GlobalTheory.T.fourier_transform_inversion_localFieldPi k n ψ hψc hψ1 ν hsd
  constructor
  · intro hN
    obtain ⟨hSB, -, hint⟩ := hT.1 hN
    have h1 : exDown ν p σ (exUp ν p σ l) v
        = ∫ β : n → k, ∫ u : n → k, (fun u : n → k => l (σ (rowE c p u) v)) u * (ψ (u ⬝ᵥ β) : ℂ)
          ∂(Measure.pi fun _ => ν) ∂(Measure.pi fun _ => ν) := by
      unfold exDown
      congr 1
      funext β
      rw [hint β]
      congr 1
      funext u
      ring
    rw [h1, (hF _ hSB).2]
    simp [rowE_zero_eq_one]
  · intro hN
    obtain ⟨hSB, hcomm⟩ := hT.2 hN
    have : SigmaCompactSpace k := sigmaCompactSpace_nonarchimedeanLocalField k
    have : SigmaFinite ν := inferInstance
    have hF2 := fun f hf => (hF f hf).2
    have hG := (hF _ hSB).1
    have hGG := (hF _ hG).1
    have h1 : exUp ν p σ (exDown ν p σ l) v
        = ∫ u : n → k, ∫ y : n → k, (∫ x : n → k, (∫ β : n → k, l (σ (colE c (p + 1) β) v)
            * (ψ (β ⬝ᵥ x) : ℂ) ∂(Measure.pi fun _ => ν)) * (ψ (x ⬝ᵥ y) : ℂ)
            ∂(Measure.pi fun _ => ν)) * (ψ (y ⬝ᵥ u) : ℂ)
          ∂(Measure.pi fun _ => ν) ∂(Measure.pi fun _ => ν) := by
      unfold exUp exDown
      congr 1
      funext u
      rw [fourier_fourier_eq_neg ψ ν hF2 _ hG u]
      congr 1
      funext β
      rw [hcomm u β, dotProduct_neg, dotProduct_comm]
      ring
    rw [h1, hF2 _ hGG]
    simp only [dotProduct_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
    rw [hF2 _ hSB]
    show l (σ (colE c (p + 1) 0) v) = l v
    rw [colE_zero_eq_one, map_one]
    rfl
end GlobalTheory.RootEx
