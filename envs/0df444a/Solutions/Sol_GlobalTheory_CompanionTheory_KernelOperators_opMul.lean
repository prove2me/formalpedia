-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelOperators.opMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:56:32.027817+00:00
-- url     : https://prove2.me/submissions/2524e081-07e4-4411-a56f-35db861c2dbe

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CompKey
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelOperators_comp_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelOperators
namespace GlobalTheory.CompanionTheory.KernelOperators
theorem _root_.solution : KerBasic → KerLin → RowInt → KernelL2RowsColumns → SchurInt → CvTest → KerMul → OpMul := by
  intro hB hLin hR hL hS hC hM X ι _ Φ₁ Φ₂ T₁ T₂ h₁ h₂ o₁ o₂
  have tcv : ∀ i j k, Tst (cv X.μ (Φ₁ i k) (Φ₂ k j)) :=
    fun i j k => (hC X _ _ (h₁ i k) (h₂ k j)).1
  have lin : ∀ i j, Tst (fun y => ∑ k, cv X.μ (Φ₁ i k) (Φ₂ k j) y) ∧
      ∀ x y, ker X.Γ (fun y => ∑ k, cv X.μ (Φ₁ i k) (Φ₂ k j) y) x y
        = ∑ k, ker X.Γ (cv X.μ (Φ₁ i k) (Φ₂ k j)) x y := by
    intro i j
    have h := hLin X ι (fun k => cv X.μ (Φ₁ i k) (Φ₂ k j)) (fun _ => 1) (fun k => tcv i j k)
    simpa only [mul_one] using h
  refine ⟨fun i j => (lin i j).1, ?_⟩
  intro f i
  have a1 := o₁ (T₂ f) i
  show ((T₁ (T₂ f)) i : X.G → ℂ) =ᵐ[X.ν] _
  filter_upwards [a1] with x hx
  rw [hx]
  have hfj : ∀ j, MemLp (f j : X.G → ℂ) 2 X.ν := fun j => Lp.memLp _
  have step : ∀ k, ∫ z, ker X.Γ (Φ₁ i k) x z * ((T₂ f) k : X.G → ℂ) z ∂X.ν
      = ∑ j, ∫ y, ker X.Γ (cv X.μ (Φ₁ i k) (Φ₂ k j)) x y * (f j : X.G → ℂ) y ∂X.ν := by
    intro k
    have e : (fun z => ker X.Γ (Φ₁ i k) x z * ((T₂ f) k : X.G → ℂ) z) =ᵐ[X.ν]
        fun z => ∑ j, ker X.Γ (Φ₁ i k) x z *
          ∫ y, ker X.Γ (Φ₂ k j) z y * (f j : X.G → ℂ) y ∂X.ν := by
      filter_upwards [o₂ f k] with z hz
      rw [hz, Finset.mul_sum]
    rw [integral_congr_ae e, integral_finset_sum _ fun j _ =>
      (comp_key hB hR hL hS hM X _ _ (h₁ i k) (h₂ k j) x _ (hfj j)).1]
    exact Finset.sum_congr rfl fun j _ =>
      (comp_key hB hR hL hS hM X _ _ (h₁ i k) (h₂ k j) x _ (hfj j)).2
  rw [Finset.sum_congr rfl fun k _ => step k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [(lin i j).2, Finset.sum_mul]
  have hi : ∀ k, Integrable
      (fun y => ker X.Γ (cv X.μ (Φ₁ i k) (Φ₂ k j)) x y * (f j : X.G → ℂ) y) X.ν :=
    fun k => MemLp.integrable_mul ((hL X _ (tcv i j k)).2 x) (hfj j)
  exact (integral_finset_sum _ fun k _ => hi k).symm
end GlobalTheory.CompanionTheory.KernelOperators
