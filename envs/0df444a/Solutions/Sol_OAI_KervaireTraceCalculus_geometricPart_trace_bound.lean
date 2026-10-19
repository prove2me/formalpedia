-- Prove2me | solution 1 for OAI.KervaireTraceCalculus.geometricPart_trace_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:32:16.758225+00:00
-- url     : https://prove2.me/submissions/6aec32c5-d21e-4f76-9b19-542f8536c0e0

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus

open OAI OAI.KervaireTraceCalculus
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped Topology
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedRing E]
  [NormedAlgebra 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
theorem kt_geom (Z : A) (hZ : ‖Z‖ < 1) :
    0 ≤ 1 + (∑' n : ℕ, Z ^ (n+1)) + star (∑' n : ℕ, Z ^ (n+1)) := by
  set G := ∑' n : ℕ, Z ^ n with hGdef
  have hsum : Summable (fun n : ℕ => Z ^ n) := summable_geometric_of_norm_lt_one hZ
  have hS : (∑' n : ℕ, Z ^ (n+1)) = G - 1 := by
    rw [hGdef, hsum.tsum_eq_zero_add]; simp
  have hR : (1 - Z) * G = 1 := mul_neg_geom_series Z hZ
  have hZG : Z * G = G - 1 := by
    rw [sub_mul, one_mul] at hR
    rw [← hR]; abel
  have hGZ : star G * star Z = star G - 1 := by
    have := congrArg star hZG; rwa [star_mul, star_sub, star_one] at this
  have key : 1 + (G - 1) + star (G - 1) = star G * (1 - star Z * Z) * G := by
    have : star G * (1 - star Z * Z) * G = star G * G - (star G * star Z) * (Z * G) := by noncomm_ring
    rw [this, hGZ, hZG, star_sub, star_one]; noncomm_ring
  rw [hS, key]
  apply star_left_conjugate_nonneg
  have h1 := CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := Z)
  have h2 : algebraMap ℝ A (‖Z‖ ^ 2) ≤ 1 := by
    rw [← map_one (algebraMap ℝ A)]
    apply algebraMap_mono
    have := norm_nonneg Z
    nlinarith
  exact sub_nonneg.2 (h1.trans h2)

theorem kt_tmn (τ : A →L[ℂ] ℂ)
    (ht : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (hp : ∀ X : A, 0 ≤ (τ (star X * X)).re)
    {B D : A} (hB : 0 ≤ B) (hD : 0 ≤ D) : 0 ≤ (τ (D * B)).re := by
  set sB := CFC.sqrt B
  set sD := CFC.sqrt D
  have hB2 : sB * sB = B := CFC.sqrt_mul_sqrt_self B hB
  have hD2 : sD * sD = D := CFC.sqrt_mul_sqrt_self D hD
  have hsB : IsSelfAdjoint sB := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)
  have hsD : IsSelfAdjoint sD := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg D)
  have h : τ (D * B) = τ (star (sD * sB) * (sD * sB)) := by
    rw [star_mul, hsB.star_eq, hsD.star_eq, ← hB2, ← hD2]
    rw [show sD * sD * (sB * sB) = (sD * sD * sB) * sB by noncomm_ring, ht]
    congr 1; noncomm_ring
  rw [h]; exact hp _

theorem solution (τ : A →L[ℂ] ℂ)
    (ht : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (hp : ∀ X : A, 0 ≤ (τ (star X * X)).re)
    (hs : ∀ X : A, τ (star X) = star (τ X))
    {B : A} (hB : 0 ≤ B) (Z : A) (hZ : ‖Z‖ < 1) :
    -2 * (τ ((∑' n : ℕ, Z ^ (n+1)) * B)).re ≤ (τ B).re := by
  set S := ∑' n : ℕ, Z ^ (n+1)
  have hD := kt_geom Z hZ
  have h0 := kt_tmn τ ht hp hB hD
  have hBsa : IsSelfAdjoint B := IsSelfAdjoint.of_nonneg hB
  have hstar : τ (star S * B) = star (τ (S * B)) := by
    rw [ht, ← hs, star_mul, hBsa.star_eq]
  have hsplit : τ ((1 + S + star S) * B) = τ B + τ (S * B) + τ (star S * B) := by
    rw [add_mul, add_mul, one_mul, map_add, map_add]
  rw [hsplit, hstar] at h0
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re] at h0
  linarith
